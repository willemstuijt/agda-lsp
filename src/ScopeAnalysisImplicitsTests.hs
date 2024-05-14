module ScopeAnalysisImplicitsTests (runTests) where
import ScopeAnalysis (sigParamsFromSigType, allInsertions, Insertion (..), allRemovals, Removal (..), ScanState, scanModule, stateScope)
import Scope (SigParam (SigExplicit, SigImplicit), innerMostScope)
import Agda.Syntax.Parser (parseFile, moduleParser, runPMIO)
import Agda.Syntax.Position (mkRangeFile, Range' (NoRange), HasRange (getRange))
import Agda.Utils.FileName (mkAbsolute)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Language.LSP.Protocol.Types qualified as LSP
import Agda.Syntax.Concrete (Module (modDecls), Declaration (Module, TypeSig, FunClause), Pattern (..), Expr (Absurd), LHS (LHS, lhsOriginalPattern))
import Data.Maybe (fromJust)
import AgdaToLSP (toLSPRange', incLSPPos)
import Data.Map qualified as Map

-- Some utilities to run the tests

data TestOutput
  = Failed String
  | Passed
  deriving (Eq)

instance Show TestOutput where
  show (Failed err) = "Failed: " ++ err
  show Passed = "Passed"

type Test = (String, [SigParam])

sigParamTests :: [Test]
sigParamTests =
  [ ("foo : Int", [])
  , ("foo : Int -> Int", [SigExplicit e])
  , ("foo : Vector m n -> Int", [SigExplicit e])
  , ("foo : Vector m n -> Matrix x -> Int", [SigExplicit e, SigExplicit e])
  , ("foo : {a : Nat} -> Int", [SigImplicit (Just "a") e])
  , ("foo : {a : Nat} {b : Nat} -> Int", [SigImplicit (Just "a") e, SigImplicit (Just "b") e])
  , ("foo : {a : Nat} {b c : Nat} -> Int", [SigImplicit (Just "a") e, SigImplicit (Just "b") e, SigImplicit (Just "c") e])
  , ("foo : {a : Nat} -> (z : Int) -> {b : Nat} -> Int", [SigImplicit (Just "a") e, SigExplicit e, SigImplicit (Just "b") e])
  , ("foo : {a : Nat} -> (z y : Int) -> {b : Nat} -> Int", [SigImplicit (Just "a") e, SigExplicit e, SigExplicit e, SigImplicit (Just "b") e])
  , ("add : {x : ℕ} -> ℕ -> ℕ", [SigImplicit (Just "x") e, SigExplicit e])
  ]
  where
    -- placeholder since Expr is not compared
    e = Absurd NoRange

type InsTest = (String, [Insertion])

insertionTests :: [InsTest]
insertionTests =
  [ ("foo : {a b : Nat} -> Nat\n\
    \foo = 10\n\
    \", [ Insertion (r (p 1 3) (p 1 4)) "a" Nothing Nothing
        , Insertion (r (p 1 3) (p 1 4)) "b" (Just "b") Nothing
    ]),
    ("foo : {a b : Nat} -> Nat\n\
    \foo {a} = 10\n\
    \", [ Insertion (r (p 1 7) (p 1 8)) "b" Nothing Nothing
    ]),
    ("foo : {a b : Nat} -> Nat\n\
    \foo {b = b} = 10\n\
    \", [ Insertion (r (p 1 3) (p 1 4)) "a" Nothing Nothing
    ]),
    ("foo : Nat -> {a : Nat} -> Nat -> {b : Nat} -> Nat\n\
    \foo x y = 10\n\
    \", [ Insertion (r (p 1 5) (p 1 6)) "a" Nothing Nothing
        , Insertion (r (p 1 7) (p 1 8)) "b" Nothing Nothing
    ]),
    ("foo : Nat -> {a : Nat} -> Nat -> {b : Nat} -> Nat\n\
    \foo x {a} y = 10\n\
    \", [ Insertion (r (p 1 11) (p 1 12)) "b" Nothing Nothing
    ]),
    ("data D : Set where\n\
    \  c : {u : Nat} -> Nat -> {v : Nat} -> D\n\
    \\n\
    \f : {y : Nat} -> D -> D\n\
    \f (c a) = ?\n\
    \", [ Insertion (r (p 4 1) (p 4 2)) "y" Nothing Nothing
        , Insertion (r (p 4 4) (p 4 5)) "u" Nothing Nothing
        , Insertion (r (p 4 6) (p 4 6)) "v" Nothing Nothing
    ]),
    ("module Mod where\n\
    \  add : {x : ℕ} -> ℕ -> ℕ\n\
    \  add a = λ z → z + z\n\
    \", [ Insertion (r (p 2 5) (p 2 6)) "x" Nothing Nothing
    ]),
    ("data D : Set where\n\
    \  d : {u : Nat} -> D\n\
    \  c : {u : Nat} -> Nat -> {v : Nat} -> D\n\
    \\n\
    \f : {y : Nat} -> D -> D\n\
    \f d = D.c\n\
    \", [ Insertion (r (p 5 1) (p 5 2)) "y" Nothing Nothing
        , Insertion (r (p 5 3) (p 5 4)) "u" Nothing (Just (r (p 5 2) (p 5 3)))
    ]),
    ("data D : Set where\n\
    \  c : {u : Nat} -> Nat -> {v : Nat} -> D\n\
    \\n\
    \foo : D -> Nat\n\
    \foo (c _) = 10\n\
    \", [ Insertion (r (p 4 6) (p 4 7)) "u" Nothing Nothing
        , Insertion (r (p 4 8) (p 4 8)) "v" Nothing Nothing
    ])
  ]

type RemTest = (String, [Removal])

removalTests :: [RemTest]
removalTests =
  [ ("foo : {a b : Nat} -> Nat\n\
    \foo {a} = 10\n\
    \", [ Removal "a" True (r (p 1 3) (p 1 7)) Nothing Nothing
    ]),
    ("foo : {a b : Nat} -> Nat\n\
    \foo {a} {b} = 10\n\
    \", [ Removal "a" True (r (p 1 3) (p 1 7)) (Just (r (p 1 9) (p 1 9), "b")) Nothing
        , Removal "b" True (r (p 1 7) (p 1 11)) Nothing Nothing
    ]),
    ("foo : {a b : Nat} -> Nat\n\
    \foo {a} {b} = a + b\n\
    \", []),
    ("foo : {a b : Nat} -> Nat\n\
    \foo {a} {b = b} = 10\n\
    \", [ Removal "a" True (r (p 1 3) (p 1 7)) Nothing Nothing
        , Removal "b" True (r (p 1 7) (p 1 15)) Nothing Nothing
    ]),
    ("foo : {a b : Nat} -> Nat\n\
    \foo {suc a} {b} = 10\n\
    \", [ Removal "a" False (r (p 1 9) (p 1 10)) Nothing Nothing
        , Removal "b" True (r (p 1 11) (p 1 15)) Nothing Nothing
    ]),
    ("foo : Nat -> {a b : Nat} -> Nat\n\
    \foo x {suc a} {b} = 10\n\
    \", [ Removal "x" False (r (p 1 4) (p 1 5)) Nothing Nothing
        , Removal "a" False (r (p 1 11) (p 1 12)) Nothing Nothing
        , Removal "b" True (r (p 1 13) (p 1 17)) Nothing Nothing
    ]),
    ("data D : Set where\n\
    \  d : {u : Nat} -> D\n\
    \\n\
    \foo : D -> Nat\n\
    \foo (D.d {u}) = 10\n\
    \", [ Removal "u" True (r (p 4 8) (p 4 12)) Nothing (Just $ r (p 4 4) (p 4 13))
    ]),
    ("data D : Set where\n\
    \  c : {u : Nat} -> Nat -> {v : Nat} -> D\n\
    \\n\
    \foo : D -> Nat\n\
    \foo (c x) = 10\n\
    \", [ Removal "x" False (r (p 4 7) (p 4 8)) Nothing Nothing
    ]),
    ("data D : Set where\n\
    \  c : {u : Nat} -> Nat -> {v : Nat} -> D\n\
    \\n\
    \foo : D -> Nat\n\
    \foo (c {u} x) = 10\n\
    \", [ Removal "u" True (r (p 4 6) (p 4 10)) Nothing Nothing
        , Removal "x" False (r (p 4 11) (p 4 12)) Nothing Nothing
    ]),
    ("data D : Set where\n\
    \  c : {u : Nat} -> Nat -> {v : Nat} -> D\n\
    \\n\
    \foo : D -> Nat\n\
    \foo (c {u} _) = 10\n\
    \", [ Removal "u" True (r (p 4 6) (p 4 10)) Nothing Nothing
    ])
  ]

runSigParamTest :: Test -> IO TestOutput
runSigParamTest (code, expected) = do
    d : _ <- parseStringDecls code
    return $ case d of
        (TypeSig _ _ _ e) -> if length expected == length ps && all sigParamEq (zip expected ps) then Passed else Failed $ "expected: '" ++ show expected ++ "', got: '" ++ show ps ++ "'"
          where
            ps = sigParamsFromSigType e
        _ -> Failed "not a fun sig"
  where
    sigParamEq (SigExplicit _, SigExplicit _) = True
    sigParamEq (SigImplicit x _, SigImplicit y _) = x == y
    sigParamEq (_, _) = False

runInsertionsTest :: InsTest -> IO TestOutput
runInsertionsTest (code, expected) = do
    (state, modl) <- parseAndCheckModl code
    let (last', l, r') = fromJust $ lastFuncClause $ modDecls modl
    let ins = allInsertions (innerMostScope l $ stateScope state) l r' last'
    return $ if ins == expected then Passed else Failed $ "expected: '" ++ show expected ++ "', got: '" ++ show ins ++ "'"

runRemovalsTest :: RemTest -> IO TestOutput
runRemovalsTest (code, expected) = do
    (state, modl) <- parseAndCheckModl code
    let (last', l, _) = fromJust $ lastFuncClause $ modDecls modl
    let ins = allRemovals state l last'
    return $ if ins == expected then Passed else Failed $ "expected: '" ++ show expected ++ "', got: '" ++ show ins ++ "'"

parseString :: String -> IO Module
parseString code = do
  let tmp = parseFile moduleParser (mkRangeFile (mkAbsolute "/test.agda") Nothing) code
  (res, _) <- liftIO $ runPMIO tmp
  case res of
    (Left _) -> error "could not parse"
    (Right ((modl, _), _)) -> do
      return modl

parseStringDecls :: String -> IO [Declaration]
parseStringDecls code = do
    modl <- parseString code
    case modDecls modl of
        [Module _ _ _ _ ds] -> return ds
        _ -> return []

parseAndCheckModl :: String -> IO (ScanState, Module)
parseAndCheckModl code = do
    modl <- parseString code
    return (scanModule Map.empty modl, modl)

lastFuncClause :: [Declaration] -> Maybe (Pattern, LSP.Position, LSP.Position)
lastFuncClause ((Module _ _ _ _ mds):ds) = case lastFuncClause ds of
  Nothing -> lastFuncClause mds
  Just x -> Just x
lastFuncClause ((FunClause (LHS {lhsOriginalPattern = lhs}) _ _ _):ds) = case lastFuncClause ds of
  Nothing -> Just (lhs, l', incLSPPos r')
    where
      (LSP.Range l' r') = toLSPRange' $ getRange lhs
  Just x -> Just x
lastFuncClause (_:ds) = lastFuncClause ds
lastFuncClause [] = Nothing

runTests :: IO [TestOutput]
runTests = do
  x <- mapM runSigParamTest sigParamTests
  y <- mapM runInsertionsTest insertionTests
  z <- mapM runRemovalsTest removalTests
  return $ x ++ y ++ z

p :: LSP.UInt -> LSP.UInt -> LSP.Position
p = LSP.Position

r :: LSP.Position -> LSP.Position -> LSP.Range
r = LSP.Range
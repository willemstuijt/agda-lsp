module ScopeAnalysisTests (runTests) where
import ScopeAnalysis (SymUse (SymUse), scanModule, scanStateUses, stateScope)
import Agda.Syntax.Parser (parseFile, moduleParser, runPMIO)
import Agda.Syntax.Position (mkRangeFile)
import Agda.Utils.FileName (mkAbsolute)
import Language.LSP.Protocol.Types
    ( CompletionItem (..) )
import Language.LSP.Protocol.Types qualified as LSP
import Control.Monad.IO.Class (MonadIO(liftIO))
import Agda.Syntax.Concrete (Module)
import Scope (SymId(SymId), innerMostScope)
import Completions qualified as C
import Data.Text (unpack)
import Debug.Trace (trace)
import Data.Map qualified as Map
import ScopeImport (resolveAllModules, emptyState)

-- Some utilities to run the tests

data TestOutput
  = Failed String
  | Passed
  deriving (Eq)

instance Show TestOutput where
  show (Failed err) = "Failed: " ++ err
  show Passed = "Passed"

type Test = (String, [SymUse])

type CompletionTest = (String, [(LSP.Position, [String])])

p :: LSP.UInt -> LSP.UInt -> LSP.Position
p = LSP.Position

r :: LSP.Position -> LSP.Position -> LSP.Range
r = LSP.Range

symUsesTests :: [Test]
symUsesTests =
  [ ("foo : Nat\n\
     \foo = 10\n\
     \", [SymUse (r (p 1 0) (p 1 3)) (SymId 0)]),
    ("module Mod where\n\
    \  foo : Nat\n\
    \  foo = 10\n\
    \\n\
    \bar : Nat\n\
    \bar = Mod.foo\
    \", [ SymUse (r (p 5 10) (p 5 13)) (SymId 0) -- "Mod.foo"
        , SymUse (r (p 5 6) (p 5 10)) (SymId 1) -- "Mod"
        , SymUse (r (p 5 0) (p 5 3)) (SymId 2) -- "bar"
        , SymUse (r (p 2 2) (p 2 5)) (SymId 0) -- "foo"
    ]),
    ("data ℕ : Set where\n\
    \  zero : ℕ\n\
    \  suc  : ℕ -> ℕ\n\
    \\n\
    \id : ℕ -> ℕ\n\
    \id x = x\n\
    \", [ SymUse (r (p 5 7) (p 5 8)) (SymId 4) -- "x"
        , SymUse (r (p 5 0) (p 5 2)) (SymId 3) -- "id"

        , SymUse (r (p 4 10) (p 4 11)) (SymId 0) -- "ℕ"
        , SymUse (r (p 4 5) (p 4 6)) (SymId 0) -- "ℕ"

        , SymUse (r (p 2 14) (p 2 15)) (SymId 0) -- "ℕ"
        , SymUse (r (p 2 9) (p 2 10)) (SymId 0) -- "ℕ"
        , SymUse (r (p 1 9) (p 1 10)) (SymId 0) -- "ℕ"
    ]),
    ("data _[_]=_ {A : Set a} {P : Pred A p} :\n\
      \  ∀ {x xs} → All P xs → x ∈ₚ xs → P x → Set (a ⊔ p) where\n\
      \", [ SymUse (r (p 1 36) (p 1 37)) (SymId 2) -- "P x"
          , SymUse (r (p 1 34) (p 1 35)) (SymId 1)

          , SymUse (r (p 1 29) (p 1 31)) (SymId 3) -- x ∈ₚ xs
          , SymUse (r (p 1 24) (p 1 25)) (SymId 2)

          , SymUse (r (p 1 19) (p 1 21)) (SymId 3) -- All P xs
          , SymUse (r (p 1 17) (p 1 18)) (SymId 1)

          , SymUse (r (p 0 34) (p 0 35)) (SymId 0) -- "Pred A p"
    ])
  ]

completionsTests :: [CompletionTest]
completionsTests =
  [ ("module Mod where\n\
      \  foo : Nat\n\
      \  foo = 10\n\
      \\n\
      \  baz : Nat\n\
      \  baz = 10\n\
      \\n\
      \bar : Nat\n\
      \bar = Mod.foo \
      \", [
        (p 5 10, ["baz", "foo"]),
        (p 8 9, ["Mod", "bar"]),
        (p 8 10, ["baz", "foo"]),
        (p 8 11, ["baz", "foo"]),
        (p 8 12, ["baz", "foo"]),
        (p 8 13, ["baz", "foo"]),
        (p 8 14, ["Mod", "bar"]),
        (p 9 0, ["Mod", "bar"])
      ]),
    ("import Category.Applicative\n\
      \\n\
      \", [
        (p 1 0, ["Category.Applicative"])
      ]),
    ("open import Category.Applicative\n\
      \\n\
      \", [
        (p 1 0, ["RawAlternative", "RawApplicative", "RawApplicativeZero"])
      ]),
    ("open import Category.Applicative hiding (RawAlternative)\n\
      \\n\
      \", [
        (p 1 0, ["RawAlternative", "RawApplicative", "RawApplicativeZero"])
      ]),
    ("open import Category.Applicative hiding (module RawAlternative)\n\
      \\n\
      \", [
        (p 1 0, ["RawApplicative", "RawApplicativeZero"])
      ]),
    ("open import Category.Applicative using (RawAlternative)\n\
      \\n\
      \", [
        (p 1 0, [])
      ]),
    ("open import Category.Applicative using (module RawAlternative)\n\
      \\n\
      \", [
        (p 1 0, ["RawAlternative"])
      ]),
    ("import Category.Applicative as App\n\
      \App.R\n\
      \", [
        (p 1 5, ["RawAlternative", "RawApplicative", "RawApplicativeZero"])
      ])
  ]

runSigParamTest :: Test -> IO TestOutput
runSigParamTest (code, expected) = do
    m <- parseString code
    let state = scanModule Map.empty m
    let uses = scanStateUses state
    let cond = length expected == length uses && expected == uses
    return $ if cond then Passed else Failed $ "expected: '" ++ show expected ++ "', got: '" ++ show uses ++ "'"

runCompletionsTest :: CompletionTest -> IO TestOutput
runCompletionsTest (code, cases) = do
    m <- parseString code
    (imps, _, _) <- resolveAllModules m emptyState
    let scope = stateScope $ scanModule imps m
    let (completions, expected) = unzip $ fmap (\(pos, e) -> (unpack . _label <$> C.completionsAtPos m scope pos, e)) cases
    let cond = all (uncurry (==)) (zip completions expected)
    return $ if cond then Passed else Failed $ "expected: '" ++ show expected ++ "', got: '" ++ show completions ++ "'"

parseString :: String -> IO Module
parseString code = do
  let tmp = parseFile moduleParser (mkRangeFile (mkAbsolute "/test.agda") Nothing) code
  (res, _) <- liftIO $ runPMIO tmp
  case res of
    (Left err) -> error $ "could not parse: " ++ show err ++ "\n\n" ++ code
    (Right ((modl, _), _)) -> do
      return modl

runTests :: IO [TestOutput]
runTests = do
  -- x <- mapM runSigParamTest symUsesTests
  x <- mapM runCompletionsTest completionsTests
  return $ x -- ++ y

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module ScopeAnalysis
  ( sigParamsFromSigType,
    matchPatternToParams,
    scanModule,
    stateScope,
    unusedSymbols,
    emptyScanState,
    scanStateUses,
    ScanState (..),
    SymUse (SymUse),
    symbolAtPos,
    allUsesOfSymbol,
    allInsertions,
    allRemovals,
    Removal (..),
    Insertion (..),
    insertableImplicits,
    removableVars,
  )
where

import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (Pretty (pretty))
import Agda.Syntax.Concrete
import Agda.Syntax.Parser
import Agda.Syntax.Position
import Agda.Utils.FileName
import Agda.Utils.List1 (NonEmpty ((:|)))
import Agda.Utils.List2 (List2 (List2))
import AgdaToLSP (containsPos, decLSPPos, endOfExpr, endOfPattern, incLSPPos, posOfPattern, posOfTypedBinding, qnameRange, rangeContainsPos, toLSPRange, toLSPRange', unpackName)
import Data.List (find)
import Data.Map qualified as Map
import Data.Maybe
import Data.Set qualified as Set
import Debug.Trace (trace)
import Language.LSP.Protocol.Types qualified as LSP
import Scope (getSym, symScope)
import Scope qualified as S
import ScopeMap (allKeys, allValues)
import Traversal (Done (Continue, Done), Node (D), doneAsMaybe, foldModule)

scanModule :: Map.Map QName S.Symbol -> Module -> ScanState
scanModule imports modl = foldl scanDecl (scanStateWithImports imports) decls
  where
    decls = partitionByTypeSig $ modDecls modl

unusedSymbols :: ScanState -> [S.Symbol]
unusedSymbols (ScanState _ nxtIdx scope uses) = unusedVars
  where
    syms = S.allSymbols scope
    used = Set.fromList (fmap (\(SymUse _ x) -> x) uses)

    unusedDefs idx | idx < nxtIdx = case Set.member idx used of
      True -> unusedDefs (S.incId idx)
      False -> case Map.lookup idx syms of
        Nothing -> rest
        Just x -> x : rest
        where
          rest = unusedDefs (S.incId idx)
    unusedDefs _ = []

    unusedVars = filter (isVar . getSym) $ unusedDefs (S.SymId 0)

    getSym (S.Symbol _ _ _ s) = s

    isVar S.SImpl = True
    isVar S.SExpl = True
    isVar _ = False

data SymUse = SymUse LSP.Range S.SymId deriving (Eq)

showPos :: LSP.Position -> String
showPos (LSP.Position l c) = show l ++ ":" ++ show c

showRange :: LSP.Range -> String
showRange (LSP.Range (LSP.Position l1 c1) (LSP.Position l2 c2))
  | l1 == l2 = show l1 ++ ":" ++ show c1 ++ "-" ++ show c2
showRange (LSP.Range a b) = showPos a ++ "-" ++ showPos b

instance Show SymUse where
  show (SymUse r i) = show i ++ " @ " ++ showRange r

data ScanState = ScanState (Map.Map QName S.Symbol) S.SymId S.Scope [SymUse]

emptyScanState :: ScanState
emptyScanState = ScanState Map.empty (S.SymId 0) S.empty []

scanStateWithImports :: Map.Map QName S.Symbol -> ScanState
scanStateWithImports imports = ScanState imports (S.SymId 0) S.empty []

getScope :: ScanState -> S.Scope
getScope (ScanState _ _ scope _) = scope

scanStateUses :: ScanState -> [SymUse]
scanStateUses (ScanState _ _ _ uses) = uses

declareSym :: LSP.Range -> String -> S.Sym -> ScanState -> ScanState
declareSym r name sym (ScanState imps nxt scope uses) = ScanState imps (S.incId nxt) (S.insert name r symbol scope) uses
  where
    symbol = S.Symbol r name nxt sym

declareSymbol :: LSP.Range -> String -> S.Symbol -> ScanState -> ScanState
declareSymbol r name symbol (ScanState imps nxt scope uses) = ScanState imps nxt (S.insert name r symbol scope) uses

overwriteSym :: LSP.Range -> S.SymId -> String -> S.Sym -> ScanState -> ScanState
overwriteSym r usedId name sym (ScanState imps nxt scope uses) = ScanState imps nxt (S.overwrite name r symbol scope) uses
  where
    symbol = S.Symbol r name usedId sym

declareName :: Bool -> Name -> ScanState -> ScanState
declareName implicit name = declareSym r n (if implicit then S.SImpl else S.SExpl)
  where
    (r, n) = unpackName name

useSym :: LSP.Range -> S.SymId -> ScanState -> ScanState
useSym range sid (ScanState imps nxt scope uses) = ScanState imps nxt scope (SymUse range sid : uses)

lookupSym :: String -> ScanState -> Maybe S.Symbol
lookupSym name (ScanState _ _ scope _) = S.lookupParent name scope

useSymName :: LSP.Range -> String -> ScanState -> ScanState
useSymName range name ss = case lookupSym name ss of
  Nothing -> ss
  Just (S.Symbol _ _ i _) -> useSym range i ss

-- also adds uses for the modules that are used for qualifiers when ScanState not Nothing
lookupSymQName_ :: Maybe ScanState -> S.Scope -> QName -> (Maybe S.Symbol, Maybe ScanState)
lookupSymQName_ state scope (QName n) = case S.lookupParent name scope of
  Nothing -> (Nothing, state)
  Just s@(S.Symbol _ _ i _) -> (Just s, fmap (useSym r i) state)
  where
    (r, name) = unpackName n
lookupSymQName_ state scope (Qual a b) = case S.lookupParent name scope of
  Just (S.Symbol _ _ i sym) -> case symScope sym of
    Nothing -> (Nothing, state)
    Just scope' -> lookupSymQName_ state' scope' b
    where
      state' = fmap (useSym r i) state
  _ -> (Nothing, state)
  where
    (r, name) = unpackName a

useSymQName :: S.Scope -> QName -> ScanState -> ScanState
useSymQName scope name state = fromJust state'
  where
    (_, state') = lookupSymQName_ (Just state) scope name

lookupSymQName :: S.Scope -> QName -> Maybe S.Symbol
lookupSymQName scope name = sym
  where
    (sym, _) = lookupSymQName_ Nothing scope name

childScope :: ScanState -> LSP.Range -> ScanState
childScope (ScanState imps nxt scope uses) range = ScanState imps nxt (S.newScope (Just scope) range) uses

addChildScope :: ScanState -> ScanState -> ScanState
addChildScope (ScanState imps _ scope _) (ScanState _ nxt scope' uses) = ScanState imps nxt (S.addChildScope scope scope') uses

-- adds all syms of S.Scope to ScanState
addSymsOfScope :: S.Scope -> ScanState -> ScanState
addSymsOfScope scope (ScanState x a b c) = ScanState x a (S.insertScope scope b) c

addSymsOfScopeFiltered :: ((String, Bool) -> Maybe String) -> S.Scope -> ScanState -> ScanState
addSymsOfScopeFiltered ft scope (ScanState x a b c) = ScanState x a (S.insertScopeFiltered ft scope b) c

stateScope :: ScanState -> S.Scope
stateScope (ScanState _ _ scope _) = scope

symbolAtPos :: ScanState -> LSP.Position -> Maybe S.Symbol
symbolAtPos (ScanState _ _ scope uses) pos = case symDef of
  Nothing -> case symUse of
    Nothing -> Nothing
    Just (SymUse _ i) -> S.symbolByID scope i
  x -> x
  where
    symDef = S.symbolAtPos scope pos
    symUse = find (\(SymUse r _) -> rangeContainsPos r pos) uses

allUsesOfSymbol :: ScanState -> S.SymId -> [SymUse]
allUsesOfSymbol (ScanState _ _ _ uses) sid = filter (\(SymUse _ x) -> x == sid) uses

scanDecl :: ScanState -> GroupedDecl -> ScanState
scanDecl state (FuncDecl ((TypeSig _ _ n typ) : cs)) = overwriteSym range usedId name (S.SFunc params cases) state''
  where
    params = sigParamsFromSigType typ
    -- For use to work, the func must already be there
    state' = declareSym range name (S.SFunc params []) (scanExpr state typ)
    (ScanState _ (S.SymId x) _ _) = state'
    usedId = S.SymId (x - 1)
    (state'', cases) = foldlState scanFuncClause state' cs
    (range, name) = unpackName n
scanDecl state (FuncDecl _) = state -- should never happen
scanDecl state (SingleDecl (Module r _ name _ ds)) = declareSym modR modN (S.SModl [] $ S.Modl scope) (addChildScope state state'')
  where
    (modR, modN) = case name of
      QName n -> unpackName n
      _ -> (qnameRange name, "")
    r2 = if modN == "_" then LSP.Range (LSP.Position 0 0) (LSP.Position 1000000000 1000000000) else toLSPRange' r -- Implicit file module named _ has no range
    state' = childScope state r2
    state'' = foldl scanDecl state' (partitionByTypeSig ds)
    (ScanState _ _ scope _) = state''
scanDecl state (SingleDecl (Data r _ name bs typ csts)) = state'''
  where
    -- We create a new scope for data declaration
    (modR, modN) = unpackName name
    r' = toLSPRange' r
    bsState = foldl scanLamBinding (childScope state (toLSPRange' $ getRange (bs, typ))) bs
    state' = declareSym modR modN (S.SData $ S.Data S.empty) $ childScope (addChildScope state $ scanExpr bsState typ) r'
    (ScanState _ (S.SymId x) _ _) = state'
    usedId = S.SymId (x - 1)
    state'' = foldl scanDecl state' (noPartition csts)
    overwrite = overwriteSym modR usedId modN (S.SData $ S.Data scope) state''
    (ScanState _ _ scope _) = overwrite
    state''' = addSymsOfScope scope (addChildScope state overwrite)
scanDecl state (SingleDecl (TypeSig _ _ name typ)) = declareSym r n (S.SConstr params) state'
  where
    (r, n) = unpackName name
    state' = scanExpr state typ
    params = sigParamsFromSigType typ
scanDecl state (SingleDecl (FunClause (LHS {lhsOriginalPattern = p}) (RHS rhs) _ _)) = state' -- this is for lets, adds no extra scope
  where
    stateLhs = scanPattern False state p
    state' = scanExpr stateLhs rhs
scanDecl state (SingleDecl (Open _ name impDir)) = case lookupSymQName (stateScope state) name of
  Nothing -> state
  Just sym -> scanOpen state sym impDir
scanDecl state (SingleDecl (Import _ name as sh impDir)) = case Map.lookup name imports of
  Nothing -> state
  Just x -> case sh of
    DontOpen -> declareSymbol r name' x state
      where
        r = toLSPRange' $ case as of
          Nothing -> getRange name
          Just (AsName n _) -> getRange n
        name' = case as of
          Nothing -> show . pretty $ name
          Just (AsName n _) -> show . pretty $ n
    DoOpen -> scanOpen state x impDir
  where
    (ScanState imports _ _ _) = state
scanDecl state (SingleDecl _) = state

impDirToFilter :: ImportDirective -> ((String, Bool) -> Maybe String)
impDirToFilter (ImportDirective _ UseEverything hiding renaming _) = filt
  where
    renameMap = renamedMap renaming
    hiddenSet = impNameSet hiding

    filt (name, isModl) =
      if Set.member (name, isModl) hiddenSet
        then Nothing
        else
          ( case Map.lookup (name, isModl) renameMap of
              Nothing -> Just name
              Just rename -> Just rename
          )
impDirToFilter (ImportDirective _ (Using using) _ renaming _) = filt
  where
    renameMap = renamedMap renaming
    usingSet = impNameSet using

    filt (name, isModl) = if Set.member (name, isModl) usingSet then Just name else maybe Nothing Just (Map.lookup (name, isModl) renameMap)

impNameSet :: [ImportedName' Name Name] -> Set.Set (String, Bool)
impNameSet (ImportedModule name : imps) = Set.insert (show . pretty $ name, True) (impNameSet imps)
impNameSet (ImportedName name : imps) = Set.insert (show . pretty $ name, False) (impNameSet imps)
impNameSet [] = Set.empty

renamedMap :: RenamingDirective' Name Name -> Map.Map (String, Bool) String
renamedMap ((Renaming (ImportedModule from) (ImportedModule to) _ _) : rds) = Map.insert (from', True) to' rest
  where
    from' = show . pretty $ from
    to' = show . pretty $ to
    rest = renamedMap rds
renamedMap ((Renaming (ImportedName from) (ImportedName to) _ _) : rds) = Map.insert (from', False) to' rest
  where
    from' = show . pretty $ from
    to' = show . pretty $ to
    rest = renamedMap rds
renamedMap (_ : rds) = renamedMap rds
renamedMap [] = Map.empty

scanOpen :: ScanState -> S.Symbol -> ImportDirective -> ScanState
scanOpen state x impDir = addSymsOfScopeFiltered (impDirToFilter impDir) scope state
  where
    scope = fromJust $ symScope (getSym x)

scanDecl' :: ScanState -> Declaration -> ScanState
scanDecl' state decl = scanDecl state (SingleDecl decl)

scanFuncClause :: ScanState -> Declaration -> (ScanState, S.FuncCase)
-- TODO where
scanFuncClause state (FunClause (LHS {lhsOriginalPattern = p}) (RHS rhs) _ _) = (state', S.FuncCase (stateScope stateRhs))
  where
    scopeR = LSP.Range (posOfPattern p) (endOfExpr rhs)
    child = childScope state scopeR
    stateLhs = scanMainPattern child p
    stateRhs = scanExpr stateLhs rhs
    state' = addChildScope state stateRhs
scanFuncClause state _ = (state, S.FuncCase (stateScope state)) -- should never happen

scanNamedPattern :: Bool -> ScanState -> NamedArg Pattern -> ScanState
scanNamedPattern scope impl (Arg {unArg = Named {namedThing = p}}) = scanPattern scope impl p

scanMainPattern :: ScanState -> Pattern -> ScanState
scanMainPattern state p@(IdentP {}) = scanPatternUse state p
scanMainPattern state p = scanPattern False state p

scanPatternUse :: ScanState -> Pattern -> ScanState
scanPatternUse state (IdentP _ x) = useSymQName (stateScope state) x state
scanPatternUse state _ = state

-- True means we are inside a HiddenP so Idents are declared as hidden
scanPattern :: Bool -> ScanState -> Pattern -> ScanState
scanPattern implicit state (IdentP _ name) = case lookupSymQName (stateScope state) name of
  Nothing -> declareNonQual name
  Just symbol -> case S.getSym symbol of
    S.SConstr {} -> useSymQName (stateScope state) name state
    _ -> declareNonQual name
  where
    declareNonQual (QName n) = declareName implicit n state
    declareNonQual _ = state
scanPattern _ state (QuoteP _) = state
scanPattern impl state (AppP fun arg) = argScope
  where
    funScope = scanPatternUse state fun
    argScope = scanNamedPattern impl funScope arg
scanPattern impl state (RawAppP _ (List2 a b c)) = foldl (scanPattern impl) state' (b : c)
  where
    state' = scanPatternUse state a
scanPattern _ state (HiddenP _ (Named {namedThing = p})) = scanPattern True state p
scanPattern impl state (ParenP _ p) = scanPattern impl state p
scanPattern _ state (WildP _) = state
scanPattern _ state (AbsurdP _) = state
scanPattern impl state (AsP _ name p) = declareName impl name state'
  where
    state' = scanPattern impl state p
scanPattern _ state (DotP _ _) = state
scanPattern _ state (LitP _ _) = state
scanPattern _ state (EqualP _ _) = state
-- -- EllipsisP TODO
-- -- WithP TODO
scanPattern _ state _ = state

scanLamBinding :: ScanState -> LamBinding -> ScanState
scanLamBinding scope (DomainFree a) = scanNamedArg scope a
scanLamBinding scope (DomainFull a) = scanTypedBinding scope a

scanNamedArg :: ScanState -> NamedArg Binder -> ScanState
scanNamedArg scope (Arg _ (Named Nothing (Binder p (BName {boundName = a})))) = declareName False a scope'
  where
    scope' = case p of
      Nothing -> scope
      (Just p') -> scanPattern False scope p'
scanNamedArg scope (Arg _ (Named _ (Binder p (BName {})))) = scope' -- {a}
  where
    scope' = case p of
      Nothing -> scope
      (Just p') -> scanPattern True scope p'

scanTypedBinding :: ScanState -> TypedBinding -> ScanState
scanTypedBinding scope (TBind _ (a :| as) typ) = foldl scanNamedArg scope' (a : as)
  where
    scope' = scanExpr scope typ
scanTypedBinding scope (TLet _ (d :| ds)) = foldl scanDecl' scope (d : ds)

scanLamClause :: ScanState -> LamClause -> ScanState
scanLamClause state (LamClause lhs AbsurdRHS _) = addChildScope state withLhs
  where
    range = LSP.Range (LSP.Position 0 0) (LSP.Position 0 0)
    withLhs = foldl (scanPattern False) (childScope state range) lhs
scanLamClause state (LamClause lhs (RHS rhs) _) = addChildScope state $ scanExpr withLhs rhs
  where
    pos = case lhs of
      [] -> LSP.Position 0 0
      (p : _) -> posOfPattern p
    withLhs = foldl (scanPattern False) (childScope state (LSP.Range pos (endOfExpr rhs))) lhs

scanFieldAssigment :: ScanState -> FieldAssignment -> ScanState
scanFieldAssigment scope (FieldAssignment _ x) = scanExpr scope x

scanRecordAssignment :: ScanState -> RecordAssignment -> ScanState
scanRecordAssignment scope (Left x) = scanFieldAssigment scope x
-- TODO ModuleAssignment?
scanRecordAssignment scope (Right x) = scope

scanExpr :: ScanState -> Expr -> ScanState
scanExpr state (Ident x) = useSymQName (stateScope state) x state
scanExpr state (Lit _ _) = state
scanExpr state (QuestionMark _ _) = state
scanExpr state (Underscore _ _) = state
scanExpr state (RawApp _ (List2 a b c)) = foldl scanExpr state (a : b : c)
scanExpr state (App _ fun (Arg {unArg = Named {namedThing = arg}})) = argScope
  where
    funScope = scanExpr state fun
    argScope = scanExpr funScope arg
-- scanExpr state (OpApp _ _ _ args) = state
scanExpr state (WithApp _ e es) = foldl scanExpr state (e : es)
scanExpr state (HiddenArg _ Named {namedThing = arg}) = scanExpr state arg
scanExpr state (InstanceArg _ Named {namedThing = arg}) = scanExpr state arg
scanExpr state (Lam range (b :| bs) rhs) = addChildScope state $ scanExpr state' rhs
  where
    state' = foldl scanLamBinding (childScope state (toLSPRange' range)) (b : bs)
scanExpr state (AbsurdLam _ _) = state
scanExpr state (ExtendedLam _ _ (c :| cs)) = foldl scanLamClause state (c : cs)
scanExpr state (Fun _ (Arg _ x) y) = foldl scanExpr state [x, y]
scanExpr state (Pi (b :| bs) rhs) = addChildScope state $ scanExpr state'' rhs
  where
    state'' = childScope state (LSP.Range (posOfTypedBinding b) (endOfExpr rhs))
-- state'' = foldl scanTypedBinding state' (b : bs)
scanExpr state (Rec _ rs) = foldl scanRecordAssignment state rs
scanExpr state (RecUpdate _ r rs) = foldl scanFieldAssigment state' rs
  where
    state' = scanExpr state r
scanExpr state (Let range (d :| ds) e) = addChildScope state $ maybe state' (scanExpr state') e
  where
    state' = foldl scanDecl' (childScope state (toLSPRange' range)) (d : ds)
scanExpr state (Paren _ e) = scanExpr state e
scanExpr state (IdiomBrackets _ es) = foldl scanExpr state es
scanExpr state (DoBlock range (s :| ss)) = addChildScope state $ foldl scanDoStmt (childScope state (toLSPRange' range)) (s : ss)
  where
    scanDoStmt sc (DoBind _ lhs rhs cs) = scanPattern False sc2 lhs
      where
        sc' = foldl scanLamClause sc cs
        sc2 = scanExpr sc' rhs
    scanDoStmt sc (DoThen e) = scanExpr sc e
    scanDoStmt sc (DoLet _ (d :| ds)) = foldl scanDecl' sc (d : ds)
scanExpr state (Absurd _) = state
scanExpr state (As _ _ e) = scanExpr state e
scanExpr state (Dot _ e) = scanExpr state e
scanExpr state (DoubleDot _ e) = scanExpr state e
scanExpr state (Quote _) = state
scanExpr state (QuoteTerm _) = state
scanExpr state (Tactic _ e) = scanExpr state e
scanExpr state (Unquote _) = state
scanExpr state (DontCare x) = scanExpr state x
scanExpr state (Equal _ a b) = foldl scanExpr state [a, b]
scanExpr state (Ellipsis _) = state
scanExpr state (KnownIdent {}) = state
scanExpr state (KnownOpApp {}) = state
scanExpr state (Generalized x) = scanExpr state x
scanExpr state _ = state

data GroupedDecl = FuncDecl [Declaration] | SingleDecl Declaration deriving (Show)

noPartition :: [Declaration] -> [GroupedDecl]
noPartition = map SingleDecl

partitionByTypeSig :: [Declaration] -> [GroupedDecl]
partitionByTypeSig (d@(TypeSig {}) : decls) = FuncDecl (d : funClauses) : partitionByTypeSig rest
  where
    (funClauses, rest) = span isFunClause decls

    isFunClause (FunClause {}) = True
    isFunClause _ = False
partitionByTypeSig (d : ds) = SingleDecl d : partitionByTypeSig ds
partitionByTypeSig [] = []

foldlState :: (s -> x -> (s, y)) -> s -> [x] -> (s, [y])
foldlState f initState = foldl step (initState, [])
  where
    step (state, ys) x =
      let (newState, y) = f state x
       in (newState, ys ++ [y]) -- TODO ++ might be slow here

-- Implicits analysis

namePartsToString :: NameParts -> Maybe String
namePartsToString ((Id name) :| []) = Just name
namePartsToString _ = Nothing -- TODO in which cases does this happen?

nameToString :: Name -> Maybe String
nameToString (Name _ _ parts) = namePartsToString parts
nameToString (NoName _ _) = Nothing -- TODO when does this happen?

sigParamFromArgBinder :: Expr -> NamedArg Binder -> Maybe S.SigParam
sigParamFromArgBinder typ (Arg (ArgInfo {argInfoHiding = NotHidden}) (Named _ (Binder _ (BName {boundName = name})))) = S.SigExplicit typ <$ nameToString name
sigParamFromArgBinder typ (Arg (ArgInfo {argInfoHiding = Hidden}) (Named _ (Binder _ (BName {boundName = name})))) = case nameToString name of
  Nothing -> Nothing
  n -> Just $ S.SigImplicit n typ
sigParamFromArgBinder _ _ = Nothing

sigParamsFromTypedBinding :: TypedBinding -> [S.SigParam]
sigParamsFromTypedBinding (TBind _ (x :| xs) typ) = catMaybes ps
  where
    ps = sigParamFromArgBinder typ x : fmap (sigParamFromArgBinder typ) xs
sigParamsFromTypedBinding (TLet _ _) = [] -- TODO does this actually happen in a type signature?

sigParamsFromTelescope :: Telescope1 -> [S.SigParam]
sigParamsFromTelescope (x :| xs) = concat $ sigParamsFromTypedBinding x : fmap sigParamsFromTypedBinding xs

sigParamsFromExpr :: Expr -> [S.SigParam]
sigParamsFromExpr (Pi telescope rhs) = sigParamsFromTelescope telescope ++ sigParamsFromExpr rhs
sigParamsFromExpr (Fun _ (Arg _ lhs) rhs) = S.SigExplicit lhs : sigParamsFromExpr rhs
sigParamsFromExpr _ = []

sigParamsFromSigType :: Expr -> [S.SigParam]
sigParamsFromSigType (Generalized e) = sigParamsFromExpr e
sigParamsFromSigType _ = []

-- TODO if name is already used, use another name

-- import Relation.Binary.PropositionalEquality

-- foo = a

data IPattern = IApp LSP.Range (Maybe S.SymId) [S.SigParam] [IPattern] | IHidden LSP.Range (Maybe String) IPattern | IVar LSP.Range (Maybe String) (Maybe S.SymId) | IOther LSP.Range | IParen LSP.Range IPattern
  deriving (Show)

iPattern :: S.Scope -> Pattern -> IPattern
iPattern scope p = case p of
  WildP r -> IVar (toLSPRange' r) (Just "_") Nothing
  IdentP _ name -> case lookupSymQName scope name of
    Just (S.Symbol _ _ i (S.SConstr ps)) -> IApp r (Just i) ps []
    Just (S.Symbol _ _ i (S.SFunc ps _)) -> IApp r (Just i) ps []
    Just (S.Symbol _ _ i _) -> IVar r strN (Just i)
    _ -> IVar r strN Nothing
    where
      r = qnameRange name
      strN = case name of
        Qual {} -> Nothing
        QName (Name _ _ ((Id a) :| [])) -> Just a
        _ -> Nothing
  HiddenP r (Named Nothing x) -> IHidden (toLSPRange' r) Nothing $ ipat x
  HiddenP r (Named (Just (WithOrigin _ (Ranged _ n))) x) -> IHidden (toLSPRange' r) (Just n) $ ipat x
  ParenP r x -> IParen (toLSPRange' r) (ipat x)
  RawAppP _ (List2 (IdentP _ a) b c) -> IApp r i ps (fmap ipat (b : c))
    where
      r = qnameRange a
      sym = lookupSymQName scope a
      ps = maybe [] (S.symParams . S.getSym) sym
      i = fmap S.symId sym
  _ -> IOther (LSP.Range (LSP.Position 0 0) (LSP.Position 0 0)) -- TODO
  where
    ipat = iPattern scope

-- returns Nothing if they do not match
-- otherwise returns a list with the position
-- of each pattern on the params
matchPatternToParams :: [S.SigParam] -> [IPattern] -> Maybe [Int]
matchPatternToParams = matchPatternToParams_ 0

matchPatternToParams_ :: Int -> [S.SigParam] -> [IPattern] -> Maybe [Int]
matchPatternToParams_ _ ((S.SigExplicit {}) : _) (IHidden {} : _) = Nothing
matchPatternToParams_ i ((S.SigExplicit {}) : xs) (_ : ys) = ([i] ++) <$> matchPatternToParams_ (i + 1) xs ys
matchPatternToParams_ i ((S.SigImplicit {}) : xs) (IHidden _ Nothing _ : ys) = ([i] ++) <$> matchPatternToParams_ (i + 1) xs ys
matchPatternToParams_ i ((S.SigImplicit xName _) : xs) (y@(IHidden _ (Just yName) _) : ys) = if xName' == yName then t else f
  where
    xName' = fromMaybe "" xName
    t = ([i] ++) <$> matchPatternToParams_ (i + 1) xs ys
    f = matchPatternToParams_ (i + 1) xs (y : ys) -- try next
    -- in this case we have a pending implicit param but its pattern is not implicit, so we skip the pattern
matchPatternToParams_ i ((S.SigImplicit {}) : xs) (y : ys) = matchPatternToParams_ (i + 1) xs (y : ys)
matchPatternToParams_ _ _ [] = Just []
matchPatternToParams_ _ [] _ = Nothing

allRemovals :: ScanState -> LSP.Position -> Pattern -> [Removal]
allRemovals state l p = removals (`Set.member` un) False ip
  where
    ip = iPattern (S.innerMostScope l $ stateScope state) p
    un = Set.fromList $ fmap S.symId (unusedSymbols state)

allInsertions :: S.Scope -> LSP.Position -> LSP.Position -> Pattern -> [Insertion]
allInsertions scope l r p = allInsertions_ parens l r ip
  where
    ip = iPattern scope p
    parens = case ip of
      IApp {} -> False -- first IApp should not have parens
      _ -> True

allInsertions_ :: Bool -> LSP.Position -> LSP.Position -> IPattern -> [Insertion]
allInsertions_ parens _ r (IApp (LSP.Range l appR) _ ps []) = fmap (\(Insertion a b c _) -> Insertion a b c (if parens then Just (LSP.Range l appR) else Nothing)) xs
  where
    xs = possibleInsertions appR r ps []
allInsertions_ _ l r (IApp (LSP.Range _ appR) _ ps pats) = possibleInsertions appR r ps pats <> xs
  where
    xs = concatMap (allInsertions_ True l r) pats
allInsertions_ _ _ _ (IParen (LSP.Range l' r') p) = allInsertions_ False (incLSPPos l') (decLSPPos r') p
allInsertions_ _ _ _ _ = []

possibleInsertions :: LSP.Position -> LSP.Position -> [S.SigParam] -> [IPattern] -> [Insertion]
possibleInsertions l r ps pats = case matchPatternToParams ps pats of
  Nothing -> []
  Just idx -> _ins False l r idx 0 ps pats

ipatRng :: IPattern -> LSP.Range
ipatRng (IApp (LSP.Range a b) _ _ ps) = LSP.Range a y
  where
    y = case ps of
      [] -> b
      _ -> t
        where
          (LSP.Range _ t) = ipatRng $ last ps
ipatRng (IHidden r _ _) = r
ipatRng (IVar r _ _) = r
ipatRng (IOther r) = r
ipatRng (IParen r _) = r

ipatPos :: IPattern -> LSP.Position
ipatPos p = x
  where
    (LSP.Range x _) = ipatRng p

ipatEnd :: IPattern -> LSP.Position
ipatEnd p = x
  where
    (LSP.Range _ x) = ipatRng p

_ins :: Bool -> LSP.Position -> LSP.Position -> [Int] -> Int -> [S.SigParam] -> [IPattern] -> [Insertion]
_ins skipped l r idx i (p : ps) pats = case x == i of
  True -> _ins False l' r (tail idx) (i + 1) ps pats'
    where
      -- current index was a match so we discard
      (p', pats') = fdes pats
      l' = ipatEnd p'
  False -> res
    where
      -- current index not a match, which means a possible insertion

      -- if no patterns left we use the end position
      r' = case pats of
        [] -> r
        (p' : _) -> ipatPos p'

      res = case p of
        S.SigImplicit (Just name) _ -> Insertion (LSP.Range l r') name named' Nothing : rest
          where
            named' = if skipped then Just name else Nothing
            rest = _ins True l r idx (i + 1) ps pats
        S.SigImplicit {} -> []
        S.SigExplicit {} -> []
  where
    x = case idx of
      [] -> -1 -- cannot equal i
      (v : _) -> v
_ins _ _ _ _ _ [] _ = []

fdes :: [a] -> (a, [a])
fdes (x : xs) = (x, xs)
fdes [] = error "bad"

data Insertion = Insertion LSP.Range String (Maybe String) (Maybe LSP.Range) deriving (Show, Eq)

-- Find the clause that contains the cursor position
-- and return the implicits that can be inserted
insertableImplicits :: ScanState -> Module -> LSP.Position -> [(String, LSP.Range, Maybe LSP.Range)]
insertableImplicits ss modl pos = case findFunClausePat pos modl of
  Nothing -> []
  Just (pat, l, r) -> mapMaybe pred' ins
    where
      ins = allInsertions (S.innerMostScope l (stateScope ss)) l r pat
      -- pred' (Insertion _  Nothing _) = Nothing
      pred' (Insertion r' txt Nothing parens) = Just (txt, r', parens)
      pred' (Insertion r' txt (Just name) parens) = Just (name ++ " = " ++ txt, r', parens)

removableVars :: ScanState -> Module -> LSP.Position -> [(String, Bool, LSP.Range, Maybe (LSP.Range, String), Maybe LSP.Range)]
removableVars ss modl pos = case findFunClausePat pos modl of
  Nothing -> []
  Just (pat, l, _) -> map pred' ins
    where
      ins = allRemovals ss l pat

      pred' (Removal name whole r insName parens) = (name, whole, r, insName, parens)

findFunClausePat :: LSP.Position -> Module -> Maybe (Pattern, LSP.Position, LSP.Position)
findFunClausePat p modl = doneAsMaybe $ foldModule fn modl
  where
    fn (D d@(FunClause (LHS {lhsOriginalPattern = pat}) _ _ _)) = if containsPos p d then Done (pat, LSP.Position l 0, incLSPPos r') else Continue
      where
        (LSP.Range (LSP.Position l _) r') = toLSPRange' $ getRange pat
    fn _ = Continue

-- first Bool is True if it does not add a _ after removing
data Removal = Removal String Bool LSP.Range (Maybe (LSP.Range, String)) (Maybe LSP.Range) deriving (Show, Eq)

-- Ahora necesito hacer Removals. Lo obvio es que necesito agregar
-- uses en IVar. Lo siguiente es proponer un Removal pa cada IVar
-- que esta unused. Si es que esta dentro de un Hidden o Paren
-- entonces tengo que eliminarlo entero. El otro tema es que
-- si es que es positional hidden, entonces necesito
-- agregarle un equal al siguiente implicit (solo si se puede namear)
-- si no se elimina dejando paren no mas.

removals :: (S.SymId -> Bool) -> Bool -> IPattern -> [Removal]
removals = _rem

_rem :: (S.SymId -> Bool) -> Bool -> IPattern -> [Removal]
_rem isUnused rmHid p = case p of
  IVar r (Just name) (Just i) -> [Removal name False r Nothing Nothing | isUnused i]
  IParen r x@(IApp _ _ _ [_]) -> case _rem isUnused rmHid x of
    [Removal a True c d _] -> [Removal a True c d (Just r)]
    rs -> rs
  IParen _ x -> _rem isUnused rmHid x
  IHidden r _ x -> case _rem isUnused rmHid x of
    [Removal a b c d e] -> if rmHid && rmWhole x then [Removal a True r Nothing e] else [Removal a b c d e]
    rs -> rs
  IApp rn _ ps pats -> concatMap fRem nxt
    where
      names = case matchPatternToParams ps pats of
        Nothing -> fmap (const Nothing) pats
        Just is -> fmap (nameP . (ps !!)) is

      nameP (S.SigExplicit {}) = Nothing
      nameP (S.SigImplicit n _) = n

      (LSP.Range _ r) = rn
      nxt = zip3 (r : map ipatEnd pats) pats (map Just (tail $ zip pats names) ++ [Nothing])

      fRem (l, p', next) = case (rmWhole p', _rem isUnused True p') of
        (True, [Removal name True (LSP.Range _ b) c d]) -> case next of
          Nothing -> [Removal name True (LSP.Range l b) c d] -- at end, no effect on next
          Just (IHidden {}, Nothing) -> _rem isUnused False p' -- next has no name, so we must preserve hidden
          Just (IHidden (LSP.Range nl _) pName _, Just n) -> [Removal name True (LSP.Range l b) insName d] -- next has name, we must insert name on next
            where
              namePos = LSP.Range (incLSPPos nl) (incLSPPos nl)
              insName = case pName of
                Nothing -> Just (namePos, n)
                Just _ -> Nothing
          _ -> [Removal name True (LSP.Range l b) c d]
        (_, rs) -> rs
  _ -> []
  where
    rmWhole p' = case p' of
      IVar {} -> True
      IParen _ x -> rmWhole x
      IHidden _ _ x -> rmWhole x
      _ -> False

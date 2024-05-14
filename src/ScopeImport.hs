module ScopeImport (State, emptyState, resolveAllModules) where
import Agda.Syntax.Scope.Base
import Agda.Interaction.Options qualified as AO
import Scope
import ScopeMap qualified as SMap
import Agda.Compiler.Backend
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.HashMap.Strict qualified as HMap
import Agda.Syntax.Internal
import Agda.Syntax.Scope.Base qualified as AS
import Agda.TypeChecking.Telescope (telView)
import Agda.TypeChecking.Substitute (TelV(TelV))
import Agda.Syntax.Common (ArgInfo(ArgInfo, argInfoHiding), Hiding (Hidden, NotHidden, Instance))
import Agda.Syntax.Concrete qualified as C
import Agda.Utils.List1 (NonEmpty ((:|)))
import Data.Maybe (catMaybes, isJust)
import Language.LSP.Protocol.Types qualified as LSP
import Agda.Syntax.Common.Pretty (Pretty(pretty))
import Traversal (foldModule, Node (D))
import Agda.Interaction.Imports (parseSource, typeCheckMain, Mode (TypeCheck), scopeCheckImport)
import Agda.Interaction.FindFile (SourceFile(SourceFile))
import Agda.Utils.FileName (mkAbsolute)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Agda.Syntax.Scope.Monad (resolveModule)
import Control.Monad.Except (MonadError(catchError))
import Debug.Trace (trace)
import Colog.Core ( (<&), logStringStderr )
import System.Directory (createDirectoryIfMissing)
import System.FilePath (takeDirectory)
import Agda.Syntax.TopLevelModuleName (rawTopLevelModuleNameForQName)
import Agda.Syntax.Translation.ConcreteToAbstract (NewModuleQName(NewModuleQName), ToAbstract (toAbstract))
import System.CPUTime (getCPUTime)

-- Here we turn Agda Names and scopes into our own names and scope representations
-- to implement imports

data State = State TCState SymId (Map.Map AgdaAbs Symbol)

type AScopes = Map.Map ModuleName Agda.Syntax.Scope.Base.Scope

emptyState :: State
emptyState = State initState (SymId 1000000) Map.empty

getTCS :: State -> TCState
getTCS (State x _ _) = x

setTCS :: TCState -> State -> State
setTCS x (State _ a b) = State x a b

scopeOfSym :: Symbol -> Scope.Scope
scopeOfSym (Symbol _ _ _ (Scope.SModl _ (Scope.Modl m))) = m
scopeOfSym _ = error "not a module"

newSymbol :: State -> String -> AgdaAbs -> Sym -> (Symbol, State)
newSymbol (State tcstate (SymId nxt) scache) aname aabs sym = (symbol, State tcstate (SymId $ nxt+1) scache')
    where
        z = LSP.Range (LSP.Position 0 0) (LSP.Position 0 0)
        symbol = Symbol z aname (SymId nxt) sym
        scache' = Map.insert aabs symbol scache

collectImports :: C.Module -> (Set.Set C.QName, [C.QName])
collectImports = foldModule fn
    where
        fn (D (C.Import _ name _ _ _)) = (Set.fromList [name], [name])
        fn (D (C.Open _ name _)) = (Set.fromList [name], [name])
        fn _ = (Set.empty, [])

maybeError :: (Show e, MonadError e m) => m a -> m (Maybe a)
maybeError x = catchError (Just <$> x) (\e -> trace (show e) $ return Nothing)

fakeImport :: C.QName -> TCM (Maybe (ModuleName, Definitions, AScopes))
fakeImport name = do
    top <- topLevelModuleName $ rawTopLevelModuleNameForQName name
    mname <- toAbstract $ NewModuleQName name
    res <- maybeError $ scopeCheckImport top mname
    case res of
        Nothing -> return Nothing
        Just (m, scopes) -> do
            sig <- useTC stImports
            let defs = _sigDefinitions sig
            return $ Just (m, defs, scopes)
    -- let tmpFile = tmpDir ++ "/" ++ "tmp.agda"
    -- liftIO $ createDirectoriesForFile tmpFile
    -- liftIO $ writeFile tmpFile ("import " ++ show (pretty name))

    -- let name' = (filter (/= '.') . show . pretty) name'
    -- let tmpFile = tmpDir ++ "/" ++ name' ++ "/" ++ name' ++ ".agda"
    -- liftIO $ createDirectoriesForFile tmpFile
    -- liftIO $ writeFile tmpFile ("import " ++ show (pretty name))

    -- src <- parseSource (SourceFile (mkAbsolute tmpFile))
    -- setCommandLineOptions' (mkAbsolute tmpDir) AO.defaultOptions
    -- res <- typeCheckMain TypeCheck src

    -- let iface = crInterface res
    -- let scope = iInsideScope iface
    -- sig <- useTC stImports
    -- setScope scope
    -- amod <- maybeError $ resolveModule name
    -- case amod of
    --     Nothing -> return Nothing
    --     Just x -> return $ Just (x, _sigDefinitions sig, AS._scopeModules scope)

maybeMap :: Ord k => [k] -> [Maybe v] -> Map.Map k v
maybeMap ks vs =
    let paired = zip ks vs
        filtered = filter (isJust . snd) paired
        tf = map (\(a, Just b) -> (a, b)) filtered
    in Map.fromList tf

resolveAllModules :: C.Module -> State -> IO (Map.Map C.QName Scope.Symbol, [C.QName], State)
resolveAllModules modl state = do
    let (imports, names) = collectImports modl
    ((res, state'), tcstate) <- runTCM initEnv (getTCS state) (resolveModuleCNames (Set.toList imports) state)
    let resMap = maybeMap (Set.toList imports) res
    let notFounds = filter (not <$> (`Map.member` resMap)) names
    return (resMap, notFounds, setTCS tcstate state')

resolveModuleCNames :: [C.QName] -> State -> TCM ([Maybe Scope.Symbol], State)
resolveModuleCNames [] state = return ([], state)
resolveModuleCNames (x:xs) state = do
    (s, state') <- resolveModuleCName x state
    (rest, state'') <- resolveModuleCNames xs state'
    return (s : rest, state'')

resolveModuleCName :: C.QName -> State -> TCM (Maybe Scope.Symbol, State)
resolveModuleCName name state = do
    startTime <- liftIO getCPUTime
    imp <- fakeImport name
    stopTime <- liftIO getCPUTime
    logStringStderr <& ("Duration: " <> show ((stopTime - startTime) `div` 1000000000) <> "ms")
    case imp of
        Nothing -> return (Nothing, state)
        Just (modl, defs, scopes) -> do
            (sym, state') <- agdaAbsToSym defs scopes state (AbsM modl)
            case sym of
                Nothing -> return (Nothing, state')
                Just sym' -> return (Just sym', state')

moduleToScope :: Definitions -> AScopes -> State -> ModuleName -> TCM (Scope.Scope, State)
moduleToScope defs scopes state@(State _ _ scache) name = case Map.lookup (AbsM name) scache of
    Just res -> return (scopeOfSym res, state)
    Nothing -> do
        let names = publicAgdaAbs $ (Map.!) scopes name
        (syms, state') <- foldState (namedAgdaAbs defs scopes) state names -- mapM (namedAgdaAbs defs state) names
        let syms' = fmap (\(n, ss) -> (show $ pretty n, ss)) syms
        let z = LSP.Range (LSP.Position 0 0) (LSP.Position 0 0)
        let r = LSP.Range (LSP.Position 0 0) (LSP.Position 100000 100000)
        let scope = Scope.Scope r Nothing [] (SMap.fromList z syms')
        return (scope, state')

definitionToSym :: Definition -> TCM (Maybe Sym)
definitionToSym def = do
    params <- typeToSigParams $ defType def
    return $ case theDef def of
        FunctionDefn {} -> Just $ SFunc params []
        ConstructorDefn {} -> Just $ SConstr params
        _ -> Nothing

typeToSigParams :: Type -> TCM [SigParam]
typeToSigParams typ = do
    TelV tele _ <- telView typ
    return $ teleToSigParams tele

teleToSigParams :: Tele (Dom Type) -> [SigParam]
teleToSigParams tele = case tele of
    EmptyTel -> []
    ExtendTel (Dom {domInfo = (ArgInfo {argInfoHiding = hiding})}) (Abs name nxt) -> p : teleToSigParams nxt
        where
            dummy = C.Ident $ C.QName $ C.simpleName "_"
            p = case hiding of
                Hidden -> SigImplicit (if name == "" then Nothing else Just name) dummy
                NotHidden -> SigExplicit dummy
                Instance {} -> SigImplicit Nothing dummy -- TODO
    _ -> error "NoAbs never happens"

namedAgdaAbs :: Definitions -> AScopes -> State -> (C.Name, [AgdaAbs]) -> TCM ((C.Name, [Symbol]), State)
namedAgdaAbs defs scopes state (name, x) = do
    (res, state') <- foldState (agdaAbsToSym defs scopes) state x
    return ((name, catMaybes res), state')

foldState :: (State -> a -> TCM (b, State)) -> State -> [a] -> TCM ([b], State)
foldState _ state [] = return ([], state)
foldState fn state (x:xs) = do
    (res, state') <- fn state x
    (res', state'') <- foldState fn state' xs
    return (res : res', state'')

agdaAbsToSym :: Definitions -> AScopes -> State -> AgdaAbs -> TCM (Maybe Symbol, State)
agdaAbsToSym defs scopes s@(State _ _ scache) (AbsM n) = case Map.lookup (AbsM n) scache of
    Just x -> return (Just x, s)
    Nothing -> do
        (scope, s') <- moduleToScope defs scopes s n
        let (symbol, s'') = newSymbol s' (show . pretty $ n) (AbsM n) (SModl [] (Modl scope))
        return (Just symbol, s'')
agdaAbsToSym defs _ s@(State _ _ scache) (AbsN n) = case Map.lookup (AbsN n) scache of
    Just x -> return (Just x, s)
    Nothing -> do
        case HMap.lookup n defs of
            Nothing -> do -- not found in definition, just use name
                let sym = SExpl
                let (symbol, s') = newSymbol s (show . pretty $ n) (AbsN n) sym
                return (Just symbol, s')
            Just def -> do
                sym <- definitionToSym def
                case sym of
                    Nothing -> return (Nothing, s)
                    Just sym' -> return (Just symbol, s')
                        where
                            (symbol, s') = newSymbol s (show . pretty $ n) (AbsN n) sym'

publicNamespaces :: Agda.Syntax.Scope.Base.Scope -> [NameSpace]
publicNamespaces scope = fmap snd fns
  where
    ns = scopeNameSpaces scope
    fns = filter (\(a, _) -> a == PublicNS) ns

data AgdaAbs = AbsM ModuleName | AbsN QName deriving (Eq, Ord, Show)

publicAgdaAbs :: Agda.Syntax.Scope.Base.Scope -> [(C.Name, [AgdaAbs])]
publicAgdaAbs scope = nsn ++ nsm
  where
    ns = publicNamespaces scope
    nsn = (\(a, b :| bs) -> (a, fmap (AbsN . anameName) $ b : bs)) <$> concatMap (Map.toList . nsNames) ns
    nsm = (\(a, b :| bs) -> (a, fmap (AbsM . amodName) $ b : bs)) <$> concatMap (Map.toList . nsModules) ns

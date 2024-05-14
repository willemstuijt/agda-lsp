module ImplicitsScope
  ( parseVFSFile,
    checkVFSFile,
    implicitsScopeFromModule,
    emptyImplicits,
    unusedImplicits,
    implicitDefById,
    implicitDefByRange,
    printFile,
    ImplicitId (ImplicitId),
    ImplicitsScope (ImplicitsScope),
    ImplicitDef (ImplicitDef),
    ImplicitUse (ImplicitUse),
  )
where

import Agda.Compiler.Backend (TCM, runTCM, runTCMTop')
import Agda.Interaction.FindFile (SourceFile (SourceFile))
import Agda.Interaction.Imports (CheckResult, Mode (ScopeCheck), parseSource, typeCheckMain)
import Agda.Syntax.Common
import Agda.Syntax.Concrete
import Agda.Syntax.Parser
import Agda.Syntax.Position
import Agda.Syntax.Translation.ConcreteToAbstract (ToAbstract (toAbstract), TopLevel (TopLevel))
import Agda.Utils.FileName
import Agda.Utils.List1 (NonEmpty ((:|)))
import Agda.Utils.List2 (List2 (List2))
import AgdaToLSP (toLSPRange, toLSPRange', toLSPPosition, incLSPPos)
import Control.Monad.IO.Class (liftIO)
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set qualified as Set
import Data.Text (pack, unpack)
import ImplicitsDecls (insertableImplicits, partitionByTypeSig)
import Language.LSP.Protocol.Types qualified as LSP
import Agda.Interaction.Options.Lenses (LensCommandLineOptions(getCommandLineOptions))

newtype ImplicitId = ImplicitId Int deriving (Show, Eq, Ord)

incId :: ImplicitId -> ImplicitId
incId (ImplicitId x) = ImplicitId $ x + 1

data ImplicitDef = ImplicitDef LSP.Range ImplicitId String deriving (Show)

data ImplicitUse = ImplicitUse LSP.Range ImplicitId deriving (Show)

data ImplicitsScope = ImplicitsScope [ImplicitDef] [ImplicitUse] (Map.Map String ImplicitId) ImplicitId deriving (Show)

emptyImplicits :: ImplicitsScope
emptyImplicits = ImplicitsScope [] [] Map.empty (ImplicitId 0)

oldScope :: ImplicitsScope -> ImplicitsScope -> ImplicitsScope
oldScope (ImplicitsScope _ _ scope _) (ImplicitsScope a b _ c) = ImplicitsScope a b scope c

defineImplicit :: LSP.Range -> String -> ImplicitsScope -> ImplicitsScope
defineImplicit range name (ImplicitsScope defs uses scope curId) = ImplicitsScope newDefs uses newScope (incId curId)
  where
    newDefs = ImplicitDef range curId name : defs
    newScope = Map.insert name curId scope

shadowImplicit :: String -> ImplicitsScope -> ImplicitsScope
shadowImplicit name (ImplicitsScope defs uses scope curId) = ImplicitsScope defs uses newScope curId
  where
    newScope = Map.delete name scope

-- Adds implicit use if in scope, otherwise ignores
useImplicit :: LSP.Range -> String -> ImplicitsScope -> ImplicitsScope
useImplicit range name old@(ImplicitsScope defs uses scope curId) = case Map.lookup name scope of
  Just varId -> ImplicitsScope defs (ImplicitUse range varId : uses) scope curId
  Nothing -> old

unusedImplicits :: ImplicitsScope -> [ImplicitDef]
unusedImplicits (ImplicitsScope defs uses _ _) = unusedDefs (reverse defs) (ImplicitId 0)
  where
    used = Set.fromList (fmap (\(ImplicitUse _ x) -> x) uses)

    unusedDefs (x : xs) idx = if Set.member idx used then unusedDefs xs (incId idx) else x : unusedDefs xs (incId idx)
    unusedDefs [] _ = []

implicitDefById :: ImplicitsScope -> ImplicitId -> Maybe ImplicitDef
implicitDefById (ImplicitsScope defs _ _ _) implicitId = List.find (\(ImplicitDef _ i _) -> i == implicitId) defs

implicitDefByRange :: ImplicitsScope -> LSP.Range -> Maybe ImplicitDef
implicitDefByRange (ImplicitsScope defs _ _ _) range = List.find (\(ImplicitDef r _ _) -> r == range) defs

indent :: Int -> String -> String
indent level ('(' : ')' : rest) = '(' : ')' : indent level rest
indent level ('[' : ']' : rest) = '[' : ']' : indent level rest
indent level ('{' : '}' : rest) = '{' : '}' : indent level rest
indent level ('(' : rest) = ('(' : '\n' : replicate (level * 2) ' ') ++ indent (level + 1) rest
indent level ('[' : rest) = ('[' : '\n' : replicate (level * 2) ' ') ++ indent (level + 1) rest
indent level ('{' : rest) = ('{' : '\n' : replicate (level * 2) ' ') ++ indent (level + 1) rest
indent level (')' : rest) = ('\n' : replicate ((level - 2) * 2) ' ') ++ (')' : indent (level - 1) rest)
indent level (']' : rest) = ('\n' : replicate ((level - 2) * 2) ' ') ++ (']' : indent (level - 1) rest)
indent level ('}' : rest) = ('\n' : replicate ((level - 2) * 2) ' ') ++ ('}' : indent (level - 1) rest)
indent level (x : rest) = x : indent level rest
indent _ [] = []

printFile :: AbsolutePath -> String -> IO ()
printFile path fileContent = do
  let tmp = parseFile moduleParser (mkRangeFile path Nothing) fileContent
  (res, _) <- liftIO $ runPMIO tmp
  case res of
    (Left _) -> print "error parsing"
    (Right ((modl, _), _)) -> do
      let decls = modDecls modl
      let part = partitionByTypeSig decls
      print $ show (insertableImplicits part (LSP.Position 1 15))
      print $ show (partitionByTypeSig decls)
      writeFile "/home/willem/Documents/plfa/test.txt" $ indent 0 (show decls)

checkVFSFile :: AbsolutePath -> TCM CheckResult
checkVFSFile path = do
  src <- parseSource (SourceFile path)
  -- options <- getCommandLineOptions
  typeCheckMain ScopeCheck src

parseVFSFile :: AbsolutePath -> String -> IO (Either (LSP.Range, String) Module)
parseVFSFile path fileContent = do
  let tmp = parseFile moduleParser (mkRangeFile path Nothing) fileContent
  (res, _) <- liftIO $ runPMIO tmp
  case res of
    (Left (ParseError {errPos=errPos, errMsg=errMsg})) -> return $ Left (LSP.Range (toLSPPosition errPos) (incLSPPos $ toLSPPosition errPos), errMsg)
    (Left _) -> return $ Left (LSP.Range (LSP.Position 0 0) (LSP.Position 0 0), "")
    (Right ((modl, _), _)) -> do
      return $ Right modl

implicitsScopeFromModule :: Module -> ImplicitsScope
implicitsScopeFromModule modl = foldl (scanDecl True) emptyImplicits decls
  where
    decls = modDecls modl

condOldScope :: Bool -> ImplicitsScope -> ImplicitsScope -> ImplicitsScope
condOldScope True a b = oldScope a b
condOldScope False _ x = x

-- True if we should remove any declared variables
-- from the pattern. We need this since Let expressions
-- use a list of Declarations and the lhs patterns must be
-- kept to later check the Let rhs.
scanDecl :: Bool -> ImplicitsScope -> Declaration -> ImplicitsScope
scanDecl stop scope (Module _ _ _ _ decls) = foldl (scanDecl stop) scope decls
scanDecl stop scope (FunClause (LHS {lhsOriginalPattern = p}) (RHS rhs) _ _) = condOldScope stop scope $ scanExpr withLhs rhs
  where
    withLhs = scanPattern False scope p
scanDecl _ scope _ = scope

scanNamedImplicit :: ImplicitsScope -> (Range, Named_ Pattern) -> ImplicitsScope
scanNamedImplicit scope (range, Named {nameOf = Nothing, namedThing = p}) = case toLSPRange range of
  Just lspRange -> defineImplicit lspRange (patternName p) scope
  _ -> scope
scanNamedImplicit scope (range, Named {nameOf = (Just name), namedThing = p}) = case toLSPRange range of
  Just lspRange -> defineImplicit lspRange (patternName p) scope
  _ -> scope

scanNamedPattern :: Bool -> ImplicitsScope -> NamedArg Pattern -> ImplicitsScope
scanNamedPattern scope impl (Arg {unArg = Named {namedThing = p}}) = scanPattern scope impl p

-- True means we are inside a HiddenP so Idents are declared as hidden
-- otherwise we simply shadow the name
scanPattern :: Bool -> ImplicitsScope -> Pattern -> ImplicitsScope
scanPattern False scope (IdentP _ (QName name)) = shadowImplicit name' scope
  where
    (_, name') = unpackName name
scanPattern True scope (IdentP _ (QName name)) = defineImplicit range name' scope
  where
    (range, name') = unpackName name
scanPattern _ scope (QuoteP _) = scope
scanPattern impl scope (AppP fun arg) = argScope
  where
    funScope = scanPattern impl scope fun
    argScope = scanNamedPattern impl funScope arg
scanPattern impl scope (RawAppP _ (List2 a b c)) = foldl (scanPattern impl) scope (a : b : c)
scanPattern _ scope (HiddenP range (Named {namedThing = p})) = case toLSPRange range of
  Just lspRange -> defineImplicit lspRange (patternName p) scope
  _ -> scope
scanPattern impl scope (ParenP _ p) = scanPattern impl scope p
scanPattern _ scope (WildP _) = scope
scanPattern _ scope (AbsurdP _) = scope
scanPattern impl scope (AsP _ name p) = shadowImplicit name' scope'
  where
    (_, name') = unpackName name
    scope' = scanPattern impl scope p
scanPattern _ scope (DotP _ _) = scope
scanPattern _ scope (LitP _ _) = scope
scanPattern _ scope (EqualP _ _) = scope
-- -- EllipsisP ?
-- -- WithP ?
scanPattern _ scope _ = scope

scanNamedArg :: ImplicitsScope -> NamedArg Binder -> ImplicitsScope
scanNamedArg scope (Arg _ (Named Nothing (Binder p (BName {boundName = a})))) = shadowImplicit name scope' -- a or a@p
  where
    (_, name) = unpackName a
    scope' = case p of
      Nothing -> scope
      (Just p') -> scanPattern False scope p'
scanNamedArg scope (Arg _ (Named _ (Binder p (BName {})))) = scope' -- {a}
  where
    scope' = case p of
      Nothing -> scope
      (Just p') -> scanPattern True scope p'

scanTypedBinding :: ImplicitsScope -> TypedBinding -> ImplicitsScope
scanTypedBinding scope (TBind _ (a :| as) typ) = foldl scanNamedArg scope' (a : as)
  where
    scope' = scanExpr scope typ
scanTypedBinding scope (TLet _ (d :| ds)) = foldl (scanDecl False) scope (d : ds)

scanLamClause :: Bool -> ImplicitsScope -> LamClause -> ImplicitsScope
scanLamClause stop scope (LamClause lhs AbsurdRHS _) = condOldScope stop scope withLhs
  where
    withLhs = foldl (scanPattern False) scope lhs
scanLamClause stop scope (LamClause lhs (RHS rhs) _) = condOldScope stop scope $ scanExpr withLhs rhs
  where
    withLhs = foldl (scanPattern False) scope lhs

scanLamBinding :: ImplicitsScope -> LamBinding -> ImplicitsScope
scanLamBinding scope (DomainFree a) = scanNamedArg scope a
scanLamBinding scope (DomainFull a) = scanTypedBinding scope a

scanFieldAssigment :: ImplicitsScope -> FieldAssignment -> ImplicitsScope
scanFieldAssigment scope (FieldAssignment _ x) = scanExpr scope x

scanRecordAssignment :: ImplicitsScope -> RecordAssignment -> ImplicitsScope
scanRecordAssignment scope (Left x) = scanFieldAssigment scope x
-- TODO ModuleAssignment?
scanRecordAssignment scope (Right x) = scope

scanExpr :: ImplicitsScope -> Expr -> ImplicitsScope
scanExpr scope (Ident (QName n)) = useImplicit range name scope
  where
    (range, name) = unpackName n
scanExpr scope (Ident _) = scope
scanExpr scope (Lit _ _) = scope
scanExpr scope (QuestionMark _ _) = scope
scanExpr scope (Underscore _ _) = scope
scanExpr scope (RawApp _ (List2 a b c)) = foldl scanExpr scope (a : b : c)
scanExpr scope (App _ fun (Arg {unArg = Named {namedThing = arg}})) = argScope
  where
    funScope = scanExpr scope fun
    argScope = scanExpr funScope arg
-- scanExpr scope (OpApp _ _ _ args) = scope
scanExpr scope (WithApp _ e es) = foldl scanExpr scope (e : es)
scanExpr scope (HiddenArg _ Named {namedThing = arg}) = scanExpr scope arg
scanExpr scope (InstanceArg _ Named {namedThing = arg}) = scanExpr scope arg
scanExpr scope (Lam _ (b :| bs) rhs) = oldScope scope $ scanExpr scope' rhs
  where
    scope' = foldl scanLamBinding scope (b : bs)
scanExpr scope (AbsurdLam _ _) = scope
scanExpr scope (ExtendedLam _ _ (c :| cs)) = foldl (scanLamClause True) scope (c : cs)
scanExpr scope (Fun _ (Arg _ x) y) = foldl scanExpr scope [x, y]
scanExpr scope (Pi (b :| bs) rhs) = oldScope scope $ scanExpr scope' rhs
  where
    scope' = foldl scanTypedBinding scope (b : bs)
scanExpr scope (Rec _ rs) = foldl scanRecordAssignment scope rs
scanExpr scope (RecUpdate _ r rs) = foldl scanFieldAssigment scope' rs
  where
    scope' = scanExpr scope r
scanExpr scope (Let _ (d :| ds) e) = maybe scope' (scanExpr scope') e
  where
    scope' = foldl (scanDecl False) scope (d : ds)
scanExpr scope (Paren _ e) = scanExpr scope e
scanExpr scope (IdiomBrackets _ es) = foldl scanExpr scope es
scanExpr scope (DoBlock _ (s :| ss)) = foldl scanDoStmt scope (s : ss)
  where
    scanDoStmt sc (DoBind _ lhs rhs cs) = scanPattern False sc2 lhs
      where
        sc' = foldl (scanLamClause True) sc cs
        sc2 = oldScope sc $ scanExpr sc' rhs
    scanDoStmt sc (DoThen e) = scanExpr sc e
    scanDoStmt sc (DoLet _ (d :| ds)) = foldl (scanDecl False) sc (d : ds)
scanExpr scope (Absurd _) = scope
scanExpr scope (As _ _ e) = scanExpr scope e
scanExpr scope (Dot _ e) = scanExpr scope e
scanExpr scope (DoubleDot _ e) = scanExpr scope e
scanExpr scope (Quote _) = scope
scanExpr scope (QuoteTerm _) = scope
scanExpr scope (Tactic _ e) = scanExpr scope e
scanExpr scope (Unquote _) = scope
scanExpr scope (DontCare x) = scanExpr scope x
scanExpr scope (Equal _ a b) = foldl scanExpr scope [a, b]
scanExpr scope (Ellipsis _) = scope
scanExpr scope (KnownIdent {}) = scope
scanExpr scope (KnownOpApp {}) = scope
scanExpr scope _ = scope

patternName :: Pattern -> String
patternName (IdentP _ (QName (Name {nameNameParts = ((Id a) :| [])}))) = a
patternName _ = ""

unpackName :: Name -> (LSP.Range, String)
unpackName (Name {nameRange = range, nameNameParts = ((Id a) :| [])}) = (toLSPRange' range, a)
-- TODO what happens when NameParts is not a single Id?
unpackName (Name {nameRange = range, nameNameParts = names}) = (toLSPRange' range, show names)
unpackName (NoName {nameRange = range}) = (toLSPRange' range, "_")

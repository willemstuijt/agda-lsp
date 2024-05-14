{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}

module CodeActions (makeCodeActions) where

import Data.Map qualified as Map
import Colog.Core ( (<&), logStringStderr )
import Control.Lens ((^.))
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.IORef (IORef, readIORef)
import Language.LSP.Protocol.Lens (HasUri (uri))
import Language.LSP.Protocol.Types
import Language.LSP.Server
import State
import Diagnostics (diagnosticKindFromJSON, diagnosticKindFromJSON', DiagnosticKind (DiagnosticUnused))
import ImplicitsScope (ImplicitDef (ImplicitDef), ImplicitsScope, implicitDefById)
import Data.Text (pack)
import Data.Maybe (mapMaybe, isNothing, isJust)
import Agda.Syntax.Concrete (Module(modDecls))
import Scope (allSymbols, SymId, Symbol (Symbol))
import ScopeAnalysis (ScanState(ScanState), insertableImplicits, removableVars)
import AgdaToLSP (incLSPPos, decLSPPos)

makeCodeActions :: CodeActionParams -> IORef State -> LspT () IO [Command |? CodeAction]
makeCodeActions (CodeActionParams _ _ doc (Range pos _) (CodeActionContext diagnostics _ _)) stateRef = do
  logStringStderr <& "sendCodeActions ..."

  let fileUri = doc ^. uri
  state <- liftIO $ readIORef stateRef

  case getFileStateByUri state fileUri of
    Just (FileState _ (Right modl) _ ss@(ScanState _ _ scope _)) -> do
      let allSyms = allSymbols scope
      let diagnosticActions = mapMaybe (diagnosticToImplicit fileUri allSyms) diagnostics

      let insertImplicitActions = implicitInsertCodeAction fileUri <$> insertableImplicits ss modl pos
      let removeImplicitActions = implicitRemoveCodeAction fileUri <$> removableVars ss modl pos

      let codeActions = insertImplicitActions ++ removeImplicitActions
      return codeActions
    _ -> return []

diagnosticToImplicit :: Uri -> Map.Map SymId Symbol -> Diagnostic -> Maybe (Command |? CodeAction)
diagnosticToImplicit fileUri scope d@(Diagnostic _ _ _ _ _ _ _ _ value) = case diagnosticKindFromJSON' value of
  Just (DiagnosticUnused i) -> case Map.lookup i scope of
    Just def -> Just $ unusedSymToCodeAction fileUri (Just [d]) def
    Nothing -> Nothing
  Nothing -> Nothing

-- let implicits = unusedImplicits scope
-- let diagnosticList = fmap (implicitToDiagnostic fileUri) implicits
-- publishDiagnostics 100 (toNormalizedUri fileUri) version (partitionBySource diagnosticList)


createWorkspaceEdit :: Uri -> TextEdit -> WorkspaceEdit
createWorkspaceEdit file_uri textEdit = WorkspaceEdit (Just $ Map.singleton file_uri [textEdit]) Nothing Nothing

unusedSymToCodeAction :: Uri -> Maybe [Diagnostic] -> Symbol -> Command |? CodeAction
unusedSymToCodeAction file_uri diagnostics (Symbol range name _ _) = InR $ CodeAction (pack ("Remove unused implicit {" ++ name ++ "}")) (Just CodeActionKind_QuickFix) diagnostics Nothing Nothing (Just $ createWorkspaceEdit file_uri (TextEdit range "")) Nothing Nothing

implicitInsertCodeAction :: Uri -> (String, Range, Maybe Range) -> Command |? CodeAction
implicitInsertCodeAction file_uri (name, range, parens) = InR $ CodeAction text Nothing Nothing Nothing Nothing (Just wsEdit) Nothing Nothing
  where
    text = pack $ "Make implicit '" ++ name ++ "' explicit"
    (Range l r) = range
    insEdit = " {" ++ name ++ (if l == r || isJust parens then "}" else "} ") ++ case parens of
      Nothing -> ""
      Just _ -> ") "
    textEdit = TextEdit range (pack insEdit)
    parensEdit = case parens of
      Nothing -> []
      Just (Range l' _) -> [TextEdit (Range l' l') (pack "(")]
    wsEdit = WorkspaceEdit (Just $ Map.singleton file_uri (parensEdit <> [textEdit])) Nothing Nothing

implicitRemoveCodeAction :: Uri -> (String, Bool, Range, Maybe (Range, String), Maybe Range) -> Command |? CodeAction
implicitRemoveCodeAction file_uri (name, whole, range, insName, parens) = InR $ CodeAction text Nothing Nothing Nothing Nothing (Just wsEdit) Nothing Nothing
  where
    text = pack $ "Remove unused variable " ++ name
    edit = TextEdit range (if whole then "" else "_")
    ins = case insName of
      Nothing -> []
      Just (r, n) -> [TextEdit r $ pack (n ++ " = ")]
    ps = case parens of
      Nothing -> []
      Just (Range l r) -> [TextEdit (Range l (incLSPPos l)) "", TextEdit (Range (decLSPPos r) r) ""]
    wsEdit = WorkspaceEdit (Just $ Map.singleton file_uri $ ins ++ [edit] ++ ps) Nothing Nothing

module Handlers (handlers) where

import Agda.Syntax.Parser
import Agda.Syntax.Position
import Agda.Utils.FileName
import AgdaToLSP (Implicit (Implicit))
import Colog.Core ( (<&), logStringStderr )
import Control.Lens ((^.))
import Control.Monad.IO.Class (liftIO)
import Data.Aeson (Value (Number))
import Data.IORef
import Data.Map qualified as Map
import Data.Text (pack, unpack)
import Diagnostics (sendDiagnostics, badImportDiagnostics)
import ImplicitsScope (parseVFSFile, implicitsScopeFromModule, emptyImplicits)
import Language.LSP.Diagnostics (partitionBySource)
import Language.LSP.Protocol.Lens (HasUri (uri), HasVersion (version))
import Language.LSP.Protocol.Message
import Language.LSP.Protocol.Types
import Language.LSP.Server
import Language.LSP.VFS (virtualFileText)
import State (FileState (FileState), State, setFileState, setImpState, getImpState)
import CodeActions (makeCodeActions)
import Data.Maybe (fromMaybe)
import ScopeAnalysis qualified as Scope
import Completions (makeCompletions)
import Rename (makeRename, declarationLocation, referencesLocations)
import SemanticTokens (tokenizeFull)
import ScopeImport qualified as Imp

onInitializeHandler :: Handlers (LspM ())
onInitializeHandler = notificationHandler SMethod_Initialized $ \_msg -> return ()

eitherToMaybe :: Either a b -> Maybe b
eitherToMaybe (Left _)  = Nothing
eitherToMaybe (Right b) = Just b

-- call whenever a document changes to parse it and update its scope
updateState :: IORef State -> Uri -> Maybe Int32 -> LspT () IO ()
updateState state fileUri fileVersion = do
  vf <- getVirtualFile $ toNormalizedUri fileUri
  case vf of
    Just file -> do
      case uriToFilePath fileUri of
        Just path -> do
          logStringStderr <& ("Path: " <> path)
          oldState <- liftIO $ readIORef state
          modl <- liftIO $ parseVFSFile (mkAbsolute path) (unpack $ virtualFileText file)
          case eitherToMaybe modl of
            Nothing -> do
              -- we still have to change state to badly parsed
              let newState = setFileState oldState path (Just (FileState file modl emptyImplicits Scope.emptyScanState))
              liftIO $ writeIORef state newState
              sendDiagnostics [] state fileUri fileVersion
            Just modl' -> do
              (imports, badImports, impState) <- liftIO $ (\x -> Imp.resolveAllModules x (getImpState oldState)) modl'
              let scope = implicitsScopeFromModule modl'
              let scope' = Scope.scanModule imports modl'
              let newState = setImpState (setFileState oldState path (Just (FileState file modl scope scope'))) impState
              liftIO $ writeIORef state newState
              let badImportDs = badImportDiagnostics fileUri badImports
              sendDiagnostics badImportDs state fileUri fileVersion
        Nothing -> do
          logStringStderr <& "No path"
          return ()
    Nothing -> return ()

onDocumentOpenHandler :: IORef State -> Handlers (LspM ())
onDocumentOpenHandler state =
  notificationHandler SMethod_TextDocumentDidOpen $ \msg -> do
    let TNotificationMessage _ _ (DidOpenTextDocumentParams doc) = msg
        file_path = uriToFilePath $ doc ^. uri
    logStringStderr <& ("Opened document: " ++ show file_path)
    updateState state (doc ^. uri) (Just $ doc ^. version)

onDocumentChangeHandler :: IORef State -> Handlers (LspM ())
onDocumentChangeHandler state =
  notificationHandler SMethod_TextDocumentDidChange $ \msg -> do
    let TNotificationMessage _ _ (DidChangeTextDocumentParams doc _content) = msg
    updateState state (doc ^. uri) (Just $ doc ^. version)

onDocumentSaveHandler :: IORef State -> Handlers (LspM ())
onDocumentSaveHandler state =
  notificationHandler SMethod_TextDocumentDidSave $ \msg -> do
    let TNotificationMessage _ _ (DidSaveTextDocumentParams doc _text) = msg
    logStringStderr <& ("Saved document: " ++ show doc)
    updateState state (doc ^. uri) Nothing

onCodeActionsHandler :: IORef State -> Handlers (LspM ())
onCodeActionsHandler state =
  requestHandler SMethod_TextDocumentCodeAction $ \req responder -> do
    logStringStderr <& "Got code actions request"
    let TRequestMessage _ _ _ params = req
    codeActions <- makeCodeActions params state
    responder $ Right $ InL codeActions

onCompletionsHandler :: IORef State -> Handlers (LspM ())
onCompletionsHandler state =
  requestHandler SMethod_TextDocumentCompletion $ \req responder -> do
    logStringStderr <& "Got completions request"
    let TRequestMessage _ _ _ params = req
    completions <- makeCompletions params state
    responder $ Right $ InL completions

onRenameHandler :: IORef State -> Handlers (LspM ())
onRenameHandler state =
  requestHandler SMethod_TextDocumentRename $ \req responder -> do
    logStringStderr <& "Got rename request"
    let TRequestMessage _ _ _ params = req
    renames <- makeRename params state
    case renames of
      Just r -> responder $ Right $ InL r
      Nothing -> return ()

onGoToDefinitionHandler :: IORef State -> Handlers (LspM ())
onGoToDefinitionHandler state =
  requestHandler SMethod_TextDocumentDefinition $ \req responder -> do
    logStringStderr <& "Got go to definition request"
    let TRequestMessage _ _ _ (DefinitionParams doc pos _ _) = req
    location <- declarationLocation doc pos state
    case location of
      Just l -> responder $ Right $ InL (Definition $ InL l)
      Nothing -> return ()

onReferencesHandler :: IORef State -> Handlers (LspM ())
onReferencesHandler state =
  requestHandler SMethod_TextDocumentReferences $ \req responder -> do
    logStringStderr <& "Got references request"
    let TRequestMessage _ _ _ (ReferenceParams doc pos _ _ _) = req
    refs <- referencesLocations doc pos state
    responder $ Right $ InL refs

onSemanticTokensFullHandler :: IORef State -> Handlers (LspM ())
onSemanticTokensFullHandler state =
  requestHandler SMethod_TextDocumentSemanticTokensFull $ \req responder -> do
    logStringStderr <& "Got semantic tokens full request"
    let TRequestMessage _ _ _ (SemanticTokensParams _ _ doc) = req
    toks <- tokenizeFull doc state
    responder $ Right $ InL toks

handlers :: IORef State -> Handlers (LspM ())
handlers state =
  mconcat
    [ onInitializeHandler,
      onDocumentOpenHandler state,
      onDocumentChangeHandler state,
      onDocumentSaveHandler state,
      onCodeActionsHandler state,
      onCompletionsHandler state,
      onRenameHandler state,
      onGoToDefinitionHandler state,
      onReferencesHandler state,
      onSemanticTokensFullHandler state
    ]

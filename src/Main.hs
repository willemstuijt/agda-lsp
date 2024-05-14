{-# LANGUAGE ExplicitNamespaces #-}

import Benchmarks (generateAgdaData, generateMyCheckData)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.IORef (newIORef)
import Handlers (handlers)
import Language.LSP.Protocol.Types
  ( SaveOptions (SaveOptions),
    TextDocumentSyncKind (TextDocumentSyncKind_Incremental),
    TextDocumentSyncOptions (..),
    type (|?) (InR),
  )
import Language.LSP.Protocol.Types qualified as LSP
import Language.LSP.Server
import ScopeAnalysisTests qualified as ScopeAnalysisTests
import State (emptyState)
import System.Environment (getArgs)

data ScopeTree = ScopeLeaf LSP.Range | ScopeTree LSP.Range [ScopeTree] deriving (Show)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["run"] -> handleRun
    ["test"] -> handleTest
    _ -> do
      state <- newIORef emptyState
      _ <-
        runServer $
          ServerDefinition
            { onConfigurationChange = \_ _ -> pure (),
              defaultConfig = (),
              doInitialize = \env _req -> pure $ Right env,
              staticHandlers = handlers state,
              interpretHandler = \env -> Iso (runLspT env) liftIO,
              options =
                defaultOptions
                  { optTextDocumentSync = Just syncOptions
                  }
            }
      pure ()

syncOptions :: TextDocumentSyncOptions
syncOptions =
  TextDocumentSyncOptions
    { _openClose = Just True,
      _change = Just TextDocumentSyncKind_Incremental,
      _willSave = Just False,
      _willSaveWaitUntil = Just False,
      _save = Just $ InR $ SaveOptions $ Just False
    }

handleTest :: IO ()
handleTest = do
  putStrLn "Running tests..."
  res <- ScopeAnalysisTests.runTests
  -- res <- ScopeAnalysisImplicitsTests.runTests
  -- res2 <- SmokeTest.runTests
  mapM_ print (fmap show res) -- <> fmap show res2)

handleRun :: IO ()
handleRun = do
  -- runLineCounter "linecounts.csv"
  generateMyCheckData "bench.csv"
  generateAgdaData "agda-bench.json"

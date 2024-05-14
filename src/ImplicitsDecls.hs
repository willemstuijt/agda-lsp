{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use tuple-section" #-}
module ImplicitsDecls (
  partitionByTypeSig,
  insertableImplicits,
  ImplicitDeclType (ImplicitDeclType),
  ImplicitDeclClause (ImplicitDeclClause)
) where

import Agda.Syntax.Common
import Agda.Syntax.Concrete
import Agda.Syntax.Parser
import Agda.Syntax.Position ()
import Agda.Utils.FileName
import Agda.Utils.List1 (NonEmpty ((:|)), List1)
import Agda.Utils.List2 (List2 (List2))
import AgdaToLSP (toLSPRange, toLSPRange', endOfExpr, incLSPPos, rangeContainsPos)
import Control.Monad.IO.Class (liftIO)
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Maybe (catMaybes, mapMaybe, fromMaybe)
import Language.LSP.Protocol.Types qualified as LSP
import Core (bindsOfPattern, Binding (ImplicitB, ExplicitB))
import Data.List (elemIndex)
import Debug.Trace (trace)

newtype ImplicitDeclType = ImplicitDeclType [String] deriving (Show)

data ImplicitDeclClause = ImplicitDeclClause LSP.Position [(String, LSP.Range)] LSP.Range deriving (Show)

namePartsToString :: NameParts -> Maybe String
namePartsToString ((Id name) :| []) = Just name
namePartsToString _ = Nothing -- TODO in which cases does this happen?

nameToString :: Name -> Maybe String
nameToString (Name _ _ parts) = namePartsToString parts
nameToString (NoName _ _) = Nothing -- TODO when does this happen?

nameFromArgBinder :: NamedArg Binder -> Maybe String
nameFromArgBinder (Arg _ (Named _ (Binder _ (BName {boundName = name})))) = nameToString name

namesFromTypedBinding :: TypedBinding -> [String]
namesFromTypedBinding (TBind _ (x :| xs) _) = catMaybes $ nameFromArgBinder x : fmap nameFromArgBinder xs
namesFromTypedBinding (TLet _ _) = [] -- TODO in which cases does this happen?

namesFromTelescope :: Telescope1 -> [String]
namesFromTelescope (x :| xs) = concat $ namesFromTypedBinding x : fmap namesFromTypedBinding xs

implicitNamesFromExpr :: Expr -> [String]
implicitNamesFromExpr (Generalized (Pi telescope _)) = namesFromTelescope telescope
implicitNamesFromExpr _ = []

funClauseImplicits :: Declaration -> Maybe ImplicitDeclClause
funClauseImplicits (FunClause (LHS {lhsOriginalPattern = p}) (RHS rhs) _ _) = Just $ ImplicitDeclClause pos pairs (LSP.Range pos end)
    where
      pos = funPatternNamePos p
      end = endOfExpr rhs
      bindings = bindsOfPattern False [] p
      pairs = mapMaybe bindingToPair bindings
      bindingToPair (ImplicitB s r) = Just (s, r)
      bindingToPair (ExplicitB _ _) = Nothing

funClauseImplicits _ = Nothing

-- Position at the end of the name of the pattern of a function
funPatternNamePos :: Pattern -> LSP.Position
funPatternNamePos (IdentP _ (QName (Name {nameRange = range}))) = pos
  where
    (LSP.Range _ pos) = toLSPRange' range
funPatternNamePos (RawAppP _ (List2 a _ _)) = funPatternNamePos a
funPatternNamePos _ = LSP.Position 0 0

partitionByTypeSig :: [Declaration] -> [(ImplicitDeclType, [ImplicitDeclClause])]
partitionByTypeSig ((Module _ _ _ _ decls) : ds) = partitionByTypeSig (decls ++ ds)
partitionByTypeSig ((TypeSig _ _ _ e) : decls) = (ImplicitDeclType names, mapMaybe funClauseImplicits funClauses) : partitionByTypeSig rest
  where
    names = implicitNamesFromExpr e

    (funClauses, rest) = span isFunClause decls

    isFunClause (FunClause {}) = True
    isFunClause _ = False
partitionByTypeSig (_ : decls) = partitionByTypeSig decls
partitionByTypeSig [] = []

-- Goes through the implicits of the clause and of the type
-- and returns a list of the missing implicits and on which
-- range to insert them
missingImplicits :: ImplicitDeclType -> ImplicitDeclClause -> [(String, LSP.Range)]
missingImplicits (ImplicitDeclType names) (ImplicitDeclClause pos impls _) = helper pos names impls
  where
    helper p names' ((cur, LSP.Range beg end) : impls') = fmap (\x -> (x, LSP.Range p beg)) ins ++ helper end rest impls'
      where
        idx = fromMaybe (length names') $ elemIndex cur names'
        (ins, rest') = splitAt idx names'
        rest = case rest' of
          [] -> []
          (_ : xs) -> xs
    helper p ns [] = fmap (\x -> (x, LSP.Range p (incLSPPos p))) ns
    -- Gives the next Begin in the list
    -- if the list is empty returns pos+1
    -- this is a heuristic to match the = of FunClase
    -- since apparently its position isn't stored in
    -- the CST

-- Find the clause that contains the cursor position
-- and return the implicits that can be inserted
insertableImplicits :: [(ImplicitDeclType, [ImplicitDeclClause])] -> LSP.Position -> [(String, LSP.Range)]
insertableImplicits ((t, clauses) : xs) pos = case clause of
  Just c -> missingImplicits t c
  Nothing -> insertableImplicits xs pos
  where
    clause = List.find (\(ImplicitDeclClause _ _ r) -> rangeContainsPos r pos) clauses
insertableImplicits [] _ = []
module Scope
    ( insert,
      overwrite,
      newScope,
      addChildScope,
      lookupParent,
      incId,
      allSymbols,
      innerMostScope,
      inScopeSymbols,
      empty,
      getSym,
      symRange,
      symbolAtPos,
      symbolByID,
      rmParent,
      symId,
      insertScope,
      insertScopeFiltered,
      symScope,
      symParams,
      namesInScope,
      Modl (Modl),
      Data (Data),
      SymId (SymId),
      Symbol (Symbol),
      Sym (..),
      FuncCase (FuncCase),
      SigParam (..),
      Scope (Scope))
where

import Data.Map qualified as DMap
import ScopeMap qualified as Map
import Language.LSP.Protocol.Types qualified as LSP
import Agda.Syntax.Concrete (Expr)
import AgdaToLSP (rangeContainsPos, incLSPRangeEnd)
import Data.List (find)
import Debug.Trace (trace)

data Scope = Scope LSP.Range (Maybe Scope) [Scope] (Map.ScopeMap String LSP.Range Symbol) deriving Show

newtype Modl = Modl Scope deriving Show
newtype Data = Data Scope deriving Show

newtype SymId = SymId Int deriving (Eq, Ord)

instance Show SymId where
  show (SymId x) = "$" ++ show x

incId :: SymId -> SymId
incId (SymId x) = SymId $ x + 1

symId :: Symbol -> SymId
symId (Symbol _ _ i _) = i

getSym :: Symbol -> Sym
getSym (Symbol _ _ _ x) = x

data Symbol = Symbol LSP.Range String SymId Sym deriving Show

symRange :: Symbol -> LSP.Range
symRange (Symbol r _ _ _) = r

data Sym = SModl [SigParam] Modl | SData Data | SConstr [SigParam] | SFunc [SigParam] [FuncCase] | SImpl | SExpl deriving Show

symScope :: Sym -> Maybe Scope
symScope (SModl _ (Modl s)) = Just s
symScope (SData (Data s)) = Just s
symScope _ = Nothing

symParams :: Sym -> [SigParam]
symParams (SModl x _) = x
symParams (SConstr x) = x
symParams (SFunc x _) = x
symParams _ = []

data SigParam = SigExplicit Expr | SigImplicit (Maybe String) Expr

instance Show SigParam where
    show (SigExplicit _) = "SigExplicit"
    show (SigImplicit (Just str) _) = "SigImplicit " ++ str
    show (SigImplicit Nothing _) = "SigImplicit"

newtype FuncCase = FuncCase Scope deriving Show

insert :: String -> LSP.Range -> Symbol -> Scope -> Scope
insert a b c (Scope r s cs m) = Scope r s cs $ Map.insert a b c m

overwrite :: String -> LSP.Range -> Symbol -> Scope -> Scope
overwrite a b c (Scope r s cs m) = Scope r s cs $ Map.overwrite a b c m

newScope :: Maybe Scope -> LSP.Range -> Scope
newScope parent range = Scope range parent [] Map.empty

addChildScope :: Scope -> Scope -> Scope
addChildScope (Scope r s cs m) child = Scope r s (cs ++ [child]) m

rmParent :: Scope -> Scope
rmParent (Scope r _ cs m) = Scope r Nothing cs m

-- Looks up in scope, if nothing found then
-- tries looking up in parent if it has a parent
lookupParent :: String -> Scope -> Maybe Symbol
lookupParent name (Scope _ parent _ mp) = case Map.lookupLast name mp of
  Nothing -> case parent of
    Nothing -> Nothing
    Just p -> lookupParent name p
  Just sym -> Just sym

-- returns all the symbols in this scope
-- and its children
allSymbols :: Scope -> DMap.Map SymId Symbol
allSymbols (Scope _ _ ss mp) = foldl (\m x -> DMap.insert (symId x) x m) recs syms
  where
    recs = foldl (\m s -> DMap.union m (allSymbols s)) DMap.empty ss
    syms = Map.allValues mp

-- adds lhs scope children to rhs scope
insertScope :: Scope -> Scope -> Scope
insertScope (Scope _ _ _ (Map.ScopeMap x)) scope = DMap.foldrWithKey (\k v acc -> foldr (\(r, s) b -> insert k r s b) acc v) scope x

-- adds lhs scope children to rhs scope after filtering
insertScopeFiltered :: ((String, Bool) -> Maybe String) -> Scope -> Scope -> Scope
insertScopeFiltered fn (Scope _ _ _ (Map.ScopeMap x)) scope = DMap.foldrWithKey inner scope x
  where
    inner k v acc = foldr f acc v
      where
        f (r, s) b = case fn (k, isModl s) of
          Nothing -> b
          Just k' -> insert k' r s b

isModl :: Symbol -> Bool
isModl (Symbol _ _ _ (SModl {})) = True
-- isModl (Symbol _ _ _ (SData {})) = True
isModl _ = False

empty :: Scope
empty = Scope r Nothing [] Map.empty
  where
    r = LSP.Range (LSP.Position 0 0) (LSP.Position 100000000 100000000)

innerMostScope :: LSP.Position -> Scope -> Scope
innerMostScope pos s@(Scope _ _ ss _) = case inner of
  Just inn -> innerMostScope pos inn
  Nothing -> s
  where
    inner = find (\(Scope r _ _ _) -> rangeContainsPos (incLSPRangeEnd r) pos) ss

inScopeSymbols :: DMap.Map SymId Symbol -> LSP.Position -> Scope -> [(String, Symbol)]
inScopeSymbols syms pos (Scope _ parent _ s) = ps ++ Map.lookupAllBefore r s
  where
    r = LSP.Range pos pos
    ps = case parent of
      Nothing -> []
      Just p -> inScopeSymbols syms pos p

-- Find symbol at given position
symbolAtPos :: Scope -> LSP.Position -> Maybe Symbol
symbolAtPos scope pos = find (\(Symbol rng _ _ _) -> rangeContainsPos rng pos) syms
  where
    syms = allSymbols scope

-- Find symbol by ID
symbolByID :: Scope -> SymId -> Maybe Symbol
symbolByID scope sid = find (\(Symbol _ _ x _) -> sid == x) syms
  where
    syms = allSymbols scope

namesInScope :: Scope -> [String]
namesInScope (Scope _ _ _ mp) = Map.allKeys mp

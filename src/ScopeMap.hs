module ScopeMap
  ( ScopeMap (ScopeMap),
    empty,
    lookupLast,
    lookupLastBefore,
    lookupAllBefore,
    insert,
    overwrite,
    allKeys,
    fromList,
    allValues
  )
where

import Data.Map qualified as Map
import Data.Maybe (catMaybes)

-- list contains elements in decreasing order
newtype ScopeMap k1 k2 v = ScopeMap (Map.Map k1 [(k2, v)]) deriving Show

fromList :: Ord k1 => k2 -> [(k1, [v])] -> ScopeMap k1 k2 v
fromList def xs = ScopeMap $ Map.fromList tmp
  where
    tmp = fmap (\(k, v) -> (k, fmap (\x ->(def,x)) v)) xs

empty :: ScopeMap k1 k2 v
empty = ScopeMap Map.empty

lookupLast :: Ord k1 => k1 -> ScopeMap k1 k2 v -> Maybe v
lookupLast k (ScopeMap m) = case Map.lookup k m of
    (Just v) -> firstElement v
    Nothing -> Nothing
    where
        firstElement [] = Nothing
        firstElement ((_, v):_) = Just v

lookupLastBefore :: (Ord k1, Ord k2) => k1 -> k2 -> ScopeMap k1 k2 v -> Maybe v
lookupLastBefore k o (ScopeMap m) = case Map.lookup k m of
    (Just v) -> findFirst o v
    Nothing -> Nothing
    where
        findFirst x pairs = case filter (\(a, _) -> a >= x) pairs of
            ((_, b):_) -> Just b
            _          -> Nothing

lookupAllBefore :: (Ord k2) => k2 -> ScopeMap k1 k2 v -> [(k1, v)]
lookupAllBefore o (ScopeMap m) = catMaybes elems''
  where
    elems = Map.toList m
    elems' = fmap (\(a, b) -> (a, filter (\(k, _) -> k <= o) b)) elems
    elems'' = fmap pairIfAny elems'

    pairIfAny (_, []) = Nothing
    pairIfAny (a1, (_,x):_) = Just (a1, x)

insert :: Ord k1 => k1 -> k2 -> v -> ScopeMap k1 k2 v -> ScopeMap k1 k2 v
insert a b c (ScopeMap m) = ScopeMap $ case Map.lookup a m of
    (Just v) -> Map.insert a ((b, c) : v) m
    Nothing -> Map.insert a [(b, c)] m

overwrite :: (Ord k1, Eq k2) => k1 -> k2 -> v -> ScopeMap k1 k2 v -> ScopeMap k1 k2 v
overwrite a b c (ScopeMap m) = ScopeMap $ case Map.lookup a m of
    (Just v) -> Map.insert a (replaceFirst (\(x, _) -> x == b) (b, c) v) m
    Nothing -> Map.insert a [] m

replaceFirst :: (a -> Bool) -> a -> [a] -> [a]
replaceFirst _ _ [] = []
replaceFirst predicate new (x:xs)
  | predicate x    = new : xs
  | otherwise = x : replaceFirst predicate new xs

allKeys :: ScopeMap k1 k2 v -> [k1]
allKeys (ScopeMap mp) = Map.keys mp

allValues :: ScopeMap k1 k2 v -> [v]
allValues (ScopeMap mp) = snd <$> concat (Map.elems mp)

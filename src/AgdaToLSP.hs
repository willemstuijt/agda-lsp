module AgdaToLSP (
  toLSPRange,
  toLSPRange',
  toLSPPosition,
  incLSPRangeEnd,
  decLSPRangeEnd,
  Implicit (Implicit),
  incLSPPos,
  decLSPPos,
  toLSPEnd',
  posOfPattern,
  endOfPattern,
  endOfExpr,
  posOfTypedBinding,
  rangeContainsPos,
  unpackName,
  qnameRange,
  containsPos,
) where

import Agda.Syntax.Position
import Agda.Syntax.Concrete
import Data.Sequence qualified as Seq
import Agda.Utils.List1 (NonEmpty ((:|)))
import Language.LSP.Protocol.Types qualified as LSP
import Agda.Syntax.Common (Ranged(rangeOf))

data Implicit = Implicit LSP.Range String deriving (Show)

rangeContainsPos :: LSP.Range -> LSP.Position -> Bool
rangeContainsPos (LSP.Range b e) pos = b <= pos && pos <= e

incLSPRangeEnd :: LSP.Range -> LSP.Range
incLSPRangeEnd (LSP.Range b (LSP.Position l c)) = LSP.Range b (LSP.Position l (c+1))

decLSPRangeEnd :: LSP.Range -> LSP.Range
decLSPRangeEnd (LSP.Range b (LSP.Position l c)) = LSP.Range b (LSP.Position l (c-1))

toLSPRange :: Range' SrcFile -> Maybe LSP.Range
toLSPRange (Range _ Seq.Empty) = Nothing
toLSPRange (Range _ b) = Just $ LSP.Range (toLSPPosition pos) (toLSPPosition end)
  where
    (Interval pos _) = case Seq.viewl b of
      Seq.EmptyL -> error "should never happen"
      x Seq.:< _ -> x
    (Interval _ end) = case Seq.viewr b of
      Seq.EmptyR -> error "should never happen"
      _ Seq.:> x -> x
toLSPRange NoRange = Nothing

toLSPRange' :: Range' SrcFile -> LSP.Range
toLSPRange' = defaultRange . toLSPRange

toLSPBegin' :: Range' SrcFile -> LSP.Position
toLSPBegin' r = pos
  where
    (LSP.Range pos _) = toLSPRange' r

toLSPEnd' :: Range' SrcFile -> LSP.Position
toLSPEnd' r = end
  where
    (LSP.Range _ end) = toLSPRange' r

incLSPPos :: LSP.Position -> LSP.Position
incLSPPos (LSP.Position l c) = LSP.Position l (c + 1)

decLSPPos :: LSP.Position -> LSP.Position
decLSPPos (LSP.Position l c) = LSP.Position l (c - 1)

defaultRange :: Maybe LSP.Range -> LSP.Range
defaultRange (Just range) = range
defaultRange Nothing = LSP.Range (LSP.Position 0 0) (LSP.Position 0 0)

toLSPPosition :: Position' () -> LSP.Position
toLSPPosition (Pn {posLine = posLine, posCol = posCol}) = LSP.Position (fromIntegral (posLine - 1)) (fromIntegral (posCol - 1))

posOfPattern :: Pattern -> LSP.Position
posOfPattern (IdentP _ (QName name)) = pos
  where
    (LSP.Range pos _, _) = unpackName name
posOfPattern (IdentP _ (Qual name _)) = pos
  where
    (LSP.Range pos _, _) = unpackName name
posOfPattern (QuoteP r) = toLSPBegin' r
posOfPattern (AppP fun _) = posOfPattern fun
posOfPattern (RawAppP r _) = toLSPBegin' r
posOfPattern (OpAppP r _ _ _) = toLSPBegin' r
posOfPattern (HiddenP r _) = toLSPBegin' r
posOfPattern (InstanceP r _) = toLSPBegin' r
posOfPattern (ParenP r _) = toLSPBegin' r
posOfPattern (WildP r) = toLSPBegin' r
posOfPattern (AbsurdP r) = toLSPBegin' r
posOfPattern (AsP r _ _) = toLSPBegin' r
posOfPattern (DotP r _) = toLSPBegin' r
posOfPattern (LitP r _) = toLSPBegin' r
posOfPattern (RecP r _) = toLSPBegin' r
posOfPattern (EqualP r _) = toLSPBegin' r
posOfPattern (EllipsisP r _) = toLSPBegin' r
posOfPattern (WithP r _) = toLSPBegin' r

endOfPattern :: Pattern -> LSP.Position
endOfPattern (IdentP _ (QName name)) = pos
  where
    (LSP.Range _ pos, _) = unpackName name
endOfPattern (IdentP _ (Qual name _)) = pos
  where
    (LSP.Range _ pos, _) = unpackName name
endOfPattern (QuoteP r) = toLSPEnd' r
endOfPattern (AppP fun _) = endOfPattern fun
endOfPattern (RawAppP r _) = toLSPEnd' r
endOfPattern (OpAppP r _ _ _) = toLSPEnd' r
endOfPattern (HiddenP r _) = toLSPEnd' r
endOfPattern (InstanceP r _) = toLSPEnd' r
endOfPattern (ParenP r _) = toLSPEnd' r
endOfPattern (WildP r) = toLSPEnd' r
endOfPattern (AbsurdP r) = toLSPEnd' r
endOfPattern (AsP r _ _) = toLSPEnd' r
endOfPattern (DotP r _) = toLSPEnd' r
endOfPattern (LitP r _) = toLSPEnd' r
endOfPattern (RecP r _) = toLSPEnd' r
endOfPattern (EqualP r _) = toLSPEnd' r
endOfPattern (EllipsisP r _) = toLSPEnd' r
endOfPattern (WithP r _) = toLSPEnd' r

endOfExpr :: Expr -> LSP.Position
endOfExpr (Ident (QName n)) = end
  where
    (LSP.Range _ end, _) = unpackName n
endOfExpr (Ident (Qual _ q)) = endOfExpr (Ident q)
endOfExpr (Lit r _) = toLSPEnd' r
endOfExpr (QuestionMark r _) = toLSPEnd' r
endOfExpr (Underscore r _) = toLSPEnd' r
endOfExpr (RawApp r _) = toLSPEnd' r
endOfExpr (App r _ _) = toLSPEnd' r
endOfExpr (OpApp r _ _ _) = toLSPEnd' r
endOfExpr (WithApp r _ _) = toLSPEnd' r
endOfExpr (HiddenArg r _) = toLSPEnd' r
endOfExpr (InstanceArg r _) = toLSPEnd' r
endOfExpr (Lam r _ _) = toLSPEnd' r
endOfExpr (AbsurdLam r _) = toLSPEnd' r
endOfExpr (ExtendedLam r _ _) = toLSPEnd' r
endOfExpr (Fun r _ _) = toLSPEnd' r
endOfExpr (Pi _ e) = endOfExpr e
endOfExpr (Rec r _) = toLSPEnd' r
endOfExpr (RecUpdate r _ _) = toLSPEnd' r
endOfExpr (Let r _ _) = toLSPEnd' r
endOfExpr (Paren r _) = toLSPEnd' r
endOfExpr (IdiomBrackets r _) = toLSPEnd' r
endOfExpr (DoBlock r _) = toLSPEnd' r
endOfExpr (Absurd r) = toLSPEnd' r
endOfExpr (As r _ _) = toLSPEnd' r
endOfExpr (Dot r _) = toLSPEnd' r
endOfExpr (DoubleDot r _) = toLSPEnd' r
endOfExpr (Quote r) = toLSPEnd' r
endOfExpr (QuoteTerm r) = toLSPEnd' r
endOfExpr (Tactic r _) = toLSPEnd' r
endOfExpr (Unquote r) = toLSPEnd' r
endOfExpr (DontCare x) = endOfExpr x
endOfExpr (Equal r _ _) = toLSPEnd' r
endOfExpr (Ellipsis r) = toLSPEnd' r
endOfExpr (KnownIdent {}) = LSP.Position 0 0
endOfExpr (KnownOpApp _ r _ _ _) = toLSPEnd' r
endOfExpr (Generalized e) = endOfExpr e

posOfTypedBinding :: TypedBinding -> LSP.Position
posOfTypedBinding (TBind r _ _) = toLSPBegin' r
posOfTypedBinding (TLet r _) = toLSPBegin' r

qnameRange :: QName -> LSP.Range
qnameRange (QName n) = fst $ unpackName n
qnameRange (Qual a b) = LSP.Range x y
  where
    (LSP.Range x _) = fst $ unpackName a
    (LSP.Range _ y) = qnameRange b

unpackName :: Name -> (LSP.Range, String)
unpackName (Name {nameRange = range, nameNameParts = (x :| xs)}) = (toLSPRange' range, namePartsStr $ x : xs)
unpackName (NoName {nameRange = range}) = (toLSPRange' range, "_")

namePartsStr :: [NamePart] -> String
namePartsStr [] = ""
namePartsStr ((Id a):xs) = a ++ namePartsStr xs
namePartsStr (Hole:xs) = "_" ++ namePartsStr xs

containsPos :: HasRange e => LSP.Position -> e -> Bool
containsPos p x = rangeContainsPos (toLSPRange' $ getRange x) p
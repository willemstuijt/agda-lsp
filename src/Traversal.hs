module Traversal (traverseIdents, Done (..), Node (..), foldModule, doneAsMaybe) where

import Agda.Syntax.Concrete
import Agda.Syntax.Common
import Agda.Utils.List1 (NonEmpty ((:|)))
import Agda.Utils.List2 (List2(List2))

traverseIdents :: Monoid m => (QName -> m) -> Module -> m
traverseIdents fn = foldModule (asq fn)

data Done t = Done t | Continue

doneAsMaybe :: Done t -> Maybe t
doneAsMaybe (Done x) = Just x
doneAsMaybe Continue = Nothing

instance Semigroup (Done t) where
  (Done x) <> _ = Done x
  Continue <> x = x

instance Monoid (Done t) where
  mempty = Continue

data Node = P Pattern | E Expr | D Declaration

foldModule :: Monoid m => (Node -> m) -> Module -> m
foldModule fn modl = foldt (foldDecl fn) $ modDecls modl

foldDecl :: Monoid m => (Node -> m) -> Declaration -> m
foldDecl fn d' = case d' of
  TypeSig _ _ _ e -> this <> fe e
  FunClause lhs rhs w _ -> this <> foldLHS fn lhs <> foldrh fe rhs <> foldwc (foldt fd) w
  Module _ _ _ _ ds -> this <> foldt fd ds
  Data _ _ _ _ _ ds -> this <> foldt fd ds
  Import {} -> this
  Open {} -> this
  _ -> mempty -- TODO
  where
    d = D d'
    this = fn d
    fe = foldExpr fn
    fd = foldDecl fn

foldExpr :: Monoid m => (Node -> m) -> Expr -> m
foldExpr fn e' = case e' of
  Ident {} -> this
  Lit {} -> this
  QuestionMark {} -> this
  Underscore {} -> this
  RawApp _ (List2 a b c) -> this <> foldt (foldExpr fn) (a : b : c)
  App _ fun arg -> this <> foldExpr fn fun <> folda (foldExpr fn) arg
  OpApp {} -> this
  WithApp _ a b -> this <> foldt (foldExpr fn) (a : b)
  HiddenArg _ x -> this <> foldn (foldExpr fn) x
  InstanceArg _ x -> this <> foldn (foldExpr fn) x
  Lam _ (a :| b) x -> this <> foldt (foldLamBinding fn) (a : b) <> foldExpr fn x
  AbsurdLam {} -> this
  ExtendedLam _ _ (a :| b) -> this <> foldt (foldLamClause fn) (a : b)
  Fun _ (Arg _ a) b -> this <> foldExpr fn a <> foldExpr fn b
  Pi (a :| b) e -> this <> foldt (foldTypedBinding fn (foldExpr fn)) (a : b) <> foldExpr fn e
  Rec _ xs -> this <> foldt (foldRecordAssignment fn) xs
  RecUpdate _ x fa -> this <> foldExpr fn x <> foldt (foldfa (foldExpr fn)) fa
  Let _ (a :| b) x -> this <> foldt (foldDecl fn) (a : b) <> foldm (foldExpr fn) x
  Paren _ x -> this <> foldExpr fn x
  IdiomBrackets _ xs -> this <> foldt (foldExpr fn) xs
  DoBlock _ (a :| b) -> this <> foldt (foldDoStmt fn) (a : b)
  Absurd {} -> this
  As _ _ x -> this <> fe x
  Dot _ x -> this <> fe x
  DoubleDot _ x -> this <> fe x
  Quote {} -> this
  QuoteTerm {} -> this
  Tactic _ x -> this <> fe x
  Unquote {} -> this
  DontCare x -> this <> fe x
  Equal _ a b -> this <> foldt fe [a, b]
  Ellipsis {} -> this
  KnownIdent {} -> error "TODO"
  KnownOpApp {} -> error "TODO"
  Generalized x -> this <> foldExpr fn x
  where
    e = E e'
    this = fn e
    fe = foldExpr fn

foldModuleAssignment :: Monoid m => (Node -> m) -> ModuleAssignment -> m
foldModuleAssignment fn (ModuleAssignment _ xs _) = foldt (foldExpr fn) xs

foldRecordAssignment :: Monoid m => (Node -> m) -> RecordAssignment -> m
foldRecordAssignment fn = folde (foldfa (foldExpr fn)) (foldModuleAssignment fn)

foldDoStmt :: Monoid m => (Node -> m) -> DoStmt -> m
foldDoStmt fn (DoBind _ p e cs) = foldPat fn p <> foldExpr fn e <> foldt (foldLamClause fn) cs
foldDoStmt fn (DoThen x) = foldExpr fn x
foldDoStmt fn (DoLet _ (a :| b)) = foldt (foldDecl fn) (a : b)

foldLamClause :: Monoid m => (Node -> m) -> LamClause -> m
foldLamClause fn (LamClause ps rhs _) = foldt (foldPat fn) ps <> foldrh (foldExpr fn) rhs

foldTypedBinding :: Monoid m => (Node -> m) -> (e -> m) -> TypedBinding' e -> m
foldTypedBinding fn fn2 (TBind _ (a :| b) x) = foldt (folda (foldBinder fn)) (a : b) <> fn2 x
foldTypedBinding fn _ (TLet _ (a :| b)) = foldt (foldDecl fn) (a : b)

foldLamBinding :: Monoid m => (Node -> m) -> LamBinding -> m
foldLamBinding fn (DomainFree x) = folda (foldBinder fn) x
foldLamBinding fn (DomainFull tb) = foldTypedBinding fn (foldExpr fn) tb

foldBinder :: Monoid m => (Node -> m) -> Binder -> m
foldBinder fn (Binder p x) = foldm (foldPat fn) p <> foldBoundName fn x

foldLHS :: Monoid m => (Node -> m) -> LHS -> m
-- TODO rewrite and with?
foldLHS fn (LHS p _ _) = foldPat fn p

foldBoundName :: Monoid m => (Node -> m) -> BoundName -> m
foldBoundName _ (BName {}) = mempty

foldPat :: Monoid m => (Node -> m) -> Pattern -> m
foldPat fn p' = case p' of
  IdentP {} -> this
  QuoteP {} -> this
  AppP fun arg -> this <> fp fun <> folda fp arg
  RawAppP _ (List2 a b c) -> this <> foldt fp (a : b : c)
  OpAppP {} -> this
  HiddenP _ x -> this <> foldn fp x
  InstanceP _ x -> this <> foldn fp x
  ParenP _ x -> this <> fp x
  WildP {} -> this
  AbsurdP {} -> this
  AsP _ _ x -> this <> fp x
  DotP {} -> this
  LitP {} -> this
  RecP _ as -> this <> foldt (foldfa fp) as
  EqualP {} -> error "TODO"
  -- foldPat fn p@(EqualP _ xs) = fn p <> foldt (foldExpr fn) x
  --   where
  --     x = concatMap (\(a, b) -> [a, b]) xs
  EllipsisP _ x -> this <> foldm fp x
  WithP _ x -> this <> fp x
  where
    p = P p'
    this = fn p
    fp = foldPat fn

asp :: Monoid m => (Pattern -> m) -> (Node -> m)
asp fn = f
  where
    f (P p) = fn p
    f (E _) = mempty
    f (D _) = mempty

asq :: Monoid m => (QName -> m) -> (Node -> m)
asq fn = f
  where
    f (P (IdentP _ x)) = fn x
    f (P _) = mempty
    f (E (Ident x)) = fn x
    f (E _) = mempty
    f (D (TypeSig _ _ n _)) = fn (QName n)
    f (D (Module _ _ n _ _)) = fn n
    f (D (Data _ _ n _ _ _)) = fn (QName n)
    f (D _) = mempty

foldt :: Monoid m => (e -> m) -> [e] -> m
foldt f (x : xs) = f x <> foldt f xs
foldt _ [] = mempty

foldm :: Monoid m => (e -> m) -> Maybe e -> m
foldm _ Nothing = mempty
foldm fn (Just x) = fn x

folde :: (e -> m) -> (f -> m) -> Either e f -> m
folde fn _ (Left x) = fn x
folde _ fn (Right x) = fn x

foldn :: (e -> m) -> Named_ e -> m
foldn fn (Named _ x) = fn x

folda :: (e -> m) -> NamedArg e -> m
folda fn (Arg _ x) = foldn fn x

foldfa :: (e -> m) -> FieldAssignment' e -> m
foldfa fn (FieldAssignment _ x) = fn x

foldrh :: Monoid m => (e -> m) -> RHS' e -> m
foldrh _ AbsurdRHS = mempty
foldrh fn (RHS x) = fn x

foldwc :: Monoid m => (e -> m) -> WhereClause' e -> m
foldwc _ NoWhere = mempty
foldwc fn (AnyWhere _ ds) = fn ds
foldwc _ (SomeWhere {}) = error "TODO"
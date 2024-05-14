module Core (
    bindsOfPattern,
    Binding (ImplicitB, ExplicitB),
) where

import Agda.Syntax.Common
import Agda.Syntax.Concrete
import Agda.Utils.List1 (NonEmpty ((:|)))
import Agda.Utils.List2 (List2 (List2))
import Language.LSP.Protocol.Types qualified as LSP
import AgdaToLSP (toLSPRange', toLSPRange)

data Binding = ImplicitB String LSP.Range | ExplicitB String LSP.Range deriving Show

bindsOfNamedPattern :: Bool -> [Binding] -> NamedArg Pattern -> [Binding]
bindsOfNamedPattern scope impl (Arg {unArg = Named {namedThing = p}}) = bindsOfPattern scope impl p

-- returns all the bindings of a pattern
bindsOfPattern :: Bool -> [Binding] -> Pattern -> [Binding]
bindsOfPattern False bs (IdentP _ (QName name)) = ExplicitB name' range : bs
  where
    (range, name') = unpackName name
bindsOfPattern True bs (IdentP _ (QName name)) = ImplicitB name' range : bs
  where
    (range, name') = unpackName name
bindsOfPattern _ bs (QuoteP _) = bs
bindsOfPattern impl bs (AppP fun arg) = argScope
  where
    funScope = bindsOfPattern impl bs fun
    argScope = bindsOfNamedPattern impl funScope arg
-- TODO not sure why I require reverse here
bindsOfPattern impl bs (RawAppP _ (List2 a b c)) = reverse $ foldl (bindsOfPattern impl) bs (a : b : c)
bindsOfPattern _ bs (HiddenP range (Named {namedThing = p})) = case toLSPRange range of
  Just lspRange -> ImplicitB (patternName p) lspRange : bs
  _ -> bs
bindsOfPattern impl bs (ParenP _ p) = bindsOfPattern impl bs p
bindsOfPattern _ bs (WildP _) = bs
bindsOfPattern _ bs (AbsurdP _) = bs
bindsOfPattern impl bs (AsP _ name p) = ExplicitB name' range : bs'
  where
    (range, name') = unpackName name
    bs' = bindsOfPattern impl bs p
bindsOfPattern _ bs (DotP _ _) = bs
bindsOfPattern _ bs (LitP _ _) = bs
bindsOfPattern _ bs (EqualP _ _) = bs
-- -- EllipsisP ?
-- -- WithP ?
bindsOfPattern _ bs _ = bs

patternName :: Pattern -> String
patternName (IdentP _ (QName (Name {nameNameParts = ((Id a) :| [])}))) = a
patternName _ = ""

unpackName :: Name -> (LSP.Range, String)
unpackName (Name {nameRange = range, nameNameParts = ((Id a) :| [])}) = (toLSPRange' range, a)
-- TODO what happens when NameParts is not a single Id?
unpackName (Name {nameRange = range, nameNameParts = names}) = (toLSPRange' range, show names)
unpackName (NoName {nameRange = range}) = (toLSPRange' range, "_")

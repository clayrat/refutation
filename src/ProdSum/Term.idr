module ProdSum.Term

import Data.List.Elem
import ProdSum.Ty

%default total

public export
data Term : List Ty -> Ty -> Type where
  Var  : Elem a g -> Term g a
  Lam  : Term (a::g) b -> Term g (a~>b)
  App  : Term g (a~>b) -> Term g a -> Term g b
  Pair : Term g a -> Term g b -> Term g (Prod a b)
  Inl  : Term g a -> Term g (Sum a b)
  Inr  : Term g b -> Term g (Sum a b)
  Fst  : Term g (Prod a b) -> Term g a
  Snd  : Term g (Prod a b) -> Term g b
  Case : Term g (Sum a b) -> Term (a::g) c -> Term (b::g) c -> Term g c

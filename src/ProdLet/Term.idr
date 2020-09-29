module ProdLet.Term

import Data.List.Elem
import ProdLet.Ty

%default total

public export
data Term : List Ty -> Ty -> Type where
  Var  : Elem a g -> Term g a
  Lam  : Term (a::g) b -> Term g (a~>b)
  App  : Term g (a~>b) -> Term g a -> Term g b
  TT   : Term g U
  Pair : Term g a -> Term g b -> Term g (Prod a b)
  LetP : Term g (Prod a b) -> Term (b::a::g) c -> Term g c

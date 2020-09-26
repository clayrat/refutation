module ProdSum.Parser

import ProdSum.Ty

%default total

-- bidirectional-style raw terms

mutual
  public export
  data Val : Type where
    Lam  : String -> Val -> Val
    Pair : Val -> Val -> Val
    Inl  : Val -> Val
    Inr  : Val -> Val
    Case : Neu -> String -> Val -> String -> Val -> Val
    Emb  : Neu -> Val

  public export
  data Neu : Type where
    Var : String -> Neu
    App : Neu -> Val -> Neu
    Fst : Neu -> Neu
    Snd : Neu -> Neu
    Cut : Val -> Ty -> Neu

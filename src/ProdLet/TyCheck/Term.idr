module ProdLet.TyCheck.Term

import Decidable.Equality
import Data.List
import Ctx
import ProdLet.Ty
import ProdLet.Term
import ProdLet.Parser

%default total

mutual
  public export
  data Val : Ctx Ty -> Val -> Ty -> Type where
    Lam  : Val ((s,a)::g) v b -> Val g (Lam s v) (a~>b)
    TT   : Val g TT U
    Pair : Val g l a -> Val g r b -> Val g (Pair l r) (Prod a b)
    LetP : -- {a, b : Ty} ->
           Neu g l (Prod a b) -> Val ((y,b)::(x,a)::g) m c -> Val g (LetP l x y m) c
    Emb  : Neu g m a -> a = b -> Val g (Emb m) b

  public export
  data Neu : Ctx Ty -> Neu -> Ty -> Type where
    Var : InCtx g s a -> Neu g (Var s) a
    App : -- {a : Ty} ->
          Neu g l (a~>b) -> Val g m a -> Neu g (App l m) b
    Cut : Val g m a -> Neu g (Cut m a) a

export
Uninhabited (Val _ (Lam _ _) U) where
  uninhabited (Lam _) impossible

export
Uninhabited (Val _ (Lam _ _) (Prod _ _)) where
  uninhabited (Lam _) impossible

export
Uninhabited (Val _ TT (Imp _ _)) where
  uninhabited TT impossible

export
Uninhabited (Val _ TT (Prod _ _)) where
  uninhabited TT impossible

export
Uninhabited (Val _ (Pair _ _) U) where
  uninhabited (Pair _ _) impossible

export
Uninhabited (Val _ (Pair _ _) (Imp _ _)) where
  uninhabited (Pair _ _) impossible

export
neuUniq : Neu g n a -> Neu g n b -> a = b
neuUniq (Var i1)   (Var i2)       = inCtxUniq i1 i2
neuUniq (App t1 _) (App t2 _)     = snd $ impInj $ neuUniq t1 t2
neuUniq (Cut v1)   (Cut v2)       = Refl

export
notArg0 : Neu g n (a~>b) -> Not (Val g m a) -> Not (c ** Neu g (App n m) c)
notArg0 n nv (_ ** App t u) =
  case fst $ impInj $ neuUniq n t of
    Refl => nv u

export
notArg : Neu g n (a~>b) -> Not (Val g m a) -> Not (Neu g (App n m) c)
notArg n nv (App t u) =
  case fst $ impInj $ neuUniq n t of
    Refl => nv u

export
notSwitch : Neu g n a -> Not (a = b) -> Not (Val g (Emb n) b)
notSwitch n neq (Emb v eq) =
  case neuUniq n v of
    Refl => neq eq

export
notLetP : Neu g n (Prod a b) -> Not (Val ((y, b) :: ((x, a) :: g)) v c) -> Not (Val g (LetP n x y v) c)
notLetP n nv (LetP n0 v0) =
  let (prf1, prf2) = prodInj $ neuUniq n n0 in
  nv $ rewrite prf1 in
       rewrite prf2 in
       v0

mutual
  export
  val2Term : Val g m a -> Term (eraseCtx g) a
  val2Term (Lam v)      = Lam $ val2Term v
  val2Term  TT          = TT
  val2Term (Pair l r)   = Pair (val2Term l) (val2Term r)
  val2Term (LetP n v)   = LetP (neu2Term n) (val2Term v)
  val2Term (Emb v Refl) = neu2Term v

  export
  neu2Term : Neu g n a -> Term (eraseCtx g) a
  neu2Term (Var i)   = Var $ eraseInCtx i
  neu2Term (App t u) = App (neu2Term t) (val2Term u)
  neu2Term (Cut v)   = val2Term v
module ProdSum.TyCheck.Term

import Decidable.Equality
import Data.List
import Ctx
import ProdSum.Ty
import ProdSum.Term
import ProdSum.Parser

%default total

mutual
  public export
  data Val : Ctx Ty -> Val -> Ty -> Type where
    Lam  : Val ((s,a)::g) v b -> Val g (Lam s v) (a~>b)
    Pair : Val g l a -> Val g r b -> Val g (Pair l r) (Prod a b)
    Inl  : Val g l a -> Val g (Inl l) (Sum a b)
    Inr  : Val g r b -> Val g (Inr r) (Sum a b)
    Case : Neu g x (Sum a b) -> Val ((s,a)::g) l c -> Val ((t,b)::g) r c -> Val g (Case x s l t r) c
    Emb  : Neu g m a -> a = b -> Val g (Emb m) b

  public export
  data Neu : Ctx Ty -> Neu -> Ty -> Type where
    Var : InCtx g s a -> Neu g (Var s) a
    App : Neu g l (a~>b) -> Val g m a -> Neu g (App l m) b
    Fst : Neu g l (Prod a b) -> Neu g (Fst l) a
    Snd : Neu g r (Prod a b) -> Neu g (Snd r) b
    Cut : Val g m a -> Neu g (Cut m a) a

export
Uninhabited (Val _ (Lam _ _) A) where
  uninhabited (Lam _) impossible

export
Uninhabited (Val _ (Lam _ _) (Prod _ _)) where
  uninhabited (Lam _) impossible

export
Uninhabited (Val _ (Lam _ _) (Sum _ _)) where
  uninhabited (Lam _) impossible

export
Uninhabited (Val _ (Pair _ _) A) where
  uninhabited (Pair _ _) impossible

export
Uninhabited (Val _ (Pair _ _) (Imp _ _)) where
  uninhabited (Pair _ _) impossible

export
Uninhabited (Val _ (Pair _ _) (Sum _ _)) where
  uninhabited (Pair _ _) impossible

export
Uninhabited (Val _ (Inl _) A) where
  uninhabited (Inl _) impossible

export
Uninhabited (Val _ (Inl _) (Imp _ _)) where
  uninhabited (Inl _) impossible

export
Uninhabited (Val _ (Inl _) (Prod _ _)) where
  uninhabited (Inl _) impossible

export
Uninhabited (Val _ (Inr _) A) where
  uninhabited (Inr _) impossible

export
Uninhabited (Val _ (Inr _) (Imp _ _)) where
  uninhabited (Inr _) impossible

export
Uninhabited (Val _ (Inr _) (Prod _ _)) where
  uninhabited (Inr _) impossible

export
neuUniq : Neu g n a -> Neu g n b -> a = b
neuUniq (Var i1)   (Var i2)   = inCtxUniq i1 i2
neuUniq (App t1 _) (App t2 _) = snd $ impInj $ neuUniq t1 t2
neuUniq (Fst t1)   (Fst t2)   = fst $ prodInj $ neuUniq t1 t2
neuUniq (Snd t1)   (Snd t2)   = snd $ prodInj $ neuUniq t1 t2
neuUniq (Cut v1)   (Cut v2)   = Refl

export
notArg : Neu g n (a~>b) -> Not (Val g m a) -> Not (Neu g (App n m) c)
notArg n nv (App t u) =
  case fst $ impInj $ neuUniq n t of
    Refl => nv u

export
notLeft : Neu g n (Sum a b) -> Not (Val ((x,a)::g) l t) -> Not (Val g (Case n x l y r) t)
notLeft n nv (Case nn p _) =
  case fst $ sumInj $ neuUniq n nn of
    Refl => nv p

export
notRight : Neu g n (Sum a b) -> Not (Val ((y,b)::g) r t) -> Not (Val g (Case n x l y r) t)
notRight n nv (Case nn _ q) =
  case snd $ sumInj $ neuUniq n nn of
    Refl => nv q

export
notSwitch : Neu g n a -> Not (a = b) -> Not (Val g (Emb n) b)
notSwitch n neq (Emb v eq) =
  case neuUniq n v of
    Refl => neq eq

mutual
  export
  val2Term : Val g m a -> Term (eraseCtx g) a
  val2Term (Lam v)      = Lam $ val2Term v
  val2Term (Pair l r)   = Pair (val2Term l) (val2Term r)
  val2Term (Inl l)      = Inl $ val2Term l
  val2Term (Inr r)      = Inr $ val2Term r
  val2Term (Case n l r) = Case (neu2Term n) (val2Term l) (val2Term r)
  val2Term (Emb v Refl) = neu2Term v

  export
  neu2Term : Neu g n a -> Term (eraseCtx g) a
  neu2Term (Var i)   = Var $ eraseInCtx i
  neu2Term (Fst n)   = Fst $ neu2Term n
  neu2Term (Snd n)   = Snd $ neu2Term n
  neu2Term (Cut v)   = val2Term v
  neu2Term (App t u) = App (neu2Term t) (val2Term u)
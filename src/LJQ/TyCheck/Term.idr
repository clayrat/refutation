module LJQ.TyCheck.Term

import Decidable.Equality
import Data.List
import Ctx
import LJQ.Ty
--import LJQ.Term
import LJQ.Parser

%default total

mutual
  public export
  data Val : Ctx Ty -> Val -> Ty -> Type where
    Lam : Neu ((s,a)::g) v b -> Val g (Lam s v) (a~>b)
    Emb : NeuV g n a -> a = b -> Val g (Emb n) b

  public export
  data NeuV : Ctx Ty -> NeuV -> Ty -> Type where
    Var : InCtx g s a -> NeuV g (Var s) a
    Cut : Val g m a -> NeuV g (Cut m a) a

  public export
  data Neu : Ctx Ty -> Neu -> Ty -> Type where
    V    : NeuV g m a -> Neu g (V m) a
    GApp : {a, b : Ty} ->
           InCtx g s (a~>b) -> Val g m a -> Neu ((x,b)::g) n c -> Neu g (GApp x s m n) c
    Let  : {a : Ty} ->
           NeuV g m a -> Neu ((x,a)::g) n b -> Neu g (Let x m n) b

export
Uninhabited (Val _ (Lam _ _) A) where
  uninhabited (Lam _) impossible

export
neuVUniq : NeuV g n a -> NeuV g n b -> a = b
neuVUniq (Var i1) (Var i2) = inCtxUniq i1 i2
neuVUniq (Cut v1) (Cut v2) = Refl

export
neuUniq : Neu g n c -> Neu g n d -> c = d
neuUniq (V nv1)         (V nv2)         = neuVUniq nv1 nv2
neuUniq (GApp el1 _ n1) (GApp el2 _ n2) =
  case snd $ impInj $ inCtxUniq el1 el2 of
    Refl => neuUniq n1 n2
neuUniq (Let nv1 n1)    (Let nv2 n2)    =
  case neuVUniq nv1 nv2 of
    Refl => neuUniq n1 n2
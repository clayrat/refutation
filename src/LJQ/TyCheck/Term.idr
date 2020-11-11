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
    GApp : InCtx g s (a~>b) -> Val g m a -> Neu ((x,b)::g) n c -> Neu g (GApp x s m n) c
    Let  : NeuV g m a -> Neu ((x,a)::g) n b -> Neu g (Let x m n) b
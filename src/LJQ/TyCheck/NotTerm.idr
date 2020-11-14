module LJQ.TyCheck.NotTerm

import Decidable.Equality
import Data.List
import Ctx
import LJQ.Ty
import LJQ.Parser
import LJQ.TyCheck.Term

%default total

mutual
  public export
  data NotVal : Ctx Ty -> Val -> Ty -> Type where
    NotLamT : {t : Ty} ->
              NotBi t Imp -> NotVal g (Lam s n)  t
    NotLamN : Neu ((s,a)::g) n c -> Not (b = c) -> NotVal g (Lam s n) (a~>b)

    NotLam : NotNeu ((s,a)::g) n -> NotVal g (Lam s n) (a~>b)

    NotEmb  : NotNeuV g m                              -> NotVal g (Emb m) a
    NotEmbQ : {a, b : Ty} ->
              NeuV g m a -> Not (a = b) -> NotVal g (Emb m) b

  public export
  data NotNeuV : Ctx Ty -> NeuV -> Type where
    NotVar : {s : String} -> {g : Ctx Ty} ->
             NotInCtx g s -> NotNeuV g (Var s)
    NotCut : NotVal g m a -> NotNeuV g (Cut m a)

  public export
  data NotNeu : Ctx Ty -> Neu -> Type where
    NotV : NotNeuV g m -> NotNeu g (V m)

    NotGAppT : InCtx g s t -> NotBi t Imp -> NotNeu g (GApp x s v n)
    NotGAppE : NotInCtx g s -> NotNeu g (GApp x s v n)
    NotGAppV : InCtx g s (a~>b) -> NotVal g v a -> NotNeu g (GApp x s v n)
    NotGAppN : InCtx g s (a~>b) -> NotNeu ((x,b)::g) n -> NotNeu g (GApp x s v n)

    NotLetV : NotNeuV g nv -> NotNeu g (Let x nv n)
    NotLetN : NeuV g nv a -> NotNeu ((x,a)::g) n -> NotNeu g (Let x nv n)

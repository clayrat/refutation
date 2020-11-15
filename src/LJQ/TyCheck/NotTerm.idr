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
              NotBi t Imp                     -> NotVal g (Lam s n)  t
    NotLam  : NotNeu ((s,a)::g) n             -> NotVal g (Lam s n) (a~>b)
    NotLamN : Neu ((s,a)::g) n c -> Not (b=c) -> NotVal g (Lam s n) (a~>b)

    NotEmb  : NotNeuV g m             -> NotVal g (Emb m) a
    NotEmbQ : {a, b : Ty} ->
              NeuV g m a -> Not (a=b) -> NotVal g (Emb m) b

  public export
  data NotNeuV : Ctx Ty -> NeuV -> Type where
    NotVar : {s : String} -> {g : Ctx Ty} ->
             NotInCtx g s -> NotNeuV g (Var s)
    NotCut : NotVal g m a -> NotNeuV g (Cut m a)

  public export
  data NotNeu : Ctx Ty -> Neu -> Type where
    NotV : NotNeuV g m -> NotNeu g (V m)

    NotGAppT : InCtx g s t -> NotBi t Imp              -> NotNeu g (GApp x s v n)
    NotGAppE : NotInCtx g s                            -> NotNeu g (GApp x s v n)
    NotGAppV : InCtx g s (a~>b) -> NotVal g v a        -> NotNeu g (GApp x s v n)
    NotGAppN : InCtx g s (a~>b) -> NotNeu ((x,b)::g) n -> NotNeu g (GApp x s v n)

    NotLetV : NotNeuV g nv                       -> NotNeu g (Let x nv n)
    NotLetN : NeuV g nv a -> NotNeu ((x,a)::g) n -> NotNeu g (Let x nv n)

mutual
  export
  valNot : NotVal g m a -> Val g m a -> Void
  valNot (NotLamT ctra)  (Lam _)        = ctra Refl
  valNot (NotLam nn)     (Lam n)        = neuNot nn n
  valNot (NotLamN n neq) (Lam n2)       = neq $ neuUniq n2 n

  valNot (NotEmb nnv)     (Emb nv Refl) = neuVNot nnv nv
  valNot (NotEmbQ nv neq) (Emb nv2 prf) = neq $ trans (neuVUniq nv nv2) prf

  export
  neuVNot : NotNeuV g m -> NeuV g m a -> Void
  neuVNot (NotVar nc) (Var c) = notInCtx nc c
  neuVNot (NotCut nv) (Cut v) = valNot nv v

  export
  neuNot : NotNeu g m -> Neu g m a -> Void
  neuNot (NotV nnv)       (V nv)        = neuVNot nnv nv
  neuNot (NotGAppT c neq) (GApp c2 _ _) = neq $ inCtxUniq c c2
  neuNot (NotGAppE nc)    (GApp c  _ _) = notInCtx nc c
  neuNot (NotGAppV c nv)  (GApp c2 v _) = case fst $ impInj $ inCtxUniq c c2 of
                                            Refl => valNot nv v
  neuNot (NotGAppN c nn)  (GApp c2 _ n) = case snd $ impInj $ inCtxUniq c c2 of
                                            Refl => neuNot nn n
  neuNot (NotLetV nnv)    (Let nv _)    = neuVNot nnv nv
  neuNot (NotLetN nv nn)  (Let nv2 n)   = case neuVUniq nv nv2 of
                                            Refl => neuNot nn n

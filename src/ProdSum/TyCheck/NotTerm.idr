module ProdSum.TyCheck.NotTerm

import Decidable.Equality
import Data.List
import Ctx
import ProdSum.Ty
import ProdSum.Parser
import ProdSum.TyCheck.Term

%default total

mutual
  public export
  data NotVal : Ctx Ty -> Val -> Ty -> Type where
    NotLamA   :                          NotVal g (Lam s v)  A
    NotLamPr  :                          NotVal g (Lam s v) (Prod a b)
    NotLamSu  :                          NotVal g (Lam s v) (Sum a b)
    NotLam    : NotVal ((s,a)::g) v b -> NotVal g (Lam s v) (a~>b)

    NotPairA  :                 NotVal g (Pair l r)  A
    NotPairIm :                 NotVal g (Pair l r) (a~>b)
    NotPairSu :                 NotVal g (Pair l r) (Sum a b)
    NotPairL  : NotVal g l a -> NotVal g (Pair l r) (Prod a b)
    NotPairR  : NotVal g r b -> NotVal g (Pair l r) (Prod a b)

    NotInlA   :                 NotVal g (Inl l)  A
    NotInlIm  :                 NotVal g (Inl l) (a~>b)
    NotInlPr  :                 NotVal g (Inl l) (Prod a b)
    NotInl    : NotVal g l a -> NotVal g (Inl l) (Sum a b)

    NotInrA   :                 NotVal g (Inr r)  A
    NotInrIm  :                 NotVal g (Inr r) (a~>b)
    NotInrPr  :                 NotVal g (Inr r) (Prod a b)
    NotInr    : NotVal g r b -> NotVal g (Inr r) (Sum a b)

    NotCaseA   : Neu g c A                                  -> NotVal g (Case c x l y r) t
    NotCaseIm  : Neu g c (Imp a b)                          -> NotVal g (Case c x l y r) t
    NotCasePr  : Neu g c (Prod a b)                         -> NotVal g (Case c x l y r) t
    NotCaseL   : Neu g c (Sum a b) -> NotVal ((x,a)::g) l t -> NotVal g (Case c x l y r) t
    NotCaseR   : Neu g c (Sum a b) -> NotVal ((y,b)::g) r t -> NotVal g (Case c x l y r) t
    NotCase    : NotNeu g c                                 -> NotVal g (Case c x l y r) t

    NotEmb   : NotNeu g m               -> NotVal g (Emb m) a
    NotEmbQ  : Neu g m a -> Not (a = b) -> NotVal g (Emb m) b

  public export
  data NotNeu : Ctx Ty -> Neu -> Type where
    NotVar    : NotInCtx g s -> NotNeu g (Var s)

    NotFstA   : Neu g n A         -> NotNeu g (Fst n)
    NotFstIm  : Neu g n (Imp a b) -> NotNeu g (Fst n)
    NotFstSu  : Neu g n (Sum a b) -> NotNeu g (Fst n)
    NotFst    : NotNeu g n        -> NotNeu g (Fst n)

    NotSndA   : Neu g n A         -> NotNeu g (Snd n)
    NotSndIm  : Neu g n (Imp a b) -> NotNeu g (Snd n)
    NotSndSu  : Neu g n (Sum a b) -> NotNeu g (Snd n)
    NotSnd    : NotNeu g n        -> NotNeu g (Snd n)

    NotAppF   : NotNeu g l                     -> NotNeu g (App l m)
    NotAppFA  : Neu g l A                      -> NotNeu g (App l m)
    NotAppFPr : Neu g l (Prod a b)             -> NotNeu g (App l m)
    NotAppFSu : Neu g l (Sum a b)              -> NotNeu g (App l m)
    NotAppA   : Neu g l (a~>b) -> NotVal g m a -> NotNeu g (App l m)

    NotCut    : NotVal g m a -> NotNeu g (Cut m a)

--lem : NotVal [] (Pair (Emb $ Var "x") (Emb $ Var "y")) (Sum a (Imp a a))
--lem = NotPairSu

mutual
  export
  valNot : NotVal g m a -> Val g m a -> Void
  valNot  NotLamA          v                    = uninhabited v
  valNot  NotLamPr         v                    = uninhabited v
  valNot  NotLamSu         v                    = uninhabited v
  valNot (NotLam nv)      (Lam v)               = valNot nv v

  valNot  NotPairA         v                    = uninhabited v
  valNot  NotPairIm        v                    = uninhabited v
  valNot  NotPairSu        v                    = uninhabited v
  valNot (NotPairL nl)    (Pair l _)            = valNot nl l
  valNot (NotPairR nr)    (Pair _ r)            = valNot nr r

  valNot  NotInlA          v                    = uninhabited v
  valNot  NotInlPr         v                    = uninhabited v
  valNot  NotInlIm         v                    = uninhabited v
  valNot (NotInl nv)      (Inl v)               = valNot nv v

  valNot  NotInrA          v                    = uninhabited v
  valNot  NotInrPr         v                    = uninhabited v
  valNot  NotInrIm         v                    = uninhabited v
  valNot (NotInr nv)      (Inr v)               = valNot nv v

  valNot (NotCaseA n)     (Case n0 _ _)         = uninhabited $ neuUniq n n0
  valNot (NotCaseIm n)    (Case n0 _ _)         = uninhabited $ neuUniq n n0
  valNot (NotCasePr n)    (Case n0 _ _)         = uninhabited $ neuUniq n n0
  valNot (NotCaseL n0 nv)  v                    = notLeft n0 (valNot nv) v
  valNot (NotCaseR n0 nv)  v                    = notRight n0 (valNot nv) v
  valNot (NotCase nn)     (Case {a} {b} n0 _ _) = neuNot nn (n0)

  valNot (NotEmb nn)      (Emb n Refl)          = neuNot nn (n)
  valNot (NotEmbQ n neq)   v                    = notSwitch n neq v

  export
  neuNot : NotNeu g m -> Neu g m a -> Void
  neuNot (NotVar nc)     (Var c)       = notInCtx nc c
  neuNot (NotAppF nn)    (App n _) = neuNot nn (n)
  neuNot (NotAppFA na)   (App n _)     = uninhabited $ neuUniq na n
  neuNot (NotAppFPr na)  (App n _)     = uninhabited $ neuUniq na n
  neuNot (NotAppFSu na)  (App n _)     = uninhabited $ neuUniq na n
  neuNot (NotAppA n0 nv)  tn              = notArg n0 (valNot nv) ?wat
  neuNot (NotFstA na)    (Fst n)       = uninhabited $ neuUniq na n
  neuNot (NotFstSu na)   (Fst n)       = uninhabited $ neuUniq na n
  neuNot (NotFstIm na)   (Fst n)       = uninhabited $ neuUniq na n
  neuNot (NotFst nn)     (Fst n)   = neuNot nn (n)
  neuNot (NotSndA na)    (Snd n)       = uninhabited $ neuUniq na n
  neuNot (NotSndSu na)   (Snd n)       = uninhabited $ neuUniq na n
  neuNot (NotSndIm na)   (Snd n)       = uninhabited $ neuUniq na n
  neuNot (NotSnd nn)     (Snd n)   = neuNot nn (n)
  neuNot (NotCut nv)     (Cut v)       = valNot nv v

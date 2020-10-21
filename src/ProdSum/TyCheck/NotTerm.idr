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
    NotLamT   : {t : Ty} -> NotBi t Imp -> NotVal g (Lam s v)  t
    NotLam    : NotVal ((s,a)::g) v b   -> NotVal g (Lam s v) (a~>b)

    NotPairT  : {t : Ty} -> NotBi t Prod -> NotVal g (Pair l r)  t
    NotPairL  : NotVal g l a             -> NotVal g (Pair l r) (Prod a b)
    NotPairR  : NotVal g r b             -> NotVal g (Pair l r) (Prod a b)

    NotInlT   : {t : Ty} -> NotBi t Sum -> NotVal g (Inl l)  t
    NotInl    : NotVal g l a            -> NotVal g (Inl l) (Sum a b)

    NotInrT   : {t : Ty} -> NotBi t Sum -> NotVal g (Inr r)  t
    NotInr    : NotVal g r b            -> NotVal g (Inr r) (Sum a b)

    NotCaseT   : {q : Ty} -> Neu g c q -> NotBi q Sum       -> NotVal g (Case c x l y r) t
    NotCaseL   : Neu g c (Sum a b) -> NotVal ((x,a)::g) l t -> NotVal g (Case c x l y r) t
    NotCaseR   : Neu g c (Sum a b) -> NotVal ((y,b)::g) r t -> NotVal g (Case c x l y r) t
    NotCase    : NotNeu g c                                 -> NotVal g (Case c x l y r) t

    NotEmb   : NotNeu g m                              -> NotVal g (Emb m) a
    NotEmbQ  : {a, b : Ty} -> Neu g m a -> Not (a = b) -> NotVal g (Emb m) b

  public export
  data NotNeu : Ctx Ty -> Neu -> Type where
    NotVar    : {s : String} -> {g : Ctx Ty} -> NotInCtx g s -> NotNeu g (Var s)

    NotFstT   : {q : Ty} -> Neu g n q -> NotBi q Prod -> NotNeu g (Fst n)
    NotFst    : NotNeu g n                            -> NotNeu g (Fst n)

    NotSndT   : {q : Ty} -> Neu g n q -> NotBi q Prod -> NotNeu g (Snd n)
    NotSnd    : NotNeu g n                            -> NotNeu g (Snd n)

    NotAppF   : NotNeu g l                           -> NotNeu g (App l m)
    NotAppFT  : {q : Ty} -> Neu g l q -> NotBi q Imp -> NotNeu g (App l m)
    NotAppA   : Neu g l (a~>b) -> NotVal g m a       -> NotNeu g (App l m)

    NotCut    : NotVal g m a -> NotNeu g (Cut m a)

--lem : NotVal [] (Pair (Emb $ Var "x") (Emb $ Var "y")) (Sum a (Imp a a))
--lem = NotPairSu

mutual
  export
  valNot : NotVal g m a -> Val g m a -> Void
  valNot (NotLamT ctra)    (Lam _)       = ctra Refl
  valNot (NotLam nv)       (Lam v)       = valNot nv v

  valNot (NotPairT ctra)   (Pair _ _)    = ctra Refl
  valNot (NotPairL nl)     (Pair l _)    = valNot nl l
  valNot (NotPairR nr)     (Pair _ r)    = valNot nr r

  valNot (NotInlT ctra)    (Inl _)       = ctra Refl
  valNot (NotInl nv)       (Inl v)       = valNot nv v

  valNot (NotInrT ctra)    (Inr _)       = ctra Refl
  valNot (NotInr nv)       (Inr v)       = valNot nv v

  valNot (NotCaseT n ctra) (Case n0 _ _) = ctra $ neuUniq n n0
  valNot (NotCaseL n0 nv)   v            = notLeft n0 (valNot nv) v
  valNot (NotCaseR n0 nv)   v            = notRight n0 (valNot nv) v
  valNot (NotCase nn)      (Case n0 _ _) = neuNot nn n0

  valNot (NotEmb nn)       (Emb n Refl)  = neuNot nn n
  valNot (NotEmbQ n neq)    v            = notSwitch n neq v

  export
  neuNot : NotNeu g m -> Neu g m a -> Void
  neuNot (NotVar nc)       (Var c)    = notInCtx nc c

  neuNot (NotAppF nn)      (App n _)  = neuNot nn n
  neuNot (NotAppFT n ctra) (App n0 _) = ctra $ neuUniq n n0
  neuNot (NotAppA n0 nv)    tn        = notArg n0 (valNot nv) tn

  neuNot (NotFstT n ctra)  (Fst n0)   = ctra $ neuUniq n n0
  neuNot (NotFst nn)       (Fst n)    = neuNot nn n

  neuNot (NotSndT n ctra)  (Snd n0)   = ctra $ neuUniq n n0
  neuNot (NotSnd nn)       (Snd n)    = neuNot nn n

  neuNot (NotCut nv)       (Cut v)    = valNot nv v

mutual
  export
  Show (NotVal g m a) where
    show (NotLamT {t} _)       = "Expected function type for lambda, but got " ++ show t
    show (NotLam nv)           = show nv
    show (NotPairT {t} _)      = "Expected product type for pair, but got " ++ show t
    show (NotPairL nl)         = show nl
    show (NotPairR nr)         = show nr
    show (NotInlT {t} _)       = "Expected sum type for inl, but got " ++ show t
    show (NotInl nv)           = show nv
    show (NotInrT {t} _)       = "Expected sum type for inr, but got " ++ show t
    show (NotInr nv)           = show nv
    show (NotCaseT {q} _ _)    = "Expected sum type for case head, but got " ++ show q
    show (NotCaseL _ nv)       = show nv
    show (NotCaseR _ nv)       = show nv
    show (NotCase nn)          = show nn
    show (NotEmb nn)           = show nn
    show (NotEmbQ {a} {b} _ _) = "Expected " ++ show a ++ ", but got " ++ show b

  export
  Show (NotNeu g m) where
    show (NotVar {s} {g} _) = "Variable " ++ s ++ " not found in context " ++ show (fst <$> g)
    show (NotAppF nn)       = show nn
    show (NotAppFT {q} _ _) = "Expected function type for application head, but got " ++ show q
    show (NotAppA _ nv)     = show nv
    show (NotFstT {q} _ _)  = "Expected product type for fst, but got " ++ show q
    show (NotFst nn)        = show nn
    show (NotSndT {q} _ _)  = "Expected product type for snd, but got " ++ show q
    show (NotSnd nn)        = show nn
    show (NotCut nv)        = show nv
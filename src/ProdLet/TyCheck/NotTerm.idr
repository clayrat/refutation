module ProdLet.TyCheck.NotTerm

import Decidable.Equality
import Data.List
import Ctx
import ProdLet.Ty
import ProdLet.Parser
import ProdLet.TyCheck.Term

%default total

mutual
  public export
  data NotVal : Ctx Ty -> Val -> Ty -> Type where
    NotLamT : {t : Ty} -> NotBi t Imp -> NotVal g (Lam s v)  t
    NotLam  : NotVal ((s,a)::g) v b   -> NotVal g (Lam s v) (a~>b)

    NotPairT : {t : Ty} -> NotBi t Prod -> NotVal g (Pair l r)  t
    NotPairL : NotVal g l a             -> NotVal g (Pair l r) (Prod a b)
    NotPairR : NotVal g r b             -> NotVal g (Pair l r) (Prod a b)

    NotTTT : {t : Ty} -> Not (t=U) -> NotVal g TT t

    NotLetPT : {q : Ty} -> Neu g n q -> NotBi q Prod              -> NotVal g (LetP n x y v) t
    NotLetP  : NotNeu g n                                         -> NotVal g (LetP n x y v) t
    NotLetPC : Neu g n (Prod a b) -> NotVal ((y,b)::(x,a)::g) v t -> NotVal g (LetP n x y v) t

    NotEmb  : NotNeu g m                              -> NotVal g (Emb m) a
    NotEmbQ : {a, b : Ty} -> Neu g m a -> Not (a = b) -> NotVal g (Emb m) b

  public export
  data NotNeu : Ctx Ty -> Neu -> Type where
    NotVar    : {s : String} -> {g : Ctx Ty} -> NotInCtx g s -> NotNeu g (Var s)

    NotAppF   : NotNeu g l                           -> NotNeu g (App l m)
    NotAppFT  : {q : Ty} -> Neu g l q -> NotBi q Imp -> NotNeu g (App l m)
    NotAppA   : Neu g l (a~>b) -> NotVal g m a       -> NotNeu g (App l m)

    NotCut    : NotVal g m a -> NotNeu g (Cut m a)

mutual
  export
  valNot : NotVal g m a -> Val g m a -> Void
  valNot (NotLamT ctra)    (Lam _)      = ctra Refl
  valNot (NotLam nv)       (Lam v)      = valNot nv v

  valNot (NotPairT ctra)   (Pair _ _)   = ctra Refl
  valNot (NotPairL nl)     (Pair l _)   = valNot nl l
  valNot (NotPairR nr)     (Pair _ r)   = valNot nr r

  valNot (NotTTT ctra)     TT           = ctra Refl

  valNot (NotLetPT n ctra) (LetP n0 _)  = ctra $ neuUniq n n0
  valNot (NotLetP nn)      (LetP n0 _)  = neuNot nn n0
  valNot (NotLetPC n0 nv)   v           = notLetP n0 (valNot nv) v

  valNot (NotEmb nn)       (Emb n Refl) = neuNot nn n
  valNot (NotEmbQ n neq)    v           = notSwitch n neq v

  export
  neuNot : NotNeu g m -> Neu g m a -> Void
  neuNot (NotVar nc)       (Var c)    = notInCtx nc c

  neuNot (NotAppF nn)      (App n _)  = neuNot nn n
  neuNot (NotAppFT n ctra) (App n0 _) = ctra $ neuUniq n n0
  neuNot (NotAppA n0 nv)    tn        = notArg n0 (valNot nv) tn

  neuNot (NotCut nv)       (Cut v)    = valNot nv v

mutual
  export
  Show (NotVal g m a) where
    show (NotLamT {t} _)       = "Expected function type for lambda, but got " ++ show t
    show (NotLam nv)           = show nv
    show (NotPairT {t} _)      = "Expected product type for pair, but got " ++ show t
    show (NotPairL nl)         = show nl
    show (NotPairR nr)         = show nr
    show (NotTTT {t} _)        = "Expected unit type for tt, but got " ++ show t
    show (NotLetPT {q} _ _)    = "Expected product type for let head, but got " ++ show q
    show (NotLetP nn)          = show nn
    show (NotLetPC _ nv)       = show nv
    show (NotEmb nn)           = show nn
    show (NotEmbQ {a} {b} _ _) = "Expected " ++ show a ++ ", but got " ++ show b

  export
  Show (NotNeu g m) where
    show (NotVar {s} {g} _) = "Variable " ++ s ++ " not found in context " ++ show (fst <$> g)
    show (NotAppF nn)       = show nn
    show (NotAppFT {q} _ _) = "Expected function type for application head, but got " ++ show q
    show (NotAppA _ nv)     = show nv
    show (NotCut nv)        = show nv

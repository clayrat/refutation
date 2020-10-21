module Lin.TyCheck.NotTermLO

import Decidable.Equality
import Data.List
import Quantifiers
import Ctx
import ProdLet.Ty
import Lin.Usage.Ctx
import Lin.Parser
import Lin.TyCheck.TermLO

%default total

public export
NotBi : Ty -> (Ty -> Ty -> Ty) -> Type
NotBi t bt = {0 x, y : Ty} -> Not (t = bt x y)

mutual
  public export
  data NotVal : {0 ctx : Ctx Ty} -> Usages ctx -> Val -> Ty -> Type where
    NotLamT  : {t : Ty} -> NotBi t Imp             -> NotVal g (Lam s v)  t
    NotLamFr : {s : String} ->
               Val (Fr (s,a)::g) v b (Fr (s,a)::d) -> NotVal g (Lam s v) (a~>b)
    NotLam   : NotVal (Fr (s,a)::g) v b            -> NotVal g (Lam s v) (a~>b)

    NotTTT : {t : Ty} -> Not (t=U) -> NotVal g TT t

    NotLetT  : NotNeu g n                  -> NotVal g (LetT n v) t
    NotLetTT : {q : Ty} -> {0 d : Usages ctx} ->
               Neu g n q d -> Not (q=U)    -> NotVal g (LetT n v) t
    NotLetTC : Neu g n U d -> NotVal d v t -> NotVal g (LetT n v) t

    NotPairT : {t : Ty} -> NotBi t Prod    -> NotVal g (Pair l r)  t
    NotPairL : NotVal g l a                -> NotVal g (Pair l r) (Prod a b)
    NotPairR : Val g l a d -> NotVal d r b -> NotVal g (Pair l r) (Prod a b)

    NotLetP    : NotNeu g n                                                                      -> NotVal g (LetP n x y v) t
    NotLetPFrL : {x : String} ->
                 Neu g n (Prod a b) d -> Val (Fr (y,b)::Fr (x,a)::d) v t (St (y,b)::Fr (x,a)::s) -> NotVal g (LetP n x y v) t
    NotLetPFrR : {y : String} ->
                 Neu g n (Prod a b) d -> Val (Fr (y,b)::Fr (x,a)::d) v t (Fr (y,b)::w::s)        -> NotVal g (LetP n x y v) t
    NotLetPT   : {q : Ty} -> {0 d : Usages ctx} ->
                 Neu g n q d -> NotBi q Prod                                                     -> NotVal g (LetP n x y v) t
    NotLetPC   : Neu g n (Prod a b) d -> NotVal (Fr (y,b)::Fr (x,a)::d) v t                      -> NotVal g (LetP n x y v) t

    NotEmb  : NotNeu g m                 -> NotVal g (Emb m) a
    NotEmbQ : {a, b : Ty} -> {0 d : Usages ctx} ->
              Neu g m a d -> Not (a = b) -> NotVal g (Emb m) b

  public export
  data NotNeu : {0 ctx : Ctx Ty} -> Usages ctx -> Neu -> Type where
    NotVar    : NotInCtxLO g s -> NotNeu g (Var s)

    NotAppF   : NotNeu g l                       -> NotNeu g (App l m)
    NotAppFT  : {q : Ty} -> {0 d : Usages ctx} ->
                Neu g l q d -> NotBi q Imp       -> NotNeu g (App l m)
    NotAppA   : Neu g l (a~>b) d -> NotVal d m a -> NotNeu g (App l m)

    NotCut    : NotVal g m a -> NotNeu g (Cut m a)

mutual
  export
  valNot : NotVal g m a -> Val g m a d -> Void
  valNot (NotLamT ctra)    (Lam _)      = ctra Refl
  valNot (NotLamFr v)      (Lam v0)     = uninhabited $ fst $ allConsInjective $ valUniq v v0
  valNot (NotLam nv)       (Lam v)      = valNot nv v

  valNot (NotTTT ctra)     TT           = ctra Refl

  valNot (NotLetT nn)      (LetT n0 _)  = neuNot nn n0
  valNot (NotLetTT n ctra) (LetT n0 _)  = ctra $ fst $ neuUniq n n0
  valNot (NotLetTC n nv)   v           = notLetT n (valNot nv) v

  valNot (NotPairT ctra)   (Pair _ _)   = ctra Refl
  valNot (NotPairL nl)     (Pair l _)   = valNot nl l
  valNot (NotPairR l nr)  (Pair l0 r)   = case valUniq l l0 of Refl => valNot nr r

  valNot (NotLetP nn)      (LetP n0 _)  = neuNot nn n0
  valNot (NotLetPFrL n v)  (LetP n0 v0) =
    let (prft, prfc) = neuUniq n n0 in
    case (prodInj prft, prfc) of
      ((Refl, Refl), Refl) => uninhabited $ fst $ allConsInjective $ snd $ allConsInjective $ valUniq v v0
  valNot (NotLetPFrR n v)  (LetP n0 v0) =
    let (prft, prfc) = neuUniq n n0 in
    case (prodInj prft, prfc) of
      ((Refl, Refl), Refl) => uninhabited $ fst $ allConsInjective $ valUniq v v0
  valNot (NotLetPT n ctra) (LetP n0 _)  = ctra $ fst $ neuUniq n n0
  valNot (NotLetPC n nv)    v           = notLetP n (valNot nv) v

  valNot (NotEmb nn)       (Emb n Refl) = neuNot nn n
  valNot (NotEmbQ n0 neq)  v@(Emb n prf)  = neq $ trans (sym $ fst $ neuUniq n n0) prf

  export
  neuNot : NotNeu g m -> Neu g m a d -> Void
  neuNot (NotVar nc)       (Var c)    = notInCtxLO nc c

  neuNot (NotAppF nn)      (App n _)  = neuNot nn n
  neuNot (NotAppFT n ctra) (App n0 _) = ctra $ fst $ neuUniq n n0
  neuNot (NotAppA n0 nv)    tn        = notArg n0 (valNot nv) tn
  -- without this the totality checker seems to have a very hard time
  neuNot (NotCut nv)       (Cut v)    = assert_total $ valNot nv v

mutual
  export
  Show (NotVal g m a) where
    show (NotLamT {t} _)       = "Expected function type for lambda, but got " ++ show t
    show (NotLamFr {s} v)      = "Variable " ++ s ++ " not used in function body" -- ++ show v
    show (NotLam nv)           = show nv
    show (NotTTT {t} _)        = "Expected unit type for tt, but got " ++ show t
    show (NotLetT nn)          = show nn
    show (NotLetTT {q} _ _)    = "Expected unit type for let head, but got " ++ show q
    show (NotLetTC _ nv)       = show nv
    show (NotPairT {t} _)      = "Expected product type for pair, but got " ++ show t
    show (NotPairL nl)         = show nl
    show (NotPairR n nr)       = show nr
    show (NotLetP nn)          = show nn
    show (NotLetPFrL {x} n v)  = "Left-projected variable " ++ x ++ " not used in continuation body" -- ++ show v
    show (NotLetPFrR {y} n v)  = "Right-projected variable " ++ y ++ " not used in continuation body" -- ++ show v
    show (NotLetPT {q} _ _)    = "Expected product type for let head, but got " ++ show q
    show (NotLetPC _ nv)       = show nv
    show (NotEmb nn)           = show nn
    show (NotEmbQ {a} {b} _ _) = "Expected " ++ show a ++ ", but got " ++ show b

  export
  Show (NotNeu g m) where
    show (NotVar nv)        = show nv
    show (NotAppF nn)       = show nn
    show (NotAppFT {q} _ _) = "Expected function type for application head, but got " ++ show q
    show (NotAppA _ nv)     = show nv
    show (NotCut nv)        = show nv

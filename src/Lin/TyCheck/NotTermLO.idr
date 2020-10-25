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

mutual
  public export
  data NotVal : {0 ctx : Ctx Ty} -> Usages ctx -> Val -> Ty -> Usages ctx -> Type where
    NotLamT  : {t : Ty} ->
               NotBi t Imp                         -> NotVal g (Lam s v)  t     d
    NotLamFr : {s : String} ->
               Val (Fr (s,a)::g) v b (Fr (s,a)::d) -> NotVal g (Lam s v) (a~>b) d
    NotLam   : NotVal (Fr (s,a)::g) v b (u::d)          -> NotVal g (Lam s v) (a~>b) d

    NotTTT : {t : Ty} -> Not (t=U) -> NotVal g TT t d

    NotLetT  : NotNeu g n d                  -> NotVal g (LetT n v) t s
    NotLetTT : {q : Ty} -> --{0 d : Usages ctx} ->
               Neu g n q d -> Not (q=U)      -> NotVal g (LetT n v) t d
    NotLetTC : Neu g n U d -> NotVal d v t s -> NotVal g (LetT n v) t s

    NotPairT : {t : Ty} ->
               NotBi t Prod                  -> NotVal g (Pair l r)  t         d
    NotPairL : NotVal g l a d                -> NotVal g (Pair l r) (Prod a b) s
    NotPairR : Val g l a d -> NotVal d r b s -> NotVal g (Pair l r) (Prod a b) s

    NotLetP    : NotNeu g n d                                                                    -> NotVal g (LetP n x y v) t d
    NotLetPFrL : {x : String} ->
                 Neu g n (Prod a b) d -> Val (Fr (y,b)::Fr (x,a)::d) v t (St (y,b)::Fr (x,a)::s) -> NotVal g (LetP n x y v) t s
    NotLetPFrR : {y : String} ->
                 Neu g n (Prod a b) d -> Val (Fr (y,b)::Fr (x,a)::d) v t (Fr (y,b)::w::s)        -> NotVal g (LetP n x y v) t s
    NotLetPT   : {q : Ty} ->
                 Neu g n q d -> NotBi q Prod                                                     -> NotVal g (LetP n x y v) t d
    NotLetPC   : Neu g n (Prod a b) d -> NotVal (Fr (y,b)::Fr (x,a)::d) v t (u::w::s)                    -> NotVal g (LetP n x y v) t s

    NotEmb  : NotNeu g m d               -> NotVal g (Emb m) a d
    NotEmbQ : {a, b : Ty} ->
              Neu g m a d -> Not (a = b) -> NotVal g (Emb m) b d

  public export
  data NotNeu : {0 ctx : Ctx Ty} -> Usages ctx -> Neu -> Usages ctx -> Type where
    NotVar    : NotInCtxLO g s -> NotNeu g (Var s) d

    NotAppF   : NotNeu g l d                       -> NotNeu g (App l m) d
    NotAppFT  : {q : Ty} ->
                Neu g l q d -> NotBi q Imp         -> NotNeu g (App l m) d
    NotAppA   : Neu g l (a~>b) d -> NotVal d m a s -> NotNeu g (App l m) s

    NotCut    : NotVal g m a d -> NotNeu g (Cut m a) d

mutual
  export
  valNot : NotVal g m a d -> Val g m a d2 -> Void
  valNot (NotLamT ctra)    (Lam _)      = ctra Refl
  valNot (NotLamFr v)      (Lam v0)     = uninhabited $ fst $ allConsInjective $ valUniq v v0
  valNot (NotLam nv)       (Lam v)      = valNot nv v

  valNot (NotTTT ctra)      TT          = ctra Refl

  valNot (NotLetT nn)      (LetT n0 _)  = neuNot nn n0
  valNot (NotLetTT n ctra) (LetT n0 _)  = ctra $ fst $ neuUniq n n0
  valNot (NotLetTC n nv)    v           = notLetT n (valNot nv) v

  valNot (NotPairT ctra)   (Pair _ _)   = ctra Refl
  valNot (NotPairL nl)     (Pair l _)   = valNot nl l
  valNot (NotPairR l nr)   (Pair l0 r)  = case valUniq l l0 of Refl => valNot nr r

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
  valNot (NotEmbQ n0 neq)  (Emb n prf)  = neq $ trans (sym $ fst $ neuUniq n n0) prf

  export
  neuNot : NotNeu g m d -> Neu g m a d2 -> Void

  neuNot (NotVar nc)       (Var c)    = notInCtxLO nc c

  neuNot (NotAppF nn)      (App n _)  = neuNot nn n
  neuNot (NotAppFT n ctra) (App n0 _) = ctra $ fst $ neuUniq n n0
  neuNot (NotAppA n0 nv)    tn        = notArg n0 (valNot nv) tn
  -- without this the totality checker seems to have a very hard time
  neuNot (NotCut nv)       (Cut v)    = assert_total $ valNot nv v

mutual
  export
  Show (NotVal g m a d) where
    show (NotLamT {t} _)       = "Expected function type for lambda, but got " ++ show t
    show (NotLamFr {s} v)      = "Variable " ++ s ++ " not used in function body" -- ++ show v
    show (NotLam nv)           = assert_total $ show nv
    show (NotTTT {t} _)        = "Expected unit type for tt, but got " ++ show t
    show (NotLetT nn)          = assert_total $ show nn
    show (NotLetTT {q} _ _)    = "Expected unit type for let head, but got " ++ show q
    show (NotLetTC _ nv)       = assert_total $ show nv
    show (NotPairT {t} _)      = "Expected product type for pair, but got " ++ show t
    show (NotPairL nl)         = assert_total $ show nl
    show (NotPairR n nr)       = assert_total $ show nr
    show (NotLetP nn)          = assert_total $ show nn
    show (NotLetPFrL {x} n v)  = "Left-projected variable " ++ x ++ " not used in continuation body" -- ++ show v
    show (NotLetPFrR {y} n v)  = "Right-projected variable " ++ y ++ " not used in continuation body" -- ++ show v
    show (NotLetPT {q} _ _)    = "Expected product type for let head, but got " ++ show q
    show (NotLetPC _ nv)       = assert_total $ show nv
    show (NotEmb nn)           = assert_total $ show nn
    show (NotEmbQ {a} {b} _ _) = "Expected " ++ show a ++ ", but got " ++ show b

  export
  Show (NotNeu g m d) where
    show (NotVar nv)        = assert_total $ show nv
    show (NotAppF nn)       = assert_total $ show nn
    show (NotAppFT {q} _ _) = "Expected function type for application head, but got " ++ show q
    show (NotAppA _ nv)     = assert_total $ show nv
    show (NotCut nv)        = assert_total $ show nv

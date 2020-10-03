module Lin.TyCheck.TermLO

import Data.List.Quantifiers
import Decidable.Equality
--import Split
import Ctx
import ProdLet.Ty
import Lin.Parser
--import Lin.Term
import Lin.TyCheck.Usage

%default total

mutual
  public export
  data Val : {ctx : Ctx Ty} -> Usages ctx -> Val -> Ty -> Usages ctx -> Type where
    Lam  : Val (Fr (s,a)::g) v b (St (s,a)::d) -> Val g (Lam s v) (a~>b) d
    TT   : Val g TT U g
    LetT : {d : Usages ctx} ->
           Neu g l U d -> Val d r a s -> Val g (LetT l r) a s
    Pair : {d : Usages ctx} ->
           Val g l a d -> Val d r b s -> Val g (Pair l r) (Prod a b) s
    LetP : {a, b : Ty} -> {d : Usages ctx} ->
           Neu g l (Prod a b) d -> Val (Fr (y,b)::Fr (x,a)::d) r c (St (y,b)::St (x,a)::s) -> Val g (LetP l x y r) c s
    Emb  : Neu g m a d -> a = b -> Val g (Emb m) b d

  public export
  data Neu : {ctx : Ctx Ty} -> Usages ctx -> Neu -> Ty -> Usages ctx -> Type where
    Var : InCtxLO g s a d -> Neu g (Var s) a d
    App : {a : Ty} -> {d : Usages ctx} ->
          Neu g l (a~>b) d -> Val d m a s -> Neu g (App l m) b s
    Cut : Val g m a d -> Neu g (Cut m a) a d

export
Uninhabited (Val g (Lam _ _) U d) where
  uninhabited (Lam _) impossible

export
Uninhabited (Val g (Lam _ _) (Prod _ _) d) where
  uninhabited (Lam _) impossible

export
Uninhabited (Val g TT (Imp _ _) d) where
  uninhabited TT impossible

export
Uninhabited (Val g TT (Prod _ _) d) where
  uninhabited TT impossible

export
Uninhabited (Val g (Pair _ _) U d) where
  uninhabited (Pair _ _) impossible

export
Uninhabited (Val g (Pair _ _) (Imp _ _) d) where
  uninhabited (Pair _ _) impossible

-- TODO contribute

export
allConsInjective : {0 x, y : a} ->
                   {0 px : p x} -> {0 pxs : All p xs} -> {0 py : p y} -> {0 pys : All p ys} ->
                   the (All p (x::xs)) (px :: pxs) = the (All p (y::ys)) (py :: pys) -> (px=py, pxs=pys)
allConsInjective Refl = (Refl, Refl)

mutual
  export
  neuUniq : Neu g n a d1 -> Neu g n b d2 -> (a = b, d1 = d2)
  neuUniq (Var i1)    (Var i2)    = inCtxLOUniq i1 i2
  neuUniq (App t1 v1) (App t2 v2) =
    let (prft, prfc) = neuUniq t1 t2 in
    case (fst $ impInj prft, prfc) of
      (Refl, Refl) => (snd $ impInj prft, valUniq v1 v2)
  neuUniq (Cut v1)    (Cut v2)    = (Refl, valUniq v1 v2)

  export
  valUniq : Val g m a d1 -> Val g m a d2 -> d1 = d2
  valUniq (Lam v1)       (Lam v2)       = snd $ allConsInjective $ valUniq v1 v2
  valUniq  TT             TT            = Refl
  valUniq (LetT n1 v1)   (LetT n2 v2)   =
    case snd $ neuUniq n1 n2 of
      Refl => valUniq v1 v2
  valUniq (Pair v11 v12) (Pair v21 v22) =
    case valUniq v11 v21 of
      Refl => valUniq v12 v22
  valUniq (LetP n1 v1)   (LetP n2 v2)   =
    let (prft, prfc) = neuUniq n1 n2 in
    case (prodInj prft, prfc) of
      ((Refl, Refl), Refl) => snd $ allConsInjective $ snd $ allConsInjective $ valUniq v1 v2
  valUniq (Emb n1 Refl)    (Emb n2 Refl)    = snd $ neuUniq n1 n2

module Lin.TyCheck.TermLO

import Data.List.Quantifiers
import Decidable.Equality
import Quantifiers
import Ctx
import ProdLet.Ty
import Lin.Usage.Ctx
import Lin.Parser
import Lin.TermLO

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

export
notArg : Neu g n (a~>b) d -> Not (Val d m a s) -> Not (Neu g (App n m) c s)
notArg n nv (App t u) =
  let (prft, prfc) = neuUniq n t in
    case (fst $ impInj prft, prfc) of
      (Refl, Refl) => nv u

export
notSwitch : Neu g n a d -> Not (b = a) -> Not (Val g (Emb n) b d)
notSwitch n neq (Emb v eq) =
  case fst $ neuUniq n v of
    Refl => neq (sym eq)

export
notLetT : Neu g n U d -> Not (Val d v c s) -> Not (Val g (LetT n v) c s)
notLetT n nv (LetT n0 v0) =
  nv $ rewrite snd $ neuUniq n n0 in v0

export
notLetP : Neu g n (Prod a b) d -> Not (Val (Fr (y,b)::Fr (x,a)::d) v c (St (y,b)::St (x,a)::s)) -> Not (Val g (LetP n x y v) c s)
notLetP n nv (LetP n0 v0) =
  let (prft, prfc) = neuUniq n n0
      (prf1, prf2) = prodInj prft
   in
  nv $ rewrite prf1 in
       rewrite prf2 in
       rewrite prfc in
       v0

mutual
  export
  val2Term : Val g m a d -> Term (eraseCtxLO g) a (eraseCtxLO d)
  val2Term (Lam v)      = Lam $ val2Term v
  val2Term  TT          = TT
  val2Term (LetT n v)   = LetT (neu2Term n) (val2Term v)
  val2Term (Pair l r)   = Pair (val2Term l) (val2Term r)
  val2Term (LetP n v)   = LetP (neu2Term n) (val2Term v)
  val2Term (Emb v Refl) = assert_total $ neu2Term v

  export
  neu2Term : Neu g n a d -> Term (eraseCtxLO g) a (eraseCtxLO d)
  neu2Term (Var i)   = Var $ eraseInCtxLO i
  neu2Term (App t u) = App (neu2Term t) (val2Term u)
  neu2Term (Cut v)   = assert_total $ val2Term v

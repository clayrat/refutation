module Lin.TyCheck.TermSp

import Ctx
import ProdLet.Ty
import Split
import Lin.Usage
import Lin.Usage.OPE
import Lin.Usage.Ctx
import Lin.Parser
import Lin.TyCheck.TermLO

%default total

mutual
  public export
  data Val : List Ty -> Val -> Ty -> Type where
    Lam  : Val (a::g) v b -> Val g (Lam s v) (a~>b)
    TT   : Val [] TT U
    LetT : Neu l m U -> Split g l r -> Val r n a -> Val g (LetT m n) a
    Pair : Val l m a -> Split g l r -> Val r n b -> Val g (Pair m n) (Prod a b)
    LetP : Neu l m (Prod a b) -> Split g l r -> Val (b::a::r) n c -> Val g (LetP m x y n) c
    Emb  : Neu g m a -> a = b -> Val g (Emb m) b

  public export
  data Neu : List Ty -> Neu -> Ty -> Type where
    Var : Neu [a] (Var s) a
    App : Neu l m (a~>b) -> Split g l r -> Val r n a -> Neu g (App m n) b
    Cut : Val g m a -> Neu g (Cut m a) a

mutual
  export
  val2Sp : {g : Usages l} -> {a : Ty} -> Val g m a d -> (o : OPE g d) -> Val (Builtin.snd <$> used o) m a
  val2Sp (Lam {s} {a} v) o = Lam $ val2Sp v (Cons (s,a) o)
  val2Sp  TT             o = rewrite usedRefl o in TT
  val2Sp (LetT n v)      o =
    let nc = neuConsumption n
        vc = valConsumption v
     in
    LetT (neu2Sp n nc) (splitMap snd $ usedDivide o nc vc) (val2Sp v vc)
  val2Sp (Pair l r)      o =
    let lc = valConsumption l
        rc = valConsumption r
     in
    Pair (val2Sp l lc) (splitMap snd $ usedDivide o lc rc) (val2Sp r rc)
  val2Sp (LetP n v)      o =
    let nc = neuConsumption n
        vc'@(Cons (y,b) (Cons (x,a) vc)) = valConsumption v
     in
    LetP (neu2Sp n nc) (splitMap snd $ usedDivide o nc vc) (val2Sp v vc')
  val2Sp (Emb v Refl)    o = assert_total $ Emb (neu2Sp v o) Refl

  export
  neu2Sp : {g : Usages l} -> {a : Ty} -> Neu g n a d -> (o : OPE g d) -> Neu (Builtin.snd <$> used o) n a
  neu2Sp (Var  Here)        (Cons (s,a) o) = rewrite usedRefl o in Var
  neu2Sp (Var (There cp i)) (Skip       o) = neu2Sp (Var i) o
  neu2Sp (Var (There cp i)) (Cons (s,b) o) impossible
  neu2Sp (App t u)                      o  =
    let tc = neuConsumption t
        uc = valConsumption u
     in
    App (neu2Sp t tc) (splitMap snd $ usedDivide o tc uc) (val2Sp u uc)
  neu2Sp (Cut v)                        o  = assert_total $ Cut $ val2Sp v o

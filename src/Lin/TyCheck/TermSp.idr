module Lin.TyCheck.TermSp

import Ctx
import ProdLet.Ty
import Split
import Lin.Usage
import Lin.Usage.Ctx
import Lin.Parser
import Lin.TyCheck.TermLO

%default total

mutual
  public export
  data Val : List Ty -> Ty -> Type where
    Lam  : Val (a::g) b -> Val g (a~>b)
    TT   : Val [] U
    LetT : Neu l U -> Split g l r -> Val r a -> Val g a
    Pair : Val l a -> Split g l r -> Val r b -> Val g (Prod a b)
    LetP : Neu l (Prod a b) -> Split g l r -> Val (b::a::r) c -> Val g c
    Emb  : Neu g a -> a = b -> Val g b

  public export
  data Neu : List Ty -> Ty -> Type where
    Var : Neu [a] a
    App : Neu l (a~>b) -> Split g l r -> Val r a -> Neu g b
    Cut : Val g a -> Neu g a

mutual
  export
  val2Sp : {g : Usages l} -> {a : Ty} -> Val g m a d -> (o : OPE g d) -> Val (Builtin.snd <$> used o) a
  val2Sp (Lam {s} {a} v) o = Lam $ val2Sp v (Cons (s,a) o)
  val2Sp  TT             o = rewrite usedRefl o in TT
  val2Sp (LetT n v)      o =
    let
      nc = neuConsumption n
      vc = valConsumption v
     in
    LetT (neu2Sp n nc) (splitMap snd $ usedDivide o nc vc) (val2Sp v vc)
  val2Sp (Pair l r)      o =
    let
      lc = valConsumption l
      rc = valConsumption r
     in
    Pair (val2Sp l lc) (splitMap snd $ usedDivide o lc rc) (val2Sp r rc)
  val2Sp (LetP n v)      o =
    let
      nc = neuConsumption n
      vc'@(Cons (y,b) (Cons (x,a) vc)) = valConsumption v
     in
    LetP (neu2Sp n nc) (splitMap snd $ usedDivide o nc vc) (val2Sp v vc')
  val2Sp (Emb v Refl)    o = assert_total $ Emb (neu2Sp v o) Refl

  export
  neu2Sp : {g : Usages l} -> {a : Ty} -> Neu g n a d -> (o : OPE g d) -> Neu (Builtin.snd <$> used o) a
  neu2Sp (Var  Here)        (Cons (s,a) o) = rewrite usedRefl o in Var
  neu2Sp (Var (There cp i)) (Skip       o) = neu2Sp (Var i) o
  neu2Sp (Var (There cp i)) (Cons (y,b) o) impossible
  neu2Sp (App t u)                      o  =
    let
      tc = neuConsumption t
      uc = valConsumption u
     in
    App (neu2Sp t tc) (splitMap snd $ usedDivide o tc uc) (val2Sp u uc)
  neu2Sp (Cut v)                        o  = assert_total $ Cut $ val2Sp v o
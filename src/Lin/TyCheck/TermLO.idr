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
    LetT : Neu g l U d -> Val d r a s -> Val g (LetT l r) a s
    Pair : Val g l a d -> Val d r b s -> Val g (Pair l r) (Prod a b) s
    LetP : Neu g l (Prod a b) d -> Val (Fr (y,b)::Fr (x,a)::d) r c (St (y,b)::St (x,a)::s) -> Val g (LetP l x y m) c s
    Emb  : Neu g m a d -> a = b -> Val g (Emb m) b d

  public export
  data Neu : {ctx : Ctx Ty} -> Usages ctx -> Neu -> Ty -> Usages ctx -> Type where
    Var : InCtxLO g s a d -> Neu g (Var s) a d
    App : {a : Ty} -> {d : Usages ctx} ->
          Neu g l (a~>b) d -> Val d m a s -> Neu g (App l m) b s
    Cut : Val g m a d -> Neu g (Cut m a) a d

export
neuUniq : Neu g n a d1 -> Neu g n b d2 -> a = b
neuUniq (Var i1)   (Var i2)   = inCtxLOUniq i1 i2
neuUniq (App t1 _) (App t2 _) = snd $ impInj $ neuUniq t1 t2
neuUniq (Cut v1)   (Cut v2)   = Refl
{-
mutual
  val2Term : Val {ctx} g v a d -> Term (eraseCtx ctx) a

  neu2Term : Neu {ctx} g v a d -> Term (eraseCtx ctx) a
  neu2Term (Var Here)   = ?wat --Var $ eraseInCtx i
  neu2Term (Var (There nx i)) = ?wat1 --Var $ eraseInCtx i
  neu2Term (App {s} t u) = App (neu2Term t) ?wat2 (val2Term u)
  neu2Term (Cut v)   = ?wat3 --val2Term v
  -}
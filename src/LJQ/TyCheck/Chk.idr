module LJQ.TyCheck.Chk

import Decidable.Equality
import Data.List
import Data.String.Parser

import Ctx
import LJQ.Ty
import LJQ.Parser
--import LJQ.Term
import LJQ.TyCheck.Term
--import LJQ.TyCheck.NotTerm

%default total

mutual
  synth : (g : Ctx Ty) -> (n : Neu) -> Dec (a ** Neu g n a)
  synth g (V nv)          = case synthV g nv of
    Yes (a**t) => Yes (a**V t)
    No ctra    => No $ \(a**V t) => ctra (a**t)
  synth g (GApp x s v n) = case lookup g s of
    Yes (A**el)       => No $ \(a**GApp el1 t u) => uninhabited $ inCtxUniq el el1
    Yes (Imp a b**el) => case inherit g v a of
      Yes t   => case synth ((x,b)::g) n of
        Yes (c**u) => Yes (c ** GApp el t u)
        No ctra    => No ?wat0
      No ctra => No ?wat1
    No ctra           => No ?wat2
  synth g (Let x nv n)   = case synthV g nv of
    Yes (a**t) => case synth ((x,a)::g) n of
      Yes (b**u) => Yes (b**Let t u)
      No ctra    => No ?wat3
    No ctra    => No ?wat4

  synthV : (g : Ctx Ty) -> (n : NeuV) -> Dec (a ** NeuV g n a)
  synthV g (Var s)   = case lookup g s of
    Yes (a**el) => Yes (a**Var el)
    No ctra => No ?wat5
  synthV g (Cut v t) = case inherit g v t of
    Yes u   => Yes (t**Cut u)
    No ctra => No ?wat6

  inherit : (g : Ctx Ty) -> (m : Val) -> (a : Ty) -> Dec (Val g m a)
  inherit _ (Lam _ _)  A        = No ?wat7
  inherit g (Lam s n) (Imp a b) = case synth ((s,a)::g) n of
    Yes (c**t) => case decEq b c of
      Yes Refl => Yes $ Lam t
      No ctra  => No ?wat9
    No ctra    => No ?wat10
  inherit g (Emb nv)   a        = case synthV g nv of
    Yes (b**m) => case decEq a b of
      Yes prf => Yes $ Emb m (sym prf)
      No ctra => No ?wat11
    No ctra    => No ?wat12

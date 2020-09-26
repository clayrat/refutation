module ProdSum.TyCheck.Chk0

import Decidable.Equality
import Data.List
import Ctx
import ProdSum.Ty
import ProdSum.Parser
import ProdSum.Term
import ProdSum.TyCheck.Term

%default total

mutual
  synth : (g : Ctx Ty) -> (n : Neu) -> Dec (a ** Neu g n a)
  synth g (Var s)   = case lookup g s of
    Yes (a**el) => Yes (a ** Var el)
    No ctra => No $ \(a**Var el) => ctra (a ** el)
  synth g (App t u) = case synth g t of
    Yes (A**n) => No $ \(_**App v _) => uninhabited $ neuUniq v n
    Yes ((Imp a b)**n) => case inherit g u a of
      Yes m => Yes (b ** App n m)
      No ctra => No $ notArg n ctra
    Yes ((Prod a b)**n) => No $ \(_**App v _) => uninhabited $ neuUniq v n
    Yes ((Sum a b)**n) => No $ \(_**App v _) => uninhabited $ neuUniq v n
    No ctra => No $ \(b**App {a} v _) => assert_total $ ctra ((a~>b) ** v)
  synth g (Fst t) = case synth g t of
    Yes (A**n) => No $ \(_**Fst nn) => uninhabited $ neuUniq n nn
    Yes ((Imp a b)**n) => No $ \(_**Fst nn) => uninhabited $ neuUniq n nn
    Yes ((Prod a b)**n) => Yes (a**Fst n)
    Yes ((Sum a b)**n) => No $ \(_**Fst nn) => uninhabited $ neuUniq n nn
    No ctra => No $ \(a**Fst {b} n) => ctra (Prod a b ** n)
  synth g (Snd t) = case synth g t of
    Yes (A**n) => No $ \(_**Snd nn) => uninhabited $ neuUniq n nn
    Yes ((Imp a b)**n) => No $ \(_**Snd nn) => uninhabited $ neuUniq n nn
    Yes ((Prod a b)**n) => Yes (b**Snd n)
    Yes ((Sum a b)**n) => No $ \(_**Snd nn) => uninhabited $ neuUniq n nn
    No ctra => No $ \(b**Snd {a} n) => ctra (Prod a b ** n)
  synth g (Cut v t) = case inherit g v t of
    Yes val => Yes (t ** Cut val)
    No ctra => No $ \(_**Cut v) => ctra v

  inherit : (g : Ctx Ty) -> (m : Val) -> (a : Ty) -> Dec (Val g m a)
  inherit _ (Lam _ _)         A         = No uninhabited
  inherit _ (Lam _ _)        (Prod _ _) = No uninhabited
  inherit _ (Lam _ _)        (Sum _ _)  = No uninhabited
  inherit g (Lam s v)        (Imp a b)  = case inherit ((s,a)::g) v b of
    Yes w => Yes $ Lam w
    No ctra => No $ \(Lam w) => ctra w
  inherit _ (Pair _ _)        A         = No uninhabited
  inherit g (Pair l r)       (Prod a b) = case inherit g l a of
    Yes x => case inherit g r b of
      Yes y => Yes $ Pair x y
      No ctra => No $ \(Pair _ y) => ctra y
    No ctra => No $ \(Pair x _) => ctra x
  inherit _ (Pair _ _)       (Sum _ _)  = No uninhabited
  inherit _ (Pair _ _)       (Imp _ _)  = No uninhabited
  inherit _ (Inl _)           A         = No uninhabited
  inherit _ (Inl _)          (Prod _ _) = No uninhabited
  inherit g (Inl l)          (Sum a _)  = case inherit g l a of
    Yes x => Yes $ Inl x
    No ctra => No $ \(Inl x) => ctra x
  inherit _ (Inl _)          (Imp _ _)  = No uninhabited
  inherit _ (Inr _)           A         = No uninhabited
  inherit _ (Inr _)          (Prod _ _) = No uninhabited
  inherit g (Inr r)          (Sum _ b)  = case inherit g r b of
    Yes y => Yes $ Inr y
    No ctra => No $ \(Inr y) => ctra y
  inherit _ (Inr _)          (Imp _ _)  = No uninhabited
  inherit g (Case c x l y r)  t         = case synth g c of
    Yes (Imp _ _  ** n) => No $ \(Case n0 _ _) => uninhabited $ neuUniq n n0
    Yes (A        ** n) => No $ \(Case n0 _ _) => uninhabited $ neuUniq n n0
    Yes (Prod _ _ ** n) => No $ \(Case n0 _ _) => uninhabited $ neuUniq n n0
    Yes (Sum a b  ** n) => case inherit ((x,a)::g) l t of
      Yes p => case inherit ((y,b)::g) r t of
        Yes q => Yes $ Case n p q
        No ctra => No $ notRight n ctra
      No ctra => No $ notLeft n ctra
    No ctra => No $ \(Case {a} {b} n _ _) => ctra (Sum a b ** n)
  inherit g (Emb n)           a         = case synth g n of
    Yes (b ** m) => case decEq a b of
      Yes prf => Yes $ Emb m (sym prf)
      No ctra => No $ notSwitch m (\p => ctra $ sym p)
    No ctra => No $ \(Emb m Refl) => ctra (a ** m)

mutual
  val2Term : Val g m a -> Term (eraseCtx g) a
  val2Term (Lam v)      = Lam $ val2Term v
  val2Term (Pair l r)   = Pair (val2Term l) (val2Term r)
  val2Term (Inl l)      = Inl $ val2Term l
  val2Term (Inr r)      = Inr $ val2Term r
  val2Term (Case n l r) = Case (neu2Term n) (val2Term l) (val2Term r)
  val2Term (Emb v Refl) = neu2Term v

  neu2Term : Neu g n a -> Term (eraseCtx g) a
  neu2Term (Var i)   = Var $ eraseInCtx i
  neu2Term (Fst n)   = Fst $ neu2Term n
  neu2Term (Snd n)   = Snd $ neu2Term n
  neu2Term (Cut v)   = val2Term v
  neu2Term (App t u) = App (neu2Term t) (val2Term u)

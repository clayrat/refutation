module Lin.TyCheck.Chk

import Data.List.Quantifiers
import Decidable.Equality
import Ctx
import ProdLet.Ty
import Lin.Parser
import Lin.TyCheck.Usage
import Lin.TyCheck.TermLO

%default total

mutual
  synth : (g : Usages ctx) -> (t : Neu) -> Dec (d ** a ** Neu g t a d)
  synth g (Var s)   =  case lookupLO g s of
    Yes (d**a**el) => Yes (d**a**Var el)
    No ctra => No $ \(d**a**Var el) => ctra (d**a**el)
  synth g (App t u) = case synth g t of
    Yes (_**U**n)        => No $ \(_**_**App n0 _) => uninhabited $ fst $ neuUniq n n0
    Yes (_**Prod _ _**n) => No $ \(_**_**App n0 _) => uninhabited $ fst $ neuUniq n n0
    Yes (d**Imp a b**n)  => case inherit d u a of
      Yes (s ** v) => Yes (s ** b ** App n v)
      No ctra => No $ \(s**b**App n0 v) => let (prft, prfc) = neuUniq n n0 in
                                           case (fst $ impInj prft, prfc) of
                                             (Refl, Refl) => ctra (s ** v)
    No ctra => No $ \(_**b**App {a} {d} n _) => ctra (d ** Imp a b ** n)
  synth g (Cut m a) = case inherit g m a of
    Yes (d**v) => Yes (d ** a ** Cut v)
    No ctra => No $ \(d**_**Cut v) => ctra (d**v)

  inherit : (g : Usages ctx) -> (t : Val) -> (a : Ty) -> Dec (d ** Val g t a d)
  inherit _ (Lam _ _)         U         = No $ \(_ ** v) => uninhabited v
  inherit _ (Lam _ _)        (Prod _ _) = No $ \(_ ** v) => uninhabited v
  inherit g (Lam s v)        (Imp a b)  = case inherit (Fr (s,a)::g) v b of
    Yes (Fr (s,a)::d**v) => No $ \(dd**Lam vv) => uninhabited $ fst $ allConsInjective $ valUniq v vv
    Yes (St (s,a)::d**v) => Yes (d ** Lam v)
    No ctra => No $ \(d**Lam v) => ctra (St (s,a)::d ** v)
  inherit g  TT               U         = Yes (g ** TT)
  inherit _  TT              (Imp _ _)  = No $ \(_ ** v) => uninhabited v
  inherit _  TT              (Prod _ _) = No $ \(_ ** v) => uninhabited v
  inherit g (LetT n m)        c         = case synth g n of
    Yes (d**U**n0)        => case inherit d m c of
      Yes (s ** v) => Yes (s ** LetT n0 v)
      No ctra => No $ \(s ** LetT nn vv) => case snd $ neuUniq n0 nn of
                                              Refl => ctra (s ** vv)
    Yes (_**Imp _ _**n0)  => No $ \(_ ** LetT nn _) => uninhabited $ fst $ neuUniq n0 nn
    Yes (_**Prod _ _**n0) => No $ \(_ ** LetT nn _) => uninhabited $ fst $ neuUniq n0 nn
    No ctra => No $ \(_ ** LetT {d} nn _) => ctra (d ** U ** nn)
  inherit _ (Pair _ _)        U         = No $ \(_ ** v) => uninhabited v
  inherit _ (Pair _ _)       (Imp _ _)  = No $ \(_ ** v) => uninhabited v
  inherit g (Pair l r)       (Prod a b) = case inherit g l a of
    Yes (d**l0) => case inherit d r b of
      Yes (s**r0) => Yes (s ** Pair l0 r0)
      No ctra => No \(_**Pair {s} l1 r1) => case valUniq l0 l1 of
                                              Refl => ctra (s ** r1)
    No ctra => No $ \(_**Pair {d} l0 _) => ctra (d ** l0)
  inherit g (LetP n x y m)    c         = case synth g n of
    Yes (_**U**n0)        => No $ \(_ ** LetP nn _) => uninhabited $ fst $ neuUniq n0 nn
    Yes (_**Imp _ _**n0)  => No $ \(_ ** LetP nn _) => uninhabited $ fst $ neuUniq n0 nn
    Yes (d**Prod a b**n0) => case inherit (Fr (y,b)::Fr (x,a)::d) m c of
      Yes (Fr (y,b)::       u::s ** v0) => No $ \(_ ** LetP nn vv) =>
                                             let (prft, prfc) = neuUniq n0 nn in
                                              case (prodInj prft, prfc) of
                                                ((Refl, Refl), Refl) => uninhabited $ fst $ allConsInjective $ valUniq v0 vv
      Yes (St (y,b)::Fr (x,a)::s ** v0) => No $ \(_ ** LetP nn vv) =>
                                             let (prft, prfc) = neuUniq n0 nn in
                                             case (prodInj prft, prfc) of
                                               ((Refl, Refl), Refl) => uninhabited $ fst $ allConsInjective $ snd $ allConsInjective $ valUniq v0 vv
      Yes (St (y,b)::St (x,a)::s ** v0) => Yes (s ** LetP n0 v0)
      No ctra => No $ \(s ** LetP nn vv) =>
                    let (prft, prfc) = neuUniq n0 nn in
                    case (prodInj prft, prfc) of
                      ((Refl, Refl), Refl) => ctra (St (y,b)::St (x,a)::s ** vv)
    No ctra => No $ \(dd ** LetP {d} {a} {b} nn vv) => ctra (d ** Prod a b ** nn)
  inherit g (Emb n)           a         = case synth g n of
    Yes (d** b ** m) => case decEq a b of
      Yes prf => Yes (d ** Emb m (sym prf))
      No ctra => No $ \(_ ** Emb m0 Refl) => ctra $ fst $ neuUniq m0 m
    No ctra => No $ \(d ** Emb m Refl) => ctra (d ** a ** m)

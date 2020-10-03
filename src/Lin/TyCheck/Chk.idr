module Lin.TyCheck.Chk

import Data.List.Quantifiers
import Ctx
import ProdLet.Ty
import Lin.Parser
import Lin.TyCheck.Usage
import Lin.TyCheck.TermLO

%default total

mutual
  synth : (g : Usages ctx) -> (t : Neu) -> Dec (d : Usages ctx ** a : Ty ** Neu g t a d)
  synth g (Var s)   =  case lookupLO g s of
    Yes (d**a**el) => Yes (d**a**Var el)
    No ctra => No $ \(d**a**Var el) => ctra (d**a**el)
  synth g (App t u) = case synth g t of
    Yes (d**U**n)        => No $ \(_**_**App n0 _) => uninhabited $ neuUniq n n0
    Yes (d**Prod _ _**n) => No $ \(_**_**App n0 _) => uninhabited $ neuUniq n n0
    Yes (d**Imp a b**n)  => ?wat
    No ctra => No $ \(_**b**App {a} {d} n _) => ctra (d ** Imp a b ** n)
  synth g (Cut v t) = ?wat3

  check : (g : Usages ctx) -> (t : Val) -> (a : Ty) -> Dec (d : Usages ctx ** Val g t a d)
  check g t a = ?wot
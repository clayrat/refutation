module Lin.TyCheck.Usage

import Data.List.Quantifiers
import Decidable.Equality
--import Split
import Ctx
import ProdLet.Ty
import Lin.Parser

%default total

public export
data Usage : t -> Type where
  Fr : (x : t) -> Usage x
  St : (x : t) -> Usage x

public export
Usages : List t -> Type
Usages = All Usage

public export
data InCtxLO : {ctx : Ctx Ty} -> Usages ctx -> String -> Ty -> Usages ctx -> Type where
  Here : InCtxLO (Fr (x,a)::g) x a (St (x,a)::d)
  There : Not (x=y) -> InCtxLO {ctx} g x a d -> InCtxLO {ctx=(y,b)::ctx} (u::g) x a (u::d)

Uninhabited (InCtxLO [] x a d) where
  uninhabited Here impossible
  uninhabited (There _ _) impossible

Uninhabited (InCtxLO (St (x,a)::g) x b d) where
  uninhabited Here impossible
  uninhabited (There n el) = n Refl

Uninhabited (InCtxLO (St (y,b)::g) x a (Fr (y,b)::d)) where
  uninhabited Here impossible
  uninhabited (There _ _) impossible

nowhereLOF : Not (x=y) -> Not (d ** a ** InCtxLO g x a d) -> Not (d ** a ** InCtxLO (Fr (y,b)::g) x a d)
nowhereLOF neq ctra ((St (y,b)::d)**b**Here)      = neq Refl
nowhereLOF neq ctra ((Fr (y,b)::d)**a**There n i) = ctra (d**a**i)

nowhereLOS : Not (x=y) -> Not (d ** a ** InCtxLO g x a d) -> Not (d ** a ** InCtxLO (St (y,b)::g) x a d)
nowhereLOS neq ctra ((Fr (y,b)::d)**a**el)        = uninhabited el
nowhereLOS neq ctra ((St (y,b)::d)**a**There n i) = ctra (d**a**i)

export
lookupLO : (g : Usages ctx) -> (x : String) -> Dec (d ** a ** InCtxLO g x a d)
lookupLO []            x = No $ \(_**_**e) => uninhabited e
lookupLO (Fr (y,b)::g) x with (decEq x y)
  lookupLO (Fr (y,b)::g) y | Yes Refl = Yes (St (y,b)::g**b**Here)
  lookupLO (Fr (y,b)::g) x | No ctra with (lookupLO g x)
    lookupLO (Fr (y,b)::g) x | No ctra | Yes (d**a**el) = Yes (Fr (y,b)::d ** a ** There ctra el)
    lookupLO (Fr (y,b)::g) x | No ctra | No ctra2 = No $ nowhereLOF ctra ctra2
lookupLO (St (y,b)::g) x with (decEq x y)
  lookupLO (St (y,b)::g) y | Yes Refl = No $ \(d**a**e) => uninhabited e
  lookupLO (St (y,b)::g) x | No ctra with (lookupLO g x)
    lookupLO (St (y,b)::g) x | No ctra | Yes (d**a**el) = Yes (St (y,b)::d ** a ** There ctra el)
    lookupLO (St (y,b)::g) x | No ctra | No ctra2 = No $ nowhereLOS ctra ctra2

export
inCtxLOUniq : InCtxLO g s a d1 -> InCtxLO g s b d2 -> a = b
inCtxLOUniq  Here           Here          = Refl
inCtxLOUniq  Here          (There neq2 _) = absurd $ neq2 Refl
inCtxLOUniq (There neq1 _)  Here          = absurd $ neq1 Refl
inCtxLOUniq (There _ i1)   (There _ i2)   = inCtxLOUniq i1 i2


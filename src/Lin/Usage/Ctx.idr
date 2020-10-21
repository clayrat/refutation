module Lin.Usage.Ctx

import Decidable.Equality
import Quantifiers
import public Lin.Usage
import Ctx
import Lin.Usage.OPE

%default total

public export
data InCtxLO : {0 ctx : Ctx t} -> Usages ctx -> String -> t -> Usages ctx -> Type where
  Here  :                                       InCtxLO                  (Fr (x,a)::g) x a (St (x,a)::g)
  There : Not (x=y) -> InCtxLO {ctx} g x a d -> InCtxLO {ctx=(y,b)::ctx} (u       ::g) x a (u       ::d)

Uninhabited (InCtxLO [] x a d) where
  uninhabited Here impossible
  uninhabited (There _ _) impossible

Uninhabited (InCtxLO (St (x,a)::g) x b d) where
  uninhabited Here impossible
  uninhabited (There n _) = n Refl

Uninhabited (InCtxLO (St (y,b)::g) x a (Fr (y,b)::d)) where
  uninhabited Here impossible
  uninhabited (There _ _) impossible

export
inCtxLOConsumption : {s : String} -> {a : t} -> {g : Usages l} -> InCtxLO g s a d -> OPE g d
inCtxLOConsumption {g=Fr (s,a)::g}  Here       = Cons (s,a) $ opeRefl g
inCtxLOConsumption                 (There _ i) = Skip $ inCtxLOConsumption i

public export
data NotInCtxLO : {0 ctx : Ctx t} -> Usages ctx -> String -> Type where
  NNil  : {x : String} -> NotInCtxLO [] x
  NUsed : {x : String} -> NotInCtxLO (St (x,a)::g) x
  NCons : Not (x=y) -> NotInCtxLO {ctx} g x -> NotInCtxLO {ctx=(y,a)::ctx} (u::g) x

export
Show (NotInCtxLO g x) where
  show (NNil {x})  = "Variable " ++ x ++ " not found"
  show (NUsed {x}) = "Variable " ++ x ++ " is already used"
  show (NCons _ n) = show n

export
notInCtxLO : NotInCtxLO g x -> InCtxLO g x a d -> Void
notInCtxLO  NNil          ic          = uninhabited ic
notInCtxLO  NUsed         ic          = uninhabited ic
notInCtxLO (NCons nn _)   Here        = nn Refl
notInCtxLO (NCons _ nic) (There _ ic) = notInCtxLO nic ic

nowhereLOF : {0 ctx : Ctx t} -> {0 g : Usages ctx} ->
             Not (x=y) -> Not (d ** a ** InCtxLO g x a d) -> Not (d ** a ** InCtxLO (Fr (y,b)::g) x a d)
nowhereLOF neq ctra ((St (y,b)::d)**b**Here)      = neq Refl
nowhereLOF neq ctra ((Fr (y,b)::d)**a**There n i) = ctra (d**a**i)

nowhereLOS : {0 ctx : Ctx t} -> {0 g : Usages ctx} ->
             Not (x=y) -> Not (d ** a ** InCtxLO g x a d) -> Not (d ** a ** InCtxLO (St (y,b)::g) x a d)
nowhereLOS neq ctra ((Fr (y,b)::d)**a**el)        = uninhabited el
nowhereLOS neq ctra ((St (y,b)::d)**a**There n i) = ctra (d**a**i)

export
lookupLO : {0 ctx : Ctx t} -> (g : Usages ctx) -> (x : String) -> Dec (d ** a ** InCtxLO g x a d)
lookupLO []            x = No $ \(_**_**e) => uninhabited e
lookupLO (Fr (y,b)::g) x with (decEq x y)
  lookupLO (Fr (y,b)::g) y | Yes Refl = Yes (St (y,b)::g**b**Here)
  lookupLO (Fr (y,b)::g) x | No ctra with (lookupLO g x)
    lookupLO (Fr (y,b)::g) x | No ctra | Yes (d**a**el) = Yes (Fr (y,b)::d**a**There ctra el)
    lookupLO (Fr (y,b)::g) x | No ctra | No ctra2 = No $ nowhereLOF ctra ctra2
lookupLO (St (y,b)::g) x with (decEq x y)
  lookupLO (St (y,b)::g) y | Yes Refl = No $ \(d**a**e) => uninhabited e
  lookupLO (St (y,b)::g) x | No ctra with (lookupLO g x)
    lookupLO (St (y,b)::g) x | No ctra | Yes (d**a**el) = Yes (St (y,b)::d ** a ** There ctra el)
    lookupLO (St (y,b)::g) x | No ctra | No ctra2 = No $ nowhereLOS ctra ctra2

export
lookupLOE : {0 ctx : Ctx t} -> (g : Usages ctx) -> (x : String) -> Either (NotInCtxLO g x) (d ** a ** InCtxLO g x a d)
lookupLOE []         x = Left NNil
lookupLOE (Fr (y,b)::g) x with (decEq x y)
  lookupLOE (Fr (y,b)::g) y | Yes Refl = Right (St (y,b)::g**b**Here)
  lookupLOE (Fr (y,b)::g) x | No ctra with (lookupLOE g x)
    lookupLOE (Fr (y,b)::g) x | No ctra | Right (d**a**el) = Right (Fr (y,b)::d**a**There ctra el)
    lookupLOE (Fr (y,b)::g) x | No ctra | Left ctra2 = Left $ NCons ctra ctra2
lookupLOE (St (y,b)::g) x with (decEq x y)
  lookupLOE (St (y,b)::g) y | Yes Refl = Left NUsed
  lookupLOE (St (y,b)::g) x | No ctra with (lookupLOE g x)
    lookupLOE (St (y,b)::g) x | No ctra | Right (d**a**el) = Right (St (y,b)::d**a**There ctra el)
    lookupLOE (St (y,b)::g) x | No ctra | Left ctra2 = Left $ NCons ctra ctra2

export
inCtxLOUniq : InCtxLO g s a d1 -> InCtxLO g s b d2 -> (a = b, d1 = d2)
inCtxLOUniq  Here             Here          = (Refl, Refl)
inCtxLOUniq  Here            (There neq2 _) = absurd $ neq2 Refl
inCtxLOUniq (There neq1 _)    Here          = absurd $ neq1 Refl
inCtxLOUniq (There {u} _ i1) (There _ i2)   = let (prft, prfc) = inCtxLOUniq i1 i2 in
                                              (prft, cong (u::) prfc)

public export
sndU : {0 c : (String, t)} -> Usage c -> Usage (snd c)
sndU (Fr (_,a)) = Fr a
sndU (St (_,a)) = St a

public export
eraseCtxLO : {0 ctx : Ctx t} -> Usages ctx -> Usages (eraseCtx ctx)
eraseCtxLO = mapTransport (sndU {t})

public export
eraseInCtxLO : {0 ctx : Ctx t} -> {0 g, d : Usages ctx} -> InCtxLO g s a d -> ElemU (eraseCtxLO g) a (eraseCtxLO d)
eraseInCtxLO  Here       = HereU
eraseInCtxLO (There _ i) = ThereU $ eraseInCtxLO i
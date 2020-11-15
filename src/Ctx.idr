
module Ctx

import Data.List
import Data.List.Elem
import Decidable.Equality

%default total

-- contexts with names

public export
Ctx : Type -> Type
Ctx t = List (String, t)

public export
eraseCtx : Ctx t -> List t
eraseCtx = map snd

public export
data InCtx : Ctx t -> String -> t -> Type where
  Here : InCtx ((x,a)::g) x a
  There : Not (x=y) -> InCtx g x a -> InCtx ((y,b)::g) x a

export
eraseInCtx : InCtx c s a -> Elem a (eraseCtx c)
eraseInCtx  Here       = Here
eraseInCtx (There _ i) = There $ eraseInCtx i

export
Uninhabited (InCtx [] x a) where
  uninhabited Here impossible
  uninhabited (There _ _) impossible

public export
data NotInCtx : Ctx t -> String -> Type where
  NNil : NotInCtx [] s
  NCons : Not (x=y) -> NotInCtx g x -> NotInCtx ((y,a)::g) x

export
notInCtx : NotInCtx g x -> InCtx g x a -> Void
notInCtx  NNil          ic          = uninhabited ic
notInCtx (NCons nn _)   Here        = nn Refl
notInCtx (NCons _ nic) (There _ ic) = notInCtx nic ic

nowhere : Not (x=y) -> Not (a ** InCtx g x a) -> Not (a ** InCtx ((y,b)::g) x a)
nowhere neq ctra (b**Here)      = neq Refl
nowhere neq ctra (a**There n i) = ctra (a**i)

export
inCtxUniq : InCtx g s a -> InCtx g s b -> a = b
inCtxUniq  Here           Here          = Refl
inCtxUniq  Here          (There neq2 _) = absurd $ neq2 Refl
inCtxUniq (There neq1 _)  Here          = absurd $ neq1 Refl
inCtxUniq (There _ i1)   (There _ i2)   = inCtxUniq i1 i2

export
lookup : (g : Ctx t) -> (x : String) -> Dec (a ** InCtx g x a)
lookup []           x = No (\(_**e) => uninhabited e)
lookup ((y,b)::g) x with (decEq x y)
  lookup ((y,b)::g) y | Yes Refl = Yes (b**Here)
  lookup ((y,b)::g) x | No ctra with (lookup g x)
    lookup ((y,b)::g) x | No ctra | Yes (a**el) = Yes (a**There ctra el)
    lookup ((y,b)::g) x | No ctra | No ctra2 = No $ nowhere ctra ctra2

export
lookupE : (g : Ctx t) -> (x : String) -> Either (NotInCtx g x) (a ** InCtx g x a)
lookupE []           x = Left NNil
lookupE ((y,b)::g) x with (decEq x y)
  lookupE ((y,b)::g) y | Yes Refl = Right (b**Here)
  lookupE ((y,b)::g) x | No ctra with (lookupE g x)
    lookupE ((y,b)::g) x | No ctra | Right (a**el) = Right (a**There ctra el)
    lookupE ((y,b)::g) x | No ctra | Left ctra2 = Left $ NCons ctra ctra2

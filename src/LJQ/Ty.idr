module LJQ.Ty

import Decidable.Equality

%default total

public export
data Ty = A | Imp Ty Ty

infixr 5 ~>
public export
(~>) : Ty -> Ty -> Ty
(~>) = Imp

public export
NotBi : Ty -> (Ty -> Ty -> Ty) -> Type
NotBi t bt = {0 x, y : Ty} -> Not (t = bt x y)

export
Uninhabited (A = Imp _ _) where
  uninhabited Refl impossible

export
Uninhabited (Imp _ _ = A) where
  uninhabited Refl impossible

export
impInj : Imp a b = Imp c d -> (a=c, b=d)
impInj Refl = (Refl, Refl)

export
DecEq Ty where
  decEq  A          A         = Yes Refl
  decEq  A         (Imp _ _)  = No uninhabited
  decEq (Imp _ _)   A         = No uninhabited
  decEq (Imp a b)  (Imp c d) with (decEq a c, decEq b d)
    decEq (Imp a b) (Imp c d) | (No ctra, _)         = No $ ctra . fst . impInj
    decEq (Imp a b) (Imp c d) | (_, No ctra2)        = No $ ctra2 . snd . impInj
    decEq (Imp a b) (Imp a b) | (Yes Refl, Yes Refl) = Yes Refl

module ProdSum.Ty

import Decidable.Equality

%default total

public export
data Ty = A | Imp Ty Ty | Prod Ty Ty | Sum Ty Ty

infixr 5 ~>
public export
(~>) : Ty -> Ty -> Ty
(~>) = Imp

export
Uninhabited (A = Imp _ _) where
  uninhabited Refl impossible

export
Uninhabited (A = Prod _ _) where
  uninhabited Refl impossible

export
Uninhabited (A = Sum _ _) where
  uninhabited Refl impossible

export
Uninhabited (Imp _ _ = A) where
  uninhabited Refl impossible

export
Uninhabited (Imp _ _ = Prod _ _) where
  uninhabited Refl impossible

export
Uninhabited (Imp _ _ = Sum _ _) where
  uninhabited Refl impossible

export
Uninhabited (Prod _ _ = A) where
  uninhabited Refl impossible

export
Uninhabited (Prod _ _ = Imp _ _) where
  uninhabited Refl impossible

export
Uninhabited (Prod _ _ = Sum _ _) where
  uninhabited Refl impossible

export
Uninhabited (Sum _ _ = A) where
  uninhabited Refl impossible

export
Uninhabited (Sum _ _ = Imp _ _) where
  uninhabited Refl impossible

export
Uninhabited (Sum _ _ = Prod _ _) where
  uninhabited Refl impossible

export
impInj : Imp a b = Imp c d -> (a=c, b=d)
impInj Refl = (Refl, Refl)

export
prodInj : Prod a b = Prod c d -> (a=c, b=d)
prodInj Refl = (Refl, Refl)

export
sumInj : Sum a b = Sum c d -> (a=c, b=d)
sumInj Refl = (Refl, Refl)

export
DecEq Ty where
  decEq  A          A         = Yes Refl
  decEq  A         (Imp _ _)  = No uninhabited
  decEq  A         (Prod _ _) = No uninhabited
  decEq  A         (Sum _ _)  = No uninhabited
  decEq (Imp _ _)   A         = No uninhabited
  decEq (Imp _ _)  (Prod _ _) = No uninhabited
  decEq (Imp _ _)  (Sum _ _)  = No uninhabited
  decEq (Imp a b)  (Imp c d) with (decEq a c, decEq b d)
    decEq (Imp a b) (Imp c d) | (No ctra, _)         = No $ ctra . fst . impInj
    decEq (Imp a b) (Imp c d) | (_, No ctra2)        = No $ ctra2 . snd . impInj
    decEq (Imp a b) (Imp a b) | (Yes Refl, Yes Refl) = Yes Refl
  decEq (Prod _ _)  A         = No uninhabited
  decEq (Prod _ _) (Imp _ _)  = No uninhabited
  decEq (Prod _ _) (Sum _ _)  = No uninhabited
  decEq (Prod a b) (Prod c d) with (decEq a c, decEq b d)
    decEq (Prod a b) (Prod c d) | (No ctra, _)         = No $ ctra . fst . prodInj
    decEq (Prod a b) (Prod c d) | (_, No ctra2)        = No $ ctra2 . snd . prodInj
    decEq (Prod a b) (Prod a b) | (Yes Refl, Yes Refl) = Yes Refl
  decEq (Sum _ _)   A         = No uninhabited
  decEq (Sum _ _)  (Imp _ _)  = No uninhabited
  decEq (Sum _ _)  (Prod _ _) = No uninhabited
  decEq (Sum a b)  (Sum c d) with (decEq a c, decEq b d)
    decEq (Sum a b) (Sum c d) | (No ctra, _)         = No $ ctra . fst . sumInj
    decEq (Sum a b) (Sum c d) | (_, No ctra2)        = No $ ctra2 . snd . sumInj
    decEq (Sum a b) (Sum a b) | (Yes Refl, Yes Refl) = Yes Refl
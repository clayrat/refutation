module ProdLet.Ty

import Decidable.Equality

%default total

public export
data Ty = U | Imp Ty Ty | Prod Ty Ty

infixr 5 ~>
public export
(~>) : Ty -> Ty -> Ty
(~>) = Imp

public export
NotBi : Ty -> (Ty -> Ty -> Ty) -> Type
NotBi t bt = {0 x, y : Ty} -> Not (t = bt x y)

export
Show Ty where
  show  U         = "1"
  show (Imp a b)  = "(" ++ show a ++ "->" ++ show b ++ ")"
  show (Prod a b) = "(" ++ show a ++ "*" ++ show b ++ ")"

export
Uninhabited (U = Imp _ _) where
  uninhabited Refl impossible

export
Uninhabited (U = Prod _ _) where
  uninhabited Refl impossible

export
Uninhabited (Imp _ _ = U) where
  uninhabited Refl impossible

export
Uninhabited (Imp _ _ = Prod _ _) where
  uninhabited Refl impossible

export
Uninhabited (Prod _ _ = U) where
  uninhabited Refl impossible

export
Uninhabited (Prod _ _ = Imp _ _) where
  uninhabited Refl impossible

export
impInj : Imp a b = Imp c d -> (a=c, b=d)
impInj Refl = (Refl, Refl)

export
prodInj : Prod a b = Prod c d -> (a=c, b=d)
prodInj Refl = (Refl, Refl)

export
DecEq Ty where
  decEq  U          U         = Yes Refl
  decEq  U         (Imp _ _)  = No uninhabited
  decEq  U         (Prod _ _) = No uninhabited
  decEq (Imp _ _)   U         = No uninhabited
  decEq (Imp _ _)  (Prod _ _) = No uninhabited
  decEq (Imp a b)  (Imp c d) with (decEq a c, decEq b d)
    decEq (Imp a b) (Imp c d) | (No ctra, _)         = No $ ctra . fst . impInj
    decEq (Imp a b) (Imp c d) | (_, No ctra2)        = No $ ctra2 . snd . impInj
    decEq (Imp a b) (Imp a b) | (Yes Refl, Yes Refl) = Yes Refl
  decEq (Prod _ _)  U         = No uninhabited
  decEq (Prod _ _) (Imp _ _)  = No uninhabited
  decEq (Prod a b) (Prod c d) with (decEq a c, decEq b d)
    decEq (Prod a b) (Prod c d) | (No ctra, _)         = No $ ctra . fst . prodInj
    decEq (Prod a b) (Prod c d) | (_, No ctra2)        = No $ ctra2 . snd . prodInj
    decEq (Prod a b) (Prod a b) | (Yes Refl, Yes Refl) = Yes Refl

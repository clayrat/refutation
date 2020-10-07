module Lin.Usage

import public Data.List.Quantifiers
import Decidable.Equality
import Quantifiers

%default total

public export
data Usage : t -> Type where
  Fr : (x : t) -> Usage x
  St : (x : t) -> Usage x

export
Uninhabited (Fr x = St x) where
  uninhabited Refl impossible

export
Uninhabited (St x = Fr x) where
  uninhabited Refl impossible

public export
Usages : List t -> Type
Usages = All Usage

public export
data ElemU : {0 l : List t} -> Usages l -> t -> Usages l -> Type where
  HereU  :                ElemU (Fr a::g) a (St a::g)
  ThereU : ElemU g a d -> ElemU (u   ::g) a (u   ::d)

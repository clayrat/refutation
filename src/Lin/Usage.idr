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

public export
data OPE : {0 l : List t} -> Usages l -> Usages l -> Type where
  Nil  : OPE [] []
  Skip : OPE g d -> OPE (a::g) (a::d)
  Cons : {0 g, d : Usages l} -> (x : t) -> OPE g d -> OPE (Fr x::g) (St x::d)

export
opeRefl : (g : Usages l) -> OPE g g
opeRefl []      = Nil
opeRefl (u::us) = Skip $ opeRefl us

export
opeTail : OPE (a::g) (b::d) -> OPE g d
opeTail (Skip o)   = o
opeTail (Cons x o) = o

public export
used : {0 l : List t} -> {0 g, d : Usages l} ->
       OPE g d -> List t
used  Nil       = []
used (Skip o)   = used o
used (Cons x o) = x :: used o

export
usedRefl : (o : OPE g g) -> used o = []
usedRefl  Nil     = Refl
usedRefl (Skip o) = usedRefl o
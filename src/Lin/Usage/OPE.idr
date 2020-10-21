module Lin.Usage.OPE

import public Data.List.Quantifiers
import Decidable.Equality
import Quantifiers
import Lin.Usage
import Split

%default total

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
opeTrans : OPE g d -> OPE d s -> OPE g s
opeTrans  Nil        Nil       = Nil
opeTrans (Skip p)   (Skip q)   = Skip $ opeTrans p q
opeTrans (Cons a p) (Skip q)   = Cons a $ opeTrans p q
opeTrans (Skip p)   (Cons a q) = Cons a $ opeTrans p q

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

export
usedDivide : (pq : OPE g s) -> (p : OPE g d) -> (q : OPE d s) -> Split (used pq) (used p) (used q)
usedDivide  Nil         Nil        Nil       = Nil
usedDivide (Skip pq)   (Skip p)   (Skip q)   = usedDivide pq p q
usedDivide (Cons a pq) (Skip p)   (Cons a q) = ConsR $ usedDivide pq p q
usedDivide (Cons a pq) (Cons a p) (Skip q)   = ConsL $ usedDivide pq p q

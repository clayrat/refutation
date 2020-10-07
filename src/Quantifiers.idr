module Quantifiers

import Data.List.Quantifiers

%default total

public export
mapId : (l : List t) -> map Basics.id l = l
mapId []      = Refl
mapId (l::ls) = cong (l::) (mapId ls)

public export
mapTransport : {0 p : t -> Type} -> {0 q : s -> Type} -> {0 l : List t} -> {0 f : t -> s} ->
    ({0 x : t} -> p x -> q (f x)) ->
    All p l -> All q (map f l)
mapTransport f []      = []
mapTransport f (a::as) = f a :: mapTransport f as

export
mapProperty0 : ({0 x : a} -> p x -> q x) -> All p l -> All q l
mapProperty0 h a = rewrite sym $ mapId l in mapTransport h a

export
allConsInjective : {0 x,y : a} -> {0 px : p x} -> {0 pxs : All p xs} -> {0 py : p y} -> {0 pys : All p ys} ->
                   the (All p (x::xs)) (px::pxs) = the (All p (y::ys)) (py::pys) -> (px=py, pxs=pys)
allConsInjective Refl = (Refl, Refl)
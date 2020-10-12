module Split

import Data.Nat

%default total

public export
data Split : List a -> List a -> List a -> Type where
  Nil   : Split [] [] []
  ConsR : Split xs ls rs -> Split (x::xs)     ls (x::rs)
  ConsL : Split xs ls rs -> Split (x::xs) (x::ls)    rs

-- here we can also use a nat measure instead
export
splitLeft : {l : List a} -> Split l l []
splitLeft {l=[]}   = Nil
splitLeft {l=_::_} = ConsL splitLeft

export
splitComm : Split x l r -> Split x r l
splitComm  Nil      = Nil
splitComm (ConsR s) = ConsL $ splitComm s
splitComm (ConsL s) = ConsR $ splitComm s

export
splitRight : {l : List a} -> Split l [] l
splitRight = splitComm splitLeft

export
splitMap : (0 f : a -> b) -> Split g l r -> Split (map f g) (map f l) (map f r)
splitMap f  Nil      = Nil
splitMap f (ConsR s) = ConsR $ splitMap f s
splitMap f (ConsL s) = ConsL $ splitMap f s

module Lin.TermLO

import Lin.Usage.Ctx
import ProdLet.Ty

%default total

public export
data Term : {l : List Ty} -> Usages l -> Ty -> Usages l -> Type where
  Var  : ElemU g a d -> Term g a d
  Lam  : Term (Fr a::g) b (St a::d) -> Term g (a~>b) d
  App  : Term g (a~>b) d -> Term d a s -> Term g b s
  TT   : Term g U g
  LetT : Term g U d -> Term d a s -> Term g a s
  Pair : Term g a d -> Term d b s -> Term g (Prod a b) s
  LetP : Term g (Prod a b) d -> Term (Fr b::Fr a::d) c (St b::St a::s) -> Term g c s

-- (\x.x) (\x.x)
idid : Term [] (U ~> U) []
idid = App (Lam $ Var HereU) (Lam $ Var HereU)

-- let (a,b) = (*,*) in let * = a in b
project : Term [] U []
project = LetP (Pair TT TT) $
          LetT (Var $ ThereU HereU) $
          Var HereU

-- \x.let (a,b) = x in (b,a)
swap : Term [] (Prod U U ~> Prod U U) []
swap = Lam $ LetP (Var HereU) $
             Pair (Var HereU) (Var $ ThereU HereU)

curry : Term [] ((Prod a b ~> c) ~> (a ~> (b ~> c))) []
curry = Lam $ Lam $ Lam $
        App (Var $ ThereU $ ThereU HereU) $
        Pair (Var $ ThereU HereU) (Var HereU)

uncurry : Term [] ((a ~> (b ~> c)) ~> (Prod a b ~> c)) []
uncurry = Lam $ Lam $ LetP (Var HereU) $
          App (App (Var $ ThereU $ ThereU $ ThereU HereU)
                   (Var $ ThereU HereU))
              (Var HereU)

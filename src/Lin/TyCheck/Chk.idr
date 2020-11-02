module Lin.TyCheck.Chk

import Data.List.Quantifiers
import Data.String.Parser
import Decidable.Equality
import Quantifiers
import Ctx
import ProdLet.Ty
import Lin.TermLO
import Lin.Usage.Ctx
import Lin.Parser
import Lin.TyCheck.TermLO
import Lin.TyCheck.NotTermLO

%default total

mutual
  synth : (g : Usages ctx) -> (t : Neu) -> (d ** Either (NotNeu g t d) (a ** Neu g t a d))
  synth g (Var s)   =  case lookupLOE g s of
    (d**Right (a**el)) => (d**Right (a**Var el))
    (d**Left ctra)     => (d**Left $ NotVar ctra)
  synth g (App t u) = case synth g t of
    (d**Right (U**n))        => (d**Left $ NotAppFT n uninhabited)
    (d**Right (Prod _ _**n)) => (d**Left $ NotAppFT n uninhabited)
    (d**Right (Imp a b**n))  => case inherit d u a of
      (s**Right v)   => (s**Right (b ** App n v))
      (s**Left ctra) => (s**Left $ NotAppA n ctra)
    (d**Left ctra)           => (d**Left $ NotAppF ctra)
  synth g (Cut m a) = case inherit g m a of
    (d**Right v)   => (d**Right (a ** Cut v))
    (d**Left ctra) => (d**Left $ NotCut ctra)

  inherit : (g : Usages ctx) -> (t : Val) -> (a : Ty) -> (d ** Either (NotVal g t a d) (Val g t a d))
  inherit g (Lam _ _)       U         = (g**Left $ NotLamT uninhabited)
  inherit g (Lam _ _)      (Prod _ _) = (g**Left $ NotLamT uninhabited)
  inherit g (Lam x m)      (Imp a b)  = case inherit (Fr (x,a)::g) m b of
    (Fr (x,a)::d**Right v)   => (d**Left $ NotLamFr v)
    (St (x,a)::d**Right v)   => (d**Right $ Lam v)
    (_       ::d**Left ctra) => (d**Left $ NotLam ctra)
  inherit g  TT             U         = (g**Right TT)
  inherit g  TT            (Imp _ _)  = (g**Left $ NotTTT uninhabited)
  inherit g  TT            (Prod _ _) = (g**Left $ NotTTT uninhabited)
  inherit g (LetT n m)      c         = case synth g n of
    (d**Right (U**n0))        => case inherit d m c of
      (s**Right v)   => (s**Right $ LetT n0 v)
      (s**Left ctra) => (s**Left $ NotLetTC n0 ctra)
    (d**Right (Imp _ _ **n0)) => (d**Left $ NotLetTT n0 uninhabited)
    (d**Right (Prod _ _**n0)) => (d**Left $ NotLetTT n0 uninhabited)
    (d**Left ctra)            => (d**Left $ NotLetT ctra)
  inherit g (Pair _ _)      U         = (g**Left $ NotPairT uninhabited)
  inherit g (Pair _ _)     (Imp _ _)  = (g**Left $ NotPairT uninhabited)
  inherit g (Pair l r)     (Prod a b) = case inherit g l a of
    (d**Right l0) => case inherit d r b of
      (s**Right r0) => (s**Right $ Pair l0 r0)
      (s**Left ctra)     => (s**Left $ NotPairR l0 ctra)
    (d**Left ctra)     => (d**Left $ NotPairL ctra)
  inherit g (LetP n x y m)  c         = case synth g n of
    (d**Right (U**n0))        => (d**Left $ NotLetPT n0 uninhabited)
    (d**Right (Imp _ _**n0))  => (d**Left $ NotLetPT n0 uninhabited)
    (d**Right (Prod a b**n0)) => case inherit (Fr (y,b)::Fr (x,a)::d) m c of
      (Fr (y,b)::_       ::s**Right v0)  => (s**Left $ NotLetPFrR n0 v0)
      (St (y,b)::Fr (x,a)::s**Right v0)  => (s**Left $ NotLetPFrL n0 v0)
      (St (y,b)::St (x,a)::s**Right v0)  => (s**Right $ LetP n0 v0)
      (_       ::_       ::s**Left ctra) => (s**Left $ NotLetPC n0 ctra)
    (d**Left ctra) => (d**Left $ NotLetP ctra)
  inherit g (Emb n)         a         = case synth g n of
    (d**Right (b**m)) => case decEq a b of
      Yes prf => (d**Right $ Emb m (sym prf))
      No ctra => (d**Left $ NotEmbQ m (\p => ctra $ sym p))
    (d**Left ctra)       => (d**Left $ NotEmb ctra)

{-
covering
parseCheckTerm : String -> Either String (a ** Term [] a [])
parseCheckTerm s = do (b,_) <- parse (neu <* eos) s
                      case synth [] b of
                        Right ([] ** a ** n) => Right (a ** neu2Term n)
                        Left ctra            => Left $ show ctra
                      -}
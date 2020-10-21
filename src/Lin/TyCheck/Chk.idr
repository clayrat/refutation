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
  synth : (g : Usages ctx) -> (t : Neu) -> Either (NotNeu g t) (d ** a ** Neu g t a d)
  synth g (Var s)   =  case lookupLOE g s of
    Right (d**a**el) => Right (d**a**Var el)
    Left ctra        => Left $ NotVar ctra
  synth g (App t u) = case synth g t of
    Right (_**U**n)        => Left $ NotAppFT n uninhabited
    Right (_**Prod _ _**n) => Left $ NotAppFT n uninhabited
    Right (d**Imp a b**n)  => case inherit d u a of
      Right (s**v) => Right (s ** b ** App n v)
      Left ctra    => Left $ NotAppA n ctra
    Left ctra              => Left $ NotAppF ctra
  synth g (Cut m a) = case inherit g m a of
    Right (d**v) => Right (d ** a ** Cut v)
    Left ctra    => Left $ NotCut ctra

  inherit : (g : Usages ctx) -> (t : Val) -> (a : Ty) -> Either (NotVal g t a) (d ** Val g t a d)
  inherit _ (Lam _ _)       U         = Left $ NotLamT uninhabited
  inherit _ (Lam _ _)      (Prod _ _) = Left $ NotLamT uninhabited
  inherit g (Lam x m)      (Imp a b)  = case inherit (Fr (x,a)::g) m b of
    Right (Fr (x,a)::d**v) => Left $ NotLamFr v
    Right (St (x,a)::d**v) => Right (d ** Lam v)
    Left ctra              => Left $ NotLam ctra
  inherit g  TT             U         = Right (g ** TT)
  inherit _  TT            (Imp _ _)  = Left $ NotTTT uninhabited
  inherit _  TT            (Prod _ _) = Left $ NotTTT uninhabited
  inherit g (LetT n m)      c         = case synth g n of
    Right (d**U**n0)        => case inherit d m c of
      Right (s**v) => Right (s ** LetT n0 v)
      Left ctra    => Left $ NotLetTC n0 ctra
    Right (_**Imp _ _ **n0) => Left $ NotLetTT n0 uninhabited
    Right (_**Prod _ _**n0) => Left $ NotLetTT n0 uninhabited
    Left ctra               => Left $ NotLetT ctra
  inherit _ (Pair _ _)      U         = Left $ NotPairT uninhabited
  inherit _ (Pair _ _)     (Imp _ _)  = Left $ NotPairT uninhabited
  inherit g (Pair l r)     (Prod a b) = case inherit g l a of
    Right (d**l0) => case inherit d r b of
      Right (s**r0) => Right (s ** Pair l0 r0)
      Left ctra     => Left $ NotPairR l0 ctra
    Left ctra     => Left $ NotPairL ctra
  inherit g (LetP n x y m)  c         = case synth g n of
    Right (_**U**n0)        => Left $ NotLetPT n0 uninhabited
    Right (_**Imp _ _**n0)  => Left $ NotLetPT n0 uninhabited
    Right (d**Prod a b**n0) => case inherit (Fr (y,b)::Fr (x,a)::d) m c of
      Right (Fr (y,b)::_       ::s**v0) => Left $ NotLetPFrR n0 v0
      Right (St (y,b)::Fr (x,a)::s**v0) => Left $ NotLetPFrL n0 v0
      Right (St (y,b)::St (x,a)::s**v0) => Right (s ** LetP n0 v0)
      Left ctra                         => Left $ NotLetPC n0 ctra
    Left ctra => Left $ NotLetP ctra
  inherit g (Emb n)         a         = case synth g n of
    Right (d**b**m) => case decEq a b of
      Yes prf => Right (d ** Emb m (sym prf))
      No ctra => Left $ NotEmbQ m (\p => ctra $ sym p)
    Left ctra       => Left $ NotEmb ctra

covering
parseCheckTerm : String -> Either String (a ** Term [] a [])
parseCheckTerm s = do (b,_) <- parse (neu <* eos) s
                      case synth [] b of
                        Right ([] ** a ** n) => Right (a ** neu2Term n)
                        Left ctra            => Left $ show ctra

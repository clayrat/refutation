module LJQ.TyCheck.Chk

import Decidable.Equality
import Data.List
import Data.String.Parser

import Ctx
import LJQ.Ty
import LJQ.Parser
--import LJQ.Term
import LJQ.TyCheck.Term
import LJQ.TyCheck.NotTerm

%default total

mutual
  synth : (g : Ctx Ty) -> (n : Neu) -> Either (NotNeu g n) (a ** Neu g n a)
  synth g (V nv)          = case synthV g nv of
    Right (a**t) => Right (a**V t)
    Left ctra    => Left $ NotV ctra
  synth g (GApp x s v n) = case lookupE g s of
    Right (A**el)       => Left $ NotGAppT el uninhabited
    Right (Imp a b**el) => case inherit g v a of
      Right t   => case synth ((x,b)::g) n of
        Right (c**u) => Right (c ** GApp el t u)
        Left ctra    => Left $ NotGAppN el ctra
      Left ctra => Left $ NotGAppV el ctra
    Left ctra           => Left $ NotGAppE ctra
  synth g (Let x nv n)   = case synthV g nv of
    Right (a**t) => case synth ((x,a)::g) n of
      Right (b**u) => Right (b**Let t u)
      Left ctra    => Left $ NotLetN t ctra
    Left ctra    => Left $ NotLetV ctra

  synthV : (g : Ctx Ty) -> (n : NeuV) -> Either (NotNeuV g n) (a ** NeuV g n a)
  synthV g (Var s)   = case lookupE g s of
    Right (a**el) => Right (a**Var el)
    Left ctra     => Left $ NotVar ctra
  synthV g (Cut v t) = case inherit g v t of
    Right u   => Right (t**Cut u)
    Left ctra => Left $ NotCut ctra

  inherit : (g : Ctx Ty) -> (m : Val) -> (a : Ty) -> Either (NotVal g m a) (Val g m a)
  inherit _ (Lam _ _)  A        = Left $ NotLamT uninhabited
  inherit g (Lam s n) (Imp a b) = case synth ((s,a)::g) n of
    Right (c**t) => case decEq b c of
      Yes Refl => Right $ Lam t
      No ctra  => Left $ NotLamN t ctra
    Left ctra    => Left $ NotLam ctra
  inherit g (Emb nv)   a        = case synthV g nv of
    Right (b**m) => case decEq a b of
      Yes prf => Right $ Emb m (sym prf)
      No ctra => Left $ NotEmbQ m (\p => ctra $ sym p)
    Left ctra    => Left $ NotEmb ctra

module ProdLet.TyCheck.Chk

import Decidable.Equality
import Data.List
import Data.String.Parser

import Ctx
import ProdLet.Ty
import ProdLet.Parser
import ProdLet.Term
import ProdLet.TyCheck.Term
import ProdLet.TyCheck.NotTerm

%default total

mutual
  synth : (g : Ctx Ty) -> (n : Neu) -> Either (NotNeu g n) (a ** Neu g n a)
  synth g (Var s)    = case lookupE g s of
    Right (a**el) => Right (a ** Var el)
    Left ctra => Left $ NotVar ctra
  synth g (App t u) = case synth g t of
    Right (U**n)        => Left $ NotAppFT n uninhabited
    Right (Prod _ _**n) => Left $ NotAppFT n uninhabited
    Right (Imp a b**n)  => case inherit g u a of
      Right m => Right (b ** App n m)
      Left ctra => Left $ NotAppA n ctra
    Left ctra => Left $ NotAppF ctra
  synth g (Cut v t) = case inherit g v t of
    Right val => Right (t ** Cut val)
    Left ctra => Left $ NotCut ctra

  inherit : (g : Ctx Ty) -> (m : Val) -> (a : Ty) -> Either (NotVal g m a) (Val g m a)
  inherit _ (Lam _ _)         U         = Left $ NotLamT uninhabited
  inherit _ (Lam _ _)        (Prod _ _) = Left $ NotLamT uninhabited
  inherit g (Lam s v)        (Imp a b)  = case inherit ((s,a)::g) v b of
    Right w => Right $ Lam w
    Left ctra => Left $ NotLam ctra
  inherit g  TT               U         = Right TT
  inherit _  TT              (Imp _ _)  = Left $ NotTTT uninhabited
  inherit _  TT              (Prod _ _) = Left $ NotTTT uninhabited
  inherit _ (Pair _ _)        U         = Left $ NotPairT uninhabited
  inherit _ (Pair _ _)       (Imp _ _)  = Left $ NotPairT uninhabited
  inherit g (Pair l r)       (Prod a b) = case inherit g l a of
    Right x => case inherit g r b of
      Right y => Right $ Pair x y
      Left ctra => Left $ NotPairR ctra
    Left ctra => Left $ NotPairL ctra
  inherit g (LetP n x y v)    c         = case synth g n of
    Right (U**n0)        => Left $ NotLetPT n0 uninhabited
    Right (Imp _ _**n0)  => Left $ NotLetPT n0 uninhabited
    Right (Prod a b**n0) => case inherit ((y,b)::(x,a)::g) v c of
      Right v0 => Right $ LetP n0 v0
      Left ctra => Left $ NotLetPC n0 ctra
    Left ctra => Left $ NotLetP ctra
  inherit g (Emb n)           a         = case synth g n of
    Right (b ** m) => case decEq a b of
      Yes prf => Right $ Emb m (sym prf)
      No ctra => Left $ NotEmbQ m (\p => ctra $ sym p)
    Left ctra => Left $ NotEmb ctra

covering
parseCheckTerm : String -> Either String (a ** Term [] a)
parseCheckTerm s = do (b,_) <- parse (neu <* eos) s
                      case synth [] b of
                        Right (a ** n) => Right (a ** neu2Term n)
                        Left e => Left $ show e
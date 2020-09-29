module ProdSum.TyCheck.Chk

import Decidable.Equality
import Data.List
import Data.String.Parser
import Control.Monad.Identity
import Ctx
import ProdSum.Ty
import ProdSum.Parser
import ProdSum.Term
import ProdSum.TyCheck.Term
import ProdSum.TyCheck.NotTerm

%default total

mutual
  synth : (g : Ctx Ty) -> (n : Neu) -> Either (NotNeu g n) (a ** Neu g n a)
  synth g (Var s)   = case lookupE g s of
    Right (a**el) => Right (a ** Var el)
    Left ctra => Left $ NotVar ctra
  synth g (App t u) = case synth g t of
    Right (A**n)          => Left $ NotAppFT n uninhabited
    Right ((Prod _ _)**n) => Left $ NotAppFT n uninhabited
    Right ((Sum _ _)**n)  => Left $ NotAppFT n uninhabited
    Right ((Imp a b)**n) => case inherit g u a of
      Right m => Right (b ** App n m)
      Left ctra => Left $ NotAppA n ctra
    Left ctra => Left $ NotAppF ctra
  synth g (Fst t) = case synth g t of
    Right (A**n)          => Left $ NotFstT n uninhabited
    Right ((Imp _ _)**n)  => Left $ NotFstT n uninhabited
    Right ((Sum _ _)**n)  => Left $ NotFstT n uninhabited
    Right ((Prod a b)**n) => Right (a**Fst n)
    Left ctra => Left $ NotFst ctra
  synth g (Snd t) = case synth g t of
    Right (A**n)          => Left $ NotSndT n uninhabited
    Right ((Imp _ _)**n)  => Left $ NotSndT n uninhabited
    Right ((Sum _ _)**n)  => Left $ NotSndT n uninhabited
    Right ((Prod a b)**n) => Right (b**Snd n)
    Left ctra => Left $ NotSnd ctra
  synth g (Cut v t) = case inherit g v t of
    Right val => Right (t ** Cut val)
    Left ctra => Left $ NotCut ctra

  inherit : (g : Ctx Ty) -> (m : Val) -> (a : Ty) -> Either (NotVal g m a) (Val g m a)
  inherit _ (Lam _ _)         A         = Left $ NotLamT uninhabited
  inherit _ (Lam _ _)        (Prod _ _) = Left $ NotLamT uninhabited
  inherit _ (Lam _ _)        (Sum _ _)  = Left $ NotLamT uninhabited
  inherit g (Lam s v)        (Imp a b)  = case inherit ((s,a)::g) v b of
    Right w => Right $ Lam w
    Left ctra => Left $ NotLam ctra
  inherit _ (Pair _ _)        A         = Left $ NotPairT uninhabited
  inherit g (Pair l r)       (Prod a b) = case inherit g l a of
    Right x => case inherit g r b of
      Right y => Right $ Pair x y
      Left ctra => Left $ NotPairR ctra
    Left ctra => Left $ NotPairL ctra
  inherit _ (Pair _ _)       (Sum _ _)  = Left $ NotPairT uninhabited
  inherit _ (Pair _ _)       (Imp _ _)  = Left $ NotPairT uninhabited
  inherit _ (Inl _)           A         = Left $ NotInlT uninhabited
  inherit _ (Inl _)          (Prod _ _) = Left $ NotInlT uninhabited
  inherit g (Inl l)          (Sum a _)  = case inherit g l a of
    Right x => Right $ Inl x
    Left ctra => Left $ NotInl ctra
  inherit _ (Inl _)          (Imp _ _)  = Left $ NotInlT uninhabited
  inherit _ (Inr _)           A         = Left $ NotInrT uninhabited
  inherit _ (Inr _)          (Prod _ _) = Left $ NotInrT uninhabited
  inherit g (Inr r)          (Sum _ b)  = case inherit g r b of
    Right y => Right $ Inr y
    Left ctra => Left $ NotInr ctra
  inherit _ (Inr _)          (Imp _ _)  = Left $ NotInrT uninhabited
  inherit g (Case c x l y r)  t         = case synth g c of
    Right (A        ** n) => Left $ NotCaseT n uninhabited
    Right (Imp _ _  ** n) => Left $ NotCaseT n uninhabited
    Right (Prod _ _ ** n) => Left $ NotCaseT n uninhabited
    Right (Sum a b  ** n) => case inherit ((x,a)::g) l t of
      Right p => case inherit ((y,b)::g) r t of
        Right q => Right $ Case n p q
        Left ctra => Left $ NotCaseR n ctra
      Left ctra => Left $ NotCaseL n ctra
    Left ctra => Left $ NotCase ctra
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

{-
"(\\x.x : 1->1)" ~ (Imp A A ** Lam $ Var Here)
"(\\x.x : ((1->1)->(1->1))->((1->1)->(1->1))) (\\x.x) (\\x.x)" ~ (Imp A A ** App (App (Lam $ Var Here) (Lam $ Var Here)) (Lam $ Var Here)))
"(\\x.x : ((1->1)->(1->1))) ((\\x.x : (1->1)->(1->1)) (\\x.x))" ~ (Imp A A ** App (Lam $ Var Here) (App (Lam $ Var Here) (Lam $ Var Here))))
"(\\x._1 x : (1->1)*(1->1)->(1->1)) (<\\x.x, \\x.x>)" ~ (Imp A A ** App (Lam $ Fst $ Var Here) (Pair (Lam $ Var Here) (Lam $ Var Here)))
-}
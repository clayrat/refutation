module ProdSum.TyCheck.CheckE

import Decidable.Equality
import Data.List
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

mutual
  val2Term : Val g m a -> Term (eraseCtx g) a
  val2Term (Lam v)      = Lam $ val2Term v
  val2Term (Pair l r)   = Pair (val2Term l) (val2Term r)
  val2Term (Inl l)      = Inl $ val2Term l
  val2Term (Inr r)      = Inr $ val2Term r
  val2Term (Case n l r) = Case (neu2Term n) (val2Term l) (val2Term r)
  val2Term (Emb v Refl) = neu2Term v

  neu2Term : Neu g n a -> Term (eraseCtx g) a
  neu2Term (Var i)   = Var $ eraseInCtx i
  neu2Term (Fst n)   = Fst $ neu2Term n
  neu2Term (Snd n)   = Snd $ neu2Term n
  neu2Term (Cut v)   = val2Term v
  neu2Term (App t u) = App (neu2Term t) (val2Term u)

{-
parseCheckTerm : String -> Either Error (a ** Term [] a)
parseCheckTerm s = do b <- parseNeu s
                      case synth [] b of
                        Right (a ** n) => Right (a ** neu2Term n)
                        Left _ => Left $ TypeError ""

private
test0 : parseCheckTerm "(\\x.x : *->*)" = Right (TestTy ** ResultTm)
test0 = Refl

--private
--test1 : parseCheckTerm "(\\x.x : ((*->*)->(*->*))->((*->*)->(*->*))) (\\x.x) (\\x.x)" = Right (TestTy ** TestTm1)
--test1 = Refl

--private
--test2 : parseCheckTerm "(\\x.x : ((*->*)->(*->*))) ((\\x.x : (*->*)->(*->*)) (\\x.x))" = Right (TestTy ** TestTm2)
--test2 = Refl
-}
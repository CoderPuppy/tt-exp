module TTExp.Cubical where

import Prelude hiding (pi)

import Control.Monad (when)
import Data.Either.Combinators (maybeToRight)
import Data.Eq.Deriving (deriveEq1)
import Data.Functor.Identity (Identity(runIdentity))
import Safe (atMay)
import Text.Show.Deriving (deriveShow1)

import TTExp.Core qualified as Core

newtype LamE a = LamE { argType :: a }
	deriving (Show, Eq, Functor)
deriveShow1 ''LamE
deriveEq1 ''LamE

data Ext t
	= EType | EPi
	| EFType | ELiftFT
	| EFPi
	| EI | EI0 | EI1
	| EMax | EMin | ENeg
	| EPathP | EMkPathP
	| EPartial
	deriving (Show, Eq, Functor)
deriveShow1 ''Ext
deriveEq1 ''Ext

type Term = Core.Term LamE Ext
pattern Lam at b = Core.Lam (LamE at) b
pattern Type = Core.Ext EType
pattern Pi at rt = Core.App (Core.App (Core.Ext EPi) at) rt
pattern FType = Core.Ext EFType
pattern LiftFT t = Core.App (Core.Ext ELiftFT) t
pattern FPi at rt = Core.App (Core.App (Core.Ext EFPi) at) rt
pattern I = Core.Ext EI
pattern I0 = Core.Ext EI0
pattern I1 = Core.Ext EI1
pattern PathP p a b = Core.App (Core.App (Core.App (Core.Ext EPathP) p) a) b
pattern Partial i t = Core.App (Core.App (Core.Ext EPartial) i) t
pi :: Term -> Term -> Term
pi at rt = Pi at $ Lam at rt
fpi :: Term -> Term -> Term
fpi at rt = FPi at $ Lam at rt

instance Core.ExtForce LamE Ext Identity where
	extForce (I0:as) EMax = pure $ Just (as, Lam I $ Core.Var 0)
	extForce (a:I0:as) EMax = pure $ Just (as, a)
	extForce (I1:as) EMax = pure $ Just (as, Lam I I1)
	extForce (a:I1:as) EMax = pure $ Just (as, I1)
	extForce (I0:as) EMin = pure $ Just (as, Lam I I0)
	extForce (a:I0:as) EMin = pure $ Just (as, I0)
	extForce (I1:as) EMin = pure $ Just (as, Lam I $ Core.Var 0)
	extForce (a:I1:as) EMin = pure $ Just (as, a)
	extForce (I0:as) ENeg = pure $ Just (as, I1)
	extForce (I1:as) ENeg = pure $ Just (as, I0)
	extForce (_:l:i:as) EMkPathP = pure $ Just (i:as, l)
	extForce _ _ = pure $ Nothing

force :: Term -> Term
force = runIdentity . Core.force

unify :: Term -> Term -> Either String ()
unify a b = case (force a, force b) of
	(Core.App af aa, Core.App bf ba) -> do
		unify af bf
		unify aa ba
	(Lam aat ab, Lam bat bb) -> do
		unify aat bat
		unify ab bb
	(a, b) | a == b -> pure ()
	(a, b) -> Left $ "unification mismatch: " <> show a <> " /= " <> show b

typeCheck :: [Term] -> Term -> Either String Term
typeCheck env (Core.Var v) =
	fmap (Core.subst $ Core.Var . (+ (v + 1))) $
	maybeToRight "unbound variable" $ atMay env v
typeCheck env (Core.App f a) = do
	(fta, ftr) <- fmap force (typeCheck env f) >>= \case
		Pi fta ftr -> pure (fta, ftr)
		LiftFT (force -> FPi fta ftr) ->
			pure (LiftFT fta, LiftFT ftr)
		PathP p _ _ -> pure (I, p)
		ft -> Left $ "invalid function type: " <> show ft
	at <- typeCheck env a
	unify fta at
	pure $ Core.App ftr a
typeCheck env (Lam at b) = do
	att <- typeCheck env at
	unify att Type
	rt <- typeCheck (at:env) b
	pure $ case (force at, force rt) of
		(LiftFT at', LiftFT rt') -> LiftFT $ fpi at rt
		(at, rt) -> pi at rt
typeCheck env Type = pure Type
typeCheck env (Core.Ext EPi) = pure $ pi Type $ pi (pi (Core.Var 0) Type) $ Type
typeCheck env FType = pure $ LiftFT FType
typeCheck env (Core.Ext ELiftFT) = pure $ pi (LiftFT FType) Type
typeCheck env (Core.Ext EFPi) = pure $ LiftFT $ fpi FType $ fpi (fpi (Core.Var 0) FType) $ FType
typeCheck env I = pure Type
typeCheck env I0 = pure I
typeCheck env I1 = pure I
typeCheck env (Core.Ext EMax) = pure $ pi I $ pi I $ I
typeCheck env (Core.Ext EMin) = pure $ pi I $ pi I $ I
typeCheck env (Core.Ext ENeg) = pure $ pi I $ I
typeCheck env (Core.Ext EPathP) = pure $
	pi (pi I $ LiftFT FType) $
	LiftFT $
	fpi (Core.App (Core.Var 0) I0) $
	fpi (Core.App (Core.Var 1) I1) $
	FType
typeCheck env (Core.Ext EMkPathP) = pure $
	pi (pi I (LiftFT FType)) $
	pi (pi I $ LiftFT $ Core.App (Core.Var 1) (Core.Var 0)) $
	LiftFT $ PathP (Core.Var 1) (Core.App (Core.Var 0) I0) (Core.App (Core.Var 0) I1)
-- typeCheck env (Core.Ext (Lift EPartial)) = pure $
-- 	pi I $ LiftFT $ fpi (Partial (Core.Var 0) _) $ FType

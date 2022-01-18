module TTExp.Refinements where

import Data.Either.Combinators (maybeToRight)
import Data.Eq.Deriving (deriveEq1)
import Data.Foldable (foldl')
import Prelude hiding (pi)
import Safe (atMay)
import Text.Show.Deriving (deriveShow1)

import TTExp.Core qualified as Core

newtype LamE t = LamE { argType :: t }
	deriving (Functor, Show, Eq)
deriveShow1 ''LamE
deriveEq1 ''LamE

data Ext t = EPi | EType | ESingleton deriving (Functor, Show, Eq)
deriveShow1 ''Ext
deriveEq1 ''Ext

type Term = Core.Term LamE Ext
pattern Lam at b = Core.Lam (LamE at) b
pattern Pi at rt = Core.App (Core.App (Core.Ext EPi) at) rt
pattern Type = Core.Ext EType
pattern Singleton t x = Core.App (Core.App (Core.Ext ESingleton) t) x
pi :: Term -> Term -> Term
pi at rt = Pi at $ Lam at rt

force' :: [Term] -> [Term] -> Term -> Term
force' env as t | Right (Singleton _ t') <- fmap (force env) (typeCheck env t) = force' env as t'
force' env as (Core.App f a) = force' env (a:as) f
force' env (a:as) (Lam _ b) = force' env as $ Core.subst (Core.envCons a Core.Var) b
force' env as t = foldl' Core.App t as

force :: [Term] -> Term -> Term
force env t = force' env [] t

unify :: [Term] -> Term -> Term -> Either String ()
unify env a b = case (force env a, force env b) of
	(Core.App af aa, Core.App bf ba) -> do
		unify env af bf
		unify env aa ba
	(Lam aat ab, Lam bat bb) -> do
		unify env aat bat
		unify (aat:env) ab bb
	(a, b) | a == b -> pure ()
	(a, b) -> Left $ "unification mismatch: " <> show a <> " /= " <> show b

typeCheck :: [Term] -> Term -> Either String Term
typeCheck env (Core.Var v) =
	fmap (Core.subst $ Core.Var . (+ (v + 1))) $
	maybeToRight "unbound variable" $ atMay env v
typeCheck env (Core.App f a) = do
	(fta, ftr) <- fmap (force env) (typeCheck env f) >>= \case
		Pi fta ftr -> pure (fta, ftr)
		ft -> Left $ "invalid function type: " <> show ft
	at <- typeCheck env a
	unify env fta at
	pure $ Core.App ftr a
typeCheck env (Lam at b) = do
	att <- typeCheck env at
	unify env att Type
	rt <- typeCheck (at:env) b
	pure $ Pi at $ Lam at rt
typeCheck env (Core.Ext EPi) = pure $ pi Type $ pi (pi (Core.Var 0) Type) $ Type
typeCheck env (Core.Ext EType) = pure Type
typeCheck env (Core.Ext ESingleton) = pure $ pi Type $ pi (Core.Var 0) $ Type

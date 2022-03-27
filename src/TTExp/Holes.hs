{-# LANGUAGE FlexibleInstances #-}

module TTExp.Holes where

-- this is currently broken

import Prelude hiding (pi)

import Control.Applicative (empty, liftA2)
import Control.Arrow (second)
import Control.Exception.Base (Exception)
import Data.Bifunctor (bimap)
import Data.Either.Combinators (maybeToRight)
import Data.Eq.Deriving (deriveEq1)
import Data.Foldable (fold, foldrM, for_)
import Data.Functor.Classes (Show1, Eq1)
import Data.IntSet qualified as IS
import Data.Typeable (Typeable)
import Debug.Trace
import Safe (atMay)
import Text.Show.Deriving (deriveShow1)

import TTExp.Core qualified as Core
import TTExp.Core hiding (Term(Lam', Ext'), Lam, Ext, Spine)
import TTExp.Monad.Meta
import TTExp.Util

newtype LamE t = LamE { argType :: t }
	deriving (Functor, Show, Eq, Foldable)
data Ext m t
	= EType | EPi
	| EMismatch | EBadAppT
	| EMeta (Lift m (Term m)) t
	| EHole t
	deriving (Functor, Foldable)
type Term m = Core.Term LamE (Ext m)
type Spine m = Core.Spine LamE (Ext m)

deriveShow1 ''LamE
deriveEq1 ''LamE
deriveShow1 ''Ext
deriveEq1 ''Ext

deriving instance (Show1 m, Show t) => Show (Ext m t)

pattern Lam at b = Core.Lam (LamE at) b
pattern Type = Core.Ext EType
pattern Pi at rt = Core.App (Core.App (Core.Ext EPi) at) rt
pattern Mismatch gt e et = Core.App (Core.App (Core.App (Core.Ext EMismatch) gt) e) et
pattern BadAppT ft at = Core.App (Core.App (Core.Ext EBadAppT) ft) at
pattern Meta m t = Core.Ext (EMeta (Lift m) t)
pattern Hole t = Core.Ext (EHole t)
pi :: Term m -> Term m -> Term m
pi at rt = Pi at $ Lam at rt

type Term' = Term MV
type Spine' = Spine MV

instance Monad m => Core.ExtForce LamE (Ext MV) (MetaT Term' m) where
	extForce as (EMeta (Lift m) t) = fmap (fmap (as,)) $ checkMV m
	extForce as e = pure Nothing

newMeta :: Monad m => [Term'] -> Term' -> MetaT Term' m Term'
newMeta env t = do
	mv <- newMV
	let mt = foldl (flip Pi) t env
	let head = Meta mv mt
	pure $ foldr (flip App . Var) head [0..length env - 1]

unifySpine :: forall m. MonadFail m => [Term'] -> Spine' -> Spine' -> MetaT Term' m ()
unifySpine env a b = liftA2 (,) (uncurry forceSpine a) (uncurry forceSpine b)
	>>= \case
		(([], Lam aat ab), ([], Lam bat bb)) -> do
			-- unifying the argument types should be unnecessary
			-- which makes this whole case unnecessary
			unifySpine env ([], aat) ([], bat)
			unifySpine (aat:env) ([], ab) ([], bb)
		(([], Lam aat ab), b) -> unifyEta (aat, ab) b
		(a, ([], Lam bat bb)) -> unifyEta (bat, bb) a
		((aas, Meta a t), b) -> unifyMeta (aas, a, t) b
		(a, (bas, Meta b t)) -> unifyMeta (bas, b, t) a
		(a, b) | a == b -> pure ()
		(a, b) -> fail $ "unification mismatch: " <> show a <> " /= " <> show b

	where
		unifyMeta :: ([Term'], MV Term', Term') -> Spine' -> MetaT Term' m ()
		unifyMeta (aas, a, t) (uncurry unspine -> b) = do
			let f = fold $ fmap freeVars aas
			(aats, t) <- spineTypes (length aas) t
			traceM $ "env = " <> show env
			traceM $ "meta = " <> show (zip aas aats, a, t)
			traceM $ "b = " <> show b
			(env', s) <- metaify
				0 (reverse aats) Var
				(reverse env) (IS.toDescList $ fold $ fmap freeVars aas)
			traceM $ "env' = " <> show env'
			traceM $ "inverted sol = " <> show (subst s b)
			for_ (zip (reverse [0..length aas - 1]) aas) $ \(v, a) -> do
				let a' = subst (subst (Var . (+ length aas)) . s) a
				unify env' (Var v) a'
			error $ "TODO: " <> show ((((aas, aats), (a, t)), b), env')

			where
				n = length env

				metaify :: Int -> [Term'] -> (Int -> Term') -> [Term'] -> [Int] -> MetaT Term' m ([Term'], Int -> Term')
				metaify m env s [] [] | n == m = pure (env, s)
				metaify m env s (t:rest) (v:vs) | n == m + v + 1 = do
					let t' = subst s t
					e <- newMeta env t'
					metaify
						(m + 1)
						(t':env)
						(envCons e s)
						rest vs
				metaify m env s (t:rest) vs =
					metaify
						(m + 1)
						(subst s t:env)
						(envCons (Var 0) $ subst (Var . (+ 1)) . s)
						rest vs
				metaify m env s rest vs = error $ show (n, m, env, rest, vs)

				spineTypes :: Int -> Term' -> MetaT Term' m ([Term'], Term')
				spineTypes 0 t = pure ([], t)
				spineTypes k t = do
					Pi at rt <- force t
					(ats, t') <- spineTypes (k - 1) rt
					pure (at:ats, t')

		unifyEta :: (Term', Term') -> Spine' -> MetaT Term' m ()
		unifyEta (aat, ab) (bas, b) =
			unifySpine
				(aat:env) ([], ab)
				(Var 0:fmap (subst (Var . (+1))) bas, b)

unify :: MonadFail m => [Term'] -> Term' -> Term' -> MetaT Term' m ()
unify env a b = unifySpine env (spine [] a) (spine [] b)

typeCheck :: MonadFail m => [Term'] -> Term' -> Term' -> MetaT Term' m Term'
typeCheck env e t = fmap (e, ) (Core.force t) >>= \case
	(Lam at1 b, Pi at2 rt) -> do
		at1' <- typeCheck env at1 Type
		unify env at1' at2
		b' <- typeCheck (at1':env) b (App (subst (Var . (+1)) rt) (Var 0))
		pure $ Lam at1' b'
	_ -> do
		(e', t') <- typeInfer env e
		locally (unify env t t') >>= \case
			Nothing -> pure $ Mismatch t' e' t
			Just () -> pure e'

typeInfer :: MonadFail m => [Term'] -> Term' -> MetaT Term' m (Term', Term')
typeInfer env e@(Core.Var v) = pure (e, Core.subst (Core.Var . (+ (v + 1))) (env !! v))
typeInfer env (Core.App f a) = do
	(f', ft) <- typeInfer env f
	(a', t) <- Core.force ft >>= \case
		Pi at rt -> do
			a' <- typeCheck env a at
			pure (a', Core.App rt a')
		_ -> fmap (second (BadAppT ft)) $ typeInfer env a
	pure (Core.App f' a', t)
typeInfer env (Lam at b) = do
	at' <- typeCheck env at Type
	fmap (bimap (Lam at') (pi at')) $ typeInfer (at':env) b
typeInfer env Type = pure (Type, Type)
typeInfer env e@(Core.Ext EMismatch) = pure (e, pi Type $ pi (Core.Var 0) $ pi Type $ Core.Var 0)
typeInfer env e@(Core.Ext EBadAppT) = pure (e, pi Type $ pi Type $ Type)
typeInfer env (Meta m t) = do
	t' <- typeCheck env t Type
	pure (Meta m t', t)
typeInfer env (Hole t) = do
	t' <- typeCheck env t Type
	e <- newMeta env t'
	pure (e, t')

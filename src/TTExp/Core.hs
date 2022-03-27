module TTExp.Core where

import Control.Monad.Trans.Maybe (MaybeT(MaybeT), runMaybeT)
import Data.Foldable (fold, foldl')
import Data.IntSet qualified as IS

import TTExp.Util (Lift(Lift))

data Term l e
	= Var Int
	| App (Term l e) (Term l e)
	| Lam' (Lift l (Term l e)) (Term l e)
	| Ext' (Lift e (Term l e))
	deriving (Show, Eq)
pattern Lam l b = Lam' (Lift l) b
pattern Ext e = Ext' (Lift e)

freeVars :: (Functor l, Functor e, Foldable l, Foldable e) => Term l e -> IS.IntSet
freeVars (Var v) = IS.singleton v
freeVars (App f a) = IS.union (freeVars f) (freeVars a)
freeVars (Lam l b) =
	IS.union
		(fold $ fmap freeVars l)
		(IS.delete 0 $ IS.mapMonotonic (+ -1) $ freeVars b)
freeVars (Ext e) = fold $ fmap freeVars e

envCons :: a -> (Int -> a) -> (Int -> a)
envCons z s 0 = z
envCons z s v = s (v - 1)

subst :: (Functor l, Functor e) => (Int -> Term l e) -> Term l e -> Term l e
subst env (Var v) = env v
subst env (App f a) = App (subst env f) (subst env a)
subst env (Lam l b) = Lam
	(fmap (subst env) l)
	(subst (envCons (Var 0) (subst (Var . (+1)) . env)) b)
subst env (Ext e) = Ext $ fmap (subst env) e

type Spine l e = ([Term l e], Term l e)

spine :: [Term l e] -> Term l e -> Spine l e
spine as (App f a) = spine (a:as) f
spine as t = (as, t)

unspine :: [Term l e] -> Term l e -> Term l e
unspine as t = foldl' App t as

class ExtForce l e m where
	extForce :: [Term l e] -> e (Term l e) -> m (Maybe (Spine l e))

forceSpine ::
	(Functor l, Functor e, ExtForce l e m, Monad m) =>
	[Term l e] -> Term l e -> m (Spine l e)
forceSpine as t = case spine as t of
	(a:as, Lam _ b) -> forceSpine as $ subst (envCons a Var) b
	s@(as, Ext e) -> extForce as e >>= \case
		Nothing -> pure s
		Just s' -> uncurry forceSpine s'
	s -> pure s

force :: (Functor l, Functor e, ExtForce l e m, Monad m) => Term l e -> m (Term l e)
force = fmap (uncurry unspine) . forceSpine []

module TTExp.Core where

import TTExp.Util (Lift(Lift))
import Data.Foldable (foldl')

data Term l e
	= Var Int
	| App (Term l e) (Term l e)
	| Lam' (Lift l (Term l e)) (Term l e)
	| Ext' (Lift e (Term l e))
	deriving (Show, Eq)
pattern Lam l b = Lam' (Lift l) b
pattern Ext e = Ext' (Lift e)

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

class ExtForce l e where
	extForce :: [Term l e] -> e (Term l e) -> Maybe ([Term l e], Term l e)

force' :: (Functor l, Functor e, ExtForce l e) => [Term l e] -> Term l e -> Term l e
force' as (App f a) = force' (a:as) f
force' (a:as) (Lam _ b) = force' as $ subst (envCons a Var) b
force' as (Ext e) | Just (as', t') <- extForce as e = force' as' t'
force' as t = foldl' App t as

force :: (Functor l, Functor e, ExtForce l e) => Term l e -> Term l e
force = force' []

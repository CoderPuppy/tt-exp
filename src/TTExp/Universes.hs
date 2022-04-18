{-# LANGUAGE FlexibleInstances #-}

module TTExp.Universes where

import Data.Foldable (foldl')

data Expected v
	= Expected v
	| ExpectedOrdinal
	| ExpectedType
	deriving (Show, Functor)
data Inspection v
	= App v
	| AppT v
	deriving (Show, Functor)
data NeutralHead v
	= Var Int
	| Mismatch v (Expected v)
	deriving (Show, Functor)
data Term
	= Neutral (NeutralHead Term)
	| Inspect Term (Inspection Term)
	| Lam Term Term
	| Type Term
	| Ordinal Term
	| O0
	| OSucc Term
	| Pi Term Term
	deriving (Show)
data Value
	= VNeutral [Inspection Value] (NeutralHead Value)
	| VClo Value [Value] Term
	| VType Value
	| VOrdinal Value
	| VO0
	| VOSucc Value
	| VPi Value Value
	deriving (Show)

inspect :: Value -> Inspection Value -> Value
inspect (VNeutral is head) i = VNeutral (i:is) head
inspect (VClo at env body) (App arg) = eval (arg:env) body
inspect (VPi at rt) (AppT arg) = inspect rt (App arg)
inspect v i = error "bad"

class Eval a where
	eval :: [Value] -> a -> Value

instance Eval v => Eval (NeutralHead v) where
	eval env (Var v) = env !! v
	eval env (Mismatch t exp) =
		VNeutral [] $ Mismatch (eval env t) (fmap (eval env) exp)
instance Eval Term where
	eval env (Neutral head) = eval env head
	eval env (Inspect t i) = inspect (eval env t) (fmap (eval env) i)
	eval env (Lam at body) = VClo (eval env at) env body
	eval env (Type o) = VType $ eval env o
	eval env (Ordinal o) = VOrdinal $ eval env o
	eval env O0 = VO0
	eval env (OSucc o) = VOSucc $ eval env o
	eval env (Pi at rt) = VPi (eval env at) (eval env rt)

reify :: Int -> Value -> Term
reify l (VNeutral is head) = foldr
	(flip Inspect)
	(Neutral $ ($ head') $ fmap $ reify l)
	(($ is) $ fmap $ fmap $ reify l)
	where head' = case head of
		Var v -> Var $ l - v - 1
		h -> h
reify l (VClo at env body) =
	Lam (reify l at) $
	reify (l + 1) $
	inspect (eval env body) (App $ VNeutral [] $ Var l)
reify l (VType o) = Type $ reify l o
reify l (VOrdinal o) = Ordinal $ reify l o
reify l VO0 = O0
reify l (VOSucc o) = OSucc $ reify l o
reify l (VPi at rt) = Pi (reify l at) (reify l rt)

-- subtype :: Term -> Term -> Bool
-- subtype = _

-- typeInfer :: [Term] -> Term -> (Term, Term)
-- typeCheck :: [Term] -> (Term, Term) -> Term

-- typeInfer env (Var v) = (Var v, subst (Var . (+ (v + 1))) (env !! v))
-- typeInfer env (App f a) = (App f' a', t)
-- 	where
-- 		(f', ft) = typeInfer env f
-- 		(a', t) = case force ft of
-- 			Pi at rt -> let
-- 					a' = typeCheck env (a, at)
-- 				in (a', App rt a')
-- 			_ -> let
-- 					(a', at) = typeInfer env a
-- 				in (a', BadAppT ft at)
-- typeInfer env (Lam at b) = (Lam at' b', Pi at' rt)
-- 	where
-- 		at' = typeCheck env (at, Type Nothing)
-- 		(b', rt) = typeInfer (at':env) b
-- typeInfer env (Type l) = (Type l', Type $ case force lt of
-- 		Level _ -> LSucc l'
-- 		_ -> BadLevel l)
-- 	where (l', lt) = typeInfer env l
-- typeInfer env (Level l) = (Level l', Type L0)
-- 	where l' = case typeInfer env l of
-- 		(l', force -> Level _) -> l'
-- 		(l', _) -> BadLevel l'
-- typeInfer env L0 = (L0, Level $ LSucc L0)
-- typeInfer env (LSucc l) = (LSucc l', Level $ LSucc lt)
-- 	where (l', lt) = case typeInfer env l of
-- 		(l', force -> Level lt) -> (l', lt)
-- 		(l', lt) -> (BadLevel l', BadLevelLevel lt)
-- typeInfer env (Pi at rt) = (Pi at' rt', Type l)
-- 	where
-- 		at' = case typeInfer env at of
-- 			(at', force -> Type atl) -> at'
-- 			(at', _) -> BadType at'
-- 		rt' = case typeInfer (at':env) rt of
-- 			(rt', force -> Pi _ (force -> Type l)) -> (rt', l)
-- 			(rt', _) -> (Lam at' (App 
--
-- typeCheck env (Lam at b, force -> Pi atP rt)
-- 	| subtype atP at'
-- 	= Lam at' $ typeCheck (at':env) (b, App rt $ Var 0)
-- 	where at' = typeCheck env (at, Type Nothing)

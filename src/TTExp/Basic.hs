module TTExp.Basic where

import Data.Either.Combinators (maybeToRight)
import Data.Eq.Deriving (deriveEq1)
import Prelude hiding (pi)
import Safe (atMay)
import Text.Show.Deriving (deriveShow1)
import Data.Bifunctor (bimap, second)

import TTExp.Core qualified as Core
import TTExp.Core (pattern Var, pattern App, force, subst)

newtype LamE t = LamE { argType :: t }
	deriving (Functor, Show, Eq)
deriveShow1 ''LamE
deriveEq1 ''LamE

data Ext t
	= EType | EPi
	| EMismatch | EBadAppT
	deriving (Functor, Show, Eq)
deriveShow1 ''Ext
deriveEq1 ''Ext
instance Core.ExtForce LamE Ext where
	extForce _ _ = Nothing

type Term = Core.Term LamE Ext
pattern Lam at b = Core.Lam (LamE at) b
pattern Type = Core.Ext EType
pattern Pi at rt = App (App (Core.Ext EPi) at) rt
pattern Mismatch gt e et = App (App (App (Core.Ext EMismatch) gt) e) et
pattern BadAppT ft at = App (App (Core.Ext EBadAppT) ft) at
pi :: Term -> Term -> Term
pi at rt = Pi at $ Lam at rt

unify :: Term -> Term -> Either String ()
unify a b = case (force a, force b) of
	(App af aa, App bf ba) -> do
		unify af bf
		unify aa ba
	(Lam aat ab, Lam bat bb) -> do
		unify aat bat
		unify ab bb
	(a, b) | a == b -> pure ()
	(a, b) -> Left $ "unification mismatch: " <> show a <> " /= " <> show b

typeInfer :: [Term] -> Term -> (Term, Term)
typeCheck :: [Term] -> (Term, Term) -> Term

typeInfer env e@(Var v) = (e, subst (Var . (+ (v + 1))) (env !! v))
typeInfer env (App f a) = (App f' a', t)
	where
		(f', ft) = typeInfer env f
		(a', t) = case force ft of
			Pi at rt -> let a' = typeCheck env (a, at) in (a', App rt a')
			_ -> second (BadAppT ft) $ typeInfer env a
typeInfer env (Lam at b) = bimap (Lam at') (pi at') $ typeInfer (at':env) b
	where at' = typeCheck env (at, Type)
typeInfer env e@(Core.Ext EType) = (e, Type)
typeInfer env e@(Core.Ext EPi) = (e, pi Type $ pi (pi (Var 0) Type) $ Type)
typeInfer env e@(Core.Ext EMismatch) = (e, pi Type $ pi (Var 0) $ pi Type $ Var 0)
typeInfer env e@(Core.Ext EBadAppT) = (e, pi Type $ pi Type $ Type)

typeCheck env (Lam at b, force -> Pi atP rt)
	| Right _ <- unify atP at'
	= Lam at' $ typeCheck (at':env) (b, App rt $ Var 0)
	where at' = typeCheck env (at, Type)
typeCheck env (e, t) = case unify t t' of
	Left _ -> Mismatch t' e t
	Right _ -> e'
	where (e', t') = typeInfer env e

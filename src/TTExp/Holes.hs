module TTExp.Holes where

import Control.Arrow (second)
import Data.Bifunctor (bimap)
import Data.Either.Combinators (maybeToRight)
import Data.Eq.Deriving (deriveEq1)
import Prelude hiding (pi)
import Safe (atMay)
import Text.Show.Deriving (deriveShow1)

import TTExp.Core qualified as Core

newtype LamE t = LamE { argType :: t }
	deriving (Functor, Show, Eq)
deriveShow1 ''LamE
deriveEq1 ''LamE

data Ext t
	= EType | EPi
	| EUnknown | EMismatch | EBadAppT
	deriving (Functor, Show, Eq)
deriveShow1 ''Ext
deriveEq1 ''Ext

type Term = Core.Term LamE Ext
pattern Lam at b = Core.Lam (LamE at) b
pattern Type = Core.Ext EType
pattern Pi at rt = Core.App (Core.App (Core.Ext EPi) at) rt
pattern Unknown t = Core.App (Core.Ext EUnknown) t
pattern Mismatch gt e et = Core.App (Core.App (Core.App (Core.Ext EMismatch) gt) e) et
pattern BadAppT ft at = Core.App (Core.App (Core.Ext EBadAppT) ft) at
pi :: Term -> Term -> Term
pi at rt = Pi at $ Lam at rt

instance Core.ExtForce LamE Ext where
	extForce as e = Nothing

typeCheck :: [Term] -> Term -> Term -> Term
typeCheck env e t = _

typeInfer :: [Term] -> Term -> (Term, Term)
typeInfer env e@(Core.Var v) = (e, Core.subst (Core.Var . (+ (v + 1))) (env !! v))
typeInfer env (Core.App f a) = (Core.App f' a', t)
	where
		(f', ft) = typeInfer env f
		(a', t) = case Core.force ft of
			Pi at rt -> let a' = typeCheck env a at in (a', Core.App rt a')
			_ -> second (BadAppT ft) $ typeInfer env a
typeInfer env (Lam at b) = bimap (Lam at') (pi at') $ typeInfer (at':env) b
	where at' = typeCheck env at Type
typeInfer env e@(Core.Ext EUnknown) = (e, pi Type $ Core.Var 0)
typeInfer env e@(Core.Ext EMismatch) = (e, pi Type $ pi (Core.Var 0) $ pi Type $ Core.Var 0)
typeInfer env e@(Core.Ext EBadAppT) = (e, pi Type $ pi Type $ Type)

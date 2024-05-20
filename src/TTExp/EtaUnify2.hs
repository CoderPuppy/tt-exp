{-# OPTIONS_GHC -Wno-tabs -Wincomplete-patterns #-}

module TTExp.EtaUnify2 where

import Control.Applicative
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Data.Functor.Identity
import Data.IntMap qualified as IM
import GHC.Stack (HasCallStack)

newtype MetaV = MetaV { unMetaV :: Int } deriving (Show, Eq)
data MetaRef tm = MetaRef
	{ metaRefV :: MetaV
	, metaRefSub :: [tm]
	} deriving (Show, Functor)

newtype Idx = Idx { unIdx :: Int } deriving (Show, Eq)

data Proj t = App t | Fst | Snd deriving (Show, Functor)

data Tm
	= TVar Idx
	| TMeta (MetaRef Tm)
	| TProj Tm (Proj Tm)
	| TType
	| TNonLinear
	| TPi Tm Tm
	| TLam Tm
	| TSg Tm Tm
	| TPair Tm Tm
	deriving (Show)

data Family
	= Closure Env Tm
	deriving (Show)

newtype Lvl = Lvl { unLvl :: Int } deriving (Show, Eq)

newtype Spine = Spine { unSpine :: [Proj Val] } deriving (Show)
pattern EmptySp = Spine []
pattern ProjSp sp proj <- Spine (proj:(Spine -> sp))
	where ProjSp sp proj = Spine (proj:unSpine sp)

data Neu = Neu'Var Lvl | Neu'Meta (MetaRef Val) deriving (Show)

data Val
	= VNeu Neu Spine
	| VType
	| VNonLinear
	| VPi Val Family
	| VLam Family
	| VSg Val Family
	| VPair Val Val
	deriving (Show)
vNeu :: Neu -> Val
vNeu n = VNeu n EmptySp
pattern VVar v sp = VNeu (Neu'Var v) sp
vVar :: Lvl -> Val
vVar v = VVar v EmptySp
pattern VMeta ref sp = VNeu (Neu'Meta ref) sp
vMeta :: MetaRef Val -> Val
vMeta ref = VMeta ref EmptySp

newtype Env = Env { unEnv :: [Val] } deriving (Show)
pattern EmptyEnv = Env []
pattern ExtendEnv env val <- Env (val:(Env -> env))
	where ExtendEnv env val = Env (val:unEnv env)
evalVar :: Env -> Idx -> Val
evalVar (Env env) (Idx idx) = env !! idx

apply :: HasCallStack => Family -> Val -> Val
apply (Closure env body) arg = eval (ExtendEnv env arg) body

project :: HasCallStack => Val -> Proj Val -> Val
project head proj = case (head, proj) of
	(VNeu neu sp, _) -> VNeu neu $ ProjSp sp proj
	(VNonLinear, _) -> VNonLinear
	(VLam fam, App arg) -> apply fam arg
	(VPair fst snd, Fst) -> fst
	(VPair fst snd, Snd) -> snd
	_ -> error $ "Projecting " <> show proj <> " out of " <> show head

eval :: HasCallStack => Env -> Tm -> Val
eval env tm = case tm of
	TVar v -> evalVar env v
	TMeta mr -> vMeta $ fmap (eval env) mr
	TProj head proj -> project (eval env head) (fmap (eval env) proj)
	TType -> VType
	TNonLinear -> VNonLinear
	TPi base fam -> VPi (eval env base) (Closure env fam)
	TLam body -> VLam (Closure env body)
	TSg base fam -> VSg (eval env base) (Closure env fam)
	TPair fst snd -> VPair (eval env fst) (eval env snd)

data Glued = Glued
	{ gluedTm :: Tm
	, gluedVal :: Val
	} deriving (Show)
newtype Ctx = Ctx { unCtx :: [Glued] } deriving (Show)
pattern EmptyCtx = Ctx []
pattern ExtendCtx ctx ty <- Ctx (ty:(Ctx -> ctx))
extendCtx :: Ctx -> Val -> (Ctx, Lvl)
extendCtx ctx ty = error "TODO"

abstractEnv :: Ctx -> Env
abstractEnv (Ctx ctx) = Env $ fmap (vVar . Lvl) $ reverse [0..length ctx - 1]

vMetaRef :: Ctx -> MetaV -> Val
vMetaRef ctx meta = vMeta $ MetaRef meta $ unEnv $ abstractEnv ctx

tMetaRef :: Ctx -> MetaV -> Tm
tMetaRef (Ctx ctx) meta = TMeta $ MetaRef meta $ fmap (TVar . Idx) [0..length ctx - 1]

class Glueable a where
	glue :: Ctx -> a -> Glued
instance Glueable Tm where
	glue ctx tm = Glued
		{ gluedTm = tm
		, gluedVal = eval (abstractEnv ctx) tm
		}
instance Glueable Val where
	glue ctx val = Glued
		{ gluedTm = quote ctx val
		, gluedVal = val
		}

quoteVar :: Ctx -> Lvl -> Idx
quoteVar (Ctx ctx) (Lvl lvl) = Idx $ length ctx - lvl - 1

quoteFamily :: Ctx -> Val -> Family -> Tm
quoteFamily ctx base fam = quote ctx' $ apply fam $ vVar var
	where (ctx', var) = extendCtx ctx base

quoteSpine :: Ctx -> Tm -> Spine -> Tm
quoteSpine ctx head sp = case sp of
	EmptySp -> head
	ProjSp sp proj -> TProj (quoteSpine ctx head sp) (fmap (quote ctx) proj)

quote :: Ctx -> Val -> Tm
quote ctx val = case val of
	VNeu neu sp -> flip (quoteSpine ctx) sp $
		case neu of
			Neu'Var var -> TVar (quoteVar ctx var)
			Neu'Meta m -> TMeta $ fmap (quote ctx) m
	VType -> TType
	VNonLinear -> TNonLinear
	VPi base fam -> TPi (quote ctx base) (quoteFamily ctx base fam)
	VLam body -> TLam $ quoteFamily ctx (error "TODO") body
	VSg base fam -> TSg (quote ctx base) (quoteFamily ctx base fam)
	VPair fst snd -> TPair (quote ctx fst) (quote ctx snd)

data MetaData = MetaData
	{
	} deriving (Show)
data MetaContext = MetaContext
	{ metaContextLinearLevel :: Maybe Lvl
	} deriving (Show)
data MetaState = MetaState
	{ metaStateData :: IM.IntMap MetaData
	, metaStateNext :: MetaV
	} deriving (Show)
newtype MetaT m a = MetaT { unMetaT :: ReaderT MetaContext (StateT MetaState m) a }
	deriving newtype (Functor, Applicative, Monad)
instance MonadTrans MetaT where
	lift = MetaT . lift . lift
type MetaM a = MetaT Identity a
newMeta :: Glueable ty => Ctx -> ty -> MetaM MetaV
newMeta ctx ty = error "TODO"
solveMeta :: MetaV -> Tm -> MetaM ()
solveMeta m sol = error "TODO"
force :: Val -> MetaM Val
force = error "TODO"

newtype UnifyErr = UnifyErr { unUnifyErr :: ShowS }
instance Show UnifyErr where
	showsPrec d = unUnifyErr

unifyErr_mismatch :: Val -> Val -> Val -> UnifyErr
unifyErr_mismatch ty a b = UnifyErr $ shows a . showString " /= " . shows b . showString " : " . shows ty

type UnifyM a = ExceptT UnifyErr (MetaT Identity) a

data Inversion = Inversion
	{ inversionArgs :: [Val]
	, inversionCtx :: Ctx
	, inversionTy :: Val
	-- idea: defunctionalize this
	, inversionBuild :: Tm -> MetaM Tm
	}

invertProj :: Inversion -> Proj Val -> MetaM Inversion
invertProj inv@Inversion{..} proj = case proj of
	App arg -> do
		(base, fam) <- flip fmap (force inversionTy) \case
			VPi base fam -> (base, fam)
			_ -> error $ "Inverting application in non-Π-type: " <> show inversionTy
		let (inversionCtx', var) = extendCtx inversionCtx base
		pure $ Inversion
			{ inversionArgs = arg:inversionArgs
			, inversionCtx = inversionCtx'
			, inversionTy = apply fam $ vVar var
			, inversionBuild = fmap TLam . inversionBuild
			}

	Fst -> do
		(base, fam) <- flip fmap (force inversionTy) \case
			VSg base fam -> (base, fam)
			_ -> error $ "Inverting fst in non-Σ-type: " <> show inversionTy
		pure $ inv
			{ inversionTy = base
			, inversionBuild = \fst -> do
				m <- newMeta inversionCtx fst
				pure $ TPair fst $ tMetaRef inversionCtx m
			}

	Snd -> do
		(base, fam) <- flip fmap (force inversionTy) \case
			VSg base fam -> (base, fam)
			_ -> error $ "Inverting snd in non-Σ-type: " <> show inversionTy
		m <- newMeta inversionCtx base
		pure $ inv
			{ inversionTy = apply fam $ vMetaRef inversionCtx m
			, inversionBuild = fmap (TPair $ tMetaRef inversionCtx m) . inversionBuild
			}

finishInversion :: Ctx -> Inversion -> UnifyM (Val -> MetaM Tm)
finishInversion eq_ctx Inversion{..} = do
	-- TODO: meta level
	-- metas_env : inversionCtx ⊢ eq_ctx
	(metas, metas_env) <- lift $ buildMetas inversionCtx eq_ctx
	sequence_ $ reverse $ getZipList do
		-- ty : inversionCtx ⊢ Type
		ty <- ZipList $ unCtx inversionCtx
		-- arg : eq_ctx ⊢ ty[…]
		arg <- ZipList inversionArgs
		-- param : inversionCtx ⊢ ty
		param <- ZipList $ unEnv $ abstractEnv inversionCtx
		pure $ case quote eq_ctx arg of
			TVar var -> lift $ solveMeta (metas !! unIdx var) (quote inversionCtx param)
			arg -> unify _ inversionCtx (gluedVal ty) param (eval metas_env arg)
	pure $ inversionBuild . quote inversionCtx . eval metas_env . quote eq_ctx

	where
		buildMetas :: Ctx -> Ctx -> MetaM ([MetaV], Env)
		buildMetas inversionCtx eq_ctx = case eq_ctx of
			EmptyCtx -> pure ([], EmptyEnv)
			ExtendCtx eq_ctx ty -> do
				(metas, metas_env) <- buildMetas inversionCtx eq_ctx
				meta <- newMeta inversionCtx $ eval metas_env $ gluedTm ty
				pure (meta:metas, ExtendEnv metas_env $ vMetaRef inversionCtx meta)

unify :: Maybe MetaV -> Ctx -> Val -> Val -> Val -> UnifyM ()
unify ml ctx ty a b = case (a, b) of
		(a@(VMeta a_m a_sp), b@(VMeta b_m b_sp)) -> error "TODO"
		(VMeta m sp, b) -> unifyMeta m sp b
		(a, VMeta m sp) -> unifyMeta m sp a

		(VLam body, b) -> unifyLam body b
		(a, VLam body) -> unifyLam body a

		(VPair fst snd, b) -> unifyPair fst snd b
		(a, VPair fst snd) -> unifyPair fst snd a

		(VType, VType) -> pure ()

		(VPi a_base a_fam, VPi b_base b_fam) -> unifyTyForm a_base a_fam b_base b_fam
		(VSg a_base a_fam, VSg b_base b_fam) -> unifyTyForm a_base a_fam b_base b_fam

		(a@(VVar a_v a_sp), b@(VVar b_v b_sp))
			| a_v == b_v, Just unif <- unifySpines a_sp b_sp -> unif

		_ -> throwE $ unifyErr_mismatch ty a b


	where
		unifyMeta :: MetaRef Val -> Spine -> Val -> UnifyM ()
		unifyMeta mr sp other = error "TODO"

		unifyLam :: Family -> Val -> UnifyM ()
		unifyLam body other = do
			(base, fam) <- flip fmap (lift $ force ty) \case
				VPi base fam -> (base, fam)
				_ -> error $ "Unifying lambda in non-Π-type: " <> show ty
			let (ctx', var) = extendCtx ctx base
			unify ml ctx'
				(apply fam           $ vVar var)
				(apply body          $ vVar var)
				(project other $ App $ vVar var)

		unifyPair :: Val -> Val -> Val -> UnifyM ()
		unifyPair fst snd other = do
			(base, fam) <- flip fmap (lift $ force ty) \case
				VSg base fam -> (base, fam)
				_ -> error $ "Unifying pair in non-Σ-type: " <> show ty
			unify ml ctx base            fst (project other Fst)
			unify ml ctx (apply fam fst) snd (project other Snd)

		unifyTyForm :: Val -> Family -> Val -> Family -> UnifyM ()
		unifyTyForm a_base a_fam b_base b_fam = do
			unify ml ctx VType a_base b_base
			let (ctx', var) = extendCtx ctx a_base
			unify ml ctx' VType
				(apply a_fam $ vVar var)
				(apply b_fam $ vVar var)

		unifySpines :: Spine -> Spine -> Maybe (UnifyM ())
		unifySpines = error "TODO"

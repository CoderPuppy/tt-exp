{-# OPTIONS_GHC -Wno-tabs -Wincomplete-patterns #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StarIsType #-}
{-# LANGUAGE ViewPatterns #-}

module TTExp.EtaUnify where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Data.Foldable
import Data.IntMap qualified as IM
import Debug.Trace
import GHC.Stack (HasCallStack)

newtype CtxLen = CtxLen { unCtxLen :: Int } deriving (Show, Eq, Ord)
newtype Idx = Idx { unIdx :: Int } deriving (Show, Eq, Ord)
newtype Lvl = Lvl { unLvl :: Int } deriving (Show, Eq, Ord)
quoteLvl :: CtxLen -> Lvl -> Idx
quoteLvl (CtxLen l) (Lvl v) = Idx $ l - v - 1

data Neu v = Var v | Meta MetaV deriving (Show, Functor)
data Proj t = App t | Fst | Snd deriving (Show, Functor)

data Tm
	= Neu (Neu Idx)
	| Proj Tm (Proj Tm)
	| Type
	| NonLinear

	| Pi Tm Tm
	| Lam Tm

	| Sg Tm Tm
	| Pair Tm Tm

	deriving (Show)

tmProj :: Tm -> [Proj Tm] -> Tm
tmProj = foldl Proj

type Spine = [Proj Val]

-- types
newtype Ctx = Ctx { unCtx :: [Glued] } deriving (Show)
ctxLookup :: Ctx -> Idx -> Glued
ctxLookup (Ctx ctx) (Idx idx) = ctx !! idx
extendCtx'Val :: Ctx -> Val -> (Ctx, Lvl)
extendCtx'Val ctx ty = extendCtx ctx $ gluedQuote (ctxLen ctx) ty
extendCtx'Tm :: HasCallStack => Ctx -> Tm -> (Ctx, Lvl)
extendCtx'Tm ctx ty = extendCtx ctx $ gluedEval (abstractEnv ctx) ty

class Context ctx where
	type ContextTy ctx :: *
	ctxLen :: ctx -> CtxLen
	emptyCtx :: ctx
	extendCtx :: ctx -> ContextTy ctx -> (ctx, Lvl)
instance Context CtxLen where
	type ContextTy CtxLen = ()
	ctxLen = id
	emptyCtx = CtxLen 0
	extendCtx (CtxLen l) _ = (CtxLen (l + 1), Lvl l)
instance Context Ctx where
	type ContextTy Ctx = Glued
	ctxLen = CtxLen . length . unCtx
	emptyCtx = Ctx []
	extendCtx (Ctx ctx) ty = (Ctx (ty:ctx), Lvl $ length ctx)

newtype Env = Env { unEnv :: [Val] } deriving (Show)
emptyEnv :: Env
emptyEnv = Env []
extendEnv :: Env -> Val -> Env
extendEnv (Env env) val = Env $ val:env
evalVar :: HasCallStack => Env -> Idx -> Val
evalVar (Env env) (Idx v) = env !! v
abstractEnv :: Context ctx => ctx -> Env
abstractEnv ctx = Env $ fmap (vVar . Lvl) $ reverse [0..unCtxLen (ctxLen ctx) - 1]

data Closure
	= Close Env Tm
	deriving (Show)

data Val
	= VNeu (Neu Lvl) Spine
	| VType
	| VNonLinear
	| VPi Val Closure
	| VLam Closure
	| VSg Val Closure
	| VPair Val Val
	deriving (Show)
vNeu :: Neu Lvl -> Val
vNeu n = VNeu n []
pattern VVar v sp = VNeu (Var v) sp
vVar :: Lvl -> Val
vVar v = VVar v []
pattern VMeta m sp = VNeu (Meta m) sp
vMeta :: MetaV -> Val
vMeta m = VMeta m []

eval :: HasCallStack => Env -> Tm -> Val
eval env = \case
	Neu (Var v) -> evalVar env v
	Neu (Meta m) -> VNeu (Meta m) []
	Proj head proj -> project (eval env head) (fmap (eval env) proj)
	Type -> VType
	NonLinear -> VNonLinear
	Pi base fam -> VPi (eval env base) (Close env fam)
	Lam body -> VLam (Close env body)
	Sg base fam -> VSg (eval env base) (Close env fam)
	Pair fst snd -> VPair (eval env fst) (eval env snd)

apply :: Closure -> Val -> Val
apply (Close env body) a = eval (extendEnv env a) body

project :: Val -> Proj Val -> Val
project (VNeu neu spine) proj = VNeu neu (proj:spine)
project VNonLinear proj = VNonLinear
project (VLam clo) (App a) = apply clo a
project (VPair fst snd) Fst = fst
project (VPair fst snd) Snd = snd
project head proj = error $ "Projecting " <> show proj <> " out of " <> show head

quoteClosure :: CtxLen -> Closure -> Tm
quoteClosure ctx clo = quote ctx' $ apply clo $ vVar var
	where (ctx', var) = extendCtx ctx ()

quote :: CtxLen -> Val -> Tm
quote l = \case
	VNeu neu spine ->
		foldr (flip Proj)
			(Neu $ fmap (quoteLvl l) neu)
			(fmap (fmap $ quote l) spine)
	VType -> Type
	VNonLinear -> NonLinear
	VPi base fam -> Pi (quote l base) (quoteClosure l fam)
	VLam clo -> Lam (quoteClosure l clo)
	VSg base fam -> Sg (quote l base) (quoteClosure l fam)
	VPair fst snd -> Pair (quote l fst) (quote l snd)

data Glued = Glued
	{ gluedEnv :: Env
	, gluedTm :: Tm
	, gluedVal :: Val
	} deriving (Show)

gluedEval :: HasCallStack => Env -> Tm -> Glued
gluedEval env tm = Glued
	{ gluedEnv = env
	, gluedTm = tm
	, gluedVal = eval env tm
	}

gluedQuote :: CtxLen -> Val -> Glued
gluedQuote ctx v = Glued
	{ gluedEnv = abstractEnv ctx
	, gluedTm = quote ctx v
	, gluedVal = v
	}

force :: Val -> State MetaEnv Val
force = \case
	v@(VNeu (Meta m) sp) -> lookupMeta m >>= \case
		MetaData { metaDataValue = Just val } -> pure $ foldr (flip project) val sp
		_ -> pure v
	v -> pure v

newtype MetaV = MetaV { unMetaV :: Int } deriving (Show, Eq, Ord)
data MetaData = MetaData
	{ metaDataTy :: Val
	, metaDataValue :: Maybe Val
	} deriving (Show)
data MetaEnv = MetaEnv
	{ metaEnvData :: IM.IntMap MetaData
	, metaEnvNext :: MetaV
	} deriving (Show)

newMeta :: Val -> State MetaEnv MetaV
newMeta ty = state $ \me@MetaEnv { metaEnvNext = MetaV mv } ->
	(MetaV mv, me
		{ metaEnvData = IM.insert mv (MetaData ty Nothing) $ metaEnvData me
		, metaEnvNext = MetaV $ mv + 1
		})

lookupMeta :: MetaV -> State MetaEnv MetaData
lookupMeta (MetaV m) = fmap ((IM.! m) . metaEnvData) get

updateMeta :: MetaV -> (Maybe Val -> Maybe Val) -> State MetaEnv ()
updateMeta (MetaV m) f = modify \me -> me {
	metaEnvData = IM.update (\md -> Just $ md {
		metaDataValue = f $ metaDataValue md
	}) m (metaEnvData me) }

-- create a new meta while abstracting over a context
newMetaAbs :: Ctx -> Val -> State MetaEnv (MetaV, Glued)
newMetaAbs ctx ty = do
	m <- newMeta $ eval emptyEnv $
		foldl (flip Pi) (quote (ctxLen ctx) ty) $ fmap gluedTm $ unCtx ctx
	let ref = gluedQuote (ctxLen ctx) $
		VNeu (Meta m) $ fmap App $
		unEnv $ abstractEnv ctx
	pure (m, ref)

applyInversion :: Ctx -> Val -> [Proj a] -> Tm -> State MetaEnv Tm
applyInversion ctx ty sp tm = case sp of
	[] -> pure tm
	App _:sp -> do
		(base, fam) <- flip fmap (force ty) \case
			VPi base fam -> (base, fam)
			ty -> error $ "Inverting application in non-Π-type: " <> show ty
		let (ctx', v) = extendCtx ctx (gluedQuote (ctxLen ctx) base)
		tm <- applyInversion ctx' (apply fam (vVar v)) sp tm
		pure $ Lam tm
	Fst:sp -> do
		(base, fam) <- flip fmap (force ty) \case
			VSg base fam -> (base, fam)
			ty -> error $ "Inverting fst in non-Σ-type: " <> show ty
		tm <- applyInversion ctx base sp tm
		(_, snd) <- newMetaAbs ctx $ apply fam $ eval (abstractEnv ctx) tm -- TODO: check this
		pure $ Pair tm (gluedTm snd)
	Snd:sp -> do
		(base, fam) <- flip fmap (force ty) \case
			VSg base fam -> (base, fam)
			ty -> error $ "Inverting snd in non-Σ-type: " <> show ty
		(_, fst) <- newMetaAbs ctx base
		tm <- applyInversion ctx (apply fam $ gluedVal fst) sp tm
		pure $ Pair (gluedTm fst) tm

unify :: Maybe MetaV -> Ctx -> Val -> Val -> Val -> ExceptT String (State MetaEnv) ()
unify ml ctx ty a b = case (a, b) of
		(a@(VNeu (Meta a_m) a_sp), b@(VNeu (Meta b_m) b_sp)) -> ExceptT $ state \me ->
			case (
				flip runState me $ runExceptT $ unifyMeta a_m a_sp b,
				flip runState me $ runExceptT $ unifyMeta b_m b_sp a
			) of
				((Right _, me), _) -> (Right (), me)
				((Left _, _), (Right _, me)) -> (Right (), me)
				((Left err, me), (Left _, _)) -> (Left err, me)
		(VNeu (Meta m) sp, b) -> unifyMeta m sp b
		(a, VNeu (Meta m) sp) -> unifyMeta m sp a

		(VLam clo, b) -> unifyLam clo b
		(a, VLam clo) -> unifyLam clo a

		(VPair fst snd, b) -> unifyPair fst snd b
		(a, VPair fst snd) -> unifyPair fst snd a

		(VType, VType) -> pure ()
		(VPi a_base a_fam, VPi b_base b_fam) -> do
			unify ml ctx VType a_base b_base
			let (ctx', var) = extendCtx ctx (gluedQuote (ctxLen ctx) a_base)
			unify ml ctx' VType
				(apply a_fam $ vVar var)
				(apply b_fam $ vVar var)
		(VSg a_base a_fam, VSg b_base b_fam) -> do
			unify ml ctx VType a_base b_base
			let (ctx', var) = extendCtx ctx (gluedQuote (ctxLen ctx) a_base)
			unify ml ctx' VType
				(apply a_fam $ vVar var)
				(apply b_fam $ vVar var)
		(a@(VNeu (Var a_v) a_sp), b@(VNeu (Var b_v) b_sp))
			| a_v == b_v, length a_sp == length b_sp ->
				void $ foldrM
					(\case
						(App a, App b) -> \(sp, ty) -> do
							(base, fam) <- flip fmap (lift $ force ty) \case
								VPi base fam -> (base, fam)
								ty -> error $ "Unifying application of non-Π-type: " <> show ty
							unify ml ctx base a b
							pure (App a:sp, apply fam a)
						(Fst, Fst) -> \(sp, ty) -> do
							(base, fam) <- flip fmap (lift $ force ty) \case
								VSg base fam -> (base, fam)
								ty -> error $ "Unifying fst of non-Σ-type: " <> show ty
							pure (Fst:sp, base)
						(Snd, Snd) -> \(sp, ty) -> do
							(base, fam) <- flip fmap (lift $ force ty) \case
								VSg base fam -> (base, fam)
								ty -> error $ "Unifying snd of non-Σ-type: " <> show ty
							pure (Snd:sp, apply fam $ VNeu (Var a_v) (Fst:sp))
						_ -> \_ -> throwE $ show a <> " /= " <> show b <> " : " <> show ty
					)
					([], gluedVal $ ctxLookup ctx $ quoteLvl (ctxLen ctx) a_v)
					(zip a_sp b_sp)

		(a, b) -> throwE $ show a <> " /= " <> show b <> " : " <> show ty

	where
		unifyMeta :: MetaV -> Spine -> Val -> ExceptT String (State MetaEnv) ()
		unifyMeta m sp other = lift (lookupMeta m) >>= \case
			MetaData { metaDataValue = Just m_val } ->
				let innerUnify = unify ml ctx ty (foldr (flip project) m_val sp) other
				in if maybe False (m >=) ml
				then lift $ runExceptT innerUnify >>= \case
					Left err -> updateMeta m $ const $ Just VNonLinear
					Right () -> pure ()
				else innerUnify
			md -> do
				-- match the arguments in the spine to the type of the meta
				-- args are reverse order (same as spines)
				(body_ctx, args, body_ty, _) <- lift $ foldrM
					(flip \(body_ctx, args, body_ty, sp) -> \case
						App arg -> do
							(base, fam) <- flip fmap (force body_ty) \case
								VPi base fam -> (base, fam)
								_ -> error $ "Inverting application in non-Π-type: " <> show body_ty
							let (body_ctx', var) = extendCtx'Val body_ctx base
							pure (
								body_ctx',
								arg:args,
								apply fam (vVar var),
								App (vVar var):sp)
						Fst -> do
							(base, fam) <- flip fmap (force body_ty) \case
								VSg base fam -> (base, fam)
								_ -> error $ "Inverting fst in non-Σ-type: " <> show body_ty
							pure (body_ctx, args, base, Fst:sp)
						Snd -> do
							(base, fam) <- flip fmap (force body_ty) \case
								VSg base fam -> (base, fam)
								_ -> error $ "Inverting snd in non-Σ-type: " <> show body_ty
							pure (body_ctx, args, apply fam (VNeu (Meta m) (Fst:sp)), Snd:sp)
					)
					(emptyCtx, [], metaDataTy md, []) sp

				ml' <- fmap metaEnvNext $ lift get

				(ctx_metas, env) <- lift $ foldrM
					(\ty (ctx_metas, env) -> do
						(m', m'_ref) <- newMetaAbs body_ctx $ eval env $ gluedTm ty
						pure $ (m':ctx_metas, extendEnv env $ gluedVal m'_ref)
					)
					([], emptyEnv) (unCtx ctx)

				sequence_ $ reverse $ getZipList $ do
					i <- ZipList [0..]
					arg_ty <- ZipList $ unCtx body_ctx
					arg <- ZipList args
					abstract_arg <- ZipList $ unEnv $ abstractEnv body_ctx
					pure $ case arg of
						VNeu (Var var) [] ->
							lift $ updateMeta (ctx_metas !! unIdx (quoteLvl (ctxLen ctx) var)) $ \case
								Nothing -> Just $ eval emptyEnv $
									flip (foldr $ const Lam) args $
									Neu $ Var $ Idx i
								Just _ -> Just VNonLinear
						_ -> unify (Just ml') body_ctx (gluedVal arg_ty) abstract_arg $
							eval env $ quote (ctxLen ctx) arg

				tm <- lift $ applyInversion emptyCtx (metaDataTy md) sp $
					quote (ctxLen body_ctx) $ eval env $ quote (ctxLen ctx) other

				-- TODO: typecheck `tm` against `metaDataty md`

				lift $ updateMeta m $ const $ Just $ eval emptyEnv tm

		unifyLam :: Closure -> Val -> ExceptT String (State MetaEnv) ()
		unifyLam clo other = do
			(base, fam) <- flip fmap (lift $ force ty) \case
				VPi base fam -> (base, fam)
				ty -> error $ "Unifying lambda in non-Π-type: " <> show ty
			let (ctx', var) = extendCtx ctx $ gluedQuote (ctxLen ctx) base
			unify ml ctx'
				(apply fam           $ vVar var)
				(apply clo           $ vVar var)
				(project other $ App $ vVar var)

		unifyPair :: Val -> Val -> Val -> ExceptT String (State MetaEnv) ()
		unifyPair fst snd other = do
			(base, fam) <- flip fmap (lift $ force ty) \case
				VSg base fam -> (base, fam)
				ty -> error $ "Unifying pair in non-Σ-type: " <> show ty
			unify ml ctx base fst (project other Fst)
			unify ml ctx (apply fam fst) snd (project other Snd)

type PP a = Int -> a -> ShowS

ppIdx :: PP Idx
ppIdx d (Idx i) = showString "^" . shows i

ppLvl :: PP Lvl
ppLvl d (Lvl l) = showString "l" . shows l

ppMetaV :: PP MetaV
ppMetaV d (MetaV mv) = showString "?" . shows mv

ppNeu :: PP v -> PP (Neu v)
ppNeu ppV d = \case
	Var v -> ppV d v
	Meta mv -> ppMetaV d mv

ppProj :: PP t -> PP (Proj t)
ppProj ppT d = \case
	App t -> ppT d t
	Fst -> showString ".1"
	Snd -> showString ".2"

ppTm :: PP Tm
ppTm d = \case
	Neu n -> ppNeu ppIdx d n
	Proj t p -> showParen (d > 10) $
		ppTm 10 t . showString " " . ppProj ppTm 11 p
	Type -> showString "Type"
	NonLinear -> showString "NonLinear"
	Pi base fam -> showParen (d > 5) $
		ppTm 6 base . showString " → " . ppTm 5 fam
	Lam body -> showParen (d > 5) $
		showString "λ " . ppTm 5 body
	Sg base fam -> showParen (d > 5) $
		ppTm 6 base . showString " × " . ppTm 5 fam
	Pair fst snd ->
		showString "(" . ppTm 0 fst . showString ", " . ppTm 0 snd . showString ")"

ppVal :: CtxLen -> Int -> Val -> ShowS
ppVal ctx d = \case
	VNeu n [] -> ppNeu ppLvl d n
	VNeu n sp -> showParen (d > 10) $
		(ppNeu ppLvl 10 n .) $
		foldr (.) id $ fmap ((showString " " .) . ppProj (ppVal ctx) 11) $ reverse sp
	VType -> showString "Type"
	VNonLinear -> showString "NonLinear"
	VPi base fam -> showParen (d > 5) $
		let (ctx', var) = extendCtx ctx () in
		showString "(" . ppLvl 0 var . showString " : " .
		ppVal ctx 0 base . showString ") → " .
		ppVal ctx' 5 (apply fam $ vVar var)
	VLam body -> showParen (d > 5) $
		let (ctx', var) = extendCtx ctx () in
		showString "λ" . ppLvl 0 var . showString " " .
		ppVal ctx' 5 (apply body $ vVar var)
	VSg base fam -> showParen (d > 5) $
		let (ctx', var) = extendCtx ctx () in
		showString "(" . ppLvl 0 var . showString " : " .
		ppVal ctx 0 base . showString ") × " .
		ppVal ctx' 5 (apply fam $ vVar var)
	VPair fst snd ->
		showString "(" . ppVal ctx 0 fst . showString ", " .
		ppVal ctx 0 snd . showString ")"

ppMetaEnv :: PP MetaEnv
ppMetaEnv d MetaEnv {..} = showParen (d > 0) $
	showString "next MV = " . ppMetaV 0 metaEnvNext . (
		foldr (.) id $ [
			showString "\n" . ppMetaV 2 mv .
			showString " : " . ppVal emptyCtx 2 metaDataTy .
			case metaDataValue of
				Nothing -> id
				Just val -> showString " = " . ppVal emptyCtx 2 val
			| (MetaV -> mv, MetaData {..}) <- IM.toList metaEnvData
		]
	)

test =
	flip runState (MetaEnv {
		metaEnvData = IM.empty,
		metaEnvNext = MetaV 0
	}) $ runExceptT do
		m <- lift $ newMeta $ eval emptyEnv $
			-- (A : Type) → (A → A → A) → A → A → A
			Pi Type $
			Pi (
				Pi (Neu $ Var $ Idx 0) $
				Pi (Neu $ Var $ Idx 1) $
				Neu $ Var $ Idx 2
			) $
			Pi (Neu $ Var $ Idx 1) $
			Pi (Neu $ Var $ Idx 2) $
			Neu $ Var $ Idx 3
		let ctx = foldl' ((fst .) . extendCtx'Tm) emptyCtx $ [
				Type,

				Pi (Neu $ Var $ Idx 0) $
				Pi (Neu $ Var $ Idx 1) $
				Neu $ Var $ Idx 2
			]
		let env = abstractEnv ctx
		unify Nothing
			ctx
			(eval env $
				Pi (Neu $ Var $ Idx $ 1) $
				Pi (Neu $ Var $ Idx $ 2) $
				Neu $ Var $ Idx 3
			)
			(eval env $
				tmProj (Neu $ Meta m) [
					App $ Neu $ Var $ Idx 1,
					App $ Lam $ Lam $ tmProj (Neu $ Var $ Idx 2) [
						App $ Neu $ Var $ Idx 0,
						App $ Neu $ Var $ Idx 1
					]
				]
			)
			(eval env $
				Neu $ Var $ Idx 0
			)

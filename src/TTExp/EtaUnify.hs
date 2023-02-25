{-# OPTIONS_GHC -Wno-tabs -Wincomplete-patterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

module TTExp.EtaUnify where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State
import Data.Foldable
import Data.IntMap qualified as IM
import Debug.Trace

newtype Idx = Idx { unIdx :: Int } deriving (Show, Eq, Ord)
newtype Lvl = Lvl { unLvl :: Int } deriving (Show, Eq, Ord)
quoteLvl :: Lvl -> Lvl -> Idx
quoteLvl (Lvl l) (Lvl v) = Idx $ l - v - 1
lvlIncr :: Lvl -> Lvl
lvlIncr (Lvl l) = Lvl $ l + 1
nextLvl :: [a] -> Lvl
nextLvl = Lvl . length

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
type Ctx = [Val]

type Env = [Val]

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

eval :: Env -> Tm -> Val
eval env = \case
	Neu (Var (Idx v)) -> env !! v
	Neu (Meta m) -> VNeu (Meta m) []
	Proj head proj -> project (eval env head) (fmap (eval env) proj)
	Type -> VType
	NonLinear -> VNonLinear
	Pi base fam -> VPi (eval env base) (Close env fam)
	Lam body -> VLam (Close env body)
	Sg base fam -> VSg (eval env base) (Close env fam)
	Pair fst snd -> VPair (eval env fst) (eval env snd)

apply :: Closure -> Val -> Val
apply (Close env body) a = eval (a:env) body

project :: Val -> Proj Val -> Val
project (VNeu neu spine) proj = VNeu neu (proj:spine)
project VNonLinear proj = VNonLinear
project (VLam clo) (App a) = apply clo a
project (VPair fst snd) Fst = fst
project (VPair fst snd) Snd = snd
project head proj = error $ "Projecting " <> show proj <> " out of " <> show head

quoteClosure :: Lvl -> Closure -> Tm
quoteClosure l clo = quote (lvlIncr l) $ apply clo $ VNeu (Var l) []

quote :: Lvl -> Val -> Tm
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

force :: Val -> State MetaEnv Val
force = \case
	v@(VNeu (Meta m) sp) -> lookupMeta m >>= \case
		MetaData { metaDataValue = Just val } -> pure $ foldr (flip project) val sp
		_ -> pure v
	v -> pure v

newMetaAbs :: [Tm] -> Val -> State MetaEnv (MetaV, (Tm, Val))
newMetaAbs ctx ty = do
	m <- newMeta $ eval [] $ foldl (flip Pi) (quote (nextLvl ctx) ty) ctx
	let tm = foldl'
		(\tm v -> Proj tm $ App $ Neu $ Var $ Idx v)
		(Neu $ Meta m) [0..length ctx - 1]
	let val = VNeu (Meta m) $
		fmap (App . flip VNeu [] . Var . Lvl) $
		reverse [0..length ctx - 1]
	pure (m, (tm, val))

applyInversion :: [Tm] -> Val -> [Proj a] -> Tm -> State MetaEnv Tm
applyInversion ctx ty sp tm = case sp of
	[] -> pure tm
	App _:sp -> do
		(base, fam) <- flip fmap (force ty) \case
			VPi base fam -> (base, fam)
			ty -> error $ "Inverting application in non-Π-type: " <> show ty
		tm <- applyInversion
			(quote (nextLvl ctx) base:ctx)
			(apply fam (VNeu (Var $ nextLvl ctx) [])) sp tm
		pure $ Lam tm
	Fst:sp -> do
		(base, fam) <- flip fmap (force ty) \case
			VSg base fam -> (base, fam)
			ty -> error $ "Inverting fst in non-Σ-type: " <> show ty
		tm <- applyInversion ctx base sp tm
		(_, (snd, _)) <- newMetaAbs ctx $ apply fam $ VNeu (Var $ nextLvl ctx) []
		pure $ Pair tm snd
	Snd:sp -> do
		(base, fam) <- flip fmap (force ty) \case
			VSg base fam -> (base, fam)
			ty -> error $ "Inverting snd in non-Σ-type: " <> show ty
		(_, (fst, _)) <- newMetaAbs ctx base
		tm <- applyInversion ctx base sp tm
		pure $ Pair fst tm

unify :: Maybe MetaV -> [Tm] -> Val -> Val -> Val -> ExceptT String (State MetaEnv) ()
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
			let var = VNeu (Var $ nextLvl ctx) []
			unify ml (quote (nextLvl ctx) a_base:ctx) VType (apply a_fam var) (apply b_fam var)
		(VSg a_base a_fam, VSg b_base b_fam) -> do
			unify ml ctx VType a_base b_base
			let var = VNeu (Var $ nextLvl ctx) []
			unify ml (quote (nextLvl ctx) a_base:ctx) VType (apply a_fam var) (apply b_fam var)
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
								ty -> error $ "Unifying fst of non-Σ-type: " <> show ty
							pure (Snd:sp, apply fam $ VNeu (Var a_v) sp)
						_ -> \_ -> throwE $ show a <> " /= " <> show b <> " : " <> show ty
					)
					([], eval
						(reverse $ fmap (flip VNeu [] . Var . Lvl) [0..length ctx - 1])
						(ctx !! (length ctx - unLvl a_v - 1)))
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
				(args, ty, _) <- lift $ foldrM
					(flip \(args, ty, sp) -> \case
						App arg -> do
							(base, fam) <- flip fmap (force ty) \case
								VPi base fam -> (base, fam)
								ty -> error $ "Inverting application in non-Π-type: " <> show ty
							let abstract_arg = VNeu (Var $ nextLvl args) []
							pure (
								((quote (nextLvl args) base, base), (arg, abstract_arg)):args,
								apply fam abstract_arg,
								App abstract_arg:sp)
						Fst -> do
							(base, fam) <- flip fmap (force ty) \case
								VSg base fam -> (base, fam)
								ty -> error $ "Inverting fst in non-Σ-type: " <> show ty
							pure (args, base, Fst:sp)
						Snd -> do
							(base, fam) <- flip fmap (force ty) \case
								VSg base fam -> (base, fam)
								ty -> error $ "Inverting snd in non-Σ-type: " <> show ty
							pure (args, apply fam (VNeu (Meta m) sp), Snd:sp)
					)
					([], metaDataTy md, []) sp

				ml' <- fmap metaEnvNext $ lift get

				(metas, env) <- lift $ foldrM
					(\ty (metas, env) -> do
						(m', (_, m'_val)) <- newMetaAbs (fmap (fst . fst) args) $ eval env ty
						pure $ (m':metas, m'_val:env)
					)
					([], []) ctx

				let ctx' = fmap fst args
				for_ (reverse $ zip [0..] args)
					\(i, ((_, arg_ty), (arg, abstract_arg))) ->
						case arg of
							VNeu (Var (Lvl l')) [] ->
								lift $ updateMeta (metas !! (length ctx - l' - 1)) $ \case
									Nothing -> Just $ eval [] $
										flip (foldr $ const Lam) args $
										Neu $ Var $ Idx i
									Just _ -> Just VNonLinear
							_ -> unify (Just ml') (fmap (fst . fst) args) arg_ty abstract_arg $
								eval env $ quote (nextLvl ctx) arg

				tm <- lift $ applyInversion [] (metaDataTy md) sp $ 
					quote (nextLvl args) $ eval env $ quote (nextLvl ctx) other

				-- TODO: typecheck `tm` against `metaDataty md`

				lift $ updateMeta m $ const $ Just $ eval [] tm

		unifyLam :: Closure -> Val -> ExceptT String (State MetaEnv) ()
		unifyLam clo other = do
			(base, fam) <- flip fmap (lift $ force ty) \case
				VPi base fam -> (base, fam)
				ty -> error $ "Unifying lambda in non-Π-type: " <> show ty
			let var = VNeu (Var $ nextLvl ctx) []
			unify ml (quote (nextLvl ctx) base:ctx)
				(apply fam var) (apply clo var) (project other $ App var)

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

ppVal :: Lvl -> Int -> Val -> ShowS
ppVal l d = \case
	VNeu n [] -> ppNeu ppLvl d n
	VNeu n sp -> showParen (d > 10) $
		(ppNeu ppLvl 10 n .) $
		foldr (.) id $ fmap ((showString " " .) . ppProj (ppVal l) 11) $ reverse sp
	VType -> showString "Type"
	VNonLinear -> showString "NonLinear"
	VPi base fam -> showParen (d > 5) $
		showString "(" . ppLvl 0 l . showString " : " .
		ppVal l 0 base . showString ") → " .
		ppVal (lvlIncr l) 5 (apply fam $ VNeu (Var l) [])
	VLam body -> showParen (d > 5) $
		showString "λ" . ppLvl 0 l . showString " " .
		ppVal (lvlIncr l) 5 (apply body $ VNeu (Var l) [])
	VSg base fam -> showParen (d > 5) $
		showString "(" . ppLvl 0 l . showString " : " .
		ppVal l 0 base . showString ") × " .
		ppVal (lvlIncr l) 5 (apply fam $ VNeu (Var l) [])
	VPair fst snd ->
		showString "(" . ppVal l 0 fst . showString ", " .
		ppVal l 0 snd . showString ")"

ppMetaEnv :: PP MetaEnv
ppMetaEnv d MetaEnv {..} = showParen (d > 0) $
	showString "next MV = " . ppMetaV 0 metaEnvNext . (
		foldr (.) id $ [
			showString "\n" . ppMetaV 2 mv .
			showString " : " . ppVal (Lvl 0) 2 metaDataTy .
			case metaDataValue of
				Nothing -> id
				Just val -> showString " = " . ppVal (Lvl 0) 2 val
			| (MetaV -> mv, MetaData {..}) <- IM.toList metaEnvData
		]
	)

test =
	flip runState (MetaEnv {
		metaEnvData = IM.empty,
		metaEnvNext = MetaV 0
	}) $ runExceptT do
		m <- lift $ newMeta $ eval [] $
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
		let env = reverse $ fmap (flip VNeu [] . Var . Lvl) [0..1]
		unify Nothing
			[
				Pi (Neu $ Var $ Idx 0) $
				Pi (Neu $ Var $ Idx 1) $
				Neu $ Var $ Idx 2,

				Type
			]
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

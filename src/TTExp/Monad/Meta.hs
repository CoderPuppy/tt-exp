module TTExp.Monad.Meta(
	MetaT, MV,
	newMV, fillMV, checkMV,
	locally,
	evalMetaT
) where

import Control.Applicative (Alternative)
import Control.Monad (MonadPlus)
import Control.Monad.Fix (MonadFix)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Trans.State.Strict (StateT(StateT, runStateT), state, get, evalStateT)
import Data.Eq.Deriving (deriveEq1)
import Data.Functor.Contravariant (Contravariant)
import Data.IntMap qualified as IM
import Text.Show.Deriving (deriveShow1)

import TTExp.Util

newtype MV t = MV { unMV :: Int }
	deriving (Show, Eq, Ord)
deriveShow1 ''MV
deriveEq1 ''MV
newtype MetaT t m a = MetaT { unMetaT :: StateT (Int, IM.IntMap t) m a }
	deriving newtype (Functor, Applicative, Monad, MonadFix, MonadFail, Contravariant, MonadIO, Alternative, MonadPlus)

newMV :: Monad m => MetaT t m (MV t)
newMV = MetaT $ state \(nv, m) -> (MV nv, (nv + 1, m))

fillMV :: MonadFail m => MV t -> t -> MetaT t m ()
fillMV (MV v) f = MetaT $ StateT \(nv, m) ->
	let (old, m') = IM.insertLookupWithKey undefined v f m
	in case old of
		Just _ -> fail $ "metavariable already filled: " <> show (MV v)
		Nothing -> pure ((), (nv, m'))

checkMV :: Monad m => MV t -> MetaT t m (Maybe t)
checkMV (MV v) = MetaT $ fmap (IM.lookup v . snd) get

locally :: (AffineFunctor m1, MonadFail m2) => MetaT t m1 a -> MetaT t m2 (m1 a)
locally b = MetaT $ state \s ->
	let r = runStateT (unMetaT b) s
	in (fmap fst r, maybe s snd $ extract r)

evalMetaT :: Monad m => MetaT t m a -> m a
evalMetaT = flip evalStateT (0, IM.empty) . unMetaT

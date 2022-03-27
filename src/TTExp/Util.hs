{-# LANGUAGE FlexibleInstances #-}

module TTExp.Util where

import Control.Monad (join)
import Control.Monad.Trans.Maybe (MaybeT(runMaybeT))
import Data.Functor.Classes (Show1(..), Eq1(..), Ord1(..))
import Data.Functor.Identity (Identity(runIdentity))

newtype Lift f a = Lift { unLift :: f a }
	deriving newtype (Functor, Show1, Eq1, Ord1)
instance (Show1 f, Show a) => Show (Lift f a) where
	showsPrec = (. unLift) . liftShowsPrec showsPrec showList
	showList = liftShowList showsPrec showList . fmap unLift
instance (Eq1 f, Eq a) => Eq (Lift f a) where
	(==) = liftEq (==)
instance (Ord1 f, Ord a) => Ord (Lift f a) where
	compare = liftCompare compare

class Functor f => AffineFunctor f where
	extract :: f a -> Maybe a
	-- f = maybe f (\a -> fmap (const a) f) (extract f)
instance AffineFunctor Maybe where
	extract = id
instance AffineFunctor Identity where
	extract = Just . runIdentity
instance AffineFunctor f => AffineFunctor (MaybeT f) where
	extract = join . extract . runMaybeT

instance MonadFail (Either String) where
	fail = Left

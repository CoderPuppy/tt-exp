module TTExp.Util where

import Data.Functor.Classes

newtype Lift f a = Lift { unLift :: f a }
	deriving newtype (Functor, Show1, Eq1)
instance (Show1 f, Show a) => Show (Lift f a) where
	showsPrec = (. unLift) . liftShowsPrec showsPrec showList
	showList = liftShowList showsPrec showList . fmap unLift
instance (Eq1 f, Eq a) => Eq (Lift f a) where
	(==) = liftEq (==)

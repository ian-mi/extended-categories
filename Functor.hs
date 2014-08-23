module Functor where

import qualified Prelude as P
import Data.Constraint
import Data.Proxy
import Data.Tagged

import Category

class (Category (Domain f :: o1 -> o1 -> *), Category (Codomain f :: o2 -> o2 -> *)) => Functor (f :: *) (k :: KProxy (o1 -> o2)) | f -> k where
    type FMap f (a :: o1) :: o2
    type Domain f :: o1 -> o1 -> *
    type Codomain f :: o2 -> o2 -> *
    morphMap :: Tagged f (Domain f (a :: o1) (b :: o1) -> Codomain f (FMap f a :: o2) (FMap f b :: o2))

objectMap :: forall f (a :: o1). Functor f ('KProxy :: KProxy (o1 -> o2)) => Tagged '(f, a) (Object (Domain f) a :- Object (Codomain f) (FMap f a :: o2))
objectMap = Tagged (Sub (case observeObjects (proxy morphMap (Proxy :: Proxy f) (id :: Domain f a a)) of Dict -> Dict))

fmap :: forall f (a :: o1) (b :: o1). Functor f ('KProxy :: KProxy (o1 -> o2)) => f -> Domain f a b -> Codomain f (FMap f a :: o2) (FMap f b :: o2)
fmap _ = proxy morphMap (Proxy :: Proxy f)

data Comp (k :: KProxy o2) (f :: *) (g :: *) where
    (:.:) :: (Functor f ('KProxy :: KProxy (o2 -> o3)), Functor g ('KProxy :: KProxy (o1 -> o2))) => f -> g -> Comp ('KProxy :: KProxy o2) f g

instance (Functor f ('KProxy :: KProxy (o2 -> o3)), Functor g ('KProxy :: KProxy (o1 -> o2)), (Domain f :: o2 -> o2 -> *) ~ Codomain g)
        => Functor (Comp ('KProxy :: KProxy o2) f g) ('KProxy :: KProxy (o1 -> o3)) where
    type FMap (Comp ('KProxy :: KProxy o2) f g) a = FMap f (FMap g a :: o2)
    type Domain (Comp 'KProxy f g) = Domain g
    type Codomain (Comp 'KProxy f g) = Codomain f
    morphMap = Tagged (proxy morphMap (Proxy :: Proxy f) . proxy morphMap (Proxy :: Proxy g))

data CanonicalF (f :: * -> *) where
    CanonicalF :: P.Functor f => CanonicalF f

instance P.Functor f => Functor (CanonicalF f) ('KProxy :: KProxy (* -> *)) where
    type FMap (CanonicalF f) a = f a
    type Domain (CanonicalF f) = (->)
    type Codomain (CanonicalF f) = (->)
    morphMap = Tagged P.fmap

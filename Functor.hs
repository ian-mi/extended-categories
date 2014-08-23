module Functor where

import qualified Prelude as P
import Data.Constraint
import Data.Proxy
import Data.Tagged

import Category

class (Category (Domain f domain), Category (Codomain f codomain)) => Functor f (domain :: KProxy o1) (codomain :: KProxy o2) | f -> domain, f -> codomain where
    type Domain f domain :: o1 -> o1 -> *
    type Codomain f codomain :: o2 -> o2 -> *
    type FMap f (a :: o1) :: o2
    morphismMap :: Tagged f (Domain f domain a b -> Codomain f codomain (FMap f a) (FMap f b))

objectMap :: forall f c1 c2 a. Functor f c1 c2 => Tagged '(f, a) (Object (Domain f c1) a :- Object (Codomain f c2) (FMap f a))
objectMap = Tagged (Sub (case observeObjects (proxy morphismMap (Proxy :: Proxy f) (id :: Domain f c1 a a)) of Dict -> Dict))

fmap :: forall f c1 c2 a b. Functor f c1 c2 => f -> Domain f c1 a b -> Codomain f c2 (FMap f a) (FMap f b)
fmap _ = proxy morphismMap (Proxy :: Proxy f)

data CompF f g c1 c2 c3 where
    (:.:) :: (Functor f c2 c3, Functor g c1 c2, Domain f c2 ~ Codomain g c2) => f -> g -> CompF f g c1 c2 c3

instance (Functor f c2 c3, Functor g c1 c2, Codomain g c2 ~ Domain f c2) => Functor (CompF f g (c1 :: KProxy o1) (c2 :: KProxy o2) (c3 :: KProxy o3)) c1 c3 where
    type Domain (CompF f g c1 c2 c3) c1 = Domain g c1
    type Codomain (CompF f g c1 c2 c3) c3 = Codomain f c3
    type FMap (CompF f g c1 c2 c3) (a :: o1) = (FMap f ((FMap g a) :: o2) :: o3)
    morphismMap = Tagged (proxy morphismMap (Proxy :: Proxy f) . proxy morphismMap (Proxy :: Proxy g))

data CanonicalF f where
    CanonicalF :: P.Functor f => CanonicalF f

instance P.Functor f => Functor (CanonicalF f) ('KProxy :: KProxy *) ('KProxy :: KProxy *) where
    type Domain (CanonicalF f) 'KProxy = (->)
    type Codomain (CanonicalF f) 'KProxy = (->)
    type FMap (CanonicalF f) a = f a
    morphismMap = Tagged P.fmap

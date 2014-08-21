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
    objectMap :: Tagged '(f, a) (Object (Domain f domain) a :- Object (Codomain f codomain) (FMap f a))
    fmap :: f -> Domain f domain a b -> Codomain f codomain (FMap f a) (FMap f b)

data CompF f g c1 c2 c3 where
    (:.:) :: (Functor f c2 c3, Functor g c1 c2, Domain f c2 ~ Codomain g c2) => f -> g -> CompF f g c1 c2 c3

instance (Functor f c2 c3, Functor g c1 c2, Codomain g c2 ~ Domain f c2) => Functor (CompF f g (c1 :: KProxy o1) (c2 :: KProxy o2) (c3 :: KProxy o3)) c1 c3 where
    type Domain (CompF f g c1 c2 c3) c1 = Domain g c1
    type Codomain (CompF f g c1 c2 c3) c3 = Codomain f c3
    type FMap (CompF f g c1 c2 c3) (a :: o1) = (FMap f ((FMap g a) :: o2) :: o3)
    objectMap :: forall a. Tagged '(CompF f g c1 c2 c3, a)
        (Object (Domain (CompF f g c1 c2 c3) c1) a :- Object (Codomain (CompF f g c1 c2 c3) c3) (FMap (CompF f g c1 c2 c3) a))
    objectMap = Tagged (proxy objectMap (Proxy :: Proxy '(f, FMap g a)) . proxy objectMap (Proxy :: Proxy '(g, a)))
    fmap (f :.: g) = fmap f . fmap g

data CanonicalF f where
    CanonicalF :: P.Functor f => CanonicalF f

instance Functor (CanonicalF f) ('KProxy :: KProxy *) ('KProxy :: KProxy *) where
    type Domain (CanonicalF f) 'KProxy = (->)
    type Codomain (CanonicalF f) 'KProxy = (->)
    type FMap (CanonicalF f) a = f a
    objectMap = Tagged (Sub Dict)
    fmap CanonicalF = P.fmap

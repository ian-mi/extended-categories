module Functor where

import qualified Prelude as P
import Data.Constraint
import Data.Proxy
import Data.Tagged

import Category

-- |The class of functors @f@ from @Domain f@ to @Codomain f@. Rather than
-- indexing functors on the type of their object mapping, Functor is indexed on
-- the phantom type variable @f@. This allows the object mapping to be any type
-- family @FMap f@, and for multiple functors to exist between categories. As a
-- consequence, a proxy @k@ for the  kind of @FMap f@ must be given as a second
-- parameter to Functor.
class (Category (Domain f :: o1 -> o1 -> *), Category (Codomain f :: o2 -> o2 -> *)) => Functor (f :: *) (k :: KProxy (o1 -> o2)) | f -> k where
    -- |The mapping of objects of @Domain f@ to objects of @Codomain f@.
    type FMap f (a :: o1) :: o2
    -- |The domain of @f@.
    type Domain f :: o1 -> o1 -> *
    -- |The codomain of @f@.
    type Codomain f :: o2 -> o2 -> *
    -- |The mapping of morphisms of @Domain f@ to morphisms of @Codomain f@, tagged on the type @f@.
    morphMap :: Tagged f (Domain f (a :: o1) (b :: o1) -> Codomain f (FMap f a :: o2) (FMap f b :: o2))

-- |Proof that functors map objects to objects. Defines a functor from Cat to (:-).
objectMap :: forall f (a :: o1). Functor f ('KProxy :: KProxy (o1 -> o2)) => Tagged '(f, a) (Object (Domain f) a :- Object (Codomain f) (FMap f a :: o2))
objectMap = Tagged (Sub (case observeObjects (proxy morphMap (Proxy :: Proxy f) (id :: Domain f a a)) of Dict -> Dict))

fmap :: forall f (a :: o1) (b :: o1). Functor f ('KProxy :: KProxy (o1 -> o2)) => f -> Domain f a b -> Codomain f (FMap f a :: o2) (FMap f b :: o2)
fmap _ = proxy morphMap (Proxy :: Proxy f)

type EndoFunctor f = (Functor f ('KProxy :: KProxy (k -> k)), (Domain f :: k -> k -> *) ~ Codomain f)

type EndoFunctorOf f (c :: k -> k -> *) = (Functor f ('KProxy :: KProxy (k -> k)), Domain f ~ c, Codomain f ~ c)

type FunctorOf f (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *) = (Functor f ('KProxy :: KProxy (o1 -> o2)), Domain f ~ c1, Codomain f ~ c2)

-- |The composition of functors. The type variable @k@ is a proxy for the kind of the objects of the codomain of @g@.
data Comp (k :: KProxy o2) (f :: *) (g :: *) where
    (:.:) :: (Functor f ('KProxy :: KProxy (o2 -> o3)), Functor g ('KProxy :: KProxy (o1 -> o2)), (Domain f :: o2 -> o2 -> *) ~ Codomain g) =>
        f -> g -> Comp ('KProxy :: KProxy o2) f g

type f :.: g = Comp ('KProxy :: KProxy *) f g

instance (Functor f ('KProxy :: KProxy (o2 -> o3)), Functor g ('KProxy :: KProxy (o1 -> o2)), (Domain f :: o2 -> o2 -> *) ~ Codomain g)
        => Functor (Comp ('KProxy :: KProxy o2) f g) ('KProxy :: KProxy (o1 -> o3)) where
    type FMap (Comp ('KProxy :: KProxy o2) f g) a = FMap f (FMap g a :: o2)
    type Domain (Comp 'KProxy f g) = Domain g
    type Codomain (Comp 'KProxy f g) = Codomain f
    morphMap = Tagged (proxy morphMap (Proxy :: Proxy f) . proxy morphMap (Proxy :: Proxy g))

-- |The identity functor.
data IdentityF c where IdentityF :: Category c => IdentityF c

type Id = IdentityF (->)

instance Category c => Functor (IdentityF (c :: k -> k -> *)) ('KProxy :: KProxy (k -> k)) where
    type Domain (IdentityF c) = c
    type Codomain (IdentityF c) = c
    type FMap (IdentityF c) (a :: k) = a
    morphMap = Tagged id

data Dual f

instance Functor f ('KProxy :: KProxy (o1 -> o2)) => Functor (Dual f) ('KProxy :: KProxy (o1 -> o2)) where
    type Domain (Dual f) = Op (Domain f)
    type Codomain (Dual f) = Op (Codomain f)
    type FMap (Dual f) a = FMap f a
    morphMap = Tagged (\(Op f) -> Op (proxy morphMap (Proxy :: Proxy f) f))

-- |Functors from Prelude.Functor
data Ftag f where Ftag :: P.Functor f => Ftag f

instance P.Functor f => Functor (Ftag f) ('KProxy :: KProxy (* -> *)) where
    type Domain (Ftag f) = (->)
    type Codomain (Ftag f) = (->)
    type FMap (Ftag f) a = f a
    morphMap = Tagged P.fmap

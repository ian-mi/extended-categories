module NaturalTransformation where

import Data.Constraint
import Data.Tagged
import Data.Proxy

import Category
import Category.Product
import Functor

data NatTr (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *) (f :: *) (g :: *) where
    NatTr :: (Object (NatTr c1 c2) f, Object (NatTr c1 c2) g) =>
        (forall (a :: o1). Object c1 a => Tagged a (c2 (FMap f a :: o2) (FMap g a :: o2))) -> NatTr (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *) f g

instance (Category c1, Category c2) => Category (NatTr (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *)) where
    type Object (NatTr c1 c2) f = (Functor f ('KProxy :: KProxy (o1 -> o2)), Domain f ~ c1, Codomain f ~ c2)
    observeObjects (NatTr _) = Dict
    id :: forall f. Object (NatTr c1 c2) f => NatTr c1 c2 f f
    id = NatTr f where
        f :: forall a. Object c1 a => Tagged a (c2 (FMap f a) (FMap f a))
        f = Tagged (id \\ proxy objectMap (Proxy :: Proxy '(f, a)))
    (.) :: forall g h f. NatTr c1 c2 g h -> NatTr c1 c2 f g -> NatTr c1 c2 f h
    NatTr f . NatTr g = NatTr h where
        h :: forall a. Object c1 a => Tagged a (c2 (FMap f a) (FMap h a))
        h = Tagged (proxy f (Proxy :: Proxy a) . proxy g (Proxy :: Proxy a))

data CompFF c1 c2 c3  where CompFF :: (Category c1, Category c2, Category c3) => CompFF c1 c2 c3

instance (Category c1, Category c2, Category c3) =>
        Functor (CompFF (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *) (c3 :: o3 -> o3 -> *)) ('KProxy :: KProxy ((*, *) -> *)) where
    type Domain (CompFF c1 c2 c3) = NatTr c2 c3 :><: NatTr c1 c2
    type Codomain (CompFF c1 c2 c3) = NatTr c1 c3
    type FMap (CompFF c1 c2 c3) '(f, g) = Comp ('KProxy :: KProxy o2) f g
    morphMap = Tagged (\(t1 :><: t2) -> compNat t1 t2)

compNat :: forall (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *) (c3 :: o3 -> o3 -> *) f1 f2 g1 g2.
    NatTr c2 c3 f1 g1 -> NatTr c1 c2 f2 g2 -> NatTr c1 c3 (Comp ('KProxy :: KProxy o2) f1 f2) (Comp ('KProxy :: KProxy o2) g1 g2)
compNat (NatTr t1) (NatTr t2) = NatTr t3 where
    t3 :: forall (a :: o1). Object c1 a => Tagged a (c3 (FMap f1 (FMap f2 a :: o2) :: o3) (FMap g1 (FMap g2 a :: o2) :: o3))
    t3 = Tagged (m1 . m2) where
        m2 = proxy morphMap (Proxy :: Proxy f1) (proxy t2 (Proxy :: Proxy a))
        m1 = proxy t1 (Proxy :: Proxy (FMap g2 a)) \\ proxy objectMap (Proxy :: Proxy '(g2, a))

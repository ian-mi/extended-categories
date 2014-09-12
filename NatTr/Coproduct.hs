module NatTr.Coproduct where

import Data.Constraint hiding ((&&&))
import Data.Tagged
import Data.Proxy

import Category
import Category.Product
import Functor
import Functor.Product
import Product
import Coproduct
import Universal
import NatTr

instance (Category c1, CoproductCategory c2, FunctorOf f c1 c2, FunctorOf g c1 c2) =>
        InitialMorphism (Diag (NatTr c1 (c2 :: o2 -> o2 -> *))) (Comp ('KProxy :: KProxy (o2, o2)) (CoproductF c2) (f :&&&: g)) '(f, g) where
    initialMorphism = Tagged (NatTr l :><: NatTr r) where
        l :: forall a. Object c1 a => Tagged a (c2 (FMap f a) (Coproduct c2 (FMap f a) (FMap g a)))
        l = Tagged (proxy inj1 (Proxy :: Proxy (FMap g a))) \\ proxy objectMap (Proxy :: Proxy '(f, a)) &&& proxy objectMap (Proxy :: Proxy '(g, a))
        r :: forall a. Object c1 a => Tagged a (c2 (FMap g a) (Coproduct c2 (FMap f a) (FMap g a)))
        r = Tagged (proxy inj2 (Proxy :: Proxy (FMap f a))) \\ proxy objectMap (Proxy :: Proxy '(f, a)) &&& proxy objectMap (Proxy :: Proxy '(g, a))
    initialFactorization = Tagged fac where
        fac :: forall h. FunctorOf h c1 c2 =>
            (NatTr c1 c2 :><: NatTr c1 c2) '(f, g) '(h, h) -> NatTr c1 c2 (Comp ('KProxy :: KProxy (o2, o2)) (CoproductF c2) (f :&&&: g)) h
        fac (NatTr l :><: NatTr r) = NatTr t where
            t :: forall a. Object c1 a => Tagged a (c2 (Coproduct c2 (FMap f a) (FMap g a)) (FMap h a))
            t = Tagged (coproduct (proxy l (Proxy :: Proxy a)) (proxy r (Proxy :: Proxy a)))

instance (Category c1, CoproductCategory c2) => CoproductCategory (NatTr c1 (c2 :: o2 -> o2 -> *)) where
    type Coproduct (NatTr c1 c2) f g = Comp ('KProxy :: KProxy (o2, o2)) (CoproductF c2) (f :&&&: g)
    univCoproduct = Tagged (Sub Dict)

type f :+: g = Coproduct (NatTr (->) (->)) f g

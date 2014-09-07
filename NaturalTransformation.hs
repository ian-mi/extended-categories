module NaturalTransformation where

import Data.Constraint hiding ((&&&))
import Data.Tagged
import Data.Proxy

import Category
import Category.Product
import Functor
import Functor.Product
import Product
import Coproduct
import Monoidal
import Universal

data NatTr (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *) (f :: *) (g :: *) where
    NatTr :: (Object (NatTr c1 c2) f, Object (NatTr c1 c2) g) =>
        (forall (a :: o1). Object c1 a => Tagged a (c2 (FMap f a :: o2) (FMap g a :: o2))) -> NatTr (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *) f g

instance (Category c1, Category c2) => Category (NatTr (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *)) where
    type Object (NatTr c1 c2) f = FunctorOf f c1 c2
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

instance Category c => Monoidal (NatTr c c) (CompFF c c c) where
    type I (CompFF c c c) = IdentityF c

instance (Category c1, ProductCategory (c2 :: o2 -> o2 -> *), FunctorOf f c1 c2, FunctorOf g c1 c2) =>
        TerminalMorphism (Diag (NatTr c1 c2)) (Comp ('KProxy :: KProxy (o2, o2)) (ProductF c2) (f :&&&: g)) '(f, g) where
    terminalMorphism = Tagged (NatTr l :><: NatTr r) where
        l :: forall a. Object c1 a => Tagged a (c2 (Product c2 (FMap f a) (FMap g a)) (FMap f a))
        l = Tagged (proxy proj1 (Proxy :: Proxy (FMap g a))) \\ (proxy objectMap (Proxy :: Proxy '(f, a)) &&& proxy objectMap (Proxy :: Proxy '(g, a)))
        r :: forall a. Object c1 a => Tagged a (c2 (Product c2 (FMap f a) (FMap g a)) (FMap g a))
        r = Tagged (proxy proj2 (Proxy :: Proxy (FMap f a))) \\ (proxy objectMap (Proxy :: Proxy '(f, a)) &&& proxy objectMap (Proxy :: Proxy '(g, a)))
    terminalFactorization = Tagged fac where
        fac :: forall h. FunctorOf h c1 c2 =>
            (NatTr c1 c2 :><: NatTr c1 c2) '(h, h) '(f, g) -> NatTr c1 c2 h (Comp ('KProxy :: KProxy (o2, o2)) (ProductF c2) (f :&&&: g))
        fac (NatTr l :><: NatTr r) = NatTr t where
            t :: forall a. Object c1 a => Tagged a (c2 (FMap h a) (Product c2 (FMap f a) (FMap g a)))
            t = Tagged (proxy l (Proxy :: Proxy a) &&& proxy r (Proxy :: Proxy a))

instance (Category c1, ProductCategory c2) => ProductCategory (NatTr c1 (c2 :: o2 -> o2 -> *)) where
    type Product (NatTr c1 c2) f g = Comp ('KProxy :: KProxy (o2, o2)) (ProductF c2) (f :&&&: g)
    univProduct = Tagged (Sub Dict)

type f :*: g = Product (NatTr (->) (->)) f g

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

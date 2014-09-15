module NatTr where

import Data.Constraint hiding ((&&&))
import Data.Tagged
import Data.Proxy

import Category
import Category.Product
import Functor

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

(<.>) :: (Functor f ('KProxy :: KProxy (o3 -> o4)), Functor g ('KProxy :: KProxy (o1 -> o2))) =>
    f -> g -> NatTr (Codomain g :: o2 -> o2 -> *) (Domain f :: o3 -> o3 -> *) h1 h2 ->
    NatTr (Domain g :: o1 -> o1 -> *) (Codomain f :: o4 -> o4 -> *)
        (Comp ('KProxy :: KProxy o3) f (Comp ('KProxy :: KProxy o2) h1 g))
        (Comp ('KProxy :: KProxy o3) f (Comp ('KProxy :: KProxy o2) h2 g))
f <.> g = compFL . compFR

compFL :: forall c1 c2 f h g. (Category c1, Functor h ('KProxy :: KProxy (o2 -> o3)), Domain h ~ c2) =>
    NatTr c1 (c2 :: o2 -> o2 -> *) f g -> NatTr c1 (Codomain h :: o3 -> o3 -> *) (Comp ('KProxy :: KProxy o2) h f) (Comp ('KProxy :: KProxy o2) h g)
compFL t | Dict <- observeObjects t = NatTr t' where
    t' :: forall a. Object c1 a => Tagged a (Codomain h (FMap h (FMap f a :: o2) :: o3) (FMap h (FMap g a :: o2)))
    t' = Tagged (proxy morphMap (Proxy :: Proxy (Comp ('KProxy :: KProxy o2) h (AppNat a c1 c2))) t)

compFR :: forall c2 c3 f h g. (Category c3, Functor h ('KProxy :: KProxy (o1 -> o2)), Codomain h ~ c2) =>
    NatTr (c2 :: o2 -> o2 -> *) c3 f g -> NatTr (Domain h :: o1 -> o1 -> *) c3 (Comp ('KProxy :: KProxy o2) f h) (Comp ('KProxy :: KProxy o2) g h)
compFR t | Dict <- observeObjects t = NatTr t' where
    t' :: forall (a :: o1). Object (Domain h) a => Tagged a (c3 (FMap f (FMap h a :: o2)) (FMap g (FMap h a :: o2)))
    t' = Tagged (proxy morphMap (Proxy :: Proxy (AppNat (FMap h a) c2 c3)) t \\ proxy objectMap (Proxy :: Proxy '(h, a)))

data AppNat a c1 c2 where AppNat :: (Category c1, Category c2, Object c1 a) => AppNat a c1 c2

instance (Category c1, Category c2, Object c1 a) => Functor (AppNat (a :: o1) (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *)) ('KProxy :: KProxy (* -> o2)) where
    type Domain (AppNat a c1 c2) = NatTr c1 c2
    type Codomain (AppNat a c1 c2) = c2
    type FMap (AppNat a c1 c2) f = (FMap f a :: o2)
    morphMap = Tagged (\(NatTr t) -> proxy t (Proxy :: Proxy a))

idL :: forall f. Functor f ('KProxy :: KProxy (o1 -> o2)) =>
    NatTr (Domain f :: o1 -> o1 -> *) (Codomain f :: o2 -> o2 -> *) (Comp ('KProxy :: KProxy o2) (IdentityF (Codomain f :: o2 -> o2 -> *)) f) f
idL = NatTr t where
    t :: forall (a :: o1). Object (Domain f) a => Tagged a (Codomain f (FMap f a :: o2) (FMap f a :: o2))
    t = Tagged (id \\ proxy objectMap (Proxy :: Proxy '(f, a)))

idLInv :: forall f. Functor f ('KProxy :: KProxy (o1 -> o2)) =>
    NatTr (Domain f :: o1 -> o1 -> *) (Codomain f :: o2 -> o2 -> *) f (Comp ('KProxy :: KProxy o2) (IdentityF (Codomain f :: o2 -> o2 -> *)) f)
idLInv = NatTr t where
    t :: forall (a :: o1). Object (Domain f) a => Tagged a (Codomain f (FMap f a :: o2) (FMap f a :: o2))
    t = Tagged (id \\ proxy objectMap (Proxy :: Proxy '(f, a)))

idR :: forall f. Functor f ('KProxy :: KProxy (o1 -> o2)) =>
    NatTr (Domain f :: o1 -> o1 -> *) (Codomain f :: o2 -> o2 -> *) (Comp ('KProxy :: KProxy o1) f (IdentityF (Domain f :: o1 -> o1 -> *))) f
idR = NatTr t where
    t :: forall (a :: o1). Object (Domain f) a => Tagged a (Codomain f (FMap f a :: o2) (FMap f a :: o2))
    t = Tagged (id \\ proxy objectMap (Proxy :: Proxy '(f, a)))

idRInv :: forall f. Functor f ('KProxy :: KProxy (o1 -> o2)) =>
    NatTr (Domain f :: o1 -> o1 -> *) (Codomain f :: o2 -> o2 -> *) f (Comp ('KProxy :: KProxy o1) f (IdentityF (Domain f :: o1 -> o1 -> *)))
idRInv = NatTr t where
    t :: forall (a :: o1). Object (Domain f) a => Tagged a (Codomain f (FMap f a :: o2) (FMap f a :: o2))
    t = Tagged (id \\ proxy objectMap (Proxy :: Proxy '(f, a)))

assocL :: forall f g h.
    (Functor f ('KProxy :: KProxy (o3 -> o4)), Functor g ('KProxy :: KProxy (o2 -> o3)), Functor h ('KProxy :: KProxy (o1 -> o2)),
    (Domain f :: o3 -> o3 -> *) ~ Codomain g, (Domain g :: o2 -> o2 -> *) ~ Codomain h) =>
        NatTr (Domain h :: o1 -> o1 -> *) (Codomain f :: o4 -> o4 -> *)
            (Comp ('KProxy :: KProxy o3) f (Comp ('KProxy :: KProxy o2) g h))
            (Comp ('KProxy :: KProxy o2) (Comp ('KProxy :: KProxy o3) f g) h)
assocL = NatTr t where
    t :: forall (a :: o1). Object (Domain h) a => Tagged a (Codomain f (FMap f (FMap g (FMap h a :: o2) :: o3) :: o4) (FMap f (FMap g (FMap h a :: o2) :: o3) :: o4))
    t = Tagged (id \\
                    proxy objectMap (Proxy :: Proxy '(f, (FMap g (FMap h a :: o2) :: o3))) .
                    proxy objectMap (Proxy :: Proxy '(g, (FMap h a :: o2))) .
                    proxy objectMap (Proxy :: Proxy '(h, a)))

assocR :: forall f g h.
    (Functor f ('KProxy :: KProxy (o3 -> o4)), Functor g ('KProxy :: KProxy (o2 -> o3)), Functor h ('KProxy :: KProxy (o1 -> o2)),
    (Domain f :: o3 -> o3 -> *) ~ Codomain g, (Domain g :: o2 -> o2 -> *) ~ Codomain h) =>
        NatTr (Domain h :: o1 -> o1 -> *) (Codomain f :: o4 -> o4 -> *)
            (Comp ('KProxy :: KProxy o2) (Comp ('KProxy :: KProxy o3) f g) h)
            (Comp ('KProxy :: KProxy o3) f (Comp ('KProxy :: KProxy o2) g h))
assocR = NatTr t where
    t :: forall (a :: o1). Object (Domain h) a => Tagged a (Codomain f (FMap f (FMap g (FMap h a :: o2) :: o3) :: o4) (FMap f (FMap g (FMap h a :: o2) :: o3) :: o4))
    t = Tagged (id \\
                    proxy objectMap (Proxy :: Proxy '(f, (FMap g (FMap h a :: o2) :: o3))) .
                    proxy objectMap (Proxy :: Proxy '(g, (FMap h a :: o2))) .
                    proxy objectMap (Proxy :: Proxy '(h, a)))

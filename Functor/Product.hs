module Functor.Product where

import Data.Constraint
import Data.Proxy
import Data.Tagged

import Category
import Category.Product
import Functor
import NatTr

data f :&&&: g

instance (Functor f ('KProxy :: KProxy (o -> o1)), Functor g ('KProxy :: KProxy (o -> o2)), (Domain f :: o -> o -> *) ~ Domain g) =>
        Functor (f :&&&: g) ('KProxy :: KProxy (o -> (o1, o2))) where
    type Domain (f :&&&: g) = Domain f
    type Codomain (f :&&&: g) = Codomain f :><: Codomain g
    type FMap (f :&&&: g) a = '(FMap f a, FMap g a)
    morphMap = Tagged (\t -> proxy morphMap (Proxy :: Proxy f) t :><: proxy morphMap (Proxy :: Proxy g) t)

data Proj1 (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *) where
    Proj1 :: (Category c1, Category c2) => Proj1 c1 c2

instance (Category c1, Category c2) => Functor (Proj1 (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *)) ('KProxy :: KProxy ((o1, o2) -> o1)) where
    type Domain (Proj1 c1 c2) = c1 :><: c2
    type Codomain (Proj1 c1 c2) = c1
    type FMap (Proj1 c1 c2) '((a :: o1), (b :: o2)) = a
    morphMap = Tagged (\(f :><: _) -> f)

data Proj2 (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *) where
    Proj2 :: (Category c1, Category c2) => Proj2 c1 c2

instance (Category c1, Category c2) => Functor (Proj2 (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *)) ('KProxy :: KProxy ((o1, o2) -> o2)) where
    type Domain (Proj2 c1 c2) = c1 :><: c2
    type Codomain (Proj2 c1 c2) = c2
    type FMap (Proj2 c1 c2) '((a :: o1), (b :: o2)) = b
    morphMap = Tagged (\(_ :><: g) -> g)

proj1F :: forall c c1 c2 f g.  (FunctorOf f c c1, FunctorOf g c c2) =>
    NatTr c c1 (Comp ('KProxy :: KProxy (o1, o2)) (Proj1 (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *)) (f :&&&: g)) f
proj1F = NatTr t where
    t :: forall a. Object c a => Tagged a (c1 (FMap f a) (FMap f a))
    t = Tagged id \\ proxy objectMap (Proxy :: Proxy '(f, a))

proj2F :: forall c c1 c2 f g.  (FunctorOf f c c1, FunctorOf g c c2) =>
    NatTr c c2 (Comp ('KProxy :: KProxy (o1, o2)) (Proj2 (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *)) (f :&&&: g)) g
proj2F = NatTr t where
    t :: forall a. Object c a => Tagged a (c2 (FMap g a) (FMap g a))
    t = Tagged id \\ proxy objectMap (Proxy :: Proxy '(g, a))

proj1FInv :: forall c c1 c2 f g.  (FunctorOf f c c1, FunctorOf g c c2) =>
    NatTr c c1 f (Comp ('KProxy :: KProxy (o1, o2)) (Proj1 (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *)) (f :&&&: g))
proj1FInv = NatTr t where
    t :: forall a. Object c a => Tagged a (c1 (FMap f a) (FMap f a))
    t = Tagged id \\ proxy objectMap (Proxy :: Proxy '(f, a))

proj2FInv :: forall c c1 c2 f g.  (FunctorOf f c c1, FunctorOf g c c2) =>
    NatTr c c2 g (Comp ('KProxy :: KProxy (o1, o2)) (Proj2 (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *)) (f :&&&: g))
proj2FInv = NatTr t where
    t :: forall a. Object c a => Tagged a (c2 (FMap g a) (FMap g a))
    t = Tagged id \\ proxy objectMap (Proxy :: Proxy '(g, a))

productNat :: forall (c :: o -> o -> *) c1 c2 f1 g1 f2 g2. NatTr c c1 f1 g1 -> NatTr c c2 f2 g2 -> NatTr c (c1 :><: c2) (f1 :&&&: f2) (g1 :&&&: g2)
productNat (NatTr t1) (NatTr t2) = NatTr t where
    t :: forall (a :: o). Object c a => Tagged a ((c1 :><: c2) '(FMap f1 a, FMap f2 a) '(FMap g1 a, FMap g2 a))
    t = Tagged (proxy t1 (Proxy :: Proxy a) :><: proxy t2 (Proxy :: Proxy a))

data f :***: g

instance (Functor f ('KProxy :: KProxy (o1 -> o2)), Functor g ('KProxy :: KProxy (o3 -> o4))) => Functor (f :***: g) ('KProxy :: KProxy ((o1, o3) -> (o2, o4))) where
    type Domain (f :***: g) = Domain f :><: Domain g
    type Codomain (f :***: g) = Codomain f :><: Codomain g
    type FMap (f :***: g) '((a :: o1), (b :: o2)) = '(FMap f a, FMap g b)
    morphMap = Tagged (\(f :><: g) -> proxy morphMap (Proxy :: Proxy f) f :><: proxy morphMap (Proxy :: Proxy g) g)

data Diag c where Diag :: Category c => Diag c

instance Category c => Functor (Diag (c :: k -> k -> *)) ('KProxy :: KProxy (k -> (k, k))) where
    type Domain (Diag c) = c
    type Codomain (Diag c) = c :><: c
    type FMap (Diag c) (a :: k) = '(a, a)
    morphMap = Tagged (\f -> f :><: f)

retractProj1 :: Category (c :: o -> o -> *) => NatTr c c (Comp ('KProxy :: KProxy (o, o)) (Proj1 c c) (Diag c)) (IdentityF c)
retractProj1 = NatTr (Tagged id)

retractProj1Inv :: Category (c :: o -> o -> *) => NatTr c c (IdentityF c) (Comp ('KProxy :: KProxy (o, o)) (Proj1 c c) (Diag c))
retractProj1Inv = NatTr (Tagged id)

retractProj2 :: Category (c :: o -> o -> *) => NatTr c c (Comp ('KProxy :: KProxy (o, o)) (Proj2 c c) (Diag c)) (IdentityF c)
retractProj2 = NatTr (Tagged id)

retractProj2Inv :: Category (c :: o -> o -> *) => NatTr c c (IdentityF c) (Comp ('KProxy :: KProxy (o, o)) (Proj2 c c) (Diag c))
retractProj2Inv = NatTr (Tagged id)

diag :: forall c1 c2 f. (Category (c2 :: o2 -> o2 -> *), FunctorOf f c1 c2)  => NatTr c1 (c2 :><: c2) (Comp ('KProxy :: KProxy o2) (Diag c2) f) (f :&&&: f)
diag = NatTr t where
    t :: forall a. Object c1 a => Tagged a ((c2 :><: c2) '(FMap f a, FMap f a) '(FMap f a, FMap f a))
    t = Tagged id \\ proxy objectMap (Proxy :: Proxy '(f :&&&: f, a))

diagInv :: forall c1 c2 f. (Category (c2 :: o2 -> o2 -> *), FunctorOf f c1 c2)  => NatTr c1 (c2 :><: c2) (f :&&&: f) (Comp ('KProxy :: KProxy o2) (Diag c2) f)
diagInv = NatTr t where
    t :: forall a. Object c1 a => Tagged a ((c2 :><: c2) '(FMap f a, FMap f a) '(FMap f a, FMap f a))
    t = Tagged id \\ proxy objectMap (Proxy :: Proxy '(f :&&&: f, a))

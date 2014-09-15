module Functor.Product where

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

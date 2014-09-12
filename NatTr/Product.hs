module NatTr.Product where

import qualified Prelude as P
import Data.Constraint hiding ((&&&))
import Data.Tagged
import Data.Proxy

import Category
import Category.Product
import Functor
import Functor.Product
import Product
import NatTr
import Adjoint

instance (Category c1, ProductCategory c2) => Functor (ProductF (NatTr c1 (c2 :: o2 -> o2 -> *))) ('KProxy :: KProxy ((*, *) -> *)) where
    type Domain (ProductF (NatTr c1 c2)) = NatTr c1 c2 :><: NatTr c1 c2
    type Codomain (ProductF (NatTr c1 c2)) = NatTr c1 c2
    type FMap (ProductF (NatTr c1 c2)) '((f :: *), (g :: *)) = Comp ('KProxy :: KProxy (o2, o2)) (ProductF c2) (f :&&&: g)
    morphMap = Tagged (\t@(f :><: g) -> case observeObjects t of Dict -> let (l, r) = proj in (f . l) &&& (g . r))

instance (Category c1, ProductCategory c2) =>
        Adjoint (NatTr c1 c2) (NatTr (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *) :><: NatTr c1 c2) (Diag (NatTr c1 c2)) (ProductF (NatTr c1 c2)) where
    leftAdjunct = NatTr (Tagged (\(s :><: t) -> NatTr (f s t))) where
        f :: forall (a :: o1) f g h. (Object c1 a, FunctorOf f c1 c2, FunctorOf g c1 c2, FunctorOf h c1 c2) =>
            NatTr c1 c2 f g -> NatTr c1 c2 f h -> Tagged a (c2 (FMap f a) (Product c2 (FMap g a :: o2) (FMap h a :: o2)))
        f s t = Tagged (proxy morphMap (Proxy :: Proxy (AppNat a c1 c2)) s &&& proxy morphMap (Proxy :: Proxy (AppNat a c1 c2)) t)
    rightAdjunct = NatTr (Tagged (\t -> f t)) where
        f :: forall f g h. (FunctorOf f c1 c2, FunctorOf g c1 c2, FunctorOf h c1 c2) =>
                NatTr c1 c2 f (Comp ('KProxy :: KProxy (o2, o2)) (ProductF c2) (g :&&&: h)) -> (NatTr c1 c2 :><: NatTr c1 c2) '(f, f) '(g, h)
        f t = (NatTr p1 . t) :><: (NatTr p2 . t) where
            NatTr p1 = compNat proj1 i
            NatTr p2 = compNat proj2 i
            i :: NatTr c1 (c2 :><: c2) (g :&&&: h) (g :&&&: h)
            i = id

instance (Category c1, ProductCategory c2) => ProductCategory (NatTr c1 c2)

type f :*: g = Product (NatTr (->) (->)) f g

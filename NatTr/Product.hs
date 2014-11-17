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
    morphMap = Tagged (\t@(f :><: g) -> case observeObjects t of Dict -> (f . appNat proj1) &&& (g . appNat proj2))

instance (Category c1, ProductCategory c2) =>
        Adjoint (NatTr c1 c2) (NatTr (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *) :><: NatTr c1 c2) (Diag (NatTr c1 c2)) (ProductF (NatTr c1 c2)) where
    leftAdjunct = NatTr (Tagged (\(s :><: t) -> compFL (productNat s t . diag) . assocR . compFR unit . idLInv))
    rightAdjunct = NatTr (Tagged (\t -> (proj1F . compFR proj1 . t) :><: (proj2F . compFR proj2 . t)))

instance (Category c1, ProductCategory c2) => ProductCategory (NatTr c1 c2)

type f :*: g = Product (NatTr (->) (->)) f g

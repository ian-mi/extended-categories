module NatTr.Coproduct where

import Data.Constraint hiding ((&&&))
import Data.Tagged
import Data.Proxy

import Adjoint
import Category
import Category.Product
import Functor
import Functor.Product
import Product
import Coproduct
import NatTr

instance (Category c1, CoproductCategory c2) => Functor (CoproductF (NatTr c1 (c2 :: o2 -> o2 -> *))) ('KProxy :: KProxy ((*, *) -> *)) where
    type Domain (CoproductF (NatTr c1 c2)) = NatTr c1 c2 :><: NatTr c1 c2
    type Codomain (CoproductF (NatTr c1 c2)) = NatTr c1 c2
    type FMap (CoproductF (NatTr c1 c2)) '((f :: *), (g :: *)) = Comp ('KProxy :: KProxy (o2, o2)) (CoproductF c2) (f :&&&: g)
    morphMap = (Tagged (\t@(f :><: g) -> case observeObjects t of Dict -> coproduct (appNat inj1 . f) (appNat inj2 . g)))

instance (Category c1, CoproductCategory c2) =>
    Adjoint (NatTr c1 c2 :><: NatTr c1 c2) (NatTr (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *)) (CoproductF (NatTr c1 c2)) (Diag (NatTr c1 c2)) where
    leftAdjunct = NatTr (Tagged (\t -> (t . compFR inj1 . proj1FInv) :><: (t . compFR inj2 . proj2FInv)))
    rightAdjunct = NatTr (Tagged (\(t1 :><: t2) -> idL . compFR counit . assocL . compFL (diagInv . productNat t1 t2)))

instance (Category c1, CoproductCategory c2) => CoproductCategory (NatTr c1 c2)

type f :+: g = Coproduct (NatTr (->) (->)) f g

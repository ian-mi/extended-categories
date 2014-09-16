module Product where

import qualified Prelude as P
import Data.Constraint hiding ((***), (&&&))
import Data.Proxy
import Data.Tagged

import Category
import Category.Product
import Functor
import Functor.Product
import NatTr
import Adjoint
import Terminal
import Universal
import Monoidal

data ProductF (c :: o -> o -> *)
class Adjoint c (c :><: c) (Diag c) (ProductF c) => ProductCategory c
type Product c a b = FMap (ProductF c) '(a, b)

proj1 :: forall (c :: o -> o -> *). ProductCategory c => NatTr (c :><: c) c (ProductF c) (Proj1 c c)
proj1 = idR . compFL counit . assocR . compFR retractProj1Inv . idLInv

proj2 :: forall (c :: o -> o -> *). ProductCategory c => NatTr (c :><: c) c (ProductF c) (Proj2 c c)
proj2 = idR . compFL counit . assocR . compFR retractProj2Inv . idLInv

(&&&) :: forall c a b1 b2. ProductCategory c => c a b1 -> c a b2 -> c a (Product c b1 b2)
f &&& g | Dict <- observeObjects f = proxy phiL (Proxy :: Proxy '(Diag c, ProductF c)) (f :><: g)

(***) :: forall c a1 a2 b1 b2. ProductCategory c => c a1 b1 -> c a2 b2 -> c (Product c a1 a2) (Product c b1 b2)
f *** g = proxy morphMap (Proxy :: Proxy (ProductF c)) (f :><: g)

instance (ProductCategory c, Terminal c) => Monoidal c (ProductF c) where
    type I (ProductF c) = T c

instance Functor (ProductF (->)) ('KProxy :: KProxy ((*,*) -> *)) where
    type Domain (ProductF (->)) = (->) :><: (->)
    type Codomain (ProductF (->)) = (->)
    type FMap (ProductF (->)) '(a, b) = (a, b)
    morphMap = Tagged (\(f :><: g) -> (f . appNat proj1) &&& (g . appNat proj2))

instance Adjoint (->) ((->) :><: (->)) (Diag (->)) (ProductF (->)) where
    leftAdjunct = NatTr (Tagged (\(f :><: g) z -> (f z, g z)))
    rightAdjunct = NatTr (Tagged (\f -> (P.fst . f) :><: (P.snd . f)))

instance ProductCategory (->)

instance Functor (ProductF (:-)) ('KProxy :: KProxy ((Constraint, Constraint) -> Constraint)) where
    type Domain (ProductF (:-)) = (:-) :><: (:-)
    type Codomain (ProductF (:-)) = (:-)
    type FMap (ProductF (:-)) '((a :: Constraint), (b :: Constraint)) = ((a, b) :: Constraint)
    morphMap = Tagged (\(f :><: g) -> (f . appNat proj1) &&& (g . appNat proj2))

instance Adjoint (:-) ((:-) :><: (:-)) (Diag (:-)) (ProductF (:-)) where
    leftAdjunct = NatTr (Tagged (\(f :><: g) -> Sub (Dict \\ f \\ g)))
    rightAdjunct = NatTr (Tagged (\f -> (Sub (Dict \\ f) :><: Sub (Dict \\ f))))

instance ProductCategory (:-)

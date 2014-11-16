module Coproduct where

import qualified Prelude as P
import Data.Constraint
import Data.Tagged
import Data.Proxy

import Adjoint
import Category
import Category.Product
import Functor
import Functor.Product
import NatTr

data CoproductF (c :: o -> o -> *) where CoproductF :: CoproductCategory c => CoproductF c
class Adjoint (c :><: c) c (CoproductF c) (Diag c) => CoproductCategory c
type Coproduct c a b = FMap (CoproductF c) '(a, b)

inj1 :: CoproductCategory c => NatTr (c :><: c) c (Proj1 c c) (CoproductF c)
inj1 = idL . compFR retractProj1 . assocL .  compFL unit . idRInv

inj2 :: CoproductCategory c => NatTr (c :><: c) c (Proj2 c c) (CoproductF c)
inj2 = idL . compFR retractProj2 . assocL .  compFL unit . idRInv

coproduct :: forall c x y z. CoproductCategory c => c x z -> c y z -> c (Coproduct c x y) z
coproduct f g | Dict <- observeObjects g = proxy phiR (Proxy :: Proxy '(CoproductF c, Diag c)) (f :><: g)

instance Functor (CoproductF (->)) ('KProxy :: KProxy ((*, *) -> *)) where
    type Domain (CoproductF (->)) = (->) :><: (->)
    type Codomain (CoproductF (->)) = (->)
    type FMap (CoproductF (->)) '(a, b) = P.Either a b
    morphMap = (Tagged (\(f :><: g) -> coproduct (appNat inj1 . f) (appNat inj2 . g)))

instance Adjoint ((->) :><: (->)) (->) (CoproductF (->)) (Diag (->)) where
    leftAdjunct = NatTr (Tagged (\f -> (f . P.Left) :><: (f . P.Right)))
    rightAdjunct = NatTr (Tagged (\(f :><: g) -> P.either f g))

instance CoproductCategory (->)

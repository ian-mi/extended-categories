module Coproduct where

import qualified Prelude as P
import Data.Constraint
import Data.Tagged
import Data.Proxy

import Category
import Category.Product
import Functor
import Universal

class Category c => CoproductCategory (c :: o -> o -> *) where
    type Coproduct c (a :: o) (b :: o) :: o
    univCoproduct :: Tagged '(c, a, b) ((Object c a, Object c b) :- InitialMorphism (Diag c) (Coproduct c a b) '(a, b))

inj :: forall c a b. (CoproductCategory c, Object c a, Object c b) => (c a (Coproduct c a b), c b (Coproduct c a b))
inj = (l, r) where
    l :><: r = m
    m :: (c :><: c) '(a, b) '(Coproduct c a b, Coproduct c a b)
    m = proxy initialMorphism (Proxy :: Proxy '(Diag c, Coproduct c a b)) \\ proxy univCoproduct (Proxy :: Proxy '(c, a, b))

inj1 :: forall c a b. (CoproductCategory c, Object c a, Object c b) => Tagged b (c a (Coproduct c a b))
inj1 = Tagged l where
    l :><: _ = m
    m :: (c :><: c) '(a, b) '(Coproduct c a b, Coproduct c a b)
    m = proxy initialMorphism (Proxy :: Proxy '(Diag c, Coproduct c a b)) \\ proxy univCoproduct (Proxy :: Proxy '(c, a, b))

inj2 :: forall c a b. (CoproductCategory c, Object c a, Object c b) => Tagged a (c b (Coproduct c a b))
inj2 = Tagged r where
    _ :><: r = m
    m :: (c :><: c) '(a, b) '(Coproduct c a b, Coproduct c a b)
    m = proxy initialMorphism (Proxy :: Proxy '(Diag c, Coproduct c a b)) \\ proxy univCoproduct (Proxy :: Proxy '(c, a, b))

coproduct :: forall c x y z. CoproductCategory c => c x z -> c y z -> c (Coproduct c x y) z
coproduct f g
    | Dict <- observeObjects f, Dict <- observeObjects g =
        proxy initialFactorization (Proxy :: Proxy (Diag c)) (f :><: g) \\ proxy univCoproduct (Proxy :: Proxy '(c, x, y))

coproductMap :: CoproductCategory c => c a1 b1 -> c a2 b2 -> c (Coproduct c a1 a2) (Coproduct c b1 b2)
coproductMap f g
    | Dict <- observeObjects f, Dict <- observeObjects g = let (l, r) = inj in coproduct (l . f) (r . g)

data CoproductF (c :: o -> o -> *)

instance CoproductCategory c => Functor (CoproductF (c :: o -> o -> *)) ('KProxy :: KProxy ((o, o) -> o)) where
    type Domain (CoproductF c) = c :><: c
    type Codomain (CoproductF c) = c
    type FMap (CoproductF c) '(a, b) = Coproduct c a b
    morphMap = Tagged (\(f :><: g) -> coproductMap f g)

instance InitialMorphism (Diag (->)) (P.Either a b) '(a, b) where
    initialMorphism = Tagged (P.Left :><: P.Right)
    initialFactorization = Tagged (\(f :><: g) -> P.either f g)

instance CoproductCategory (->) where
    type Coproduct (->) a b = P.Either a b
    univCoproduct = Tagged (Sub Dict)

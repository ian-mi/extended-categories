module Product where

import qualified Prelude as P
import Data.Constraint hiding ((***), (&&&))
import Data.Proxy
import Data.Tagged

import Category
import Functor
import TerminalMorphism

data (c1 :><: c2) a b where
    (:><:) :: (a ~ '(L a, R a), b ~ '(L b, R b))  => c1 (L a) (L b) -> c2 (R a) (R b) -> (c1 :><: c2) a b

type family L t where L '(a, b) = a
type family R t where R '(a, b) = b

instance (Category c1, Category c2) => Category (c1 :><: c2) where
    type Object (c1 :><: c2) a = (Object c1 (L a), Object c2 (R a), a ~ '(L a, R a))
    id = id :><: id
    observeObjects (f :><: g)
        | Dict <- observeObjects f, Dict <- observeObjects g = Dict
    (f1 :><: f2) . (g1 :><: g2) = (f1 . g1) :><: (f2 . g2)

data Diag c where Diag :: Category c => Diag c

instance Category c => Functor (Diag (c :: k -> k -> *)) ('KProxy :: KProxy k) ('KProxy :: KProxy (k, k)) where
    type Domain (Diag c) 'KProxy = c
    type Codomain (Diag c) 'KProxy = c :><: c
    type FMap (Diag c) (a :: k) = '(a, a)
    objectMap Diag = Tagged (Sub Dict)
    fmap Diag f = f :><: f

class Category c => ProductCategory (c :: k -> k -> *) where
    type (><) (a :: k) (b :: k) :: k
    productObjectMap :: Tagged '(c, a, b) ((Object c a, Object c b) :- Object c (a >< b))
    univProduct :: forall (a :: k) (b :: k). Tagged '(c, a, b) ((Object c a, Object c b) :- TerminalMorphism (Diag c) (a >< b) '(a, b) 'KProxy 'KProxy)

proj1 :: forall a b c. (ProductCategory c, Object c a, Object c b) => Tagged b (c (a >< b) a)
proj1 = Tagged p where
    p :><: _ = t
    t :: (c :><: c) '(a >< b, a >< b) '(a, b)
    t = proxy terminalMorphism (Proxy :: Proxy '(Diag c, a >< b)) \\ proxy univProduct (Proxy :: Proxy '(c, a, b))

proj2 :: forall a b c. (ProductCategory c, Object c a, Object c b) => Tagged a (c (a >< b) b)
proj2 = Tagged p where
    _ :><: p = t
    t :: (c :><: c) '(a >< b, a >< b) '(a, b)
    t = proxy terminalMorphism (Proxy :: Proxy '(Diag c, a >< b)) \\ proxy univProduct (Proxy :: Proxy '(c, a, b))

(&&&) :: forall c a b1 b2. ProductCategory c => c a b1 -> c a b2 -> c a (b1 >< b2)
f &&& g
    | Dict <- observeObjects f, Dict <- observeObjects g
        = proxy terminalFactorization (Proxy :: Proxy (Diag c)) (f :><: g) \\ proxy univProduct (Proxy :: Proxy '(c, b1, b2))

(***) :: forall c a1 a2 b1 b2. ProductCategory c => c a1 b1 -> c a2 b2 -> c (a1 >< a2) (b1 >< b2)
f *** g
    | Dict <- observeObjects f, Dict <- observeObjects g
        = (f . (proxy proj1 (Proxy :: Proxy a2))) &&& (g . (proxy proj2 (Proxy :: Proxy a1)))

data ProductF c where ProductF :: ProductCategory c => ProductF c

instance ProductCategory (c :: k -> k -> *) => Functor (ProductF c) ('KProxy :: KProxy (k, k)) ('KProxy :: KProxy k) where
    type Domain (ProductF c) 'KProxy = c :><: c
    type Codomain (ProductF c) 'KProxy = c
    type FMap (ProductF c) (a :: (k, k)) = L a >< R a
    objectMap :: forall a. ProductF c -> Tagged a
        (Object (Domain (ProductF c) ('KProxy :: KProxy (k, k))) a :- Object (Codomain (ProductF c) ('KProxy :: KProxy k)) (FMap (ProductF c) a))
    objectMap ProductF = Tagged (proxy productObjectMap (Proxy :: Proxy '(c, L a, R a)) . Sub Dict)
    fmap ProductF (f :><: g) = f *** g

instance TerminalMorphism (Diag (->)) (a, b) '(a, b) ('KProxy :: KProxy *) ('KProxy :: KProxy (*, *)) where
    terminalMorphism = Tagged (P.fst :><: P.snd)
    terminalFactorization  = Tagged (\(f :><: g) z -> (f z, g z))

instance ProductCategory (->) where
    type (><) a b = (a, b)
    productObjectMap = Tagged (Sub Dict)
    univProduct = Tagged (Sub Dict)

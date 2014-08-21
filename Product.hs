module Product where

import qualified Prelude as P
import Data.Constraint hiding ((***), (&&&))
import Data.Proxy
import Data.Tagged

import Category
import Category.Product
import Functor
import TerminalMorphism

class Category c => ProductCategory (c :: k -> k -> *) where
    type (><) (a :: k) (b :: k) :: k
    productObjectMap :: Tagged '(c, a, b) ((Object c a, Object c b) :- Object c (a >< b))
    univProduct :: forall (a :: k) (b :: k). Tagged '(c, a, b) ((Object c a, Object c b) :- TerminalMorphism (Diag c) (a >< b) '(a, b))

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
    objectMap :: forall a. Tagged '(ProductF c, a)
        (Object (Domain (ProductF c) ('KProxy :: KProxy (k, k))) a :- Object (Codomain (ProductF c) ('KProxy :: KProxy k)) (FMap (ProductF c) a))
    objectMap = Tagged (proxy productObjectMap (Proxy :: Proxy '(c, L a, R a)) . Sub Dict)
    fmap ProductF (f :><: g) = f *** g

instance TerminalMorphism (Diag (->)) (a, b) '(a, b) where
    terminalMorphism = Tagged (P.fst :><: P.snd)
    terminalFactorization  = Tagged (\(f :><: g) z -> (f z, g z))

instance ProductCategory (->) where
    type (><) a b = (a, b)
    productObjectMap = Tagged (Sub Dict)
    univProduct = Tagged (Sub Dict)

instance TerminalMorphism (Diag (:-)) ((a :: Constraint), b) '(a, b) where
    terminalMorphism = Tagged (Sub Dict :><: Sub Dict)
    terminalFactorization = Tagged (\(f :><: g) -> Sub (Dict \\ f \\ g))

instance ProductCategory (:-) where
    type (><) a b = ((a, b) :: Constraint)
    productObjectMap = Tagged (Sub Dict)
    univProduct = Tagged (Sub Dict)

module Product where

import qualified Prelude as P
import Data.Constraint hiding ((***), (&&&))
import Data.Proxy
import Data.Tagged

import Category
import Category.Product
import Functor
import Terminal
import Universal
import Monoidal

class Category c => ProductCategory (c :: k -> k -> *) where
    type Product c (a :: k) (b :: k) :: k
    univProduct :: forall (a :: k) (b :: k). Tagged '(c, a, b) ((Object c a, Object c b) :- TerminalMorphism (Diag c) (Product c a b) '(a, b))

proj :: forall a b c. (ProductCategory c, Object c a, Object c b) => (c (Product c a b) a, c (Product c a b) b)
proj = (l, r) where
    l :><: r = t
    t :: (c :><: c) '(Product c a b, Product c a b) '(a, b)
    t = proxy terminalMorphism (Proxy :: Proxy '(Diag c, Product c a b)) \\ proxy univProduct (Proxy :: Proxy '(c, a, b))

proj1 :: forall a b c. (ProductCategory c, Object c a, Object c b) => Tagged b (c (Product c a b) a)
proj1 = Tagged p where
    p :><: _ = t
    t :: (c :><: c) '(Product c a b, Product c a b) '(a, b)
    t = proxy terminalMorphism (Proxy :: Proxy '(Diag c, Product c a b)) \\ proxy univProduct (Proxy :: Proxy '(c, a, b))

proj2 :: forall a b c. (ProductCategory c, Object c a, Object c b) => Tagged a (c (Product c a b) b)
proj2 = Tagged p where
    _ :><: p = t
    t :: (c :><: c) '(Product c a b, Product c a b) '(a, b)
    t = proxy terminalMorphism (Proxy :: Proxy '(Diag c, Product c a b)) \\ proxy univProduct (Proxy :: Proxy '(c, a, b))

(&&&) :: forall c a b1 b2. ProductCategory c => c a b1 -> c a b2 -> c a (Product c b1 b2)
f &&& g
    | Dict <- observeObjects f, Dict <- observeObjects g
        = proxy terminalFactorization (Proxy :: Proxy (Diag c)) (f :><: g) \\ proxy univProduct (Proxy :: Proxy '(c, b1, b2))

(***) :: ProductCategory c => c a1 b1 -> c a2 b2 -> c (Product c a1 a2) (Product c b1 b2)
f *** g
    | Dict <- observeObjects f, Dict <- observeObjects g = let (l, r) = proj in (f . l) &&& (g . r)

data ProductF (c :: o -> o -> *)

instance ProductCategory c => Functor (ProductF (c :: o -> o -> *)) ('KProxy :: KProxy ((o, o) -> o)) where
    type Domain (ProductF c) = c :><: c
    type Codomain (ProductF c) = c
    type FMap (ProductF c) '(a, b) = Product c a b
    morphMap = Tagged (\(f :><: g) -> f *** g)

instance (ProductCategory c, Terminal c) => Monoidal c (ProductF c) where
    type I (ProductF c) = T c

instance TerminalMorphism (Diag (->)) (a, b) '(a, b) where
    terminalMorphism = Tagged (P.fst :><: P.snd)
    terminalFactorization  = Tagged (\(f :><: g) z -> (f z, g z))

instance ProductCategory (->) where
    type Product (->) a b = (a, b)
    univProduct = Tagged (Sub Dict)

instance TerminalMorphism (Diag (:-)) ((a :: Constraint), b) '(a, b) where
    terminalMorphism = Tagged (Sub Dict :><: Sub Dict)
    terminalFactorization = Tagged (\(f :><: g) -> Sub (Dict \\ f \\ g))

instance ProductCategory (:-) where
    type Product (:-) a b = ((a, b) :: Constraint)
    univProduct = Tagged (Sub Dict)

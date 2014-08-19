module Category where

import qualified Prelude as P
import GHC.Prim
import Data.Constraint

class Category m where
    type Object (m :: k -> k -> *) (a :: k) :: Constraint
    id :: Object m a => m a a
    observeObjects :: m a b -> Dict (Object m a, Object m b)
    (.) :: m b c -> m a b -> m a c

instance Category (->) where
    type Object (->) a = ()
    id = P.id
    observeObjects = P.const Dict
    (.) = (P..)

instance Category (:-) where
    type Object (:-) a = ()
    id = refl
    observeObjects = P.const Dict
    (.) = trans

module Category where

import qualified Prelude as P
import GHC.Prim
import Data.Constraint

class Category m where
    type Object (m :: k -> k -> *) (a :: k) :: Constraint
    id :: Object m a => m a a
    (.) :: (Object m a, Object m b, Object m c) => m b c -> m a b -> m a c

instance Category (->) where
    type Object (->) a = ()
    id = P.id
    (.) = (P..)

instance Category (:-) where
    type Object (:-) a = ()
    id = refl
    (.) = trans

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}

module Category where

import qualified Prelude as P
import GHC.Prim

class Category m where
    type Object (m :: k -> k -> *) (a :: k) :: Constraint
    id :: m a a
    (.) :: m b c -> m a b -> m a c

instance Category (->) where
    type Object (->) a = ()
    id = P.id
    (.) = (P..)

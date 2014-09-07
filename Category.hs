module Category where

import qualified Prelude as P
import GHC.Prim
import Data.Constraint

-- |The class of categories @m@ with objects of kind @k@ which satisfy the
-- constraint @Object m@. For any objects @a@ and @b@, the type @m a b@ is the
-- type of morphisms with domain @a@ and codomain @b@.
class Category (m :: k -> k -> *) where
    -- |The set of objects.
    type Object m (a :: k) :: Constraint
    -- |The Identity operator.
    id :: Object m a => m a a
    -- |The Composition operator.
    (.) :: m b c -> m a b -> m a c
    -- |Morphisms are arrows between objects.
    observeObjects :: m a b -> Dict (Object m a, Object m b)

-- |The category Hask of functions between types.
instance Category (->) where
    type Object (->) a = ()
    id = P.id
    observeObjects = P.const Dict
    (.) = (P..)

-- |The category of entailment from 'constraints'
instance Category (:-) where
    type Object (:-) a = ()
    id = refl
    observeObjects = P.const Dict
    (.) = trans

-- |Dual categories
newtype Op c a b = Op {unOp :: c b a}

instance Category c => Category (Op c) where
    id = Op id
    (Op f) . (Op g) = Op (g . f)
    type Object (Op c) a = Object c a
    observeObjects (Op c) = case observeObjects c of Dict -> Dict

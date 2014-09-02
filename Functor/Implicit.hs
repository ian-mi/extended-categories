module Functor.Implicit where

import qualified Prelude as P
import Data.Proxy
import Data.Tagged

import Category

class (Category (Domain f), Category (Codomain f)) => Functor (f :: o1 -> o2) where
    type Domain f :: o1 -> o1 -> *
    type Codomain f :: o2 -> o2 -> *
    fmap :: Domain f a b -> Codomain f (f a) (f b)

type EndoFunctor f = (Functor f, Domain f ~ Codomain f)

instance P.Functor f => Functor f where
    type Domain f = (->)
    type Codomain f = (->)
    fmap = P.fmap

module Monoidal where

import Data.Tagged
import Data.Proxy

import Category
import Category.Product
import Functor

class (Category c, FunctorOf mu (c :><: c) c) => Monoidal (c :: o -> o -> *) mu | mu -> c where
    type I mu :: o

(<>) :: forall (c :: o -> o -> *) mu a1 a2 b1 b2. Monoidal c mu => c a1 b1 -> c a2 b2 -> Tagged mu (c (FMap mu '(a1, a2)) (FMap mu '(b1, b2)))
f <> g = Tagged (proxy morphMap (Proxy :: Proxy mu) (f :><: g))


module Monoidal where

import Data.Tagged
import Data.Proxy

import Category
import Category.Product
import Functor

class (Category c, Functor (Mu c) ('KProxy :: KProxy ((k, k) -> k)), Domain (Mu c) ~ (c :><: c), Codomain (Mu c) ~ c, Object c (I c)) =>
        Monoidal (c :: k -> k -> *) where
    type Mu c
    type I c :: k

(<>) :: forall c a1 a2 b1 b2. Monoidal c => c a1 b1 -> c a2 b2 -> c (FMap (Mu c) '(a1, a2)) (FMap (Mu c) '(b1, b2))
f <> g = proxy morphMap (Proxy :: Proxy (Mu c)) (f :><: g)

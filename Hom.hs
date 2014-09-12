module Hom where

import Data.Proxy
import Data.Tagged

import Category
import Category.Product
import Functor

data Hom c

instance Category c => Functor (Hom (c :: o -> o -> *)) ('KProxy :: KProxy ((o, o) -> *)) where
    type Domain (Hom c) = Op c :><: c
    type Codomain (Hom c) = (->)
    type FMap (Hom c) '(a, b) = c a b
    morphMap = Tagged (\(Op f :><: g) h -> g . h . f)

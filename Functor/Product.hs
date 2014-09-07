module Functor.Product where

import Data.Proxy
import Data.Tagged

import Category
import Category.Product
import Functor

data f :&&&: g where
    (:&&&:) :: (Functor f ('KProxy :: KProxy (o -> o1)), Functor g ('KProxy :: KProxy (o -> o2)), (Domain f :: o -> o -> *) ~ Domain g) =>
        f -> g -> f :&&&: g

instance (Functor f ('KProxy :: KProxy (o -> o1)), Functor g ('KProxy :: KProxy (o -> o2)), (Domain f :: o -> o -> *) ~ Domain g) =>
        Functor (f :&&&: g) ('KProxy :: KProxy (o -> (o1, o2))) where
    type Domain (f :&&&: g) = Domain f
    type Codomain (f :&&&: g) = Codomain f :><: Codomain g
    type FMap (f :&&&: g) a = '(FMap f a, FMap g a)
    morphMap = Tagged (\t -> proxy morphMap (Proxy :: Proxy f) t :><: proxy morphMap (Proxy :: Proxy g) t)

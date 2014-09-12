module Category.Product where

import Data.Constraint

import Category

data (c1 :><: c2) a b where
    (:><:) :: (a ~ '(L a, R a), b ~ '(L b, R b))  => c1 (L a) (L b) -> c2 (R a) (R b) -> (c1 :><: c2) a b

type family L t where L '(a, b) = a
type family R t where R '(a, b) = b

instance (Category c1, Category c2) => Category (c1 :><: c2) where
    type Object (c1 :><: c2) a = (Object c1 (L a), Object c2 (R a), a ~ '(L a, R a))
    id = id :><: id
    observeObjects (f :><: g)
        | Dict <- observeObjects f, Dict <- observeObjects g = Dict
    (f1 :><: f2) . (g1 :><: g2) = (f1 . g1) :><: (f2 . g2)

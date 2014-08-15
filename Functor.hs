{-# LANGUAGE PolyKinds, DataKinds, TypeFamilies, ConstraintKinds #-}
{-# LANGUAGE InstanceSigs, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}

module Functor where

import qualified Prelude as P
import Data.Constraint
import Data.Tagged

import Category
import KProxy

class (Category (Domain f domain), Category (Codomain f codomain)) => Functor f (domain :: KProxy o1) (codomain :: KProxy o2) | f -> domain, f -> codomain where
    type Domain f domain :: o1 -> o1 -> *
    type Codomain f codomain :: o2 -> o2 -> *
    type FMap f (a :: o1) :: o2
    objectMap :: f -> Tagged a (Object (Domain f domain) a :- Object (Codomain f codomain) (FMap f a))
    fmap :: (Object (Domain f domain) a, Object (Domain f domain) b) => f -> Domain f domain a b -> Codomain f codomain (FMap f a) (FMap f b)

data f :.: g = f :.: g

instance (Functor f domainF codomainF, Functor g domainG codomainG, codomainG ~ domainF) => Functor (f :.: g) domainG codomainF where
    type Domain (f :.: g) domainG = Domain g domainG
    type Codomain (f :.: g) codomainF = Codomain f codomainF
    type FMap (f :.: g) a = FMap f (FMap g a)

data MaybeF = MaybeF

instance Functor MaybeF ('KProxy :: KProxy *) ('KProxy :: KProxy *) where
    type Domain MaybeF ('KProxy :: KProxy *) = (->)
    type Codomain MaybeF ('KProxy :: KProxy *) = (->)
    type FMap MaybeF a = P.Maybe a
    objectMap MaybeF = Tagged (Sub Dict)
    fmap MaybeF = P.fmap

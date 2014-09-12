module Monad where

import qualified Prelude as P
import Data.Constraint
import Data.Proxy
import Data.Tagged

import Category
import Functor
import NatTr

class EndoFunctorOf t c => Monad t (c :: o -> o -> *) | t -> c where
    nu :: NatTr c c (IdentityF c) t
    mu :: NatTr c c (Comp ('KProxy :: KProxy o) t t) t

data MonadMorph c t s where MonadMorph :: (Monad t c, Monad s c) => NatTr c c t s -> MonadMorph c t s

instance Category c => Category (MonadMorph c) where
    type Object (MonadMorph c) t = Monad t c
    id = MonadMorph id
    MonadMorph f . MonadMorph g = MonadMorph (f . g)
    observeObjects (MonadMorph _) = Dict

data ForgetM c where
    ForgetM :: Category c => ForgetM c

instance Category c => Functor (ForgetM c) ('KProxy :: KProxy (* -> *)) where
    type Domain (ForgetM c) = MonadMorph c
    type Codomain (ForgetM c) = NatTr c c
    type FMap (ForgetM c) (t :: *) = t
    morphMap = Tagged (\(MonadMorph t) -> t)

instance (P.Functor m, P.Monad m) => Monad (Ftag m) (->) where
    nu = NatTr (Tagged P.return)
    mu = NatTr (Tagged (P.>>= id))

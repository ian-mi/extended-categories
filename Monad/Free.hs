module Monad.Free where

import qualified Prelude as P
import Data.Constraint
import Data.Proxy
import Data.Tagged

import Category
import Functor
import Coproduct
import Monad
import NatTr
import NatTr.Coproduct

data Free f a where
    Free :: FMap f (Free f a) -> Free f a
    Pure :: EndoFunctorOf f (->) => a -> Free f a

freeT :: EndoFunctorOf f (->) => NatTr (->) (->) (f :.: Ftag (Free f)) (Ftag (Free f))
freeT = NatTr (Tagged Free)

pureT :: EndoFunctorOf f (->) => NatTr (->) (->) Id (Ftag (Free f))
pureT = NatTr (Tagged Pure)

unfreeT :: forall f. EndoFunctorOf f (->) => NatTr (->) (->) (Ftag (Free f)) ((f :.: Ftag (Free f)) :+: Id)
unfreeT = NatTr (Tagged t) where
    t :: forall a. Free f a -> FMap ((f :.: Ftag (Free f)) :+: Id) a
    t (Free f) = appNat inj1 f
    t (Pure a) = appNat inj2 a

instance EndoFunctorOf f (->) => P.Functor (Free f) where
    fmap t = go where
        go (Free f) = Free (proxy morphMap (Proxy :: Proxy f) go f)
        go (Pure a) = Pure (t a)

instance EndoFunctorOf f (->) => P.Monad (Free f) where
    f >>= t = go f where
        go (Free x) = Free (proxy morphMap (Proxy :: Proxy f) go x)
        go (Pure a) = t a
    return = Pure

data FreeM = FreeM

instance Functor FreeM ('KProxy :: KProxy (* -> *)) where
    type Domain FreeM = NatTr (->) (->)
    type Codomain FreeM = MonadMorph (->)
    type FMap FreeM f = Ftag (Free f)
    morphMap = Tagged (\t -> case observeObjects t of Dict -> f t) where
        f t = MonadMorph go where
            go = coproduct (freeT . compNat t go) pureT . unfreeT

module TerminalMorphism where

import qualified Prelude as P
import Data.Tagged
import Data.Proxy

import Category
import Functor

class (Functor f ('KProxy :: KProxy k1) ('KProxy :: KProxy k2), Object (Domain f 'KProxy) a, Object (Codomain f 'KProxy) x) =>
        TerminalMorphism f (a :: k1) (x :: k2) where
    terminalMorphism :: Tagged '(f, a) (Codomain f 'KProxy (FMap f a) x)
    terminalFactorization :: Object (Domain f 'KProxy) y => Tagged f (Codomain f 'KProxy (FMap f y) x -> Domain f 'KProxy y a)

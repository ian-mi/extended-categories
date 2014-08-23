module TerminalMorphism where

import Data.Tagged
import Data.Proxy

import Category
import Functor

class (Functor f ('KProxy :: KProxy (o1 -> o2)), Object (Domain f) a, Object (Codomain f) x) =>
        TerminalMorphism f (a :: o1) (x :: o2) where
    terminalMorphism :: Tagged '(f, a) (Codomain f (FMap f a) x)
    terminalFactorization :: Object (Domain f) y => Tagged f (Codomain f (FMap f y) x -> Domain f y a)

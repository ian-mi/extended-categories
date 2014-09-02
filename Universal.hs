module Universal where

import Data.Tagged
import Data.Proxy

import Category
import Functor

class (Functor f ('KProxy :: KProxy (o1 -> o2)), Object (Domain f) a, Object (Codomain f) x) =>
        InitialMorphism f (a :: o1) (x :: o2) where
    initialMorphism :: Tagged '(f, a) (Codomain f x (FMap f a))
    initialFactorization :: Object (Domain f) b => Tagged f (Codomain f x (FMap f b) -> Domain f a b)

class (Functor f ('KProxy :: KProxy (o1 -> o2)), Object (Domain f) a, Object (Codomain f) x) =>
        TerminalMorphism f (a :: o1) (x :: o2) where
    terminalMorphism :: Tagged '(f, a) (Codomain f (FMap f a) x)
    terminalFactorization :: Object (Domain f) b => Tagged f (Codomain f (FMap f b) x -> Domain f b a)

{-# LANGUAGE PolyKinds, DataKinds, TypeFamilies, ConstraintKinds #-}
{-# LANGUAGE InstanceSigs, ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators, GADTs, MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}

module TerminalMorphism where

import qualified Prelude as P

import Category
import Functor

class (Functor f c1 c2, Object (Domain f c1) a, Object (Codomain f c2) x) => TerminalMorphism f a x c1 c2 | f -> c1, f -> c2 where
    terminalMorphism :: Codomain f c2 (FMap f a) x
    terminalFactorization :: Object (Domain f c1) y => Codomain f c2 (FMap f y) x -> Domain f c1 y a

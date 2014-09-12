module Adjoint where

import Data.Constraint
import Data.Proxy
import Data.Tagged

import Category
import Category.Product
import Functor
import Functor.Product
import NatTr

class (FunctorOf f c1 c2, FunctorOf g c2 c1) => Adjoint (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *) f g | f -> c1, f -> c2, g -> c1, g -> c2 where
    leftAdjunct :: NatTr (Op c1 :><: c2) (->)
        (Comp ('KProxy :: KProxy (o2, o2)) (Hom c2) (Dual f :***: IdentityF c2))
        (Comp ('KProxy :: KProxy (o1, o1)) (Hom c1) (IdentityF (Op c1) :***: g))
    rightAdjunct :: NatTr (Op c1 :><: c2) (->)
        (Comp ('KProxy :: KProxy (o1, o1)) (Hom c1) (IdentityF (Op c1) :***: g))
        (Comp ('KProxy :: KProxy (o2, o2)) (Hom c2) (Dual f :***: IdentityF c2))

phiL :: forall (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *) f g (x :: o1) (w :: o2).
    (Adjoint c1 c2 f g, Object c1 x) => Tagged '(f, g) (c2 (FMap f x) w -> c1 x (FMap g w))
phiL = Tagged f where
    f m | Dict <- observeObjects m = proxy morphMap (Proxy :: Proxy (AppNat '(x, w) (Op c1 :><: c2) (->))) adj m
    adj :: NatTr (Op c1 :><: c2) (->)
        (Comp ('KProxy :: KProxy (o2, o2)) (Hom c2) (Dual f :***: IdentityF c2))
        (Comp ('KProxy :: KProxy (o1, o1)) (Hom c1) (IdentityF (Op c1) :***: g))
    adj = leftAdjunct

phiR :: forall (c1 :: o1 -> o1 -> *) (c2 :: o2 -> o2 -> *) f g (x :: o1) (w :: o2).
    (Adjoint c1 c2 f g, Object c2 w) => Tagged '(f, g) (c1 x (FMap g w) -> c2 (FMap f x) w)
phiR = Tagged f where
    f m | Dict <- observeObjects m = proxy morphMap (Proxy :: Proxy (AppNat '(x, w) (Op c1 :><: c2) (->))) adj m
    adj :: NatTr (Op c1 :><: c2) (->)
        (Comp ('KProxy :: KProxy (o1, o1)) (Hom c1) (IdentityF (Op c1) :***: g))
        (Comp ('KProxy :: KProxy (o2, o2)) (Hom c2) (Dual f :***: IdentityF c2))
    adj = rightAdjunct

unit :: forall c1 (c2 :: o2 -> o2 -> *) f g. Adjoint c1 c2 f g => NatTr c1 c1 (IdentityF c1) (Comp ('KProxy :: KProxy o2) g f)
unit = NatTr t where
    t :: forall x. Object c1 x => Tagged x (c1 x (FMap g (FMap f x :: o2)))
    t = Tagged (proxy phiL (Proxy :: Proxy '(f, g)) (id :: c2 (FMap f x) (FMap f x))) \\ proxy objectMap (Proxy :: Proxy '(f, x))

counit :: forall (c1 :: o1 -> o1 -> *) c2 f g. Adjoint c1 c2 f g => NatTr c2 c2 (Comp ('KProxy :: KProxy o1) f g) (IdentityF c2)
counit = NatTr t where
    t :: forall y. Object c2 y => Tagged y (c2 (FMap f (FMap g y :: o1)) y)
    t = Tagged (proxy phiR (Proxy :: Proxy '(f, g)) (id :: c1 (FMap g y) (FMap g y))) \\ proxy objectMap (Proxy :: Proxy '(g, y))

module Terminal where

import Category

class (Category c, Object c (T c)) => Terminal c where
    type T c
    term :: Object c a => c a (T c)

instance Terminal (->) where
    type T (->) = ()
    term _ = ()

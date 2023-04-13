# Reordering Binds

(>>=) :: m a -> (a -> m b) -> m b

mb :: m b
{mb >>= \b -> {? : m ?}} : m ?

ma >>= \a ->
( mb >>= \b ->
  ( mc >>= \c ->
    md >>= \d ->
    me 
  ) : m e
) : m e

let :: a -> (a -> b) -> b

let a \x ->
let b \y -> 
let c \z -> 
let d \w -> 
_


- poly
  - ==
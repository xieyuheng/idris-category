module Category

%default total

export
interface Category object (arrow : object -> object -> Type) where
  identity : (a : object) -> arrow a a
  compose : {a, b, c : object} ->
    arrow a b -> arrow b c -> arrow a c
  Eqv : {a, b : object} ->
    arrow a b -> arrow a b -> Type
  identityLeft : {a, b : object} ->
    (f : arrow a b) -> Eqv (compose (identity a) f) f
  identityRight : {a, b : object} ->
    (f : arrow a b) -> Eqv (compose f (identity b)) f
  assoc : {a, b, c, d : object} ->
    (f : arrow a b) -> (g : arrow b c) -> (h : arrow c d) ->
    Eqv (compose f (compose g h)) (compose (compose f g) h)

-- can not define Inverse

-- - + Errors (1)
--  `-- Category.idr line 23 col 22:
--      When checking right hand side of Inverse with expected type
--              Type
--      Can't find implementation for Category object arrow

export
Inverse : Category object arrow =>
  arrow a b -> arrow b a -> Type
Inverse {a} {b} f g = Eqv (compose f g) (identity a)

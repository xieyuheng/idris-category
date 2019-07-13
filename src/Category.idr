module Category

%default total

export
interface Category object (arrow : object -> object -> Type) where
  id : (a : object) -> arrow a a
  compose : arrow a b -> arrow b c -> arrow a c
  idLeft : (f : arrow a b) -> compose (id a) f = f
  idRight : (f : arrow a b) -> compose f (id b) = f
  assoc : (f : arrow a b) -> (g : arrow b c) -> (h : arrow c d) ->
    compose f (compose g h) = compose (compose f g) h

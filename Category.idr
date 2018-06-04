module Category

%default total

export
interface
  Category Object (Arrow : Object -> Object -> Type)
where
  identity
    : (a : Object) -> Arrow a a
  compose
    : Arrow a b ->
      Arrow b c ->
      Arrow a c
  identityLeft
    : (f : Arrow a b) ->
      compose (identity a) f = f
  identityRight
    : (f : Arrow a b) ->
      compose f (identity b) = f
  composeAssociative
    : (f : Arrow a b) ->
      (g : Arrow b c) ->
      (h : Arrow c d) ->
      compose f (compose g h) = compose (compose f g) h

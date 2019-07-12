module Category

%default total

-- record Category where
--   constructor MkCategory
--   object : Type
--   arrow : object -> object -> Type
--   identity
--     : (a : object) -> arrow a a
--   compose
--     : {a, b, c : object} ->
--       arrow a b ->
--       arrow b c ->
--       arrow a c
--   identityLeft
--     : {a, b : object} ->
--       (f : arrow a b) ->
--       compose (identity a) f = f
--   identityRight
--     : {a, b : object} ->
--       (f : arrow a b) ->
--       compose f (identity b) = f
--   composeAssociative
--     : {a, b, c, d : object} ->
--       (f : arrow a b) ->
--       (g : arrow b c) ->
--       (h : arrow c d) ->
--       compose f (compose g h) = compose (compose f g) h

export
interface
  Category object (arrow : object -> object -> Type)
where
  identity
    : (a : object) -> arrow a a
  compose
    : arrow a b ->
      arrow b c ->
      arrow a c
  identityLeft
    : (f : arrow a b) ->
      compose (identity a) f = f
  identityRight
    : (f : arrow a b) ->
      compose f (identity b) = f
  composeAssociative
    : (f : arrow a b) ->
      (g : arrow b c) ->
      (h : arrow c d) ->
      compose f (compose g h) = compose (compose f g) h

-- export
-- Inverse
--   : (Category object arrow) =>
--     (f : arrow a b) ->
--     (g : arrow b a) -> Type
-- Inverse {a} {b} f g = (?x = ?y)

-- export
-- Inverse
--   : (Category object arrow) =>
--     (f : arrow a b) ->
--     (g : arrow b a) ->
--     (compose f g) = (identity a)

module Morphism

import Category

%default total

funext : (f, g : a -> b) -> ((x : a) -> f x = g x) -> f = g
funext f g = believe_me

leftIdPoint : (f : a -> b) -> (x : a) -> id (f x) = f x
leftIdPoint f x = Refl

rightIdPoint : (f : a -> b) -> (x : a) -> f (id x) = f x
rightIdPoint f x = Refl

Id : a -> a
Id = Prelude.Basics.id

leftId : (f : a -> b) -> Id . f = f
leftId f = funext (Id . f) f $ leftIdPoint f

rightId : (f : a -> b) -> f . Id = f
rightId f = funext (f . Id) f $ rightIdPoint f

compPoint : (f : b -> c) -> (g : a -> b) -> (x : a) -> f (g x) = (f . g) x
compPoint f g x = Refl

compAssociative : (f : a -> b) -> (g : b -> c) -> (h : c -> d) ->
                  h . (g . f) = (h . g) . f
compAssociative f g h = qed where
  step_1   : (x : _) -> h ((g . f) x) = (h . (g . f)) x
  step_1   = compPoint h (g . f)

  step_2   : (x : _) -> (h . (g . f)) x = h ((g . f) x)
  step_2 x = sym (step_1 x)

  step_3   : (x : _) -> (h . g) (f x) = ((h . g) . f) x
  step_3   = compPoint (h . g) f

  step_4   : (x : _) -> (h . (g . f)) x = ((h . g) . f) x
  step_4 x = trans (step_2 x) (step_3 x)

  qed      : h . (g . f) = (h . g) . f
  qed      = funext (h . (g . f)) ((h . g) . f) step_4

-- sym : {l:a} -> {r:a} -> l = r -> r = l
-- sym Refl = Refl

-- trans : {a:x} -> {b:y} -> {c:z} -> a = b -> b = c -> a = c
-- trans Refl Refl = Refl

data Morphism : Type -> Type -> Type where
  Mor : (a -> b) -> Morphism a b

infixr 10 ~>
(~>) : Type -> Type -> Type
(~>) = Morphism

mComp : (b ~> c) -> (a ~> b) -> (a ~> c)
mComp (Mor f) (Mor g) = Mor (f . g)

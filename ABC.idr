module ABC

import Category

-- directed total graph with three node A, B, C

%default total

data ABC : Type where
  A : ABC
  B : ABC
  C : ABC

data ABCArrow : (x, y : ABC) -> Type where
  MkABCArrow : (x, y : ABC) -> ABCArrow x y

namespace ABCCat

  identity : (x : ABC) -> ABCArrow x x
  identity x = MkABCArrow x x

  compose
    : ABCArrow x y ->
      ABCArrow y z ->
      ABCArrow x z
  compose (MkABCArrow x y) (MkABCArrow y z) = MkABCArrow x z

  identityLeft : (f : ABCArrow x y) -> compose (identity x) f = f
  identityLeft (MkABCArrow x y) = Refl

  identityRight : (f : ABCArrow x y) -> compose f (identity y) = f
  identityRight (MkABCArrow x y) = Refl

  composeAssociative : (f : ABCArrow x y) ->
      (g : ABCArrow y z) ->
      (h : ABCArrow z w) ->
      compose f (compose g h) = compose (compose f g) h
  composeAssociative (MkABCArrow x y) (MkABCArrow y z) (MkABCArrow z w) = Refl

Category ABC ABCArrow where
  identity = ABCCat.identity
  compose = ABCCat.compose
  identityLeft = ABCCat.identityLeft
  identityRight = ABCCat.identityRight
  composeAssociative = ABCCat.composeAssociative

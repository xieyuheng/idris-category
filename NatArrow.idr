module NatArrow

import Category

%default total

data NatArrow : () -> () -> Type where
  GetNat : Nat -> NatArrow () ()

namespace NatArrowCat

  identity : (a : ()) -> NatArrow a a
  identity () = GetNat 0

  compose
    : NatArrow a b ->
      NatArrow b c ->
      NatArrow a c
  compose (GetNat k) (GetNat j) = GetNat (k + j)

  identityLeft
    : (f : NatArrow a b) ->
      compose (identity a) f = f
  identityLeft (GetNat k) = cong (plusZeroLeftNeutral k)

  identityRight
    : (f : NatArrow a b) ->
      compose f (identity b) = f
  identityRight (GetNat k) = cong (plusZeroRightNeutral k)

  composeAssociative
    : (f : NatArrow a b) ->
      (g : NatArrow b c) ->
      (h : NatArrow c d) ->
      compose f (compose g h) = compose (compose f g) h
  composeAssociative (GetNat f) (GetNat g) (GetNat h) =
    cong (plusAssociative f g h)

Category () NatArrow where
  identity = NatArrowCat.identity
  compose = NatArrowCat.compose
  identityLeft = NatArrowCat.identityLeft
  identityRight = NatArrowCat.identityRight
  composeAssociative = NatArrowCat.composeAssociative

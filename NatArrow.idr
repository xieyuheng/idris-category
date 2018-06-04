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

  -- identityLeft
  --   : (f : NatArrow a b) ->
  --     compose (identity a) f = f
  -- identityLeft (GetNat k) = cong () Refl

  -- cIdLeft  (getNat f) = cong (plusZeroLeftNeutral  f)
  -- cIdRight (getNat f) = cong (plusZeroRightNeutral f)
  -- cCompAssociative (getNat f) (getNat g) (getNat h) =
  --   cong (plusAssociative h g f)

-- plusZeroLeftNeutral
-- plusZeroRightNeutral
-- plusAssociative

Category () NatArrow where
  identity = NatArrowCat.identity
  compose = NatArrowCat.compose
  -- identityLeft = NatArrowCat.identityLeft
  -- identityRight = NatArrowCat.identityRight
  -- composeAssociative = NatArrowCat.composeAssociative


-- interface
--   Category Object Arrow =>
--   Terminal Object (Arrow : Object -> Object -> Type)
-- where

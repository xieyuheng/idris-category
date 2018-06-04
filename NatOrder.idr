module NatOrder

import Category

%default total

data NatOrder : (l, r : Nat) -> Type where
  ZeroOrder : NatOrder Z _
  SuccOrder : NatOrder l r -> NatOrder (S l) (S r)

nonNegativeNat : (n : Nat) -> NatOrder Z n
nonNegativeNat n = ZeroOrder

reflexiveNatOrder : (n : Nat) -> NatOrder n n
reflexiveNatOrder Z = ZeroOrder
reflexiveNatOrder (S n) = SuccOrder (reflexiveNatOrder n)

transitiveNatOrder : NatOrder a b -> NatOrder b c -> NatOrder a c
transitiveNatOrder ZeroOrder y = ZeroOrder
transitiveNatOrder (SuccOrder x) (SuccOrder y) =
  SuccOrder (transitiveNatOrder x y)

NatLessThen : (l, r : Nat) -> Type
NatLessThen l r = NatOrder (S l) r

archimedeanPropertyNat : (n : Nat) -> (m : Nat ** NatLessThen n m)
archimedeanPropertyNat n = (S n ** reflexiveNatOrder (S n))

namespace NatOrderCat

  identity : (a : Nat) -> NatOrder a a
  identity = reflexiveNatOrder

  compose
    : NatOrder a b ->
      NatOrder b c ->
      NatOrder a c
  compose = transitiveNatOrder

  identityLeft
    : (f : NatOrder a b) ->
      compose (identity a) f = f
  identityLeft ZeroOrder = Refl
  identityLeft (SuccOrder x) =
    cong (identityLeft x)

  identityRight
    : (f : NatOrder a b) ->
      compose f (identity b) = f
  identityRight ZeroOrder = Refl
  identityRight (SuccOrder x) =
    cong (identityRight x)

  composeAssociative
    : (f : NatOrder a b) ->
      (g : NatOrder b c) ->
      (h : NatOrder c d) ->
      compose f (compose g h) = compose (compose f g) h
  composeAssociative ZeroOrder _ _ = Refl
  composeAssociative (SuccOrder f) (SuccOrder g) (SuccOrder h) =
    cong (composeAssociative f g h)

Category Nat NatOrder where
  identity = NatOrderCat.identity
  compose = NatOrderCat.compose
  identityLeft = NatOrderCat.identityLeft
  identityRight = NatOrderCat.identityRight
  composeAssociative = NatOrderCat.composeAssociative

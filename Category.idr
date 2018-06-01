module Category

%default total

interface Category
  Object
  (Arrow : Object -> Object -> Type)
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

Category Nat NatOrder where
  identity = reflexiveNatOrder
  compose = transitiveNatOrder

  identityLeft ZeroOrder = Refl
  identityLeft (SuccOrder x) =
    cong {f = SuccOrder} (identityLeft x)

  identityRight ZeroOrder = Refl
  identityRight (SuccOrder x) =
    cong {f = SuccOrder} (identityRight x)

  composeAssociative ZeroOrder _ _ = Refl
  composeAssociative (SuccOrder f) (SuccOrder g) (SuccOrder h) =
    cong {f = SuccOrder} (composeAssociative f g h)

but in the implementation of the interface I have ::
  identity = reflexiveNatOrder   and   compose = transitiveNatOrder

Type mismatch between `compose (identity l) x`
and `transitiveNatOrder (reflexiveNatOrder l) x`

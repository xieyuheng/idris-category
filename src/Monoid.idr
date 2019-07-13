module Monoid

%default total

export
interface Monoid a where
  mempty : a
  mappend : a -> a -> a

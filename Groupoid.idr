module Groupoid

import Category

%default total

-- export
-- interface
--   Category object arrow =>
--   Groupoid object (arrow : object -> object -> Type)
-- where
--   inverse : (f : arrow a b) -> (g : arrow b a ** Inverse f g)

export
interface
  Category object arrow =>
  Groupoid object (arrow : object -> object -> Type)
where
  inverse : (f : arrow a b) -> (g : arrow b a ** Inverse f g)

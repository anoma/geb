import GebLean.Utilities.TwistedArrow
import GebLean.Utilities.TwArrPresheaf
import GebLean.Utilities.Grothendieck

/-!
# The connected Grothendieck construction

Given a functor `F : Tw(C) → Cat`, this module defines a category `E(F)`
equipped with a functor `E(F) → Arr(C)`. This defines a functor

```text
E : Fun(Tw(C), Cat) → Cat/Arr(C).
```

The construction generalizes the two-sided Grothendieck construction by
allowing the indexing category to depend on the arrow `f : a → b` itself,
not just on `a` and `b` separately. The morphisms carry both an arrow-category
square and a fiber morphism in the common diagonal category.

See `docs/connected-grothendieck-construction.md` for the mathematical
specification.
-/

universe v u

namespace GebLean

open CategoryTheory

end GebLean

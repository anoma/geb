import GebLean.SliceW.FreeM
import GebLean.SliceW.Iso
import GebLean.SliceW.Reindex
import GebLean.SliceW.Translate

/-!
# Native free-monad layer on the slice W-type

Directory index for the native development on the vendored slice W-type
(`Geb.Mathlib.Data.PFunctor.Slice.W`), independent of the polynomial-algebra
and ramified layers. `Iso` supplies container isomorphisms of slice
functors and, for endofunctors, the equivalence they induce on the
associated W-types. `Reindex` supplies base change and dependent sum along
maps of a slice functor's domain and codomain and, for the endofunctor case
of a single index equivalence, the equivalence it induces on the associated
W-types. `Translate` supplies the free-monad augmentation `Y + F(-)` of a
slice endofunctor. `FreeM` supplies the free monad's carrier and constructors
as the fibers and node shapes of the translate augmentation's W-type.
-/

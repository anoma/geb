import GebLean.Ramified.Polynomial.RType

/-!
# Tests for `RType'` on the vendored slice stack

Executable checks that the bridge equivalence `rTypeSliceEquiv` carries a
native constructor tree to its legacy counterpart, and that the native
order measure `RType'.ord` agrees with the legacy `RType.ord` across the
bridge. Also checks the raw-subterm paramorphisms `RType'.domains` and
`RType'.objTarget`, and the `W.RecProp`-based predicates `RType'.IsTower`
and `RType'.IsSimple`, on a concrete arrow type. Each check goes through a
proven compatibility lemma rather than kernel reduction of the underlying
slice `W`-tree.
-/

namespace GebLeanTests.Ramified.Polynomial.RType

open GebLean.Ramified GebLean.Ramified.Polynomial

example :
    rTypeSliceEquiv (RType'.arrow RType'.o RType'.o) = RType.arrow RType.o RType.o := by
  simp [rTypeSliceEquiv_arrow, rTypeSliceEquiv_o]

example :
    RType'.ord (RType'.arrow RType'.o RType'.o)
      = RType.ord (RType.arrow RType.o RType.o) := by
  simp [rTypeSliceEquiv_ord, rTypeSliceEquiv_arrow, rTypeSliceEquiv_o]

-- The domain paramorphism reads the raw arrow subterm: `domains (o -> o) = [o]`.
example :
    (RType'.domains (RType'.arrow RType'.o RType'.o)).map rTypeSliceEquiv = [RType.o] := by
  rw [rTypeSliceEquiv_domains, rTypeSliceEquiv_arrow, rTypeSliceEquiv_o]
  rfl

-- The object-target paramorphism reads an arrow's codomain: target `o -> o` is `o`.
example :
    rTypeSliceEquiv (RType'.objTarget (RType'.arrow RType'.o RType'.o)) = RType.o := by
  rw [rTypeSliceEquiv_objTarget, rTypeSliceEquiv_arrow, rTypeSliceEquiv_o]
  rfl

-- The `W.RecProp` tower predicate: `Omega o` is a tower sort.
example : RType'.IsTower (RType'.omega RType'.o) := by
  rw [rTypeSliceEquiv_isTower, rTypeSliceEquiv_omega, rTypeSliceEquiv_o]
  decide

-- The `W.RecProp` simple predicate: `o -> o` has no `Omega` occurrence.
example : RType'.IsSimple (RType'.arrow RType'.o RType'.o) := by
  rw [rTypeSliceEquiv_isSimple, rTypeSliceEquiv_arrow, rTypeSliceEquiv_o]
  decide

-- The primed paramorphism agrees with the legacy one across the bridge, with
-- the legacy step reading the subterms as images of the primed ones.
example
    (g : (b : natAlgSig.B) → Unit → (Fin (natAlgSig.ar b) → FreeAlg natAlgSig) →
      (Fin (natAlgSig.ar b) → Nat) → Nat)
    (x : FreeAlg' natAlgSig) :
    FreeAlg'.recurse
        (fun b q sub rec => g b q (fun e => freeAlgSliceEquiv natAlgSig (sub e)) rec) () x
      = FreeAlg.recurse g () (freeAlgSliceEquiv natAlgSig x) :=
  freeAlgSliceEquiv_recurse g () x

-- The denotation of an object sort is a copy of the carrier.
example : RType'.interp Nat RType'.o = Nat :=
  RType'.interp_isObj Nat (Or.inl (RType'.shape_mk RTypeShape.o Fin.elim0))

-- The carrier bridge is the interp cast followed by the denotation congruence.
example :
    carrierSliceEquiv natAlgSig RType'.o
      = (Equiv.cast (rTypeSliceEquiv_interp (FreeAlg' natAlgSig) RType'.o)).trans
          (RType.interpCongr (freeAlgSliceEquiv natAlgSig) (rTypeSliceEquiv RType'.o)) :=
  rfl

-- At an object sort the carrier bridge computes to `freeAlgSliceEquiv`.
example (hObj : RType'.o.IsObj) (x : RType'.interp (FreeAlg' natAlgSig) RType'.o) :
    cast (RType.interp_isObj (FreeAlg natAlgSig) (cast (rTypeSliceEquiv_isObj RType'.o) hObj))
        (carrierSliceEquiv natAlgSig RType'.o x)
      = freeAlgSliceEquiv natAlgSig (cast (RType'.interp_isObj (FreeAlg' natAlgSig) hObj) x) :=
  carrierSliceEquiv_isObj hObj x

end GebLeanTests.Ramified.Polynomial.RType

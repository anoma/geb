import GebLean.Ramified.Polynomial.FreeAlg
import GebLean.Ramified.RType
import GebLean.Ramified.OmegaShift
import GebLean.Ramified.Soundness.Normalization

/-!
# Ramified types on the vendored slice `W`-type

A second realization of the ramified types (r-types) of Leivant's
higher-type ramified recurrence on the vendored `geb-mathlib` slice
`W`-type stack, mirroring `GebLean/Ramified/RType.lean`'s `RType` on
`FreeAlg'` (`GebLean/Ramified/Polynomial/FreeAlg.lean`) in place of the
legacy `FreeAlg`. `RType'` is `FreeAlg' rTypeSig`; its constructors,
shape reader, denotation, tower sorts, and the object-, tower-, and
simple-sort predicates are re-expressed natively over the slice
eliminator, and the bridge equivalence `rTypeSliceEquiv : RType' ≃ RType`
identifies each with its legacy counterpart. Each operation carries a
compatibility lemma stating that it agrees with the legacy operation
across `rTypeSliceEquiv`.

## Main definitions

* `RType'` — the ramified types on the slice `W`-type: `FreeAlg' rTypeSig`.
* `RType'.o`, `RType'.arrow`, `RType'.omega` — the derived constructors,
  native via `FreeAlg'.mk`.
* `rTypeSliceEquiv` — the bridge equivalence `RType' ≃ RType`.
* `RType'.shape` — the top constructor shape, native via `W.dest`.
* `RType'.IsObj` — the object-sort predicate, shape-based.
* `RType'.interp` — the denotation over a carrier, native via `W.elim`.
* `carrierSliceEquiv` — the carrier bridge: the equivalence between the primed
  and legacy denotations at a translated r-type.
* `RType'.IsTower`, `RType'.IsSimple` — the tower- and simple-sort
  predicates, native via `W.RecProp`.
* `RType'.objTarget`, `RType'.domains` — the object target and domain
  list, native via the paramorphism `FreeAlg'.recurse`.
* `RType'.omegaShift`, `RType'.ord` — the Omega shift and order measure,
  native via the catamorphism `FreeAlg'.recurse`.
* `RType'.tower` — the tower sorts `Omega^m o`, native via `Nat.rec`.

## Main statements

* `rTypeSliceEquiv_o`, `rTypeSliceEquiv_arrow`, `rTypeSliceEquiv_omega` —
  the constructor compatibility lemmas.
* `rTypeSliceEquiv_shape`, `rTypeSliceEquiv_isObj`, `rTypeSliceEquiv_interp`,
  `rTypeSliceEquiv_isTower`, `rTypeSliceEquiv_isSimple`,
  `rTypeSliceEquiv_objTarget`, `rTypeSliceEquiv_domains`,
  `rTypeSliceEquiv_omegaShift`, `rTypeSliceEquiv_ord`, `rTypeSliceEquiv_tower` —
  the operation compatibility lemmas, each stating agreement with the
  legacy operation across `rTypeSliceEquiv`.
* `RType'.interp_isObj` — every object sort denotes a copy of the carrier.
* `freeAlgSliceEquiv_recurse` — the primed recurrence agrees with the legacy
  recurrence across the bridge.
* `cast_arrow` — transport along an equality of function types acts as
  transport of the argument and of the value.
* `carrierSliceEquiv_arrow`, `carrierSliceEquiv_o` — the carrier bridge at an
  arrow sort and at the base object sort.
* `carrierSliceEquiv_cast_heq` — the carrier bridge commutes with transport of
  its argument along a sort equality.
* `isObj_o'`, `isObj_omega'` — the base sort and every `Omega` sort are object
  sorts.
* `carrierSliceEquiv_isObj` — the carrier bridge at an object sort computes to
  the free-algebra bridge equivalence.

## References

D. Leivant, "Ramified recurrence and computational complexity III:
Higher type recurrence and elementary complexity", Annals of Pure and
Applied Logic 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.
The r-types are section 2.3; the tower sorts `Omega^m o` are section
2.4(3); the standard denotation of object sorts is section 2.7; the
object target and domain decomposition `tau = sigma-vec -> theta` is
section 2.4, p. 213; the simple (omega-free) types are section 4.2.

## Tags

ramified recurrence, ramified type, object sort, tower sort, free algebra,
polynomial functor, W-type, interpretation
-/

namespace GebLean.Ramified.Polynomial

open GebLean.Ramified GebLean.PolyBridge

/-- The ramified types on the vendored slice `W`-type: `FreeAlg' rTypeSig`.
A second realization of `RType` (`GebLean/Ramified/RType.lean`), related to
it by `rTypeSliceEquiv`. -/
def RType' : Type := FreeAlg' rTypeSig

/-- The base type `o` (Leivant III section 2.3): the nullary shape, native
via `FreeAlg'.mk`. -/
def RType'.o : RType' := FreeAlg'.mk RTypeShape.o Fin.elim0

/-- The function type `arrow tau sigma` (Leivant III section 2.3): the
binary shape applied to domain `a` and codomain `b`, native via
`FreeAlg'.mk`. -/
def RType'.arrow (a b : RType') : RType' := FreeAlg'.mk RTypeShape.arrow ![a, b]

/-- The type `Omega tau` (Leivant III section 2.3): the unary shape applied
to `a`, native via `FreeAlg'.mk`. -/
def RType'.omega (a : RType') : RType' := FreeAlg'.mk RTypeShape.omega ![a]

/-- The bridge equivalence between `RType'` and the legacy `RType`:
`freeAlgSliceEquiv` at the r-type signature. -/
def rTypeSliceEquiv : RType' ≃ RType := freeAlgSliceEquiv rTypeSig

/-- `rTypeSliceEquiv` carries the native base type to the legacy base type
(Leivant III section 2.3). -/
@[simp] theorem rTypeSliceEquiv_o : rTypeSliceEquiv RType'.o = RType.o := by
  change freeAlgSliceEquiv rTypeSig (FreeAlg'.mk RTypeShape.o Fin.elim0)
    = FreeAlg.mk RTypeShape.o Fin.elim0
  rw [freeAlgSliceEquiv_mk]
  congr 1
  funext e
  exact e.elim0

/-- `rTypeSliceEquiv` carries the native arrow to the legacy arrow on the
images of the children (Leivant III section 2.3). -/
@[simp] theorem rTypeSliceEquiv_arrow (a b : RType') :
    rTypeSliceEquiv (RType'.arrow a b)
      = RType.arrow (rTypeSliceEquiv a) (rTypeSliceEquiv b) := by
  change freeAlgSliceEquiv rTypeSig (FreeAlg'.mk RTypeShape.arrow ![a, b])
    = FreeAlg.mk RTypeShape.arrow ![rTypeSliceEquiv a, rTypeSliceEquiv b]
  rw [freeAlgSliceEquiv_mk]
  congr 1
  funext e
  refine Fin.cases ?_ (fun j => ?_) e
  · rfl
  · exact Fin.cases rfl (fun j' => j'.elim0) j

/-- `rTypeSliceEquiv` carries the native `Omega` to the legacy `Omega` on the
image of the child (Leivant III section 2.3). -/
@[simp] theorem rTypeSliceEquiv_omega (a : RType') :
    rTypeSliceEquiv (RType'.omega a) = RType.omega (rTypeSliceEquiv a) := by
  change freeAlgSliceEquiv rTypeSig (FreeAlg'.mk RTypeShape.omega ![a])
    = FreeAlg.mk RTypeShape.omega ![rTypeSliceEquiv a]
  rw [freeAlgSliceEquiv_mk]
  congr 1
  funext e
  exact Fin.cases rfl (fun j => j.elim0) e

/-- Structural induction over `FreeAlg'` in constructor form: a predicate
holds of every element once it holds of `FreeAlg'.mk b sub` whenever it
holds of each subterm `sub e`. The `FreeAlg'.mk`-phrased wrapping of the
slice `W`-type's `SlicePFunctor.W.induction`; the generic node `x` is
rewritten to `FreeAlg'.mk` form by `PUnit` eta and proof irrelevance. -/
theorem FreeAlg'.induction {A : AlgSig} {motive : FreeAlg' A → Prop}
    (mk : ∀ (b : A.B) (sub : Fin (A.ar b) → FreeAlg' A),
        (∀ e, motive (sub e)) → motive (FreeAlg'.mk b sub)) :
    ∀ t, motive t := by
  intro t
  refine SlicePFunctor.W.induction (F := toSlice A.polyEndo)
    (motive := fun w => ∀ h, motive ⟨w, h⟩) ?_ t.1 t.2
  intro x ih h
  change motive (FreeAlg'.mk x.1.1.2 (fun e => ⟨x.1.2 e, Subsingleton.elim _ _⟩))
  exact mk x.1.1.2 _ (fun e => ih e _)

/-- The top constructor shape of an r-type on the slice `W`-type (Leivant
III section 2.3): the label read off the one-level destructor
`SlicePFunctor.W.dest`. Non-recursive. -/
def RType'.shape (t : RType') : RTypeShape := (SlicePFunctor.W.dest t.1).1.1.2

/-- `RType'.shape` reads the label of a constructor node. -/
@[simp] theorem RType'.shape_mk (b : rTypeSig.B) (sub : Fin (rTypeSig.ar b) → RType') :
    RType'.shape (FreeAlg'.mk b sub) = b := by
  simp only [RType'.shape, FreeAlg'.mk]
  rw [SlicePFunctor.W.dest_mk]

/-- The top constructor shape agrees with the legacy shape across the bridge
(Leivant III section 2.3). -/
theorem rTypeSliceEquiv_shape (t : RType') :
    RType'.shape t = RType.shape (rTypeSliceEquiv t) := by
  refine FreeAlg'.induction
    (motive := fun t => RType'.shape t = RType.shape (rTypeSliceEquiv t))
    (fun b sub _ => ?_) t
  simp only [RType'.shape_mk]
  change b = RType.shape (freeAlgSliceEquiv rTypeSig (FreeAlg'.mk b sub))
  rw [freeAlgSliceEquiv_mk]
  rfl

/-- Object sorts on the slice `W`-type (Leivant III section 2.3): `o` and
every `Omega tau`, equivalently the r-types whose top shape is `o` or
`omega`. Shape-based, non-recursive. -/
def RType'.IsObj (t : RType') : Prop :=
  t.shape = RTypeShape.o ∨ t.shape = RTypeShape.omega

/-- The object-sort predicate agrees with the legacy predicate across the
bridge (Leivant III section 2.3). -/
@[simp] theorem rTypeSliceEquiv_isObj (t : RType') :
    RType'.IsObj t = RType.IsObj (rTypeSliceEquiv t) := by
  simp only [RType'.IsObj, RType.IsObj, rTypeSliceEquiv_shape]

/-- The order of an r-type on the slice `W`-type (Leivant III section 4.2's
order measure, extended over `Omega`): `ord o = 0`,
`ord (tau -> sigma) = max (1 + ord tau) (ord sigma)`, `ord (Omega tau) =
ord tau`. A catamorphism, native via `FreeAlg'.recurse`. -/
def RType'.ord (t : RType') : ℕ :=
  FreeAlg'.recurse (A := rTypeSig) (P := Unit)
    (fun b _ _sub rec => match b with
      | RTypeShape.o => 0
      | RTypeShape.arrow =>
        max (rec (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)) + 1)
          (rec (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)))
      | RTypeShape.omega => rec (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega))) () t

/-- The order measure agrees with the legacy order across the bridge
(Leivant III section 4.2). -/
@[simp] theorem rTypeSliceEquiv_ord (t : RType') :
    RType'.ord t = RType.ord (rTypeSliceEquiv t) := by
  refine FreeAlg'.induction
    (motive := fun t => RType'.ord t = RType.ord (rTypeSliceEquiv t))
    (fun b sub ih => ?_) t
  change RType'.ord (FreeAlg'.mk b sub)
    = RType.ord (freeAlgSliceEquiv rTypeSig (FreeAlg'.mk b sub))
  rw [freeAlgSliceEquiv_mk]
  simp only [RType'.ord] at ih ⊢
  cases b
  · rw [FreeAlg'.recurse_mk]; rfl
  · rw [FreeAlg'.recurse_mk]; simp only [ih]; rfl
  · rw [FreeAlg'.recurse_mk]; simp only [ih]; rfl

/-- The Omega shift on r-types on the slice `W`-type (Leivant III section
2.4(1)): the base substitution `tau[o := Omega o]`, sending `o` to `Omega o`
and commuting with `arrow` and `omega`. A catamorphism, native via
`FreeAlg'.recurse`. -/
def RType'.omegaShift (t : RType') : RType' :=
  FreeAlg'.recurse (A := rTypeSig) (P := Unit)
    (fun b _ _sub rec => match b with
      | RTypeShape.o => RType'.omega RType'.o
      | RTypeShape.arrow =>
        RType'.arrow (rec (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)))
          (rec (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)))
      | RTypeShape.omega =>
        RType'.omega (rec (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega)))) () t

/-- The Omega shift agrees with the legacy Omega shift across the bridge
(Leivant III section 2.4(1)). -/
@[simp] theorem rTypeSliceEquiv_omegaShift (t : RType') :
    rTypeSliceEquiv (RType'.omegaShift t) = RType.omegaShift (rTypeSliceEquiv t) := by
  refine FreeAlg'.induction
    (motive := fun t =>
      rTypeSliceEquiv (RType'.omegaShift t) = RType.omegaShift (rTypeSliceEquiv t))
    (fun b sub ih => ?_) t
  change rTypeSliceEquiv (RType'.omegaShift (FreeAlg'.mk b sub))
    = RType.omegaShift (freeAlgSliceEquiv rTypeSig (FreeAlg'.mk b sub))
  rw [freeAlgSliceEquiv_mk]
  simp only [RType'.omegaShift] at ih ⊢
  cases b
  · rw [FreeAlg'.recurse_mk]; simp only [rTypeSliceEquiv_omega, rTypeSliceEquiv_o]; rfl
  · rw [FreeAlg'.recurse_mk]; simp only [rTypeSliceEquiv_arrow, ih]; rfl
  · rw [FreeAlg'.recurse_mk]; simp only [rTypeSliceEquiv_omega, ih]; rfl

/-- The final object sort of an r-type on the slice `W`-type (Leivant III
section 2.4, p. 213): `o` and every `Omega tau` are their own target, and an
arrow's target is its codomain's. A paramorphism, native via
`FreeAlg'.recurse` (the `Omega` step reads the raw subterm). -/
def RType'.objTarget (t : RType') : RType' :=
  FreeAlg'.recurse (A := rTypeSig) (P := Unit)
    (fun b _ sub rec => match b with
      | RTypeShape.o => RType'.o
      | RTypeShape.arrow => rec (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))
      | RTypeShape.omega =>
        RType'.omega (sub (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega)))) () t

/-- The object target agrees with the legacy object target across the bridge
(Leivant III section 2.4, p. 213). -/
@[simp] theorem rTypeSliceEquiv_objTarget (t : RType') :
    rTypeSliceEquiv (RType'.objTarget t) = RType.objTarget (rTypeSliceEquiv t) := by
  refine FreeAlg'.induction
    (motive := fun t =>
      rTypeSliceEquiv (RType'.objTarget t) = RType.objTarget (rTypeSliceEquiv t))
    (fun b sub ih => ?_) t
  change rTypeSliceEquiv (RType'.objTarget (FreeAlg'.mk b sub))
    = RType.objTarget (freeAlgSliceEquiv rTypeSig (FreeAlg'.mk b sub))
  rw [freeAlgSliceEquiv_mk]
  simp only [RType'.objTarget] at ih ⊢
  cases b
  · rw [FreeAlg'.recurse_mk]; simp only [rTypeSliceEquiv_o]; rfl
  · rw [FreeAlg'.recurse_mk]; simp only [ih]; rfl
  · rw [FreeAlg'.recurse_mk]; simp only [rTypeSliceEquiv_omega]; rfl

/-- The domain sorts of an r-type `tau = sigma-vec -> theta` on the slice
`W`-type (Leivant III section 2.4, p. 213): empty at an object sort, and the
domain prepended to the codomain's domains at an arrow. A paramorphism,
native via `FreeAlg'.recurse` (the `arrow` step reads the raw domain
subterm). -/
def RType'.domains (t : RType') : List RType' :=
  FreeAlg'.recurse (A := rTypeSig) (P := Unit) (C := List RType')
    (fun b _ sub rec => match b with
      | RTypeShape.o => []
      | RTypeShape.arrow =>
        sub (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))
          :: rec (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))
      | RTypeShape.omega => []) () t

/-- The domain list agrees with the legacy domain list across the bridge,
mapped through `rTypeSliceEquiv` (Leivant III section 2.4, p. 213). -/
@[simp] theorem rTypeSliceEquiv_domains (t : RType') :
    (RType'.domains t).map rTypeSliceEquiv = RType.domains (rTypeSliceEquiv t) := by
  refine FreeAlg'.induction
    (motive := fun t =>
      (RType'.domains t).map rTypeSliceEquiv = RType.domains (rTypeSliceEquiv t))
    (fun b sub ih => ?_) t
  change (RType'.domains (FreeAlg'.mk b sub)).map rTypeSliceEquiv
    = RType.domains (freeAlgSliceEquiv rTypeSig (FreeAlg'.mk b sub))
  rw [freeAlgSliceEquiv_mk]
  simp only [RType'.domains] at ih ⊢
  cases b
  · rw [FreeAlg'.recurse_mk]; rfl
  · rw [FreeAlg'.recurse_mk]; simp only [List.map_cons, ih]; rfl
  · rw [FreeAlg'.recurse_mk]; rfl

/-- The tower-sort predicate on the slice `W`-type (Leivant III section
2.4(3)): `o` qualifies, an `arrow` does not, and `Omega tau` qualifies
exactly when `tau` does. A recursive `Prop`, native via
`SlicePFunctor.W.RecProp`. -/
def RType'.IsTower (t : RType') : Prop :=
  SlicePFunctor.W.RecProp (F := toSlice rTypeSig.polyEndo)
    (fun x ih => match x, ih with
      | ⟨⟨⟨_, RTypeShape.o⟩, _⟩, _⟩, _ => True
      | ⟨⟨⟨_, RTypeShape.arrow⟩, _⟩, _⟩, _ => False
      | ⟨⟨⟨_, RTypeShape.omega⟩, _⟩, _⟩, ih =>
        ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega)))
    t.1

/-- The omega-free (simple-type) predicate on the slice `W`-type (Leivant
III section 4.2): `o` is simple, `arrow a b` is simple exactly when both `a`
and `b` are, and no `Omega tau` is simple. A recursive `Prop`, native via
`SlicePFunctor.W.RecProp`. -/
def RType'.IsSimple (t : RType') : Prop :=
  SlicePFunctor.W.RecProp (F := toSlice rTypeSig.polyEndo)
    (fun x ih => match x, ih with
      | ⟨⟨⟨_, RTypeShape.o⟩, _⟩, _⟩, _ => True
      | ⟨⟨⟨_, RTypeShape.arrow⟩, _⟩, _⟩, ih =>
        ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)) ∧
          ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))
      | ⟨⟨⟨_, RTypeShape.omega⟩, _⟩, _⟩, _ => False)
    t.1

/-- The tower-sort predicate agrees with the legacy predicate across the
bridge (Leivant III section 2.4(3)). -/
@[simp] theorem rTypeSliceEquiv_isTower (t : RType') :
    RType'.IsTower t = RType.IsTower (rTypeSliceEquiv t) := by
  refine FreeAlg'.induction
    (motive := fun t => RType'.IsTower t = RType.IsTower (rTypeSliceEquiv t))
    (fun b sub ih => ?_) t
  change RType'.IsTower (FreeAlg'.mk b sub)
    = RType.IsTower (freeAlgSliceEquiv rTypeSig (FreeAlg'.mk b sub))
  rw [freeAlgSliceEquiv_mk]
  simp only [RType'.IsTower] at ih ⊢
  simp only [FreeAlg'.mk]
  rw [SlicePFunctor.W.recProp_mk]
  cases b
  · rfl
  · rfl
  · exact ih ⟨0, by decide⟩

/-- The simple-type predicate agrees with the legacy predicate across the
bridge (Leivant III section 4.2). -/
@[simp] theorem rTypeSliceEquiv_isSimple (t : RType') :
    RType'.IsSimple t = RType.IsSimple (rTypeSliceEquiv t) := by
  refine FreeAlg'.induction
    (motive := fun t => RType'.IsSimple t = RType.IsSimple (rTypeSliceEquiv t))
    (fun b sub ih => ?_) t
  change RType'.IsSimple (FreeAlg'.mk b sub)
    = RType.IsSimple (freeAlgSliceEquiv rTypeSig (FreeAlg'.mk b sub))
  rw [freeAlgSliceEquiv_mk]
  simp only [RType'.IsSimple] at ih ⊢
  simp only [FreeAlg'.mk]
  rw [SlicePFunctor.W.recProp_mk]
  cases b
  · rfl
  · exact congrArg₂ And (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
  · rfl

/-- The tower sorts `Omega^m o` on the slice `W`-type (Leivant III section
2.4(3)): the `m`-fold iterate of `omega` on `o`. Built from the `RType'`
constructors by recursion on `Nat`. -/
def RType'.tower : Nat → RType'
  | 0 => RType'.o
  | n + 1 => RType'.omega (RType'.tower n)

/-- The tower sorts agree with the legacy tower sorts across the bridge
(Leivant III section 2.4(3)). -/
@[simp] theorem rTypeSliceEquiv_tower (n : Nat) :
    rTypeSliceEquiv (RType'.tower n) = RType.tower n := by
  induction n with
  | zero => simp only [RType'.tower, RType.tower, rTypeSliceEquiv_o]
  | succ n ih => simp only [RType'.tower, RType.tower, rTypeSliceEquiv_omega, ih]

/-- The denotation of an r-type on the slice `W`-type over a carrier (Leivant
III section 2.7): every object sort denotes a copy of the carrier, and each
arrow denotes the function space of its subterms' denotations. `Type`-valued,
native via `SlicePFunctor.W.elim` at `Y := Type`. -/
def RType'.interp (carrier : Type) (t : RType') : Type :=
  SlicePFunctor.W.elim (toSlice rTypeSig.polyEndo) Type (fun _ => PUnit.unit)
    (fun node => match node with
      | ⟨⟨⟨_, RTypeShape.o⟩, _⟩, _⟩ => carrier
      | ⟨⟨⟨_, RTypeShape.arrow⟩, ch⟩, _⟩ =>
        ch (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)) →
          ch (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))
      | ⟨⟨⟨_, RTypeShape.omega⟩, _⟩, _⟩ => carrier)
    (Subsingleton.elim _ _)
    t.1

/-- The denotation agrees with the legacy denotation across the bridge
(Leivant III section 2.7). -/
@[simp] theorem rTypeSliceEquiv_interp (C : Type) (t : RType') :
    RType'.interp C t = RType.interp C (rTypeSliceEquiv t) := by
  refine FreeAlg'.induction
    (motive := fun t => RType'.interp C t = RType.interp C (rTypeSliceEquiv t))
    (fun b sub ih => ?_) t
  change RType'.interp C (FreeAlg'.mk b sub)
    = RType.interp C (freeAlgSliceEquiv rTypeSig (FreeAlg'.mk b sub))
  rw [freeAlgSliceEquiv_mk]
  simp only [RType'.interp] at ih ⊢
  simp only [FreeAlg'.mk]
  rw [SlicePFunctor.W.elim_mk]
  cases b
  · rfl
  · exact congrArg₂ (fun a b => a → b) (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
  · rfl

/-- The denotation of an object sort is a copy of the carrier (Leivant III
section 2.7): for any `t` with `t.IsObj`, `RType'.interp C t = C`. Mirror of
the legacy `RType.interp_isObj`. -/
theorem RType'.interp_isObj (C : Type) {t : RType'} (h : t.IsObj) :
    RType'.interp C t = C := by
  refine FreeAlg'.induction
    (motive := fun t => RType'.IsObj t → RType'.interp C t = C) (fun b sub _ h => ?_) t h
  simp only [RType'.IsObj, RType'.shape_mk] at h
  simp only [RType'.interp, FreeAlg'.mk]
  rw [SlicePFunctor.W.elim_mk]
  cases b
  · rfl
  · rcases h with h | h <;> exact absurd h (by decide)
  · rfl

/-- The primed paramorphism `FreeAlg'.recurse` agrees with the legacy
`FreeAlg.recurse` across the bridge equivalence (Leivant III section 2.1):
running the primed recurrence on `x` with a legacy step function `g` — whose
subterm reads on the primed side are pushed forward by `freeAlgSliceEquiv A`
— equals running the legacy recurrence on the image `freeAlgSliceEquiv A x`.
By `FreeAlg'.induction` with the reduction rules of both recurrences at a
constructor node and `mk`-naturality of `freeAlgSliceEquiv`. -/
theorem freeAlgSliceEquiv_recurse {A : AlgSig} {P C : Type}
    (g : (b : A.B) → P → (Fin (A.ar b) → FreeAlg A) → (Fin (A.ar b) → C) → C)
    (p : P) (x : FreeAlg' A) :
    FreeAlg'.recurse
        (fun b q sub rec => g b q (fun e => freeAlgSliceEquiv A (sub e)) rec) p x
      = FreeAlg.recurse g p (freeAlgSliceEquiv A x) := by
  refine FreeAlg'.induction
    (motive := fun x =>
      FreeAlg'.recurse
          (fun b q sub rec => g b q (fun e => freeAlgSliceEquiv A (sub e)) rec) p x
        = FreeAlg.recurse g p (freeAlgSliceEquiv A x))
    (fun b sub ih => ?_) x
  dsimp only
  rw [FreeAlg'.recurse_mk, freeAlgSliceEquiv_mk, FreeAlg.recurse_mk]
  exact congrArg (g b p (fun e => freeAlgSliceEquiv A (sub e))) (funext ih)

/-- The carrier bridge (Leivant III section 2.7): the equivalence between the
primed denotation `RType'.interp (FreeAlg' A) t'` and the legacy denotation
`RType.interp (FreeAlg A)` at the translated r-type. The composite of the
denotation-agreement cast `rTypeSliceEquiv_interp` with the denotation
congruence `RType.interpCongr` along the free-algebra bridge equivalence
`freeAlgSliceEquiv`. The single named carrier bridge for the identifier
interp-agreement proofs. -/
def carrierSliceEquiv (A : AlgSig) (t' : RType') :
    RType'.interp (FreeAlg' A) t' ≃ RType.interp (FreeAlg A) (rTypeSliceEquiv t') :=
  (Equiv.cast (rTypeSliceEquiv_interp (FreeAlg' A) t')).trans
    (RType.interpCongr (freeAlgSliceEquiv A) (rTypeSliceEquiv t'))

/-- At an object sort the carrier bridge computes to the free-algebra bridge
equivalence, read through the object-sort denotation equalities (Leivant III
section 2.7): for `t'.IsObj`, `carrierSliceEquiv A t'` transports to
`freeAlgSliceEquiv A`. By `RType.interpCongr_isObj` together with the
composition of the denotation casts. -/
theorem carrierSliceEquiv_isObj {A : AlgSig} {t' : RType'} (h : t'.IsObj)
    (x : RType'.interp (FreeAlg' A) t') :
    cast (RType.interp_isObj (FreeAlg A) (cast (rTypeSliceEquiv_isObj t') h))
        (carrierSliceEquiv A t' x)
      = freeAlgSliceEquiv A (cast (RType'.interp_isObj (FreeAlg' A) h) x) := by
  simp only [carrierSliceEquiv, Equiv.trans_apply, Equiv.cast_apply]
  rw [RType.interpCongr_isObj (freeAlgSliceEquiv A) (cast (rTypeSliceEquiv_isObj t') h)]
  congr 1
  simp only [cast_cast]

/-- Transport of a function along an equality of function types acts as
transport of the argument and of the value. -/
theorem cast_arrow {α β γ δ : Type} (hα : α = γ) (hβ : β = δ) (h : (α → β) = (γ → δ))
    (f : α → β) (x : α) : cast h f (cast hα x) = cast hβ (f x) := by
  subst hα; subst hβ; rfl

/-- The carrier bridge at an arrow sort: the bridge image of a function,
read at the translated arrow, is the conjugate of the function by the bridges
at the domain and codomain. -/
theorem carrierSliceEquiv_arrow {A : AlgSig} (a b : RType')
    (f : RType'.interp (FreeAlg' A) (RType'.arrow a b))
    (x : RType'.interp (FreeAlg' A) a) :
    cast (congrArg (RType.interp (FreeAlg A)) (rTypeSliceEquiv_arrow a b))
        (carrierSliceEquiv A (RType'.arrow a b) f) (carrierSliceEquiv A a x)
      = carrierSliceEquiv A b (f x) := by
  change cast (congrArg (RType.interp (FreeAlg A)) (rTypeSliceEquiv_arrow a b))
      (RType.interpCongr (freeAlgSliceEquiv A) (rTypeSliceEquiv (RType'.arrow a b))
        (cast (rTypeSliceEquiv_interp (FreeAlg' A) (RType'.arrow a b)) f))
      (RType.interpCongr (freeAlgSliceEquiv A) (rTypeSliceEquiv a)
        (cast (rTypeSliceEquiv_interp (FreeAlg' A) a) x))
    = RType.interpCongr (freeAlgSliceEquiv A) (rTypeSliceEquiv b)
        (cast (rTypeSliceEquiv_interp (FreeAlg' A) b) (f x))
  rw [interpCongr_cast (freeAlgSliceEquiv A) (rTypeSliceEquiv_arrow a b),
    interpCongr_arrow, Equiv.symm_apply_apply]
  refine congrArg (RType.interpCongr (freeAlgSliceEquiv A) (rTypeSliceEquiv b)) ?_
  exact cast_arrow (rTypeSliceEquiv_interp (FreeAlg' A) a)
    (rTypeSliceEquiv_interp (FreeAlg' A) b) _ f x

/-- The base object sort is an object sort. -/
theorem isObj_o' : RType'.IsObj RType'.o :=
  Or.inl (RType'.shape_mk RTypeShape.o Fin.elim0)

/-- Every `Omega` sort is an object sort. -/
theorem isObj_omega' (t' : RType') : RType'.IsObj (RType'.omega t') :=
  Or.inr (RType'.shape_mk RTypeShape.omega ![t'])

/-- The carrier bridge at the base object sort computes to the free-algebra
bridge: both denotations are copies of the base carrier. -/
theorem carrierSliceEquiv_o {A : AlgSig} (x : RType'.interp (FreeAlg' A) RType'.o) :
    cast (congrArg (RType.interp (FreeAlg A)) rTypeSliceEquiv_o)
        (carrierSliceEquiv A RType'.o x)
      = freeAlgSliceEquiv A x :=
  carrierSliceEquiv_isObj isObj_o' x

/-- The carrier bridge commutes with transport of its argument along a sort
equality, heterogeneously. -/
theorem carrierSliceEquiv_cast_heq {A : AlgSig} {s t : RType'} (h : s = t)
    (x : RType'.interp (FreeAlg' A) s) :
    HEq (carrierSliceEquiv A t (cast (congrArg (RType'.interp (FreeAlg' A)) h) x))
      (carrierSliceEquiv A s x) := by
  subst h; rfl

end GebLean.Ramified.Polynomial

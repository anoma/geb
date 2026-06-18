import GebLean.Utilities.EraDiophantine
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

/-!
# Per-coordinate degree certificate for the `diophOf` reduction

The cube-sum factorisation `cubeSum_factor` and Corollary 3.6 of
arXiv:2407.12928 apply to a single-fold sum-of-squares Diophantine system
whose `sqDist`-squared monomials are simple exponential polynomials of
per-coordinate degree at most `2`. This file certifies that the systems
produced by `diophOf` (`GebLean/Utilities/EraDiophantine.lean`) meet that
hypothesis: every `SimpleMonomial` occurring in a `diophOf`-reachable system
carries a per-coordinate polynomial exponent of `0`, hence per-coordinate
polynomial degree at most `1`. After the `sqDist` squaring this becomes at
most `2`, the precise input the factorisation requires.

This validates "route (ii)" of the Task-6.4 reduction: the per-coordinate
degree bound is read off structurally from the monomial data, so the full
Lemma 3.5 chain-variable reduction of arXiv:2407.12928 is not needed.

## Main definitions

* `SimpleMonomial.PolyExpZero`, `SimpleSum.PolyExpZero`,
  `SosTerm.PolyExpZero`, `SosSystem.PolyExpZero` — the structural predicate
  asserting that every monomial occurring in the object has an identically
  zero per-coordinate polynomial exponent.
* `ZMonomial` — the signed simple-exponential monomial, the `ℤ`-valued
  reflection of Expression (6) of arXiv:2407.12928 specialised to base `2`,
  with `ZMonomial.eval` its `ℤ`-valued denotation and `ZMonomial.evalNat` its
  unsigned `ℕ` magnitude.
* `ZMonomial.mul` — the product of two signed simple-exponential monomials,
  formed by sign exclusive-or, coefficient product, per-variable
  exponential-coefficient sum (the shared base-`2` merge), and per-variable
  polynomial-exponent sum.
* `ETm.IsVarProduct` — the restricted coefficient grammar of a `diophOf`
  monomial: an `ETm` built from `Era.one`, single variables, and `*ᵉ`.
* `ETm.extractCubeDegree` — the cube-coordinate degree extraction: it moves the
  cube-coordinate variable powers out of a coefficient (over `Fin (p + k)`) into
  a degree vector `Fin k → ℕ`, leaving a residual coefficient.
* `SimpleMonomial.CoeffVarProduct`, `SimpleSum.CoeffVarProduct`,
  `SosTerm.CoeffVarProduct`, `SosSystem.CoeffVarProduct` — the structural
  predicate asserting that every monomial coefficient occurring in the object
  lies in the `ETm.IsVarProduct` grammar.
* `SimpleMonomial.BasePaired`, `SimpleSum.BasePaired`, `SosTerm.BasePaired`,
  `SosSystem.BasePaired` — the structural predicate asserting that every
  monomial's per-slot exponential data is either trivial (`expBase = .zero`,
  `expCoeff = .zero`) or the base-`2` shape (`expBase = .succ Era.one`,
  `expCoeff = Era.one`).
* `SimpleMonomial.toZ`, `SimpleSum.toZ` — the lift of a `diophOf` monomial (and
  simple sum) over `Fin (p + k)` to the signed `ZMonomial` reflection, moving the
  cube-coordinate polynomial degree of the coefficient into the `polyExp` field.
* `ZMonomial.listMul` — the list of all pairwise products of two `ZMonomial`
  lists, the term-level distribution of `(∑ L₁) · (∑ L₂)`.
* `ZMonomial.negDouble` — sign-flip and coefficient-doubling of a `ZMonomial`,
  realising the `−2 P Q` cross-term of a truncated squared distance.
* `ZMonomial.weaken` — re-index a signed simple-exponential monomial along a
  variable map `f`, renaming the coefficient and per-variable exponential
  coefficients and reading each target slot off the `preimage` of `f`.
* `SosTerm.toZ`, `SosSystem.toZ` — the lift of a `diophOf` sum-of-squares atom
  (and system) over `Fin (p + k)` to a flat `ZMonomial` list: a `sqDist P Q` atom
  expands to `P² + Q² − 2 P Q`, a `prod s t` atom to the pairwise product.
* `chainIdx`, `cubeSlot`, `chainSlot`, `castAddEmb` — the index plumbing of the
  Lemma 3.5 chain-variable reduction. The enlarged variable scope is
  `Fin (p + k + k * d)`, with `p` parameter slots, `k` cube-coordinate slots, and
  a trailing `k * d`-block of chain variables laid out as a `Fin k × Fin d`
  rectangle. `chainIdx c i` is the rectangle's flat index (via mathlib's
  `finProdFinEquiv`); `cubeSlot c` is the cube coordinate `c`'s slot; `chainSlot
  c i` is the chain cell `(c, i)`'s slot; `castAddEmb` embeds the old scope
  `Fin (p + k)`.
* `ZMonomial.varMon`, `ZMonomial.negVarMon`, `ZMonomial.mulVarMon` — the small signed
  monomial constructors `x_j`, `−x_j`, and `x_j · x_{j'}` (the last for distinct slots)
  out of which the chain equations are built.
* `ZMonomial.maxCubeDegree` — the maximum cube-coordinate polynomial degree over a list
  of monomials, the global chain length `h` of Lemma 3.5.
* `chainEqList`, `chainEqs` — the chain-equation left side `S_{c,i}` (a two-monomial
  signed difference) and the full squared chain-equation block (every `S_{c,i}²`).
* `chainSub` — lower each cube slot's polynomial degree to `0`, depositing the removed
  degree at the matching chain slot (the substitution `x_c^{i+1} ↦ y_{c,i+1}`).
* `ChainHolds` — the sub-domain predicate `ρ (chainSlot c i) = ρ (cubeSlot c) ^ (i + 1)`
  on which `chainSub` preserves the monomial denotation.

## Main statements

* `SimpleMonomial.weaken_polyExpZero`, `SimpleSum.weaken_polyExpZero`,
  `SosTerm.weaken_polyExpZero`, `SosSystem.weaken_polyExpZero` — the
  predicate is preserved by re-indexing along any variable map.
* `diophVar_polyExpZero`, `diophZero_polyExpZero`, `diophSucc_polyExpZero`,
  `diophAdd_polyExpZero`, `diophMul_polyExpZero`, `diophPow2_polyExpZero`,
  `diophTsub_polyExpZero`, `diophMod_polyExpZero`, `diophDiv_polyExpZero`,
  `diophOne_polyExpZero`, `diophPow_polyExpZero` — each combinator builds a
  system satisfying the predicate from sub-systems satisfying it.
* `diophOf_polyExpZero` — every system `(diophOf t).sys` satisfies the
  predicate, by induction over the term `t`.
* `diophOf_polyExp_le_one` — the headline certificate: every monomial
  occurring in `(diophOf t).sys` has per-coordinate polynomial exponent at
  most `1`.
* `ZMonomial.evalNat_cast`, `ZMonomial.eval_eq` — the bridge between the
  `ℤ`-valued `eval` and the `ℕ`-valued `evalNat`: the magnitude cast to `ℤ` is
  the absolute value of `eval`, and `eval` is `evalNat` signed by `sign`.
* `ZMonomial.mul_eval` — the `ℤ`-valued denotation is multiplicative: the
  denotation of `ZMonomial.mul` is the product of the denotations.
* `ETm.IsVarProduct.weaken` — the coefficient grammar is closed under
  variable-renaming substitution.
* `ETm.extractCubeDegree_eval` — under the coefficient grammar, evaluating a
  coefficient at an appended context factors as the residual coefficient times
  the cube-coordinate monomial `∏ c, (a c) ^ (degree c)`.
* `diophOf_coeffVarProduct` — every monomial coefficient in `(diophOf t).sys`
  lies in the `ETm.IsVarProduct` grammar, by induction over the term `t`.
* `diophOf_basePaired` — every monomial in `(diophOf t).sys` is base-paired, so
  each per-slot exponential factor is either `1` or `2 ^ ρ i`.
* `SimpleMonomial.toZ_eval`, `SimpleSum.toZ_eval` — under the coefficient-grammar
  and base-paired predicates, the `ℤ`-valued denotation of the lift at an appended
  context `Fin.append ctx a` equals the natural-number `SimpleMonomial` (resp.
  `SimpleSum`) value cast to `ℤ`.
* `ZMonomial.listMul_eval` — the pairwise-product list's denotation sum
  factorises as the product of the two factors' denotation sums.
* `ZMonomial.negDouble_eval` — the denotation of `negDouble mon` is
  `−(2 · mon.eval ρ)`.
* `ZMonomial.weaken_eval`, `ZMonomial.weaken_list_eval` — for injective `f`,
  the denotation of `mon.weaken f` at `ρ'` equals that of `mon` at `ρ' ∘ f`,
  with the list corollary summing termwise.
* `SosTerm.cast_sqDist` — the truncated squared distance cast to `ℤ` is the honest
  quadratic `x² + y² − 2 x y`.
* `SosTerm.toZ_eval`, `SosSystem.toZ_eval` — under the coefficient-grammar and
  base-paired predicates, the sum of the `ℤ`-valued denotations of the lift at an
  appended context equals the natural-number `SosTerm` (resp. `SosSystem`) value
  cast to `ℤ`.
* `chainIdx_val`, `chainIdx_injective` — the `finProdFinEquiv` flattening value
  `i.val + d * c.val` and the injectivity of `chainIdx`.
* `castAddEmb_injective`, `cubeSlot_injective`, `chainSlot_injective` — the index
  helpers are injective.
* `cubeSlot_ne_chainSlot`, `castAddEmb_ne_chainSlot` — cube slots and old-scope
  embeddings are disjoint from chain slots.
* `preimage_castAddEmb_apply`, `preimage_castAddEmb_chainSlot` — the `preimage`
  search recovers the source index of an embedded index and returns `none` on a
  chain slot.
* `ZMonomial.varMon_eval`, `ZMonomial.negVarMon_eval`, `ZMonomial.mulVarMon_eval` — the
  small constructors denote `ρ j`, `−ρ j`, and (for distinct slots) `ρ j · ρ j'`.
* `ZMonomial.le_maxCubeDegree` — every monomial's cube-coordinate degree is at most
  `ZMonomial.maxCubeDegree`.
* `chainEqList_polyExp_le_one`, `chainEqs_degree` — each `chainEqList` monomial has
  per-slot polynomial degree at most `1`, hence each `chainEqs` monomial at most `2`.
* `chainSub_polyExp_cubeSlot`, `chainSub_polyExp_chainSlot`, `chainSub_polyExp_param`,
  `chainSub_polyExp_le_one` — the per-slot behaviour of `chainSub` (cube → `0`, chain →
  base plus a single deposit, parameter unchanged) and the resulting degree bound.
* `chainSub_polyProd`, `chainSub_eval` — on the `ChainHolds` sub-domain, with cube
  degrees bounded by the chain length, `chainSub` preserves the polynomial-factor
  product, hence the whole monomial denotation.

## Implementation notes

Route-(ii) decision (Task 6.4b, Step 1). The four monomial atoms reachable
from `diophOf` are `SimpleMonomial.var` (value `ρ j`),
`SimpleMonomial.one` (value `1`), `SimpleMonomial.mulVars` (value
`ρ j · ρ k`), and `SimpleMonomial.pow2Var` (value `2 ^ ρ j`). All four set
`polyExp := fun _ => 0`. The only degree-`2` atom, `mulVars`, encodes its
degree not through `polyExp` but through two distinct witness slots `j ≠ k`,
each entering its `coeff` term to the first power; the per-coordinate
polynomial exponent therefore remains `0`. Re-indexing (`SimpleMonomial.weaken`
and the splice/extend wrappers built on it) reads each target index's
`polyExp` off the source monomial's `polyExp`, defaulting to `0` off the image
of the variable map, so it preserves the zero-exponent property. The
certificate is consequently a structural induction over the `diophOf`
combinators, with no appeal to the values denoted.

The certificate is stated and proved as `polyExp i = 0` (`PolyExpZero`), the
exact property that holds, and the `≤ 1` headline form `diophOf_polyExp_le_one`
is derived from it. The `sqDist` squaring that the consuming factorisation
applies raises the per-coordinate degree from this `≤ 1` to `≤ 2`.

`ZMonomial` reflects Expression (6) of arXiv:2407.12928 with the single
exponential base specialised to `2`: every exponential reachable from a
`diophOf` atom has base `2`, so no per-variable base field is stored. This
specialisation is a standing assumption of the reflection. Should a `diophOf`
atom with a different exponential base be introduced, the base-`2` normal form
no longer covers all atoms, and this phase must regain an `expBase` field on
`ZMonomial` (mirroring `SimpleMonomial.expBase`) before the reflection is
sound again.

## References

* Prunescu, arXiv:2407.12928, Lemma 3.5 (chain-variable reduction, here
  avoided) and Corollary 3.6 (the single-fold factorisation requiring
  per-coordinate degree at most `2`); Expression (6) (the simple exponential
  monomial form).
* Local copy:
  `/home/terence/wingeb/representation-number-theoretic-functions-arithmetic-terms.pdf`.

## Tags

elementary recursive, Diophantine, degree, simple exponential polynomial
-/

namespace GebLean

open Era

/-- A simple monomial has identically zero per-coordinate polynomial exponent:
every `polyExp i` is `0`, so the polynomial-factor product `∏ᵢ (ρ i) ^ (polyExp i)`
is trivial and the monomial contributes per-coordinate polynomial degree `0`. -/
def SimpleMonomial.PolyExpZero {m : ℕ} (mon : SimpleMonomial m) : Prop :=
  ∀ i, mon.polyExp i = 0

/-- A simple sum has the zero-exponent property when every one of its
monomials does. -/
def SimpleSum.PolyExpZero {m : ℕ} (p : SimpleSum m) : Prop :=
  ∀ mon ∈ p, mon.PolyExpZero

mutual
/-- A sum-of-squares atom has the zero-exponent property: a `sqDist P Q` atom
when both simple sums do, a `prod s t` atom when both sub-systems do. -/
def SosTerm.PolyExpZero {m : ℕ} (a : SosTerm m) : Prop :=
  match a with
  | .sqDist P Q => P.PolyExpZero ∧ Q.PolyExpZero
  | .prod s t => SosSystem.PolyExpZero s ∧ SosSystem.PolyExpZero t
--
/-- A sum-of-squares system has the zero-exponent property when every one of
its atoms does. -/
def SosSystem.PolyExpZero {m : ℕ} (s : SosSystem m) : Prop :=
  match s with
  | [] => True
  | a :: rest => a.PolyExpZero ∧ SosSystem.PolyExpZero rest
end

/-- The zero-exponent property of a concatenated system is the conjunction of
the parts' properties. -/
theorem SosSystem.polyExpZero_append {m : ℕ} (s t : SosSystem m) :
    (s ++ t).PolyExpZero ↔ s.PolyExpZero ∧ t.PolyExpZero := by
  induction s with
  | nil => simp only [List.nil_append, SosSystem.PolyExpZero, true_and]
  | cons a rest ih =>
    rw [List.cons_append, SosSystem.PolyExpZero, SosSystem.PolyExpZero, ih, and_assoc]

/-- The empty simple sum has the zero-exponent property vacuously. -/
theorem SimpleSum.nil_polyExpZero {m : ℕ} :
    SimpleSum.PolyExpZero ([] : SimpleSum m) :=
  fun _ hmon => by simp only [List.not_mem_nil] at hmon

/-- A simple sum prepended with a zero-exponent monomial keeps the property when
its tail does. -/
theorem SimpleSum.cons_polyExpZero {m : ℕ} {mon : SimpleMonomial m} {p : SimpleSum m}
    (hmon : mon.PolyExpZero) (hp : SimpleSum.PolyExpZero p) :
    SimpleSum.PolyExpZero (mon :: p) := by
  intro mon' hmon'
  rcases List.mem_cons.mp hmon' with h | h
  · rw [h]; exact hmon
  · exact hp mon' h

/-- A singleton simple sum has the zero-exponent property when its monomial
does. -/
theorem SimpleSum.singleton_polyExpZero {m : ℕ} {mon : SimpleMonomial m}
    (hmon : mon.PolyExpZero) : SimpleSum.PolyExpZero ([mon] : SimpleSum m) :=
  SimpleSum.cons_polyExpZero hmon SimpleSum.nil_polyExpZero

/-- A squared-distance atom has the zero-exponent property when both its simple
sums do. -/
theorem SosTerm.sqDist_polyExpZero {m : ℕ} {P Q : SimpleSum m}
    (hP : SimpleSum.PolyExpZero P) (hQ : SimpleSum.PolyExpZero Q) :
    (SosTerm.sqDist P Q).PolyExpZero :=
  ⟨hP, hQ⟩

/-- A product atom has the zero-exponent property when both its sub-systems
do. -/
theorem SosTerm.prod_polyExpZero {m : ℕ} {s t : SosSystem m}
    (hs : SosSystem.PolyExpZero s) (ht : SosSystem.PolyExpZero t) :
    (SosTerm.prod s t).PolyExpZero :=
  ⟨hs, ht⟩

/-- The empty sum-of-squares system has the zero-exponent property vacuously. -/
theorem SosSystem.nil_polyExpZero {m : ℕ} :
    SosSystem.PolyExpZero ([] : SosSystem m) := True.intro

/-- A sum-of-squares system prepended with a zero-exponent atom keeps the
property when its tail does. -/
theorem SosSystem.cons_polyExpZero {m : ℕ} {a : SosTerm m} {rest : SosSystem m}
    (ha : a.PolyExpZero) (hrest : SosSystem.PolyExpZero rest) :
    SosSystem.PolyExpZero (a :: rest) :=
  ⟨ha, hrest⟩

/-- The variable monomial has the zero-exponent property. -/
theorem SimpleMonomial.var_polyExpZero {m : ℕ} (j : Fin m) :
    (SimpleMonomial.var j).PolyExpZero := fun _ => rfl

/-- The constant monomial has the zero-exponent property. -/
theorem SimpleMonomial.one_polyExpZero {m : ℕ} :
    (SimpleMonomial.one (m := m)).PolyExpZero := fun _ => rfl

/-- The product monomial has the zero-exponent property. -/
theorem SimpleMonomial.mulVars_polyExpZero {m : ℕ} (j k : Fin m) :
    (SimpleMonomial.mulVars j k).PolyExpZero := fun _ => rfl

/-- The base-`2` power monomial has the zero-exponent property. -/
theorem SimpleMonomial.pow2Var_polyExpZero {m : ℕ} (j : Fin m) :
    (SimpleMonomial.pow2Var j).PolyExpZero := fun _ => rfl

/-- Re-indexing a monomial preserves the zero-exponent property: each target
index's `polyExp` is read off the source `polyExp` or defaults to `0`. -/
theorem SimpleMonomial.weaken_polyExpZero {m m' : ℕ} {mon : SimpleMonomial m}
    (h : mon.PolyExpZero) (f : Fin m → Fin m') : (mon.weaken f).PolyExpZero := by
  intro j
  change (match preimage f j with
    | some i => mon.polyExp i
    | none => 0) = 0
  cases preimage f j with
  | none => rfl
  | some i => exact h i

/-- Re-indexing a simple sum preserves the zero-exponent property. -/
theorem SimpleSum.weaken_polyExpZero {m m' : ℕ} {p : SimpleSum m}
    (h : p.PolyExpZero) (f : Fin m → Fin m') : (p.weaken f).PolyExpZero := by
  intro mon hmon
  unfold SimpleSum.weaken at hmon
  rw [List.mem_map] at hmon
  obtain ⟨mon₀, hmon₀, rfl⟩ := hmon
  exact SimpleMonomial.weaken_polyExpZero (h mon₀ hmon₀) f

mutual
/-- Re-indexing a sum-of-squares atom preserves the zero-exponent property. -/
theorem SosTerm.weaken_polyExpZero {m m' : ℕ} {a : SosTerm m}
    (h : a.PolyExpZero) (f : Fin m → Fin m') : (a.weaken f).PolyExpZero := by
  match a with
  | .sqDist P Q =>
    rw [SosTerm.weaken]
    exact SosTerm.sqDist_polyExpZero (SimpleSum.weaken_polyExpZero h.1 f)
      (SimpleSum.weaken_polyExpZero h.2 f)
  | .prod s t =>
    rw [SosTerm.weaken]
    exact SosTerm.prod_polyExpZero (SosSystem.weaken_polyExpZero h.1 f)
      (SosSystem.weaken_polyExpZero h.2 f)
--
/-- Re-indexing a sum-of-squares system preserves the zero-exponent property. -/
theorem SosSystem.weaken_polyExpZero {m m' : ℕ} {s : SosSystem m}
    (h : s.PolyExpZero) (f : Fin m → Fin m') : (s.weaken f).PolyExpZero := by
  match s with
  | [] =>
    rw [SosSystem.weaken]
    exact SosSystem.nil_polyExpZero
  | a :: rest =>
    rw [SosSystem.weaken]
    exact SosSystem.cons_polyExpZero (SosTerm.weaken_polyExpZero h.1 f)
      (SosSystem.weaken_polyExpZero h.2 f)
end

/-- The spliced system preserves the zero-exponent property: it is an instance
of `SosSystem.weaken_polyExpZero`. -/
theorem SosSystem.spliceWeaken_polyExpZero {n wSub wComp : ℕ}
    {s : SosSystem (n + 1 + wSub)} (h : s.PolyExpZero) (outSlot : Fin wComp)
    (witEmb : Fin wSub → Fin wComp) :
    (s.spliceWeaken outSlot witEmb).PolyExpZero :=
  SosSystem.weaken_polyExpZero h (spliceEmb outSlot witEmb)

/-- The binary spliced system has the zero-exponent property when both
sub-systems do. -/
theorem binSplicedSys_polyExpZero {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.PolyExpZero) (h2 : sub2.sys.PolyExpZero) :
    (binSplicedSys sub1 sub2).PolyExpZero := by
  rw [binSplicedSys, SosSystem.polyExpZero_append]
  exact ⟨SosSystem.spliceWeaken_polyExpZero h1 binOutSlot1 binWitEmb1,
    SosSystem.spliceWeaken_polyExpZero h2 binOutSlot2 binWitEmb2⟩

/-- The extended binary spliced system has the zero-exponent property when both
sub-systems do. -/
theorem binExtSplicedSys_polyExpZero {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.PolyExpZero) (h2 : sub2.sys.PolyExpZero) (k : ℕ) :
    (binExtSplicedSys sub1 sub2 k).PolyExpZero :=
  SosSystem.weaken_polyExpZero (binSplicedSys_polyExpZero h1 h2) binExtEmb

/-- `diophVar i` builds a system with the zero-exponent property. -/
theorem diophVar_polyExpZero {n : ℕ} (i : Fin n) : (diophVar i).sys.PolyExpZero :=
  SosSystem.cons_polyExpZero
    (SosTerm.sqDist_polyExpZero
      (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _))
      (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _)))
    SosSystem.nil_polyExpZero

/-- `diophZero` builds a system with the zero-exponent property. -/
theorem diophZero_polyExpZero {n : ℕ} : (diophZero (n := n)).sys.PolyExpZero :=
  SosSystem.cons_polyExpZero
    (SosTerm.sqDist_polyExpZero SimpleSum.nil_polyExpZero
      (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _)))
    SosSystem.nil_polyExpZero

/-- `diophSucc sub` builds a system with the zero-exponent property when `sub`
does. -/
theorem diophSucc_polyExpZero {n : ℕ} {sub : DiophEnc n} (h : sub.sys.PolyExpZero) :
    (diophSucc sub).sys.PolyExpZero :=
  (SosSystem.polyExpZero_append _ _).mpr
    ⟨SosSystem.spliceWeaken_polyExpZero h (Fin.last sub.witArity) succWitEmb,
      SosSystem.cons_polyExpZero
        (SosTerm.sqDist_polyExpZero
          (SimpleSum.cons_polyExpZero (SimpleMonomial.var_polyExpZero _)
            (SimpleSum.singleton_polyExpZero SimpleMonomial.one_polyExpZero))
          (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _)))
        SosSystem.nil_polyExpZero⟩

/-- `diophAdd sub1 sub2` builds a system with the zero-exponent property when
both sub-systems do. -/
theorem diophAdd_polyExpZero {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.PolyExpZero) (h2 : sub2.sys.PolyExpZero) :
    (diophAdd sub1 sub2).sys.PolyExpZero :=
  (SosSystem.polyExpZero_append _ _).mpr
    ⟨binSplicedSys_polyExpZero h1 h2,
      SosSystem.cons_polyExpZero
        (SosTerm.sqDist_polyExpZero
          (SimpleSum.cons_polyExpZero (SimpleMonomial.var_polyExpZero _)
            (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _)))
          (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _)))
        SosSystem.nil_polyExpZero⟩

/-- `diophMul sub1 sub2` builds a system with the zero-exponent property when
both sub-systems do. -/
theorem diophMul_polyExpZero {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.PolyExpZero) (h2 : sub2.sys.PolyExpZero) :
    (diophMul sub1 sub2).sys.PolyExpZero :=
  (SosSystem.polyExpZero_append _ _).mpr
    ⟨binSplicedSys_polyExpZero h1 h2,
      SosSystem.cons_polyExpZero
        (SosTerm.sqDist_polyExpZero
          (SimpleSum.singleton_polyExpZero (SimpleMonomial.mulVars_polyExpZero _ _))
          (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _)))
        SosSystem.nil_polyExpZero⟩

/-- `diophPow2 sub` builds a system with the zero-exponent property when `sub`
does. -/
theorem diophPow2_polyExpZero {n : ℕ} {sub : DiophEnc n} (h : sub.sys.PolyExpZero) :
    (diophPow2 sub).sys.PolyExpZero :=
  (SosSystem.polyExpZero_append _ _).mpr
    ⟨SosSystem.spliceWeaken_polyExpZero h (Fin.last sub.witArity) succWitEmb,
      SosSystem.cons_polyExpZero
        (SosTerm.sqDist_polyExpZero
          (SimpleSum.singleton_polyExpZero (SimpleMonomial.pow2Var_polyExpZero _))
          (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _)))
        SosSystem.nil_polyExpZero⟩

/-- `diophTsub sub1 sub2` builds a system with the zero-exponent property when
both sub-systems do. -/
theorem diophTsub_polyExpZero {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.PolyExpZero) (h2 : sub2.sys.PolyExpZero) :
    (diophTsub sub1 sub2).sys.PolyExpZero :=
  (SosSystem.polyExpZero_append _ _).mpr
    ⟨binExtSplicedSys_polyExpZero h1 h2 1,
      SosSystem.cons_polyExpZero
        (SosTerm.sqDist_polyExpZero
          (SimpleSum.cons_polyExpZero (SimpleMonomial.var_polyExpZero _)
            (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _)))
          (SimpleSum.cons_polyExpZero (SimpleMonomial.var_polyExpZero _)
            (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _))))
        (SosSystem.cons_polyExpZero
          (SosTerm.sqDist_polyExpZero
            (SimpleSum.singleton_polyExpZero (SimpleMonomial.mulVars_polyExpZero _ _))
            SimpleSum.nil_polyExpZero)
          SosSystem.nil_polyExpZero)⟩

/-- `diophMod sub1 sub2` builds a system with the zero-exponent property when
both sub-systems do. -/
theorem diophMod_polyExpZero {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.PolyExpZero) (h2 : sub2.sys.PolyExpZero) :
    (diophMod sub1 sub2).sys.PolyExpZero :=
  (SosSystem.polyExpZero_append _ _).mpr
    ⟨binExtSplicedSys_polyExpZero h1 h2 2,
      SosSystem.cons_polyExpZero
        (SosTerm.prod_polyExpZero
          -- the `prod` atom's first sub-system: two `sqDist` atoms.
          (SosSystem.cons_polyExpZero
            (SosTerm.sqDist_polyExpZero
              (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _))
              (SimpleSum.cons_polyExpZero (SimpleMonomial.mulVars_polyExpZero _ _)
                (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _))))
            (SosSystem.cons_polyExpZero
              (SosTerm.sqDist_polyExpZero
                (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _))
                (SimpleSum.cons_polyExpZero (SimpleMonomial.var_polyExpZero _)
                  (SimpleSum.cons_polyExpZero (SimpleMonomial.var_polyExpZero _)
                    (SimpleSum.singleton_polyExpZero SimpleMonomial.one_polyExpZero))))
              SosSystem.nil_polyExpZero))
          -- the `prod` atom's second sub-system: four `sqDist` atoms.
          (SosSystem.cons_polyExpZero
            (SosTerm.sqDist_polyExpZero
              (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _))
              SimpleSum.nil_polyExpZero)
            (SosSystem.cons_polyExpZero
              (SosTerm.sqDist_polyExpZero
                (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _))
                SimpleSum.nil_polyExpZero)
              (SosSystem.cons_polyExpZero
                (SosTerm.sqDist_polyExpZero
                  (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _))
                  (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _)))
                (SosSystem.cons_polyExpZero
                  (SosTerm.sqDist_polyExpZero
                    (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _))
                    SimpleSum.nil_polyExpZero)
                  SosSystem.nil_polyExpZero)))))
        SosSystem.nil_polyExpZero⟩

/-- `diophDiv sub1 sub2` builds a system with the zero-exponent property when
both sub-systems do. -/
theorem diophDiv_polyExpZero {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.PolyExpZero) (h2 : sub2.sys.PolyExpZero) :
    (diophDiv sub1 sub2).sys.PolyExpZero :=
  (SosSystem.polyExpZero_append _ _).mpr
    ⟨binExtSplicedSys_polyExpZero h1 h2 2,
      SosSystem.cons_polyExpZero
        (SosTerm.prod_polyExpZero
          -- the `prod` atom's first sub-system: two `sqDist` atoms.
          (SosSystem.cons_polyExpZero
            (SosTerm.sqDist_polyExpZero
              (SimpleSum.cons_polyExpZero (SimpleMonomial.mulVars_polyExpZero _ _)
                (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _)))
              (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _)))
            (SosSystem.cons_polyExpZero
              (SosTerm.sqDist_polyExpZero
                (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _))
                (SimpleSum.cons_polyExpZero (SimpleMonomial.var_polyExpZero _)
                  (SimpleSum.cons_polyExpZero (SimpleMonomial.var_polyExpZero _)
                    (SimpleSum.singleton_polyExpZero SimpleMonomial.one_polyExpZero))))
              SosSystem.nil_polyExpZero))
          -- the `prod` atom's second sub-system: four `sqDist` atoms.
          (SosSystem.cons_polyExpZero
            (SosTerm.sqDist_polyExpZero
              (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _))
              SimpleSum.nil_polyExpZero)
            (SosSystem.cons_polyExpZero
              (SosTerm.sqDist_polyExpZero
                (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _))
                SimpleSum.nil_polyExpZero)
              (SosSystem.cons_polyExpZero
                (SosTerm.sqDist_polyExpZero
                  (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _))
                  SimpleSum.nil_polyExpZero)
                (SosSystem.cons_polyExpZero
                  (SosTerm.sqDist_polyExpZero
                    (SimpleSum.singleton_polyExpZero (SimpleMonomial.var_polyExpZero _))
                    SimpleSum.nil_polyExpZero)
                  SosSystem.nil_polyExpZero)))))
        SosSystem.nil_polyExpZero⟩

/-- `diophOne` builds a system with the zero-exponent property. -/
theorem diophOne_polyExpZero {n : ℕ} : (diophOne (n := n)).sys.PolyExpZero :=
  diophSucc_polyExpZero diophZero_polyExpZero

/-- `diophPow sub1 sub2` builds a system with the zero-exponent property when
both sub-systems do: it is a composition of the combinators above along
Marchenkov's identity. -/
theorem diophPow_polyExpZero {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.PolyExpZero) (h2 : sub2.sys.PolyExpZero) :
    (diophPow sub1 sub2).sys.PolyExpZero := by
  unfold diophPow
  refine diophMod_polyExpZero (diophPow2_polyExpZero (diophMul_polyExpZero ?_ h2))
    (diophTsub_polyExpZero (diophPow2_polyExpZero ?_) h1)
  · exact diophAdd_polyExpZero (diophAdd_polyExpZero (diophMul_polyExpZero h1 h2) h1)
      diophOne_polyExpZero
  · exact diophAdd_polyExpZero (diophAdd_polyExpZero (diophMul_polyExpZero h1 h2) h1)
      diophOne_polyExpZero

/-- Every system produced by `diophOf` has the zero-exponent property: each
constructor case dispatches to its combinator's preservation lemma. -/
theorem diophOf_polyExpZero {n : ℕ} (t : ETm n) : (diophOf t).sys.PolyExpZero := by
  induction t with
  | var i => exact diophVar_polyExpZero i
  | zero => exact diophZero_polyExpZero
  | succ s ih => exact diophSucc_polyExpZero ih
  | app b ts ih =>
    cases b with
    | add => exact diophAdd_polyExpZero (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    | mul => exact diophMul_polyExpZero (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    | pow2 => exact diophPow2_polyExpZero (ih ⟨0, by decide⟩)
    | tsub => exact diophTsub_polyExpZero (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    | div => exact diophDiv_polyExpZero (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    | mod => exact diophMod_polyExpZero (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    | pow => exact diophPow_polyExpZero (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)

/-- A simple monomial has per-coordinate polynomial exponent at most `1`. -/
def SimpleMonomial.PolyExpLeOne {m : ℕ} (mon : SimpleMonomial m) : Prop :=
  ∀ i, mon.polyExp i ≤ 1

/-- A simple sum has the degree-`≤ 1` property when every one of its monomials
does. -/
def SimpleSum.PolyExpLeOne {m : ℕ} (p : SimpleSum m) : Prop :=
  ∀ mon ∈ p, mon.PolyExpLeOne

mutual
/-- A sum-of-squares atom has the degree-`≤ 1` property: a `sqDist P Q` atom
when both simple sums do, a `prod s t` atom when both sub-systems do. -/
def SosTerm.PolyExpLeOne {m : ℕ} (a : SosTerm m) : Prop :=
  match a with
  | .sqDist P Q => P.PolyExpLeOne ∧ Q.PolyExpLeOne
  | .prod s t => SosSystem.PolyExpLeOne s ∧ SosSystem.PolyExpLeOne t
--
/-- A sum-of-squares system has the degree-`≤ 1` property when every one of its
atoms does. -/
def SosSystem.PolyExpLeOne {m : ℕ} (s : SosSystem m) : Prop :=
  match s with
  | [] => True
  | a :: rest => a.PolyExpLeOne ∧ SosSystem.PolyExpLeOne rest
end

/-- The zero-exponent property implies the degree-`≤ 1` property for a
monomial. -/
theorem SimpleMonomial.polyExpZero_polyExpLeOne {m : ℕ} {mon : SimpleMonomial m}
    (h : mon.PolyExpZero) : mon.PolyExpLeOne := fun i => by rw [h i]; exact Nat.zero_le 1

/-- The zero-exponent property implies the degree-`≤ 1` property for a sum. -/
theorem SimpleSum.polyExpZero_polyExpLeOne {m : ℕ} {p : SimpleSum m}
    (h : p.PolyExpZero) : p.PolyExpLeOne :=
  fun mon hmon => SimpleMonomial.polyExpZero_polyExpLeOne (h mon hmon)

mutual
/-- The zero-exponent property implies the degree-`≤ 1` property for an atom. -/
theorem SosTerm.polyExpZero_polyExpLeOne {m : ℕ} {a : SosTerm m}
    (h : a.PolyExpZero) : a.PolyExpLeOne := by
  match a with
  | .sqDist P Q =>
    exact ⟨SimpleSum.polyExpZero_polyExpLeOne h.1, SimpleSum.polyExpZero_polyExpLeOne h.2⟩
  | .prod s t =>
    exact ⟨SosSystem.polyExpZero_polyExpLeOne h.1, SosSystem.polyExpZero_polyExpLeOne h.2⟩
--
/-- The zero-exponent property implies the degree-`≤ 1` property for a
system. -/
theorem SosSystem.polyExpZero_polyExpLeOne {m : ℕ} {s : SosSystem m}
    (h : s.PolyExpZero) : s.PolyExpLeOne := by
  match s with
  | [] => exact True.intro
  | a :: rest =>
    exact ⟨SosTerm.polyExpZero_polyExpLeOne h.1, SosSystem.polyExpZero_polyExpLeOne h.2⟩
end

/-- The degree certificate for route (ii): every monomial occurring in a
`sqDist`/`prod` atom of `(diophOf t).sys` has per-coordinate polynomial
exponent at most `1`. Combined with the `sqDist` squaring applied by the
consuming cube-sum factorisation, this gives per-coordinate degree at most `2`,
the hypothesis of Corollary 3.6 of arXiv:2407.12928. The bound holds because
the stronger `diophOf_polyExpZero` shows the exponents are identically `0`. -/
theorem diophOf_polyExp_le_one {n : ℕ} (t : ETm n) :
    (diophOf t).sys.PolyExpLeOne :=
  SosSystem.polyExpZero_polyExpLeOne (diophOf_polyExpZero t)

/-- A signed simple-exponential monomial over `m` variables, the `ℤ`-valued
reflection of arXiv:2407.12928, Expression (6) specialised to base `2`:
`(-1)^sign · coeff · ∏ᵢ 2 ^ (expCoeff i · ρ i) · ∏ᵢ (ρ i) ^ (polyExp i)`.
The single exponential base is `2`, so no per-variable base is stored. -/
@[ext]
structure ZMonomial (m : ℕ) where
  /-- The sign of the monomial: `true` negates the unsigned magnitude. -/
  sign : Bool
  /-- The leading coefficient. -/
  coeff : ETm m
  /-- The per-variable exponential coefficient, multiplying the variable in the
  base-`2` exponent. -/
  expCoeff : Fin m → ETm m
  /-- The per-variable constant polynomial exponent. -/
  polyExp : Fin m → ℕ

/-- The `ℤ`-valued denotation of a signed simple-exponential monomial at a
context `ρ`: `(-1)^sign · coeff · ∏ᵢ 2 ^ ((expCoeff i) · ρ i) · ∏ᵢ (ρ i) ^
(polyExp i)`, with the `ETm`-valued fields evaluated by `Tm.eval eraInterp` and
the natural-number products cast into `ℤ`. -/
def ZMonomial.eval {m : ℕ} (mon : ZMonomial m) (ρ : Fin m → ℕ) : ℤ :=
  (if mon.sign then -1 else 1) *
    ((Tm.eval eraInterp mon.coeff ρ
      * (∏ i, 2 ^ (Tm.eval eraInterp (mon.expCoeff i) ρ * ρ i))
      * (∏ i, ρ i ^ mon.polyExp i) : ℤ))

/-- The unsigned natural-number magnitude of a signed simple-exponential
monomial at a context `ρ`: the product `coeff · ∏ᵢ 2 ^ ((expCoeff i) · ρ i) ·
∏ᵢ (ρ i) ^ (polyExp i)` with the sign factor dropped. -/
def ZMonomial.evalNat {m : ℕ} (mon : ZMonomial m) (ρ : Fin m → ℕ) : ℕ :=
  Tm.eval eraInterp mon.coeff ρ
    * (∏ i, 2 ^ (Tm.eval eraInterp (mon.expCoeff i) ρ * ρ i))
    * (∏ i, ρ i ^ mon.polyExp i)

/-- The `ℤ`-valued `eval` equals the unsigned magnitude `evalNat` signed by
`sign`: negated when `sign` is `true`, the magnitude itself otherwise. -/
theorem ZMonomial.eval_eq {m : ℕ} (mon : ZMonomial m) (ρ : Fin m → ℕ) :
    mon.eval ρ =
      (if mon.sign then -(mon.evalNat ρ : ℤ) else (mon.evalNat ρ : ℤ)) := by
  rw [ZMonomial.eval, ZMonomial.evalNat]
  cases mon.sign
  · simp only [Bool.false_eq_true, if_false, Nat.cast_mul, Nat.cast_prod, Nat.cast_pow,
      Nat.cast_ofNat, one_mul]
  · simp only [if_true, Nat.cast_mul, Nat.cast_prod, Nat.cast_pow, Nat.cast_ofNat, neg_one_mul]

/-- The unsigned magnitude `evalNat` cast to `ℤ` is the absolute value of the
signed `eval`: the sign factor is `±1`, so it contributes only the sign. -/
theorem ZMonomial.evalNat_cast {m : ℕ} (mon : ZMonomial m) (ρ : Fin m → ℕ) :
    (mon.evalNat ρ : ℤ) = |mon.eval ρ| := by
  rw [ZMonomial.eval_eq]
  cases mon.sign <;> simp [abs_of_nonneg]

/-- The product of two signed simple-exponential monomials. The sign is the
exclusive-or of the factor signs (`(-1)^a · (-1)^b = (-1)^(a ⊕ b)`); the
coefficient is the term product; the per-variable exponential coefficient is the
term sum (merging the shared base `2`: `2 ^ (c₁ ρ) · 2 ^ (c₂ ρ) = 2 ^ ((c₁ + c₂)
ρ)`); and the per-variable polynomial exponent is the sum (`ρ ^ p₁ · ρ ^ p₂ = ρ ^
(p₁ + p₂)`). -/
def ZMonomial.mul {m : ℕ} (a b : ZMonomial m) : ZMonomial m where
  sign := xor a.sign b.sign
  coeff := a.coeff *ᵉ b.coeff
  expCoeff := fun i => a.expCoeff i +ᵉ b.expCoeff i
  polyExp := fun i => a.polyExp i + b.polyExp i

/-- The `ℤ`-valued denotation is multiplicative: the denotation of the product
monomial is the product of the denotations. The base-`2` exponentials merge by
`pow_add`, the polynomial factors by `pow_add`, the coefficients by the `emul`
evaluation lemma, and the signs by `(-1)^(a ⊕ b) = (-1)^a · (-1)^b`. -/
theorem ZMonomial.mul_eval {m : ℕ} (a b : ZMonomial m) (ρ : Fin m → ℕ) :
    (a.mul b).eval ρ = a.eval ρ * b.eval ρ := by
  obtain ⟨sa, ca, eca, pa⟩ := a
  obtain ⟨sb, cb, ecb, pb⟩ := b
  simp only [ZMonomial.eval, ZMonomial.mul, emul_eval, eraInterp, fcons, eadd_eval]
  have hexp : (∏ i, (2 : ℤ) ^ ((Tm.eval eraInterp (eca i) ρ
        + Tm.eval eraInterp (ecb i) ρ) * ρ i))
      = (∏ i, (2 : ℤ) ^ (Tm.eval eraInterp (eca i) ρ * ρ i))
        * (∏ i, (2 : ℤ) ^ (Tm.eval eraInterp (ecb i) ρ * ρ i)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => by rw [add_mul, pow_add])
  have hpoly : (∏ i, (ρ i : ℤ) ^ (pa i + pb i))
      = (∏ i, (ρ i : ℤ) ^ pa i) * (∏ i, (ρ i : ℤ) ^ pb i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => pow_add _ _ _)
  rw [hexp]
  push_cast [hpoly]
  cases sa <;> cases sb <;>
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true] <;>
    ring

/-- The restricted coefficient grammar of a `diophOf` monomial: an `ETm` built
from the constant `Era.one`, single variables `.var j`, and their products under
`*ᵉ`. Every `coeff` field of a monomial reachable from `diophOf` lies in this
grammar (`diophOf_coeffVarProduct`), which is what makes the cube-coordinate
degree extraction `ETm.extractCubeDegree` sound. -/
inductive ETm.IsVarProduct {m : ℕ} : ETm m → Prop
  | one : ETm.IsVarProduct Era.one
  | var (j : Fin m) : ETm.IsVarProduct (.var j)
  | mul {a b : ETm m} : ETm.IsVarProduct a → ETm.IsVarProduct b →
      ETm.IsVarProduct (a *ᵉ b)

/-- The coefficient grammar is closed under variable-renaming substitution: if
`e.IsVarProduct` then so is `e.subst (fun i => .var (f i))`, the substitution
underlying `SimpleMonomial.weaken`. A constant maps to a constant, a variable to
a variable, and a product to a product. -/
theorem ETm.IsVarProduct.weaken {m m' : ℕ} {e : ETm m} (he : ETm.IsVarProduct e)
    (f : Fin m → Fin m') : ETm.IsVarProduct (e.subst (fun i => .var (f i))) := by
  induction he with
  | one => exact ETm.IsVarProduct.one
  | var j => exact ETm.IsVarProduct.var (f j)
  | mul _ _ iha ihb => rw [emul_subst]; exact ETm.IsVarProduct.mul iha ihb

/-- Extract the cube-coordinate polynomial degree from a `diophOf` coefficient.
The variable block `Fin (p + k)` splits into `p` parameter slots and `k`
cube-coordinate slots. A cube-coordinate variable `.var (Fin.natAdd p c)`
contributes degree `1` at slot `c` and is removed from the coefficient (replaced
by `Era.one`); a parameter variable `.var (Fin.castAdd k i)` is kept in the
coefficient with zero degree; the constant `Era.one` contributes nothing; a
product `a *ᵉ b` multiplies the residual coefficients and adds the degree vectors
component-wise. Terms outside the `IsVarProduct` grammar return the sound
fallback `(e, fun _ => 0)`; correctness (`ETm.extractCubeDegree_eval`) is
conditioned on `IsVarProduct`. -/
def ETm.extractCubeDegree {p k : ℕ} (e : ETm (p + k)) :
    ETm (p + k) × (Fin k → ℕ) :=
  match e with
  | .succ .zero => (Era.one, fun _ => 0)
  | .var j =>
      Fin.addCases
        (fun i => (.var (Fin.castAdd k i), fun _ => 0))
        (fun c => (Era.one, fun c' => if c' = c then 1 else 0))
        j
  | .app .mul ts =>
      let r0 := ETm.extractCubeDegree (ts ⟨0, by decide⟩)
      let r1 := ETm.extractCubeDegree (ts ⟨1, by decide⟩)
      (r0.1 *ᵉ r1.1, fun c => r0.2 c + r1.2 c)
  | e => (e, fun _ => 0)

/-- The extraction is sound under the coefficient grammar: for an `IsVarProduct`
coefficient `e`, evaluating `e` at the appended context `Fin.append ctx a`
factors as the residual coefficient times the cube-coordinate monomial
`∏ c, (a c) ^ (degree c)`, where the residual coefficient and degree vector are
the two components of `ETm.extractCubeDegree e`. -/
theorem ETm.extractCubeDegree_eval {p k : ℕ} (e : ETm (p + k))
    (he : ETm.IsVarProduct e) (ctx : Fin p → ℕ) (a : Fin k → ℕ) :
    Tm.eval eraInterp e (Fin.append ctx a)
      = Tm.eval eraInterp (ETm.extractCubeDegree e).1 (Fin.append ctx a)
          * ∏ c : Fin k, (a c) ^ ((ETm.extractCubeDegree e).2 c) := by
  induction he with
  | one =>
    simp only [ETm.extractCubeDegree, Era.one, Tm.eval, pow_zero, Finset.prod_const_one, mul_one,
      Nat.zero_add]
  | var j =>
    induction j using Fin.addCases with
    | left i =>
      simp only [ETm.extractCubeDegree, Fin.addCases_left, Tm.eval, Fin.append_left, pow_zero,
        Finset.prod_const_one, mul_one]
    | right c =>
      simp only [ETm.extractCubeDegree, Fin.addCases_right, Era.one, Tm.eval, Fin.append_right,
        Nat.zero_add, one_mul]
      rw [Finset.prod_eq_single c]
      · rw [if_pos rfl, pow_one]
      · intro c' _ hc'; rw [if_neg hc', pow_zero]
      · intro h; exact absurd (Finset.mem_univ c) h
  | @mul ea eb ha hb iha ihb =>
    have hred : ETm.extractCubeDegree (ea *ᵉ eb)
        = ((ETm.extractCubeDegree ea).1 *ᵉ (ETm.extractCubeDegree eb).1,
          fun c => (ETm.extractCubeDegree ea).2 c + (ETm.extractCubeDegree eb).2 c) := rfl
    rw [hred]
    simp only [emul_eval, eraInterp, fcons]
    rw [iha, ihb]
    have hsplit : (∏ x, a x ^ ((ETm.extractCubeDegree ea).2 x + (ETm.extractCubeDegree eb).2 x))
        = (∏ x, a x ^ (ETm.extractCubeDegree ea).2 x) * (∏ x, a x ^ (ETm.extractCubeDegree eb).2 x)
        := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => pow_add _ _ _)
    rw [hsplit]
    ring

/-- A simple monomial has the coefficient-grammar property when its coefficient
lies in the `IsVarProduct` grammar (built from `Era.one`, single variables, and
`*ᵉ`). This is the precondition under which `ETm.extractCubeDegree` reads off the
cube-coordinate degree of the monomial's coefficient. -/
def SimpleMonomial.CoeffVarProduct {m : ℕ} (mon : SimpleMonomial m) : Prop :=
  ETm.IsVarProduct mon.coeff

/-- A simple sum has the coefficient-grammar property when every one of its
monomials does. -/
def SimpleSum.CoeffVarProduct {m : ℕ} (p : SimpleSum m) : Prop :=
  ∀ mon ∈ p, mon.CoeffVarProduct

mutual
/-- A sum-of-squares atom has the coefficient-grammar property: a `sqDist P Q`
atom when both simple sums do, a `prod s t` atom when both sub-systems do. -/
def SosTerm.CoeffVarProduct {m : ℕ} (a : SosTerm m) : Prop :=
  match a with
  | .sqDist P Q => P.CoeffVarProduct ∧ Q.CoeffVarProduct
  | .prod s t => SosSystem.CoeffVarProduct s ∧ SosSystem.CoeffVarProduct t
--
/-- A sum-of-squares system has the coefficient-grammar property when every one
of its atoms does. -/
def SosSystem.CoeffVarProduct {m : ℕ} (s : SosSystem m) : Prop :=
  match s with
  | [] => True
  | a :: rest => a.CoeffVarProduct ∧ SosSystem.CoeffVarProduct rest
end

/-- The coefficient-grammar property of a concatenated system is the conjunction
of the parts' properties. -/
theorem SosSystem.coeffVarProduct_append {m : ℕ} (s t : SosSystem m) :
    (s ++ t).CoeffVarProduct ↔ s.CoeffVarProduct ∧ t.CoeffVarProduct := by
  induction s with
  | nil => simp only [List.nil_append, SosSystem.CoeffVarProduct, true_and]
  | cons a rest ih =>
    rw [List.cons_append, SosSystem.CoeffVarProduct, SosSystem.CoeffVarProduct, ih, and_assoc]

/-- The empty simple sum has the coefficient-grammar property vacuously. -/
theorem SimpleSum.nil_coeffVarProduct {m : ℕ} :
    SimpleSum.CoeffVarProduct ([] : SimpleSum m) :=
  fun _ hmon => by simp only [List.not_mem_nil] at hmon

/-- A simple sum prepended with a grammar-conforming monomial keeps the property
when its tail does. -/
theorem SimpleSum.cons_coeffVarProduct {m : ℕ} {mon : SimpleMonomial m}
    {p : SimpleSum m} (hmon : mon.CoeffVarProduct) (hp : SimpleSum.CoeffVarProduct p) :
    SimpleSum.CoeffVarProduct (mon :: p) := by
  intro mon' hmon'
  rcases List.mem_cons.mp hmon' with h | h
  · rw [h]; exact hmon
  · exact hp mon' h

/-- A singleton simple sum has the coefficient-grammar property when its monomial
does. -/
theorem SimpleSum.singleton_coeffVarProduct {m : ℕ} {mon : SimpleMonomial m}
    (hmon : mon.CoeffVarProduct) : SimpleSum.CoeffVarProduct ([mon] : SimpleSum m) :=
  SimpleSum.cons_coeffVarProduct hmon SimpleSum.nil_coeffVarProduct

/-- A squared-distance atom has the coefficient-grammar property when both its
simple sums do. -/
theorem SosTerm.sqDist_coeffVarProduct {m : ℕ} {P Q : SimpleSum m}
    (hP : SimpleSum.CoeffVarProduct P) (hQ : SimpleSum.CoeffVarProduct Q) :
    (SosTerm.sqDist P Q).CoeffVarProduct :=
  ⟨hP, hQ⟩

/-- A product atom has the coefficient-grammar property when both its sub-systems
do. -/
theorem SosTerm.prod_coeffVarProduct {m : ℕ} {s t : SosSystem m}
    (hs : SosSystem.CoeffVarProduct s) (ht : SosSystem.CoeffVarProduct t) :
    (SosTerm.prod s t).CoeffVarProduct :=
  ⟨hs, ht⟩

/-- The empty sum-of-squares system has the coefficient-grammar property
vacuously. -/
theorem SosSystem.nil_coeffVarProduct {m : ℕ} :
    SosSystem.CoeffVarProduct ([] : SosSystem m) := True.intro

/-- A sum-of-squares system prepended with a grammar-conforming atom keeps the
property when its tail does. -/
theorem SosSystem.cons_coeffVarProduct {m : ℕ} {a : SosTerm m} {rest : SosSystem m}
    (ha : a.CoeffVarProduct) (hrest : SosSystem.CoeffVarProduct rest) :
    SosSystem.CoeffVarProduct (a :: rest) :=
  ⟨ha, hrest⟩

/-- The variable monomial has the coefficient-grammar property: its coefficient
is a single variable. -/
theorem SimpleMonomial.var_coeffVarProduct {m : ℕ} (j : Fin m) :
    (SimpleMonomial.var j).CoeffVarProduct := ETm.IsVarProduct.var j

/-- The constant monomial has the coefficient-grammar property: its coefficient
is `Era.one`. -/
theorem SimpleMonomial.one_coeffVarProduct {m : ℕ} :
    (SimpleMonomial.one (m := m)).CoeffVarProduct := ETm.IsVarProduct.one

/-- The product monomial has the coefficient-grammar property: its coefficient is
a product of two variables. -/
theorem SimpleMonomial.mulVars_coeffVarProduct {m : ℕ} (j k : Fin m) :
    (SimpleMonomial.mulVars j k).CoeffVarProduct :=
  ETm.IsVarProduct.mul (ETm.IsVarProduct.var j) (ETm.IsVarProduct.var k)

/-- The base-`2` power monomial has the coefficient-grammar property: its
coefficient is `Era.one` (its base-`2` factor lives in the exponential data, not
the coefficient). -/
theorem SimpleMonomial.pow2Var_coeffVarProduct {m : ℕ} (j : Fin m) :
    (SimpleMonomial.pow2Var j).CoeffVarProduct := ETm.IsVarProduct.one

/-- Re-indexing a monomial preserves the coefficient-grammar property: the
coefficient is renamed by the variable-renaming substitution underlying
`SimpleMonomial.weaken`, under which `IsVarProduct` is closed. -/
theorem SimpleMonomial.weaken_coeffVarProduct {m m' : ℕ} {mon : SimpleMonomial m}
    (h : mon.CoeffVarProduct) (f : Fin m → Fin m') : (mon.weaken f).CoeffVarProduct :=
  ETm.IsVarProduct.weaken h f

/-- Re-indexing a simple sum preserves the coefficient-grammar property. -/
theorem SimpleSum.weaken_coeffVarProduct {m m' : ℕ} {p : SimpleSum m}
    (h : p.CoeffVarProduct) (f : Fin m → Fin m') : (p.weaken f).CoeffVarProduct := by
  intro mon hmon
  unfold SimpleSum.weaken at hmon
  rw [List.mem_map] at hmon
  obtain ⟨mon₀, hmon₀, rfl⟩ := hmon
  exact SimpleMonomial.weaken_coeffVarProduct (h mon₀ hmon₀) f

mutual
/-- Re-indexing a sum-of-squares atom preserves the coefficient-grammar
property. -/
theorem SosTerm.weaken_coeffVarProduct {m m' : ℕ} {a : SosTerm m}
    (h : a.CoeffVarProduct) (f : Fin m → Fin m') : (a.weaken f).CoeffVarProduct := by
  match a with
  | .sqDist P Q =>
    rw [SosTerm.weaken]
    exact SosTerm.sqDist_coeffVarProduct (SimpleSum.weaken_coeffVarProduct h.1 f)
      (SimpleSum.weaken_coeffVarProduct h.2 f)
  | .prod s t =>
    rw [SosTerm.weaken]
    exact SosTerm.prod_coeffVarProduct (SosSystem.weaken_coeffVarProduct h.1 f)
      (SosSystem.weaken_coeffVarProduct h.2 f)
--
/-- Re-indexing a sum-of-squares system preserves the coefficient-grammar
property. -/
theorem SosSystem.weaken_coeffVarProduct {m m' : ℕ} {s : SosSystem m}
    (h : s.CoeffVarProduct) (f : Fin m → Fin m') : (s.weaken f).CoeffVarProduct := by
  match s with
  | [] =>
    rw [SosSystem.weaken]
    exact SosSystem.nil_coeffVarProduct
  | a :: rest =>
    rw [SosSystem.weaken]
    exact SosSystem.cons_coeffVarProduct (SosTerm.weaken_coeffVarProduct h.1 f)
      (SosSystem.weaken_coeffVarProduct h.2 f)
end

/-- The spliced system preserves the coefficient-grammar property: it is an
instance of `SosSystem.weaken_coeffVarProduct`. -/
theorem SosSystem.spliceWeaken_coeffVarProduct {n wSub wComp : ℕ}
    {s : SosSystem (n + 1 + wSub)} (h : s.CoeffVarProduct) (outSlot : Fin wComp)
    (witEmb : Fin wSub → Fin wComp) :
    (s.spliceWeaken outSlot witEmb).CoeffVarProduct :=
  SosSystem.weaken_coeffVarProduct h (spliceEmb outSlot witEmb)

/-- The binary spliced system has the coefficient-grammar property when both
sub-systems do. -/
theorem binSplicedSys_coeffVarProduct {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.CoeffVarProduct) (h2 : sub2.sys.CoeffVarProduct) :
    (binSplicedSys sub1 sub2).CoeffVarProduct := by
  rw [binSplicedSys, SosSystem.coeffVarProduct_append]
  exact ⟨SosSystem.spliceWeaken_coeffVarProduct h1 binOutSlot1 binWitEmb1,
    SosSystem.spliceWeaken_coeffVarProduct h2 binOutSlot2 binWitEmb2⟩

/-- The extended binary spliced system has the coefficient-grammar property when
both sub-systems do. -/
theorem binExtSplicedSys_coeffVarProduct {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.CoeffVarProduct) (h2 : sub2.sys.CoeffVarProduct) (k : ℕ) :
    (binExtSplicedSys sub1 sub2 k).CoeffVarProduct :=
  SosSystem.weaken_coeffVarProduct (binSplicedSys_coeffVarProduct h1 h2) binExtEmb

/-- `diophVar i` builds a system with the coefficient-grammar property. -/
theorem diophVar_coeffVarProduct {n : ℕ} (i : Fin n) :
    (diophVar i).sys.CoeffVarProduct :=
  SosSystem.cons_coeffVarProduct
    (SosTerm.sqDist_coeffVarProduct
      (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _))
      (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)))
    SosSystem.nil_coeffVarProduct

/-- `diophZero` builds a system with the coefficient-grammar property. -/
theorem diophZero_coeffVarProduct {n : ℕ} : (diophZero (n := n)).sys.CoeffVarProduct :=
  SosSystem.cons_coeffVarProduct
    (SosTerm.sqDist_coeffVarProduct SimpleSum.nil_coeffVarProduct
      (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)))
    SosSystem.nil_coeffVarProduct

/-- `diophSucc sub` builds a system with the coefficient-grammar property when
`sub` does. -/
theorem diophSucc_coeffVarProduct {n : ℕ} {sub : DiophEnc n}
    (h : sub.sys.CoeffVarProduct) : (diophSucc sub).sys.CoeffVarProduct :=
  (SosSystem.coeffVarProduct_append _ _).mpr
    ⟨SosSystem.spliceWeaken_coeffVarProduct h (Fin.last sub.witArity) succWitEmb,
      SosSystem.cons_coeffVarProduct
        (SosTerm.sqDist_coeffVarProduct
          (SimpleSum.cons_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)
            (SimpleSum.singleton_coeffVarProduct SimpleMonomial.one_coeffVarProduct))
          (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)))
        SosSystem.nil_coeffVarProduct⟩

/-- `diophAdd sub1 sub2` builds a system with the coefficient-grammar property
when both sub-systems do. -/
theorem diophAdd_coeffVarProduct {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.CoeffVarProduct) (h2 : sub2.sys.CoeffVarProduct) :
    (diophAdd sub1 sub2).sys.CoeffVarProduct :=
  (SosSystem.coeffVarProduct_append _ _).mpr
    ⟨binSplicedSys_coeffVarProduct h1 h2,
      SosSystem.cons_coeffVarProduct
        (SosTerm.sqDist_coeffVarProduct
          (SimpleSum.cons_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)
            (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)))
          (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)))
        SosSystem.nil_coeffVarProduct⟩

/-- `diophMul sub1 sub2` builds a system with the coefficient-grammar property
when both sub-systems do. -/
theorem diophMul_coeffVarProduct {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.CoeffVarProduct) (h2 : sub2.sys.CoeffVarProduct) :
    (diophMul sub1 sub2).sys.CoeffVarProduct :=
  (SosSystem.coeffVarProduct_append _ _).mpr
    ⟨binSplicedSys_coeffVarProduct h1 h2,
      SosSystem.cons_coeffVarProduct
        (SosTerm.sqDist_coeffVarProduct
          (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.mulVars_coeffVarProduct _ _))
          (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)))
        SosSystem.nil_coeffVarProduct⟩

/-- `diophPow2 sub` builds a system with the coefficient-grammar property when
`sub` does. -/
theorem diophPow2_coeffVarProduct {n : ℕ} {sub : DiophEnc n}
    (h : sub.sys.CoeffVarProduct) : (diophPow2 sub).sys.CoeffVarProduct :=
  (SosSystem.coeffVarProduct_append _ _).mpr
    ⟨SosSystem.spliceWeaken_coeffVarProduct h (Fin.last sub.witArity) succWitEmb,
      SosSystem.cons_coeffVarProduct
        (SosTerm.sqDist_coeffVarProduct
          (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.pow2Var_coeffVarProduct _))
          (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)))
        SosSystem.nil_coeffVarProduct⟩

/-- `diophTsub sub1 sub2` builds a system with the coefficient-grammar property
when both sub-systems do. -/
theorem diophTsub_coeffVarProduct {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.CoeffVarProduct) (h2 : sub2.sys.CoeffVarProduct) :
    (diophTsub sub1 sub2).sys.CoeffVarProduct :=
  (SosSystem.coeffVarProduct_append _ _).mpr
    ⟨binExtSplicedSys_coeffVarProduct h1 h2 1,
      SosSystem.cons_coeffVarProduct
        (SosTerm.sqDist_coeffVarProduct
          (SimpleSum.cons_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)
            (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)))
          (SimpleSum.cons_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)
            (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _))))
        (SosSystem.cons_coeffVarProduct
          (SosTerm.sqDist_coeffVarProduct
            (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.mulVars_coeffVarProduct _ _))
            SimpleSum.nil_coeffVarProduct)
          SosSystem.nil_coeffVarProduct)⟩

/-- `diophMod sub1 sub2` builds a system with the coefficient-grammar property
when both sub-systems do. -/
theorem diophMod_coeffVarProduct {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.CoeffVarProduct) (h2 : sub2.sys.CoeffVarProduct) :
    (diophMod sub1 sub2).sys.CoeffVarProduct :=
  (SosSystem.coeffVarProduct_append _ _).mpr
    ⟨binExtSplicedSys_coeffVarProduct h1 h2 2,
      SosSystem.cons_coeffVarProduct
        (SosTerm.prod_coeffVarProduct
          (SosSystem.cons_coeffVarProduct
            (SosTerm.sqDist_coeffVarProduct
              (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _))
              (SimpleSum.cons_coeffVarProduct (SimpleMonomial.mulVars_coeffVarProduct _ _)
                (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _))))
            (SosSystem.cons_coeffVarProduct
              (SosTerm.sqDist_coeffVarProduct
                (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _))
                (SimpleSum.cons_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)
                  (SimpleSum.cons_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)
                    (SimpleSum.singleton_coeffVarProduct SimpleMonomial.one_coeffVarProduct))))
              SosSystem.nil_coeffVarProduct))
          (SosSystem.cons_coeffVarProduct
            (SosTerm.sqDist_coeffVarProduct
              (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _))
              SimpleSum.nil_coeffVarProduct)
            (SosSystem.cons_coeffVarProduct
              (SosTerm.sqDist_coeffVarProduct
                (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _))
                SimpleSum.nil_coeffVarProduct)
              (SosSystem.cons_coeffVarProduct
                (SosTerm.sqDist_coeffVarProduct
                  (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _))
                  (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)))
                (SosSystem.cons_coeffVarProduct
                  (SosTerm.sqDist_coeffVarProduct
                    (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _))
                    SimpleSum.nil_coeffVarProduct)
                  SosSystem.nil_coeffVarProduct)))))
        SosSystem.nil_coeffVarProduct⟩

/-- `diophDiv sub1 sub2` builds a system with the coefficient-grammar property
when both sub-systems do. -/
theorem diophDiv_coeffVarProduct {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.CoeffVarProduct) (h2 : sub2.sys.CoeffVarProduct) :
    (diophDiv sub1 sub2).sys.CoeffVarProduct :=
  (SosSystem.coeffVarProduct_append _ _).mpr
    ⟨binExtSplicedSys_coeffVarProduct h1 h2 2,
      SosSystem.cons_coeffVarProduct
        (SosTerm.prod_coeffVarProduct
          (SosSystem.cons_coeffVarProduct
            (SosTerm.sqDist_coeffVarProduct
              (SimpleSum.cons_coeffVarProduct (SimpleMonomial.mulVars_coeffVarProduct _ _)
                (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)))
              (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)))
            (SosSystem.cons_coeffVarProduct
              (SosTerm.sqDist_coeffVarProduct
                (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _))
                (SimpleSum.cons_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)
                  (SimpleSum.cons_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _)
                    (SimpleSum.singleton_coeffVarProduct SimpleMonomial.one_coeffVarProduct))))
              SosSystem.nil_coeffVarProduct))
          (SosSystem.cons_coeffVarProduct
            (SosTerm.sqDist_coeffVarProduct
              (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _))
              SimpleSum.nil_coeffVarProduct)
            (SosSystem.cons_coeffVarProduct
              (SosTerm.sqDist_coeffVarProduct
                (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _))
                SimpleSum.nil_coeffVarProduct)
              (SosSystem.cons_coeffVarProduct
                (SosTerm.sqDist_coeffVarProduct
                  (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _))
                  SimpleSum.nil_coeffVarProduct)
                (SosSystem.cons_coeffVarProduct
                  (SosTerm.sqDist_coeffVarProduct
                    (SimpleSum.singleton_coeffVarProduct (SimpleMonomial.var_coeffVarProduct _))
                    SimpleSum.nil_coeffVarProduct)
                  SosSystem.nil_coeffVarProduct)))))
        SosSystem.nil_coeffVarProduct⟩

/-- `diophOne` builds a system with the coefficient-grammar property. -/
theorem diophOne_coeffVarProduct {n : ℕ} : (diophOne (n := n)).sys.CoeffVarProduct :=
  diophSucc_coeffVarProduct diophZero_coeffVarProduct

/-- `diophPow sub1 sub2` builds a system with the coefficient-grammar property
when both sub-systems do: it is the same combinator composition as
`diophPow_polyExpZero`. -/
theorem diophPow_coeffVarProduct {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.CoeffVarProduct) (h2 : sub2.sys.CoeffVarProduct) :
    (diophPow sub1 sub2).sys.CoeffVarProduct := by
  unfold diophPow
  refine diophMod_coeffVarProduct
    (diophPow2_coeffVarProduct (diophMul_coeffVarProduct ?_ h2))
    (diophTsub_coeffVarProduct (diophPow2_coeffVarProduct ?_) h1)
  · exact diophAdd_coeffVarProduct
      (diophAdd_coeffVarProduct (diophMul_coeffVarProduct h1 h2) h1) diophOne_coeffVarProduct
  · exact diophAdd_coeffVarProduct
      (diophAdd_coeffVarProduct (diophMul_coeffVarProduct h1 h2) h1) diophOne_coeffVarProduct

/-- Every system produced by `diophOf` has the coefficient-grammar property: each
constructor case dispatches to its combinator's preservation lemma. Together with
`ETm.extractCubeDegree_eval` this licenses reading off each monomial's
cube-coordinate degree. -/
theorem diophOf_coeffVarProduct {n : ℕ} (t : ETm n) :
    (diophOf t).sys.CoeffVarProduct := by
  induction t with
  | var i => exact diophVar_coeffVarProduct i
  | zero => exact diophZero_coeffVarProduct
  | succ s ih => exact diophSucc_coeffVarProduct ih
  | app b ts ih =>
    cases b with
    | add => exact diophAdd_coeffVarProduct (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    | mul => exact diophMul_coeffVarProduct (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    | pow2 => exact diophPow2_coeffVarProduct (ih ⟨0, by decide⟩)
    | tsub => exact diophTsub_coeffVarProduct (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    | div => exact diophDiv_coeffVarProduct (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    | mod => exact diophMod_coeffVarProduct (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    | pow => exact diophPow_coeffVarProduct (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)

/-- A simple monomial is base-paired when, at every slot `i`, its exponential
data is one of the two shapes reachable from a `diophOf` atom: either the trivial
shape `expBase i = .zero ∧ expCoeff i = .zero` (no exponential factor, since
`0 ^ (0 · ρ i) = 1`), or the base-`2` shape `expBase i = .succ Era.one ∧
expCoeff i = Era.one` (the `pow2Var` factor `2 ^ ρ i`). Every monomial reachable
from `diophOf` is base-paired (`diophOf_basePaired`); consequently each slot's
exponential factor is either `1` or `2 ^ ρ i`, the single normalised base the
downstream cube-sum factorisation assumes. -/
def SimpleMonomial.BasePaired {m : ℕ} (mon : SimpleMonomial m) : Prop :=
  ∀ i, (mon.expBase i = .zero ∧ mon.expCoeff i = .zero) ∨
    (mon.expBase i = .succ Era.one ∧ mon.expCoeff i = Era.one)

/-- A simple sum is base-paired when every one of its monomials is. -/
def SimpleSum.BasePaired {m : ℕ} (p : SimpleSum m) : Prop :=
  ∀ mon ∈ p, mon.BasePaired

mutual
/-- A sum-of-squares atom is base-paired: a `sqDist P Q` atom when both simple
sums are, a `prod s t` atom when both sub-systems are. -/
def SosTerm.BasePaired {m : ℕ} (a : SosTerm m) : Prop :=
  match a with
  | .sqDist P Q => P.BasePaired ∧ Q.BasePaired
  | .prod s t => SosSystem.BasePaired s ∧ SosSystem.BasePaired t
--
/-- A sum-of-squares system is base-paired when every one of its atoms is. -/
def SosSystem.BasePaired {m : ℕ} (s : SosSystem m) : Prop :=
  match s with
  | [] => True
  | a :: rest => a.BasePaired ∧ SosSystem.BasePaired rest
end

/-- The base-paired property of a concatenated system is the conjunction of the
parts' properties. -/
theorem SosSystem.basePaired_append {m : ℕ} (s t : SosSystem m) :
    (s ++ t).BasePaired ↔ s.BasePaired ∧ t.BasePaired := by
  induction s with
  | nil => simp only [List.nil_append, SosSystem.BasePaired, true_and]
  | cons a rest ih =>
    rw [List.cons_append, SosSystem.BasePaired, SosSystem.BasePaired, ih, and_assoc]

/-- The empty simple sum is base-paired vacuously. -/
theorem SimpleSum.nil_basePaired {m : ℕ} :
    SimpleSum.BasePaired ([] : SimpleSum m) :=
  fun _ hmon => by simp only [List.not_mem_nil] at hmon

/-- A simple sum prepended with a base-paired monomial keeps the property when
its tail does. -/
theorem SimpleSum.cons_basePaired {m : ℕ} {mon : SimpleMonomial m} {p : SimpleSum m}
    (hmon : mon.BasePaired) (hp : SimpleSum.BasePaired p) :
    SimpleSum.BasePaired (mon :: p) := by
  intro mon' hmon'
  rcases List.mem_cons.mp hmon' with h | h
  · rw [h]; exact hmon
  · exact hp mon' h

/-- A singleton simple sum is base-paired when its monomial is. -/
theorem SimpleSum.singleton_basePaired {m : ℕ} {mon : SimpleMonomial m}
    (hmon : mon.BasePaired) : SimpleSum.BasePaired ([mon] : SimpleSum m) :=
  SimpleSum.cons_basePaired hmon SimpleSum.nil_basePaired

/-- A squared-distance atom is base-paired when both its simple sums are. -/
theorem SosTerm.sqDist_basePaired {m : ℕ} {P Q : SimpleSum m}
    (hP : SimpleSum.BasePaired P) (hQ : SimpleSum.BasePaired Q) :
    (SosTerm.sqDist P Q).BasePaired :=
  ⟨hP, hQ⟩

/-- A product atom is base-paired when both its sub-systems are. -/
theorem SosTerm.prod_basePaired {m : ℕ} {s t : SosSystem m}
    (hs : SosSystem.BasePaired s) (ht : SosSystem.BasePaired t) :
    (SosTerm.prod s t).BasePaired :=
  ⟨hs, ht⟩

/-- The empty sum-of-squares system is base-paired vacuously. -/
theorem SosSystem.nil_basePaired {m : ℕ} :
    SosSystem.BasePaired ([] : SosSystem m) := True.intro

/-- A sum-of-squares system prepended with a base-paired atom keeps the property
when its tail does. -/
theorem SosSystem.cons_basePaired {m : ℕ} {a : SosTerm m} {rest : SosSystem m}
    (ha : a.BasePaired) (hrest : SosSystem.BasePaired rest) :
    SosSystem.BasePaired (a :: rest) :=
  ⟨ha, hrest⟩

/-- The variable monomial is base-paired: its exponential data is trivial. -/
theorem SimpleMonomial.var_basePaired {m : ℕ} (j : Fin m) :
    (SimpleMonomial.var j).BasePaired := fun _ => Or.inl ⟨rfl, rfl⟩

/-- The constant monomial is base-paired: its exponential data is trivial. -/
theorem SimpleMonomial.one_basePaired {m : ℕ} :
    (SimpleMonomial.one (m := m)).BasePaired := fun _ => Or.inl ⟨rfl, rfl⟩

/-- The product monomial is base-paired: its exponential data is trivial. -/
theorem SimpleMonomial.mulVars_basePaired {m : ℕ} (j k : Fin m) :
    (SimpleMonomial.mulVars j k).BasePaired := fun _ => Or.inl ⟨rfl, rfl⟩

/-- The base-`2` power monomial is base-paired: at slot `j` it has the base-`2`
shape, at every other slot the trivial shape. -/
theorem SimpleMonomial.pow2Var_basePaired {m : ℕ} (j : Fin m) :
    (SimpleMonomial.pow2Var j).BasePaired := by
  intro i
  by_cases hij : i = j
  · exact Or.inr ⟨by simp only [SimpleMonomial.pow2Var, if_pos hij],
      by simp only [SimpleMonomial.pow2Var, if_pos hij]⟩
  · exact Or.inl ⟨by simp only [SimpleMonomial.pow2Var, if_neg hij],
      by simp only [SimpleMonomial.pow2Var, if_neg hij]⟩

/-- Re-indexing a monomial preserves the base-paired property: each target slot's
exponential data is either the renaming of a source slot's data (renaming sends
`.zero` to `.zero` and `.succ Era.one` to `.succ Era.one`, both variable-free) or
the off-image default `.zero`, which is the trivial shape. -/
theorem SimpleMonomial.weaken_basePaired {m m' : ℕ} {mon : SimpleMonomial m}
    (h : mon.BasePaired) (f : Fin m → Fin m') : (mon.weaken f).BasePaired := by
  intro j
  change (match preimage f j with
      | some i => (mon.expBase i).weaken f
      | none => .zero) = .zero ∧
        (match preimage f j with
          | some i => (mon.expCoeff i).weaken f
          | none => .zero) = .zero ∨
      (match preimage f j with
          | some i => (mon.expBase i).weaken f
          | none => .zero) = .succ Era.one ∧
        (match preimage f j with
          | some i => (mon.expCoeff i).weaken f
          | none => .zero) = Era.one
  cases preimage f j with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some i =>
    dsimp only
    rcases h i with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · exact Or.inl ⟨by rw [hb]; rfl, by rw [hc]; rfl⟩
    · exact Or.inr ⟨by rw [hb]; rfl, by rw [hc]; rfl⟩

/-- Re-indexing a simple sum preserves the base-paired property. -/
theorem SimpleSum.weaken_basePaired {m m' : ℕ} {p : SimpleSum m}
    (h : p.BasePaired) (f : Fin m → Fin m') : (p.weaken f).BasePaired := by
  intro mon hmon
  unfold SimpleSum.weaken at hmon
  rw [List.mem_map] at hmon
  obtain ⟨mon₀, hmon₀, rfl⟩ := hmon
  exact SimpleMonomial.weaken_basePaired (h mon₀ hmon₀) f

mutual
/-- Re-indexing a sum-of-squares atom preserves the base-paired property. -/
theorem SosTerm.weaken_basePaired {m m' : ℕ} {a : SosTerm m}
    (h : a.BasePaired) (f : Fin m → Fin m') : (a.weaken f).BasePaired := by
  match a with
  | .sqDist P Q =>
    rw [SosTerm.weaken]
    exact SosTerm.sqDist_basePaired (SimpleSum.weaken_basePaired h.1 f)
      (SimpleSum.weaken_basePaired h.2 f)
  | .prod s t =>
    rw [SosTerm.weaken]
    exact SosTerm.prod_basePaired (SosSystem.weaken_basePaired h.1 f)
      (SosSystem.weaken_basePaired h.2 f)
--
/-- Re-indexing a sum-of-squares system preserves the base-paired property. -/
theorem SosSystem.weaken_basePaired {m m' : ℕ} {s : SosSystem m}
    (h : s.BasePaired) (f : Fin m → Fin m') : (s.weaken f).BasePaired := by
  match s with
  | [] =>
    rw [SosSystem.weaken]
    exact SosSystem.nil_basePaired
  | a :: rest =>
    rw [SosSystem.weaken]
    exact SosSystem.cons_basePaired (SosTerm.weaken_basePaired h.1 f)
      (SosSystem.weaken_basePaired h.2 f)
end

/-- The spliced system preserves the base-paired property: it is an instance of
`SosSystem.weaken_basePaired`. -/
theorem SosSystem.spliceWeaken_basePaired {n wSub wComp : ℕ}
    {s : SosSystem (n + 1 + wSub)} (h : s.BasePaired) (outSlot : Fin wComp)
    (witEmb : Fin wSub → Fin wComp) :
    (s.spliceWeaken outSlot witEmb).BasePaired :=
  SosSystem.weaken_basePaired h (spliceEmb outSlot witEmb)

/-- The binary spliced system is base-paired when both sub-systems are. -/
theorem binSplicedSys_basePaired {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.BasePaired) (h2 : sub2.sys.BasePaired) :
    (binSplicedSys sub1 sub2).BasePaired := by
  rw [binSplicedSys, SosSystem.basePaired_append]
  exact ⟨SosSystem.spliceWeaken_basePaired h1 binOutSlot1 binWitEmb1,
    SosSystem.spliceWeaken_basePaired h2 binOutSlot2 binWitEmb2⟩

/-- The extended binary spliced system is base-paired when both sub-systems
are. -/
theorem binExtSplicedSys_basePaired {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.BasePaired) (h2 : sub2.sys.BasePaired) (k : ℕ) :
    (binExtSplicedSys sub1 sub2 k).BasePaired :=
  SosSystem.weaken_basePaired (binSplicedSys_basePaired h1 h2) binExtEmb

/-- `diophVar i` builds a base-paired system. -/
theorem diophVar_basePaired {n : ℕ} (i : Fin n) : (diophVar i).sys.BasePaired :=
  SosSystem.cons_basePaired
    (SosTerm.sqDist_basePaired
      (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _))
      (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _)))
    SosSystem.nil_basePaired

/-- `diophZero` builds a base-paired system. -/
theorem diophZero_basePaired {n : ℕ} : (diophZero (n := n)).sys.BasePaired :=
  SosSystem.cons_basePaired
    (SosTerm.sqDist_basePaired SimpleSum.nil_basePaired
      (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _)))
    SosSystem.nil_basePaired

/-- `diophSucc sub` builds a base-paired system when `sub` does. -/
theorem diophSucc_basePaired {n : ℕ} {sub : DiophEnc n} (h : sub.sys.BasePaired) :
    (diophSucc sub).sys.BasePaired :=
  (SosSystem.basePaired_append _ _).mpr
    ⟨SosSystem.spliceWeaken_basePaired h (Fin.last sub.witArity) succWitEmb,
      SosSystem.cons_basePaired
        (SosTerm.sqDist_basePaired
          (SimpleSum.cons_basePaired (SimpleMonomial.var_basePaired _)
            (SimpleSum.singleton_basePaired SimpleMonomial.one_basePaired))
          (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _)))
        SosSystem.nil_basePaired⟩

/-- `diophAdd sub1 sub2` builds a base-paired system when both sub-systems do. -/
theorem diophAdd_basePaired {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.BasePaired) (h2 : sub2.sys.BasePaired) :
    (diophAdd sub1 sub2).sys.BasePaired :=
  (SosSystem.basePaired_append _ _).mpr
    ⟨binSplicedSys_basePaired h1 h2,
      SosSystem.cons_basePaired
        (SosTerm.sqDist_basePaired
          (SimpleSum.cons_basePaired (SimpleMonomial.var_basePaired _)
            (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _)))
          (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _)))
        SosSystem.nil_basePaired⟩

/-- `diophMul sub1 sub2` builds a base-paired system when both sub-systems do. -/
theorem diophMul_basePaired {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.BasePaired) (h2 : sub2.sys.BasePaired) :
    (diophMul sub1 sub2).sys.BasePaired :=
  (SosSystem.basePaired_append _ _).mpr
    ⟨binSplicedSys_basePaired h1 h2,
      SosSystem.cons_basePaired
        (SosTerm.sqDist_basePaired
          (SimpleSum.singleton_basePaired (SimpleMonomial.mulVars_basePaired _ _))
          (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _)))
        SosSystem.nil_basePaired⟩

/-- `diophPow2 sub` builds a base-paired system when `sub` does: the new
`pow2Var` atom has the base-`2` shape. -/
theorem diophPow2_basePaired {n : ℕ} {sub : DiophEnc n} (h : sub.sys.BasePaired) :
    (diophPow2 sub).sys.BasePaired :=
  (SosSystem.basePaired_append _ _).mpr
    ⟨SosSystem.spliceWeaken_basePaired h (Fin.last sub.witArity) succWitEmb,
      SosSystem.cons_basePaired
        (SosTerm.sqDist_basePaired
          (SimpleSum.singleton_basePaired (SimpleMonomial.pow2Var_basePaired _))
          (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _)))
        SosSystem.nil_basePaired⟩

/-- `diophTsub sub1 sub2` builds a base-paired system when both sub-systems
do. -/
theorem diophTsub_basePaired {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.BasePaired) (h2 : sub2.sys.BasePaired) :
    (diophTsub sub1 sub2).sys.BasePaired :=
  (SosSystem.basePaired_append _ _).mpr
    ⟨binExtSplicedSys_basePaired h1 h2 1,
      SosSystem.cons_basePaired
        (SosTerm.sqDist_basePaired
          (SimpleSum.cons_basePaired (SimpleMonomial.var_basePaired _)
            (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _)))
          (SimpleSum.cons_basePaired (SimpleMonomial.var_basePaired _)
            (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _))))
        (SosSystem.cons_basePaired
          (SosTerm.sqDist_basePaired
            (SimpleSum.singleton_basePaired (SimpleMonomial.mulVars_basePaired _ _))
            SimpleSum.nil_basePaired)
          SosSystem.nil_basePaired)⟩

/-- `diophMod sub1 sub2` builds a base-paired system when both sub-systems do. -/
theorem diophMod_basePaired {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.BasePaired) (h2 : sub2.sys.BasePaired) :
    (diophMod sub1 sub2).sys.BasePaired :=
  (SosSystem.basePaired_append _ _).mpr
    ⟨binExtSplicedSys_basePaired h1 h2 2,
      SosSystem.cons_basePaired
        (SosTerm.prod_basePaired
          (SosSystem.cons_basePaired
            (SosTerm.sqDist_basePaired
              (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _))
              (SimpleSum.cons_basePaired (SimpleMonomial.mulVars_basePaired _ _)
                (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _))))
            (SosSystem.cons_basePaired
              (SosTerm.sqDist_basePaired
                (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _))
                (SimpleSum.cons_basePaired (SimpleMonomial.var_basePaired _)
                  (SimpleSum.cons_basePaired (SimpleMonomial.var_basePaired _)
                    (SimpleSum.singleton_basePaired SimpleMonomial.one_basePaired))))
              SosSystem.nil_basePaired))
          (SosSystem.cons_basePaired
            (SosTerm.sqDist_basePaired
              (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _))
              SimpleSum.nil_basePaired)
            (SosSystem.cons_basePaired
              (SosTerm.sqDist_basePaired
                (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _))
                SimpleSum.nil_basePaired)
              (SosSystem.cons_basePaired
                (SosTerm.sqDist_basePaired
                  (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _))
                  (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _)))
                (SosSystem.cons_basePaired
                  (SosTerm.sqDist_basePaired
                    (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _))
                    SimpleSum.nil_basePaired)
                  SosSystem.nil_basePaired)))))
        SosSystem.nil_basePaired⟩

/-- `diophDiv sub1 sub2` builds a base-paired system when both sub-systems do. -/
theorem diophDiv_basePaired {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.BasePaired) (h2 : sub2.sys.BasePaired) :
    (diophDiv sub1 sub2).sys.BasePaired :=
  (SosSystem.basePaired_append _ _).mpr
    ⟨binExtSplicedSys_basePaired h1 h2 2,
      SosSystem.cons_basePaired
        (SosTerm.prod_basePaired
          (SosSystem.cons_basePaired
            (SosTerm.sqDist_basePaired
              (SimpleSum.cons_basePaired (SimpleMonomial.mulVars_basePaired _ _)
                (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _)))
              (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _)))
            (SosSystem.cons_basePaired
              (SosTerm.sqDist_basePaired
                (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _))
                (SimpleSum.cons_basePaired (SimpleMonomial.var_basePaired _)
                  (SimpleSum.cons_basePaired (SimpleMonomial.var_basePaired _)
                    (SimpleSum.singleton_basePaired SimpleMonomial.one_basePaired))))
              SosSystem.nil_basePaired))
          (SosSystem.cons_basePaired
            (SosTerm.sqDist_basePaired
              (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _))
              SimpleSum.nil_basePaired)
            (SosSystem.cons_basePaired
              (SosTerm.sqDist_basePaired
                (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _))
                SimpleSum.nil_basePaired)
              (SosSystem.cons_basePaired
                (SosTerm.sqDist_basePaired
                  (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _))
                  SimpleSum.nil_basePaired)
                (SosSystem.cons_basePaired
                  (SosTerm.sqDist_basePaired
                    (SimpleSum.singleton_basePaired (SimpleMonomial.var_basePaired _))
                    SimpleSum.nil_basePaired)
                  SosSystem.nil_basePaired)))))
        SosSystem.nil_basePaired⟩

/-- `diophOne` builds a base-paired system. -/
theorem diophOne_basePaired {n : ℕ} : (diophOne (n := n)).sys.BasePaired :=
  diophSucc_basePaired diophZero_basePaired

/-- `diophPow sub1 sub2` builds a base-paired system when both sub-systems do:
the same combinator composition as `diophPow_polyExpZero`. -/
theorem diophPow_basePaired {n : ℕ} {sub1 sub2 : DiophEnc n}
    (h1 : sub1.sys.BasePaired) (h2 : sub2.sys.BasePaired) :
    (diophPow sub1 sub2).sys.BasePaired := by
  unfold diophPow
  refine diophMod_basePaired (diophPow2_basePaired (diophMul_basePaired ?_ h2))
    (diophTsub_basePaired (diophPow2_basePaired ?_) h1)
  · exact diophAdd_basePaired (diophAdd_basePaired (diophMul_basePaired h1 h2) h1)
      diophOne_basePaired
  · exact diophAdd_basePaired (diophAdd_basePaired (diophMul_basePaired h1 h2) h1)
      diophOne_basePaired

/-- Every system produced by `diophOf` is base-paired: each constructor case
dispatches to its combinator's preservation lemma. Consequently every monomial's
per-slot exponential factor is either `1` or `2 ^ ρ i`, the normalised base-`2`
form the downstream cube-sum factorisation assumes. -/
theorem diophOf_basePaired {n : ℕ} (t : ETm n) : (diophOf t).sys.BasePaired := by
  induction t with
  | var i => exact diophVar_basePaired i
  | zero => exact diophZero_basePaired
  | succ s ih => exact diophSucc_basePaired ih
  | app b ts ih =>
    cases b with
    | add => exact diophAdd_basePaired (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    | mul => exact diophMul_basePaired (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    | pow2 => exact diophPow2_basePaired (ih ⟨0, by decide⟩)
    | tsub => exact diophTsub_basePaired (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    | div => exact diophDiv_basePaired (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    | mod => exact diophMod_basePaired (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)
    | pow => exact diophPow_basePaired (ih ⟨0, by decide⟩) (ih ⟨1, by decide⟩)

/-- Lift a single `diophOf` monomial over `Fin (p + k)` to a signed
simple-exponential `ZMonomial`, moving the cube-coordinate polynomial degree of
the coefficient into the `polyExp` field. The sign is positive (a `SimpleMonomial`
denotes a natural number); the coefficient is the cube-degree-extraction residual
`(mon.coeff.extractCubeDegree).1`; the exponential coefficient is carried over
verbatim (the base-`2` specialisation of `ZMonomial` matches the base-paired
shape of a `diophOf` monomial); and the polynomial exponent at each slot is the
monomial's own `polyExp` plus the extracted cube degree, placed at the cube block
`Fin.natAdd p c` and zero on the parameter block `Fin.castAdd k i` via
`Fin.addCases`. -/
def SimpleMonomial.toZ {p k : ℕ} (mon : SimpleMonomial (p + k)) : ZMonomial (p + k) where
  sign := false
  coeff := (ETm.extractCubeDegree mon.coeff).1
  expCoeff := fun i => mon.expCoeff i
  polyExp := fun i => mon.polyExp i +
    Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (ETm.extractCubeDegree mon.coeff).2 i

/-- The lift agrees with the natural-number monomial on the cube: the `ℤ`-valued
denotation of `mon.toZ` at the appended context `Fin.append ctx a` equals the
`SimpleMonomial` value cast to `ℤ`. The coefficient factor is reconciled by
`ETm.extractCubeDegree_eval` (the cube-coordinate degree extracted into `polyExp`
balances the residual coefficient); the polynomial-exponent product splits into
the monomial's own polynomial factor times the extracted cube-coordinate
monomial; and under `hbase` the base-paired exponential factors agree pointwise,
since the trivial slot gives `0 ^ 0 = 2 ^ 0 = 1` and the base-`2` slot gives
`2 ^ (expCoeff · ρ)` on both sides. -/
theorem SimpleMonomial.toZ_eval {p k : ℕ} (mon : SimpleMonomial (p + k))
    (ctx : Fin p → ℕ) (a : Fin k → ℕ)
    (hcoeff : mon.CoeffVarProduct) (hbase : mon.BasePaired) :
    mon.toZ.eval (Fin.append ctx a) = (mon.eval (Fin.append ctx a) : ℤ) := by
  rw [ZMonomial.eval, SimpleMonomial.eval, SimpleMonomial.toZ]
  simp only [Bool.false_eq_true, if_false, one_mul]
  -- The exponential factor: base-paired slots agree pointwise with base `2`.
  have hexp : (∏ i, (2 : ℤ)
        ^ (Tm.eval eraInterp (mon.expCoeff i) (Fin.append ctx a) * (Fin.append ctx a) i))
      = ((∏ i, Tm.eval eraInterp (mon.expBase i) (Fin.append ctx a)
          ^ (Tm.eval eraInterp (mon.expCoeff i) (Fin.append ctx a)
            * (Fin.append ctx a) i) : ℕ) : ℤ) := by
    push_cast
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rcases hbase i with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · rw [hb, hc]
      simp only [Tm.eval, Nat.zero_mul, pow_zero]
    · rw [hb, hc]
      simp only [Era.one, Tm.eval]
      norm_num
  -- The polynomial-exponent factor splits into the own part and the cube part.
  have hpoly : (∏ i, ((Fin.append ctx a) i : ℤ)
        ^ (mon.polyExp i + Fin.addCases (motive := fun _ => ℕ) (fun _ => 0)
            (ETm.extractCubeDegree mon.coeff).2 i))
      = (∏ i, ((Fin.append ctx a) i : ℤ) ^ mon.polyExp i)
        * (∏ c, (a c : ℤ) ^ ((ETm.extractCubeDegree mon.coeff).2 c)) := by
    rw [show (∏ i, ((Fin.append ctx a) i : ℤ)
          ^ (mon.polyExp i + Fin.addCases (motive := fun _ => ℕ) (fun _ => 0)
              (ETm.extractCubeDegree mon.coeff).2 i))
        = (∏ i, ((Fin.append ctx a) i : ℤ) ^ mon.polyExp i)
          * (∏ i, ((Fin.append ctx a) i : ℤ)
              ^ Fin.addCases (motive := fun _ => ℕ) (fun _ => 0)
                  (ETm.extractCubeDegree mon.coeff).2 i) from by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => pow_add _ _ _)]
    congr 1
    rw [Fin.prod_univ_add]
    have hleft : (∏ i : Fin p, ((Fin.append ctx a) (Fin.castAdd k i) : ℤ)
        ^ Fin.addCases (motive := fun _ => ℕ) (fun _ => 0)
            (ETm.extractCubeDegree mon.coeff).2 (Fin.castAdd k i)) = 1 := by
      refine Finset.prod_eq_one (fun i _ => ?_)
      rw [Fin.addCases_left, pow_zero]
    rw [hleft, one_mul]
    refine Finset.prod_congr rfl (fun c _ => ?_)
    rw [Fin.addCases_right, Fin.append_right]
  rw [hexp]
  push_cast
  rw [hpoly]
  -- The coefficient factor: extraction balances the cube-coordinate degree.
  rw [ETm.extractCubeDegree_eval mon.coeff hcoeff ctx a]
  push_cast
  ring

/-- Lift a simple sum over `Fin (p + k)` to a list of signed simple-exponential
`ZMonomial`s, lifting each monomial with `SimpleMonomial.toZ`. -/
def SimpleSum.toZ {p k : ℕ} (s : SimpleSum (p + k)) : List (ZMonomial (p + k)) :=
  s.map SimpleMonomial.toZ

/-- The lifted simple sum agrees with the natural-number simple sum on the cube:
the sum of the `ℤ`-valued denotations of the lifted monomials at the appended
context equals the `SimpleSum` value cast to `ℤ`. Each member's agreement is
`SimpleMonomial.toZ_eval`, whose per-monomial hypotheses follow from the sum-level
`CoeffVarProduct`/`BasePaired` predicates by membership. -/
theorem SimpleSum.toZ_eval {p k : ℕ} (s : SimpleSum (p + k))
    (ctx : Fin p → ℕ) (a : Fin k → ℕ)
    (hcoeff : s.CoeffVarProduct) (hbase : s.BasePaired) :
    ((s.toZ).map (fun mon => mon.eval (Fin.append ctx a))).sum
      = (s.eval (Fin.append ctx a) : ℤ) := by
  rw [SimpleSum.toZ, SimpleSum.eval]
  induction s with
  | nil => simp only [List.map_nil, List.sum_nil, Nat.cast_zero]
  | cons mon rest ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
      Nat.cast_add]
    rw [SimpleMonomial.toZ_eval mon ctx a (hcoeff mon (List.mem_cons_self ..))
      (hbase mon (List.mem_cons_self ..))]
    rw [ih (fun m hm => hcoeff m (List.mem_cons_of_mem _ hm))
      (fun m hm => hbase m (List.mem_cons_of_mem _ hm))]

/-- The list of all pairwise products of two lists of signed simple-exponential
monomials: for each `a ∈ L₁` and `b ∈ L₂` the product monomial `a.mul b`. This is
the term-level distribution of `(∑ L₁) · (∑ L₂)`, used to realise both the
cross-term of a `sqDist` square and the product of a `prod` atom as a single flat
`ZMonomial` list. -/
def ZMonomial.listMul {m : ℕ} (L₁ L₂ : List (ZMonomial m)) : List (ZMonomial m) :=
  L₁.flatMap (fun a => L₂.map (fun b => a.mul b))

/-- The pairwise-product list's denotation sum factorises: the sum of the
`ℤ`-valued denotations of `ZMonomial.listMul L₁ L₂` is the product of the two
factors' denotation sums. The per-element product is `ZMonomial.mul_eval`; the
distribution over `L₂` is `List.sum_map_mul_left`; the recursion over `L₁` is the
list-append split of `List.flatMap` on a cons. -/
theorem ZMonomial.listMul_eval {m : ℕ} (L₁ L₂ : List (ZMonomial m)) (ρ : Fin m → ℕ) :
    ((ZMonomial.listMul L₁ L₂).map (fun mon => mon.eval ρ)).sum
      = (((L₁.map (fun mon => mon.eval ρ)).sum) * ((L₂.map (fun mon => mon.eval ρ)).sum)) := by
  induction L₁ with
  | nil => simp only [ZMonomial.listMul, List.flatMap_nil, List.map_nil, List.sum_nil, zero_mul]
  | cons a rest ih =>
    rw [ZMonomial.listMul, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_map, List.map_cons, List.sum_cons, add_mul]
    rw [← ZMonomial.listMul, ih]
    congr 1
    rw [show ((fun mon => mon.eval ρ) ∘ fun b => a.mul b)
        = (fun b => a.eval ρ * b.eval ρ) from by
      funext b; simp only [Function.comp_apply]; exact ZMonomial.mul_eval a b ρ]
    exact List.sum_map_mul_left L₂ (fun b => b.eval ρ) (a.eval ρ)

/-- Negate and double a signed simple-exponential monomial: flip its sign and
multiply its coefficient by the constant `2` (`Era.one.succ`). This realises the
`−2 P Q` cross-term of a truncated squared distance `(P − Q)²`: applied to each
member of `ZMonomial.listMul Pz Qz` it produces the doubled negative cross-terms. -/
def ZMonomial.negDouble {m : ℕ} (mon : ZMonomial m) : ZMonomial m where
  sign := !mon.sign
  coeff := mon.coeff *ᵉ Era.one.succ
  expCoeff := mon.expCoeff
  polyExp := mon.polyExp

/-- The denotation of `ZMonomial.negDouble mon` is `−(2 · mon.eval ρ)`: the sign
flip contributes the negation and the coefficient times `2` contributes the
doubling. -/
theorem ZMonomial.negDouble_eval {m : ℕ} (mon : ZMonomial m) (ρ : Fin m → ℕ) :
    (mon.negDouble).eval ρ = -(2 * mon.eval ρ) := by
  obtain ⟨s, c, ec, p⟩ := mon
  simp only [ZMonomial.eval, ZMonomial.negDouble, emul_eval, eraInterp, fcons, Era.one, Tm.eval]
  cases s <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true] <;>
    push_cast <;>
    ring

/-- The truncated squared distance, cast to `ℤ`, is the honest quadratic: for any
two naturals `x y`, `((x − y)² + (y − x)² : ℕ) : ℤ = x² + y² − 2 x y`, where the
`ℕ` subtractions are truncated. Proved by `le_total`: in each ordering one
truncated subtraction is `0` and the other is the honest difference, lifted by
`Nat.cast_sub`. This is the `sqDist` ℕ→ℤ reconciliation underlying
`SosTerm.toZ_eval`. -/
theorem SosTerm.cast_sqDist {x y : ℕ} :
    (((x - y) ^ 2 + (y - x) ^ 2 : ℕ) : ℤ) = (x : ℤ) ^ 2 + (y : ℤ) ^ 2 - 2 * x * y := by
  rcases le_total x y with h | h
  · rw [Nat.sub_eq_zero_of_le h]
    push_cast [Nat.cast_sub h]
    ring
  · rw [Nat.sub_eq_zero_of_le h]
    push_cast [Nat.cast_sub h]
    ring

mutual
/-- Lift a sum-of-squares atom over `Fin (p + k)` to a list of signed
simple-exponential `ZMonomial`s whose denotation sum equals the atom's
natural-number value (cast to `ℤ`). A `sqDist P Q` atom expands to
`P² + Q² − 2 P Q`: with `Pz := P.toZ`, `Qz := Q.toZ`, the list is
`ZMonomial.listMul Pz Pz ++ ZMonomial.listMul Qz Qz ++ (ZMonomial.listMul Pz Qz).map negDouble`,
the last block supplying the doubled negative cross-term. A `prod s t` atom expands
to the pairwise product `ZMonomial.listMul (SosSystem.toZ s) (SosSystem.toZ t)`. -/
def SosTerm.toZ {p k : ℕ} (a : SosTerm (p + k)) : List (ZMonomial (p + k)) :=
  match a with
  | .sqDist P Q =>
    ZMonomial.listMul P.toZ P.toZ ++ ZMonomial.listMul Q.toZ Q.toZ ++
      (ZMonomial.listMul P.toZ Q.toZ).map ZMonomial.negDouble
  | .prod s t => ZMonomial.listMul (SosSystem.toZ s) (SosSystem.toZ t)
--
/-- Lift a sum-of-squares system over `Fin (p + k)` to a list of signed
simple-exponential `ZMonomial`s by concatenating each atom's lift. -/
def SosSystem.toZ {p k : ℕ} (s : SosSystem (p + k)) : List (ZMonomial (p + k)) :=
  match s with
  | [] => []
  | a :: rest => a.toZ ++ SosSystem.toZ rest
end

mutual
/-- The lifted atom agrees with the natural-number atom on the cube: the sum of
the `ℤ`-valued denotations of `a.toZ` at the appended context equals the
`SosTerm` value cast to `ℤ`. For `sqDist P Q` the three `listMul` blocks reflect
`P²`, `Q²`, and `−2 P Q` (via `ZMonomial.listMul_eval`, `SimpleSum.toZ_eval`, and
`ZMonomial.negDouble_eval`), reconciled to the truncated-subtraction value by
`SosTerm.cast_sqDist`; for `prod s t` the single `listMul` block reflects the product
by `ZMonomial.listMul_eval` and the sub-system induction hypotheses. -/
theorem SosTerm.toZ_eval {p k : ℕ} (a : SosTerm (p + k))
    (ctx : Fin p → ℕ) (a' : Fin k → ℕ)
    (hcoeff : a.CoeffVarProduct) (hbase : a.BasePaired) :
    ((a.toZ).map (fun mon => mon.eval (Fin.append ctx a'))).sum
      = (SosTerm.eval a (Fin.append ctx a') : ℤ) := by
  match a with
  | .sqDist P Q =>
    obtain ⟨hcP, hcQ⟩ := hcoeff
    obtain ⟨hbP, hbQ⟩ := hbase
    rw [SosTerm.toZ, SosTerm.eval, List.map_append, List.sum_append, List.map_append,
      List.sum_append, ZMonomial.listMul_eval, ZMonomial.listMul_eval,
      SimpleSum.toZ_eval P ctx a' hcP hbP, SimpleSum.toZ_eval Q ctx a' hcQ hbQ]
    rw [List.map_map,
      show ((fun mon => ZMonomial.eval mon (Fin.append ctx a')) ∘ ZMonomial.negDouble)
          = (fun mon => -2 * mon.eval (Fin.append ctx a')) from by
        funext mon
        simp only [Function.comp_apply, ZMonomial.negDouble_eval]
        ring]
    rw [List.sum_map_mul_left (ZMonomial.listMul P.toZ Q.toZ)
      (fun mon => mon.eval (Fin.append ctx a')) (-2),
      ZMonomial.listMul_eval, SimpleSum.toZ_eval P ctx a' hcP hbP,
      SimpleSum.toZ_eval Q ctx a' hcQ hbQ, SosTerm.cast_sqDist]
    ring
  | .prod s t =>
    obtain ⟨hcs, hct⟩ := hcoeff
    obtain ⟨hbs, hbt⟩ := hbase
    rw [SosTerm.toZ, SosTerm.eval, ZMonomial.listMul_eval,
      SosSystem.toZ_eval s ctx a' hcs hbs, SosSystem.toZ_eval t ctx a' hct hbt,
      Nat.cast_mul]
--
/-- The lifted system agrees with the natural-number system on the cube: the sum
of the `ℤ`-valued denotations of `s.toZ` at the appended context equals the
`SosSystem` value cast to `ℤ`. Each atom's agreement is `SosTerm.toZ_eval`; the
concatenation is the append split of `List.map`/`List.sum`. -/
theorem SosSystem.toZ_eval {p k : ℕ} (s : SosSystem (p + k))
    (ctx : Fin p → ℕ) (a : Fin k → ℕ)
    (hcoeff : s.CoeffVarProduct) (hbase : s.BasePaired) :
    ((s.toZ).map (fun mon => mon.eval (Fin.append ctx a))).sum
      = (SosSystem.eval s (Fin.append ctx a) : ℤ) := by
  match s with
  | [] =>
    rw [SosSystem.toZ, SosSystem.eval]
    simp only [List.map_nil, List.sum_nil, Nat.cast_zero]
  | b :: rest =>
    obtain ⟨hcb, hcrest⟩ := hcoeff
    obtain ⟨hbb, hbrest⟩ := hbase
    rw [SosSystem.toZ, SosSystem.eval, List.map_append, List.sum_append,
      SosTerm.toZ_eval b ctx a hcb hbb, SosSystem.toZ_eval rest ctx a hcrest hbrest,
      Nat.cast_add]
end

/-- The rectangle index of the chain-variable block. The `k · d` new chain
variables are laid out as a `Fin k × Fin d` rectangle; `chainIdx c i` is the
flat index of the cell `(c, i)`, reusing mathlib's `finProdFinEquiv`. With
`finProdFinEquiv`'s convention `(c, i) ↦ i.val + d · c.val`, the value of
`chainIdx c i` is `i.val + d · c.val`. -/
def chainIdx {k d : ℕ} (c : Fin k) (i : Fin d) : Fin (k * d) :=
  finProdFinEquiv (c, i)

/-- The value of `chainIdx c i` is `i.val + d · c.val`, the `finProdFinEquiv`
flattening convention. -/
theorem chainIdx_val {k d : ℕ} (c : Fin k) (i : Fin d) :
    (chainIdx c i).val = i.val + d * c.val :=
  finProdFinEquiv_apply_val (c, i)

/-- `chainIdx` is injective: distinct rectangle cells receive distinct flat
indices, as `finProdFinEquiv` is an equivalence. -/
theorem chainIdx_injective {k d : ℕ} :
    Function.Injective (fun p : Fin k × Fin d => chainIdx p.1 p.2) := by
  intro p q h
  exact finProdFinEquiv.injective h

/-- The cube-coordinate slot of the enlarged scope `Fin (p + k + k * d)`: cube
coordinate `c : Fin k` sits in the `k`-block following the `p` parameter slots,
embedded past the chain block by `Fin.castAdd`. -/
def cubeSlot {p k d : ℕ} (c : Fin k) : Fin (p + k + k * d) :=
  Fin.castAdd (k * d) (Fin.natAdd p c)

/-- The chain-variable slot of the enlarged scope `Fin (p + k + k * d)`: the
chain cell `(c, i) : Fin k × Fin d` sits in the trailing `k * d`-block, at the
rectangle index `chainIdx c i`. -/
def chainSlot {p k d : ℕ} (c : Fin k) (i : Fin d) : Fin (p + k + k * d) :=
  Fin.natAdd (p + k) (chainIdx c i)

/-- The old-scope embedding into the enlarged scope `Fin (p + k + f)`: the
identity on the first `p + k` indices, by `Fin.castAdd`. -/
def castAddEmb {p k f : ℕ} : Fin (p + k) → Fin (p + k + f) := Fin.castAdd f

/-- `castAddEmb` is injective, inherited from `Fin.castAdd_injective`. -/
theorem castAddEmb_injective {p k f : ℕ} :
    Function.Injective (castAddEmb : Fin (p + k) → Fin (p + k + f)) :=
  Fin.castAdd_injective (p + k) f

/-- `cubeSlot` is injective in the cube coordinate: it is the composite of the
injective `Fin.natAdd p` and `Fin.castAdd (k * d)`. -/
theorem cubeSlot_injective {p k d : ℕ} :
    Function.Injective (cubeSlot : Fin k → Fin (p + k + k * d)) := by
  intro c c' h
  unfold cubeSlot at h
  exact (Fin.natAdd_inj p).mp (Fin.castAdd_injective (p + k) (k * d) h)

/-- `chainSlot` is injective in the chain cell: it is the composite of the
injective `Fin.natAdd (p + k)` and `chainIdx`. -/
theorem chainSlot_injective {p k d : ℕ} :
    Function.Injective (fun q : Fin k × Fin d => chainSlot (p := p) q.1 q.2) := by
  intro q q' h
  unfold chainSlot at h
  exact chainIdx_injective ((Fin.natAdd_inj (p + k)).mp h)

/-- A cube slot and a chain slot are distinct: cube slots live in the
`Fin.castAdd (k * d)` block of the first `p + k` indices, chain slots in the
trailing `Fin.natAdd (p + k)` block, which are disjoint. -/
theorem cubeSlot_ne_chainSlot {p k d : ℕ} (c : Fin k) (c' : Fin k) (i' : Fin d) :
    cubeSlot (p := p) c ≠ chainSlot c' i' := by
  unfold cubeSlot chainSlot
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_castAdd, Fin.val_natAdd, Fin.val_natAdd] at hv
  have hlt : c.val < k := c.isLt
  omega

/-- A chain slot is never in the image of `castAddEmb`: `castAddEmb`'s image is
exactly the first `p + k` indices, while a chain slot lies in the trailing
`Fin.natAdd (p + k)` block. -/
theorem castAddEmb_ne_chainSlot {p k d : ℕ} (j : Fin (p + k)) (c : Fin k) (i : Fin d) :
    castAddEmb j ≠ chainSlot (d := d) c i := by
  unfold castAddEmb chainSlot
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_castAdd, Fin.val_natAdd] at hv
  have hlt : j.val < p + k := j.isLt
  omega

/-- The preimage of an embedded index under `castAddEmb` is its source index,
by `preimage_apply` and the injectivity of `castAddEmb`. -/
theorem preimage_castAddEmb_apply {p k f : ℕ} (j : Fin (p + k)) :
    preimage (castAddEmb : Fin (p + k) → Fin (p + k + f)) (castAddEmb j) = some j :=
  preimage_apply castAddEmb_injective j

/-- The preimage of a chain slot under `castAddEmb` is `none`: chain slots lie
off the image of `castAddEmb`, by `castAddEmb_ne_chainSlot` and
`preimage_eq_none`. -/
theorem preimage_castAddEmb_chainSlot {p k d : ℕ} (c : Fin k) (i : Fin d) :
    preimage (castAddEmb : Fin (p + k) → Fin (p + k + k * d)) (chainSlot c i) = none :=
  preimage_eq_none (fun j => castAddEmb_ne_chainSlot j c i)

/-- Re-index a signed simple-exponential monomial along `f`. The coefficient
and per-variable exponential coefficients are renamed by `Tm.weaken f`; each
target slot reads the source data of its `preimage`, defaulting off the image
to the trivial value. -/
def ZMonomial.weaken {m m' : ℕ} (mon : ZMonomial m) (f : Fin m → Fin m') :
    ZMonomial m' where
  sign     := mon.sign
  coeff    := mon.coeff.weaken f
  expCoeff := fun j => match preimage f j with
    | some i => (mon.expCoeff i).weaken f
    | none   => .zero
  polyExp  := fun j => match preimage f j with
    | some i => mon.polyExp i
    | none   => 0

/-- Re-indexing compatibility for signed monomials: for injective `f`,
evaluating `mon.weaken f` at `ρ'` equals evaluating `mon` at `ρ' ∘ f`. The sign
is unchanged, the coefficient by `Tm.eval_weaken`, and the two `ℕ` products by
`Finset.prod_of_injOn` over the image of `f` (off-image factors are
`2 ^ (0 · ρ) = 1` and `_ ^ 0 = 1`), cast into `ℤ`. -/
theorem ZMonomial.weaken_eval {m m' : ℕ} (mon : ZMonomial m)
    (f : Fin m → Fin m') (hf : Function.Injective f) (ρ' : Fin m' → ℕ) :
    (mon.weaken f).eval ρ' = mon.eval (ρ' ∘ f) := by
  unfold ZMonomial.eval ZMonomial.weaken
  congr 1
  congr 1
  · congr 1
    · exact congrArg Int.ofNat (Tm.eval_weaken eraInterp f mon.coeff ρ')
    · refine (Finset.prod_of_injOn f (fun a _ b _ h => hf h) (fun _ _ => Finset.mem_univ _)
        ?_ ?_).symm
      · intro j _ hj
        have hnone : preimage f j = none := by
          apply preimage_eq_none
          intro i hi
          exact hj ⟨i, Finset.mem_univ i, hi⟩
        simp only [hnone]
        simp only [Tm.eval]
        rw [Nat.zero_mul, pow_zero]
      · intro i _
        simp only [preimage_apply hf]
        rw [Tm.eval_weaken]
        rfl
  · refine congrArg Int.ofNat
      (Finset.prod_of_injOn f (fun a _ b _ h => hf h) (fun _ _ => Finset.mem_univ _) ?_ ?_).symm
    · intro j _ hj
      have hnone : preimage f j = none := by
        apply preimage_eq_none
        intro i hi
        exact hj ⟨i, Finset.mem_univ i, hi⟩
      simp only [hnone]
      rw [Nat.pow_zero]
    · intro i _
      simp only [preimage_apply hf]
      rfl

/-- Re-indexing compatibility for a list of signed monomials: for injective `f`,
the sum of the re-indexed monomials' denotations at `ρ'` equals the sum of the
originals' denotations at `ρ' ∘ f`. Termwise by `ZMonomial.weaken_eval`. -/
theorem ZMonomial.weaken_list_eval {m m' : ℕ} (L : List (ZMonomial m))
    (f : Fin m → Fin m') (hf : Function.Injective f) (ρ' : Fin m' → ℕ) :
    ((L.map (fun mon => mon.weaken f)).map (fun mon => mon.eval ρ')).sum
      = (L.map (fun mon => mon.eval (ρ' ∘ f))).sum := by
  rw [List.map_map]
  exact congrArg List.sum
    (List.map_congr_left (fun mon _ => ZMonomial.weaken_eval mon f hf ρ'))

/-- The single-variable signed monomial `x_j`: trivial sign, unit coefficient, no
exponential factor, and polynomial exponent `1` at slot `j` and `0` elsewhere. Its
denotation is the variable value `ρ j`. Used to build the linear chain equation
`x_c − y_{c,1}`. -/
def ZMonomial.varMon {m : ℕ} (j : Fin m) : ZMonomial m where
  sign := false
  coeff := Era.one
  expCoeff := fun _ => .zero
  polyExp := fun j' => if j' = j then 1 else 0

/-- The denotation of `ZMonomial.varMon j` is the variable value `ρ j`: the unit
coefficient and trivial exponential factor leave the polynomial product, which is
`ρ j` because the exponent vector is the indicator of `j`. -/
theorem ZMonomial.varMon_eval {m : ℕ} (j : Fin m) (ρ : Fin m → ℕ) :
    (ZMonomial.varMon j).eval ρ = (ρ j : ℤ) := by
  simp only [ZMonomial.eval, ZMonomial.varMon, Era.one, Tm.eval, Bool.false_eq_true, if_false,
    Nat.zero_mul, pow_zero, Finset.prod_const_one, one_mul]
  rw [Nat.cast_prod, Finset.prod_eq_single j]
  · rw [if_pos rfl, pow_one]; push_cast; ring
  · intro j' _ hj'; rw [if_neg hj', pow_zero, Nat.cast_one]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The negated single-variable signed monomial `−x_j`: `ZMonomial.varMon j` with the
sign flipped to `true`. Its denotation is `−ρ j`. Used as the right summand of every
chain equation. -/
def ZMonomial.negVarMon {m : ℕ} (j : Fin m) : ZMonomial m :=
  { ZMonomial.varMon j with sign := true }

/-- The denotation of `ZMonomial.negVarMon j` is `−ρ j`: it negates the magnitude of
`ZMonomial.varMon j`, whose denotation is `ρ j`. -/
theorem ZMonomial.negVarMon_eval {m : ℕ} (j : Fin m) (ρ : Fin m → ℕ) :
    (ZMonomial.negVarMon j).eval ρ = -(ρ j : ℤ) := by
  have h := ZMonomial.varMon_eval j ρ
  rw [ZMonomial.eval, ZMonomial.negVarMon, ZMonomial.varMon]
  rw [ZMonomial.eval, ZMonomial.varMon] at h
  dsimp only at h ⊢
  rw [if_neg Bool.false_ne_true, one_mul] at h
  rw [if_pos rfl, neg_one_mul, h]

/-- The product signed monomial `x_j · x_{j'}` for distinct slots `j ≠ j'`: trivial
sign, unit coefficient, no exponential factor, and polynomial exponent the sum of the
indicators of `j` and `j'` (so degree `1` at each distinct slot). Its denotation, for
`j ≠ j'`, is `ρ j · ρ j'`. Used to build the multiplicative chain equation
`y_{c,i} · x_c − y_{c,i+1}`. -/
def ZMonomial.mulVarMon {m : ℕ} (j j' : Fin m) : ZMonomial m where
  sign := false
  coeff := Era.one
  expCoeff := fun _ => .zero
  polyExp := fun s => (if s = j then 1 else 0) + (if s = j' then 1 else 0)

/-- For distinct slots `j ≠ j'`, the denotation of `ZMonomial.mulVarMon j j'` is the
product `ρ j · ρ j'`: the polynomial product picks out exponent `1` at each of the two
distinct slots and `0` elsewhere. -/
theorem ZMonomial.mulVarMon_eval {m : ℕ} (j j' : Fin m) (h : j ≠ j') (ρ : Fin m → ℕ) :
    (ZMonomial.mulVarMon j j').eval ρ = (ρ j : ℤ) * ρ j' := by
  simp only [ZMonomial.eval, ZMonomial.mulVarMon, Era.one, Tm.eval, Bool.false_eq_true, if_false,
    Nat.zero_mul, pow_zero, Finset.prod_const_one, one_mul]
  push_cast
  rw [← Finset.prod_subset (Finset.subset_univ ({j, j'} : Finset (Fin m)))
    (fun i _ hi => ?_), Finset.prod_pair h]
  · rw [if_pos rfl, if_neg h, if_pos rfl, if_neg (Ne.symm h)]
    simp only [Nat.add_zero, Nat.zero_add, pow_one, one_mul]
  · rw [Finset.mem_insert, Finset.mem_singleton] at hi
    push_neg at hi
    rw [if_neg hi.1, if_neg hi.2, Nat.add_zero, pow_zero]

/-- The maximum cube-coordinate polynomial degree over a list of monomials: the
maximum of `mon.polyExp (Fin.natAdd p c)` over all monomials `mon ∈ L` and all cube
coordinates `c : Fin k`. This is the paper's `h`, the global chain length, computed by
folding `max` over the list and over `List.finRange k`. -/
def ZMonomial.maxCubeDegree {p k : ℕ} (L : List (ZMonomial (p + k))) : ℕ :=
  List.foldr max 0
    (L.map (fun mon =>
      List.foldr max 0 ((List.finRange k).map (fun c => mon.polyExp (Fin.natAdd p c)))))

/-- Every monomial in the list, at every cube coordinate, has polynomial degree at most
`ZMonomial.maxCubeDegree L`: the bound is the outer fold's `max` over the list (via
`List.le_max_of_le'` at the membership witness) of the inner fold's `max` over the cube
coordinates (again via `List.le_max_of_le'`, with `c ∈ List.finRange k`). -/
theorem ZMonomial.le_maxCubeDegree {p k : ℕ} (L : List (ZMonomial (p + k)))
    (mon : ZMonomial (p + k)) (hmon : mon ∈ L) (c : Fin k) :
    mon.polyExp (Fin.natAdd p c) ≤ ZMonomial.maxCubeDegree L := by
  refine List.le_max_of_le' 0 (List.mem_map_of_mem hmon) ?_
  exact List.le_max_of_le' 0 (List.mem_map_of_mem (List.mem_finRange c)) (le_refl _)

/-- The left side `S_{c,i}` of the chain equation for cube coordinate `c` and chain
level `i`, as a two-monomial signed difference over the enlarged scope. For `i = 0` it is
`x_c − y_{c,1} = [varMon (cubeSlot c), negVarMon (chainSlot c 0)]`; for `i = j + 1` it is
`y_{c,i} · x_c − y_{c,i+1} = [mulVarMon (chainSlot c j) (cubeSlot c), negVarMon (chainSlot
c i)]`, where `chainSlot c j` (with `j = i − 1`) holds `x_c^i`. The chain equation asserts
`S_{c,i}` evaluates to `0`. -/
def chainEqList {p k d : ℕ} (c : Fin k) (i : Fin d) : List (ZMonomial (p + k + k * d)) :=
  match h : i.val with
  | 0 => [ZMonomial.varMon (cubeSlot c), ZMonomial.negVarMon (chainSlot c i)]
  | j + 1 =>
    [ZMonomial.mulVarMon (chainSlot c ⟨j, by omega⟩) (cubeSlot c),
      ZMonomial.negVarMon (chainSlot c i)]

/-- The full squared chain-equation block over the enlarged scope `Fin (p + k + k * d)`:
for every cube coordinate `c : Fin k` and chain level `i : Fin d`, the literal square
`listMul (chainEqList c i) (chainEqList c i)` of the chain-equation left side `S_{c,i}`,
all concatenated. Each `S_{c,i}²` is a sum-of-squares atom that vanishes exactly when the
chain equation holds. -/
def chainEqs {p k d : ℕ} : List (ZMonomial (p + k + k * d)) :=
  (List.finRange k).flatMap (fun c => (List.finRange d).flatMap (fun i =>
    ZMonomial.listMul (chainEqList c i) (chainEqList c i)))

/-- The single-variable monomial has per-slot polynomial degree at most `1`: its
exponent vector is the indicator of one slot. -/
theorem ZMonomial.varMon_polyExp_le_one {m : ℕ} (j : Fin m) (s : Fin m) :
    (ZMonomial.varMon j).polyExp s ≤ 1 := by
  simp only [ZMonomial.varMon]; split <;> omega

/-- The negated single-variable monomial has per-slot polynomial degree at most `1`: it
shares `ZMonomial.varMon`'s exponent vector. -/
theorem ZMonomial.negVarMon_polyExp_le_one {m : ℕ} (j : Fin m) (s : Fin m) :
    (ZMonomial.negVarMon j).polyExp s ≤ 1 := by
  simp only [ZMonomial.negVarMon, ZMonomial.varMon]; split <;> omega

/-- For distinct slots `j ≠ j'`, the product monomial has per-slot polynomial degree at
most `1`: its exponent vector sets exactly the two distinct slots `j` and `j'` to `1`, so
no single slot reaches `2`. -/
theorem ZMonomial.mulVarMon_polyExp_le_one {m : ℕ} (j j' : Fin m) (h : j ≠ j') (s : Fin m) :
    (ZMonomial.mulVarMon j j').polyExp s ≤ 1 := by
  simp only [ZMonomial.mulVarMon]
  by_cases hj : s = j
  · rw [if_pos hj, if_neg (by rw [hj]; exact h)]
  · rw [if_neg hj]; split <;> omega

/-- Every monomial of `chainEqList c i` has per-slot polynomial degree at most `1`: the
left side `S_{c,i}` is built from `varMon`/`negVarMon` (indicator exponents) and
`mulVarMon` at the two distinct slots `chainSlot c (i-1)` and `cubeSlot c` (distinct by
`cubeSlot_ne_chainSlot`). -/
theorem chainEqList_polyExp_le_one {p k d : ℕ} (c : Fin k) (i : Fin d)
    (mon : ZMonomial (p + k + k * d)) (hmon : mon ∈ chainEqList c i) (s : Fin (p + k + k * d)) :
    mon.polyExp s ≤ 1 := by
  unfold chainEqList at hmon
  split at hmon
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmon
    rcases hmon with rfl | rfl
    · exact ZMonomial.varMon_polyExp_le_one _ s
    · exact ZMonomial.negVarMon_polyExp_le_one _ s
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmon
    rcases hmon with rfl | rfl
    · exact ZMonomial.mulVarMon_polyExp_le_one _ _
        (fun heq => cubeSlot_ne_chainSlot c c _ heq.symm) s
    · exact ZMonomial.negVarMon_polyExp_le_one _ s

/-- A monomial of `ZMonomial.listMul L₁ L₂` is a product `a.mul b` of a member `a ∈ L₁`
and a member `b ∈ L₂`: the list is the `flatMap` of the pairwise products. -/
theorem ZMonomial.mem_listMul {m : ℕ} {L₁ L₂ : List (ZMonomial m)} {mon : ZMonomial m}
    (hmon : mon ∈ ZMonomial.listMul L₁ L₂) :
    ∃ a ∈ L₁, ∃ b ∈ L₂, mon = a.mul b := by
  unfold ZMonomial.listMul at hmon
  rw [List.mem_flatMap] at hmon
  obtain ⟨a, ha, hb⟩ := hmon
  rw [List.mem_map] at hb
  obtain ⟨b, hb, rfl⟩ := hb
  exact ⟨a, ha, b, hb, rfl⟩

/-- Every monomial of `chainEqs` has per-slot polynomial degree at most `2`: each
monomial is a product `a.mul b` of two `chainEqList` monomials (via
`ZMonomial.mem_listMul`), whose exponents sum (`ZMonomial.mul`) and are each at most `1`
(`chainEqList_polyExp_le_one`). -/
theorem chainEqs_degree {p k d : ℕ} (mon : ZMonomial (p + k + k * d))
    (hmon : mon ∈ (chainEqs : List (ZMonomial (p + k + k * d)))) (s : Fin (p + k + k * d)) :
    mon.polyExp s ≤ 2 := by
  unfold chainEqs at hmon
  rw [List.mem_flatMap] at hmon
  obtain ⟨c, _, hmon⟩ := hmon
  rw [List.mem_flatMap] at hmon
  obtain ⟨i, _, hmon⟩ := hmon
  obtain ⟨a, ha, b, hb, rfl⟩ := ZMonomial.mem_listMul hmon
  simp only [ZMonomial.mul]
  have hab := chainEqList_polyExp_le_one c i a ha s
  have hbb := chainEqList_polyExp_le_one c i b hb s
  omega

/-- Lower each cube slot's polynomial degree to `0`, depositing the removed degree at the
matching chain slot. The sign, coefficient, and exponential coefficients are unchanged.
The polynomial exponent at slot `j` is: `0` at a cube slot `cubeSlot c`; at a chain slot
`chainSlot c i` (recovered from the trailing block by `finProdFinEquiv.symm`) the original
exponent plus `1` when `mon`'s cube degree at `c` is exactly `i + 1` (the level this chain
slot represents); and the original exponent at a parameter slot. Equivalently, a cube
degree `e + 1` deposits at chain level `e`. This realises the substitution
`x_c^{i+1} ↦ y_{c,i+1}` of arXiv:2407.12928, Lemma 3.5. -/
def chainSub {p k d : ℕ} (mon : ZMonomial (p + k + k * d)) : ZMonomial (p + k + k * d) where
  sign := mon.sign
  coeff := mon.coeff
  expCoeff := mon.expCoeff
  polyExp := fun j =>
    Fin.addCases
      (fun j₁ : Fin (p + k) => Fin.addCases (fun _ : Fin p => mon.polyExp j)
        (fun _ : Fin k => 0) j₁)
      (fun j₂ : Fin (k * d) =>
        mon.polyExp j
          + (if mon.polyExp (cubeSlot (finProdFinEquiv.symm j₂).1)
              = (finProdFinEquiv.symm j₂).2.val + 1 then 1 else 0))
      j

/-- `chainSub` zeroes every cube slot: the cube branch of the classification returns
`0`. -/
theorem chainSub_polyExp_cubeSlot {p k d : ℕ} (mon : ZMonomial (p + k + k * d)) (c : Fin k) :
    (chainSub mon).polyExp (cubeSlot c) = 0 := by
  simp only [chainSub, cubeSlot, Fin.addCases_left, Fin.addCases_right]

/-- `chainSub` at a chain slot `chainSlot c i` keeps the original exponent and deposits an
extra `1` when `mon`'s cube degree at `c` equals `i + 1`. The chain branch recovers `(c,
i)` from the trailing block by `finProdFinEquiv.symm (chainIdx c i) = (c, i)`. -/
theorem chainSub_polyExp_chainSlot {p k d : ℕ} (mon : ZMonomial (p + k + k * d))
    (c : Fin k) (i : Fin d) :
    (chainSub mon).polyExp (chainSlot c i)
      = mon.polyExp (chainSlot c i)
        + (if mon.polyExp (cubeSlot c) = i.val + 1 then 1 else 0) := by
  simp only [chainSub, chainSlot, Fin.addCases_right]
  rw [show finProdFinEquiv.symm (chainIdx c i) = (c, i) from by
    rw [chainIdx, Equiv.symm_apply_apply]]

/-- `chainSub` preserves the per-slot degree bound `≤ 1` for a monomial whose chain
slots all carry exponent `0` (the weakened monomials produced by `SosSystem.toZ` along
`castAddEmb`). Cube slots become `0`; a chain slot's exponent is `0` (by the hypothesis)
plus at most `1` (the deposit); a parameter slot is unchanged, hence `≤ 1` by the input
bound. -/
theorem chainSub_polyExp_le_one {p k d : ℕ} (mon : ZMonomial (p + k + k * d))
    (hbound : ∀ j, mon.polyExp j ≤ 1)
    (hchain : ∀ (c : Fin k) (i : Fin d), mon.polyExp (chainSlot c i) = 0)
    (j : Fin (p + k + k * d)) :
    (chainSub mon).polyExp j ≤ 1 := by
  simp only [chainSub]
  induction j using Fin.addCases with
  | left j₁ =>
    rw [Fin.addCases_left]
    induction j₁ using Fin.addCases with
    | left pp => rw [Fin.addCases_left]; exact hbound _
    | right c => rw [Fin.addCases_right]; exact Nat.zero_le 1
  | right j₂ =>
    rw [Fin.addCases_right]
    have hcj : mon.polyExp (Fin.natAdd (p + k) j₂)
        = mon.polyExp (chainSlot (finProdFinEquiv.symm j₂).1 (finProdFinEquiv.symm j₂).2) := by
      rw [chainSlot, chainIdx, Equiv.apply_symm_apply]
    rw [hcj, hchain]
    split <;> omega

/-- The chain-substitution predicate on a context: each chain slot `y_{c,i+1}` holds the
power `x_c^{i+1}` of its cube coordinate. This is the sub-domain on which `chainSub`
preserves the monomial denotation (`chainSub_eval`). -/
def ChainHolds {p k d : ℕ} (ρ : Fin (p + k + k * d) → ℕ) : Prop :=
  ∀ (c : Fin k) (i : Fin d), ρ (chainSlot c i) = ρ (cubeSlot c) ^ (i.val + 1)

/-- The per-cube reconciliation of the chain-substitution: under `ChainHolds`, the chain
block's deposit product for a fixed cube coordinate `c` collapses to the cube power
`(ρ (cubeSlot c)) ^ (mon.polyExp (cubeSlot c))`, provided the cube degree fits the chain
length (`≤ d`). When the degree is `0` every deposit vanishes and the product is `1`; when
it is `e + 1 ≤ d` the single chain slot at level `e` contributes
`ρ (chainSlot c ⟨e, _⟩) = ρ (cubeSlot c) ^ (e + 1)`. -/
theorem chainSub_cube_prod {p k d : ℕ} (mon : ZMonomial (p + k + k * d))
    (ρ : Fin (p + k + k * d) → ℕ) (hchain : ChainHolds ρ) (c : Fin k)
    (hdeg : mon.polyExp (cubeSlot c) ≤ d) :
    (∏ i : Fin d, (ρ (chainSlot c i)) ^ (if mon.polyExp (cubeSlot c) = i.val + 1 then 1 else 0))
      = (ρ (cubeSlot c)) ^ (mon.polyExp (cubeSlot c)) := by
  rcases Nat.eq_zero_or_pos (mon.polyExp (cubeSlot c)) with h0 | hpos
  · rw [h0, pow_zero]
    apply Finset.prod_eq_one
    intro i _
    rw [if_neg (by omega), pow_zero]
  · obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero (n := mon.polyExp (cubeSlot c)) (by omega)
    have hed : e < d := by omega
    rw [Finset.prod_eq_single (⟨e, hed⟩ : Fin d)]
    · rw [if_pos (by rw [he]), pow_one, hchain c ⟨e, hed⟩]
      congr 1
      have hv : (⟨e, hed⟩ : Fin d).val = e := rfl
      omega
    · intro i _ hi
      rw [if_neg ?_, pow_zero]
      intro hc
      apply hi
      apply Fin.ext
      have hv : (⟨e, hed⟩ : Fin d).val = e := rfl
      omega
    · intro hcon; exact absurd (Finset.mem_univ _) hcon

/-- `chainSub` leaves the polynomial exponent of a parameter slot unchanged: the
parameter branch of the classification returns `mon.polyExp` at the slot. -/
theorem chainSub_polyExp_param {p k d : ℕ} (mon : ZMonomial (p + k + k * d)) (pp : Fin p) :
    (chainSub mon).polyExp (Fin.castAdd (k * d) (Fin.castAdd k pp))
      = mon.polyExp (Fin.castAdd (k * d) (Fin.castAdd k pp)) := by
  simp only [chainSub, Fin.addCases_left]

/-- The polynomial-factor product is invariant under `chainSub` on the `ChainHolds`
sub-domain, when the cube degrees fit the chain length. Splitting the product over the
parameter, cube, and chain blocks (`Fin.prod_univ_add`): parameter factors are unchanged;
the cube block of `chainSub` is `1` while `mon`'s cube block is matched by `chainSub`'s
chain-block deposits (reindexed by `finProdFinEquiv` and reconciled per cube by
`chainSub_cube_prod`); `mon`'s chain block is `1` by `hweak`. -/
theorem chainSub_polyProd {p k d : ℕ} (mon : ZMonomial (p + k + k * d))
    (ρ : Fin (p + k + k * d) → ℕ) (hchain : ChainHolds ρ)
    (hweak : ∀ (c : Fin k) (i : Fin d), mon.polyExp (chainSlot c i) = 0)
    (hdeg : ∀ c : Fin k, mon.polyExp (cubeSlot c) ≤ d) :
    (∏ j, (ρ j) ^ ((chainSub mon).polyExp j)) = ∏ j, (ρ j) ^ (mon.polyExp j) := by
  rw [Fin.prod_univ_add (a := p + k) (b := k * d)
        (fun j => (ρ j) ^ ((chainSub mon).polyExp j)),
    Fin.prod_univ_add (a := p + k) (b := k * d) (fun j => (ρ j) ^ (mon.polyExp j)),
    Fin.prod_univ_add (a := p) (b := k)
        (fun j₁ => (ρ (Fin.castAdd (k * d) j₁)) ^
          ((chainSub mon).polyExp (Fin.castAdd (k * d) j₁))),
    Fin.prod_univ_add (a := p) (b := k)
        (fun j₁ => (ρ (Fin.castAdd (k * d) j₁)) ^ (mon.polyExp (Fin.castAdd (k * d) j₁)))]
  -- the parameter blocks coincide; rewrite the cube, chain (mon), and chain (chainSub) blocks
  have hparam : (∏ pp : Fin p,
        (ρ (Fin.castAdd (k * d) (Fin.castAdd k pp))) ^
          ((chainSub mon).polyExp (Fin.castAdd (k * d) (Fin.castAdd k pp))))
      = ∏ pp : Fin p,
        (ρ (Fin.castAdd (k * d) (Fin.castAdd k pp))) ^
          (mon.polyExp (Fin.castAdd (k * d) (Fin.castAdd k pp))) :=
    Finset.prod_congr rfl (fun pp _ => by rw [chainSub_polyExp_param])
  have hcubeSub : (∏ c : Fin k,
        (ρ (Fin.castAdd (k * d) (Fin.natAdd p c))) ^
          ((chainSub mon).polyExp (Fin.castAdd (k * d) (Fin.natAdd p c)))) = 1 := by
    apply Finset.prod_eq_one
    intro c _
    rw [show Fin.castAdd (k * d) (Fin.natAdd p c) = cubeSlot c from rfl,
      chainSub_polyExp_cubeSlot, pow_zero]
  have hchainMon : (∏ j₂ : Fin (k * d),
        (ρ (Fin.natAdd (p + k) j₂)) ^ (mon.polyExp (Fin.natAdd (p + k) j₂))) = 1 := by
    apply Finset.prod_eq_one
    intro j₂ _
    rw [show Fin.natAdd (p + k) j₂
          = chainSlot (finProdFinEquiv.symm j₂).1 (finProdFinEquiv.symm j₂).2 from by
        rw [chainSlot, chainIdx, Equiv.apply_symm_apply], hweak, pow_zero]
  rw [hparam, hcubeSub, hchainMon, mul_one, mul_one]
  -- remaining: chainSub chain block = mon cube block (the common param block cancels)
  congr 1
  rw [show (∏ j₂ : Fin (k * d),
        (ρ (Fin.natAdd (p + k) j₂)) ^ ((chainSub mon).polyExp (Fin.natAdd (p + k) j₂)))
      = ∏ q : Fin k × Fin d,
        (ρ (chainSlot q.1 q.2)) ^ (if mon.polyExp (cubeSlot q.1) = q.2.val + 1 then 1 else 0)
        from by
      rw [← Equiv.prod_comp finProdFinEquiv
        (fun j₂ => (ρ (Fin.natAdd (p + k) j₂)) ^
          ((chainSub mon).polyExp (Fin.natAdd (p + k) j₂)))]
      apply Finset.prod_congr rfl
      intro q _
      rw [show (finProdFinEquiv q : Fin (k * d)) = chainIdx q.1 q.2 from rfl,
        show Fin.natAdd (p + k) (chainIdx q.1 q.2) = chainSlot q.1 q.2 from rfl,
        chainSub_polyExp_chainSlot, hweak, Nat.zero_add]]
  rw [Fintype.prod_prod_type
    (fun q : Fin k × Fin d =>
      (ρ (chainSlot q.1 q.2)) ^ (if mon.polyExp (cubeSlot q.1) = q.2.val + 1 then 1 else 0))]
  apply Finset.prod_congr rfl
  intro c _
  exact chainSub_cube_prod mon ρ hchain c (hdeg c)

/-- `chainSub` preserves the monomial denotation on the `ChainHolds` sub-domain, when
the cube degrees fit the chain length and the monomial's chain slots all carry exponent
`0`. The sign, coefficient, and exponential-coefficient factors are identical to those of
`mon`; the polynomial-factor products agree by `chainSub_polyProd`, which moves each cube
power to its matching chain slot using `ChainHolds`. This is the substitution correctness
of arXiv:2407.12928, Lemma 3.5. The `hdeg` hypothesis (cube degree at most the chain
length `d`) is met downstream by choosing `d ≥ ZMonomial.maxCubeDegree`. -/
theorem chainSub_eval {p k d : ℕ} (mon : ZMonomial (p + k + k * d))
    (ρ : Fin (p + k + k * d) → ℕ) (hchain : ChainHolds ρ)
    (hweak : ∀ (c : Fin k) (i : Fin d), mon.polyExp (chainSlot c i) = 0)
    (hdeg : ∀ c : Fin k, mon.polyExp (cubeSlot c) ≤ d) :
    (chainSub mon).eval ρ = mon.eval ρ := by
  unfold ZMonomial.eval
  congr 2
  exact congrArg Int.ofNat (chainSub_polyProd mon ρ hchain hweak hdeg)

end GebLean

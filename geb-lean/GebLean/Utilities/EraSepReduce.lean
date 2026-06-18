import GebLean.Utilities.EraDiophantine
import Mathlib.Algebra.BigOperators.Ring.Finset
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

end GebLean

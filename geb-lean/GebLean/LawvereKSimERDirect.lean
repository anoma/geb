import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp
import GebLean.LawvereKSimQuot
import GebLean.LawvereERQuot
import GebLean.Utilities.KSimSzudzikSimrec

/-!
# Direct-translation construction `kToERDirect : K^sim → ER`

Translation of K^sim term-language morphisms (depth ≤ 2)
to elementary-recursive `ERMor1` terms by structural
recursion on the K^sim term.  Atomic constructors map to
ER atoms; `comp` and `raise` recurse; `simrec` at depth
≤ 2 (children at depth ≤ 1) is encoded via Szudzik
pairing and `ERMor1.boundedRec` with a pointwise tower
bound (`kSimTowerBound`).

This is **not** the load-bearing forward functor of the
ER ↔ K^sim_2 categorical equivalence.  The published
proofs of `K^sim_2 ⊆ ER` (Tourlakis 2018 §0.1.0.44 via
§0.1.0.43 Ritchie–Cobham and §0.1.0.15 `K^sim_n = L_n`)
do not bound the K^sim function value pointwise by an
ER expression; they bound the runtime of a register-
machine simulator and lift to ER membership through a
runtime-bound theorem.  The categorical equivalence is
therefore being developed via a separate URM-simulation
construction; see the forthcoming `LawvereKSimER` module
and `docs/research/2026-05-02-ksim-to-er-architectural-pivot-handoff.md`.

The level-0 and level-1 dominance results downstream of
this module (`kToERDirect_linearBound_dominates_level_zero`,
`kToERDirect_linearBound_dominates_level_one`) are valid
mathematical statements about K^sim values bounded by ER
expressions and remain available for downstream uses
independent of the categorical-equivalence construction.

See `docs/plans/2026-04-29-lawvere-k-sim-ktoer-design.md`
for the original direct-translation design (now
superseded as the equivalence path).
-/

namespace GebLean

/-- Forward translation: maps a K^sim morphism of level
≤ 2 to an `ERMor1` term of the same arity.  Defined by
structural recursion on the K^sim term; each case
discharges its level-bound assumption to the recursive
calls.  The simrec case composes C5 helpers from
`Utilities/KSimSzudzikSimrec.lean`. -/
def kToERDirect : {a : ℕ} → (f : KMor1 a) → f.level ≤ 2 →
    ERMor1 a
  | _, .zero,        _ => ERMor1.zeroN _
  | _, .succ,        _ => ERMor1.succ
  | _, .proj i,      _ => ERMor1.proj i
  | _, .comp f gs,   h => by
      have hf : f.level ≤ 2 := by
        unfold KMor1.level at h
        exact le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 2 := fun i => by
        unfold KMor1.level at h
        have hsup : Finset.univ.sup
            (fun j => (gs j).level) ≤ 2 :=
          le_trans (le_max_right _ _) h
        exact le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          hsup
      exact ERMor1.comp (kToERDirect f hf)
        (fun i => kToERDirect (gs i) (hgs i))
  | _, .simrec (a := a) (k := k) i h g, hyp => by
      have hh : ∀ j, (h j).level ≤ 1 := fun j => by
        unfold KMor1.level at hyp
        have hsup_le : Finset.univ.sup
            (fun j => (h j).level) ≤ 1 := by omega
        exact le_trans
          (Finset.le_sup (f := fun j => (h j).level)
            (Finset.mem_univ j))
          hsup_le
      have hg_lvl : ∀ j, (g j).level ≤ 1 := fun j => by
        unfold KMor1.level at hyp
        have hsup_le : Finset.univ.sup
            (fun j => (g j).level) ≤ 1 := by omega
        exact le_trans
          (Finset.le_sup (f := fun j => (g j).level)
            (Finset.mem_univ j))
          hsup_le
      have h_le_2 : ∀ j, (h j).level ≤ 2 := fun j =>
        le_trans (hh j) (by norm_num)
      have g_le_2 : ∀ j, (g j).level ≤ 2 := fun j =>
        le_trans (hg_lvl j) (by norm_num)
      let h_ER : Fin (k + 1) → ERMor1 a :=
        fun j => kToERDirect (h j) (h_le_2 j)
      let g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
        fun j => kToERDirect (g j) (g_le_2 j)
      let recur : ERMor1 (a + 1) :=
        ERMor1.boundedRec
          (kSimPackedBase h_ER)
          (kSimPackedStep g_ER)
          (kSimTowerBound h_ER g_ER)
      exact ERMor1.comp
        (kSimSzudzikUnpackAt a i.val) (fun j =>
          if h_eq : j.val = 0 then recur
          else ERMor1.proj (k := a + 1)
            ⟨j.val, by
              have := j.isLt; omega⟩)
  | _, .raise f,     h => by
      have hf : f.level ≤ 2 := by
        unfold KMor1.level at h
        omega
      exact kToERDirect f hf

/-- Multi-output forward translation: pointwise lift of
`kToERDirect` over a `KMorN` family. -/
def kToERNDirect {a m : ℕ} (f : KMorN a m)
    (h : ∀ i, (f i).level ≤ 2) : ERMorN a m :=
  fun i => kToERDirect (f i) (h i)

end GebLean

import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp
import GebLean.LawvereKSimQuot
import GebLean.LawvereERQuot
import GebLean.Utilities.KSimSzudzikSimrec

/-!
# Forward translation `kToER : K^sim → ER`

Translation of K^sim term-language morphisms (depth ≤ 2)
to elementary-recursive `ERMor1` terms.  Atomic
constructors map to ER atoms; `comp` and `raise` recurse;
`simrec` at depth ≤ 2 (children at depth ≤ 1) is encoded
via Szudzik pairing and `ERMor1.boundedRec` with a tower
bound.

The function-level translation `kToER` is paired with a
multi-output companion `kToERN` and an
interp-preservation theorem `kToER_interp` /
`kToERN_interp`.  The translation is then lifted to a
categorical functor
`kToERFunctor : KSimMor 2 ⥤ LawvereERCat` using the
data-bearing `KMorNQuo.atDepth` Setoid quotient from
Phase 1's refactored `LawvereKSimQuot.lean`.

See `docs/plans/2026-04-29-lawvere-k-sim-ktoer-design.md`.
-/

namespace GebLean

/-- Forward translation: maps a K^sim morphism of level
≤ 2 to an `ERMor1` term of the same arity.  Defined by
structural recursion on the K^sim term; each case
discharges its level-bound assumption to the recursive
calls.  The simrec case composes C5 helpers from
`Utilities/KSimSzudzikSimrec.lean`. -/
def kToER : {a : ℕ} → (f : KMor1 a) → f.level ≤ 2 →
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
      exact ERMor1.comp (kToER f hf)
        (fun i => kToER (gs i) (hgs i))
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
        fun j => kToER (h j) (h_le_2 j)
      let g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
        fun j => kToER (g j) (g_le_2 j)
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
      exact kToER f hf

/-- Multi-output forward translation: pointwise lift of
`kToER` over a `KMorN` family. -/
def kToERN {a m : ℕ} (f : KMorN a m)
    (h : ∀ i, (f i).level ≤ 2) : ERMorN a m :=
  fun i => kToER (f i) (h i)

end GebLean

import GebLean.LawvereER
import GebLean.LawvereERQuot
import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp
import GebLean.LawvereKSimMajorization
import GebLean.LawvereKSimQuot
import GebLean.Utilities.ERAMajorants
import GebLean.Utilities.ERSimultaneousBoundedRec

/-!
# Forward functor `kToER : KMor1 → ERMor1` (level ≤ 2)

Realises Tourlakis 2018 §0.1.0.44 ⊆-direction pointwise:
every K^sim morphism of level ≤ 2 translates structurally
to an `ERMor1` term, with the simrec node routed through
`ERMor1.simultaneousBoundedRec` (step 2) using the bound
from `KMor1.majorize_by_componentBound` (step 4).
Master design §3.5.
-/

namespace GebLean

/-- Forward translation `KMor1 a → ERMor1 a` for K^sim
morphisms of level ≤ 2.  Atomic constructors map to ER
atoms; `comp` and `raise` recurse structurally; `simrec`
routes through `ERMor1.simultaneousBoundedRec` with the
bound from `KMor1.majorize_by_componentBound` (step 4).
Master design §3.5; Tourlakis 2018 §0.1.0.44 ⊆ direction. -/
def kToER : ∀ {a : ℕ} (f : KMor1 a), f.level ≤ 2 → ERMor1 a
  | _, .zero,         _ => ERMor1.zeroN _
  | _, .succ,         _ => ERMor1.succ
  | _, .proj i,       _ => ERMor1.proj i
  | _, .comp f gs,    h =>
      have hf  : f.level ≤ 2 :=
        le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 2 := fun i =>
        le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          (le_trans (le_max_right _ _) h)
      ERMor1.comp (kToER f hf)
        (fun i => kToER (gs i) (hgs i))
  | _, .raise f,      h =>
      have hf : f.level ≤ 2 := by
        unfold KMor1.level at h; omega
      kToER f hf
  | _, .simrec (a := a) (k := k) i h_fam g_fam, hyp =>
      have h_h : ∀ j, (h_fam j).level ≤ 2 := fun j => by
        have h1 : (h_fam j).level ≤ 1 :=
          le_trans
            (Finset.le_sup
              (f := fun l => (h_fam l).level)
              (Finset.mem_univ j))
            (le_trans (le_max_left _ _)
              (Nat.le_of_succ_le_succ
                (by unfold KMor1.level at hyp; exact hyp)))
        omega
      have h_g : ∀ j, (g_fam j).level ≤ 2 := fun j => by
        have h1 : (g_fam j).level ≤ 1 :=
          le_trans
            (Finset.le_sup
              (f := fun l => (g_fam l).level)
              (Finset.mem_univ j))
            (le_trans (le_max_right _ _)
              (Nat.le_of_succ_le_succ
                (by unfold KMor1.level at hyp; exact hyp)))
        omega
      let bases : Fin (k + 1) → ERMor1 a :=
        fun j => kToER (h_fam j) (h_h j)
      let steps : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
        fun j => kToER (g_fam j) (h_g j)
      let p : ℕ × ℕ :=
        KMor1.majorize (.simrec i h_fam g_fam) hyp
      let bound : ERMor1 (a + 1) :=
        ERMor1.comp (ERMor1.A_two_iter p.1)
          (fun _ : Fin 1 => ERMor1.sumCtxERPlusOffset (a + 1) p.2)
      ERMor1.simultaneousBoundedRec k a bases steps bound i

end GebLean

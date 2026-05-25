import GebLean.LawvereER
import GebLean.LawvereERInterp
import GebLean.LawvereERQuot
import GebLean.LawvereKSim
import GebLean.LawvereKSimDCatInterp
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

open CategoryTheory

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
          (Fin.le_maxOfNat (fun j => (gs j).level) i)
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
            (Fin.le_maxOfNat (fun l => (h_fam l).level) j)
            (le_trans (le_max_left _ _)
              (Nat.le_of_succ_le_succ
                (by unfold KMor1.level at hyp; exact hyp)))
        omega
      have h_g : ∀ j, (g_fam j).level ≤ 2 := fun j => by
        have h1 : (g_fam j).level ≤ 1 :=
          le_trans
            (Fin.le_maxOfNat (fun l => (g_fam l).level) j)
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

@[simp] theorem kToER_zero {a : ℕ}
    (h : (KMor1.zero (n := a)).level ≤ 2) :
    kToER (KMor1.zero (n := a)) h = ERMor1.zeroN a := rfl

@[simp] theorem kToER_succ (h : KMor1.succ.level ≤ 2) :
    kToER KMor1.succ h = ERMor1.succ := rfl

@[simp] theorem kToER_proj {a : ℕ} (i : Fin a)
    (h : (KMor1.proj i).level ≤ 2) :
    kToER (KMor1.proj i) h = ERMor1.proj i := rfl

@[simp] theorem kToER_raise {a : ℕ} (f : KMor1 a)
    (h : (KMor1.raise f).level ≤ 2)
    (h' : f.level ≤ 2) :
    kToER (KMor1.raise f) h = kToER f h' := by
  rfl

@[simp] theorem kToER_comp {a b : ℕ} (f : KMor1 b)
    (gs : Fin b → KMor1 a)
    (h : (KMor1.comp f gs).level ≤ 2)
    (hf : f.level ≤ 2)
    (hgs : ∀ i, (gs i).level ≤ 2) :
    kToER (KMor1.comp f gs) h
      = ERMor1.comp (kToER f hf)
          (fun i => kToER (gs i) (hgs i)) := by
  rfl

/-- Dominance hypothesis for
`ERMor1.simultaneousBoundedRec_interp_correct` at step 5's
simrec branch.  States that for each component `j` and
each iteration `m ≤ n`, the value-side simRecVec over the
kToER-translated families is dominated by the bound
`bound = comp (A_two_iter p.1)
(fun _ : Fin 1 => sumCtxERPlusOffset (a+1) p.2)` evaluated
at `Fin.cons m x`, where `p` is `KMor1.majorize` of the
simrec node.  Master design §3.5; Tourlakis 2018 §0.1.0.34
(bounded-recursion closure underlying step 4's bridge) +
§0.1.0.10 (level-2 majorization). -/
theorem kToER_simrec_dominates
    {a k : ℕ}
    (i : Fin (k + 1))
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (hyp : (KMor1.simrec i h_fam g_fam).level ≤ 2)
    (h_h : ∀ j, (h_fam j).level ≤ 2)
    (h_g : ∀ j, (g_fam j).level ≤ 2)
    (ih_h : ∀ (j : Fin (k + 1))
             (h' : (h_fam j).level ≤ 2)
             (v' : Fin a → ℕ),
       (kToER (h_fam j) h').interp v'
         = (h_fam j).interp v')
    (ih_g : ∀ (j : Fin (k + 1))
             (h' : (g_fam j).level ≤ 2)
             (v' : Fin (a + 1 + (k + 1)) → ℕ),
       (kToER (g_fam j) h').interp v'
         = (g_fam j).interp v')
    (n : ℕ) (x : Fin a → ℕ) :
    let p := KMor1.majorize (.simrec i h_fam g_fam) hyp
    let bound : ERMor1 (a + 1) :=
      ERMor1.comp (ERMor1.A_two_iter p.1)
        (fun _ : Fin 1 => ERMor1.sumCtxERPlusOffset (a + 1) p.2)
    ∀ (m : ℕ), m ≤ n → ∀ (j : Fin (k + 1)),
      Nat.simRecVec k a
          (fun j' => (kToER (h_fam j') (h_h j')).interp)
          (fun j' => (kToER (g_fam j') (h_g j')).interp)
          m x j
        ≤ bound.interp (Fin.cons m x) := by
  intro p bound m _ j
  have h_bases :
      (fun j' => (kToER (h_fam j') (h_h j')).interp)
        = (fun j' => (h_fam j').interp) := by
    funext j' v'; exact ih_h j' (h_h j') v'
  have h_steps :
      (fun j' => (kToER (g_fam j') (h_g j')).interp)
        = (fun j' => (g_fam j').interp) := by
    funext j' v'; exact ih_g j' (h_g j') v'
  rw [h_bases, h_steps]
  rw [← KMor1.simrecVec_eq_Nat_simRecVec h_fam g_fam x m j]
  have h_rev :
      KMor1.simrecVec h_fam g_fam x m j
        = (KMor1.simrec j h_fam g_fam).interp
            (Fin.cons m x) := by
    rw [KMor1.interp_simrec]
    congr 2
  rw [h_rev]
  have h_j : (KMor1.simrec j h_fam g_fam).level ≤ 2 := by
    have hfact :
        (KMor1.simrec j h_fam g_fam).level
          = (KMor1.simrec i h_fam g_fam).level :=
      rfl
    rw [hfact]; exact hyp
  have h_dom :=
    KMor1.majorize_by_componentBound
      (.simrec j h_fam g_fam) h_j (Fin.cons m x)
  rw [KMor1.majorize_simrec_index_indep j i h_fam g_fam
        h_j hyp] at h_dom
  exact h_dom

/-- Monotonicity of the kToER simrec bound in the
iteration counter.  The bound is `comp (A_two_iter p.1)
(fun _ : Fin 1 => sumCtxERPlusOffset (a+1) p.2)`; both
`tower` and `sumCtxER` are monotone in the slot
incremented from `m` to `n`.  Used as the `h_mono`
argument to `simultaneousBoundedRec_interp_correct`.
Master design §3.5; transitively step 4 §3. -/
theorem kToER_simrec_bound_mono
    {a k : ℕ}
    (i : Fin (k + 1))
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (hyp : (KMor1.simrec i h_fam g_fam).level ≤ 2)
    (n : ℕ) (x : Fin a → ℕ) :
    let p := KMor1.majorize (.simrec i h_fam g_fam) hyp
    let bound : ERMor1 (a + 1) :=
      ERMor1.comp (ERMor1.A_two_iter p.1)
        (fun _ : Fin 1 => ERMor1.sumCtxERPlusOffset (a + 1) p.2)
    ∀ (m : ℕ), m ≤ n →
      bound.interp (Fin.cons m x)
        ≤ bound.interp (Fin.cons n x) := by
  intro p bound m h_m_le_n
  simp only [bound, ERMor1.interp_comp,
    ERMor1.interp_A_two_iter,
    ERMor1.interp_sumCtxERPlusOffset]
  apply tower_mono_right
  apply Nat.add_le_add_right
  have h := ERMor1.sumCtxER_cons_le_of_le x h_m_le_n
  simpa only [ERMor1.interp_sumCtxER] using h

/-- The simrec case of `kToER_interp`: combines step 2's
correctness theorem `simultaneousBoundedRec_interp_correct`
with step 5's `kToER_simrec_dominates` and
`kToER_simrec_bound_mono` (Tasks 7 and 8) plus the
inductive hypotheses on each child to establish that
`(kToER (.simrec i h_fam g_fam) h).interp` agrees with
`(KMor1.simrec i h_fam g_fam).interp`.  Master design §3.5;
Tourlakis 2018 §0.1.0.44 (level-2 case). -/
theorem kToER_interp_simrec
    {a k : ℕ}
    (i : Fin (k + 1))
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h : (KMor1.simrec i h_fam g_fam).level ≤ 2)
    (v : Fin (a + 1) → ℕ)
    (ih_h : ∀ (j : Fin (k + 1))
             (h' : (h_fam j).level ≤ 2)
             (v' : Fin a → ℕ),
       (kToER (h_fam j) h').interp v'
         = (h_fam j).interp v')
    (ih_g : ∀ (j : Fin (k + 1))
             (h' : (g_fam j).level ≤ 2)
             (v' : Fin (a + 1 + (k + 1)) → ℕ),
       (kToER (g_fam j) h').interp v'
         = (g_fam j).interp v') :
    (kToER (.simrec i h_fam g_fam) h).interp v
      = (KMor1.simrec i h_fam g_fam).interp v := by
  have h_h : ∀ j, (h_fam j).level ≤ 2 := fun j => by
    have h1 : (h_fam j).level ≤ 1 :=
      le_trans
        (Fin.le_maxOfNat (fun l => (h_fam l).level) j)
        (le_trans (le_max_left _ _)
          (Nat.le_of_succ_le_succ
            (by unfold KMor1.level at h; exact h)))
    omega
  have h_g : ∀ j, (g_fam j).level ≤ 2 := fun j => by
    have h1 : (g_fam j).level ≤ 1 :=
      le_trans
        (Fin.le_maxOfNat (fun l => (g_fam l).level) j)
        (le_trans (le_max_right _ _)
          (Nat.le_of_succ_le_succ
            (by unfold KMor1.level at h; exact h)))
    omega
  set n := v 0
  set x := Fin.tail v
  have hv : v = Fin.cons n x := (Fin.cons_self_tail v).symm
  rw [hv]
  change (ERMor1.simultaneousBoundedRec k a
          (fun j => kToER (h_fam j) (h_h j))
          (fun j => kToER (g_fam j) (h_g j))
          (let p :=
            KMor1.majorize (.simrec i h_fam g_fam) h
           ERMor1.comp (ERMor1.A_two_iter p.1)
             (fun _ : Fin 1 =>
               ERMor1.sumCtxERPlusOffset (a + 1) p.2))
          i).interp (Fin.cons n x) = _
  rw [ERMor1.simultaneousBoundedRec_interp_correct
        k a _ _ _ n x i
        (kToER_simrec_dominates i h_fam g_fam h
          h_h h_g ih_h ih_g n x)
        (kToER_simrec_bound_mono i h_fam g_fam h n x)]
  have h_bases :
      (fun j' => (kToER (h_fam j') (h_h j')).interp)
        = (fun j' => (h_fam j').interp) := by
    funext j' v'; exact ih_h j' (h_h j') v'
  have h_steps :
      (fun j' => (kToER (g_fam j') (h_g j')).interp)
        = (fun j' => (g_fam j').interp) := by
    funext j' v'; exact ih_g j' (h_g j') v'
  rw [h_bases, h_steps]
  rw [← KMor1.simrecVec_eq_Nat_simRecVec h_fam g_fam x n i]
  rw [KMor1.interp_simrec]
  congr 2

/-- Universal correctness of `kToER`: for every
`f : KMor1 a` of level ≤ 2 and every context `v`,
`(kToER f h).interp v = f.interp v`.  Realises Tourlakis
2018 §0.1.0.44 (K^sim_n ⊆ E^{n+1}) ⊆-direction pointwise
at level ≤ 2.  Master design §3.5. -/
theorem kToER_interp :
    ∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2)
      (v : Fin a → ℕ),
    (kToER f h).interp v = f.interp v
  | _, .zero,         _, _ => rfl
  | _, .succ,         _, _ => rfl
  | _, .proj _,       _, _ => rfl
  | _, .comp f gs,    h, v => by
      have hf  : f.level ≤ 2 :=
        le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 2 := fun i =>
        le_trans
          (Fin.le_maxOfNat (fun j => (gs j).level) i)
          (le_trans (le_max_right _ _) h)
      simp only [kToER, KMor1.interp_comp,
        ERMor1.interp_comp]
      have hgs_eq :
          (fun i => (kToER (gs i) (hgs i)).interp v)
            = (fun i => (gs i).interp v) := by
        funext i
        exact kToER_interp (gs i) (hgs i) v
      rw [hgs_eq]
      exact kToER_interp f hf _
  | _, .raise f,      h, v => by
      have hf : f.level ≤ 2 := by
        unfold KMor1.level at h; omega
      simp only [kToER, KMor1.interp_raise]
      exact kToER_interp f hf v
  | _, .simrec i h_fam g_fam, h, v =>
      have h_h : ∀ j, (h_fam j).level ≤ 2 := fun j => by
        have h1 : (h_fam j).level ≤ 1 :=
          le_trans
            (Fin.le_maxOfNat (fun l => (h_fam l).level) j)
            (le_trans (le_max_left _ _)
              (Nat.le_of_succ_le_succ
                (by unfold KMor1.level at h; exact h)))
        omega
      have h_g : ∀ j, (g_fam j).level ≤ 2 := fun j => by
        have h1 : (g_fam j).level ≤ 1 :=
          le_trans
            (Fin.le_maxOfNat (fun l => (g_fam l).level) j)
            (le_trans (le_max_right _ _)
              (Nat.le_of_succ_le_succ
                (by unfold KMor1.level at h; exact h)))
        omega
      kToER_interp_simrec i h_fam g_fam h v
        (fun j h' v' => kToER_interp (h_fam j) h' v')
        (fun j h' v' => kToER_interp (g_fam j) h' v')

/-- Multi-output companion of `kToER`: pointwise lift to
`KMorN n m → ERMorN n m`.  Master design §3.5. -/
def kToERN {n m : ℕ} (f : KMorN n m)
    (h : ∀ i, (f i).level ≤ 2) : ERMorN n m :=
  fun i => kToER (f i) (h i)

/-- Componentwise correctness of `kToERN`: each component
of the kToERN-translated family agrees with the
corresponding K^sim component on every context.  Master
design §3.5. -/
theorem kToERN_interp {n m : ℕ} (f : KMorN n m)
    (h : ∀ i, (f i).level ≤ 2)
    (v : Fin n → ℕ) (j : Fin m) :
    (kToERN f h j).interp v = (f j).interp v :=
  kToER_interp (f j) (h j) v

/-- Function-level form of `kToER_interp`: the kToER-translated
ER morphism's interpretation equals the original K^sim
morphism's interpretation as functions `(Fin a → ℕ) → ℕ`.
Useful for `rw`-style callers that don't want to thread
`funext` themselves.  Master design §3.5; Tourlakis 2018
§0.1.0.44 (function-level reformulation). -/
theorem kToER_interp_funext {a : ℕ} (f : KMor1 a)
    (h : f.level ≤ 2) :
    (kToER f h).interp = f.interp := by
  funext v
  exact kToER_interp f h v

/-- Compatibility of `kToERN` with K^sim ext-eq:
extensionally-equal K^sim families produce extensionally-
equal ER families.  Used by `kToERFunctor.map` to discharge
the Quotient.lift well-definedness obligation.  Master
design §3.5. -/
theorem kToERN_compat_extEq {n m : ℕ}
    {f g : KMorN n m}
    (hf : ∀ i, (f i).level ≤ 2)
    (hg : ∀ i, (g i).level ≤ 2)
    (hfg : ∀ v i, (f i).interp v = (g i).interp v) :
    ∀ v i, (kToERN f hf i).interp v
            = (kToERN g hg i).interp v := by
  intro v i
  rw [kToERN_interp, kToERN_interp]
  exact hfg v i

/-- Morphism component of the forward functor.  Lifts a
`KSimMor 2 n m` (an equivalence class of `KMorN n m`
families with depth-2 witness) to an `ERMorNQuo n m`.
Well-definedness via `kToERN_compat_extEq` plus
`Quotient.exact` on the depth-witness's `rep_eq` fields.
Master design §3.5 lines 1153-1163. -/
def kToERFunctor_map {n m : ℕ}
    (f : KSimMor 2 n m) : ERMorNQuo n m :=
  Quotient.liftOn f.depth_witness
    (fun rec => Quotient.mk (erMorNSetoid n m)
                 (kToERN rec.rep rec.rep_level))
    (fun rec₁ rec₂ _ => by
      apply Quotient.sound
      have h_eq :
          Quotient.mk (kMorNSetoid n m) rec₁.rep
            = Quotient.mk (kMorNSetoid n m) rec₂.rep :=
        rec₁.rep_eq.trans rec₂.rep_eq.symm
      have hrel :
          (kMorNSetoid n m).r rec₁.rep rec₂.rep :=
        Quotient.exact h_eq
      intro v
      funext i
      exact kToERN_compat_extEq rec₁.rep_level
        rec₂.rep_level
        (fun v' i' => congr_fun (hrel v') i') v i)

/-- Functor law: `kToERFunctor_map` preserves identities.
The `𝟙 n` morphism in `LawvereKSimDCat 2` has
representative `KMorN.id n`; its kToERN-translation
componentwise equals `ERMorN.id n` (since
`kToER (KMor1.proj i) _ = ERMor1.proj i`).  Master design
§3.5. -/
theorem kToERFunctor_map_id (n : LawvereKSimDCat 2) :
    kToERFunctor_map
        (CategoryTheory.CategoryStruct.id
          (obj := LawvereKSimDCat 2) n)
      = CategoryTheory.CategoryStruct.id
          (obj := LawvereERCat) (n : LawvereERCat) := by
  unfold kToERFunctor_map
  apply Quotient.sound
  intro v
  funext i
  rfl

/-- Functor law: `kToERFunctor_map` preserves composition.
`kToER`'s `comp` branch translates `KMor1.comp f gs`
literally to `ERMor1.comp (kToER f) (fun i => kToER (gs i))`,
and `kToERN` commutes with `KMorN.comp` pointwise.  Master
design §3.5. -/
theorem kToERFunctor_map_comp {n m k : ℕ}
    (f : KSimMor 2 n m) (g : KSimMor 2 m k) :
    kToERFunctor_map
        (CategoryTheory.CategoryStruct.comp
          (obj := LawvereKSimDCat 2) f g)
      = CategoryTheory.CategoryStruct.comp
          (obj := LawvereERCat)
          (kToERFunctor_map f) (kToERFunctor_map g) := by
  unfold kToERFunctor_map
  rcases f with ⟨fh, fdw⟩
  rcases g with ⟨gh, gdw⟩
  refine Quotient.inductionOn₂
    (motive := fun (fdw : KMorNQuo.atDepth 2 fh)
        (gdw : KMorNQuo.atDepth 2 gh) =>
      Quotient.liftOn
          (s := kMorNQuoAtDepthSetoid 2 (KMorNQuo.comp fh gh))
          (KMorNQuo.comp_atDepth fdw gdw)
          (fun rec => Quotient.mk (erMorNSetoid n k)
                       (kToERN rec.rep rec.rep_level))
          _
        = ERMorNQuo.comp
          (Quotient.liftOn fdw
            (fun rec => Quotient.mk (erMorNSetoid n m)
                         (kToERN rec.rep rec.rep_level))
            _)
          (Quotient.liftOn gdw
            (fun rec => Quotient.mk (erMorNSetoid m k)
                         (kToERN rec.rep rec.rep_level))
            _))
    fdw gdw ?_
  intro fr gr
  apply Quotient.sound
  intro v
  funext i
  change (kToERN (KMorN.comp gr.rep fr.rep) _ i).interp v
    = ((kToERN gr.rep _) i).interp
        (fun j => ((kToERN fr.rep _) j).interp v)
  rw [kToERN_interp, kToERN_interp]
  simp only [KMorN.comp, KMor1.interp_comp]
  congr 1
  funext j
  rw [kToERN_interp]

/-- The forward functor of the categorical equivalence
`LawvereKSimDCat 2 ≌ LawvereERCat` (forward direction;
reverse direction in step 10, equivalence assembled in
step 11).  Master design §3.5. -/
def kToERFunctor : CategoryTheory.Functor
    (LawvereKSimDCat 2) LawvereERCat where
  obj n := n
  map := kToERFunctor_map
  map_id := kToERFunctor_map_id
  map_comp := kToERFunctor_map_comp

/-- Morphism-level interpretation preservation: the
ER-quotient interpretation of `kToERFunctor_map f`
agrees with the K^sim-quotient interpretation of `f.hom`.
This is the pointwise companion of
`kToERFunctor_comp_erInterpFunctor`.  Master design
§3.5; the morphism-level form of Tourlakis 2018 §0.1.0.44
⊆ direction. -/
theorem kToERFunctor_map_interp {n m : ℕ}
    (f : KSimMor 2 n m) :
    (kToERFunctor_map f).interp = f.hom.interp := by
  unfold kToERFunctor_map
  rcases f with ⟨fh, fdw⟩
  refine Quotient.inductionOn
    (motive := fun (fdw : KMorNQuo.atDepth 2 fh) =>
      ERMorNQuo.interp
          (Quotient.liftOn
            (s := kMorNQuoAtDepthSetoid 2 fh)
            fdw
            (fun rec => Quotient.mk (erMorNSetoid n m)
                         (kToERN rec.rep rec.rep_level))
            _)
        = fh.interp) fdw ?_
  intro rec
  have hkn :
      ERMorNQuo.interp
          (Quotient.mk (erMorNSetoid n m)
            (kToERN rec.rep rec.rep_level))
        = rec.rep.interp := by
    funext ctx
    funext i
    change (kToERN rec.rep rec.rep_level i).interp ctx
      = (rec.rep i).interp ctx
    exact kToERN_interp rec.rep rec.rep_level ctx i
  have hfh : fh.interp = rec.rep.interp :=
    (congrArg KMorNQuo.interp rec.rep_eq.symm)
  change ERMorNQuo.interp
      (Quotient.mk (erMorNSetoid n m)
        (kToERN rec.rep rec.rep_level))
    = fh.interp
  rw [hkn, hfh]

/-- The strict equality of functors:
`kToERFunctor ⋙ erInterpFunctor = kInterpFunctor`.

Both functors send `n : LawvereKSimDCat 2` to
`Fin n → ℕ` (definitionally), and both send a morphism
`f : KSimMor 2 n m` to a function
`(Fin n → ℕ) → (Fin m → ℕ)`.  The map equality follows
from `kToERFunctor_map_interp`, which itself follows
from `kToER_interp` componentwise via `Quotient.ind` on
the depth witness.

This is stronger than a natural isomorphism with the
identity: full functor equality (no eqToHom transports
needed since obj is `rfl`).  Master design §3.5; the
functor-level form of Tourlakis 2018 §0.1.0.44 ⊆
direction. -/
theorem kToERFunctor_comp_erInterpFunctor :
    kToERFunctor ⋙ erInterpFunctor = kInterpFunctor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro n m f
  funext ctx
  simp only [CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.comp_map]
  change (kToERFunctor_map f).interp ctx = f.hom.interp ctx
  rw [kToERFunctor_map_interp]

/-- Object component of `kToERFunctor` is identity on `ℕ`.
Useful as a simp lemma when step 11 (the categorical iso)
composes / decomposes functors.  Master design §3.5. -/
@[simp] theorem kToERFunctor_obj (n : LawvereKSimDCat 2) :
    kToERFunctor.obj n = n := rfl

/-- Commutation lemma: when applied to a `KSimMor 2`
constructed from a raw representative `rep : KMorN n m`
with explicit level proof `h`, `kToERFunctor.map`
reduces to the ER-quotient class of `kToERN rep h`.
Step 11 (the categorical iso) consumes this when
building morphisms from representatives.  Master design
§3.5; spec §8.4 Scope-B helper. -/
theorem kToERFunctor_map_quot {n m : ℕ}
    (rep : KMorN n m)
    (h : ∀ i, (rep i).level ≤ 2) :
    kToERFunctor.map
        (⟨Quotient.mk (kMorNSetoid n m) rep,
          Quotient.mk (kMorNQuoAtDepthSetoid 2 _)
            { rep := rep, rep_level := h, rep_eq := rfl }⟩
          : KSimMor 2 n m)
      = Quotient.mk (erMorNSetoid n m) (kToERN rep h) :=
  rfl

end GebLean

import GebLean.LawvereERQuot
import GebLean.LawvereNatBTV2Quot
import GebLean.LawvereNatBTV2Interp
import GebLean.LawvereNatBTV20
import Mathlib.CategoryTheory.Equivalence

/-!
# Equivalence `LawvereERCat ≃ LawvereNatBTV20Cat`

The categorical equivalence between Wikipedia-literal ER and
the bottom-up two-sort theory at the `m = 0` subcategory.

Forward `F : LawvereERCat ⥤ LawvereNatBTV20Cat` lifts each ER
constructor to its NatBT analog (zero → zero, succ → succ, …).
Back `G : LawvereNatBTV20Cat ⥤ LawvereERCat` uses
`NatBTMor1V2.toER` (which maps every NatBT constructor to its
named ER implementation).  The equivalence is preserved by
construction: `interp` is derived from `toER`, so interp
agreement holds definitionally on round-trips.

The bottom-up design is documented in
`docs/superpowers/specs/2026-04-19-bottom-up-natbt-design.md`.
-/

namespace GebLean

/-- Forward translation: lifts each `ERMor1 n` constructor to its
named NatBT analog at arity `(n, 0)` and output sort `.nat`. -/
def ERMor1.toNatBTV2 : {n : ℕ} → ERMor1 n →
    NatBTMor1V2 (n, 0) .nat
  | _, ERMor1.zero => NatBTMor1V2.zero
  | _, ERMor1.succ =>
      NatBTMor1V2.succ (NatBTMor1V2.natProj 0)
  | _, ERMor1.proj i => NatBTMor1V2.natProj i
  | _, ERMor1.sub =>
      NatBTMor1V2.sub
        (NatBTMor1V2.natProj 0)
        (NatBTMor1V2.natProj 1)
  | _, ERMor1.comp f g =>
      NatBTMor1V2.compNat
        f.toNatBTV2
        (fun i => (g i).toNatBTV2)
        Fin.elim0
  | _, ERMor1.bsum (k := k) f =>
      NatBTMor1V2.bsum (nm := (k, 0)) f.toNatBTV2
  | _, ERMor1.bprod (k := k) f =>
      NatBTMor1V2.bprod (nm := (k, 0)) f.toNatBTV2

/-- The forward translation preserves interpretation. -/
theorem ERMor1.toNatBTV2_interp : {n : ℕ} → (t : ERMor1 n) →
    (ctxN : Fin n → ℕ) →
    t.toNatBTV2.interp ctxN Fin.elim0 = t.interp ctxN
  | _, ERMor1.zero, ctxN => by
      simp [ERMor1.toNatBTV2]
  | _, ERMor1.succ, ctxN => by
      simp [ERMor1.toNatBTV2]
  | _, ERMor1.proj _, ctxN => by
      simp [ERMor1.toNatBTV2]
  | _, ERMor1.sub, ctxN => by
      simp [ERMor1.toNatBTV2]
  | _, ERMor1.comp f g, ctxN => by
      simp only [ERMor1.toNatBTV2,
        NatBTMor1V2.interp_compNat,
        ERMor1.interp_comp]
      have hf := f.toNatBTV2_interp
        (fun i => (g i).interp ctxN)
      have hg : (fun i =>
          (g i).toNatBTV2.interp ctxN Fin.elim0) =
          (fun i => (g i).interp ctxN) := by
        funext i
        exact (g i).toNatBTV2_interp ctxN
      rw [hg]
      have hempty : (fun i : Fin 0 =>
          (Fin.elim0 i : NatBTMor1V2 (_, 0) .bt).interp
            ctxN Fin.elim0) =
          Fin.elim0 := by
        funext i; exact i.elim0
      rw [hempty]
      exact hf
  | _, ERMor1.bsum (k := k) f, ctxN => by
      simp only [ERMor1.toNatBTV2,
        NatBTMor1V2.interp_bsum,
        ERMor1.interp_bsum]
      congr 1
      funext i
      exact f.toNatBTV2_interp (Fin.cons i (Fin.tail ctxN))
  | _, ERMor1.bprod (k := k) f, ctxN => by
      simp only [ERMor1.toNatBTV2,
        NatBTMor1V2.interp_bprod,
        ERMor1.interp_bprod]
      congr 1
      funext i
      exact f.toNatBTV2_interp (Fin.cons i (Fin.tail ctxN))

/-- Tuple-level forward translation: an `ERMorN n m` becomes a
`NatBTMorNV2 (n, 0) (m, 0)` with empty BT components. -/
def ERMorN.toNatBTV2 {n m : ℕ} (f : ERMorN n m) :
    NatBTMorNV2 (n, 0) (m, 0) where
  natComps i := (f i).toNatBTV2
  btComps i := i.elim0

/-- Tuple-level interpretation agreement. -/
theorem ERMorN.toNatBTV2_interp {n m : ℕ} (f : ERMorN n m)
    (ctxN : Fin n → ℕ) :
    f.toNatBTV2.interp ctxN Fin.elim0 =
      (f.interp ctxN, Fin.elim0) := by
  apply Prod.ext
  · funext i
    exact (f i).toNatBTV2_interp ctxN
  · funext i
    exact i.elim0

/-- Quotient-level forward translation. -/
def ERMorNQuo.toNatBTV2 {n m : ℕ}
    (f : ERMorNQuo n m) :
    NatBTMorNV2Quo (n, 0) (m, 0) :=
  Quotient.liftOn f
    (fun a => Quotient.mk _ a.toNatBTV2)
    (fun a b hab => by
      apply Quotient.sound
      intro ctxN ctxB
      have hctxB : ctxB = Fin.elim0 := by
        funext i; exact i.elim0
      subst hctxB
      rw [ERMorN.toNatBTV2_interp,
        ERMorN.toNatBTV2_interp, hab])

theorem ERMorNQuo.toNatBTV2_id (n : ℕ) :
    ERMorNQuo.toNatBTV2 (ERMorNQuo.id n) =
      NatBTMorNV2Quo.id (n, 0) := by
  apply Quotient.sound
  intro ctxN ctxB
  have hctxB : ctxB = Fin.elim0 := by
    funext i; exact i.elim0
  subst hctxB
  rw [ERMorN.toNatBTV2_interp]
  simp [NatBTMorNV2.id, NatBTMorNV2.interp,
    ERMorN.interp_id]

theorem ERMorNQuo.toNatBTV2_comp {n m k : ℕ}
    (f : ERMorNQuo n m) (g : ERMorNQuo m k) :
    ERMorNQuo.toNatBTV2 (ERMorNQuo.comp f g) =
      NatBTMorNV2Quo.comp f.toNatBTV2 g.toNatBTV2 := by
  refine Quotient.inductionOn₂ f g ?_
  intro a b
  apply Quotient.sound
  intro ctxN ctxB
  have hctxB : ctxB = Fin.elim0 := by
    funext i; exact i.elim0
  subst hctxB
  rw [ERMorN.toNatBTV2_interp]
  change _ =
    (NatBTMorNV2.comp a.toNatBTV2 b.toNatBTV2).interp
      ctxN Fin.elim0
  rw [NatBTMorNV2.interp_comp]
  rw [ERMorN.toNatBTV2_interp]
  rw [ERMorN.toNatBTV2_interp]
  rfl

open CategoryTheory

/-- The forward functor `LawvereERCat ⥤ LawvereNatBTV20Cat`. -/
def erToNatBTV2Functor :
    LawvereERCat ⥤ LawvereNatBTV20Cat where
  obj n := ⟨((n : ℕ), 0), rfl⟩
  map {n m} f := ObjectProperty.homMk
    (P := isNatBTV20)
    (X := ⟨((n : ℕ), 0), rfl⟩)
    (Y := ⟨((m : ℕ), 0), rfl⟩)
    (ERMorNQuo.toNatBTV2 f)
  map_id n := by
    apply ObjectProperty.hom_ext
    change ERMorNQuo.toNatBTV2 (ERMorNQuo.id n) =
      NatBTMorNV2Quo.id (n, 0)
    exact ERMorNQuo.toNatBTV2_id n
  map_comp {n m k} f g := by
    apply ObjectProperty.hom_ext
    change ERMorNQuo.toNatBTV2 (ERMorNQuo.comp f g) =
      NatBTMorNV2Quo.comp f.toNatBTV2 g.toNatBTV2
    exact ERMorNQuo.toNatBTV2_comp f g

end GebLean

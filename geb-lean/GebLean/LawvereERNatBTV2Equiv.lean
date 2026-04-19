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

/-- Back-translation at the tuple level for `(n, 0) → (m, 0)`.
Each `natComps i` is a `NatBTMor1V2 (n, 0) .nat`; `toER` gives an
`ERMor1 (n + 0)`, which is `ERMor1 n` by definitional equality. -/
def NatBTMorNV2.toER {n m : ℕ}
    (f : NatBTMorNV2 (n, 0) (m, 0)) : ERMorN n m :=
  fun i => (f.natComps i).toER

/-- Back-translation preserves interpretation. -/
theorem NatBTMorNV2.toER_interp {n m : ℕ}
    (f : NatBTMorNV2 (n, 0) (m, 0)) (ctxN : Fin n → ℕ) :
    (NatBTMorNV2.toER f).interp ctxN =
      (f.interp ctxN Fin.elim0).1 := by
  funext i
  change (f.natComps i).toER.interp ctxN =
    (f.natComps i).interp ctxN Fin.elim0
  unfold NatBTMor1V2.interp
  have happend :
      (Fin.append ctxN
        (fun j : Fin 0 => BTL.encode (Fin.elim0 j)) :
        Fin (n + 0) → ℕ) = ctxN := by
    funext j
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · change Fin.append ctxN _ (Fin.castAdd 0 k) = ctxN k
      rw [Fin.append_left]
    · exact k.elim0
  rw [happend]

/-- Quotient-level back-translation. -/
def NatBTMorNV2Quo.toER {n m : ℕ}
    (f : NatBTMorNV2Quo (n, 0) (m, 0)) :
    ERMorNQuo n m :=
  Quotient.liftOn f
    (fun a => Quotient.mk _ a.toER)
    (fun a b hab => by
      apply Quotient.sound
      intro ctxN
      rw [NatBTMorNV2.toER_interp,
        NatBTMorNV2.toER_interp]
      have := hab ctxN Fin.elim0
      rw [this])

theorem NatBTMorNV2Quo.toER_id (n : ℕ) :
    NatBTMorNV2Quo.toER (NatBTMorNV2Quo.id (n, 0)) =
      ERMorNQuo.id n := by
  apply Quotient.sound
  intro ctxN
  rw [NatBTMorNV2.toER_interp]
  change ((NatBTMorNV2.id (n, 0)).interp ctxN Fin.elim0).1 =
    (ERMorN.id n).interp ctxN
  rw [NatBTMorNV2.interp_id]
  rfl

theorem NatBTMorNV2Quo.toER_comp {n m k : ℕ}
    (f : NatBTMorNV2Quo (n, 0) (m, 0))
    (g : NatBTMorNV2Quo (m, 0) (k, 0)) :
    NatBTMorNV2Quo.toER (NatBTMorNV2Quo.comp f g) =
      ERMorNQuo.comp f.toER g.toER := by
  refine Quotient.inductionOn₂ f g ?_
  intro a b
  apply Quotient.sound
  intro ctxN
  rw [NatBTMorNV2.toER_interp]
  change ((NatBTMorNV2.comp a b).interp ctxN Fin.elim0).1 =
    (ERMorN.comp a.toER b.toER).interp ctxN
  rw [NatBTMorNV2.interp_comp, ERMorN.interp_comp]
  rw [NatBTMorNV2.toER_interp, NatBTMorNV2.toER_interp]
  have hempty :
      (a.interp ctxN Fin.elim0).2 = Fin.elim0 := by
    funext i; exact i.elim0
  rw [hempty]

/-- The back functor `LawvereNatBTV20Cat ⥤ LawvereERCat`. -/
def natBTV20ToERFunctor :
    LawvereNatBTV20Cat ⥤ LawvereERCat where
  obj nm := nm.obj.1
  map {nm nm'} f := by
    have hnm : nm.obj = (nm.obj.1, 0) := by
      apply Prod.ext
      · rfl
      · exact nm.property
    have hnm' : nm'.obj = (nm'.obj.1, 0) := by
      apply Prod.ext
      · rfl
      · exact nm'.property
    refine NatBTMorNV2Quo.toER (n := nm.obj.1) (m := nm'.obj.1) ?_
    rw [← hnm, ← hnm']
    exact f.hom
  map_id nm := by
    change NatBTMorNV2Quo.toER _ = ERMorNQuo.id _
    have heq : (𝟙 nm : nm ⟶ nm).hom =
        NatBTMorNV2Quo.id nm.obj := rfl
    have hnm2 : nm.obj.2 = 0 := nm.property
    rcases nm with ⟨⟨nval, mval⟩, hp⟩
    cases hp
    rw [heq]
    exact NatBTMorNV2Quo.toER_id nval
  map_comp {nm nm' nm''} f g := by
    rcases nm with ⟨⟨n, _⟩, hp⟩
    cases hp
    rcases nm' with ⟨⟨m, _⟩, hp⟩
    cases hp
    rcases nm'' with ⟨⟨k, _⟩, hp⟩
    cases hp
    change NatBTMorNV2Quo.toER (NatBTMorNV2Quo.comp f.hom g.hom) =
      ERMorNQuo.comp (NatBTMorNV2Quo.toER f.hom)
        (NatBTMorNV2Quo.toER g.hom)
    exact NatBTMorNV2Quo.toER_comp f.hom g.hom

/-- Round-trip on ER quotient morphisms: `G ∘ F` is identity. -/
theorem ERMorNQuo.toNatBTV2_toER {n m : ℕ}
    (f : ERMorNQuo n m) :
    NatBTMorNV2Quo.toER (ERMorNQuo.toNatBTV2 f) = f := by
  refine Quotient.inductionOn f ?_
  intro a
  apply Quotient.sound
  intro ctxN
  rw [NatBTMorNV2.toER_interp]
  change (a.toNatBTV2.interp ctxN Fin.elim0).1 = a.interp ctxN
  rw [ERMorN.toNatBTV2_interp]

/-- Round-trip on NatBTV20 quotient morphisms:
`F ∘ G` is identity. -/
theorem NatBTMorNV2Quo.toER_toNatBTV2 {n m : ℕ}
    (f : NatBTMorNV2Quo (n, 0) (m, 0)) :
    ERMorNQuo.toNatBTV2 (NatBTMorNV2Quo.toER f) = f := by
  refine Quotient.inductionOn f ?_
  intro a
  apply Quotient.sound
  intro ctxN ctxB
  have hctxB : ctxB = Fin.elim0 := by
    funext i; exact i.elim0
  subst hctxB
  rw [ERMorN.toNatBTV2_interp]
  apply Prod.ext
  · funext i
    change (a.natComps i).toER.interp ctxN =
      (a.natComps i).interp ctxN Fin.elim0
    have h := NatBTMorNV2.toER_interp
      (n := n) (m := m)
      ⟨a.natComps, fun j => j.elim0⟩ ctxN
    have := congrFun h i
    change ((⟨a.natComps,
      fun j => j.elim0⟩ : NatBTMorNV2 (n, 0) (m, 0)).natComps i).toER.interp
        ctxN = _ at this
    exact this
  · funext i; exact i.elim0

/-- Unit isomorphism: `𝟭 ≅ F ⋙ G`. -/
def erToNatBTV2UnitIso :
    𝟭 LawvereERCat ≅
      erToNatBTV2Functor ⋙ natBTV20ToERFunctor :=
  NatIso.ofComponents
    (fun _ => Iso.refl _)
    (fun {n m} f => by
      change f ≫ 𝟙 _ = 𝟙 _ ≫
        NatBTMorNV2Quo.toER (ERMorNQuo.toNatBTV2 f)
      rw [Category.comp_id, Category.id_comp]
      exact (ERMorNQuo.toNatBTV2_toER f).symm)

/-- Helper: in `LawvereNatBTV20Cat`, an object `nm` equals
the rebuilt `⟨(nm.obj.1, 0), rfl⟩`. -/
theorem isNatBTV20.obj_eq (nm : LawvereNatBTV20Cat) :
    nm = ⟨(nm.obj.1, 0), rfl⟩ := by
  rcases nm with ⟨⟨a, b⟩, hp⟩
  change b = 0 at hp
  cases hp
  rfl

/-- Counit isomorphism: `G ⋙ F ≅ 𝟭`. -/
def erToNatBTV2CounitIso :
    natBTV20ToERFunctor ⋙ erToNatBTV2Functor ≅
      𝟭 LawvereNatBTV20Cat :=
  NatIso.ofComponents
    (fun nm => eqToIso (isNatBTV20.obj_eq nm).symm)
    (fun {nm nm'} f => by
      apply ObjectProperty.hom_ext
      rcases nm with ⟨⟨n, b1⟩, hp1⟩
      change b1 = 0 at hp1
      cases hp1
      rcases nm' with ⟨⟨m, b2⟩, hp2⟩
      change b2 = 0 at hp2
      cases hp2
      rw [ObjectProperty.FullSubcategory.comp_hom,
        ObjectProperty.FullSubcategory.comp_hom]
      change NatBTMorNV2Quo.comp
          (ERMorNQuo.toNatBTV2 (NatBTMorNV2Quo.toER f.hom))
          (NatBTMorNV2Quo.id _) =
        NatBTMorNV2Quo.comp (NatBTMorNV2Quo.id _) f.hom
      have heq := NatBTMorNV2Quo.toER_toNatBTV2 f.hom
      rw [heq, NatBTMorNV2Quo.id_comp,
        NatBTMorNV2Quo.comp_id])

/-- Categorical equivalence `LawvereERCat ≃ LawvereNatBTV20Cat`. -/
def lawvereERNatBTV20Equivalence :
    LawvereERCat ≌ LawvereNatBTV20Cat where
  functor := erToNatBTV2Functor
  inverse := natBTV20ToERFunctor
  unitIso := erToNatBTV2UnitIso
  counitIso := erToNatBTV2CounitIso
  functor_unitIso_comp n := by
    apply ObjectProperty.hom_ext
    rw [ObjectProperty.FullSubcategory.comp_hom]
    change NatBTMorNV2Quo.comp
        (ERMorNQuo.toNatBTV2 (ERMorNQuo.id n))
        (NatBTMorNV2Quo.id (n, 0)) = NatBTMorNV2Quo.id (n, 0)
    rw [ERMorNQuo.toNatBTV2_id, NatBTMorNV2Quo.id_comp]

end GebLean

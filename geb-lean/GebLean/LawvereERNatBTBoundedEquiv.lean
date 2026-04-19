import GebLean.LawvereERQuot
import GebLean.LawvereNatBTBoundedQuot
import GebLean.LawvereNatBTBoundedInterp
import GebLean.LawvereNatBTBounded0
import GebLean.Utilities.NatERStyleSoundness
import Mathlib.CategoryTheory.Equivalence

/-!
# Equivalence `LawvereERCat ≃ LawvereNatBTBounded0Cat`

The categorical equivalence between Wikipedia-literal ER and
the bounded two-sort theory at the `m = 0` subcategory.  The
forward translation maps each ER constructor to its NatBT
analog (direct mapping; both theories share `zero`, `succ`,
`proj`, `sub`, `comp`, `bsum`, `bprod`).  The back-translation
is sort-uniform: at sort `.nat`, the ER term's value matches
the original; at sort `.bt`, the ER term's value is
`BTL.encode` of the original tree.  For `foldBTNat` and
`boundedNatRec`, the back-translation uses ER's
`foldBTLOnCode` and `boundedRec` combinators with
on-the-nose interpretation matching guaranteed by the Layer 0
soundness theorems in `Utilities/NatERStyleSoundness.lean`.
The structural predicate `NatBTMor1Bounded.isWellFormed`
restricts the back-translation's domain by excluding
`foldBTBT` (whose `stepNode` carries internal BT context that
cannot be reflected to ER without enriching the
representation) and requiring composition sites to have inner
BT-arity 0.

The two-stage architecture is documented in
`docs/superpowers/specs/2026-04-18-option-e-bounded-natbt-design.md`.
-/

namespace GebLean

/-- Forward translation from ER to bounded NatBT.  Each ER
constructor maps to its NatBT analog at BT-arity 0. -/
def ERMor1.toNatBT : {n : ℕ} → ERMor1 n →
    NatBTMor1Bounded (n, 0) .nat
  | _, ERMor1.zero => NatBTMor1Bounded.zero
  | _, ERMor1.succ =>
      NatBTMor1Bounded.succ (NatBTMor1Bounded.natProj 0)
  | _, ERMor1.proj i => NatBTMor1Bounded.natProj i
  | _, ERMor1.sub =>
      NatBTMor1Bounded.sub
        (NatBTMor1Bounded.natProj 0)
        (NatBTMor1Bounded.natProj 1)
  | _, ERMor1.comp f g =>
      NatBTMor1Bounded.compNat
        (ERMor1.toNatBT f)
        (fun i => ERMor1.toNatBT (g i))
        Fin.elim0
  | _, @ERMor1.bsum k f =>
      NatBTMor1Bounded.bsum (nm := (k, 0)) (ERMor1.toNatBT f)
  | _, @ERMor1.bprod k f =>
      NatBTMor1Bounded.bprod (nm := (k, 0)) (ERMor1.toNatBT f)

/-- The forward translation `ERMor1.toNatBT` preserves the
standard interpretation: applying the bounded NatBT interp to
the translated term with an empty BT context yields the same
result as ER's interp. -/
theorem ERMor1.toNatBT_interp : {n : ℕ} → (t : ERMor1 n) →
    (ctx : Fin n → ℕ) →
    (t.toNatBT).interp ctx Fin.elim0 = t.interp ctx := by
  intro n t ctx
  induction t with
  | zero => rfl
  | succ => rfl
  | proj i => rfl
  | sub => rfl
  | @comp k n' f g ih_f ih_g =>
      change (NatBTMor1Bounded.compNat (ERMor1.toNatBT f)
            (fun i => ERMor1.toNatBT (g i))
            (Fin.elim0 (α := NatBTMor1Bounded (n', 0)
              .bt))).interp ctx Fin.elim0 =
          (ERMor1.comp f g).interp ctx
      rw [NatBTMor1Bounded.interp_compNat,
          ERMor1.interp_comp]
      have hbt :
          (fun i : Fin 0 =>
            ((Fin.elim0 (α := NatBTMor1Bounded (n', 0)
              .bt) i)).interp ctx Fin.elim0) =
            Fin.elim0 := funext (fun i => i.elim0)
      rw [hbt, ih_f]
      congr 1
      funext i
      exact ih_g i _
  | bsum f ih =>
      simp only [ERMor1.toNatBT, NatBTMor1Bounded.interp_bsum,
                 ERMor1.interp_bsum]
      apply congrArg
      funext i
      exact ih _
  | bprod f ih =>
      simp only [ERMor1.toNatBT, NatBTMor1Bounded.interp_bprod,
                 ERMor1.interp_bprod]
      apply congrArg
      funext i
      exact ih _

/-- Tuple-level forward translation: an `m`-tuple of `n`-ary
ER terms maps to a `NatBTMorNBounded (n, 0) (m, 0)` whose
ℕ-components are the per-term translations and whose
BT-components are empty. -/
def ERMorN.toNatBT {n m : ℕ} (f : ERMorN n m) :
    NatBTMorNBounded (n, 0) (m, 0) where
  natComps := fun i => (f i).toNatBT
  btComps := Fin.elim0

/-- Tuple-level interp agreement.  The translated tuple's
interp on `(ctx, Fin.elim0)` matches ER's interp on `ctx` in
the ℕ component, with the empty BT component unchanged. -/
theorem ERMorN.toNatBT_interp {n m : ℕ} (f : ERMorN n m)
    (ctx : Fin n → ℕ) :
    (f.toNatBT).interp ctx Fin.elim0 =
      (f.interp ctx, Fin.elim0) := by
  apply Prod.ext
  · funext i
    exact ERMor1.toNatBT_interp (f i) ctx
  · funext i
    exact i.elim0

open CategoryTheory

/-- Map on morphism classes: lift `ERMorN.toNatBT` through
the ER quotient.  Defined separately to keep the categorical
typeclass resolution at the morphism level explicit. -/
def erToNatBTBoundedMap {n m : ℕ}
    (f : ERMorNQuo n m) :
    NatBTMorNBoundedQuo (n, 0) (m, 0) :=
  Quotient.liftOn f
    (fun (g : ERMorN n m) =>
      Quotient.mk (natBTMorNBoundedSetoid (n, 0) (m, 0))
        g.toNatBT)
    (fun a b hab => by
      apply Quotient.sound
      intro ctxN ctxB
      have hctxB : ctxB = Fin.elim0 :=
        funext (fun i => i.elim0)
      subst hctxB
      rw [ERMorN.toNatBT_interp, ERMorN.toNatBT_interp]
      rw [hab ctxN])

theorem erToNatBTBoundedMap_id (n : ℕ) :
    erToNatBTBoundedMap (ERMorNQuo.id n) =
      NatBTMorNBoundedQuo.id (n, 0) := by
  apply Quotient.sound
  intro ctxN ctxB
  have hctxB : ctxB = Fin.elim0 :=
    funext (fun i => i.elim0)
  subst hctxB
  rw [ERMorN.toNatBT_interp,
      NatBTMorNBounded.interp_id]
  apply Prod.ext
  · rfl
  · funext i; exact i.elim0

theorem erToNatBTBoundedMap_comp {n m k : ℕ}
    (f : ERMorNQuo n m) (g : ERMorNQuo m k) :
    erToNatBTBoundedMap (ERMorNQuo.comp f g) =
      NatBTMorNBoundedQuo.comp
        (erToNatBTBoundedMap f)
        (erToNatBTBoundedMap g) := by
  refine Quotient.inductionOn₂ f g ?_
  intro a b
  apply Quotient.sound
  intro ctxN ctxB
  have hctxB : ctxB = Fin.elim0 :=
    funext (fun i => i.elim0)
  subst hctxB
  rw [ERMorN.toNatBT_interp,
      NatBTMorNBounded.interp_comp,
      ERMorN.toNatBT_interp,
      ERMorN.toNatBT_interp]
  apply Prod.ext
  · rfl
  · funext i; exact i.elim0

/-- Wrapper structure for `LawvereERCat` providing an
unambiguous `Category` instance.  Because `LawvereERCat` and
`LawvereBTQuotCat` are both `@[reducible] def := ℕ` and both
imported transitively, plain `LawvereERCat ⥤ ...` cannot
unambiguously resolve `Hom = ERMorNQuo`.  This wrapper carries
exactly the `LawvereERCat` category structure and serves as
the source object of the forward functor. -/
structure LawvereERWrap where
  /-- Underlying arity of the ER object. -/
  val : ℕ

/-- The category structure on `LawvereERWrap` is exactly that
of `LawvereERCat`: `Hom n m := ERMorNQuo n.val m.val`. -/
instance : CategoryStruct LawvereERWrap where
  Hom n m := ERMorNQuo n.val m.val
  id n := ERMorNQuo.id n.val
  comp f g := ERMorNQuo.comp f g

instance : Category LawvereERWrap where
  id_comp f := ERMorNQuo.id_comp f
  comp_id f := ERMorNQuo.comp_id f
  assoc f g h := ERMorNQuo.comp_assoc f g h

/-- Forward functor `LawvereERWrap ⥤ LawvereNatBTBoundedCat`.
On objects: `⟨n⟩ ↦ (n, 0)`.  On morphism classes: lift the
componentwise translation `ERMorN.toNatBT` through the
quotient. -/
def erToNatBTBoundedFunctor :
    LawvereERWrap ⥤ LawvereNatBTBoundedCat where
  obj n := (n.val, 0)
  map {n m} (f : ERMorNQuo n.val m.val) :=
    erToNatBTBoundedMap f
  map_id n := erToNatBTBoundedMap_id n.val
  map_comp {n m k}
      (f : ERMorNQuo n.val m.val)
      (g : ERMorNQuo m.val k.val) :=
    erToNatBTBoundedMap_comp f g

/-- Structural well-formedness predicate for the
back-translation.  Excludes `foldBTBT` (whose `stepNode`
sub-term has BT-arity > 0 in a way that defeats sort-uniform
back-translation) and requires every composition site to have
inner BT-arity 0.  All other constructors propagate
structurally. -/
def NatBTMor1Bounded.isWellFormed : {nm : ℕ × ℕ} →
    {σ : NatBTSort} → NatBTMor1Bounded nm σ → Prop
  | _, _, NatBTMor1Bounded.zero => True
  | _, _, NatBTMor1Bounded.succ x => x.isWellFormed
  | _, _, NatBTMor1Bounded.natProj _ => True
  | _, _, NatBTMor1Bounded.sub a b =>
      a.isWellFormed ∧ b.isWellFormed
  | _, _, NatBTMor1Bounded.compNat (nm' := nm') f gNat _ =>
      nm'.2 = 0 ∧ f.isWellFormed ∧
        ∀ i, (gNat i).isWellFormed
  | _, _, NatBTMor1Bounded.bsum f => f.isWellFormed
  | _, _, NatBTMor1Bounded.bprod f => f.isWellFormed
  | _, _, NatBTMor1Bounded.leafBT label => label.isWellFormed
  | _, _, NatBTMor1Bounded.nodeBT l r =>
      l.isWellFormed ∧ r.isWellFormed
  | _, _, NatBTMor1Bounded.btProj _ => True
  | _, _, NatBTMor1Bounded.compBT (nm' := nm') f gNat _ =>
      nm'.2 = 0 ∧ f.isWellFormed ∧
        ∀ i, (gNat i).isWellFormed
  | _, _, NatBTMor1Bounded.foldBTNat
      baseLeaf stepNode tree bound =>
      baseLeaf.isWellFormed ∧ stepNode.isWellFormed ∧
        tree.isWellFormed ∧ bound.isWellFormed
  | _, _, NatBTMor1Bounded.foldBTBT _ _ _ _ => False
  | _, _, NatBTMor1Bounded.boundedNatRec
      base step n bound =>
      base.isWellFormed ∧ step.isWellFormed ∧
        n.isWellFormed ∧ bound.isWellFormed
  | _, _, NatBTMor1Bounded.encodeBT t => t.isWellFormed
  | _, _, NatBTMor1Bounded.decodeBT k => k.isWellFormed

/-- Sort-uniform back-translation from bounded NatBT to ER.
At sort `.nat`, produces an ER term whose interpretation
matches the original.  At sort `.bt`, produces an ER term
whose interpretation equals `BTL.encode` of the original.
For `foldBTNat` and `boundedNatRec`, uses ER's
`foldBTLOnCode` / `boundedRec` combinators with the tree /
counter supplied via composition.  Off-diagonal cases
(`btProj`, `foldBTBT`, comp sites with inner BT-arity > 0)
map to placeholder terms; correctness is conditional on
`isWellFormed` and BT-arity 0. -/
def NatBTMor1Bounded.toERUniform : {nm : ℕ × ℕ} →
    {σ : NatBTSort} → NatBTMor1Bounded nm σ → ERMor1 nm.1
  | _, _, NatBTMor1Bounded.zero => ERMor1.zeroN _
  | _, _, NatBTMor1Bounded.succ x =>
      ERMor1.comp ERMor1.succ
        (fun _ : Fin 1 => x.toERUniform)
  | _, _, NatBTMor1Bounded.natProj i => ERMor1.proj i
  | _, _, NatBTMor1Bounded.sub a b =>
      ERMor1.comp ERMor1.sub (fun i => match i with
        | ⟨0, _⟩ => a.toERUniform
        | ⟨1, _⟩ => b.toERUniform)
  | _, _, NatBTMor1Bounded.compNat (nm' := nm') f gNat _ =>
      if _ : nm'.2 = 0 then
        ERMor1.comp f.toERUniform
          (fun i => (gNat i).toERUniform)
      else
        ERMor1.zeroN _
  | _, _, NatBTMor1Bounded.bsum f => ERMor1.bsum f.toERUniform
  | _, _, NatBTMor1Bounded.bprod f =>
      ERMor1.bprod f.toERUniform
  | _, _, NatBTMor1Bounded.leafBT label =>
      ERMor1.comp ERMor1.btlEncodeLeaf
        (fun _ : Fin 1 => label.toERUniform)
  | _, _, NatBTMor1Bounded.nodeBT l r =>
      ERMor1.comp ERMor1.btlEncodeNode
        (fun i => match i with
          | ⟨0, _⟩ => l.toERUniform
          | ⟨1, _⟩ => r.toERUniform)
  | _, _, NatBTMor1Bounded.btProj _ => ERMor1.zeroN _
  | _, _, NatBTMor1Bounded.compBT (nm' := nm') f gNat _ =>
      if _ : nm'.2 = 0 then
        ERMor1.comp f.toERUniform
          (fun i => (gNat i).toERUniform)
      else
        ERMor1.zeroN _
  | _, _, NatBTMor1Bounded.foldBTNat
      baseLeaf stepNode tree bound =>
      ERMor1.comp
        (ERMor1.foldBTLOnCode baseLeaf.toERUniform
          stepNode.toERUniform bound.toERUniform)
        (fun i => Fin.cases tree.toERUniform
          (fun k => ERMor1.proj k) i)
  | _, _, NatBTMor1Bounded.foldBTBT _ _ _ _ =>
      ERMor1.zeroN _
  | _, _, NatBTMor1Bounded.boundedNatRec
      base step n bound =>
      ERMor1.comp
        (ERMor1.boundedRec base.toERUniform
          step.toERUniform bound.toERUniform)
        (fun i => Fin.cases n.toERUniform
          (fun k => ERMor1.proj k) i)
  | _, _, NatBTMor1Bounded.encodeBT t => t.toERUniform
  | _, _, NatBTMor1Bounded.decodeBT k => k.toERUniform

/-- Back-translation specialized to `.nat` outputs at
BT-arity 0. -/
def NatBTMor1Bounded.toER {n : ℕ}
    (t : NatBTMor1Bounded (n, 0) .nat) : ERMor1 n :=
  t.toERUniform

/-- Back-translation specialized to `.bt` outputs at
BT-arity 0: the ER value is `BTL.encode` of the interpreted
tree. -/
def NatBTMor1Bounded.toER_bt {n : ℕ}
    (t : NatBTMor1Bounded (n, 0) .bt) : ERMor1 n :=
  t.toERUniform

/-- Encode a value of either carrier sort to ℕ: identity on
`.nat`, `BTL.encode` on `.bt`. -/
def NatBTSort.encodeValueBounded :
    (σ : NatBTSort) → σ.carrier → ℕ
  | .nat, v => v
  | .bt, v => v.encode

/-- Sort-uniform correctness of the back-translation.  For a
well-formed term at ambient BT-arity 0, the ER interpretation
of `toERUniform` equals the sort-encoded original
interpretation. -/
theorem NatBTMor1Bounded.toERUniform_interp_aux :
    {nm : ℕ × ℕ} → {σ : NatBTSort} →
    (t : NatBTMor1Bounded nm σ) → t.isWellFormed →
    (h2 : nm.2 = 0) → (ctxN : Fin nm.1 → ℕ) →
    t.toERUniform.interp ctxN =
      σ.encodeValueBounded
        (t.interp ctxN
          (h2 ▸ (Fin.elim0 : Fin 0 → BTL))) := by
  intro nm σ t
  induction t with
  | zero =>
      intro _ _ _
      simp [NatBTMor1Bounded.toERUniform,
        NatBTMor1Bounded.interp,
        NatBTSort.encodeValueBounded]
  | succ x ih =>
      intro h h2 ctxN
      simp only [NatBTMor1Bounded.toERUniform,
        ERMor1.interp_comp, ERMor1.interp_succ,
        NatBTMor1Bounded.interp,
        NatBTSort.encodeValueBounded]
      have := ih h h2 ctxN
      simp only [NatBTSort.encodeValueBounded] at this
      rw [this]
  | natProj i =>
      intro _ _ _
      simp [NatBTMor1Bounded.toERUniform,
        NatBTMor1Bounded.interp,
        NatBTSort.encodeValueBounded]
  | sub a b iha ihb =>
      intro h h2 ctxN
      obtain ⟨ha, hb⟩ := h
      have ea := iha ha h2 ctxN
      have eb := ihb hb h2 ctxN
      simp only [NatBTSort.encodeValueBounded] at ea eb
      simp only [NatBTMor1Bounded.toERUniform,
        ERMor1.interp_comp, ERMor1.interp_sub,
        NatBTMor1Bounded.interp,
        NatBTSort.encodeValueBounded]
      change (a.toERUniform.interp ctxN) -
        (b.toERUniform.interp ctxN) = _
      rw [ea, eb]
      rfl
  | @compNat nm nm' f gNat gBT ih_f ih_gNat _ =>
      intro h h2 ctxN
      obtain ⟨hm', hff, hgs⟩ := h
      have ih_f' :
          f.toERUniform.interp
              (fun i => (gNat i).toERUniform.interp ctxN) =
            (NatBTSort.nat).encodeValueBounded
              (f.interp
                (fun i =>
                  (gNat i).toERUniform.interp ctxN)
                (hm' ▸ (Fin.elim0 : Fin 0 → BTL))) :=
        ih_f hff hm'
            (fun i => (gNat i).toERUniform.interp ctxN)
      simp only [NatBTSort.encodeValueBounded] at ih_f'
      have hgeq :
          (fun i => (gNat i).toERUniform.interp ctxN)
          = (fun i => (gNat i).interp ctxN
              (h2 ▸ (Fin.elim0 : Fin 0 → BTL))) := by
        funext i
        have := ih_gNat i (hgs i) h2 ctxN
        simp only [NatBTSort.encodeValueBounded] at this
        exact this
      have hBTeq :
          (fun i : Fin nm'.2 => (gBT i).interp ctxN
              (h2 ▸ (Fin.elim0 : Fin 0 → BTL))) =
            (hm' ▸ (Fin.elim0 : Fin 0 → BTL)) := by
        funext i
        have : i.val < 0 := hm' ▸ i.isLt
        exact absurd this (Nat.not_lt_zero _)
      simp only [NatBTMor1Bounded.toERUniform, hm',
        dif_pos, ERMor1.interp_comp,
        NatBTMor1Bounded.interp,
        NatBTSort.encodeValueBounded]
      rw [ih_f', hgeq, hBTeq]
  | bsum f ih =>
      intro h h2 ctxN
      simp only [NatBTMor1Bounded.toERUniform,
        ERMor1.interp_bsum, NatBTMor1Bounded.interp,
        NatBTSort.encodeValueBounded]
      apply congrArg
      funext i
      have := ih h h2 (Fin.cons i (Fin.tail ctxN))
      simp only [NatBTSort.encodeValueBounded] at this
      exact this
  | bprod f ih =>
      intro h h2 ctxN
      simp only [NatBTMor1Bounded.toERUniform,
        ERMor1.interp_bprod, NatBTMor1Bounded.interp,
        NatBTSort.encodeValueBounded]
      apply congrArg
      funext i
      have := ih h h2 (Fin.cons i (Fin.tail ctxN))
      simp only [NatBTSort.encodeValueBounded] at this
      exact this
  | leafBT label ih =>
      intro h h2 ctxN
      have e := ih h h2 ctxN
      simp only [NatBTSort.encodeValueBounded] at e
      simp only [NatBTMor1Bounded.toERUniform,
        NatBTMor1Bounded.interp,
        NatBTSort.encodeValueBounded, ERMor1.interp_comp]
      have hleaf :
          ERMor1.btlEncodeLeaf.interp
              ![label.toERUniform.interp ctxN] =
            BTL.encode
              (BTL.leaf (label.toERUniform.interp ctxN)) :=
        ERMor1.interp_btlEncodeLeaf _
      change ERMor1.btlEncodeLeaf.interp
          (fun _ : Fin 1 =>
            label.toERUniform.interp ctxN) = _
      have hfunext :
          (fun _ : Fin 1 =>
              label.toERUniform.interp ctxN) =
            ![label.toERUniform.interp ctxN] := by
        funext i
        match i with
        | ⟨0, _⟩ => rfl
      rw [hfunext, hleaf, e]
  | nodeBT l r ihl ihr =>
      intro h h2 ctxN
      obtain ⟨hl, hr⟩ := h
      have el := ihl hl h2 ctxN
      have er := ihr hr h2 ctxN
      simp only [NatBTSort.encodeValueBounded] at el er
      simp only [NatBTMor1Bounded.toERUniform,
        NatBTMor1Bounded.interp,
        NatBTSort.encodeValueBounded, ERMor1.interp_comp]
      have hfunext :
          (fun i : Fin 2 =>
              (match i with
                | ⟨0, _⟩ => l.toERUniform
                | ⟨1, _⟩ => r.toERUniform).interp ctxN) =
            ![l.toERUniform.interp ctxN,
              r.toERUniform.interp ctxN] := by
        funext i
        match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
      rw [hfunext]
      rw [ERMor1.interp_btlEncodeNode]
      rw [el, er]
      rfl
  | btProj i =>
      intro _ h2 _
      exact (h2 ▸ i).elim0
  | @compBT nm nm' f gNat gBT ih_f ih_gNat _ =>
      intro h h2 ctxN
      obtain ⟨hm', hff, hgs⟩ := h
      have ih_f' :
          f.toERUniform.interp
              (fun i => (gNat i).toERUniform.interp ctxN) =
            (NatBTSort.bt).encodeValueBounded
              (f.interp
                (fun i =>
                  (gNat i).toERUniform.interp ctxN)
                (hm' ▸ (Fin.elim0 : Fin 0 → BTL))) :=
        ih_f hff hm'
            (fun i => (gNat i).toERUniform.interp ctxN)
      simp only [NatBTSort.encodeValueBounded] at ih_f'
      have hgeq :
          (fun i => (gNat i).toERUniform.interp ctxN)
          = (fun i => (gNat i).interp ctxN
              (h2 ▸ (Fin.elim0 : Fin 0 → BTL))) := by
        funext i
        have := ih_gNat i (hgs i) h2 ctxN
        simp only [NatBTSort.encodeValueBounded] at this
        exact this
      have hBTeq :
          (fun i : Fin nm'.2 => (gBT i).interp ctxN
              (h2 ▸ (Fin.elim0 : Fin 0 → BTL))) =
            (hm' ▸ (Fin.elim0 : Fin 0 → BTL)) := by
        funext i
        have : i.val < 0 := hm' ▸ i.isLt
        exact absurd this (Nat.not_lt_zero _)
      simp only [NatBTMor1Bounded.toERUniform, hm',
        dif_pos, ERMor1.interp_comp,
        NatBTMor1Bounded.interp,
        NatBTSort.encodeValueBounded]
      rw [ih_f', hgeq, hBTeq]
  | foldBTNat baseLeaf stepNode tree bound
      ih_base ih_step ih_tree ih_bound =>
      intro h h2 ctxN
      obtain ⟨hbase, hstep, htree, hbound⟩ := h
      have e_tree := ih_tree htree h2 ctxN
      simp only [NatBTSort.encodeValueBounded] at e_tree
      simp only [NatBTMor1Bounded.toERUniform,
        ERMor1.interp_comp,
        NatBTMor1Bounded.interp_foldBTNat,
        NatBTSort.encodeValueBounded]
      set ctx' : Fin (_ + 1) → ℕ :=
        Fin.cons (tree.toERUniform.interp ctxN) ctxN
        with hctx'_def
      have hctx'_eval :
          (fun i =>
            (Fin.cases tree.toERUniform
              (fun k => ERMor1.proj k) i :
              ERMor1 _).interp ctxN) = ctx' := by
        funext i
        induction i using Fin.cases with
        | zero =>
            change tree.toERUniform.interp ctxN = ctx' 0
            rw [hctx'_def]
            rfl
        | succ k =>
            change (ERMor1.proj k).interp ctxN = ctx' _
            rw [hctx'_def]
            rfl
      rw [hctx'_eval]
      rw [ERMor1.interp_foldBTLOnCode_eq_natFoldBTLOnCodeERStyle
            baseLeaf.toERUniform stepNode.toERUniform
            bound.toERUniform ctx']
      have htail : Fin.tail ctx' = ctxN := by
        funext i
        rw [hctx'_def]
        rfl
      have hfst : ctx' 0 =
          tree.toERUniform.interp ctxN := by
        rw [hctx'_def]; rfl
      rw [htail, hfst, e_tree]
      congr 1
      · funext lbl
        have := ih_base hbase h2 (Fin.cons lbl ctxN)
        simp only [NatBTSort.encodeValueBounded] at this
        exact this
      · funext a b
        have := ih_step hstep h2
          (Fin.cons a (Fin.cons b ctxN))
        simp only [NatBTSort.encodeValueBounded] at this
        exact this
      · funext j
        have := ih_bound hbound h2 (Fin.cons j ctxN)
        simp only [NatBTSort.encodeValueBounded] at this
        exact this
  | foldBTBT _ _ _ _ _ _ _ _ =>
      intro h _ _
      exact absurd h (by
        simp [NatBTMor1Bounded.isWellFormed])
  | boundedNatRec base step n bound
      ih_base ih_step ih_n ih_bound =>
      intro h h2 ctxN
      obtain ⟨hbase, hstep, hn, hbound⟩ := h
      have e_n := ih_n hn h2 ctxN
      simp only [NatBTSort.encodeValueBounded] at e_n
      simp only [NatBTMor1Bounded.toERUniform,
        ERMor1.interp_comp,
        NatBTMor1Bounded.interp_boundedNatRec,
        NatBTSort.encodeValueBounded]
      set ctx' : Fin (_ + 1) → ℕ :=
        Fin.cons (n.toERUniform.interp ctxN) ctxN
        with hctx'_def
      have hctx'_eval :
          (fun i =>
            (Fin.cases n.toERUniform
              (fun k => ERMor1.proj k) i :
              ERMor1 _).interp ctxN) = ctx' := by
        funext i
        induction i using Fin.cases with
        | zero =>
            change n.toERUniform.interp ctxN = ctx' 0
            rw [hctx'_def]
            rfl
        | succ k =>
            change (ERMor1.proj k).interp ctxN = ctx' _
            rw [hctx'_def]
            rfl
      rw [hctx'_eval]
      rw [ERMor1.interp_boundedRec_eq_natBoundedRecERStyle
            base.toERUniform step.toERUniform
            bound.toERUniform ctx']
      have htail : Fin.tail ctx' = ctxN := by
        funext i
        rw [hctx'_def]
        rfl
      have hfst : ctx' 0 =
          n.toERUniform.interp ctxN := by
        rw [hctx'_def]; rfl
      rw [htail, hfst, e_n]
      congr 1
      · have := ih_base hbase h2 ctxN
        simp only [NatBTSort.encodeValueBounded] at this
        exact this
      · funext j prev
        have := ih_step hstep h2
          (Fin.cons j (Fin.cons prev ctxN))
        simp only [NatBTSort.encodeValueBounded] at this
        exact this
      · funext j
        have := ih_bound hbound h2 (Fin.cons j ctxN)
        simp only [NatBTSort.encodeValueBounded] at this
        exact this
  | encodeBT t ih =>
      intro h h2 ctxN
      have e := ih h h2 ctxN
      simp only [NatBTSort.encodeValueBounded] at e
      simp only [NatBTMor1Bounded.toERUniform,
        NatBTMor1Bounded.interp,
        NatBTSort.encodeValueBounded]
      exact e
  | decodeBT k ih =>
      intro h h2 ctxN
      have e := ih h h2 ctxN
      simp only [NatBTSort.encodeValueBounded] at e
      simp only [NatBTMor1Bounded.toERUniform,
        NatBTMor1Bounded.interp,
        NatBTSort.encodeValueBounded]
      rw [e]
      exact (BTL.encode_decode _).symm

/-- Correctness of `toER` on `.nat` outputs at BT-arity 0. -/
theorem NatBTMor1Bounded.toER_interp {n : ℕ}
    (t : NatBTMor1Bounded (n, 0) .nat) (h : t.isWellFormed)
    (ctxN : Fin n → ℕ) :
    t.toER.interp ctxN = t.interp ctxN Fin.elim0 := by
  have :=
    NatBTMor1Bounded.toERUniform_interp_aux t h rfl ctxN
  simpa [NatBTMor1Bounded.toER,
    NatBTSort.encodeValueBounded] using this

/-- Correctness of `toER_bt` on `.bt` outputs at BT-arity 0:
the value equals `BTL.encode` of the interpreted tree. -/
theorem NatBTMor1Bounded.toER_bt_interp {n : ℕ}
    (t : NatBTMor1Bounded (n, 0) .bt) (h : t.isWellFormed)
    (ctxN : Fin n → ℕ) :
    t.toER_bt.interp ctxN =
      BTL.encode (t.interp ctxN Fin.elim0) := by
  have :=
    NatBTMor1Bounded.toERUniform_interp_aux t h rfl ctxN
  simpa [NatBTMor1Bounded.toER_bt,
    NatBTSort.encodeValueBounded] using this

/-- Tuple-level well-formedness: every component is
`isWellFormed`.  At BT-arity 0 there are no BT components to
check. -/
def NatBTMorNBounded.isWellFormed {n m : ℕ}
    (f : NatBTMorNBounded (n, 0) (m, 0)) : Prop :=
  ∀ i, (f.natComps i).isWellFormed

/-- Tuple-level back-translation at BT-arity 0.  Lifts
`toER` componentwise; the output BT arity is 0 so there are
no BT components to emit. -/
def NatBTMorNBounded.toER {n m : ℕ}
    (f : NatBTMorNBounded (n, 0) (m, 0)) : ERMorN n m :=
  fun i => (f.natComps i).toER

/-- Correctness of the tuple-level back-translation. -/
theorem NatBTMorNBounded.toER_interp {n m : ℕ}
    (f : NatBTMorNBounded (n, 0) (m, 0))
    (h : f.isWellFormed) (ctxN : Fin n → ℕ) :
    f.toER.interp ctxN = (f.interp ctxN Fin.elim0).1 := by
  funext i
  exact (f.natComps i).toER_interp (h i) ctxN

end GebLean

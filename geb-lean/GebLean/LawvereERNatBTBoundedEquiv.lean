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
maps each NatBT constructor to an ER term — for the recursive
constructors (`foldBTNat`, `foldBTBT`, `boundedNatRec`), this
uses ER's `foldBTLOnCode` and `boundedRec` combinators, with
agreement guaranteed by the Layer 0 soundness theorems in
`Utilities/NatERStyleSoundness.lean`.

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

end GebLean

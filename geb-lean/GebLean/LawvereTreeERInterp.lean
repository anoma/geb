import GebLean.LawvereTreeERQuot
import GebLean.LawvereBTInterp
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Interpretation and Inclusion Functors for
# LawvereTreeERCat

Defines two functors out of `LawvereTreeERCat`:

1. `treeErInterpFunctor`: a faithful functor into
   `Type` sending arity `n` to `Fin n → BT` and
   each morphism class to its interpretation.

2. `treeErInclusion`: a faithful functor into
   `LawvereBTQuotObj` (a non-reducible copy of
   `LawvereBTQuotCat` that avoids typeclass
   instance confusion between multiple
   `@[reducible]` abbreviations of `ℕ`),
   sending each tree-native ER morphism to its
   underlying `BTMor1` translation via
   `TreeMor1.toBTMor1`.
-/

namespace GebLean

open CategoryTheory

/-- Lift `TreeERMorN.interp` to the quotient.
Well-defined because the setoid relation is
extensional equality of interpretations. -/
def TreeERMorNQuo.interp {n m : ℕ}
    (f : TreeERMorNQuo n m) :
    (Fin n → BT.{0}) → (Fin m → BT.{0}) :=
  Quotient.lift
    (s := treeErMorNSetoid n m)
    TreeERMorN.interp
    (fun _ _ h => funext h)
    f

/-- `TreeERMorNQuo.interp` on a concrete
representative reduces to
`TreeERMorN.interp`. -/
@[simp] theorem TreeERMorNQuo.interp_mk
    {n m : ℕ} (f : TreeERMorN n m) :
    TreeERMorNQuo.interp
      (Quotient.mk (treeErMorNSetoid n m) f) =
      f.interp :=
  rfl

/-- Interpretation of the quotient identity. -/
@[simp] theorem TreeERMorNQuo.interp_id
    (n : ℕ) (ctx : Fin n → BT.{0}) :
    (TreeERMorNQuo.id n).interp ctx = ctx := by
  unfold TreeERMorNQuo.id
  simp [TreeERMorNQuo.interp_mk,
    TreeERMorN.interp_id]

/-- Interpretation of quotient composition. -/
@[simp] theorem TreeERMorNQuo.interp_comp
    {n m k : ℕ} (f : TreeERMorNQuo n m)
    (g : TreeERMorNQuo m k)
    (ctx : Fin n → BT.{0}) :
    (TreeERMorNQuo.comp f g).interp ctx =
      g.interp (f.interp ctx) := by
  revert f g
  apply Quotient.ind₂
  intro f_raw g_raw
  change (TreeERMorN.comp f_raw g_raw).interp
    ctx = _
  simp only [TreeERMorN.interp_comp,
    TreeERMorNQuo.interp_mk]

/-! ## Interpretation functor

`LawvereTreeERCat`, `LawvereBTQuotCat`, and
`LawvereBTCat` are all `@[reducible]` to `ℕ`,
each with its own `Category` instance.  We
raise the priority of the `LawvereTreeERCat`
instances so that `n ⟶ m` for
`n m : LawvereTreeERCat` resolves to
`TreeERMorNQuo n m`. -/

attribute [local instance 2000]
  instCategoryStructLawvereTreeERCat
attribute [local instance 2000]
  instCategoryLawvereTreeERCat

/-- The interpretation functor from
`LawvereTreeERCat` into `Type`.  Sends arity `n`
to `Fin n → BT` and each morphism class to its
interpretation. -/
def treeErInterpFunctor :
    LawvereTreeERCat ⥤ Type where
  obj n := Fin n → BT.{0}
  map f := f.interp
  map_id n := by
    funext ctx
    exact TreeERMorNQuo.interp_id n ctx
  map_comp f g := by
    funext ctx
    exact TreeERMorNQuo.interp_comp f g ctx

/-- The interpretation functor is faithful:
distinct morphism classes produce distinct
functions.  This is immediate from the
extensional quotient. -/
instance : treeErInterpFunctor.Faithful where
  map_injective {n m} {f g} h := by
    revert f g
    apply Quotient.ind₂
    intro f_raw g_raw heq
    exact Quotient.sound
      (s := treeErMorNSetoid n m)
      (fun ctx => congrFun heq ctx)

/-! ## Inclusion into LawvereBTQuotObj

`LawvereBTQuotObj` is a non-reducible copy of
`LawvereBTQuotCat` (whose objects are `ℕ` and
whose morphisms are `BTMorNQuo`).  It exists
because `LawvereTreeERCat` and
`LawvereBTQuotCat` are both `@[reducible]` to
`ℕ`, causing Lean's typeclass resolution to
conflate their `Category` instances.  Using a
`def` (not `@[reducible]`) wrapper disambiguates
them. -/

/-- Non-reducible copy of `ℕ` carrying the
`LawvereBTQuotCat` category structure. -/
def LawvereBTQuotObj := ℕ

instance : CategoryStruct LawvereBTQuotObj
    where
  Hom (a b : LawvereBTQuotObj) :=
    BTMorNQuo a b
  id (a : LawvereBTQuotObj) :=
    BTMorNQuo.id a
  comp f g := BTMorNQuo.comp f g

instance : Category LawvereBTQuotObj where
  id_comp := BTMorNQuo.id_comp
  comp_id := BTMorNQuo.comp_id
  assoc := BTMorNQuo.comp_assoc

/-- Map each component of a `TreeERMorN` tuple to
its `BTMor1` translation via
`TreeMor1.toBTMor1`. -/
def TreeERMorN.toBTMorN {n m : ℕ}
    (f : TreeERMorN n m) : BTMorN n m :=
  fun i => (f i).val.toBTMor1

/-- If two `TreeERMorN` tuples have the same
interpretation on all contexts, then their
`BTMorN` translations also have the same
`interpU` on all contexts.  This holds because
`TreeERMor1.interp` factors through
`toBTMor1.interpU`. -/
theorem TreeERMorN.toBTMorN_sound {n m : ℕ}
    (f g : TreeERMorN n m)
    (h : ∀ ctx : Fin n → BT.{0},
      f.interp ctx = g.interp ctx) :
    ∀ ctx : Fin n → BT.{0},
      f.toBTMorN.interpU ctx =
        g.toBTMorN.interpU ctx := by
  intro ctx
  funext i
  exact congrFun (h ctx) i

/-- Lift `TreeERMorN.toBTMorN` to the quotient,
producing a `BTMorNQuo` from a
`TreeERMorNQuo`. -/
def TreeERMorNQuo.toBTMorNQuo {n m : ℕ}
    (f : TreeERMorNQuo n m) : BTMorNQuo n m :=
  Quotient.lift
    (s := treeErMorNSetoid n m)
    (fun f' =>
      Quotient.mk (btMorNSetoid n m)
        f'.toBTMorN)
    (fun _ _ h =>
      Quotient.sound
        (s := btMorNSetoid n m)
        (fun j => interpU_complete _ _
          (fun ctx =>
            congrFun
              (TreeERMorN.toBTMorN_sound
                _ _ h ctx) j)))
    f

/-- `toBTMorNQuo` on the identity: the BT
translation of the TreeER identity equals the
BT identity up to `btMorRel`. -/
private theorem toBTMorNQuo_id (n : ℕ) :
    TreeERMorNQuo.toBTMorNQuo
      (TreeERMorNQuo.id n) =
      BTMorNQuo.id n := by
  apply Quotient.sound (s := btMorNSetoid n n)
  intro j
  apply interpU_complete
  intro ctx
  simp only [TreeERMorN.toBTMorN,
    BTMorN.id, BTMor1.interpU_proj,
    TreeERMorN.id, TreeERMor1.proj,
    TreeERMor1_0.proj,
    TreeERMor1_0.toDepth2,
    TreeERMor1_0.toDepth1,
    TreeERMor1_1.toDepth2,
    TreeMor1.toBTMor1,
    BTMor1.interpU_proj]

/-- `toBTMorNQuo` preserves composition. -/
private theorem toBTMorNQuo_comp
    {n m k : ℕ}
    (f : TreeERMorNQuo n m)
    (g : TreeERMorNQuo m k) :
    TreeERMorNQuo.toBTMorNQuo
      (TreeERMorNQuo.comp f g) =
      BTMorNQuo.comp
        (TreeERMorNQuo.toBTMorNQuo f)
        (TreeERMorNQuo.toBTMorNQuo g) := by
  revert f g
  apply Quotient.ind₂
  intro f_raw g_raw
  apply Quotient.sound (s := btMorNSetoid n k)
  intro j
  apply interpU_complete
  intro ctx
  simp only [TreeERMorN.toBTMorN,
    BTMorN.comp, BTMor1.interpU_subst,
    TreeERMorN.comp, TreeERMor1.comp,
    TreeMor1.toBTMor1,
    BTMor1.interpU_subst]

/-- The inclusion functor from
`LawvereTreeERCat` into `LawvereBTQuotObj`,
sending each tree-native ER morphism to its
`BTMor1` translation. -/
def treeErInclusion :
    LawvereTreeERCat ⥤ LawvereBTQuotObj where
  obj n := (n : LawvereBTQuotObj)
  map f := TreeERMorNQuo.toBTMorNQuo f
  map_id n := by
    change TreeERMorNQuo.toBTMorNQuo
      (TreeERMorNQuo.id n) = BTMorNQuo.id n
    exact toBTMorNQuo_id n
  map_comp f g := by
    change TreeERMorNQuo.toBTMorNQuo
      (TreeERMorNQuo.comp f g) =
      BTMorNQuo.comp
        (TreeERMorNQuo.toBTMorNQuo f)
        (TreeERMorNQuo.toBTMorNQuo g)
    exact toBTMorNQuo_comp f g

/-- The inclusion functor is faithful: if the
`BTMor1` translations of two TreeER morphism
classes are equal in `LawvereBTQuotObj`, then
the original TreeER classes are equal. -/
instance : treeErInclusion.Faithful where
  map_injective {n m} {f g} h := by
    revert f g
    apply Quotient.ind₂
    intro f_raw g_raw heq
    apply Quotient.sound
      (s := treeErMorNSetoid n m)
    intro ctx
    funext i
    have hbt :
        f_raw.toBTMorN.interpU ctx =
          g_raw.toBTMorN.interpU ctx := by
      have hmap :
          TreeERMorNQuo.toBTMorNQuo
            (Quotient.mk
              (treeErMorNSetoid n m)
              f_raw) =
            TreeERMorNQuo.toBTMorNQuo
              (Quotient.mk
                (treeErMorNSetoid n m)
                g_raw) := heq
      simp only [
        TreeERMorNQuo.toBTMorNQuo,
        Quotient.lift_mk] at hmap
      have h1 :
          BTMorNQuo.interpU.{0}
            (Quotient.mk (btMorNSetoid n m)
              f_raw.toBTMorN) ctx =
            BTMorNQuo.interpU.{0}
              (Quotient.mk (btMorNSetoid n m)
                g_raw.toBTMorN) ctx := by
        rw [hmap]
      exact h1
    exact congrFun hbt i

end GebLean

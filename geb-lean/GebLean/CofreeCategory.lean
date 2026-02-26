import GebLean.PolyAlg
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Cofree Category of a Polynomial Endofunctor

For a polynomial endofunctor `P : PolyEndo X`, the cofree
category `C_P` is the category corresponding to the cofree
comonoid on `P`.  It is constructed from the comonad
arising from the `Forget ⊣ Cofree` adjunction on
P-coalgebras, transported through the equivalence between
the cofree comonad and polynomial evaluation.

The category of P-coalgebras is equivalent to the
copresheaf topos `Set^{C_P}` (Adamek-Porst 2005/2006,
Spivak 2021).

## Construction

The comonad-first approach:
1. Derive `Comonad (Over X)` from
   `polyForgetCofreeAdjunction P`
   via `Adjunction.toComonad`.
2. Show the comonad's underlying functor is naturally
   isomorphic to `polyEndoFunctor X (polyCofreeMPoly P)`.
3. Transport the comonad structure to a comonoid in the
   monoidal category of polynomial endofunctors.
4. Extract the cofree category from the comonoid.
-/

namespace GebLean

open CategoryTheory

universe u

variable (X : Type u)

/-! ## Phase 1: Comonad from Adjunction -/

/--
The comonad on `Over X` arising from the
`Forget ⊣ Cofree` adjunction on P-coalgebras.
The underlying functor sends `A : Over X` to
`polyCofreeCarrier A P`.
-/
def polyCofreeComonad (P : PolyEndo X) :
    Comonad (Over X) :=
  (polyForgetCofreeAdjunction P).toComonad

/-! ## Phase 2: Natural Isomorphism -/

section NaturalIsomorphism

variable {X : Type u}

/--
Mapping annotations preserves shape at the approximation
level: stripping annotations after mapping gives the same
result as stripping annotations directly.
-/
lemma polyCofreeApproxToShape_map
    (A B : Over X) (P : PolyEndo X)
    (f : A ⟶ B) {n : Nat} {x : X}
    (a : PolyCofixApprox (polyScale A P) n x) :
    polyCofreeApproxToShape B P
      (polyCofreeMapApprox A B P f a) =
    polyCofreeApproxToShape A P a := by
  induction a with
  | «continue» y => rfl
  | intro y idx children ih =>
    obtain ⟨aVal, pIdx⟩ := idx
    dsimp only [polyCofreeMapApprox,
      polyCofreeApproxToShape]
    congr 1
    funext e
    exact ih e

/--
Mapping annotations preserves shape: the shape of a
mapped M-type equals the shape of the original.
-/
theorem polyCofreeToShape_map
    (A B : Over X) (P : PolyEndo X)
    (f : A ⟶ B) {x : X}
    (m : PolyCofreeM A P x) :
    polyCofreeToShape B P
      (polyCofreeMapAt A B P f m) =
    polyCofreeToShape A P m := by
  apply PolyCofix.ext
  intro n
  exact polyCofreeApproxToShape_map A B P f
    (m.approx n)

/--
The result of `polyCofreeFromShapeAndDataApprox`
depends only on the data function, not on its proof
of fiber compatibility.
-/
lemma polyCofreeFromShapeAndDataApprox_proof_irrel
    (A : Over X) (P : PolyEndo X) {x : X}
    (shape : PolyCofreeShape P x)
    (f : (pos : PolyCofreeAnnotPos P shape) →
      A.left)
    (hf1 hf2 : ∀ pos, A.hom (f pos) =
      PolyCofreeAnnotFiber P shape pos)
    (n : Nat) :
    polyCofreeFromShapeAndDataApprox A P
      shape f hf1 n =
    polyCofreeFromShapeAndDataApprox A P
      shape f hf2 n := by
  induction n generalizing x shape f hf1 hf2 with
  | zero => rfl
  | succ n ih =>
    unfold polyCofreeFromShapeAndDataApprox
    congr 1

/--
Mapping by `g` commutes with building from shape and
data at the approximation level: re-annotating with
`g` then converting equals converting with `g.left ∘ f`.
-/
lemma polyCofreeFromShapeAndDataApprox_map
    (A B : Over X) (P : PolyEndo X)
    (g : A ⟶ B) {x : X}
    (shape : PolyCofreeShape P x)
    (f : (pos : PolyCofreeAnnotPos P shape) →
      A.left)
    (hf : ∀ pos, A.hom (f pos) =
      PolyCofreeAnnotFiber P shape pos)
    (n : Nat) :
    polyCofreeMapApprox A B P g
      (polyCofreeFromShapeAndDataApprox A P
        shape f hf n) =
    polyCofreeFromShapeAndDataApprox B P shape
      (g.left ∘ f)
      (fun pos =>
        (overMor_w g (f pos)).trans (hf pos))
      n := by
  induction n generalizing x shape f hf with
  | zero => rfl
  | succ n ih =>
    unfold polyCofreeFromShapeAndDataApprox
      polyCofreeMapApprox
    dsimp only [polyCofreeFromShapeAndDataApprox,
      polyCofreeMapApprox]
    congr 1
    funext e
    rw [ih (shape.children e)
      (polyCofreeChildAnnotFn A P shape f e)
      (polyCofreeChildAnnotFn_fiber
        A P shape f hf e)]
    exact
      polyCofreeFromShapeAndDataApprox_proof_irrel
        B P (shape.children e) _ _ _ _

/--
Mapping by `g` commutes with building from shape and
data at the M-type level.
-/
theorem polyCofreeFromShapeAndData_map
    (A B : Over X) (P : PolyEndo X)
    (g : A ⟶ B) {x : X}
    (shape : PolyCofreeShape P x)
    (f : (pos : PolyCofreeAnnotPos P shape) →
      A.left)
    (hf : ∀ pos, A.hom (f pos) =
      PolyCofreeAnnotFiber P shape pos) :
    polyCofreeMapAt A B P g
      (polyCofreeFromShapeAndData A P
        shape f hf) =
    polyCofreeFromShapeAndData B P shape
      (g.left ∘ f)
      (fun pos =>
        (overMor_w g (f pos)).trans (hf pos)) := by
  apply PolyCofix.ext
  intro n
  exact polyCofreeFromShapeAndDataApprox_map
    A B P g shape f hf n

/--
The result of `polyCofreeFromShapeAndData` depends only
on the data function, not on its proof.
-/
theorem polyCofreeFromShapeAndData_proof_irrel
    (A : Over X) (P : PolyEndo X) {x : X}
    (shape : PolyCofreeShape P x)
    (f : (pos : PolyCofreeAnnotPos P shape) →
      A.left)
    (hf1 hf2 : ∀ pos, A.hom (f pos) =
      PolyCofreeAnnotFiber P shape pos) :
    polyCofreeFromShapeAndData A P
      shape f hf1 =
    polyCofreeFromShapeAndData A P
      shape f hf2 := by
  apply PolyCofix.ext
  intro n
  exact polyCofreeFromShapeAndDataApprox_proof_irrel
    A P shape f hf1 hf2 n

/--
The inverse of `polyCofreeEquiv` is natural in `A`:
mapping by `g` then converting from poly eval form
equals converting from (post-composed) poly eval form.
-/
theorem polyCofreePolyEval_to_M_natural
    (A B : Over X) (P : PolyEndo X)
    (g : A ⟶ B) {x : X}
    (eval : PolyCofreePolyEval A P x) :
    polyCofreeMapAt A B P g
      (polyCofreePolyEval_to_polyCofreeM
        A P eval) =
    polyCofreePolyEval_to_polyCofreeM B P
      (ccrEvalMap g eval) := by
  obtain ⟨shape, mor⟩ := eval
  simp only [polyCofreePolyEval_to_polyCofreeM,
    ccrEvalMap]
  rw [polyCofreeFromShapeAndData_map
    A B P g shape mor.left
    (fun pos => overMor_w mor pos)]
  exact polyCofreeFromShapeAndData_proof_irrel
    B P shape (g.left ∘ mor.left) _ _

end NaturalIsomorphism

end GebLean

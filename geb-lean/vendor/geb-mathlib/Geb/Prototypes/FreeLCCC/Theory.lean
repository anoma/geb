/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Theory

set_option doc.verso true in
/-!
# The theory of a locally cartesian closed category with finite colimits and an NNO

The objects and arrows are the sorts of a partial Horn theory. The finite-limit and
finite-colimit operations reuse the corresponding signature and axioms of
{name}`Geb.FreeTopos.theory`, without its subobject classifier or additional data objects.
The natural numbers object has its recursion equations and uniqueness.

An object of the slice over {lit}`A` is an arrow with codomain {lit}`A`. For an arrow
{lit}`f : A ⟶ B`, dependent sum is composition with {lit}`f`, and base change is the
pullback constructed from a product and an equalizer. Dependent product is an arrow
{lit}`pi f p` over {lit}`B`, with evaluation and abstraction. Their typing, computation,
and uniqueness equations express the right adjoint to base change, as in
\[Seely1984\], Section 2.4. No separate primitive slice categories are needed.

The presentation chooses structure: its homomorphisms preserve the named operations
strictly. Initiality for these homomorphisms is distinct from freeness for functors preserving
structure up to isomorphism. The latter requires a coherence theorem in addition to the
initial-model theorem. The finite colimits are not assumed disjoint or effective.

## Main definitions

* {lit}`sig`, {lit}`theory` — the signature and partial Horn theory.
* {lit}`pullback`, {lit}`baseChange`, {lit}`sigma`, {lit}`pi` — the slice operations.
* {lit}`piEval`, {lit}`piLam` — evaluation and abstraction for dependent product.

## References

* \[PalmgrenVickers2007\], Example 4 and Theorem 22, for partial Horn presentations.
* \[Seely1984\], Section 2.4, for the slice adjunctions.

## Tags

locally cartesian closed category, finite colimits, natural numbers object, partial Horn logic
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeLCCC

open PartialHorn FreeTopos.Sorts

export FreeTopos (x dom cod idt comp one bang prod fst snd pair eqz eqIncl eqLift zero absurd
  coprod inl inr copair coeqz coeqProj coeqDesc dfd)

/-- The finite-limit and finite-colimit signature, followed by the NNO and dependent product. -/
def sig : Sig := FreeTopos.sig.take 22 ++ [
  ([], obj), ([], arr), ([], arr), ([arr, arr], arr),
  ([arr, arr], arr), ([arr, arr], arr), ([arr, arr, arr, arr], arr)]

/-- The natural numbers object. -/
def nat : Tree := op 22 []

/-- Zero of the natural numbers object. -/
def zeroN : Tree := op 23 []

/-- Successor of the natural numbers object. -/
def succ : Tree := op 24 []

/-- Recursion from a start and an endomorphism. -/
def natRec (z s : Tree) : Tree := op 25 [z, s]

/-- The first arrow whose equalizer constructs a pullback. -/
def pullbackLeft (f q : Tree) : Tree := comp f (fst (dom f) (dom q))

/-- The second arrow whose equalizer constructs a pullback. -/
def pullbackRight (f q : Tree) : Tree := comp q (snd (dom f) (dom q))

/-- The pullback object of arrows with a common codomain. -/
def pullback (f q : Tree) : Tree := eqz (pullbackLeft f q) (pullbackRight f q)

/-- The pullback projection to the domain of the first arrow. -/
def pullFst (f q : Tree) : Tree :=
  comp (fst (dom f) (dom q)) (eqIncl (pullbackLeft f q) (pullbackRight f q))

/-- The pullback projection to the domain of the second arrow. -/
def pullSnd (f q : Tree) : Tree :=
  comp (snd (dom f) (dom q)) (eqIncl (pullbackLeft f q) (pullbackRight f q))

/-- The universal arrow into a pullback from a commuting cone. -/
def pullLift (f q a b : Tree) : Tree :=
  eqLift (pullbackLeft f q) (pullbackRight f q) (pair a b)

/-- Dependent sum sends a slice object to its composite with the indexing arrow. -/
def sigma (f p : Tree) : Tree := comp f p

/-- Base change sends a slice object to the first projection of its pullback. -/
def baseChange (f q : Tree) : Tree := pullFst f q

/-- Base change on a slice morphism from {lit}`q` to {lit}`r`. -/
def baseChangeMap (f q r h : Tree) : Tree :=
  pullLift f r (pullFst f q) (comp h (pullSnd f q))

/-- Dependent product of a slice object {lit}`p` along {lit}`f`, as an arrow over its codomain. -/
def pi (f p : Tree) : Tree := op 26 [f, p]

/-- Evaluation from the pullback of a dependent product. -/
def piEval (f p : Tree) : Tree := op 27 [f, p]

/-- Abstraction of a slice morphism from the base change of {lit}`q` to {lit}`p`. -/
def piLam (f p q h : Tree) : Tree := op 28 [f, p, q, h]

/-- Dependent product on a slice morphism from {lit}`p` to {lit}`r`. -/
def piMap (f p r h : Tree) : Tree := piLam f r (pi f p) (comp h (piEval f p))

/-- The transpose for the adjunction between dependent sum and base change. -/
def sigmaTranspose (f p q h : Tree) : Tree := pullLift f q p h

/-- The inverse transpose for the adjunction between dependent sum and base change. -/
def sigmaUntranspose (f q k : Tree) : Tree := comp (pullSnd f q) k

/-- An operation is defined exactly when its listed equations hold. -/
def domainAxioms (ctx : List ℕ) (conditions : List Eqn) (t : Tree) : List Seq :=
  ⟨ctx, conditions, dfd t⟩ :: conditions.map fun q ↦ ⟨ctx, [dfd t], q⟩

/-- A defined arrow has the indicated source and target. -/
def arrowAxioms (ctx : List ℕ) (t a b : Tree) : List Seq :=
  [⟨ctx, [dfd t], ⟨dom t, a⟩⟩, ⟨ctx, [dfd t], ⟨cod t, b⟩⟩]

/-- The recursion and uniqueness axioms of the natural numbers object. -/
def natAxioms : List Seq := [
  ⟨[], [], ⟨dom zeroN, one⟩⟩,
  ⟨[], [], ⟨cod zeroN, nat⟩⟩,
  ⟨[], [], ⟨dom succ, nat⟩⟩,
  ⟨[], [], ⟨cod succ, nat⟩⟩] ++
  domainAxioms [arr, arr]
    [⟨dom (x 0), one⟩, ⟨cod (x 0), dom (x 1)⟩, ⟨dom (x 1), cod (x 1)⟩]
    (natRec (x 0) (x 1)) ++
  arrowAxioms [arr, arr] (natRec (x 0) (x 1)) nat (cod (x 0)) ++ [
  ⟨[arr, arr], [dfd (natRec (x 0) (x 1))], ⟨comp (natRec (x 0) (x 1)) zeroN, x 0⟩⟩,
  ⟨[arr, arr], [dfd (natRec (x 0) (x 1))],
    ⟨comp (natRec (x 0) (x 1)) succ, comp (x 1) (natRec (x 0) (x 1))⟩⟩,
  ⟨[arr, arr, arr],
    [dfd (natRec (x 0) (x 1)), ⟨dom (x 2), nat⟩, ⟨comp (x 2) zeroN, x 0⟩,
      ⟨comp (x 2) succ, comp (x 1) (x 2)⟩],
    ⟨x 2, natRec (x 0) (x 1)⟩⟩]

/-- The conditions for abstracting a slice morphism over the domain of {lit}`f`. -/
def piLamDomain (f p q h : Tree) : List Eqn :=
  [⟨cod p, dom f⟩, ⟨cod q, cod f⟩, ⟨dom h, pullback f q⟩, ⟨cod h, dom p⟩,
    ⟨comp p h, pullFst f q⟩]

/-- The axioms of dependent product: its slice, evaluation, abstraction, and beta and eta. -/
def piAxioms : List Seq :=
  domainAxioms [arr, arr] [⟨cod (x 1), dom (x 0)⟩] (pi (x 0) (x 1)) ++ [
  ⟨[arr, arr], [dfd (pi (x 0) (x 1))], ⟨cod (pi (x 0) (x 1)), cod (x 0)⟩⟩] ++
  domainAxioms [arr, arr] [dfd (pi (x 0) (x 1))] (piEval (x 0) (x 1)) ++
  arrowAxioms [arr, arr] (piEval (x 0) (x 1)) (pullback (x 0) (pi (x 0) (x 1)))
    (dom (x 1)) ++ [
  ⟨[arr, arr], [dfd (piEval (x 0) (x 1))],
    ⟨comp (x 1) (piEval (x 0) (x 1)), pullFst (x 0) (pi (x 0) (x 1))⟩⟩] ++
  domainAxioms [arr, arr, arr, arr] (piLamDomain (x 0) (x 1) (x 2) (x 3))
    (piLam (x 0) (x 1) (x 2) (x 3)) ++
  arrowAxioms [arr, arr, arr, arr] (piLam (x 0) (x 1) (x 2) (x 3)) (dom (x 2))
    (dom (pi (x 0) (x 1))) ++ [
  ⟨[arr, arr, arr, arr], [dfd (piLam (x 0) (x 1) (x 2) (x 3))],
    ⟨comp (pi (x 0) (x 1)) (piLam (x 0) (x 1) (x 2) (x 3)), x 2⟩⟩,
  ⟨[arr, arr, arr, arr], [dfd (piLam (x 0) (x 1) (x 2) (x 3))],
    ⟨comp (piEval (x 0) (x 1))
      (baseChangeMap (x 0) (x 2) (pi (x 0) (x 1)) (piLam (x 0) (x 1) (x 2) (x 3))),
      x 3⟩⟩,
  ⟨[arr, arr, arr, arr],
    [dfd (pi (x 0) (x 1)), ⟨cod (x 2), cod (x 0)⟩, ⟨dom (x 3), dom (x 2)⟩,
      ⟨cod (x 3), dom (pi (x 0) (x 1))⟩, ⟨comp (pi (x 0) (x 1)) (x 3), x 2⟩],
    ⟨piLam (x 0) (x 1) (x 2)
      (comp (piEval (x 0) (x 1)) (baseChangeMap (x 0) (x 2) (pi (x 0) (x 1)) (x 3))),
      x 3⟩⟩]

/-- The reused axioms of a category with finite limits and finite colimits. -/
def finiteAxioms : List Seq :=
  FreeTopos.categoryAxioms ++ FreeTopos.terminalAxioms ++ FreeTopos.productAxioms ++
    FreeTopos.equalizerAxioms ++ FreeTopos.initialAxioms ++ FreeTopos.coproductAxioms ++
    FreeTopos.coequalizerAxioms

/-- The axioms of finite limits, finite colimits, an NNO, and local cartesian closure. -/
def axioms : List Seq := finiteAxioms ++ natAxioms ++ piAxioms

/-- The theory with chosen structure and no additional generators. -/
def theory : Theory := ⟨sig, axioms⟩

end Geb.FreeLCCC

end

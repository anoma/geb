/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Prover.Tactic

set_option doc.verso true in
/-!
# The prover's library of rewriting rules

The rules by which the prover normalizes arrows, and the derived equations among them, each
proved by the prover and added to the library's development. The axioms supply associativity,
read to compose to the right; the identity laws; the projections after a pairing; the
contraction of a pairing of projections after one arrow; the uniqueness of the morphism to the
terminal object; and the computation rules of recursion from the natural numbers object and
from a list object. The development supplies composition after a pairing, which distributes over
it; the pairing of the two projections, which is the identity; evaluation after the pairing of a
currying, after an arrow or alone, with another arrow, which is the curried morphism after a
pairing; the naturality of currying in its domain; and the morphism from the terminal object to
itself, which is the identity. The uniqueness of the morphism to the terminal object does not
apply at an identity, so that the identity of the terminal object stays one.

## Main definitions

* {lit}`baseRules` — the rules from the axioms.
* {lit}`compPairSeq`, {lit}`pairFstSndSeq`, {lit}`evCurrySeq`, {lit}`evCurry0Seq`,
  {lit}`curryNatSeq`, {lit}`bangOneSeq` — the derived equations.
* {lit}`libraryWith`, {lit}`library` — the library's development, with the indices of the
  derived equations.
* {lit}`rules` — the rules of the axioms and of the library.

## Tags

elementary topos, rewriting, proof certificate
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Prover

open PartialHorn Sorts
open scoped FinEnum

/-- The rules from the axioms: associativity to the right, the identity laws, the projections
after a pairing, the contraction of a pairing of projections, the morphism to the terminal
object, and the computation rules of recursion. -/
def baseRules : List RwRule := [
  { src := .ax 7, flip := true },
  { src := .ax 10 },
  { src := .ax 11 },
  { src := .ax (axIdx beforeProduct 9) },
  { src := .ax (axIdx beforeProduct 10) },
  { src := .ax (axIdx beforeProduct 11) },
  { src := .ax (axIdx beforeTerminal 3), avoid := [3, 6] },
  { src := .ax (axIdx beforeNat 10) },
  { src := .ax (axIdx beforeNat 11) },
  { src := .ax (axIdx beforeList 11) },
  { src := .ax (axIdx beforeList 12) }]

/-- Composition after a pairing distributes over it:
{lit}`comp (pair f g) h = pair (comp f h) (comp g h)`. -/
def compPairSeq : Seq :=
  ⟨[arr, arr, arr], [⟨dom (x 1), dom (x 0)⟩, ⟨cod (x 2), dom (x 0)⟩],
    ⟨comp (pair (x 0) (x 1)) (x 2), pair (comp (x 0) (x 2)) (comp (x 1) (x 2))⟩⟩

/-- The pairing of the projections of a product is its identity. -/
def pairFstSndSeq : Seq :=
  ⟨[obj, obj], [], ⟨pair (fst (x 0) (x 1)) (snd (x 0) (x 1)), idt (prod (x 0) (x 1))⟩⟩

/-- Evaluation after the pairing of a currying after an arrow with another arrow is the curried
morphism after the pairing of the two arrows. -/
def evCurrySeq : Seq :=
  ⟨[obj, obj, arr, arr, arr],
    [⟨dom (x 2), prod (x 0) (x 1)⟩, ⟨cod (x 3), x 0⟩, ⟨cod (x 4), x 1⟩, ⟨dom (x 4), dom (x 3)⟩],
    ⟨comp (ev (x 1) (cod (x 2))) (pair (comp (curry (x 0) (x 1) (x 2)) (x 3)) (x 4)),
      comp (x 2) (pair (x 3) (x 4))⟩⟩

/-- Evaluation after the pairing of a currying with an arrow is the curried morphism after the
pairing of the identity with the arrow. -/
def evCurry0Seq : Seq :=
  ⟨[obj, obj, arr, arr], [⟨dom (x 2), prod (x 0) (x 1)⟩, ⟨cod (x 3), x 1⟩, ⟨dom (x 3), x 0⟩],
    ⟨comp (ev (x 1) (cod (x 2))) (pair (curry (x 0) (x 1) (x 2)) (x 3)),
      comp (x 2) (pair (idt (x 0)) (x 3))⟩⟩

/-- Currying is natural in its domain: a currying after an arrow is the currying of the curried
morphism after the product of the arrow with the identity. -/
def curryNatSeq : Seq :=
  ⟨[obj, obj, arr, arr], [⟨dom (x 2), prod (x 0) (x 1)⟩, ⟨cod (x 3), x 0⟩],
    ⟨comp (curry (x 0) (x 1) (x 2)) (x 3),
      curry (dom (x 3)) (x 1) (comp (x 2) (prodMapLeft (x 3) (x 1)))⟩⟩

/-- The morphism from the terminal object to itself is its identity. -/
def bangOneSeq : Seq := ⟨[], [], ⟨bang one, idt one⟩⟩

/-- The proof of {lit}`compPairSeq`: expand the composite into the product, and normalize. -/
def compPairProof : PM Tree := do
  let (e, ce) ← etaExpand compPairSeq.concl.lhs
  let (n, cn) ← normalize baseRules e
  guard (n == compPairSeq.concl.rhs)
  pure (Cert.trans ce cn)

/-- The proof of {lit}`pairFstSndSeq`: the contraction of the pairing of the projections after
the identity, whose projections normalize to the projections. -/
def pairFstSndProof : PM Tree := do
  let p := prod (x 0) (x 1)
  let (q, c) ← inst (.ax (axIdx beforeProduct 11)) [idt p, x 0, x 1]
  let (n, cn) ← normalize baseRules q.lhs
  guard (n == pairFstSndSeq.concl.lhs)
  pure (Cert.trans (Cert.symm cn) c)

/-- The proof of {lit}`evCurrySeq`: currying's computation rule after the pairing of the two
arrows, whose left side normalizes to the equation's. -/
def evCurryProof (cp : ℕ) : PM Tree := do
  let rs := baseRules ++ [{ src := .thm cp }]
  let (q, c) ← inst (.ax (axIdx beforeExponential 7)) [x 0, x 1, x 2]
  let gh := pair (x 3) (x 4)
  let u := comp q.lhs gh
  let (nu, cu) ← normalize rs u
  let (ng, cg) ← normalize rs evCurrySeq.concl.lhs
  guard (nu == ng)
  let du ← typeTerm u
  pure (Cert.trans (Cert.trans cg (Cert.symm cu)) (Cert.cong du.dfd [c, (← typeTerm gh).dfd]))

/-- The proof of {lit}`evCurry0Seq`: {lit}`evCurrySeq` after the identity, whose left side
normalizes to the equation's. -/
def evCurry0Proof (ec : ℕ) : PM Tree := do
  let (q, c) ← inst (.thm ec) [x 0, x 1, x 2, idt (x 0), x 3]
  let (n, cn) ← normalize baseRules q.lhs
  guard (n == evCurry0Seq.concl.lhs && q.rhs == evCurry0Seq.concl.rhs)
  pure (Cert.trans (Cert.symm cn) c)

/-- The proof of {lit}`curryNatSeq`: the uniqueness of currying at the composite, whose
curried morphism normalizes, by {lit}`evCurrySeq`, to the equation's. -/
def curryNatProof (cp ec : ℕ) : PM Tree := do
  let rs := baseRules ++ [{ src := .thm cp }, { src := .thm ec }]
  let k := curryNatSeq.concl.lhs
  let (q, c) ← inst (.ax (axIdx beforeExponential 8)) [dom (x 3), x 1, cod (x 2), k]
  let (n, cn) ← normalize rs q.lhs
  let (r, cr) ← normalize rs curryNatSeq.concl.rhs
  guard (n == r)
  pure (Cert.trans (Cert.symm c) (Cert.trans cn (Cert.symm cr)))

/-- The proof of {lit}`bangOneSeq`: the uniqueness of the morphism to the terminal object at
its identity. -/
def bangOneProof : PM Tree := do
  let (q, c) ← inst (.ax (axIdx beforeTerminal 3)) [idt one]
  let (n, cn) ← normalize baseRules q.rhs
  guard (n == bang one)
  pure (Cert.symm (Cert.trans c cn))

/-- The indices of the library's derived equations in its development. -/
structure LibIdx where
  /-- {lit}`compPairSeq`. -/
  compPair : ℕ
  /-- {lit}`pairFstSndSeq`. -/
  pairFstSnd : ℕ
  /-- {lit}`evCurrySeq`. -/
  evCurry : ℕ
  /-- {lit}`evCurry0Seq`. -/
  evCurry0 : ℕ
  /-- {lit}`curryNatSeq`. -/
  curryNat : ℕ
  /-- {lit}`bangOneSeq`. -/
  bangOne : ℕ

/-- The library's development, and the indices of its derived equations, its typing certified
by lemmas or, when {lit}`infer` holds, by the checker's oracle rules. -/
def libraryWith (infer : Bool) : Option (LibIdx × Development) := (do
  let prove (a : Seq) (m : PM Tree) := proveSeq a m (infer := infer)
  let cp ← prove compPairSeq compPairProof
  let pf ← prove pairFstSndSeq pairFstSndProof
  let ec ← prove evCurrySeq (evCurryProof cp)
  let e0 ← prove evCurry0Seq (evCurry0Proof ec)
  let cn ← prove curryNatSeq (curryNatProof cp ec)
  let bo ← prove bangOneSeq bangOneProof
  pure ⟨cp, pf, ec, e0, cn, bo⟩ : StateT Development Option LibIdx).run []

/-- The library's development, its typing certified by the checker's oracle rules. -/
def library : Option (LibIdx × Development) := libraryWith true

/-- The rules of the axioms and of the library's derived equations. A currying after an arrow
is absorbed into the currying, so that evaluation meets curryings alone. -/
def rules (i : LibIdx) : List RwRule :=
  baseRules ++ [{ src := .thm i.compPair }, { src := .thm i.pairFstSnd },
    { src := .thm i.curryNat }, { src := .thm i.evCurry0 }, { src := .thm i.bangOne }]

end Geb.FreeTopos.Prover

end

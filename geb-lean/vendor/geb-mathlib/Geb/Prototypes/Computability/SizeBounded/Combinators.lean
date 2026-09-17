/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Basic

set_option doc.verso true in
/-!
# Expression combinators of the non-size-increasing algebra

Each shape of {name}`Geb.SizeBounded.sig` as a constructor of expressions of a
declared arity, {name}`Geb.SizeBounded.SOf`, carrying admissibility, together with
the equations their meanings satisfy; and on top of them the tail, the four-way
conditional and the diagonal, each a single recursion or substitution node.
Every expression built here is admissible by construction, so no
{lit}`decide` is discharged and no side condition is proved: this is what
distinguishes the algebra from {name}`Cobham.C`, whose {lit}`Cobham.scan`
takes a bound on the value it produces.

# Main definitions

* {lit}`constOf`, {lit}`projOf`, {lit}`sbsOf` — the base forms as expressions.
* {lit}`compOf` — substitution of a family of expressions into one.
* {lit}`srnOf` — one component of a simultaneous recursion on notation.
* {lit}`tailOf` — the word with its head bit dropped.
* {lit}`condOf`, {lit}`cond4Sem` — the four-way conditional, branching on
  emptiness and head bit, and the function it computes.
* {lit}`diagOf` — a binary expression at its sole argument in both positions.
* {lit}`cond4`, {lit}`tailApp`, {lit}`sbsApp` — the conditional, the tail and the
  size-bounded successor applied to expressions of a common arity.

# Main statements

* {lit}`sem_constOf`, {lit}`sem_projOf`, {lit}`sem_sbsOf`, {lit}`sem_compOf`,
  {lit}`sem_srnOf_nil`, {lit}`sem_srnOf_cons` — the meaning of each node in
  terms of its children's, each definitional.
* {lit}`sem_tailOf`, {lit}`sem_condOf`, {lit}`sem_diagOf`, {lit}`sem_cond4`,
  {lit}`sem_tailApp`, {lit}`sem_sbsApp` — the meanings of the derived
  expressions.

# Implementation notes

The meaning of an expression of a declared arity, {name}`Geb.SizeBounded.SOf.sem`,
is a single transport along the composite of {name}`Geb.SizeBounded.fst_eval` with
the arity equation, and {name}`Geb.SizeBounded.evalValue` transports each child
along the composite of the same theorem with the node's compatibility. Two
transports along proofs of one equation are definitionally equal by proof
irrelevance, so every node equation here is a {lit}`rfl`; the double transport
that makes {lit}`Cobham.baseWord_eq_eval` a theorem does not arise.

Admissibility of a node is the pair of its children's admissibility and the
{lit}`funext` identifying their arities with what {name}`Geb.SizeBounded.rc`
prescribes, the latter through
{name}`SlicePFunctor.wIndexValid_index_eq_wIndexRoot`, as in
{lit}`Cobham.wValid_scanRaw`.

# References

* \[Mazzanti2016\]

# Tags

non-size-increasing, simultaneous recursion on notation, function algebra,
combinator
-/

set_option doc.verso true

namespace Geb.SizeBounded

open Cobham (Sem)

public section

/-- The constant word {lit}`w` as an expression of arity {lit}`n`. -/
@[expose] def constOf (n : ℕ) (w : List Bool) : SOf n :=
  ⟨⟨WType.mk (.const n w) Fin.elim0, ⟨fun i ↦ i.elim0, funext fun i ↦ i.elim0⟩⟩, rfl⟩

/-- The meaning of a constant. -/
theorem sem_constOf (n : ℕ) (w : List Bool) (x : Fin n → List Bool) :
    (constOf n w).sem x = w := rfl

/-- The {lit}`i`th of {lit}`n` variables, as an expression of arity {lit}`n`. -/
@[expose] def projOf (n : ℕ) (i : Fin n) : SOf n :=
  ⟨⟨WType.mk (.proj n i) Fin.elim0, ⟨fun i ↦ i.elim0, funext fun i ↦ i.elim0⟩⟩, rfl⟩

/-- The meaning of a projection. -/
theorem sem_projOf (n : ℕ) (i : Fin n) (x : Fin n → List Bool) : (projOf n i).sem x = x i :=
  rfl

/-- The size-bounded successor prepending {lit}`b`, as an expression of arity two. -/
@[expose] def sbsOf (b : Bool) : SOf 2 :=
  ⟨⟨WType.mk (.sbs b) Fin.elim0, ⟨fun i ↦ i.elim0, funext fun i ↦ i.elim0⟩⟩, rfl⟩

/-- The meaning of the size-bounded successor. -/
theorem sem_sbsOf (b : Bool) (x : Fin 2 → List Bool) :
    (sbsOf b).sem x = sbsSem b (x 0) (x 1) := rfl

/-- The substitution of {lit}`m` expressions of arity {lit}`n` into an expression
of arity {lit}`m`. -/
@[expose] def compOf {n m : ℕ} (h : SOf m) (g : Fin m → SOf n) : SOf n :=
  ⟨⟨WType.mk (.comp n m) fun d ↦
      match d with
      | .inl () => h.1.1
      | .inr i => (g i).1.1,
    ⟨fun d ↦ match d with
      | .inl () => h.1.2
      | .inr i => (g i).1.2,
    funext fun d ↦ match d with
      | .inl () => (sig.wIndexValid_index_eq_wIndexRoot h.1.1).trans h.2
      | .inr i => (sig.wIndexValid_index_eq_wIndexRoot (g i).1.1).trans (g i).2⟩⟩,
  rfl⟩

/-- The meaning of a substitution. -/
theorem sem_compOf {n m : ℕ} (h : SOf m) (g : Fin m → SOf n) (x : Fin n → List Bool) :
    (compOf h g).sem x = h.sem (fun i ↦ (g i).sem x) := rfl

/-- The {lit}`j`th of the {lit}`b` functions defined by simultaneous recursion on
notation from the bases {lit}`g` and the steps {lit}`h`, with {lit}`a`
parameters. -/
@[expose] def srnOf {a b : ℕ} (g : Fin b → SOf a) (h : Bool → Fin b → SOf (b + a + 1))
    (j : Fin b) : SOf (a + 1) :=
  ⟨⟨WType.mk (.srn a b j) fun d ↦
      match d with
      | .inl l => (g l).1.1
      | .inr (.inl l) => (h false l).1.1
      | .inr (.inr l) => (h true l).1.1,
    ⟨fun d ↦ match d with
      | .inl l => (g l).1.2
      | .inr (.inl l) => (h false l).1.2
      | .inr (.inr l) => (h true l).1.2,
    funext fun d ↦ match d with
      | .inl l => (sig.wIndexValid_index_eq_wIndexRoot (g l).1.1).trans (g l).2
      | .inr (.inl l) => (sig.wIndexValid_index_eq_wIndexRoot (h false l).1.1).trans (h false l).2
      | .inr (.inr l) =>
        (sig.wIndexValid_index_eq_wIndexRoot (h true l).1.1).trans (h true l).2⟩⟩,
  rfl⟩

/-- The meaning of a recursion node is {name}`evalSRN` at its children's meanings,
on slot zero, with the remaining slots as parameters. The base family agrees with
the children's meanings definitionally; the step family does so only once the bit
is a constructor, since the direction of a step is selected by a case split on the
bit. -/
theorem sem_srnOf {a b : ℕ} (g : Fin b → SOf a) (h : Bool → Fin b → SOf (b + a + 1))
    (j : Fin b) (x : Fin (a + 1) → List Bool) :
    (srnOf g h j).sem x =
      evalSRN (fun l ↦ (g l).sem) (fun i l ↦ (h i l).sem) (x 0) j (Fin.tail x) := by
  change evalSRN _ (srnSteps _ _) (x 0) j (Fin.tail x) = _
  exact congrArg (fun H ↦ evalSRN _ H (x 0) j (Fin.tail x))
    (funext fun i ↦ funext fun l ↦ by cases i <;> rfl)

/-- A recursion on the empty word is its base. -/
theorem sem_srnOf_nil {a b : ℕ} (g : Fin b → SOf a) (h : Bool → Fin b → SOf (b + a + 1))
    (j : Fin b) (y : Fin a → List Bool) :
    (srnOf g h j).sem (Fin.cons [] y) = (g j).sem y := rfl

/-- A recursion on {lit}`i :: v` is the step on {lit}`i`, at the environment
holding {lit}`v`, every component's value on {lit}`v`, and the parameters. -/
theorem sem_srnOf_cons {a b : ℕ} (g : Fin b → SOf a) (h : Bool → Fin b → SOf (b + a + 1))
    (j : Fin b) (i : Bool) (v : List Bool) (y : Fin a → List Bool) :
    (srnOf g h j).sem (Fin.cons (i :: v) y) =
      (h i j).sem (stepEnv v (fun l ↦ (srnOf g h l).sem (Fin.cons v y)) y) := by
  simp only [sem_srnOf, Fin.cons_zero, Fin.tail_cons]
  rfl

/-- The word with its head bit dropped: a recursion whose base is the empty word
and whose steps return the remaining word. -/
@[expose] def tailOf : SOf 1 :=
  srnOf (fun _ ↦ constOf 0 []) (fun _ _ ↦ projOf 2 0) 0

/-- The meaning of the tail. -/
theorem sem_tailOf (w : List Bool) : tailOf.sem ![w] = w.tail := by
  cases w with
  | nil => rfl
  | cons i v => cases i <;> rfl

/-- The four-way conditional as a recursion with three parameters: on the empty
scrutinee the first parameter, on a head bit {lit}`true` the second, on
{lit}`false` the third. The step environment holds the remaining word in slot
zero, the recursive value in slot one and the parameters after them. -/
@[expose] def condOf : SOf 4 :=
  srnOf (fun _ ↦ projOf 3 0) (fun i _ ↦ if i then projOf 5 3 else projOf 5 4) 0

/-- The four-way conditional's meaning: the second, third or fourth argument
according as the first is empty, has head {lit}`true` or has head {lit}`false`. -/
@[expose] def cond4Sem (u v w z : List Bool) : List Bool :=
  match u with
  | [] => v
  | true :: _ => w
  | false :: _ => z

/-- The conditional computes {name}`cond4Sem`. -/
theorem sem_condOf (u v w z : List Bool) : condOf.sem ![u, v, w, z] = cond4Sem u v w z := by
  match u with
  | [] | true :: _ | false :: _ => rfl

/-- The conditional applied to four expressions of a common arity. -/
@[expose] def cond4 {n : ℕ} (s e t f : SOf n) : SOf n := compOf condOf ![s, e, t, f]

/-- The meaning of an applied conditional. -/
theorem sem_cond4 {n : ℕ} (s e t f : SOf n) (x : Fin n → List Bool) :
    (cond4 s e t f).sem x = cond4Sem (s.sem x) (e.sem x) (t.sem x) (f.sem x) := by
  change condOf.sem (fun i ↦ (![s, e, t, f] i).sem x) = _
  rw [show (fun i ↦ (![s, e, t, f] i).sem x) = ![s.sem x, e.sem x, t.sem x, f.sem x] from
    funext fun i ↦ match i with | 0 | 1 | 2 | 3 => rfl]
  exact sem_condOf _ _ _ _

/-- The tail applied to an expression. -/
@[expose] def tailApp {n : ℕ} (e : SOf n) : SOf n := compOf tailOf ![e]

/-- The meaning of an applied tail. -/
theorem sem_tailApp {n : ℕ} (e : SOf n) (x : Fin n → List Bool) :
    (tailApp e).sem x = (e.sem x).tail := by
  change tailOf.sem (fun i ↦ (![e] i).sem x) = _
  rw [show (fun i ↦ (![e] i).sem x) = ![e.sem x] from funext fun i ↦ match i with | 0 => rfl]
  exact sem_tailOf _

/-- A binary expression at its sole argument in both positions. -/
@[expose] def diagOf (e : SOf 2) : SOf 1 := compOf e fun _ ↦ projOf 1 0

/-- The meaning of the diagonal. -/
theorem sem_diagOf (e : SOf 2) (w : List Bool) : (diagOf e).sem ![w] = e.sem ![w, w] := by
  change e.sem (fun _ ↦ w) = e.sem ![w, w]
  exact congrArg e.sem (funext fun i ↦ match i with | 0 | 1 => rfl)

/-- The size-bounded successor of {lit}`e`, bounded by {lit}`bound`. -/
@[expose] def sbsApp {n : ℕ} (b : Bool) (e bound : SOf n) : SOf n :=
  compOf (sbsOf b) ![e, bound]

/-- The meaning of a bounded successor application. -/
theorem sem_sbsApp {n : ℕ} (b : Bool) (e bound : SOf n) (x : Fin n → List Bool) :
    (sbsApp b e bound).sem x = sbsSem b (e.sem x) (bound.sem x) := rfl

end

end Geb.SizeBounded

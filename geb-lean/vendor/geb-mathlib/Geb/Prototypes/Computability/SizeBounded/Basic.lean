/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Computability.Cobham.Basic

set_option doc.verso true

/-!
# Mazzanti's algebra of non-size-increasing bitstring functions

The syntax of the function algebra {lit}`S(sbs₀, sbs₁)` of \[Mazzanti2016\]
over bitstrings, together with its interpretation and the theorem that every
expression denotes a non-size-increasing function. The base functions are the
constants, the projections and the two size-bounded binary successors
{lit}`sbs_b(x, y)`, which prepend the bit {lit}`b` to {lit}`x` when the result is
no longer than {lit}`y` and return {lit}`x` otherwise; the operators are
substitution and simultaneous recursion on notation. Unlike bounded recursion on
notation, whose side condition {name}`Cobham.RecBounded` enforces, simultaneous
recursion here carries no condition: every admissible tree of the signature is an
expression of the algebra, and its meaning is non-size-increasing by
{lit}`nsi_eval`, the bitstring form of \[Mazzanti2016\] Lemma 2.1.

The paper works over the natural numbers in binary notation. Over
{lit}`List Bool` both successors are injective, so the guard {lit}`x > 0` the
paper attaches to the {lit}`i = 0` recursion clause is vacuous, and the length
of a word is its list length. The signature, the environment convention and the
meaning type are those of {name}`Cobham.sig`: an environment is a function
{lit}`Fin n → List Bool`, the meaning of an arity is {name}`Cobham.Sem`, and a
recursion peels the list's head, passing the remaining word in slot zero, the
recursive values in the next slots and the parameters after them.

# Main definitions

* {lit}`Shape` — the five constructor forms, with their arities as parameters.
* {lit}`Direction`, {lit}`rc`, {lit}`q` — the subterm positions of a shape, the
  arity each must carry, and the arity a shape produces.
* {lit}`sig` — the signature, as a slice polynomial functor over {lit}`ℕ`.
* {lit}`sigFinitary` — every shape has finitely many directions.
* {lit}`sbsSem` — the size-bounded successor.
* {lit}`evalSRN` — simultaneous recursion on notation, by {lit}`List.rec`.
* {lit}`srnBases`, {lit}`srnSteps` — the base and step families a recursion
  node's children supply.
* {lit}`evalValue`, {lit}`evalStep`, {lit}`eval` — the meaning of one node, the
  slice algebra it forms, and the interpretation of a tree.
* {lit}`S`, {lit}`SOf`, {lit}`arity`, {lit}`semAt` — the expressions, those of a
  given arity, the arity of an expression, and its meaning at a given arity.
* {lit}`NSI` — a function is non-size-increasing with a given constant.
* {lit}`finMax`, {lit}`nsiConst` — a finite maximum, and the constant an
  expression's meaning is non-size-increasing with, read off its syntax.

# Main statements

* {lit}`fst_eval` — the index component of a tree's interpretation is its arity.
* {lit}`le_finMax` — every value is at most the finite maximum.
* {lit}`nsi_mono`, {lit}`nsi_transport` — the property is monotone in its
  constant and invariant under transport of the arity.
* {lit}`nsi_const`, {lit}`nsi_proj`, {lit}`nsi_sbs`, {lit}`nsi_comp`,
  {lit}`nsi_srn` — the base functions are non-size-increasing, and substitution
  and simultaneous recursion preserve the property.
* {lit}`nsi_eval` — every expression denotes a non-size-increasing function, with
  the constant {lit}`nsiConst` reads off its syntax.

# Implementation notes

The syntax is a slice W-type as {name}`Cobham.sig`'s is, since a self-referential
inductive type is excluded by the project's recursion discipline; the
{lit}`evalValue`, {lit}`evalStep`, {lit}`eval`, {lit}`semAt` layer transcribes
{name}`Cobham.evalValue` and its successors, with {name}`Cobham.transport` carrying
a child's meaning to the arity {lit}`rc` prescribes. Simultaneous recursion with
{lit}`b` components is one shape per component, {lit}`srn a b j`, whose children
are the {lit}`b` base expressions and the {lit}`2 b` step expressions shared by
all components; {lit}`evalSRN` computes every component and {lit}`evalValue`
projects the {lit}`j`th. At {lit}`b = 1` its environment
{lit}`Fin.cons v (Fin.append vals x)` is {name}`Cobham.evalRec`'s
{lit}`Fin.cons v (Fin.cons (ih x) x)` up to the identification of a one-element
{lit}`Fin.append` with a {lit}`Fin.cons`.

{lit}`NSI k f` quantifies over a bound {lit}`m` on every argument's length rather
than over their maximum, so that no finite supremum enters the statement;
{lit}`finMax` is a {lit}`Nat.rec` because {lit}`Finset.sup` over {lit}`Fin m` was
measured to depend on {lit}`Classical.choice`. Constants are a shape at every
arity rather than a nullary shape under a substitution, which spares the
{lit}`comp n 0` node {name}`Cobham.zeroAt` builds.

# References

* \[Mazzanti2016\]
* \[Clote1999\]

# Tags

non-size-increasing, simultaneous recursion on notation, function algebra,
polynomial time, linear space, W-type, polynomial functor
-/

namespace Geb.SizeBounded

open scoped FinEnum
open Cobham (Sem transport)

public section

/-- The five constructor forms of the algebra, each carrying its arities as
parameters: {lit}`const n w` the constant word {lit}`w` at arity {lit}`n`;
{lit}`proj n i` the {lit}`i`th of {lit}`n` variables; {lit}`sbs b` the size-bounded
successor prepending {lit}`b`; {lit}`comp n m` the substitution of {lit}`m`
{lit}`n`-ary expressions into an {lit}`m`-ary one; {lit}`srn a b j` the {lit}`j`th
of the {lit}`b` functions defined by simultaneous recursion on notation with
{lit}`a` parameters. -/
inductive Shape
  | const (n : ℕ) (w : List Bool)
  | proj (n : ℕ) (i : Fin n)
  | sbs (b : Bool)
  | comp (n m : ℕ)
  | srn (a b : ℕ) (j : Fin b)

/-- The subterm positions of a shape. The three base forms have none; {lit}`comp`
has its head and its {lit}`m` arguments; {lit}`srn` has the {lit}`b` base
expressions, then the {lit}`b` steps taken on a {lit}`false` bit, then the
{lit}`b` steps taken on a {lit}`true` bit. -/
@[expose, reducible] def Direction : Shape → Type
  | .const _ _ => Fin 0
  | .proj _ _ => Fin 0
  | .sbs _ => Fin 0
  | .comp _ m => Unit ⊕ Fin m
  | .srn _ b _ => Fin b ⊕ (Fin b ⊕ Fin b)

/-- The arity each subterm position must carry: a base expression of the
recursion takes the {lit}`a` parameters, a step takes the remaining word, the
{lit}`b` recursive values and the parameters. -/
@[expose, reducible] def rc : (a : Shape) → Direction a → ℕ
  | .const _ _, i => i.elim0
  | .proj _ _, i => i.elim0
  | .sbs _, i => i.elim0
  | .comp _ m, .inl () => m
  | .comp n _, .inr _ => n
  | .srn a _ _, .inl _ => a
  | .srn a b _, .inr _ => b + a + 1

/-- The arity a shape produces. -/
@[expose, reducible] def q : Shape → ℕ
  | .const n _ => n
  | .proj n _ => n
  | .sbs _ => 2
  | .comp n _ => n
  | .srn a _ _ => a + 1

/-- The signature as a slice polynomial functor over {lit}`ℕ`, the index being the
arity. -/
@[expose] def sig : SlicePFunctor ℕ ℕ where
  A := Shape
  B := Direction
  r := fun x ↦ rc x.1 x.2
  q := q

/-- Every shape has finitely many directions, which makes admissibility of a tree
decidable. The branches ascribe their instances as {name}`Cobham.sigFinitary`'s
do. -/
instance sigFinitary : sig.toPFunctor.Finitary
  | .const _ _ => inferInstanceAs (FinEnum (Fin 0))
  | .proj _ _ => inferInstanceAs (FinEnum (Fin 0))
  | .sbs _ => inferInstanceAs (FinEnum (Fin 0))
  | .comp _ m => inferInstanceAs (FinEnum (Unit ⊕ Fin m))
  | .srn _ b _ => inferInstanceAs (FinEnum (Fin b ⊕ (Fin b ⊕ Fin b)))

/-- The direction of the step taken on bit {lit}`i` for component {lit}`l`. -/
@[expose] def stepDir {b : ℕ} (i : Bool) (l : Fin b) : Fin b ⊕ (Fin b ⊕ Fin b) :=
  .inr (if i then .inr l else .inl l)

/-- The size-bounded successor of \[Mazzanti2016\] § 2 over bitstrings:
{lit}`b` prepended to {lit}`x` when the result is no longer than {lit}`y`, and
{lit}`x` otherwise. -/
@[expose] def sbsSem (b : Bool) (x y : List Bool) : List Bool :=
  if x.length + 1 ≤ y.length then b :: x else x

/-- Simultaneous recursion on notation, by {lit}`List.rec`: on the empty word each
component is its base; on {lit}`i :: v` the {lit}`j`th component is the step
{lit}`h i j` at the environment holding {lit}`v`, the {lit}`b` recursive values and
the parameters. -/
@[expose] def evalSRN {a b : ℕ} (g : Fin b → Sem a) (h : Bool → Fin b → Sem (b + a + 1)) :
    List Bool → Fin b → Sem a :=
  List.rec g (fun i v ih j x ↦
    h i j (Fin.cons v (Fin.append (fun l ↦ ih l x) x) : Fin (b + a + 1) → List Bool))

/-- The base family a recursion node's children supply: the meaning of the
{lit}`l`th base child, at the arity {lit}`rc` prescribes. -/
@[expose] def srnBases {a b : ℕ} {j : Fin b} (c : Direction (.srn a b j) → Σ i, Sem i)
    (h : ∀ d, (c d).1 = rc (.srn a b j) d) : Fin b → Sem a :=
  fun l ↦ transport (h (.inl l)) (c (.inl l)).2

/-- The step family a recursion node's children supply: the meaning of the step
child for bit {lit}`i` and component {lit}`l`, at the arity {lit}`rc`
prescribes. -/
@[expose] def srnSteps {a b : ℕ} {j : Fin b} (c : Direction (.srn a b j) → Σ i, Sem i)
    (h : ∀ d, (c d).1 = rc (.srn a b j) d) : Bool → Fin b → Sem (b + a + 1) :=
  fun i l ↦ transport (h (stepDir i l)) (c (stepDir i l)).2

/-- The meaning of one node, from its children's meanings and the proof that each
child's index is the one {lit}`rc` prescribes. -/
@[expose] def evalValue : (a : Shape) → (c : Direction a → Σ i, Sem i) →
    (∀ b, (c b).1 = rc a b) → Sem (q a)
  | .const _ w, _, _ => fun _ ↦ w
  | .proj _ i, _, _ => fun x ↦ x i
  | .sbs b, _, _ => fun x ↦ sbsSem b (x 0) (x 1)
  | .comp _ _, c, h => fun x ↦
      transport (h (.inl ())) (c (.inl ())).2
        (fun i ↦ transport (h (.inr i)) (c (.inr i)).2 x)
  | .srn _ _ j, c, h => fun x ↦ evalSRN (srnBases c h) (srnSteps c h) (x 0) j (Fin.tail x)

/-- {lit}`evalValue` as an algebra for {lit}`sig` in the slice over {lit}`ℕ`. -/
@[expose] def evalStep :
    sig.toSliceDomPFunctor.Obj (Sigma.fst (β := Sem)) → Σ i, Sem i :=
  fun z ↦ ⟨sig.q z.1.1,
    evalValue z.1.1 z.1.2
      ((sig.toSliceDomPFunctor.compatible_iff _ z.1.1 z.1.2).mp z.2)⟩

/-- The interpretation of a tree: its arity together with its meaning at that
arity, by the slice W-type's eliminator. -/
@[expose] def eval : sig.W → Σ n, Sem n :=
  SlicePFunctor.W.elim sig (Σ n, Sem n) (Sigma.fst (β := Sem)) evalStep rfl

/-- The expressions of the algebra: the admissible trees of the signature. No
further condition applies. -/
@[expose] def S : Type := sig.W

/-- The arity of an expression. -/
@[expose] def arity : S → ℕ := sig.wIndex

/-- The expressions of a given arity. -/
@[expose] def SOf (n : ℕ) : Type := { e : S // arity e = n }

/-- The index component of a tree's interpretation is the tree's arity. -/
theorem fst_eval (z : S) : (eval z).1 = arity z :=
  congrFun (SlicePFunctor.W.comp_elim sig (Σ n, Sem n) (Sigma.fst (β := Sem)) evalStep rfl) z

/-- The meaning of an expression at a given arity. -/
@[expose] def semAt (n : ℕ) (e : S) (he : arity e = n) : Sem n :=
  transport ((fst_eval e).trans he) (eval e).2

/-- The meaning of an expression of a given arity. -/
@[expose] def SOf.sem {n : ℕ} (e : SOf n) : Sem n := semAt n e.1 e.2

/-- A function is non-size-increasing with constant {lit}`k`: whenever every
argument has length at most {lit}`m`, the value has length at most
{lit}`max m k`. This is \[Mazzanti2016\] § 2's
{lit}`|f(x)| ≤ max(|x|, k)` with the maximum of the argument lengths replaced
by any bound on them. -/
@[expose] def NSI {n : ℕ} (k : ℕ) (f : Sem n) : Prop :=
  ∀ (x : Fin n → List Bool) (m : ℕ), (∀ i, (x i).length ≤ m) → (f x).length ≤ max m k

/-- The property is monotone in its constant. -/
theorem nsi_mono {n k k' : ℕ} {f : Sem n} (hk : k ≤ k') (hf : NSI k f) : NSI k' f :=
  fun x m hx ↦ by
    have := hf x m hx
    omega

/-- The property is invariant under transport of the arity. -/
theorem nsi_transport {i j k : ℕ} (h : i = j) {f : Sem i} (hf : NSI k f) :
    NSI k (transport h f) := by
  subst h
  exact hf

/-- A constant is non-size-increasing with its own length as constant. -/
theorem nsi_const (n : ℕ) (w : List Bool) : NSI (n := n) w.length (fun _ ↦ w) :=
  fun _ m _ ↦ Nat.le_max_right m _

/-- A projection is non-size-increasing with constant zero. -/
theorem nsi_proj (n : ℕ) (i : Fin n) : NSI 0 (fun x : Fin n → List Bool ↦ x i) :=
  fun _ m hx ↦ Nat.le_trans (hx i) (Nat.le_max_left m 0)

/-- The size-bounded successor is non-size-increasing with constant zero: it
prepends only when the result is no longer than its second argument. -/
theorem nsi_sbs (b : Bool) : NSI 0 (fun x : Fin 2 → List Bool ↦ sbsSem b (x 0) (x 1)) := by
  intro x m hx
  have h0 := hx 0
  have h1 := hx 1
  change (sbsSem b (x 0) (x 1)).length ≤ max m 0
  unfold sbsSem
  split
  · simp only [List.length_cons]
    omega
  · omega

/-- Substitution preserves the property, with the maximum of the constants. -/
theorem nsi_comp {n m kh kg : ℕ} {h : Sem m} {g : Fin m → Sem n} (hh : NSI kh h)
    (hg : ∀ i, NSI kg (g i)) : NSI (max kh kg) (fun x ↦ h (fun i ↦ g i x)) := by
  intro x l hx
  have := hh (fun i ↦ g i x) (max l kg) (fun i ↦ hg i x l hx)
  change (h (fun i ↦ g i x)).length ≤ _
  omega

/-- The environment a step of simultaneous recursion reads: the remaining word,
the recursive values, and the parameters. Named so that its slots can be bounded
one family at a time. -/
@[expose] def stepEnv {a b : ℕ} (v : List Bool) (vals : Fin b → List Bool)
    (x : Fin a → List Bool) : Fin (b + a + 1) → List Bool :=
  Fin.cons v (Fin.append vals x)

/-- Every slot of a step environment is bounded when its three parts are. -/
theorem length_stepEnv_le {a b : ℕ} (v : List Bool) (vals : Fin b → List Bool)
    (x : Fin a → List Bool) (m : ℕ) (hv : v.length ≤ m) (hvals : ∀ l, (vals l).length ≤ m)
    (hx : ∀ i, (x i).length ≤ m) : ∀ s, (stepEnv v vals x s).length ≤ m :=
  Fin.cases hv (fun s ↦
    Fin.addCases (motive := fun s ↦ (stepEnv v vals x s.succ).length ≤ m)
      (fun l ↦ by beta_reduce; unfold stepEnv; rw [Fin.cons_succ, Fin.append_left]; exact hvals l)
      (fun i ↦ by beta_reduce; unfold stepEnv; rw [Fin.cons_succ, Fin.append_right]; exact hx i) s)

/-- Simultaneous recursion on notation preserves the property, with the maximum of
the base and step constants: the bitstring form of \[Mazzanti2016\] Lemma 2.1's
recursion case. The recursion variable is slot zero and the parameters are the
rest, as in {lit}`evalValue`. -/
theorem nsi_srn {a b kg kh : ℕ} {g : Fin b → Sem a} {h : Bool → Fin b → Sem (b + a + 1)}
    (hg : ∀ l, NSI kg (g l)) (hh : ∀ i l, NSI kh (h i l)) (j : Fin b) :
    NSI (max kg kh) (fun x : Fin (a + 1) → List Bool ↦ evalSRN g h (x 0) j (Fin.tail x)) := by
  intro x m hx
  have hy : ∀ i, (Fin.tail x i).length ≤ m := fun i ↦ hx i.succ
  have key : ∀ (w : List Bool), w.length ≤ m →
      ∀ l, (evalSRN g h w l (Fin.tail x)).length ≤ max m (max kg kh) := by
    refine List.rec (fun _ l ↦ ?_) (fun i v ih hw l ↦ ?_)
    · have := hg l (Fin.tail x) m hy
      change (g l (Fin.tail x)).length ≤ _
      omega
    · have hv : v.length ≤ m := by simp only [List.length_cons] at hw; omega
      have hvals : ∀ l, (evalSRN g h v l (Fin.tail x)).length ≤ max m (max kg kh) :=
        ih hv
      have hy' : ∀ i, (Fin.tail x i).length ≤ max m (max kg kh) :=
        fun i ↦ Nat.le_trans (hy i) (Nat.le_max_left _ _)
      have hv' : v.length ≤ max m (max kg kh) := Nat.le_trans hv (Nat.le_max_left _ _)
      have := hh i l (stepEnv v (fun l ↦ evalSRN g h v l (Fin.tail x)) (Fin.tail x))
        (max m (max kg kh)) (length_stepEnv_le _ _ _ _ hv' hvals hy')
      change (h i l (stepEnv v (fun l ↦ evalSRN g h v l (Fin.tail x)) (Fin.tail x))).length ≤ _
      omega
  exact key (x 0) (hx 0) j

/-- The maximum of a finite family, by recursion on its length. -/
@[expose] def finMax : (m : ℕ) → (Fin m → ℕ) → ℕ :=
  Nat.rec (fun _ ↦ 0) fun m ih f ↦ max (ih fun i ↦ f i.castSucc) (f (Fin.last m))

/-- Every member of a finite family is at most its maximum. -/
theorem le_finMax : ∀ (m : ℕ) (f : Fin m → ℕ) (i : Fin m), f i ≤ finMax m f :=
  Nat.rec (fun _ i ↦ i.elim0) fun m ih f i ↦
    Fin.lastCases (motive := fun i ↦ f i ≤ finMax (m + 1) f) (Nat.le_max_right _ _)
      (fun j ↦ Nat.le_trans (ih (fun i ↦ f i.castSucc) j) (Nat.le_max_left _ _)) i

/-- The constant one node contributes, from its children's: a constant its
length, the other base forms nothing, and the operators the maximum of their
children's constants. -/
@[expose] def nsiValue : (a : Shape) → (Direction a → ℕ) → ℕ
  | .const _ w, _ => w.length
  | .proj _ _, _ => 0
  | .sbs _, _ => 0
  | .comp _ m, k => max (k (.inl ())) (finMax m fun i ↦ k (.inr i))
  | .srn _ b _, k =>
      max (finMax b fun l ↦ k (.inl l))
        (max (finMax b fun l ↦ k (.inr (.inl l))) (finMax b fun l ↦ k (.inr (.inr l))))

/-- The constant an expression's meaning is non-size-increasing with, read off
the syntax by folding {lit}`nsiValue` over the tree. -/
@[expose] def nsiConst : sig.toPFunctor.W → ℕ :=
  WType.elim ℕ fun x ↦ nsiValue x.1 x.2

/-- One node's meaning is non-size-increasing with the constant {lit}`nsiValue`
assigns when each child's is with the constant given for it. Each shape's case is
the corresponding closure lemma. -/
theorem nsi_evalValue (a : Shape) (c : Direction a → Σ i, Sem i)
    (h : ∀ b, (c b).1 = rc a b) (k : Direction a → ℕ) (hk : ∀ b, NSI (k b) (c b).2) :
    NSI (nsiValue a k) (evalValue a c h) := by
  cases a with
  | const n w => exact nsi_const n w
  | proj n i => exact nsi_proj n i
  | sbs b => exact nsi_sbs b
  | comp n m =>
    change NSI (max (k (.inl ())) (finMax m fun i ↦ k (.inr i)))
      (fun x : Fin n → List Bool ↦ transport (h (.inl ())) (c (.inl ())).2
        (fun i ↦ transport (h (.inr i)) (c (.inr i)).2 x))
    exact nsi_comp (nsi_transport _ (hk (.inl ())))
      (fun i ↦ nsi_mono (le_finMax m (fun i ↦ k (.inr i)) i) (nsi_transport _ (hk (.inr i))))
  | srn a b j =>
    refine nsi_srn (fun l ↦ nsi_mono (le_finMax b (fun l ↦ k (.inl l)) l)
      (nsi_transport _ (hk (.inl l)))) (fun i l ↦ ?_) j
    cases i
    · exact nsi_mono (Nat.le_trans (le_finMax b (fun l ↦ k (.inr (.inl l))) l)
        (Nat.le_max_left _ _)) (nsi_transport _ (hk (.inr (.inl l))))
    · exact nsi_mono (Nat.le_trans (le_finMax b (fun l ↦ k (.inr (.inr l))) l)
        (Nat.le_max_right _ _)) (nsi_transport _ (hk (.inr (.inr l))))

/-- Every expression denotes a non-size-increasing function, with the constant
{lit}`nsiConst` reads off its syntax: the bitstring form of \[Mazzanti2016\]
Lemma 2.1 for {lit}`S(sbs₀, sbs₁)`. By structural induction on the slice W-type,
each node being {lit}`nsi_evalValue` at its children. -/
theorem nsi_eval : ∀ e : S, NSI (nsiConst e.1) (eval e).2 :=
  SlicePFunctor.W.induction fun x ih ↦ nsi_evalValue x.1.1 (fun b ↦ eval (x.1.2 b)) _ _ ih

/-- The non-size-increase of an expression of a given arity, at that arity. -/
theorem nsi_sem {n : ℕ} (e : SOf n) : NSI (nsiConst e.1.1) e.sem :=
  nsi_transport _ (nsi_eval e.1)

end

end Geb.SizeBounded

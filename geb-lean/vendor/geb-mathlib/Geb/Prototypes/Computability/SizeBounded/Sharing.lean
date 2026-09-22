/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Cost
public import Geb.Mathlib.Data.Vector.OfFn
public import Mathlib.Lean.Thunk

set_option doc.verso true in
/-!
# The evaluator with sharing

An interpretation of the algebra that evaluates each value at most once. The
reference interpretation {name}`Geb.SizeBounded.eval` passes the arguments of
a substitution to its head as a function of the argument index, and returns
the registers of a recursion stage as a function of the register index, so a
head that reads an argument twice evaluates it twice and a step that reads a
register twice evaluates the whole previous stage twice: the time is
exponential in the word's length for a recursion whose steps read several
registers. The interpretation here holds both families in vectors of thunks,
{lit}`evalValueVec` the arguments of a substitution and {lit}`runSRNLazy` the
registers of each stage: a value is computed on its first reference and
retained, and a value never referenced, such as the branch a conditional does
not take, is never computed. Its value is the reference interpretation's, by
{lit}`evalVec_eq`, so it serves evaluation on words longer than a few bits
while every equation of the reference interpretation applies unchanged. What
remains is the cost of the expressions themselves: the tail
{lit}`Geb.SizeBounded.tailOf` is a recursion over its whole argument, so
each derived expression that applies it at every stage of a recursion over
the word costs a further factor of the word's length.

# Main definitions

* {lit}`srnStepLazy`, {lit}`runSRNLazy` — one stage of a recursion and the
  recursion as a fold over the reversed word, each stage's registers held as
  thunks: the iterative recursion of
  {lit}`Geb.Prototypes.Computability.SizeBounded.Iteration` with its vector
  of values replaced by a vector of thunks.
* {lit}`evalValueVec`, {lit}`evalStepVec`, {lit}`evalVec` — the meaning of one
  node, the slice algebra it forms, and the interpretation of a tree, each
  mirroring the reference interpretation's layer.
* {lit}`semVecAt`, {lit}`SOf.semVec` — the meaning of an expression at a given
  arity and of an expression of a given arity.

# Main statements

* {lit}`runSRNLazy_eq` — the fold holds the word and the thunks of the
  recursion's values.
* {lit}`evalValueVec_eq`, {lit}`evalVec_eq` — one node's and a tree's shared
  interpretation is the reference interpretation.
* {lit}`fst_evalVec` — the index component of a tree's interpretation is its
  arity.
* {lit}`SOf.semVec_eq` — the shared meaning of an expression is its meaning.

# Tags

non-size-increasing, simultaneous recursion on notation, evaluator, sharing,
thunk
-/

set_option doc.verso true

namespace Geb.SizeBounded

open Cobham (Sem transport)

public section

/-- One stage of a recursion: the suffix extended by the bit, and each
register's step at the previous stage as a thunk. -/
@[expose] def srnStepLazy {a b : ℕ} (h : Bool → Fin b → Sem (b + a + 1)) (y : Fin a → List Bool)
    (s : List Bool × Vector (Thunk (List Bool)) b) (i : Bool) :
    List Bool × Vector (Thunk (List Bool)) b :=
  (i :: s.1, Vector.ofFnC fun j ↦ Thunk.mk fun _ ↦ h i j (stepEnv s.1 (fun l ↦ (s.2.get l).get) y))

/-- Simultaneous recursion as a fold over the reversed word, each stage's
registers held as thunks. -/
@[expose] def runSRNLazy {a b : ℕ} (g : Fin b → Sem a) (h : Bool → Fin b → Sem (b + a + 1))
    (w : List Bool) (y : Fin a → List Bool) : List Bool × Vector (Thunk (List Bool)) b :=
  w.reverse.foldl (srnStepLazy h y) ([], Vector.ofFnC fun j ↦ Thunk.mk fun _ ↦ g j y)

/-- Extending the word runs one stage after the fold on its tail. -/
theorem runSRNLazy_cons {a b : ℕ} (g : Fin b → Sem a) (h : Bool → Fin b → Sem (b + a + 1))
    (i : Bool) (w : List Bool) (y : Fin a → List Bool) :
    runSRNLazy g h (i :: w) y = srnStepLazy h y (runSRNLazy g h w y) i := by
  simp only [runSRNLazy, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The fold holds the word and the thunks of the recursion's values. -/
theorem runSRNLazy_eq {a b : ℕ} (g : Fin b → Sem a) (h : Bool → Fin b → Sem (b + a + 1))
    (w : List Bool) (y : Fin a → List Bool) :
    runSRNLazy g h w y = (w, Vector.ofFnC fun j ↦ Thunk.mk fun _ ↦ evalSRN g h w j y) := by
  refine List.rec rfl (fun i v ih ↦ ?_) w
  rw [runSRNLazy_cons, ih]
  simp only [srnStepLazy, Vector.get_ofFnC, Thunk.get_mk, evalSRN, stepEnv]

/-- The meaning of one node, evaluating each child at most once: a substitution
holds its arguments as thunks before entering the head, and a recursion is
{lit}`runSRNLazy`. -/
@[expose] def evalValueVec : (a : Shape) → (c : Direction a → Σ i, Sem i) →
    (∀ b, (c b).1 = rc a b) → Sem (q a)
  | .const _ w, _, _ => fun _ ↦ w
  | .proj _ i, _, _ => fun x ↦ x i
  | .sbs b, _, _ => fun x ↦ sbsSem b (x 0) (x 1)
  | .comp _ _, c, h => fun x ↦
      let args := Vector.ofFnC fun i ↦ Thunk.mk fun _ ↦ transport (h (.inr i)) (c (.inr i)).2 x
      transport (h (.inl ())) (c (.inl ())).2 fun i ↦ (args.get i).get
  | .srn _ _ j, c, h => fun x ↦
      ((runSRNLazy (srnBases c h) (srnSteps c h) (x 0) (Fin.tail x)).2.get j).get

/-- {lit}`evalValueVec` as an algebra for {name}`Geb.SizeBounded.sig` in the
slice over {lit}`ℕ`. -/
@[expose] def evalStepVec :
    sig.toSliceDomPFunctor.Obj (Sigma.fst (β := Sem)) → Σ i, Sem i :=
  fun z ↦ ⟨sig.q z.1.1,
    evalValueVec z.1.1 z.1.2
      ((sig.toSliceDomPFunctor.compatible_iff _ z.1.1 z.1.2).mp z.2)⟩

/-- The shared interpretation of a tree. -/
@[expose] def evalVec : sig.W → Σ n, Sem n :=
  SlicePFunctor.W.elim sig (Σ n, Sem n) (Sigma.fst (β := Sem)) evalStepVec rfl

/-- The index component of a tree's shared interpretation is its arity. -/
theorem fst_evalVec (z : S) : (evalVec z).1 = arity z :=
  congrFun
    (SlicePFunctor.W.comp_elim sig (Σ n, Sem n) (Sigma.fst (β := Sem)) evalStepVec rfl) z

/-- The shared meaning of an expression at a given arity. -/
@[expose] def semVecAt (n : ℕ) (e : S) (he : arity e = n) : Sem n :=
  transport ((fst_evalVec e).trans he) (evalVec e).2

/-- The shared meaning of an expression of a given arity. -/
@[expose] def SOf.semVec {n : ℕ} (e : SOf n) : Sem n := semVecAt n e.1 e.2

/-- One node's shared meaning is its meaning: the thunks read back the families
they hold. -/
theorem evalValueVec_eq (a : Shape) (c : Direction a → Σ i, Sem i)
    (h : ∀ b, (c b).1 = rc a b) : evalValueVec a c h = evalValue a c h := by
  cases a with
  | const n w => rfl
  | proj n i => rfl
  | sbs b => rfl
  | comp n m =>
    funext x
    simp only [evalValueVec, evalValue, Vector.get_ofFnC, Thunk.get_mk]
  | srn a b j =>
    funext x
    change ((runSRNLazy (srnBases c h) (srnSteps c h) (x 0) (Fin.tail x)).2.get j).get = _
    rw [runSRNLazy_eq, Vector.get_ofFnC, Thunk.get_mk]
    rfl

/-- The shared interpretation of a tree is its interpretation. -/
theorem evalVec_eq : ∀ e : S, evalVec e = eval e :=
  SlicePFunctor.W.induction fun x ih ↦
    Sigma.ext rfl (heq_of_eq
      ((evalValueVec_eq x.1.1 (fun b ↦ evalVec (x.1.2 b)) _).trans
        (evalValue_congr _ _ _ (funext ih) _ _)))

/-- The shared meaning of an expression is its meaning. -/
theorem SOf.semVec_eq {n : ℕ} (e : SOf n) : e.semVec = e.sem :=
  transport_eq_of_sigma_eq (evalVec_eq e.1) _ _

end

end Geb.SizeBounded

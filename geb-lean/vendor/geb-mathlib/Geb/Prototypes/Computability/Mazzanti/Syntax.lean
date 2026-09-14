/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Mazzanti.Basic
public import Geb.Mathlib.Data.FinEnum
public import Geb.Mathlib.Data.PFunctor.Slice.W
public import Geb.Mathlib.Data.PFunctor.Slice.Decidable
public import Geb.Mathlib.Data.PFunctor.Univariate.Finitary

set_option doc.verso true

/-!
# Syntax of Mazzanti's function algebra

The algebra {lit}`S(sbs₀, sbs₁)` is the closure of constants, projections, and
size-bounded binary successors under substitution and simultaneous recursion on
notation. Its syntax is an arity-indexed polynomial W-type, using the same slice
polynomial machinery as the repository's Cobham algebra.

## Main definitions

* {lit}`Expr` is the type of arity-correct expressions.
* {lit}`wellFormed` checks the arity equations of a raw syntax tree.
* {lit}`Expr.constant`, {lit}`Expr.proj`, {lit}`Expr.succ`, {lit}`Expr.comp`, and
  {lit}`Expr.recursion` construct programs without semantic side conditions.
* {lit}`Expr.eval` evaluates an expression on natural-number arguments.

## Main statements

* {lit}`Expr.nonSizeIncreasing_eval` proves the size invariant for every expression.
* {lit}`Expr.eval_comp` and {lit}`Expr.eval_recursion` identify the closure operators.

## Implementation notes

Admissibility checks only the finite tree's arity equations. In particular, a
recursion node has no bound child and requires no bound proof. Evaluation folds
into a function together with its inferred cutoff and the proof of the size
invariant; these certificates are produced internally, not stored in the syntax.

The simultaneous result vector must be evaluated once per recursion step in a
resource-bounded implementation. These denotational definitions do not claim a
bound on Lean's evaluator, and do not formalize Theorem 5.7's machine characterization.

## References

* \[Mazzanti2016\], Section 2, Lemma 2.1, and Section 5.

## Tags

implicit complexity, function algebra, W-type, non-size-increasing function
-/

@[expose] public section

namespace Geb.Mazzanti

open scoped FinEnum

/-- An interpreted function with its inferred cutoff and size proof. -/
@[ext] structure Certified (n : ℕ) where
  /-- The numerical function. -/
  fn : Sem n
  /-- A fixed cutoff, independent of the arguments. -/
  cutoff : ℕ
  /-- The function preserves bounds above the cutoff. -/
  bounded : Bounded fn cutoff

/-- Interpretation of substitution, inferring the maximum of the child cutoffs. -/
def Certified.comp {a b : ℕ} (h : Certified b) (g : Fin b → Certified a) : Certified a where
  fn x := h.fn (fun i ↦ (g i).fn x)
  cutoff := max h.cutoff (maxValue fun i ↦ (g i).cutoff)
  bounded := bounded_comp (h.bounded.mono (Nat.le_max_left _ _)) fun i ↦
    (g i).bounded.mono ((le_maxValue (fun j ↦ (g j).cutoff) i).trans (Nat.le_max_right _ _))

/-- Interpretation of simultaneous recursion, inferring a common cutoff for every child. -/
def Certified.recursion {a b : ℕ} (g : Fin b → Certified a)
    (h₀ h₁ : Fin b → Certified (a + b + 1)) (j : Fin b) : Certified (a + 1) where
  fn x := simultaneousRec (fun i ↦ (g i).fn)
    (fun bit i ↦ if bit then (h₁ i).fn else (h₀ i).fn) (x 0) (Fin.tail x) j
  cutoff := maxValue fun i ↦ max (g i).cutoff (max (h₀ i).cutoff (h₁ i).cutoff)
  bounded := by
    have hc (i : Fin b) :=
      le_maxValue (fun i ↦ max (g i).cutoff (max (h₀ i).cutoff (h₁ i).cutoff)) i
    have hg (i : Fin b) : (g i).cutoff ≤ maxValue
        (fun i ↦ max (g i).cutoff (max (h₀ i).cutoff (h₁ i).cutoff)) := by
      have h := hc i
      omega
    have hh₀ (i : Fin b) : (h₀ i).cutoff ≤ maxValue
        (fun i ↦ max (g i).cutoff (max (h₀ i).cutoff (h₁ i).cutoff)) := by
      have h := hc i
      omega
    have hh₁ (i : Fin b) : (h₁ i).cutoff ≤ maxValue
        (fun i ↦ max (g i).cutoff (max (h₀ i).cutoff (h₁ i).cutoff)) := by
      have h := hc i
      omega
    apply bounded_simultaneousRec (fun i ↦ (g i).bounded.mono (hg i)) _ j
    intro bit i
    cases bit
    · exact (h₀ i).bounded.mono (hh₀ i)
    · exact (h₁ i).bounded.mono (hh₁ i)

/-- Constructor labels, with arities and a selected simultaneous result component. -/
inductive Shape
  | constant (n value : ℕ)
  | proj (n : ℕ) (i : Fin n)
  | succ (bit : Bool)
  | comp (a b : ℕ)
  | recursion (a b : ℕ) (j : Fin b)
  deriving DecidableEq, Repr

/-- Child positions: the head and arguments of substitution, or bases and both step families. -/
@[reducible] def Direction : Shape → Type
  | .constant _ _ | .proj _ _ | .succ _ => Fin 0
  | .comp _ b => Unit ⊕ Fin b
  | .recursion _ b _ => Fin b ⊕ (Fin b ⊕ Fin b)

/-- The arity required of each child. -/
@[reducible] def childArity : (s : Shape) → Direction s → ℕ
  | .constant _ _, i | .proj _ _, i | .succ _, i => i.elim0
  | .comp _ b, .inl () => b
  | .comp a _, .inr _ => a
  | .recursion a _ _, .inl _ => a
  | .recursion a b _, .inr _ => a + b + 1

/-- The arity produced by a constructor. -/
@[reducible] def resultArity : Shape → ℕ
  | .constant n _ | .proj n _ => n
  | .succ _ => 2
  | .comp a _ => a
  | .recursion a _ _ => a + 1

/-- The arity-indexed polynomial signature of the algebra. -/
def sig : SlicePFunctor ℕ ℕ where
  A := Shape
  B := Direction
  r x := childArity x.1 x.2
  q := resultArity

/-- Every constructor has a constructively enumerable finite set of children. -/
instance sigFinitary : sig.toPFunctor.Finitary
  | .constant _ _ | .proj _ _ | .succ _ => inferInstanceAs (FinEnum (Fin 0))
  | .comp _ b => inferInstanceAs (FinEnum (Unit ⊕ Fin b))
  | .recursion _ b _ => inferInstanceAs (FinEnum (Fin b ⊕ (Fin b ⊕ Fin b)))

/-- Check the arity equations throughout a raw tree, using the generic slice-W validator. -/
def wellFormed (w : sig.toPFunctor.W) : Bool := decide (sig.WValid w)

/-- The executable validator accepts exactly the syntactically admissible trees. -/
@[simp] theorem wellFormed_eq_true (w : sig.toPFunctor.W) :
    wellFormed w = true ↔ sig.WValid w := by simp [wellFormed]

/-- Interpret a constructor from its already-interpreted children. -/
def evalNode : (s : Shape) → ((d : Direction s) → Certified (childArity s d)) →
    Certified (resultArity s)
  | .constant _ value, _ => ⟨fun _ ↦ value, value.size, fun _ h _ _ ↦ h⟩
  | .proj _ i, _ => ⟨fun x ↦ x i, 0, fun _ _ _ h ↦ h i⟩
  | .succ bit, _ => ⟨fun x ↦ sizeBoundedSucc bit (x 0) (x 1), 0,
      fun L _ x h ↦ size_sizeBoundedSucc_le bit (x 0) (x 1) L (h 0) (h 1)⟩
  | .comp _ _, c => (c (.inl ())).comp (fun i ↦ c (.inr i))
  | .recursion _ _ j, c => Certified.recursion (fun i ↦ c (.inl i))
      (fun i ↦ c (.inr (.inl i))) (fun i ↦ c (.inr (.inr i))) j

/-- Transport an interpretation across an arity equality. -/
def transport {a b : ℕ} (h : a = b) (c : Certified a) : Certified b := h ▸ c

/-- The interpreting algebra in the slice over arities. -/
def evalStep : sig.toSliceDomPFunctor.Obj (Sigma.fst (β := Certified)) → Σ n, Certified n :=
  fun z ↦ ⟨resultArity z.1.1, evalNode z.1.1 fun d ↦
    transport (((sig.toSliceDomPFunctor.compatible_iff _ z.1.1 z.1.2).mp z.2) d)
      (z.1.2 d).2⟩

/-- Interpretation of an arity-correct tree, by the slice W-type eliminator. -/
def interpret : sig.W → Σ n, Certified n :=
  SlicePFunctor.W.elim sig (Σ n, Certified n) (Sigma.fst (β := Certified)) evalStep rfl

/-- Interpretation preserves the syntax's arity. -/
theorem fst_interpret (w : sig.W) : (interpret w).1 = sig.wIndex w :=
  congrFun (SlicePFunctor.W.comp_elim sig (Σ n, Certified n)
    (Sigma.fst (β := Certified)) evalStep rfl) w

/-- An expression with a specified arity. The sole admissibility condition is syntactic. -/
def Expr (n : ℕ) := {w : sig.W // sig.wIndex w = n}

namespace Expr

/-- Build an arity-correct node from arity-correct children. -/
def node (s : Shape) (c : (d : Direction s) → Expr (childArity s d)) : Expr (resultArity s) :=
  ⟨⟨WType.mk s (fun d ↦ (c d).1.1), (sig.wValid_mk _ _).mpr
    ⟨fun d ↦ (c d).1.2, funext fun d ↦ (c d).2⟩⟩, rfl⟩

/-- Constant functions are permitted at every arity. -/
def constant (n value : ℕ) : Expr n := node (.constant n value) fun d ↦ d.elim0

/-- Projection onto one argument. -/
def proj (n : ℕ) (i : Fin n) : Expr n := node (.proj n i) fun d ↦ d.elim0

/-- Size-bounded binary successor, with the size bound supplied as ordinary input data. -/
def succ (bit : Bool) : Expr 2 := node (.succ bit) fun d ↦ d.elim0

/-- Substitution of expressions into an expression's argument positions. -/
def comp {a b : ℕ} (h : Expr b) (g : Fin b → Expr a) : Expr a :=
  node (.comp a b) fun d ↦ match d with
    | .inl () => h
    | .inr i => g i

/-- A selected component of simultaneous recursion; no bound expression or proof is required. -/
def recursion {a b : ℕ} (g : Fin b → Expr a)
    (h₀ h₁ : Fin b → Expr (a + b + 1)) (j : Fin b) : Expr (a + 1) :=
  node (.recursion a b j) fun d ↦ match d with
    | .inl i => g i
    | .inr (.inl i) => h₀ i
    | .inr (.inr i) => h₁ i

/-- Evaluate the syntax, inferring a size certificate in the same fold. -/
def certified {n : ℕ} (e : Expr n) : Certified n :=
  transport ((fst_interpret e.1).trans e.2) (interpret e.1).2

/-- The numerical meaning of an expression. -/
def eval {n : ℕ} (e : Expr n) : Sem n := e.certified.fn

/-- Evaluation commutes with the signature's constructor. -/
theorem certified_node (s : Shape) (c : (d : Direction s) → Expr (childArity s d)) :
    (node s c).certified = evalNode s (fun d ↦ (c d).certified) := rfl

/-- Evaluation of a constant. -/
@[simp] theorem eval_constant (n value : ℕ) (x : Fin n → ℕ) :
    (constant n value).eval x = value := rfl

/-- Evaluation of a projection. -/
@[simp] theorem eval_proj (n : ℕ) (i : Fin n) (x : Fin n → ℕ) :
    (proj n i).eval x = x i := rfl

/-- Evaluation of the size-bounded successor primitive. -/
@[simp] theorem eval_succ (bit : Bool) (x : Fin 2 → ℕ) :
    (succ bit).eval x = sizeBoundedSucc bit (x 0) (x 1) := rfl

/-- Evaluation of substitution. -/
@[simp] theorem eval_comp {a b : ℕ} (h : Expr b) (g : Fin b → Expr a) (x : Fin a → ℕ) :
    (comp h g).eval x = h.eval (fun i ↦ (g i).eval x) := rfl

/-- Evaluation of simultaneous recursion. -/
@[simp] theorem eval_recursion {a b : ℕ} (g : Fin b → Expr a)
    (h₀ h₁ : Fin b → Expr (a + b + 1)) (j : Fin b) (x : Fin (a + 1) → ℕ) :
    (recursion g h₀ h₁ j).eval x = simultaneousRec (fun i ↦ (g i).eval)
      (fun bit i ↦ if bit then (h₁ i).eval else (h₀ i).eval) (x 0) (Fin.tail x) j := rfl

/-- Every syntactically well-formed expression is non-size-increasing. No semantic
admissibility hypothesis occurs in this theorem. -/
theorem nonSizeIncreasing_eval {n : ℕ} (e : Expr n) : NonSizeIncreasing e.eval :=
  nonSizeIncreasing_iff.mpr ⟨e.certified.cutoff, e.certified.bounded⟩

/-- A recursion at zero evaluates its selected base expression. -/
theorem eval_recursion_zero {a b : ℕ} (g : Fin b → Expr a)
    (h₀ h₁ : Fin b → Expr (a + b + 1)) (j : Fin b) (y : Fin a → ℕ) :
    (recursion g h₀ h₁ j).eval (Fin.cons 0 y) = (g j).eval y := by
  simp only [eval_recursion, Fin.cons_zero, Fin.tail_cons, simultaneousRec_zero]

/-- The expression-level step equation passes all previous components to one step expression. -/
theorem eval_recursion_bit {a b : ℕ} (g : Fin b → Expr a)
    (h₀ h₁ : Fin b → Expr (a + b + 1)) (j : Fin b) (bit : Bool) (n : ℕ)
    (hn : n = 0 → bit = true) (y : Fin a → ℕ) :
    (recursion g h₀ h₁ j).eval (Fin.cons (Nat.bit bit n) y) =
      (if bit then h₁ j else h₀ j).eval
        (Fin.cons n (Fin.append y (fun i ↦ (recursion g h₀ h₁ i).eval (Fin.cons n y)))) := by
  rw [eval_recursion]
  simp only [Fin.cons_zero, Fin.tail_cons]
  rw [simultaneousRec_bit _ _ bit n hn]
  cases bit <;> rfl

end Expr

end Geb.Mazzanti

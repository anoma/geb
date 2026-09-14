/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Basic

set_option doc.verso true

/-!
# A cost model for the non-size-increasing algebra

An evaluator of the algebra that accounts for its work: with the value of an
expression it returns the time taken and the greatest length of any value read
or produced on the way, and every expression's time is bounded by a polynomial
in the length of its arguments while every length is bounded by that length or
a constant. This is the bitstring form of \[Mazzanti2016\] Lemma 2.2 in the
model of the algebra's own evaluator, which the paper states without proof;
it is not a bound on a machine, and the remaining distance to one is the
compilation of this evaluator into a machine whose step count and cell count
are those accounted for here, the evaluator holding at most a fixed number of
values, one per node of the expression, at any time.

The time of a base form is the length of what it reads and writes; substitution
and recursion add one unit per node visited. The length accounted for is the
greatest among the arguments read, the values produced, and, in a recursion,
every intermediate state. The value component of the account is the meaning
{name}`Geb.SizeBounded.eval` assigns, by {lit}`valueC_eq`.

# Main definitions

* {lit}`finSum` — the sum of a finite family.
* {lit}`Account`, {lit}`SemC`, {lit}`transportC` — an evaluation's value, time
  and greatest length; the meaning of an arity with an account; and transport of
  such a meaning along an equality of arities.
* {lit}`envMax` — the greatest length among the arguments.
* {lit}`evalSRNC`, {lit}`srnBasesC`, {lit}`srnStepsC`, {lit}`evalValueC`,
  {lit}`evalStepC`, {lit}`evalC` — the accounted evaluator, mirroring
  {name}`Geb.SizeBounded.eval` layer by layer.
* {lit}`accountAt`, {lit}`SOf.account` — the account of an expression at a
  given arity.
* {lit}`NSIC` — an accounted meaning is non-size-increasing in value and in
  greatest length, with a given constant.
* {lit}`IsPolyBounded` — a function on lengths is bounded by a polynomial.
* {lit}`timeValue`, {lit}`costData`, {lit}`timePoly` — the polynomial bounding
  an expression's time, read off its syntax together with its
  non-size-increase constant.

# Main statements

* {lit}`valueC_eq`, {lit}`SOf.sem_eq_account` — the accounted evaluator's value
  is the meaning.
* {lit}`nsiC_eval`, {lit}`space_le` — every length the evaluator accounts for
  is at most the argument bound or the expression's constant: linear space.
* {lit}`costData_fst` — the constant the cost fold carries is
  {name}`Geb.SizeBounded.nsiConst`.
* {lit}`time_le`, {lit}`isPolyBounded_timePoly`, {lit}`time_le_poly` — the
  evaluator's time is bounded by the expression's polynomial, which is a
  polynomial: polynomial time.

# Implementation notes

The accounted evaluator is a second slice-W-type fold rather than an
instrumentation of the first, since a fold's carrier is fixed at its
definition; {lit}`valueC_eq` recovers the first from the second. The non-size-
increase of the accounted values is proved again, as {lit}`nsiC_evalValueC`,
because the time bound of a recursion step needs the lengths of the recursive
values at that step, which the identification with {name}`Geb.SizeBounded.eval`
gives only at the root.

The polynomial is carried as a function {lit}`ℕ → ℕ` with a separate proof that
it is bounded by {lit}`c * (m + 1) ^ d`, rather than as a pair of coefficients,
so that the time bound is proved by the same induction as the length bound and
the arithmetic is confined to the closure lemmas of {lit}`IsPolyBounded`. A
recursion's polynomial reads its steps' polynomials at {lit}`max m K`, {lit}`K`
the recursion's own constant, since the recursive values a step reads are
bounded by that rather than by {lit}`m`.

# References

* \[Mazzanti2016\]

# Tags

non-size-increasing, simultaneous recursion on notation, polynomial time, linear
space, cost model
-/

namespace Geb.SizeBounded

open Cobham (Sem transport)

public section

/-- The sum of a finite family, by recursion on its length. -/
@[expose] def finSum : (m : ℕ) → (Fin m → ℕ) → ℕ :=
  Nat.rec (fun _ ↦ 0) fun m ih f ↦ ih (fun i ↦ f i.castSucc) + f (Fin.last m)

/-- A finite sum is monotone in its family. -/
theorem finSum_le_finSum : ∀ (m : ℕ) (f g : Fin m → ℕ), (∀ i, f i ≤ g i) →
    finSum m f ≤ finSum m g :=
  Nat.rec (fun _ _ _ ↦ Nat.le_refl 0) fun m ih f g h ↦
    Nat.add_le_add (ih (fun i ↦ f i.castSucc) (fun i ↦ g i.castSucc) fun i ↦ h i.castSucc)
      (h (Fin.last m))

/-- A finite maximum is at most any common bound. -/
theorem finMax_le : ∀ (m : ℕ) (f : Fin m → ℕ) (K : ℕ), (∀ i, f i ≤ K) → finMax m f ≤ K :=
  Nat.rec (fun _ _ _ ↦ Nat.zero_le _) fun m ih f K h ↦
    Nat.max_le.mpr ⟨ih (fun i ↦ f i.castSucc) K fun i ↦ h i.castSucc, h (Fin.last m)⟩

/-- An evaluation's account: its value, the time taken, and the greatest length
of any value read or produced. -/
@[ext]
structure Account where
  /-- The value computed. -/
  value : List Bool
  /-- The time taken. -/
  time : ℕ
  /-- The greatest length of any value read or produced. -/
  space : ℕ
  deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprAccount.repr

/-- The meaning of an arity with an account. -/
@[expose] def SemC (n : ℕ) : Type := (Fin n → List Bool) → Account

/-- Transport of an accounted meaning along an equality of arities. -/
@[expose] def transportC {i j : ℕ} (h : i = j) (v : SemC i) : SemC j := h ▸ v

/-- A property of accounted meanings at every arity holds of a transport when it
holds of what is transported. -/
theorem transportC_prop {i j : ℕ} (h : i = j) (v : SemC i) (P : ∀ {n : ℕ}, SemC n → Prop)
    (hv : P v) : P (transportC h v) := by
  subst h
  exact hv

/-- The greatest length among the arguments. -/
@[expose] def envMax {n : ℕ} (x : Fin n → List Bool) : ℕ := finMax n fun i ↦ (x i).length

/-- The greatest argument length is at most any common bound. -/
theorem envMax_le {n : ℕ} (x : Fin n → List Bool) (m : ℕ) (hx : ∀ i, (x i).length ≤ m) :
    envMax x ≤ m :=
  finMax_le n _ m hx

/-- Simultaneous recursion on notation with an account. On the empty word each
component's value is its base's, the time is one plus the bases' times and the
length the greatest of theirs; on {lit}`i :: v` the step of each component reads
the environment of the previous stage's values, the time adds one plus the
steps' times to the previous stage's, and the length is the greatest of the
previous stage's and the steps'. -/
@[expose] def evalSRNC {a b : ℕ} (g : Fin b → SemC a) (h : Bool → Fin b → SemC (b + a + 1)) :
    List Bool → Fin b → SemC a :=
  List.rec
    (fun j x ↦ ⟨(g j x).value, 1 + finSum b fun l ↦ (g l x).time, finMax b fun l ↦ (g l x).space⟩)
    (fun i v ih j x ↦
      ⟨(h i j (stepEnv v (fun l ↦ (ih l x).value) x)).value,
        (ih j x).time + 1 +
          finSum b (fun l ↦ (h i l (stepEnv v (fun l ↦ (ih l x).value) x)).time),
        max (ih j x).space
          (finMax b fun l ↦ (h i l (stepEnv v (fun l ↦ (ih l x).value) x)).space)⟩)

/-- The base family a recursion node's children supply, with accounts. -/
@[expose] def srnBasesC {a b : ℕ} {j : Fin b} (c : Direction (.srn a b j) → Σ i, SemC i)
    (h : ∀ d, (c d).1 = rc (.srn a b j) d) : Fin b → SemC a :=
  fun l ↦ transportC (h (.inl l)) (c (.inl l)).2

/-- The step family a recursion node's children supply, with accounts. -/
@[expose] def srnStepsC {a b : ℕ} {j : Fin b} (c : Direction (.srn a b j) → Σ i, SemC i)
    (h : ∀ d, (c d).1 = rc (.srn a b j) d) : Bool → Fin b → SemC (b + a + 1) :=
  fun i l ↦ transportC (h (stepDir i l)) (c (stepDir i l)).2

/-- The accounted meaning of one node. A base form's time is the length of what
it reads and writes plus one, and its greatest length that of its arguments and
its value; a substitution adds one to its arguments' times and its head's, the
head read at the arguments' values; a recursion is {lit}`evalSRNC`. -/
@[expose] def evalValueC : (a : Shape) → (c : Direction a → Σ i, SemC i) →
    (∀ b, (c b).1 = rc a b) → SemC (q a)
  | .const _ w, _, _ => fun x ↦ ⟨w, w.length + 1, max (envMax x) w.length⟩
  | .proj _ i, _, _ => fun x ↦ ⟨x i, (x i).length + 1, envMax x⟩
  | .sbs b, _, _ => fun x ↦
      ⟨sbsSem b (x 0) (x 1), (x 0).length + (x 1).length + 1,
        max (envMax x) (sbsSem b (x 0) (x 1)).length⟩
  | .comp _ m, c, h => fun x ↦
      let gs := fun i ↦ transportC (h (.inr i)) (c (.inr i)).2 x
      let r := transportC (h (.inl ())) (c (.inl ())).2 (fun i ↦ (gs i).value)
      ⟨r.value, 1 + finSum m (fun i ↦ (gs i).time) + r.time,
        max (finMax m fun i ↦ (gs i).space) r.space⟩
  | .srn _ _ j, c, h => fun x ↦ evalSRNC (srnBasesC c h) (srnStepsC c h) (x 0) j (Fin.tail x)

/-- {lit}`evalValueC` as an algebra for {name}`Geb.SizeBounded.sig` in the slice over
{lit}`ℕ`. -/
@[expose] def evalStepC :
    sig.toSliceDomPFunctor.Obj (Sigma.fst (β := SemC)) → Σ i, SemC i :=
  fun z ↦ ⟨sig.q z.1.1,
    evalValueC z.1.1 z.1.2
      ((sig.toSliceDomPFunctor.compatible_iff _ z.1.1 z.1.2).mp z.2)⟩

/-- The accounted interpretation of a tree. -/
@[expose] def evalC : sig.W → Σ n, SemC n :=
  SlicePFunctor.W.elim sig (Σ n, SemC n) (Sigma.fst (β := SemC)) evalStepC rfl

/-- The index component of a tree's accounted interpretation is its arity. -/
theorem fst_evalC (z : S) : (evalC z).1 = arity z :=
  congrFun
    (SlicePFunctor.W.comp_elim sig (Σ n, SemC n) (Sigma.fst (β := SemC)) evalStepC rfl) z

/-- The account of an expression at a given arity. -/
@[expose] def accountAt (n : ℕ) (e : S) (he : arity e = n) : SemC n :=
  transportC ((fst_evalC e).trans he) (evalC e).2

/-- The account of an expression of a given arity. -/
@[expose] def SOf.account {n : ℕ} (e : SOf n) : SemC n := accountAt n e.1 e.2

/-- The value component of an accounted meaning, as a meaning. -/
@[expose] def valueOf {n : ℕ} (f : SemC n) : Sem n := fun x ↦ (f x).value

/-- The value component of a transport is the transport of the value component. -/
theorem valueOf_transportC {i j : ℕ} (h : i = j) (v : SemC i) :
    valueOf (transportC h v) = transport h (valueOf v) := by
  subst h
  rfl

/-- The value component of a transport, applied. -/
theorem value_transportC {i j : ℕ} (h : i = j) (v : SemC i) (x : Fin j → List Bool) :
    (transportC h v x).value = transport h (valueOf v) x :=
  congrFun (valueOf_transportC h v) x

/-- The accounted recursion's values are the recursion's. -/
theorem value_evalSRNC {a b : ℕ} (g : Fin b → SemC a) (h : Bool → Fin b → SemC (b + a + 1)) :
    ∀ (w : List Bool) (j : Fin b) (x : Fin a → List Bool),
      (evalSRNC g h w j x).value =
        evalSRN (fun l ↦ valueOf (g l)) (fun i l ↦ valueOf (h i l)) w j x :=
  List.rec (fun _ _ ↦ rfl) fun i v ih j x ↦ by
    change (h i j (stepEnv v (fun l ↦ (evalSRNC g h v l x).value) x)).value =
      (h i j (stepEnv v (fun l ↦ evalSRN (fun l ↦ valueOf (g l)) (fun i l ↦ valueOf (h i l)) v l x)
        x)).value
    rw [show (fun l ↦ (evalSRNC g h v l x).value) =
      fun l ↦ evalSRN (fun l ↦ valueOf (g l)) (fun i l ↦ valueOf (h i l)) v l x from
      funext fun l ↦ ih l x]

/-- The value component of one accounted node is the node's meaning at its
children's value components. -/
theorem valueOf_evalValueC (a : Shape) (c : Direction a → Σ i, SemC i)
    (h : ∀ b, (c b).1 = rc a b) :
    valueOf (evalValueC a c h) = evalValue a (fun b ↦ ⟨(c b).1, valueOf (c b).2⟩) h := by
  cases a with
  | const n w => rfl
  | proj n i => rfl
  | sbs b => rfl
  | comp n m =>
    funext x
    change (transportC (h (.inl ())) (c (.inl ())).2
      (fun i ↦ (transportC (h (.inr i)) (c (.inr i)).2 x).value)).value = _
    simp only [value_transportC]
    rfl
  | srn a b j =>
    funext x
    change (evalSRNC (srnBasesC c h) (srnStepsC c h) (x 0) j (Fin.tail x)).value = _
    rw [value_evalSRNC]
    exact congrArg₂ (fun G H ↦ evalSRN G H (x 0) j (Fin.tail x))
      (funext fun l ↦ valueOf_transportC _ _)
      (funext fun i ↦ funext fun l ↦ valueOf_transportC _ _)

/-- The meaning of a node depends on its children's meanings alone: the proof of
their arities is immaterial. -/
theorem evalValue_congr (a : Shape) (c c' : Direction a → Σ i, Sem i) (hc : c = c')
    (h : ∀ b, (c b).1 = rc a b) (h' : ∀ b, (c' b).1 = rc a b) :
    evalValue a c h = evalValue a c' h' := by
  subst hc
  rfl

/-- The accounted evaluator's value component is the meaning, as a pair with its
arity. -/
theorem valueC_eq : ∀ e : S, (⟨(evalC e).1, valueOf (evalC e).2⟩ : Σ n, Sem n) = eval e :=
  SlicePFunctor.W.induction fun x ih ↦
    Sigma.ext rfl (heq_of_eq
      ((valueOf_evalValueC x.1.1 (fun b ↦ evalC (x.1.2 b)) _).trans
        (evalValue_congr _ _ _ (funext ih) _ _)))

/-- Two meanings whose pairs with their arities agree are equal once transported
to a common arity. -/
theorem transport_eq_of_sigma_eq {i j k : ℕ} {u : Sem i} {v : Sem j}
    (h : (⟨i, u⟩ : Σ n, Sem n) = ⟨j, v⟩) (hi : i = k) (hj : j = k) :
    transport hi u = transport hj v := by
  cases h
  subst hi
  rfl

/-- The meaning of an expression is the value component of its account. -/
theorem SOf.sem_eq_account {n : ℕ} (e : SOf n) : e.sem = valueOf e.account := by
  change transport _ (eval e.1).2 = valueOf (transportC _ (evalC e.1).2)
  rw [valueOf_transportC]
  exact (transport_eq_of_sigma_eq (valueC_eq e.1) _ _).symm

/-- An accounted meaning is non-size-increasing with constant {lit}`k` in value
and in greatest length: whenever every argument has length at most {lit}`m`,
both are at most {lit}`max m k`. -/
@[expose] def NSIC {n : ℕ} (k : ℕ) (f : SemC n) : Prop :=
  ∀ (x : Fin n → List Bool) (m : ℕ), (∀ i, (x i).length ≤ m) →
    (f x).value.length ≤ max m k ∧ (f x).space ≤ max m k

/-- The property is monotone in its constant. -/
theorem nsiC_mono {n k k' : ℕ} {f : SemC n} (hk : k ≤ k') (hf : NSIC k f) : NSIC k' f :=
  fun x m hx ↦ by
    have := hf x m hx
    exact ⟨by omega, by omega⟩

/-- The property is invariant under transport of the arity. -/
theorem nsiC_transportC {i j k : ℕ} (h : i = j) {f : SemC i} (hf : NSIC k f) :
    NSIC k (transportC h f) :=
  transportC_prop h f (NSIC k) hf

/-- A constant node is non-size-increasing with its length as constant. -/
theorem nsiC_const (n : ℕ) (w : List Bool) :
    NSIC w.length (fun x : Fin n → List Bool ↦
      (⟨w, w.length + 1, max (envMax x) w.length⟩ : Account)) :=
  fun x m hx ↦ ⟨Nat.le_max_right m _, by
    have := envMax_le x m hx
    change max (envMax x) w.length ≤ max m w.length
    omega⟩

/-- A projection node is non-size-increasing with constant zero. -/
theorem nsiC_proj (n : ℕ) (i : Fin n) :
    NSIC 0 (fun x : Fin n → List Bool ↦ (⟨x i, (x i).length + 1, envMax x⟩ : Account)) :=
  fun x m hx ↦ ⟨by have := hx i; change (x i).length ≤ max m 0; omega, by
    have := envMax_le x m hx
    change envMax x ≤ max m 0
    omega⟩

/-- A size-bounded successor node is non-size-increasing with constant zero. -/
theorem nsiC_sbs (b : Bool) :
    NSIC 0 (fun x : Fin 2 → List Bool ↦
      (⟨sbsSem b (x 0) (x 1), (x 0).length + (x 1).length + 1,
        max (envMax x) (sbsSem b (x 0) (x 1)).length⟩ : Account)) := by
  intro x m hx
  have hv := nsi_sbs b x m hx
  have he := envMax_le x m hx
  change (sbsSem b (x 0) (x 1)).length ≤ max m 0 at hv
  exact ⟨hv, by change max (envMax x) (sbsSem b (x 0) (x 1)).length ≤ max m 0; omega⟩

/-- Substitution preserves the property, with the maximum of the constants. -/
theorem nsiC_comp {n m kh kg : ℕ} {h : SemC m} {g : Fin m → SemC n} (hh : NSIC kh h)
    (hg : ∀ i, NSIC kg (g i)) :
    NSIC (max kh kg) (fun x ↦
      (⟨(h (fun i ↦ (g i x).value)).value, 1 + finSum m (fun i ↦ (g i x).time) +
        (h (fun i ↦ (g i x).value)).time,
        max (finMax m fun i ↦ (g i x).space) (h (fun i ↦ (g i x).value)).space⟩ : Account)) := by
  intro x l hx
  have hgs := fun i ↦ hg i x l hx
  have hhs := hh (fun i ↦ (g i x).value) (max l kg) (fun i ↦ (hgs i).1)
  have hsp : finMax m (fun i ↦ (g i x).space) ≤ max l kg := finMax_le m _ _ fun i ↦ (hgs i).2
  refine ⟨?_, ?_⟩
  · change (h (fun i ↦ (g i x).value)).value.length ≤ _
    omega
  · change max (finMax m fun i ↦ (g i x).space) (h (fun i ↦ (g i x).value)).space ≤ _
    omega

/-- Simultaneous recursion on notation preserves the property, with the maximum
of the base and step constants; stated with the recursion's word and parameters
separate, as the time bound consumes it. -/
theorem nsiC_srn_aux {a b kg kh : ℕ} {g : Fin b → SemC a} {h : Bool → Fin b → SemC (b + a + 1)}
    (hg : ∀ l, NSIC kg (g l)) (hh : ∀ i l, NSIC kh (h i l)) (y : Fin a → List Bool) (m : ℕ)
    (hy : ∀ i, (y i).length ≤ m) :
    ∀ (w : List Bool), w.length ≤ m → ∀ l,
      (evalSRNC g h w l y).value.length ≤ max m (max kg kh) ∧
        (evalSRNC g h w l y).space ≤ max m (max kg kh) := by
  refine List.rec (fun _ l ↦ ?_) (fun i v ih hw l ↦ ?_)
  · have hv := fun l ↦ hg l y m hy
    refine ⟨?_, ?_⟩
    · change (g l y).value.length ≤ _
      have := (hv l).1
      omega
    · change finMax b (fun l ↦ (g l y).space) ≤ _
      have := finMax_le b (fun l ↦ (g l y).space) (max m kg) fun l ↦ (hv l).2
      omega
  · have hv : v.length ≤ m := by simp only [List.length_cons] at hw; omega
    have hvals := ih hv
    have hm : m ≤ max m (max kg kh) := Nat.le_max_left _ _
    have henv := length_stepEnv_le v (fun l ↦ (evalSRNC g h v l y).value) y (max m (max kg kh))
      (Nat.le_trans hv hm) (fun l ↦ (hvals l).1) (fun i ↦ Nat.le_trans (hy i) hm)
    have hst := fun l ↦ hh i l (stepEnv v (fun l ↦ (evalSRNC g h v l y).value) y)
      (max m (max kg kh)) henv
    refine ⟨?_, ?_⟩
    · change (h i l (stepEnv v (fun l ↦ (evalSRNC g h v l y).value) y)).value.length ≤ _
      have := (hst l).1
      omega
    · change max (evalSRNC g h v l y).space
        (finMax b fun l ↦ (h i l (stepEnv v (fun l ↦ (evalSRNC g h v l y).value) y)).space) ≤ _
      have h1 := (hvals l).2
      have h2 := finMax_le b _ (max (max m (max kg kh)) kh) fun l ↦ (hst l).2
      omega

/-- Simultaneous recursion on notation preserves the property. -/
theorem nsiC_srn {a b kg kh : ℕ} {g : Fin b → SemC a} {h : Bool → Fin b → SemC (b + a + 1)}
    (hg : ∀ l, NSIC kg (g l)) (hh : ∀ i l, NSIC kh (h i l)) (j : Fin b) :
    NSIC (max kg kh) (fun x : Fin (a + 1) → List Bool ↦ evalSRNC g h (x 0) j (Fin.tail x)) :=
  fun x m hx ↦
    nsiC_srn_aux hg hh (Fin.tail x) m (fun i ↦ hx i.succ) (x 0) (hx 0) j

/-- One accounted node is non-size-increasing with the constant
{name}`Geb.SizeBounded.nsiValue` assigns when each child's is with the constant given
for it. -/
theorem nsiC_evalValueC (a : Shape) (c : Direction a → Σ i, SemC i)
    (h : ∀ b, (c b).1 = rc a b) (k : Direction a → ℕ) (hk : ∀ b, NSIC (k b) (c b).2) :
    NSIC (nsiValue a k) (evalValueC a c h) := by
  cases a with
  | const n w => exact nsiC_const n w
  | proj n i => exact nsiC_proj n i
  | sbs b => exact nsiC_sbs b
  | comp n m =>
    change NSIC (max (k (.inl ())) (finMax m fun i ↦ k (.inr i))) (fun x ↦ _)
    exact nsiC_comp (nsiC_transportC _ (hk (.inl ())))
      (fun i ↦ nsiC_mono (le_finMax m (fun i ↦ k (.inr i)) i) (nsiC_transportC _ (hk (.inr i))))
  | srn a b j =>
    refine nsiC_srn (fun l ↦ nsiC_mono (le_finMax b (fun l ↦ k (.inl l)) l)
      (nsiC_transportC _ (hk (.inl l)))) (fun i l ↦ ?_) j
    cases i
    · exact nsiC_mono (Nat.le_trans (le_finMax b (fun l ↦ k (.inr (.inl l))) l)
        (Nat.le_max_left _ _)) (nsiC_transportC _ (hk (.inr (.inl l))))
    · exact nsiC_mono (Nat.le_trans (le_finMax b (fun l ↦ k (.inr (.inr l))) l)
        (Nat.le_max_right _ _)) (nsiC_transportC _ (hk (.inr (.inr l))))

/-- Every expression's account is non-size-increasing in value and greatest
length, with the constant {name}`Geb.SizeBounded.nsiConst`. -/
theorem nsiC_evalC : ∀ e : S, NSIC (nsiConst e.1) (evalC e).2 :=
  SlicePFunctor.W.induction fun x ih ↦ nsiC_evalValueC x.1.1 (fun b ↦ evalC (x.1.2 b)) _ _ ih

/-- Every length the evaluator accounts for, on arguments of length at most
{lit}`m`, is at most {lit}`max m k` with {lit}`k` the expression's constant:
linear space. -/
theorem space_le {n : ℕ} (e : SOf n) (x : Fin n → List Bool) (m : ℕ)
    (hx : ∀ i, (x i).length ≤ m) : (e.account x).space ≤ max m (nsiConst e.1.1) :=
  (nsiC_transportC _ (nsiC_evalC e.1) x m hx).2

/-- A function on lengths is bounded by a polynomial. -/
@[expose] def IsPolyBounded (p : ℕ → ℕ) : Prop := ∃ c d, ∀ m, p m ≤ c * (m + 1) ^ d

/-- A function below a polynomially bounded one is polynomially bounded. -/
theorem isPolyBounded_of_le {p q : ℕ → ℕ} (h : ∀ m, q m ≤ p m) (hp : IsPolyBounded p) :
    IsPolyBounded q :=
  hp.elim fun c hc ↦ hc.elim fun d hd ↦ ⟨c, d, fun m ↦ Nat.le_trans (h m) (hd m)⟩

/-- A constant is polynomially bounded. -/
theorem isPolyBounded_const (k : ℕ) : IsPolyBounded fun _ ↦ k :=
  ⟨k, 0, fun m ↦ by rw [Nat.pow_zero, Nat.mul_one]⟩

/-- The successor is polynomially bounded. -/
theorem isPolyBounded_succ : IsPolyBounded fun m ↦ m + 1 :=
  ⟨1, 1, fun m ↦ by rw [Nat.pow_one, Nat.one_mul]⟩

/-- A power of the successor is monotone in the exponent. -/
theorem pow_succ_le_pow_succ (m d d' : ℕ) (h : d ≤ d') : (m + 1) ^ d ≤ (m + 1) ^ d' :=
  Nat.pow_le_pow_right (Nat.succ_pos m) h

/-- A sum of polynomially bounded functions is polynomially bounded. -/
theorem isPolyBounded_add {p q : ℕ → ℕ} (hp : IsPolyBounded p) (hq : IsPolyBounded q) :
    IsPolyBounded fun m ↦ p m + q m :=
  hp.elim fun c hc ↦ hc.elim fun d hd ↦ hq.elim fun c' hc' ↦ hc'.elim fun d' hd' ↦
    ⟨c + c', max d d', fun m ↦ by
      have h1 : c * (m + 1) ^ d ≤ c * (m + 1) ^ max d d' :=
        Nat.mul_le_mul_left c (pow_succ_le_pow_succ m d _ (Nat.le_max_left d d'))
      have h2 : c' * (m + 1) ^ d' ≤ c' * (m + 1) ^ max d d' :=
        Nat.mul_le_mul_left c' (pow_succ_le_pow_succ m d' _ (Nat.le_max_right d d'))
      calc p m + q m ≤ c * (m + 1) ^ d + c' * (m + 1) ^ d' := Nat.add_le_add (hd m) (hd' m)
        _ ≤ c * (m + 1) ^ max d d' + c' * (m + 1) ^ max d d' := Nat.add_le_add h1 h2
        _ = (c + c') * (m + 1) ^ max d d' := (Nat.add_mul c c' _).symm⟩

/-- A product of polynomially bounded functions is polynomially bounded. -/
theorem isPolyBounded_mul {p q : ℕ → ℕ} (hp : IsPolyBounded p) (hq : IsPolyBounded q) :
    IsPolyBounded fun m ↦ p m * q m :=
  hp.elim fun c hc ↦ hc.elim fun d hd ↦ hq.elim fun c' hc' ↦ hc'.elim fun d' hd' ↦
    ⟨c * c', d + d', fun m ↦ by
      calc p m * q m ≤ (c * (m + 1) ^ d) * (c' * (m + 1) ^ d') := Nat.mul_le_mul (hd m) (hd' m)
        _ = (c * c') * ((m + 1) ^ d * (m + 1) ^ d') := by
          rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_left_comm ((m + 1) ^ d)]
        _ = (c * c') * (m + 1) ^ (d + d') := by rw [Nat.pow_add]⟩

/-- A finite sum of polynomially bounded functions is polynomially bounded. -/
theorem isPolyBounded_finSum : ∀ (k : ℕ) (p : Fin k → ℕ → ℕ), (∀ i, IsPolyBounded (p i)) →
    IsPolyBounded fun m ↦ finSum k fun i ↦ p i m :=
  Nat.rec (fun _ _ ↦ isPolyBounded_const 0) fun k ih p hp ↦
    isPolyBounded_add (ih (fun i ↦ p i.castSucc) fun i ↦ hp i.castSucc) (hp (Fin.last k))

/-- A shift of the argument to its maximum with a constant preserves polynomial
boundedness. -/
theorem isPolyBounded_shift {p : ℕ → ℕ} (K : ℕ) (hp : IsPolyBounded p) :
    IsPolyBounded fun m ↦ p (max m K) :=
  hp.elim fun c hc ↦ hc.elim fun d hd ↦
    ⟨c * (K + 1) ^ d, d, fun m ↦ by
      have h1 : m + 1 ≤ (K + 1) * (m + 1) := Nat.le_mul_of_pos_left (m + 1) (Nat.succ_pos K)
      have h2 : K + 1 ≤ (K + 1) * (m + 1) := Nat.le_mul_of_pos_right (K + 1) (Nat.succ_pos m)
      have h3 : max m K + 1 ≤ (K + 1) * (m + 1) := by omega
      calc p (max m K) ≤ c * (max m K + 1) ^ d := hd _
        _ ≤ c * ((K + 1) * (m + 1)) ^ d := Nat.mul_le_mul_left c (Nat.pow_le_pow_left h3 d)
        _ = c * (K + 1) ^ d * (m + 1) ^ d := by rw [Nat.mul_pow, Nat.mul_assoc]⟩

/-- The polynomial bounding one node's time, from its children's constants and
polynomials. A base form's is the length it reads and writes; a substitution's
adds its arguments' polynomials to its head's read at the arguments' bound; a
recursion's adds its bases' polynomials to the word's length times its steps',
read at the recursion's own bound, since a step reads the recursive values. -/
@[expose] def timeValue : (a : Shape) → (Direction a → ℕ × (ℕ → ℕ)) → ℕ → ℕ
  | .const _ w, _ => fun _ ↦ w.length + 1
  | .proj _ _, _ => fun m ↦ m + 1
  | .sbs _, _ => fun m ↦ 2 * m + 1
  | .comp _ m', k => fun m ↦
      1 + finSum m' (fun i ↦ (k (.inr i)).2 m) +
        (k (.inl ())).2 (max m (finMax m' fun i ↦ (k (.inr i)).1))
  | .srn a b j, k => fun m ↦
      1 + finSum b (fun l ↦ (k (.inl l)).2 m) +
        m * (1 + finSum b fun l ↦
          (k (.inr (.inl l))).2 (max m (nsiValue (.srn a b j) fun d ↦ (k d).1)) +
            (k (.inr (.inr l))).2 (max m (nsiValue (.srn a b j) fun d ↦ (k d).1)))

/-- The constant and the polynomial of one node, from its children's. -/
@[expose] def costValue (a : Shape) (k : Direction a → ℕ × (ℕ → ℕ)) : ℕ × (ℕ → ℕ) :=
  (nsiValue a fun d ↦ (k d).1, timeValue a k)

/-- The constant and the polynomial of a tree, by folding {lit}`costValue`. -/
@[expose] def costData : sig.toPFunctor.W → ℕ × (ℕ → ℕ) :=
  WType.elim (ℕ × (ℕ → ℕ)) fun x ↦ costValue x.1 x.2

/-- The polynomial of a tree. -/
@[expose] def timePoly (w : sig.toPFunctor.W) : ℕ → ℕ := (costData w).2

/-- The constant the cost fold carries is {name}`Geb.SizeBounded.nsiConst`. -/
theorem costData_fst : ∀ w : sig.toPFunctor.W, (costData w).1 = nsiConst w :=
  WType.rec fun a _ ih ↦ congrArg (nsiValue a) (funext ih)

/-- The time of one accounted node is at most the node's polynomial when each
child's is at most the polynomial given for it and each child is
non-size-increasing with the constant given for it. -/
theorem time_evalValueC (a : Shape) (c : Direction a → Σ i, SemC i)
    (h : ∀ b, (c b).1 = rc a b) (kp : Direction a → ℕ × (ℕ → ℕ))
    (hk : ∀ b, NSIC (kp b).1 (c b).2)
    (hp : ∀ b (x : Fin (c b).1 → List Bool) (m : ℕ), (∀ i, (x i).length ≤ m) →
      ((c b).2 x).time ≤ (kp b).2 m) :
    ∀ (x : Fin (q a) → List Bool) (m : ℕ), (∀ i, (x i).length ≤ m) →
      (evalValueC a c h x).time ≤ timeValue a kp m := by
  cases a with
  | const n w => exact fun _ _ _ ↦ Nat.le_refl _
  | proj n i => exact fun x m hx ↦ Nat.succ_le_succ (hx i)
  | sbs b =>
    intro x m hx
    have h0 := hx 0
    have h1 := hx 1
    change (x 0).length + (x 1).length + 1 ≤ 2 * m + 1
    omega
  | comp n m' =>
    intro x m hx
    have hp' : ∀ b (x : Fin (rc (.comp n m') b) → List Bool) (m : ℕ), (∀ i, (x i).length ≤ m) →
        ((transportC (h b) (c b).2) x).time ≤ (kp b).2 m :=
      fun b ↦ transportC_prop (h b) (c b).2
        (fun f ↦ ∀ (x : Fin _ → List Bool) (m : ℕ), (∀ i, (x i).length ≤ m) →
          (f x).time ≤ (kp b).2 m) (hp b)
    have hk' : ∀ b, NSIC (kp b).1 (transportC (h b) (c b).2) :=
      fun b ↦ nsiC_transportC (h b) (hk b)
    have hgs : ∀ i, (transportC (h (.inr i)) (c (.inr i)).2 x).value.length ≤
        max m (finMax m' fun i ↦ (kp (.inr i)).1) := fun i ↦ by
      have := (hk' (.inr i) x m hx).1
      have := le_finMax m' (fun i ↦ (kp (.inr i)).1) i
      omega
    have hr := hp' (.inl ()) (fun i ↦ (transportC (h (.inr i)) (c (.inr i)).2 x).value) _ hgs
    have hs := finSum_le_finSum m' (fun i ↦ (transportC (h (.inr i)) (c (.inr i)).2 x).time)
      (fun i ↦ (kp (.inr i)).2 m) (fun i ↦ hp' (.inr i) x m hx)
    change 1 + finSum m' (fun i ↦ (transportC (h (.inr i)) (c (.inr i)).2 x).time) +
      (transportC (h (.inl ())) (c (.inl ())).2
        (fun i ↦ (transportC (h (.inr i)) (c (.inr i)).2 x).value)).time ≤
      1 + finSum m' (fun i ↦ (kp (.inr i)).2 m) +
        (kp (.inl ())).2 (max m (finMax m' fun i ↦ (kp (.inr i)).1))
    omega
  | srn a b j =>
    intro x m hx
    have hp' : ∀ d (x : Fin (rc (.srn a b j) d) → List Bool) (m : ℕ), (∀ i, (x i).length ≤ m) →
        ((transportC (h d) (c d).2) x).time ≤ (kp d).2 m :=
      fun d ↦ transportC_prop (h d) (c d).2
        (fun f ↦ ∀ (x : Fin _ → List Bool) (m : ℕ), (∀ i, (x i).length ≤ m) →
          (f x).time ≤ (kp d).2 m) (hp d)
    have hk' : ∀ d, NSIC (kp d).1 (transportC (h d) (c d).2) :=
      fun d ↦ nsiC_transportC (h d) (hk d)
    -- the recursion's constant and the bound on every step's environment
    set K := nsiValue (.srn a b j) fun d ↦ (kp d).1 with hK
    have hkg : ∀ l, (kp (.inl l)).1 ≤ K := fun l ↦ by
      have := le_finMax b (fun l ↦ (kp (.inl l)).1) l
      rw [hK]
      change _ ≤ max (finMax b fun l ↦ (kp (.inl l)).1) _
      omega
    have hkf : ∀ l, (kp (.inr (.inl l))).1 ≤ K := fun l ↦ by
      have := le_finMax b (fun l ↦ (kp (.inr (.inl l))).1) l
      rw [hK]
      change _ ≤ max _ (max (finMax b fun l ↦ (kp (.inr (.inl l))).1) _)
      omega
    have hkt : ∀ l, (kp (.inr (.inr l))).1 ≤ K := fun l ↦ by
      have := le_finMax b (fun l ↦ (kp (.inr (.inr l))).1) l
      rw [hK]
      change _ ≤ max _ (max _ (finMax b fun l ↦ (kp (.inr (.inr l))).1))
      omega
    have hg : ∀ l, NSIC K (srnBasesC c h l) := fun l ↦ nsiC_mono (hkg l) (hk' (.inl l))
    have hh : ∀ i l, NSIC K (srnStepsC c h i l) := fun i l ↦ by
      cases i
      · exact nsiC_mono (hkf l) (hk' (.inr (.inl l)))
      · exact nsiC_mono (hkt l) (hk' (.inr (.inr l)))
    have hy : ∀ i, (Fin.tail x i).length ≤ m := fun i ↦ hx i.succ
    have hvals := nsiC_srn_aux hg hh (Fin.tail x) m hy
    -- the time of every stage
    have key : ∀ (w : List Bool), w.length ≤ m → ∀ l,
        (evalSRNC (srnBasesC c h) (srnStepsC c h) w l (Fin.tail x)).time ≤
          1 + finSum b (fun l ↦ (kp (.inl l)).2 m) +
            w.length * (1 + finSum b fun l ↦
              (kp (.inr (.inl l))).2 (max m K) + (kp (.inr (.inr l))).2 (max m K)) := by
      refine List.rec (fun _ l ↦ ?_) (fun i v ih hw l ↦ ?_)
      · change 1 + finSum b (fun l ↦ (srnBasesC c h l (Fin.tail x)).time) ≤ _
        have := finSum_le_finSum b (fun l ↦ (srnBasesC c h l (Fin.tail x)).time)
          (fun l ↦ (kp (.inl l)).2 m) (fun l ↦ hp' (.inl l) (Fin.tail x) m hy)
        change _ ≤ 1 + finSum b (fun l ↦ (kp (.inl l)).2 m) + 0 * (1 + finSum b fun l ↦
          (kp (.inr (.inl l))).2 (max m K) + (kp (.inr (.inr l))).2 (max m K))
        omega
      · have hv : v.length ≤ m := by simp only [List.length_cons] at hw; omega
        have hvb := hvals v hv
        have hm : m ≤ max m K := Nat.le_max_left _ _
        have henv := length_stepEnv_le v
          (fun l ↦ (evalSRNC (srnBasesC c h) (srnStepsC c h) v l (Fin.tail x)).value)
          (Fin.tail x) (max m K) (Nat.le_trans hv hm)
          (fun l ↦ by beta_reduce; have := (hvb l).1; omega)
          (fun i ↦ Nat.le_trans (hy i) hm)
        have hstep : ∀ l, (srnStepsC c h i l (stepEnv v
            (fun l ↦ (evalSRNC (srnBasesC c h) (srnStepsC c h) v l (Fin.tail x)).value)
            (Fin.tail x))).time ≤
            (kp (.inr (.inl l))).2 (max m K) + (kp (.inr (.inr l))).2 (max m K) := fun l ↦ by
          cases i
          · exact Nat.le_add_right_of_le (hp' (.inr (.inl l)) _ _ henv)
          · exact Nat.le_add_left_of_le (hp' (.inr (.inr l)) _ _ henv)
        have hs := finSum_le_finSum b _ _ hstep
        have hprev := ih hv l
        change (evalSRNC (srnBasesC c h) (srnStepsC c h) v l (Fin.tail x)).time + 1 +
          finSum b (fun l ↦ (srnStepsC c h i l (stepEnv v
            (fun l ↦ (evalSRNC (srnBasesC c h) (srnStepsC c h) v l (Fin.tail x)).value)
            (Fin.tail x))).time) ≤ _
        rw [List.length_cons, Nat.succ_mul]
        omega
    refine Nat.le_trans (key (x 0) (hx 0) j) ?_
    change _ ≤ 1 + finSum b (fun l ↦ (kp (.inl l)).2 m) + m * (1 + finSum b fun l ↦
      (kp (.inr (.inl l))).2 (max m K) + (kp (.inr (.inr l))).2 (max m K))
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (hx 0)) _

/-- Every expression's time is at most its polynomial, on arguments of length at
most {lit}`m`. -/
theorem time_le : ∀ (e : S) (x : Fin (evalC e).1 → List Bool) (m : ℕ),
    (∀ i, (x i).length ≤ m) → ((evalC e).2 x).time ≤ timePoly e.1 m :=
  SlicePFunctor.W.induction fun x ih ↦
    time_evalValueC x.1.1 (fun b ↦ evalC (x.1.2 b)) _ (fun b ↦ costData (x.1.2 b).1)
      (fun b ↦ nsiC_mono (Nat.le_of_eq (costData_fst (x.1.2 b).1).symm) (nsiC_evalC (x.1.2 b)))
      ih

/-- Every expression's polynomial is a polynomial. -/
theorem isPolyBounded_timePoly : ∀ w : sig.toPFunctor.W, IsPolyBounded (timePoly w) :=
  WType.rec (motive := fun w ↦ IsPolyBounded (timePoly w)) fun a f ih ↦ by
    cases a with
    | const n w => exact isPolyBounded_const _
    | proj n i => exact isPolyBounded_succ
    | sbs _ =>
      have hsbs : IsPolyBounded fun m ↦ 2 * m + 1 :=
        isPolyBounded_of_le (p := fun m ↦ (m + 1) + (m + 1))
          (fun m ↦ by beta_reduce; omega)
          (isPolyBounded_add isPolyBounded_succ isPolyBounded_succ)
      exact hsbs
    | comp n m' =>
      exact isPolyBounded_add (isPolyBounded_add (isPolyBounded_const 1)
        (isPolyBounded_finSum m' _ fun i ↦ ih (.inr i)))
        (isPolyBounded_shift _ (ih (.inl ())))
    | srn a b j =>
      refine isPolyBounded_add (isPolyBounded_add (isPolyBounded_const 1)
        (isPolyBounded_finSum b _ fun l ↦ ih (.inl l))) ?_
      refine isPolyBounded_of_le (p := fun m ↦ (m + 1) * _)
        (fun m ↦ Nat.mul_le_mul_right _ (Nat.le_succ m)) (isPolyBounded_mul isPolyBounded_succ ?_)
      exact isPolyBounded_add (isPolyBounded_const 1)
        (isPolyBounded_finSum b _ fun l ↦
          isPolyBounded_add (isPolyBounded_shift _ (ih (.inr (.inl l))))
            (isPolyBounded_shift _ (ih (.inr (.inr l)))))

/-- Every expression's time is bounded by a polynomial in the length of its
arguments: polynomial time. -/
theorem time_le_poly {n : ℕ} (e : SOf n) : ∃ c d, ∀ (x : Fin n → List Bool) (m : ℕ),
    (∀ i, (x i).length ≤ m) → (e.account x).time ≤ c * (m + 1) ^ d :=
  (isPolyBounded_timePoly e.1.1).elim fun c hc ↦ hc.elim fun d hd ↦
    ⟨c, d, fun x m hx ↦ Nat.le_trans
      (transportC_prop _ (evalC e.1).2
        (fun f ↦ ∀ (x : Fin _ → List Bool) (m : ℕ), (∀ i, (x i).length ≤ m) →
          (f x).time ≤ timePoly e.1.1 m) (time_le e.1) x m hx)
      (hd m)⟩

end

end Geb.SizeBounded

/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Basic
public import Mathlib.Data.List.DropRight

set_option doc.verso true in
/-!
# The logarithmic-space representation of values

The machine of \[Kristiansen2005\] Theorem 4.7 holds each register as a
status bit, a word of bounded length and the length of an end segment of the
input in binary. The representation here is the pair of a word and an end
segment length with no status bit: a value {lit}`⟨u, l⟩` denotes the word
{lit}`u` followed by the last {lit}`l` bits of the input. The operations of
the algebra only destruct words, so every value an expression computes on
representations is a constant of the expression, or an end segment of one,
followed by an end segment of the input; the word part stays within the
expression's constant on a successor-free expression, and the length part
within the input's length on every expression.

{lit}`evalRep` interprets an expression on representations, at a fixed input
word, by the same fold as {name}`Geb.SizeBounded.eval`. Simultaneous recursion
on the value {lit}`⟨u, l⟩` runs in two phases: first over the end segment
lengths {lit}`0` to {lit}`l`, the bit peeled at each being read off the input
and the cursor being {lit}`⟨[], l'⟩`; then over the word {lit}`u` from its last
bit, the cursor being {lit}`⟨u', l⟩` for each suffix {lit}`u'` of {lit}`u`. The
size-bounded successor is interpreted too, by the lengths of the denotations,
so that {lit}`den_evalRep` holds of every expression; only the bound on the
word part requires successor-freeness.

# Main definitions

* {lit}`Rep`, {lit}`Rep.den` — a representation and the word it denotes at an
  input.
* {lit}`bitAt` — the bit of the input at the head of its end segment of a
  given length plus one.
* {lit}`RepSem`, {lit}`repTransport` — the meaning of an arity on
  representations, and its transport along an equality of arities.
* {lit}`sbsRep`, {lit}`phaseSuffix`, {lit}`evalSRNRep` — the successor and the
  two phases of simultaneous recursion on representations.
* {lit}`evalRepValue`, {lit}`evalRep`, {lit}`repSemAt`, {lit}`SOf.repSem`,
  {lit}`LOf.repSem` — the fold and the meaning of an expression on
  representations.
* {lit}`ValidAt`, {lit}`Denotes`, {lit}`WordBounded` — a function keeps the
  length part within the input, denotes a function on words, and keeps the
  word part within a constant.

# Main statements

* {lit}`bitAt_eq_getElem`, {lit}`rtake_succ_eq_cons` — the bit at an end
  segment's head as an element of the input, and the end segment one longer
  as that bit consed on.
* {lit}`den_evalSRNRep` — recursion on representations denotes
  {name}`Geb.SizeBounded.evalSRN`.
* {lit}`validAt_evalRep`, {lit}`den_evalRep`, {lit}`wordBounded_evalRep` —
  every expression keeps the length part within the input and denotes its
  meaning; every successor-free expression keeps the word part within its
  constant.
* {lit}`den_repSem`, {lit}`validAt_repSem`, {lit}`wordBounded_repSem` — the
  same for an expression of the subalgebra at its arity.

# References

* \[Kristiansen2005\]

# Tags

logspace, end segment, simultaneous recursion on notation, representation
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace

open Cobham (Sem transport)

public section

/-- A value of the algebra as a word followed by an end segment of the input,
given by its length. -/
@[ext]
structure Rep where
  /-- The word part. -/
  word : List Bool
  /-- The length of the end segment of the input. -/
  suffix : ℕ
  deriving DecidableEq, Repr, Inhabited

attribute [nolint unusedArguments] instReprRep.repr

/-- The word a representation denotes at an input. -/
@[expose] def Rep.den (w : List Bool) (r : Rep) : List Bool := r.word ++ w.rtake r.suffix

/-- A bit consed on the word part is consed on the denotation. -/
theorem Rep.den_cons (w : List Bool) (c : Bool) (u : List Bool) (l : ℕ) :
    Rep.den w ⟨c :: u, l⟩ = c :: Rep.den w ⟨u, l⟩ := rfl

/-- The length of an end segment within the input. -/
theorem length_rtake_of_le (w : List Bool) {l : ℕ} (hl : l ≤ w.length) :
    (w.rtake l).length = l := by
  unfold List.rtake
  rw [List.length_drop]
  omega

/-- The length of a denotation whose end segment is within the input. -/
theorem Rep.length_den (w : List Bool) (r : Rep) (hr : r.suffix ≤ w.length) :
    (r.den w).length = r.word.length + r.suffix := by
  unfold Rep.den
  rw [List.length_append, length_rtake_of_le w hr]

/-- The bit of the input at the head of its end segment of length {lit}`l + 1`. -/
@[expose] def bitAt (w : List Bool) (l : ℕ) : Bool := w.getD (w.length - 1 - l) false

/-- Within the input, the bit at an end segment's head is the element at the
corresponding index. -/
theorem bitAt_eq_getElem (w : List Bool) {l : ℕ} (hl : l < w.length) :
    bitAt w l = w[w.length - 1 - l]'(by omega) := by
  unfold bitAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- The end segment one longer is the bit at its head consed on. -/
theorem rtake_succ_eq_cons (w : List Bool) {l : ℕ} (hl : l < w.length) :
    w.rtake (l + 1) = bitAt w l :: w.rtake l := by
  unfold List.rtake bitAt
  have h1 : w.length - (l + 1) + 1 = w.length - l := by omega
  have h2 : w.length - 1 - l = w.length - (l + 1) := by omega
  rw [List.drop_eq_getElem_cons (by omega), h1, h2, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- The meaning of an arity on representations. -/
@[expose] def RepSem (n : ℕ) : Type := (Fin n → Rep) → Rep

/-- Transport of a meaning along an equality of arities. -/
@[expose] def repTransport {i j : ℕ} (h : i = j) (f : RepSem i) : RepSem j := h ▸ f

/-- Transport composes. -/
theorem repTransport_repTransport {i j l : ℕ} (h : i = j) (g : j = l) (f : RepSem i) :
    repTransport g (repTransport h f) = repTransport (h.trans g) f := by
  subst h
  subst g
  rfl

/-- The size-bounded successor on representations, by the lengths of the
denotations. -/
@[expose] def sbsRep (w : List Bool) (b : Bool) (x y : Rep) : Rep :=
  if (x.den w).length + 1 ≤ (y.den w).length then ⟨b :: x.word, x.suffix⟩ else x

/-- The successor on representations denotes {name}`Geb.SizeBounded.sbsSem`. -/
theorem den_sbsRep (w : List Bool) (b : Bool) (x y : Rep) :
    (sbsRep w b x y).den w = sbsSem b (x.den w) (y.den w) := by
  unfold sbsRep sbsSem
  by_cases h : (x.den w).length + 1 ≤ (y.den w).length
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]

/-- The environment a step of recursion on representations reads: the cursor,
the recursive values and the parameters. -/
@[expose] def stepEnvRep {a b : ℕ} (r : Rep) (v : Fin b → Rep) (x : Fin a → Rep) :
    Fin (b + a + 1) → Rep :=
  Fin.cons r (Fin.append v x)

/-- The first phase of recursion on representations: over the end segment
lengths, the bit peeled at length {lit}`l` being {name}`bitAt` and the cursor
{lit}`⟨[], l⟩`. -/
@[expose] def phaseSuffix (w : List Bool) {a b : ℕ} (g : Fin b → RepSem a)
    (h : Bool → Fin b → RepSem (b + a + 1)) : ℕ → Fin b → RepSem a :=
  Nat.rec g fun l ih j x ↦ h (bitAt w l) j (stepEnvRep ⟨[], l⟩ (fun l' ↦ ih l' x) x)

/-- Simultaneous recursion on representations: the first phase over the end
segment lengths up to the value's, then the second over the value's word from
its last bit, the cursor {lit}`⟨u', l⟩` for each suffix {lit}`u'`. -/
@[expose] def evalSRNRep (w : List Bool) {a b : ℕ} (g : Fin b → RepSem a)
    (h : Bool → Fin b → RepSem (b + a + 1)) : Rep → Fin b → RepSem a :=
  fun y ↦ List.rec (phaseSuffix w g h y.suffix)
    (fun c u ih j x ↦ h c j (stepEnvRep ⟨u, y.suffix⟩ (fun l ↦ ih l x) x)) y.word

/-- The denotation of a step environment on representations is the step
environment of the denotations. -/
theorem den_stepEnvRep (w : List Bool) {a b : ℕ} (r : Rep) (v : Fin b → Rep)
    (x : Fin a → Rep) :
    (fun s ↦ (stepEnvRep r v x s).den w) =
      stepEnv (r.den w) (fun l ↦ (v l).den w) (fun i ↦ (x i).den w) := by
  funext s
  refine Fin.cases rfl (fun s ↦ ?_) s
  refine Fin.addCases (motive := fun s ↦ (stepEnvRep r v x s.succ).den w =
    stepEnv (r.den w) (fun l ↦ (v l).den w) (fun i ↦ (x i).den w) s.succ) (fun l ↦ ?_)
    (fun i ↦ ?_) s
  · beta_reduce; unfold stepEnvRep stepEnv
    rw [Fin.cons_succ, Fin.cons_succ, Fin.append_left, Fin.append_left]
  · beta_reduce; unfold stepEnvRep stepEnv
    rw [Fin.cons_succ, Fin.cons_succ, Fin.append_right, Fin.append_right]

/-- A function on representations keeps the length part within {lit}`n`. -/
@[expose] def ValidAt (n : ℕ) {m : ℕ} (f : RepSem m) : Prop :=
  ∀ x : Fin m → Rep, (∀ i, (x i).suffix ≤ n) → (f x).suffix ≤ n

/-- A function on representations denotes a function on words at the input
{lit}`w`, on environments within the input. -/
@[expose] def Denotes (w : List Bool) {m : ℕ} (f : RepSem m) (f' : Sem m) : Prop :=
  ∀ x : Fin m → Rep, (∀ i, (x i).suffix ≤ w.length) → (f x).den w = f' fun i ↦ (x i).den w

/-- A function on representations keeps the word part within the bound on the
environment's or the constant {lit}`k`. -/
@[expose] def WordBounded (k : ℕ) {m : ℕ} (f : RepSem m) : Prop :=
  ∀ (x : Fin m → Rep) (M : ℕ), (∀ i, (x i).word.length ≤ M) → (f x).word.length ≤ max M k

/-- Validity transports along an equality of arities. -/
theorem validAt_transport {n i j : ℕ} (h : i = j) {f : RepSem i} (hf : ValidAt n f) :
    ValidAt n (repTransport h f) := by
  subst h
  exact hf

/-- Denotation transports along an equality of arities. -/
theorem denotes_transport {w : List Bool} {i j : ℕ} (h : i = j) {f : RepSem i} {f' : Sem i}
    (hf : Denotes w f f') : Denotes w (repTransport h f) (transport h f') := by
  subst h
  exact hf

/-- The word bound transports along an equality of arities. -/
theorem wordBounded_transport {k i j : ℕ} (h : i = j) {f : RepSem i} (hf : WordBounded k f) :
    WordBounded k (repTransport h f) := by
  subst h
  exact hf

/-- The word bound is monotone in its constant. -/
theorem wordBounded_mono {k k' m : ℕ} {f : RepSem m} (hk : k ≤ k') (hf : WordBounded k f) :
    WordBounded k' f :=
  fun x M hx ↦ by
    have := hf x M hx
    omega

/-- Every slot of a step environment on representations satisfies a predicate
when its three parts do. -/
theorem stepEnvRep_prop {P : Rep → Prop} {a b : ℕ} (r : Rep) (v : Fin b → Rep) (x : Fin a → Rep)
    (hr : P r) (hv : ∀ l, P (v l)) (hx : ∀ i, P (x i)) : ∀ s, P (stepEnvRep r v x s) :=
  Fin.cases hr (fun s ↦
    Fin.addCases (motive := fun s ↦ P (stepEnvRep r v x s.succ))
      (fun l ↦ by
        beta_reduce; unfold stepEnvRep; rw [Fin.cons_succ, Fin.append_left]; exact hv l)
      (fun i ↦ by
        beta_reduce; unfold stepEnvRep; rw [Fin.cons_succ, Fin.append_right]; exact hx i) s)

/-- The first phase keeps the length part within the input when its bases and
steps do, up to the input's length. -/
theorem validAt_phaseSuffix {n : ℕ} {a b : ℕ} {g : Fin b → RepSem a}
    {h : Bool → Fin b → RepSem (b + a + 1)} (hg : ∀ l, ValidAt n (g l))
    (hh : ∀ i l, ValidAt n (h i l)) (w : List Bool) (x : Fin a → Rep) (hx : ∀ i, (x i).suffix ≤ n) :
    ∀ l, l ≤ n → ∀ j, (phaseSuffix w g h l j x).suffix ≤ n := by
  refine Nat.rec (fun _ j ↦ hg j x hx) (fun l ih hl j ↦ ?_)
  exact hh _ j _ (stepEnvRep_prop (P := fun r ↦ r.suffix ≤ n) _ _ _ (by change l ≤ n; omega)
    (ih (by omega)) hx)

/-- Recursion on representations keeps the length part within the input when its
bases and steps do. -/
theorem validAt_evalSRNRep {n : ℕ} {a b : ℕ} {g : Fin b → RepSem a}
    {h : Bool → Fin b → RepSem (b + a + 1)} (hg : ∀ l, ValidAt n (g l))
    (hh : ∀ i l, ValidAt n (h i l)) (w : List Bool) (j : Fin b) :
    ValidAt n (fun x : Fin (a + 1) → Rep ↦ evalSRNRep w g h (x 0) j (Fin.tail x)) := by
  intro x hx
  have hy : ∀ i, (Fin.tail x i).suffix ≤ n := fun i ↦ hx i.succ
  have key : ∀ (u : List Bool) (l : ℕ), l ≤ n →
      ∀ j, (evalSRNRep w g h ⟨u, l⟩ j (Fin.tail x)).suffix ≤ n := by
    refine List.rec (fun l hl j ↦ validAt_phaseSuffix hg hh w _ hy l hl j) (fun c u ih l hl j ↦ ?_)
    exact hh c j _ (stepEnvRep_prop (P := fun r ↦ r.suffix ≤ n) _ _ _ hl (ih l hl) hy)
  exact key (x 0).word (x 0).suffix (hx 0) j

/-- The first phase denotes {name}`Geb.SizeBounded.evalSRN` at the end segment of
the input of each length, when its bases and steps denote the recursion's and
keep the length part within the input. -/
theorem den_phaseSuffix {w : List Bool} {a b : ℕ} {g : Fin b → RepSem a}
    {h : Bool → Fin b → RepSem (b + a + 1)} {g' : Fin b → Sem a}
    {h' : Bool → Fin b → Sem (b + a + 1)} (hgv : ∀ l, ValidAt w.length (g l))
    (hhv : ∀ i l, ValidAt w.length (h i l)) (hg : ∀ l, Denotes w (g l) (g' l))
    (hh : ∀ i l, Denotes w (h i l) (h' i l)) (x : Fin a → Rep)
    (hx : ∀ i, (x i).suffix ≤ w.length) :
    ∀ l, l ≤ w.length → ∀ j,
      (phaseSuffix w g h l j x).den w = evalSRN g' h' (w.rtake l) j fun i ↦ (x i).den w := by
  refine Nat.rec (fun _ j ↦ ?_) (fun l ih hl j ↦ ?_)
  · rw [List.rtake_zero]
    exact hg j x hx
  · rw [rtake_succ_eq_cons w hl]
    change (h (bitAt w l) j (stepEnvRep ⟨[], l⟩ (fun l' ↦ phaseSuffix w g h l l' x) x)).den w =
      h' (bitAt w l) j (stepEnv (w.rtake l)
        (fun l' ↦ evalSRN g' h' (w.rtake l) l' fun i ↦ (x i).den w) fun i ↦ (x i).den w)
    rw [hh _ j _ (stepEnvRep_prop (P := fun r ↦ r.suffix ≤ w.length) _ _ _ (by change l ≤ _; omega)
      (validAt_phaseSuffix hgv hhv w x hx l (by omega)) hx), den_stepEnvRep]
    congr 1
    refine congrArg₂ (fun v vals ↦ stepEnv v vals fun i ↦ (x i).den w) ?_ (funext fun l' ↦ ?_)
    · change [] ++ w.rtake l = w.rtake l
      rfl
    · exact ih (by omega) l'

/-- Recursion on representations denotes {name}`Geb.SizeBounded.evalSRN` when its
bases and steps denote the recursion's and keep the length part within the
input. -/
theorem den_evalSRNRep {w : List Bool} {a b : ℕ} {g : Fin b → RepSem a}
    {h : Bool → Fin b → RepSem (b + a + 1)} {g' : Fin b → Sem a}
    {h' : Bool → Fin b → Sem (b + a + 1)} (hgv : ∀ l, ValidAt w.length (g l))
    (hhv : ∀ i l, ValidAt w.length (h i l)) (hg : ∀ l, Denotes w (g l) (g' l))
    (hh : ∀ i l, Denotes w (h i l) (h' i l)) (j : Fin b) :
    Denotes w (fun x : Fin (a + 1) → Rep ↦ evalSRNRep w g h (x 0) j (Fin.tail x))
      (fun x : Fin (a + 1) → List Bool ↦ evalSRN g' h' (x 0) j (Fin.tail x)) := by
  intro x hx
  have hy : ∀ i, (Fin.tail x i).suffix ≤ w.length := fun i ↦ hx i.succ
  have key : ∀ (u : List Bool) (l : ℕ), l ≤ w.length → ∀ j,
      (evalSRNRep w g h ⟨u, l⟩ j (Fin.tail x)).den w =
        evalSRN g' h' (Rep.den w ⟨u, l⟩) j fun i ↦ (Fin.tail x i).den w := by
    refine List.rec (fun l hl j ↦ den_phaseSuffix hgv hhv hg hh _ hy l hl j)
      (fun c u ih l hl j ↦ ?_)
    rw [Rep.den_cons]
    change (h c j (stepEnvRep ⟨u, l⟩ (fun l' ↦ evalSRNRep w g h ⟨u, l⟩ l' (Fin.tail x))
      (Fin.tail x))).den w = h' c j (stepEnv (Rep.den w ⟨u, l⟩)
        (fun l' ↦ evalSRN g' h' (Rep.den w ⟨u, l⟩) l' fun i ↦ (Fin.tail x i).den w)
        fun i ↦ (Fin.tail x i).den w)
    have hvals : ∀ l', (evalSRNRep w g h ⟨u, l⟩ l' (Fin.tail x)).suffix ≤ w.length :=
      fun l' ↦ validAt_evalSRNRep hgv hhv w l' (Fin.cons ⟨u, l⟩ (Fin.tail x)) (Fin.cases hl hy)
    rw [hh c j _ (stepEnvRep_prop (P := fun r ↦ r.suffix ≤ w.length) _ _ _ hl hvals hy),
      den_stepEnvRep]
    congr 1
    exact congrArg (fun vals ↦ stepEnv (Rep.den w ⟨u, l⟩) vals fun i ↦ (Fin.tail x i).den w)
      (funext fun l' ↦ ih l hl l')
  exact key (x 0).word (x 0).suffix (hx 0) j

/-- The second phase keeps the word part within a bound its steps keep and the
value's word is within. -/
theorem wordBounded_evalSRNRep {k : ℕ} {a b : ℕ} {g : Fin b → RepSem a}
    {h : Bool → Fin b → RepSem (b + a + 1)} (hg : ∀ l, WordBounded k (g l))
    (hh : ∀ i l, WordBounded k (h i l)) (w : List Bool) (j : Fin b) :
    WordBounded k (fun x : Fin (a + 1) → Rep ↦ evalSRNRep w g h (x 0) j (Fin.tail x)) := by
  intro x M hx
  have hy : ∀ i, (Fin.tail x i).word.length ≤ M := fun i ↦ hx i.succ
  have hy' : ∀ i, (Fin.tail x i).word.length ≤ max M k :=
    fun i ↦ Nat.le_trans (hy i) (Nat.le_max_left _ _)
  have h1 : ∀ l j, (phaseSuffix w g h l j (Fin.tail x)).word.length ≤ max M k := by
    refine Nat.rec (fun j ↦ hg j _ M hy) (fun l ih j ↦ ?_)
    have := hh (bitAt w l) j _ (max M k) (stepEnvRep_prop (P := fun r ↦ r.word.length ≤ max M k)
      ⟨[], l⟩ _ _ (Nat.zero_le _) ih hy')
    change (h (bitAt w l) j (stepEnvRep ⟨[], l⟩ (fun l' ↦ phaseSuffix w g h l l' (Fin.tail x))
      (Fin.tail x))).word.length ≤ max M k
    omega
  have key : ∀ (u : List Bool) (l : ℕ), u.length ≤ M →
      ∀ j, (evalSRNRep w g h ⟨u, l⟩ j (Fin.tail x)).word.length ≤ max M k := by
    refine List.rec (fun l _ j ↦ h1 l j) (fun c u ih l hu j ↦ ?_)
    have hu' : u.length ≤ M := by rw [List.length_cons] at hu; omega
    have := hh c j _ (max M k) (stepEnvRep_prop (P := fun r ↦ r.word.length ≤ max M k) ⟨u, l⟩ _ _
      (Nat.le_trans hu' (Nat.le_max_left _ _)) (ih l hu') hy')
    change (h c j (stepEnvRep ⟨u, l⟩ (fun l' ↦ evalSRNRep w g h ⟨u, l⟩ l' (Fin.tail x))
      (Fin.tail x))).word.length ≤ max M k
    omega
  exact key (x 0).word (x 0).suffix (hx 0) j

/-- The base family a recursion node's children supply, at the arity
{name}`Geb.SizeBounded.rc` prescribes. -/
@[expose] def srnBasesRep {a b : ℕ} {j : Fin b} (c : Direction (.srn a b j) → Σ i, RepSem i)
    (h : ∀ d, (c d).1 = rc (.srn a b j) d) : Fin b → RepSem a :=
  fun l ↦ repTransport (h (.inl l)) (c (.inl l)).2

/-- The step family a recursion node's children supply, at the arity
{name}`Geb.SizeBounded.rc` prescribes. -/
@[expose] def srnStepsRep {a b : ℕ} {j : Fin b} (c : Direction (.srn a b j) → Σ i, RepSem i)
    (h : ∀ d, (c d).1 = rc (.srn a b j) d) : Bool → Fin b → RepSem (b + a + 1) :=
  fun i l ↦ repTransport (h (stepDir i l)) (c (stepDir i l)).2

/-- The meaning of one node on representations, from its children's. -/
@[expose] def evalRepValue (w : List Bool) : (a : Shape) → (c : Direction a → Σ i, RepSem i) →
    (∀ b, (c b).1 = rc a b) → RepSem (q a)
  | .const _ v, _, _ => fun _ ↦ ⟨v, 0⟩
  | .proj _ i, _, _ => fun x ↦ x i
  | .sbs b, _, _ => fun x ↦ sbsRep w b (x 0) (x 1)
  | .comp _ _, c, h => fun x ↦
      repTransport (h (.inl ())) (c (.inl ())).2
        (fun i ↦ repTransport (h (.inr i)) (c (.inr i)).2 x)
  | .srn _ _ j, c, h => fun x ↦
      evalSRNRep w (srnBasesRep c h) (srnStepsRep c h) (x 0) j (Fin.tail x)

/-- {name}`evalRepValue` as an algebra for {name}`Geb.SizeBounded.sig` in the
slice over {lit}`ℕ`. -/
@[expose] def evalRepStep (w : List Bool) :
    sig.toSliceDomPFunctor.Obj (Sigma.fst (β := RepSem)) → Σ i, RepSem i :=
  fun z ↦ ⟨sig.q z.1.1,
    evalRepValue w z.1.1 z.1.2
      ((sig.toSliceDomPFunctor.compatible_iff _ z.1.1 z.1.2).mp z.2)⟩

/-- The interpretation of a tree on representations at an input: its arity
together with its meaning at that arity. -/
@[expose] def evalRep (w : List Bool) : sig.W → Σ n, RepSem n :=
  SlicePFunctor.W.elim sig (Σ n, RepSem n) (Sigma.fst (β := RepSem)) (evalRepStep w) rfl

/-- The index component of a tree's interpretation on representations is its
arity. -/
theorem fst_evalRep (w : List Bool) (z : S) : (evalRep w z).1 = arity z :=
  congrFun (SlicePFunctor.W.comp_elim sig (Σ n, RepSem n) (Sigma.fst (β := RepSem))
    (evalRepStep w) rfl) z

/-- The meaning of an expression on representations at a given arity. -/
@[expose] def repSemAt (w : List Bool) (n : ℕ) (e : S) (he : arity e = n) : RepSem n :=
  repTransport ((fst_evalRep w e).trans he) (evalRep w e).2

/-- The meaning of an expression of a given arity on representations. -/
@[expose] def SOf.repSem (w : List Bool) {n : ℕ} (e : SOf n) : RepSem n := repSemAt w n e.1 e.2

/-- The meaning of an expression of the subalgebra on representations. -/
@[expose] def LOf.repSem (w : List Bool) {n : ℕ} (e : LOf n) : RepSem n := SOf.repSem w e.1

/-- Denotation of an indexed pair, the indices agreeing. -/
@[expose] def DenotesSigma (w : List Bool) (p : Σ i, RepSem i) (m : Σ i, Sem i) : Prop :=
  ∃ h : p.1 = m.1, Denotes w (repTransport h p.2) m.2

/-- A child's denotation at the arity its parent prescribes. -/
theorem DenotesSigma.atArity {w : List Bool} {p : Σ i, RepSem i} {m : Σ i, Sem i}
    (hk : DenotesSigma w p m) {n : ℕ} (h : p.1 = n) (hm : m.1 = n) :
    Denotes w (repTransport h p.2) (transport hm m.2) := by
  obtain ⟨e, hc⟩ := hk
  have hc' := denotes_transport hm hc
  rw [repTransport_repTransport] at hc'
  exact hc'

/-- One node keeps the length part within the input when its children do. -/
theorem validAt_evalRepValue (w : List Bool) (a : Shape) (c : Direction a → Σ i, RepSem i)
    (h : ∀ b, (c b).1 = rc a b) (hc : ∀ b, ValidAt w.length (c b).2) :
    ValidAt w.length (evalRepValue w a c h) := by
  cases a with
  | const n v => exact fun _ _ ↦ Nat.zero_le _
  | proj n i => exact fun x hx ↦ hx i
  | sbs b =>
    intro x hx
    change (sbsRep w b (x 0) (x 1)).suffix ≤ _
    unfold sbsRep
    split
    · exact hx 0
    · exact hx 0
  | comp n m =>
    intro x hx
    exact validAt_transport _ (hc _) _ fun i ↦ validAt_transport _ (hc _) _ hx
  | srn a b j =>
    exact validAt_evalSRNRep (fun l ↦ validAt_transport _ (hc _))
      (fun i l ↦ validAt_transport _ (hc _)) w j

/-- Every expression keeps the length part within the input. -/
theorem validAt_evalRep (w : List Bool) : ∀ e : S, ValidAt w.length (evalRep w e).2 :=
  SlicePFunctor.W.induction fun x ih ↦
    validAt_evalRepValue w x.1.1 (fun b ↦ evalRep w (x.1.2 b)) _ ih

/-- One node denotes its meaning when its children do and keep the length part
within the input. -/
theorem den_evalRepValue (w : List Bool) (a : Shape) (c : Direction a → Σ i, RepSem i)
    (h : ∀ b, (c b).1 = rc a b) (s : Direction a → Σ i, Sem i) (hs : ∀ b, (s b).1 = rc a b)
    (hv : ∀ b, ValidAt w.length (c b).2) (hk : ∀ b, DenotesSigma w (c b) (s b)) :
    Denotes w (evalRepValue w a c h) (evalValue a s hs) := by
  cases a with
  | const n v =>
    intro x _
    change v ++ w.rtake 0 = v
    rw [List.rtake_zero, List.append_nil]
  | proj n i => exact fun x _ ↦ rfl
  | sbs b => exact fun x _ ↦ den_sbsRep w b (x 0) (x 1)
  | comp n m =>
    intro x hx
    change (repTransport (h (.inl ())) (c (.inl ())).2
      (fun i ↦ repTransport (h (.inr i)) (c (.inr i)).2 x)).den w =
      transport (hs (.inl ())) (s (.inl ())).2
        (fun i ↦ transport (hs (.inr i)) (s (.inr i)).2 fun i ↦ (x i).den w)
    rw [(hk (.inl ())).atArity (h _) (hs _) _
      fun i ↦ validAt_transport _ (hv _) _ hx]
    exact congrArg _ (funext fun i ↦ (hk (.inr i)).atArity (h _) (hs _) x hx)
  | srn a b j =>
    exact den_evalSRNRep (fun l ↦ validAt_transport _ (hv _)) (fun i l ↦ validAt_transport _ (hv _))
      (fun l ↦ (hk (.inl l)).atArity (h _) (hs _))
      (fun i l ↦ (hk (stepDir i l)).atArity (h _) (hs _)) j

/-- Every expression denotes its meaning on representations. -/
theorem den_evalRep (w : List Bool) : ∀ e : S, DenotesSigma w (evalRep w e) (eval e) :=
  SlicePFunctor.W.induction fun x ih ↦
    ⟨rfl, den_evalRepValue w x.1.1 (fun b ↦ evalRep w (x.1.2 b)) _ (fun b ↦ eval (x.1.2 b)) _
      (fun b ↦ validAt_evalRep w (x.1.2 b)) ih⟩

/-- One successor-free node keeps the word part within the constant
{name}`Geb.SizeBounded.nsiValue` assigns when each child keeps it within the
constant given for it. -/
theorem wordBounded_evalRepValue (w : List Bool) (a : Shape) (c : Direction a → Σ i, RepSem i)
    (h : ∀ b, (c b).1 = rc a b) (kb : Direction a → Bool) (hkb : sbsFreeValue a kb = true)
    (k : Direction a → ℕ) (hk : ∀ b, kb b = true → WordBounded (k b) (c b).2) :
    WordBounded (nsiValue a k) (evalRepValue w a c h) := by
  cases a with
  | const n v => exact fun _ M _ ↦ Nat.le_max_right M _
  | proj n i => exact fun x M hx ↦ Nat.le_trans (hx i) (Nat.le_max_left M 0)
  | sbs b => exact absurd hkb Bool.false_ne_true
  | comp n m =>
    change (kb (.inl ()) && finAll m fun i ↦ kb (.inr i)) = true at hkb
    rw [Bool.and_eq_true, finAll_eq_true_iff] at hkb
    intro x M hx
    change (repTransport (h (.inl ())) (c (.inl ())).2
      (fun i ↦ repTransport (h (.inr i)) (c (.inr i)).2 x)).word.length ≤
      max M (max (k (.inl ())) (finMax m fun i ↦ k (.inr i)))
    have hargs : ∀ i, (repTransport (h (.inr i)) (c (.inr i)).2 x).word.length ≤
        max M (finMax m fun i ↦ k (.inr i)) := fun i ↦ by
      have h1 : k (.inr i) ≤ finMax m fun i ↦ k (.inr i) := le_finMax m (fun i ↦ k (.inr i)) i
      have h2 : (repTransport (h (.inr i)) (c (.inr i)).2 x).word.length ≤ max M (k (.inr i)) :=
        wordBounded_transport (h _) (hk _ (hkb.2 i)) x M hx
      omega
    have := wordBounded_transport (h (.inl ())) (hk _ hkb.1) _
      (max M (finMax m fun i ↦ k (.inr i))) hargs
    omega
  | srn a b j =>
    change (finAll b (fun l ↦ kb (.inl l)) &&
      (finAll b (fun l ↦ kb (.inr (.inl l))) && finAll b fun l ↦ kb (.inr (.inr l)))) = true
      at hkb
    rw [Bool.and_eq_true, Bool.and_eq_true, finAll_eq_true_iff, finAll_eq_true_iff,
      finAll_eq_true_iff] at hkb
    refine wordBounded_evalSRNRep (fun l ↦ ?_) (fun i l ↦ ?_) w j
    · exact wordBounded_mono (Nat.le_trans (le_finMax b (fun l ↦ k (.inl l)) l)
        (Nat.le_max_left _ _)) (wordBounded_transport _ (hk _ (hkb.1 l)))
    · cases i
      · exact wordBounded_mono (Nat.le_trans (le_finMax b (fun l ↦ k (.inr (.inl l))) l)
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
          (wordBounded_transport _ (hk _ (hkb.2.1 l)))
      · exact wordBounded_mono (Nat.le_trans (le_finMax b (fun l ↦ k (.inr (.inr l))) l)
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
          (wordBounded_transport _ (hk _ (hkb.2.2 l)))

/-- Every successor-free expression keeps the word part within the constant
{name}`Geb.SizeBounded.nsiConst` reads off its syntax. -/
theorem wordBounded_evalRep (w : List Bool) :
    ∀ e : S, sbsFree e.1 = true → WordBounded (nsiConst e.1) (evalRep w e).2 :=
  SlicePFunctor.W.induction fun x ih hfree ↦
    wordBounded_evalRepValue w x.1.1 (fun b ↦ evalRep w (x.1.2 b)) _
      (fun b ↦ sbsFree (x.1.2 b).1) hfree (fun b ↦ nsiConst (x.1.2 b).1) ih

/-- An expression of the subalgebra denotes its meaning on representations. -/
theorem den_repSem (w : List Bool) {n : ℕ} (e : LOf n) : Denotes w (e.repSem w) e.sem :=
  (den_evalRep w e.1.1).atArity ((fst_evalRep w e.1.1).trans e.1.2) ((fst_eval e.1.1).trans e.1.2)

/-- An expression of the subalgebra keeps the length part within the input. -/
theorem validAt_repSem (w : List Bool) {n : ℕ} (e : LOf n) : ValidAt w.length (e.repSem w) :=
  validAt_transport ((fst_evalRep w e.1.1).trans e.1.2) (validAt_evalRep w e.1.1)

/-- An expression of the subalgebra keeps the word part within its constant. -/
theorem wordBounded_repSem (w : List Bool) {n : ℕ} (e : LOf n) :
    WordBounded (nsiConst e.1.1.1) (e.repSem w) :=
  wordBounded_transport ((fst_evalRep w e.1.1).trans e.1.2) (wordBounded_evalRep w e.1.1 e.2)

end

end Geb.SizeBounded.Logspace

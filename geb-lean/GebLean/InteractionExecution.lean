import GebLean.PolyGSOS

/-!
Research prototype for interaction nets, GSOS, and fairness.

Run from the repository root:
  lake env lean docs/research/InteractionExecution.lean

This constructs GSOS laws for polynomial state machines, including finite
nondeterministic branching, and a two-constructor compositional polling rule.
It does not implement interaction-net graphs or prove adequacy for a
graph-compositional translation.

The merger consumes total, nonblocking source steps. `none` means a silent
step, not an end-of-stream test. Its two output equations prove that every
source event is emitted in order, even when the other source is silent forever.
This polling interface is stronger than opaque streams with only `amb`.
-/

open CategoryTheory GebLean

namespace GebLean.Research.InteractionExecution

/-- One nullary syntax operation for each complete machine state. -/
-- ponytail: whole states are constants; compositional graph syntax needs a separate adequacy proof.
def stateSignature (S : Type) : PolyEndo Unit :=
  fun _ ↦ ccrObjMk (fun _ : S ↦ overEmpty Unit)

/-- The arbitrary polynomial behavior Q(X) = Σ o, X^(E o). -/
def behavior (O : Type) (E : O → Type) : PolyEndo Unit :=
  fun _ ↦ ccrObjMk (fun o : O ↦ Over.mk (fun _ : E o ↦ ()))

/-- Package any polynomial coalgebra as a rule in the actual polynomial GSOS API. -/
def machineGSOS {S O : Type} {E : O → Type}
    (step : S → (o : O) × (E o → S)) :
    PolyGSOSRule (stateSignature S) (behavior O E) where
  rule := fun _ ↦ ccrHomMk
    (fun p ↦ ⟨(step p.1).1,
      fun e ↦ polyFreeMShapeSingleNode (stateSignature S) ((step p.1).2 e)⟩)
    (fun _ ↦ Over.homMk (fun e ↦ PEmpty.elim e.2.1)
      (by funext e; exact PEmpty.elim e.2.1))

/-- Obtain all four distributive-law coherence proofs from the existing implementation. -/
def machineLaw {S O : Type} {E : O → Type}
    (step : S → (o : O) × (E o → S)) :=
  polyGSOSDistributiveLaw _ _ (machineGSOS step)

/-- The actual initial-to-final lambda-bialgebra map for this machine. -/
def machineSemantics {S O : Type} {E : O → Type}
    (step : S → (o : O) × (E o → S)) :=
  universalSemantics (machineLaw step)
    (overInitial_isInitial Unit) (overTerminal_isTerminal Unit)

/-- Lists present finite nondeterminism, retaining transition order and multiplicity. -/
def listMachine {S L : Type} (step : S → List (L × S))
    (s : S) : (labels : List L) × (Fin labels.length → S) :=
  ⟨(step s).map Prod.fst,
    fun i ↦ ((step s).get ⟨i.val, by simpa using i.isLt⟩).2⟩

/-- In particular, an enumerated finite transition relation gives a polynomial GSOS rule. -/
def listGSOS {S L : Type} (step : S → List (L × S)) :=
  machineGSOS (listMachine step)

/-- Two binary operators, one for each turn of a polling merger: P(X) = X² + X². -/
def mergeSignature : PolyEndo Unit := behavior Bool (fun _ ↦ Bool)

/-- A nonblocking observation and one continuation: Q(X) = Option A × X. -/
def pollingBehavior (A : Type) : PolyEndo Unit :=
  behavior (Option A) (fun _ ↦ PUnit)

/--
A compositional GSOS rule for polling, without making whole configurations constants.

The selected operand contributes its observation and advances to its continuation.
The other operand is retained, and the next term switches the turn.
-/
def pollingGSOS (A : Type) : PolyGSOSRule mergeSignature (pollingBehavior A) where
  rule := fun _ ↦ ccrHomMk
    (fun p ↦ ⟨p.2 p.1 (.inr .unit),
      fun _ ↦ polyFreeMShapeSingleNode mergeSignature (!p.1)⟩)
    (fun p ↦ Over.homMk
      (fun e ↦ ⟨e.2.1,
        if @BEq.beq Bool _ e.2.1 p.1 then ⟨.inr .unit, .unit⟩ else ⟨.inl .unit, .unit⟩⟩)
      (by funext e; exact @Subsingleton.elim Unit _ _ _))

/-- The two operators act on final polling behaviors via the existing final bialgebra. -/
def pollingAlgebra (A : Type) :=
  (finalBialgebra (polyGSOSDistributiveLaw _ _ (pollingGSOS A))
    (overTerminal_isTerminal Unit)).algebra

/-- Scheduler state; false polls the left source, true polls the right source. -/
structure MergeState (S T : Type) where
  /-- Conventional "left" -- not significant, just consistent. -/
  left : S
  /-- Conventional "right" -- not significant, just consistent. -/
  right : T
  /-- Is it "right"'s turn to be polled? -/
  rightTurn : Bool

/-- One nonblocking poll. A silent source still relinquishes the next turn. -/
def mergeTick {S T A B : Type}
    (leftStep : S → Option A × S) (rightStep : T → Option B × T)
    (s : MergeState S T) : Option (A ⊕ B) × MergeState S T :=
  if s.rightTurn then
    let r := rightStep s.right
    (r.1.map Sum.inr, ⟨s.left, r.2, false⟩)
  else
    let l := leftStep s.left
    (l.1.map Sum.inl, ⟨l.2, s.right, true⟩)

/-- State transition underlying the merger. -/
def mergeNext {S T A B : Type}
    (leftStep : S → Option A × S) (rightStep : T → Option B × T) :=
  fun s ↦ (mergeTick leftStep rightStep s).2

/-- After 2n ticks, both sources have advanced exactly n steps. -/
theorem merge_even {S T A B : Type}
    (leftStep : S → Option A × S) (rightStep : T → Option B × T)
    (l : S) (r : T) (n : Nat) :
    (mergeNext leftStep rightStep)^[2 * n] ⟨l, r, false⟩ =
      ⟨(fun x ↦ (leftStep x).2)^[n] l, (fun x ↦ (rightStep x).2)^[n] r, false⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm (2 * n) 2, Function.iterate_add_apply, ih]
    simp [Function.iterate_succ_apply', mergeNext, mergeTick]

/-- Every left event occurs at its designated finite time; no right-side progress is assumed. -/
theorem merge_left_output {S T A B : Type}
    (leftStep : S → Option A × S) (rightStep : T → Option B × T)
    (l : S) (r : T) (n : Nat) :
    (mergeTick leftStep rightStep
      ((mergeNext leftStep rightStep)^[2 * n] ⟨l, r, false⟩)).1 =
      (leftStep ((fun x ↦ (leftStep x).2)^[n] l)).1.map Sum.inl := by
  rw [merge_even]
  rfl

/-- Every right event occurs at its designated finite time; no left-side progress is assumed. -/
theorem merge_right_output {S T A B : Type}
    (leftStep : S → Option A × S) (rightStep : T → Option B × T)
    (l : S) (r : T) (n : Nat) :
    (mergeTick leftStep rightStep
      ((mergeNext leftStep rightStep)^[2 * n + 1] ⟨l, r, false⟩)).1 =
      (rightStep ((fun x ↦ (rightStep x).2)^[n] r)).1.map Sum.inr :=
        by rw [Function.iterate_succ_apply', merge_even] ; rfl

/-- Put the merger in polynomial form, with one successor per observation. -/
def mergeMachine {S T A B : Type}
    (leftStep : S → Option A × S) (rightStep : T → Option B × T)
    (s : MergeState S T) :
    (_o : Option (A ⊕ B)) × (Unit → MergeState S T) :=
  let next := mergeTick leftStep rightStep s
  ⟨next.1, fun _ ↦ next.2⟩

/-- The polling merger instantiates the repository's universalSemantics. -/
def mergeSemantics {S T A B : Type}
    (leftStep : S → Option A × S) (rightStep : T → Option B × T) :=
  machineSemantics (mergeMachine leftStep rightStep)

/-- Both choices must recur arbitrarily far along an infinite schedule. -/
def FairSchedule (schedule : Nat → Bool) : Prop :=
  ∀ b n, ∃ m, n ≤ m ∧ schedule m = b

/-- A trivial example of a non-fair stream:  constant "false".
-/
theorem always_left_not_fair : ¬ FairSchedule (fun _ ↦ false) := by
  intro h
  obtain ⟨_, _, hm⟩ := h true 0
  cases hm

/-- Alternate booleans one by one. -/
def alternating (n : Nat) : Bool := n % 2 == 1

theorem alternating_fair : FairSchedule alternating := by
  intro b n
  cases b with
  | false =>
    refine ⟨2 * n, by omega, ?_⟩
    simp [alternating]
  | true =>
    refine ⟨2 * n + 1, by omega, ?_⟩
    simp [alternating]

/-- Finite observations alone cannot distinguish arbitrary schedules from fair schedules. -/
theorem every_prefix_has_fair_extension (given : Nat → Bool) (cutoff : Nat) :
    ∃ schedule, FairSchedule schedule ∧ ∀ n < cutoff, schedule n = given n := by
  refine ⟨fun n ↦ if n < cutoff then given n else alternating (n - cutoff), ?_, ?_⟩
  · intro b n
    cases b with
    | false =>
      refine ⟨cutoff + 2 * n, by omega, ?_⟩
      simp [alternating]
    | true =>
      refine ⟨cutoff + (2 * n + 1), by omega, ?_⟩
      simp [alternating]
  · intro n hn
    exact if_pos hn

/-- A genuine two-way choice at each step, despite the rule itself being a function. -/
def choiceStep (n : Nat) : List (Bool × Nat) :=
  [(false, n + 1), (true, n + 1)]

example (n : Nat) : (listMachine choiceStep n).1 = [false, true] := rfl

/-- A source that never supplies a value. -/
def waitingSource : Unit → Option Nat × Unit := fun u ↦ (none, u)

/-- A source that supplies a value on every poll. -/
def countingSource (n : Nat) : Option Nat × Nat := (some n, n + 1)

-- A permanently silent left source does not block the right source.
example : (List.range 6).map (fun n ↦
  (mergeTick waitingSource countingSource
    ((mergeNext waitingSource countingSource)^[n] ⟨(), 0, false⟩)).1) =
  [none, some (Sum.inr 0), none, some (Sum.inr 1), none, some (Sum.inr 2)] := by decide

end GebLean.Research.InteractionExecution

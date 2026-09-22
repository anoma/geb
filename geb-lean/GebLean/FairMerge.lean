/-!
# Fair merge in a synchronous (GSOS-shaped) semantics, and why a
# step-wise demonic scheduler cannot produce it

Core Lean only.

Panangaden–Shanbhogue ("The expressive power of indeterminate dataflow
primitives", Inf. & Comp. 98, 1992) show fair merge is interdefinable with
Keller's `poll` (a primitive sensitive to the *absence* of input), and that
no network of Hoare-monotone, limit-closed asynchronous processes computes
it (their Thm. 9). In an abstract-GSOS semantics the rule for an operator
sees the current-step behaviour of each argument, including silence, so
`poll` is available for free. Part 1 exhibits fair merge as such an
operator. Part 2 shows the complementary obstruction: the set of fair
interleavings is not the path set of any tree, so no scheduler choosing
step by step (demonic amb) has fair merge as its set of runs.
-/

namespace GebLean

/-! ## Part 1: fair merge as a `Q`-coalgebra with `Q X = Option A × X` -/

/-- A polled input stream (Panangaden–Shanbhogue's `poll` output):
at each tick, a value or `?` (`none`). This is the "matter". -/
abbrev Polled (A : Type) := Nat → Option A

/-- State of the alternating zipper: the two polled inputs and whose turn it is. -/
structure ZipState (A : Type) where
  /-- The input read on `true` turns. -/
  left : Polled A
  /-- The input read on `false` turns. -/
  right : Polled A
  /-- Whether the next tick reads `left`. -/
  turn : Bool

variable (A : Type)

/-- One tick of the zipper: strict alternation. The GSOS rule for the
operator `zip` reads the current-step behaviour of one argument
(possibly silence) and re-forms a `zip` term. -/
def ZipState.step (s : ZipState A) : Option A × ZipState A :=
  if s.turn then (s.left 0, ⟨fun t => s.left (t + 1), s.right, false⟩)
  else (s.right 0, ⟨s.left, fun t => s.right (t + 1), true⟩)

/-- The trace (unique map into the final coalgebra of `Option A × -`). -/
def ZipState.trace (s : ZipState A) : Polled A
  | 0 => s.step.1
  | t + 1 => s.step.2.trace t

/-- Fair merge of two polled streams by strict alternation, reading `x` first. -/
def fairMerge (x y : Polled A) : Polled A := ZipState.trace A ⟨x, y, true⟩

theorem fairMerge_left (x y : Polled A) (t : Nat) :
    fairMerge A x y (2 * t) = x t := by
  induction t generalizing x y with
  | zero => rfl
  | succ t ih =>
    show ZipState.trace A _ (2 * t + 2) = _
    simp only [ZipState.trace, ZipState.step, if_true]
    exact ih _ _

theorem fairMerge_right (x y : Polled A) (t : Nat) :
    fairMerge A x y (2 * t + 1) = y t := by
  induction t generalizing x y with
  | zero => rfl
  | succ t ih =>
    show ZipState.trace A _ (2 * t + 3) = _
    simp only [ZipState.trace, ZipState.step, if_true]
    exact ih _ _

/-- Fairness: every value offered on either input appears in the output,
regardless of whether the other input is finite, silent, or infinite. -/
theorem fairMerge_fair (x y : Polled A) (t : Nat) (a : A) :
    (x t = some a → ∃ u, fairMerge A x y u = some a) ∧
    (y t = some a → ∃ u, fairMerge A x y u = some a) :=
  ⟨fun h => ⟨2 * t, (fairMerge_left A x y t).trans h⟩,
   fun h => ⟨2 * t + 1, (fairMerge_right A x y t).trans h⟩⟩

/-! ## Part 2: no tree has the fair interleavings as its path set -/

/-- Infinite schedules over two sides. -/
abbrev Sched := Nat → Bool

/-- Fair: each side is chosen infinitely often. -/
def Fair (w : Sched) : Prop :=
  (∀ n, ∃ m ≥ n, w m = true) ∧ (∀ n, ∃ m ≥ n, w m = false)

/-- The first `n` choices of a schedule, as a finite word. -/
def prefixOf (w : Sched) : Nat → List Bool
  | 0 => []
  | n + 1 => prefixOf w n ++ [w n]

/-- Infinite paths of a set of finite words (the runs of a step-wise
scheduler): every finite prefix is permitted. -/
def Paths (T : List Bool → Prop) (w : Sched) : Prop := ∀ n, T (prefixOf w n)

/-- The schedule `false^n (true false)^ω`. -/
def repair (n : Nat) : Sched := fun m => if m < n then false else m % 2 = 0

theorem repair_fair (n : Nat) : Fair (repair n) :=
  ⟨fun k => ⟨2 * (k + n), by omega, by simp [repair] <;> omega⟩,
   fun k => ⟨2 * (k + n) + 1, by omega, by simp [repair] <;> omega⟩⟩

theorem prefixOf_congr (w v : Sched) (n : Nat) (h : ∀ m < n, w m = v m) :
    prefixOf w n = prefixOf v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prefixOf, ih (fun m hm => h m (by omega)), h n (by omega)]

/-- If every fair schedule is a path of `T`, so is the unfair schedule
`false^ω`; hence `Fair ≠ Paths T` for every `T`. -/
theorem fair_not_paths (T : List Bool → Prop) (hT : ∀ w, Fair w → Paths T w) :
    ¬ (∀ w, Paths T w → Fair w) := by
  intro hP
  have hall : Paths T (fun _ => false) := fun n => by
    have := hT (repair n) (repair_fair n) n
    rwa [prefixOf_congr (repair n) (fun _ => false) n
      (fun m hm => by simp [repair, hm])] at this
  obtain ⟨m, -, hm⟩ := (hP _ hall).1 0
  exact Bool.false_ne_true hm

end GebLean

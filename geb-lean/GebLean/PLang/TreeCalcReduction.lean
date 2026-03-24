import GebLean.PLang.TreeCalcPoly

/-!
# Tree Calculus Reduction

Behavior polynomial, one-step reduction, and
coalgebraic evaluation for tree calculus.
-/

namespace GebLean

open CategoryTheory

universe u

/-! ## Behavior Polynomial

The behavior polynomial `polyBehavior` describes
observations of tree calculus computations.  It is
a single-sorted polynomial on `PUnit` with four
positions:

- 0 (done-leaf): computation terminated as leaf;
  no children.
- 1 (done-stem): computation terminated as stem;
  one child (sub-computation).
- 2 (done-fork): computation terminated as fork;
  two children (sub-computations).
- 3 (cont): computation not yet terminated;
  one child (continuation to next state).

Elements of `PolyCofix polyBehavior PUnit.unit`
are potentially infinite trees.  Finite elements
correspond to terminating computations; infinite
elements (with infinite chains of `cont` nodes)
correspond to diverging computations.
-/

/-- Direction type for each position of the
behavior polynomial. -/
def behaviorDirType : Fin 4 → Type u
  | 0 => PEmpty.{u + 1}
  | 1 => PUnit.{u + 1}
  | 2 => PUnit.{u + 1} ⊕ PUnit.{u + 1}
  | 3 => PUnit.{u + 1}

/-- The behavior polynomial for tree calculus
computation.  Single-sorted on `PUnit` with
four positions indexed by `Fin 4`. -/
def polyBehavior : PolyEndo PUnit.{u + 1} :=
  fun _ => ccrObjMk
    (fun (p : Σ _ : Fin 4, PUnit.{u + 1}) =>
      Over.mk
        (fun (_ : behaviorDirType.{u} p.1) =>
          PUnit.unit))

/-! ## Observation Type

`BehaviorObs A` is the type of observations
produced by the behavior polynomial at a
carrier `A : Over PUnit`.  It is defined as the
polynomial evaluation family of `polyBehavior`
at `A`, not as a separate inductive.
-/

/-- Carrier for the reduction coalgebra:
`CompTree` over `PUnit`. -/
def stepCarrier : Over PUnit.{u + 1} :=
  Over.mk (fun (_ : CompTree.{u}) => PUnit.unit)

/-- Observation type: the behavior polynomial
evaluated at carrier `A`.  Elements are pairs
of a position index and a morphism from the
direction object at that position to `A`. -/
abbrev BehaviorObs (A : Over PUnit.{u + 1}) :=
  polyBetweenEvalFamily PUnit PUnit
    polyBehavior.{u} A PUnit.unit

/-- Extract the position index (Fin 4) from
an observation. -/
def BehaviorObs.tag
    (obs : BehaviorObs stepCarrier.{u}) :
    Fin 4 :=
  obs.1.1

/-- Done-leaf observation: computation terminated
as a leaf with no sub-computations. -/
def BehaviorObs.doneLeaf :
    BehaviorObs stepCarrier.{u} :=
  ⟨⟨(0 : Fin 4), PUnit.unit⟩,
   Over.homMk (fun e => PEmpty.elim e)
     (by funext e; exact PEmpty.elim e)⟩

/-- Done-stem observation: computation terminated
as a stem; `child` is the sub-computation. -/
def BehaviorObs.doneStem
    (child : CompTree.{u}) :
    BehaviorObs stepCarrier.{u} :=
  ⟨⟨(1 : Fin 4), PUnit.unit⟩,
   Over.homMk (fun _ => child)
     (by funext _; rfl)⟩

/-- Done-fork observation: computation terminated
as a fork; `l` and `r` are the
sub-computations. -/
def BehaviorObs.doneFork
    (l r : CompTree.{u}) :
    BehaviorObs stepCarrier.{u} :=
  ⟨⟨(2 : Fin 4), PUnit.unit⟩,
   Over.homMk
     (fun e => match e with
       | Sum.inl _ => l
       | Sum.inr _ => r)
     (by funext e; match e with
       | Sum.inl _ => rfl
       | Sum.inr _ => rfl)⟩

/-- Continuation observation: computation not
yet terminated; `next` is the next state. -/
def BehaviorObs.cont
    (next : CompTree.{u}) :
    BehaviorObs stepCarrier.{u} :=
  ⟨⟨(3 : Fin 4), PUnit.unit⟩,
   Over.homMk (fun _ => next)
     (by funext _; rfl)⟩

/-! ## Rule Application

`applyRule v x` attempts to apply value `v` to
argument `x`, returning `some result` when a rule
fires and `none` when the argument must be reduced
further before the rule can apply.

Partial applications (leaf applied to one value
argument, stem applied to one value argument)
produce values.  K and S rules apply regardless
of the argument's form.  Triage rules require the
argument to be an embedded value.
-/

/-- Helper: build a `CompTree` application,
unwrapping singletons and treating empty as
leaf. -/
def mkApp : List CompTree.{u} → CompTree.{u}
  | [] => CompTree.embed CompValue.leaf
  | [t] => t
  | ts => CompTree.app ts

/-- Apply value `v` to argument `x`.  Returns
`some result` when a rule fires, `none` when
the argument must be reduced first. -/
def applyRule :
    CompValue.{u} → CompTree.{u} →
    Option CompTree.{u} :=
  fun v x =>
    CompValue.cases
      -- v = leaf: partial application
      (CompTree.cases
        (fun y => some
          (CompTree.embed (CompValue.stem y)))
        (fun _ => none)
        x)
      -- v = stem(a): partial application
      (fun a => CompTree.cases
        (fun y => some
          (CompTree.embed (CompValue.fork a y)))
        (fun _ => none)
        x)
      -- v = fork(a, b): K, S, or triage
      (fun a b =>
        CompValue.cases
          -- a = leaf: K rule (discard x)
          (some (CompTree.embed b))
          -- a = stem(c): S rule
          (fun c => some (CompTree.app
            [ CompTree.embed c, x,
              CompTree.app
                [CompTree.embed b, x] ]))
          -- a = fork(w, xf): triage on x
          (fun w xf =>
            CompTree.cases
              (fun z =>
                CompValue.cases
                  -- z = leaf: rule 3a
                  (some (CompTree.embed w))
                  -- z = stem(u): rule 3b
                  (fun u => some (CompTree.app
                    [ CompTree.embed xf,
                      CompTree.embed u ]))
                  -- z = fork(u, v'): rule 3c
                  (fun u v' => some (CompTree.app
                    [ CompTree.embed b,
                      CompTree.embed u,
                      CompTree.embed v' ]))
                  z)
              -- x is app: need to reduce first
              (fun _ => none)
              x)
          a)
      v

/-! ## One-Step Reduction

`reduce1` performs one step of eager (leftmost
innermost) reduction on a `CompTree`.
-/

/-- One step of eager (leftmost-innermost)
reduction on a `CompTree`.  The `fuel` parameter
bounds the depth of sub-term reduction; at
fuel 0, the tree is returned unchanged if the
top-level redex cannot fire. -/
def reduce1 (fuel : Nat) :
    CompTree.{u} → CompTree.{u} :=
  fun t => CompTree.cases
    (fun _ => t)
    (fun ts =>
      match ts with
      | [] => CompTree.embed CompValue.leaf
      | [s] => s
      | head :: arg :: rest =>
        CompTree.cases
          (fun v =>
            match applyRule v arg with
            | some result =>
              mkApp (result :: rest)
            | none =>
              match fuel with
              | 0 => t
              | fuel + 1 =>
                CompTree.app
                  (head
                  :: reduce1 fuel arg
                  :: rest))
          (fun _ =>
            match fuel with
            | 0 => t
            | fuel + 1 =>
              CompTree.app
                (reduce1 fuel head
                :: arg :: rest))
          head)
    t

/-! ## Step Function

The `step` function is the coalgebra structure
map: given a `CompTree`, it produces an
observation in `BehaviorObs stepCarrier` (the
behavior polynomial evaluated at the carrier).
Values are observed immediately (done-leaf,
done-stem, done-fork).  Computations are reduced
by one step and returned as continuations.
-/

/-- Observe a `CompValue`: report its top-level
structure as a `BehaviorObs`. -/
def observeValue (v : CompValue.{u}) :
    BehaviorObs stepCarrier.{u} :=
  CompValue.cases
    BehaviorObs.doneLeaf
    (fun child => BehaviorObs.doneStem
      (CompTree.embed child))
    (fun l r => BehaviorObs.doneFork
      (CompTree.embed l) (CompTree.embed r))
    v

/-- The coalgebra step function: observe a value
or reduce and continue.  The `fuel` parameter
bounds the depth of sub-term reduction within
a single step. -/
def step (fuel : Nat) (t : CompTree.{u}) :
    BehaviorObs stepCarrier.{u} :=
  CompTree.cases
    (fun v => observeValue v)
    (fun ts =>
      match ts with
      | [] => BehaviorObs.doneLeaf
      | [s] => BehaviorObs.cont s
      | _ =>
        let t' := reduce1 fuel t
        CompTree.cases
          (fun v => observeValue v)
          (fun _ => BehaviorObs.cont t')
          t')
    t

/-! ## Coalgebra Packaging

The `step` function is packaged as a
`PolyCoalg polyBehavior` with carrier
`CompTree` (viewed as an object of
`Over PUnit`).  No conversion is needed: `step`
already produces elements of the polynomial
evaluation family.
-/

/-- The `.left` component of the reduction
coalgebra structure map. -/
def stepCoalgStrLeft (fuel : Nat) :
    CompTree.{u} →
    (Σ _ : PUnit.{u + 1},
      BehaviorObs stepCarrier.{u}) :=
  fun t => ⟨PUnit.unit, step fuel t⟩

/-- The reduction coalgebra: `CompTree` equipped
with the `step` structure map. -/
def stepCoalg (fuel : Nat) :
    PolyCoalg polyBehavior.{u} where
  V := stepCarrier
  str := Over.homMk (stepCoalgStrLeft fuel)
    (by funext _; rfl)

/-! ## Evaluation Anamorphism

Full evaluation maps a `CompTree` to an element
of `PolyCofix polyBehavior PUnit.unit` via the
anamorphism from the reduction coalgebra.
-/

/-- Full evaluation of a `CompTree` into the
terminal coalgebra of the behavior polynomial.
The `fuel` parameter bounds the depth of
sub-term reduction per step. -/
def eval (fuel : Nat) (t : CompTree.{u}) :
    PolyCofix polyBehavior.{u} PUnit.unit :=
  polyCofixUnfoldAt polyBehavior
    (stepCoalg fuel) PUnit.unit ⟨t, rfl⟩

/-! ## Multi-Step Reduction

`Reduces` is defined via iteration of `reduce1`,
not as a separate inductive: `t1` reduces to
`t2` when some number of `reduce1` iterations
transforms `t1` into `t2`.
-/

/-- One-step reduction relation: `t1` reduces to
`t2` in one step (with the given fuel). -/
def ReducesOnce (fuel : Nat)
    (t1 t2 : CompTree.{u}) : Prop :=
  reduce1 fuel t1 = t2

/-- Multi-step reduction: `t1` reduces to `t2`
in `n` steps of `reduce1` for some `n`. -/
def Reduces (fuel : Nat)
    (t1 t2 : CompTree.{u}) : Prop :=
  ∃ n : Nat, (reduce1 fuel)^[n] t1 = t2

/-- `Reduces` is reflexive. -/
lemma Reduces.refl
    {fuel : Nat} {t : CompTree.{u}} :
    Reduces fuel t t :=
  ⟨0, rfl⟩

/-- `Reduces` is transitive. -/
lemma Reduces.trans
    {fuel : Nat}
    {t1 t2 t3 : CompTree.{u}} :
    Reduces fuel t1 t2 →
    Reduces fuel t2 t3 →
    Reduces fuel t1 t3 := by
  intro ⟨m, hm⟩ ⟨n, hn⟩
  exact ⟨m + n, by
    rw [show m + n = n + m from Nat.add_comm m n,
        Function.iterate_add,
        Function.comp_apply, hm, hn]⟩

/-- One step extends a reduction sequence. -/
lemma Reduces.step
    {fuel : Nat}
    {t1 t2 t3 : CompTree.{u}} :
    ReducesOnce fuel t1 t2 →
    Reduces fuel t2 t3 →
    Reduces fuel t1 t3 := by
  intro h1 ⟨n, hn⟩
  exact ⟨n + 1, by
    simp only [Function.iterate_succ,
      Function.comp]
    rw [h1, hn]⟩

end GebLean

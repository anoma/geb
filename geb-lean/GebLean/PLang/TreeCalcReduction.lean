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
innermost) reduction on a `CompTree`.  It
pattern-matches on the `PolyFix` constructor to
enable structural recursion: recursive calls are
always on direct children of the current node.
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
observation.  Values are observed immediately
(done-leaf, done-stem, done-fork).  Computations
are reduced by one step and returned as
continuations.

`StepResult α` is the type of observations,
isomorphic to `polyBehavior PUnit.unit` applied
to the constant carrier `α`.
-/

/-- Result of one step of the behavior
coalgebra.  Isomorphic to applying the behavior
polynomial at the sole fiber. -/
inductive StepResult (α : Type u) : Type u where
  | doneLeaf : StepResult α
  | doneStem : α → StepResult α
  | doneFork : α → α → StepResult α
  | cont : α → StepResult α
  deriving Inhabited

/-- Observe a `CompValue`: report its top-level
structure as a `StepResult`. -/
def observeValue (v : CompValue.{u}) :
    StepResult CompTree.{u} :=
  CompValue.cases
    StepResult.doneLeaf
    (fun x => StepResult.doneStem
      (CompTree.embed x))
    (fun l r => StepResult.doneFork
      (CompTree.embed l) (CompTree.embed r))
    v

/-- The coalgebra step function: observe a value
or reduce and continue.  The `fuel` parameter
bounds the depth of sub-term reduction within
a single step. -/
def step (fuel : Nat) (t : CompTree.{u}) :
    StepResult CompTree.{u} :=
  CompTree.cases
    (fun v => observeValue v)
    (fun ts =>
      match ts with
      | [] => StepResult.doneLeaf
      | [s] => StepResult.cont s
      | _ =>
        let t' := reduce1 fuel t
        CompTree.cases
          (fun v => observeValue v)
          (fun _ => StepResult.cont t')
          t')
    t

/-! ## Coalgebra Packaging

The `step` function is packaged as a
`PolyCoalg polyBehavior` with carrier
`CompTree` (viewed as an object of
`Over PUnit`).
-/

/-- Carrier for the reduction coalgebra:
`CompTree` over `PUnit`. -/
def stepCarrier : Over PUnit.{u + 1} :=
  Over.mk (fun (_ : CompTree.{u}) => PUnit.unit)

/-- Convert a `StepResult CompTree` to the
sigma type used by `polyBetweenEvalFamily`. -/
def stepResultToSigma
    (r : StepResult CompTree.{u}) :
    polyBetweenEvalFamily PUnit PUnit
      polyBehavior.{u} stepCarrier
      PUnit.unit :=
  match r with
  | .doneLeaf =>
    ⟨⟨(0 : Fin 4), PUnit.unit⟩,
     Over.homMk (fun e => PEmpty.elim e)
       (by funext e; exact PEmpty.elim e)⟩
  | .doneStem child =>
    ⟨⟨(1 : Fin 4), PUnit.unit⟩,
     Over.homMk (fun _ => child)
       (by funext _; rfl)⟩
  | .doneFork l r =>
    ⟨⟨(2 : Fin 4), PUnit.unit⟩,
     Over.homMk
       (fun e => match e with
         | Sum.inl _ => l
         | Sum.inr _ => r)
       (by funext e; match e with
         | Sum.inl _ => rfl
         | Sum.inr _ => rfl)⟩
  | .cont child =>
    ⟨⟨(3 : Fin 4), PUnit.unit⟩,
     Over.homMk (fun _ => child)
       (by funext _; rfl)⟩

/-- The `.left` component of the reduction
coalgebra structure map. -/
def stepCoalgStrLeft (fuel : Nat) :
    CompTree.{u} →
    (Σ x : PUnit.{u + 1},
      polyBetweenEvalFamily PUnit PUnit
        polyBehavior.{u} stepCarrier x) :=
  fun t => ⟨PUnit.unit,
    stepResultToSigma (step fuel t)⟩

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

`Reduces` is the reflexive-transitive closure
of one-step reduction.
-/

/-- One-step reduction relation: `t1` reduces to
`t2` in one step (with the given fuel). -/
def ReducesOnce (fuel : Nat)
    (t1 t2 : CompTree.{u}) : Prop :=
  reduce1 fuel t1 = t2

/-- Multi-step reduction: reflexive-transitive
closure of `ReducesOnce`. -/
inductive Reduces (fuel : Nat) :
    CompTree.{u} → CompTree.{u} → Prop where
  | refl {t : CompTree.{u}} :
    Reduces fuel t t
  | step {t1 t2 t3 : CompTree.{u}} :
    ReducesOnce fuel t1 t2 →
    Reduces fuel t2 t3 →
    Reduces fuel t1 t3

end GebLean

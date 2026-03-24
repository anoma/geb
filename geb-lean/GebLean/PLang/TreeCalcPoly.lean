import GebLean.PolyAlg
import GebLean.PolyUMorph
import GebLean.PLang.Syntax
import GebLean.Utilities.PolyCombinators

/-!
# Tree Calculus Polynomials

Polynomial endofunctors for tree calculus: the value
polynomial (leaf/stem/fork) and supporting
constructions.
-/

namespace GebLean

open CategoryTheory

universe u

/--
The direction type for each constructor of the value
polynomial.  Leaf has no directions, stem has one,
fork has two.
-/
def valueDirType : Fin 3 → Type u
  | 0 => PEmpty.{u + 1}
  | 1 => PUnit.{u + 1}
  | 2 => PUnit.{u + 1} ⊕ PUnit.{u + 1}

/--
The value polynomial endofunctor for tree calculus on
`PUnit`.  Three summands indexed by `Fin 3`:

- 0 (leaf): one position, no directions
- 1 (stem): one position, one direction
- 2 (fork): one position, two directions

Each direction maps to `PUnit.unit` (the sole fiber).
-/
def polyValue : PolyEndo PUnit.{u + 1} :=
  fun _ => ccrObjMk
    (fun (ip : Σ _ : Fin 3, PUnit.{u + 1}) =>
      Over.mk
        (fun _ : valueDirType.{u} ip.1 =>
          PUnit.unit))

/-- The type of tree calculus values: the initial
algebra of `polyValue` at the sole fiber
`PUnit.unit`. -/
abbrev Value : Type u :=
  PolyFix polyValue PUnit.unit

/-- The leaf constructor: a value with no
children. -/
def Value.leaf : Value.{u} :=
  PolyFix.mk PUnit.unit
    ⟨(0 : Fin 3), PUnit.unit⟩
    (fun e => PEmpty.elim e)

/-- The stem constructor: a value with one child. -/
def Value.stem (x : Value.{u}) : Value.{u} :=
  PolyFix.mk PUnit.unit
    ⟨(1 : Fin 3), PUnit.unit⟩
    (fun _ => x)

/-- The fork constructor: a value with two
children. -/
def Value.fork
    (l r : Value.{u}) : Value.{u} :=
  PolyFix.mk PUnit.unit
    ⟨(2 : Fin 3), PUnit.unit⟩
    (fun e => match e with
      | Sum.inl _ => l
      | Sum.inr _ => r)

/-- Catamorphism on `Value`: recursively replaces
leaf with `onLeaf`, stem with `onStem`, and fork
with `onFork`.

Implemented via `polyFixFoldAtWithProof` with the
algebra whose carrier is the constant `α`-valued
object over `PUnit`. -/
def Value.fold {α : Type u}
    (onLeaf : α)
    (onStem : α → α)
    (onFork : α → α → α)
    (v : Value.{u}) : α :=
  let carrier : Over PUnit.{u + 1} :=
    Over.mk (fun (_ : α) => PUnit.unit)
  let strFn :
      (Σ x : PUnit.{u + 1},
        polyBetweenEvalFamily PUnit PUnit
          polyValue carrier x) → α :=
    fun p => match p with
    | ⟨_, ⟨⟨⟨0, _⟩, _⟩, _⟩⟩ => onLeaf
    | ⟨_, ⟨⟨⟨1, _⟩, _⟩, mor⟩⟩ =>
      onStem (mor.left PUnit.unit)
    | ⟨_, ⟨⟨⟨2, _⟩, _⟩, mor⟩⟩ =>
      onFork
        (mor.left (Sum.inl PUnit.unit))
        (mor.left (Sum.inr PUnit.unit))
  let alg : PolyAlg polyValue := {
    a := carrier
    str := Over.homMk strFn
      (by funext ⟨_, _⟩; rfl)
  }
  (polyFixFoldAtWithProof polyValue alg
    PUnit.unit v).val

/-- Non-recursive case analysis on `Value`.  Passes
raw child values to the callbacks rather than
recursing. -/
def Value.cases {α : Type u}
    (onLeaf : α)
    (onStem : Value.{u} → α)
    (onFork : Value.{u} → Value.{u} → α)
    (v : Value.{u}) : α :=
  match v with
  | PolyFix.mk _ ⟨⟨0, _⟩, _⟩ _ => onLeaf
  | PolyFix.mk _ ⟨⟨1, _⟩, _⟩ children =>
    onStem (children PUnit.unit)
  | PolyFix.mk _ ⟨⟨2, _⟩, _⟩ children =>
    onFork
      (children (Sum.inl PUnit.unit))
      (children (Sum.inr PUnit.unit))

instance : Inhabited Value.{u} := ⟨Value.leaf⟩

@[simp]
lemma Value.fold_leaf {α : Type 0}
    (onLeaf : α) (onStem : α → α)
    (onFork : α → α → α) :
    Value.fold onLeaf onStem onFork
      Value.leaf = onLeaf := by
  rfl

@[simp]
lemma Value.fold_stem {α : Type 0}
    (onLeaf : α) (onStem : α → α)
    (onFork : α → α → α)
    (x : Value.{0}) :
    Value.fold onLeaf onStem onFork
      (Value.stem x) =
    onStem
      (Value.fold onLeaf onStem onFork x) := by
  rfl

@[simp]
lemma Value.fold_fork {α : Type 0}
    (onLeaf : α) (onStem : α → α)
    (onFork : α → α → α)
    (l r : Value.{0}) :
    Value.fold onLeaf onStem onFork
      (Value.fork l r) =
    onFork
      (Value.fold onLeaf onStem onFork l)
      (Value.fold onLeaf onStem onFork r) := by
  rfl

/-- Tag extraction: which constructor was used.
Returns `0` for leaf, `1` for stem, `2` for fork. -/
def Value.tag : Value.{u} → Fin 3 :=
  fun v => match v with
  | PolyFix.mk _ ⟨⟨0, _⟩, _⟩ _ => 0
  | PolyFix.mk _ ⟨⟨1, _⟩, _⟩ _ => 1
  | PolyFix.mk _ ⟨⟨2, _⟩, _⟩ _ => 2

/-- Constructor injection for `stem`. -/
lemma Value.stem_injective
    {x y : Value.{u}} (h : stem x = stem y) :
    x = y := by
  have h' := congrArg
    (fun v => Value.cases (α := Value.{u})
      Value.leaf id (fun l _ => l) v) h
  exact h'

/-- Constructor injection for `fork` (left). -/
lemma Value.fork_left_injective
    {l₁ r₁ l₂ r₂ : Value.{u}}
    (h : fork l₁ r₁ = fork l₂ r₂) :
    l₁ = l₂ := by
  have h' := congrArg
    (fun v => Value.cases (α := Value.{u})
      Value.leaf id (fun l _ => l) v) h
  exact h'

/-- Constructor injection for `fork` (right). -/
lemma Value.fork_right_injective
    {l₁ r₁ l₂ r₂ : Value.{u}}
    (h : fork l₁ r₁ = fork l₂ r₂) :
    r₁ = r₂ := by
  have h' := congrArg
    (fun v => Value.cases (α := Value.{u})
      Value.leaf id (fun _ r => r) v) h
  exact h'

/-- Discrimination: `leaf` is not `stem`. -/
lemma Value.leaf_ne_stem
    {x : Value.{u}} :
    Value.leaf ≠ Value.stem x := by
  intro h
  exact absurd (congrArg Value.tag h)
    (by simp [tag, leaf, stem])

/-- Discrimination: `leaf` is not `fork`. -/
lemma Value.leaf_ne_fork
    {l r : Value.{u}} :
    Value.leaf ≠ Value.fork l r := by
  intro h
  exact absurd (congrArg Value.tag h)
    (by simp [tag, leaf, fork])

/-- Discrimination: `stem` is not `fork`. -/
lemma Value.stem_ne_fork
    {x l r : Value.{u}} :
    Value.stem x ≠ Value.fork l r := by
  intro h
  exact absurd (congrArg Value.tag h)
    (by simp [tag, stem, fork])

/-- Size of a `Value` tree (number of nodes). -/
def Value.size : Value.{0} → Nat :=
  Value.fold 1 (· + 1) (· + · + 1)

@[simp]
lemma Value.size_leaf :
    Value.leaf.size = 1 := rfl

@[simp]
lemma Value.size_stem (x : Value.{0}) :
    (Value.stem x).size = x.size + 1 := rfl

@[simp]
lemma Value.size_fork (l r : Value.{0}) :
    (Value.fork l r).size =
      l.size + r.size + 1 := rfl

/-- Auxiliary inductive mirroring `Value` with standard
leaf/stem/fork constructors, used to derive `Repr`
and `BEq` and transport them to `Value`. -/
inductive ValueAux : Type u where
  | leaf : ValueAux
  | stem : ValueAux → ValueAux
  | fork : ValueAux → ValueAux → ValueAux
  deriving DecidableEq, Repr, Inhabited

/-- Convert `Value` to `ValueAux` via the fold. -/
def Value.toAux : Value.{0} → ValueAux.{0} :=
  Value.fold
    ValueAux.leaf
    ValueAux.stem
    ValueAux.fork

/-- Convert `ValueAux` to `Value`. -/
def ValueAux.toValue :
    ValueAux.{0} → Value.{0}
  | .leaf => Value.leaf
  | .stem x => Value.stem (toValue x)
  | .fork l r =>
    Value.fork (toValue l) (toValue r)

lemma ValueAux.toAux_toValue
    (a : ValueAux.{0}) :
    (a.toValue).toAux = a := by
  induction a with
  | leaf => rfl
  | stem x ih =>
    change Value.toAux
      (Value.stem x.toValue) =
      ValueAux.stem x
    rw [Value.toAux, Value.fold_stem]
    exact congrArg ValueAux.stem ih
  | fork l r ihl ihr =>
    change Value.toAux
      (Value.fork l.toValue r.toValue) =
      ValueAux.fork l r
    rw [Value.toAux, Value.fold_fork]
    exact congrArg₂ ValueAux.fork ihl ihr

/-- `Repr` for `Value` via `ValueAux`. -/
instance : Repr Value.{0} where
  reprPrec v n := reprPrec (Value.toAux v) n

/-- `BEq` for `Value` via `ValueAux`. -/
instance : BEq Value.{0} where
  beq v₁ v₂ := v₁.toAux == v₂.toAux

/--
Universe-polymorphic two-element fiber index for the
two-sorted computation polynomial.  `Sum.inl _`
represents the value fiber and `Sum.inr _`
represents the computation fiber.
-/
abbrev CompFiber :=
  PUnit.{u + 1} ⊕ PUnit.{u + 1}

/-- The value fiber. -/
abbrev CompFiber.val : CompFiber.{u} :=
  Sum.inl PUnit.unit

/-- The computation fiber. -/
abbrev CompFiber.comp : CompFiber.{u} :=
  Sum.inr PUnit.unit

/--
The position type for the two-sorted computation
polynomial at each fiber.  The value fiber has the
same three constructors as `polyValue`.  The
computation fiber has `embed` (one position) or
`app n` (one position per natural number `n`).
-/
def compPosType :
    CompFiber.{u} → Type u
  | Sum.inl _ =>
    Σ _ : Fin 3, PUnit.{u + 1}
  | Sum.inr _ =>
    PUnit.{u + 1} ⊕ ULift.{u} Nat

/--
The direction type for the two-sorted computation
polynomial at each fiber and position.  The value
fiber reuses `valueDirType`.  At the computation
fiber, `embed` has one direction and `app n` has
`n` directions.
-/
def compDirType :
    (x : CompFiber.{u}) →
    compPosType x → Type u
  | Sum.inl _, ⟨i, _⟩ =>
    valueDirType.{u} i
  | Sum.inr _, Sum.inl _ =>
    PUnit.{u + 1}
  | Sum.inr _, Sum.inr n =>
    ULift.{u} (Fin n.down)

/--
Maps each direction to the fiber it targets.
All value directions target the value fiber; the
`embed` direction targets the value fiber; all
`app` directions target the computation fiber.
-/
def compDirFiber :
    (x : CompFiber.{u}) →
    (p : compPosType x) →
    compDirType x p → CompFiber.{u}
  | Sum.inl _, _, _ =>
    CompFiber.val
  | Sum.inr _, Sum.inl _, _ =>
    CompFiber.val
  | Sum.inr _, Sum.inr _, _ =>
    CompFiber.comp

/--
The two-sorted computation polynomial endofunctor on
`CompFiber`.  The value fiber encodes values
(leaf/stem/fork); the computation fiber encodes
computations (embed value | app of list of
computations).
-/
def polyComputation :
    PolyEndo CompFiber.{u} :=
  fun x => ccrObjMk
    (fun (p : compPosType.{u} x) =>
      Over.mk
        (fun (d : compDirType.{u} x p) =>
          compDirFiber.{u} x p d))

/-- Values in the two-sorted system: the initial
algebra of `polyComputation` at the value fiber. -/
abbrev CompValue : Type u :=
  PolyFix polyComputation CompFiber.val

/-- Computation trees: the initial algebra of
`polyComputation` at the computation fiber. -/
abbrev CompTree : Type u :=
  PolyFix polyComputation CompFiber.comp

/-- Embeds a `CompValue` into a `CompTree`. -/
def CompTree.embed (v : CompValue.{u}) :
    CompTree.{u} :=
  PolyFix.mk CompFiber.comp
    (Sum.inl PUnit.unit)
    (fun _ => v)

/-- Constructs a computation tree from a list of
computation subtrees. -/
def CompTree.app
    (children : List CompTree.{u}) :
    CompTree.{u} :=
  PolyFix.mk CompFiber.comp
    (Sum.inr ⟨children.length⟩)
    (fun ⟨i⟩ => children[i])

/-- The leaf constructor for `CompValue`. -/
def CompValue.leaf : CompValue.{u} :=
  PolyFix.mk CompFiber.val
    ⟨(0 : Fin 3), PUnit.unit⟩
    (fun e => PEmpty.elim e)

/-- The stem constructor for `CompValue`. -/
def CompValue.stem (x : CompValue.{u}) :
    CompValue.{u} :=
  PolyFix.mk CompFiber.val
    ⟨(1 : Fin 3), PUnit.unit⟩
    (fun _ => x)

/-- The fork constructor for `CompValue`. -/
def CompValue.fork
    (l r : CompValue.{u}) :
    CompValue.{u} :=
  PolyFix.mk CompFiber.val
    ⟨(2 : Fin 3), PUnit.unit⟩
    (fun e => match e with
      | Sum.inl _ => l
      | Sum.inr _ => r)

/-- Converts a `Value` to the corresponding
`CompValue` (value fiber of the two-sorted
polynomial). -/
def valueToCompValue :
    Value.{u} → CompValue.{u} :=
  Value.fold
    CompValue.leaf
    CompValue.stem
    CompValue.fork

/-- Non-recursive case analysis on `CompValue`.
Passes raw child values to the callbacks rather
than recursing. -/
def CompValue.cases {α : Type u}
    (onLeaf : α)
    (onStem : CompValue.{u} → α)
    (onFork :
      CompValue.{u} → CompValue.{u} → α)
    (v : CompValue.{u}) : α :=
  match v with
  | PolyFix.mk _ ⟨⟨0, _⟩, _⟩ _ => onLeaf
  | PolyFix.mk _ ⟨⟨1, _⟩, _⟩ children =>
    onStem (children PUnit.unit)
  | PolyFix.mk _ ⟨⟨2, _⟩, _⟩ children =>
    onFork
      (children (Sum.inl PUnit.unit))
      (children (Sum.inr PUnit.unit))

/-- Extract the inner `Value` from either
summand. -/
def compValueSumGet :
    Value.{u} ⊕ Value.{u} → Value.{u}
  | Sum.inl v => v
  | Sum.inr v => v

/-- Carrier for the `polyComputation`-algebra
used by `compValueToValue`.  Elements are
`Value ⊕ Value`, with `Sum.inl` at the value
fiber and `Sum.inr` at the computation fiber. -/
def compValueAlgCarrier :
    Over CompFiber.{u} :=
  Over.mk
    (fun (p : Value.{u} ⊕ Value.{u}) =>
      match p with
      | Sum.inl _ => CompFiber.val
      | Sum.inr _ => CompFiber.comp)

/-- The `.left` component of the structure map
for the `compValueToValue` algebra. -/
def compValueAlgStrLeft :
    (Σ x : CompFiber.{u},
      polyBetweenEvalFamily
        CompFiber CompFiber
        polyComputation
        compValueAlgCarrier x) →
    Value.{u} ⊕ Value.{u}
  | ⟨Sum.inl _, ⟨⟨⟨0, _⟩, _⟩, _⟩⟩ =>
    Sum.inl Value.leaf
  | ⟨Sum.inl _, ⟨⟨⟨1, _⟩, _⟩, mor⟩⟩ =>
    Sum.inl
      (Value.stem
        (compValueSumGet (mor.left PUnit.unit)))
  | ⟨Sum.inl _, ⟨⟨⟨2, _⟩, _⟩, mor⟩⟩ =>
    Sum.inl
      (Value.fork
        (compValueSumGet
          (mor.left (Sum.inl PUnit.unit)))
        (compValueSumGet
          (mor.left (Sum.inr PUnit.unit))))
  | ⟨Sum.inr _, ⟨Sum.inl _, mor⟩⟩ =>
    Sum.inr
      (compValueSumGet (mor.left PUnit.unit))
  | ⟨Sum.inr _, ⟨Sum.inr _, _⟩⟩ =>
    Sum.inr Value.leaf

/-- The `polyComputation`-algebra mapping to
`Value` at both fibers. -/
def compValueAlg :
    PolyAlg polyComputation.{u} := {
  a := compValueAlgCarrier
  str := Over.homMk compValueAlgStrLeft
    (by funext ⟨x, e⟩; match x, e with
     | Sum.inl _, ⟨⟨⟨0, _⟩, _⟩, _⟩ => rfl
     | Sum.inl _, ⟨⟨⟨1, _⟩, _⟩, _⟩ => rfl
     | Sum.inl _, ⟨⟨⟨2, _⟩, _⟩, _⟩ => rfl
     | Sum.inr _, ⟨Sum.inl _, _⟩ => rfl
     | Sum.inr _, ⟨Sum.inr _, _⟩ => rfl)
}

/-- Converts a `CompValue` to the corresponding
`Value` via catamorphism. -/
def compValueToValue (v : CompValue.{u}) :
    Value.{u} :=
  compValueSumGet
    (polyFixFoldAtWithProof
      polyComputation compValueAlg
      CompFiber.val v).val

/-- Catamorphism on `CompValue`: recursively
replaces leaf with `onLeaf`, stem with `onStem`,
and fork with `onFork`. -/
def CompValue.fold {α : Type u}
    (onLeaf : α)
    (onStem : α → α)
    (onFork : α → α → α) :
    CompValue.{u} → α :=
  fun v => (compValueToValue v).fold
    onLeaf onStem onFork

/-- Embeds a `Value` directly into a `CompTree`
by first converting to `CompValue` and then
embedding. -/
def CompTree.embedValue (v : Value.{u}) :
    CompTree.{u} :=
  CompTree.embed (valueToCompValue v)

/-- Non-recursive case analysis on `CompTree`.
Passes the embedded `CompValue` or the list of
children to the appropriate callback. -/
def CompTree.cases {α : Type u}
    (onEmbed : CompValue.{u} → α)
    (onApp : List CompTree.{u} → α)
    (t : CompTree.{u}) : α :=
  match t with
  | PolyFix.mk _ (Sum.inl _) children =>
    onEmbed (children PUnit.unit)
  | PolyFix.mk _ (Sum.inr ⟨_⟩) children =>
    onApp (List.ofFn
      (fun i => children ⟨i⟩))

instance : Inhabited CompValue.{u} :=
  ⟨CompValue.leaf⟩

instance : Inhabited CompTree.{u} :=
  ⟨CompTree.embed CompValue.leaf⟩

end GebLean

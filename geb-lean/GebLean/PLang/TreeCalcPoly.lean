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

end GebLean

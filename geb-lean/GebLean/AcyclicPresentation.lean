import GebLean.CategoryPresentation
import GebLean.AcyclicQuiver
import GebLean.AcyclicCat
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Prod

/-!
# Presentations of Acyclic Categories

This module specializes category presentations to acyclic and finite acyclic
categories, providing convenient constructors and additional properties that
hold in these special cases.

## Main definitions

- `AcyclicPresentation`: A category presentation where the generators form
  an acyclic quiver
- `FiniteAcyclicPresentation`: An acyclic presentation where the generators
  and generator morphisms are finite

## Special properties of acyclic presentations

Acyclic categories have special properties that may simplify working with
presentations:

1. **Well-founded paths**: The acyclicity condition means paths have bounded
   length, enabling well-founded induction
2. **Unique normal forms**: In the absence of non-trivial relations, each
   morphism may have a unique expression as a path
3. **Decidability**: For finite acyclic presentations, equality of morphisms
   may be decidable

-/

namespace GebLean

open CategoryTheory Quiver

universe v u

/-- An acyclic category presentation is a category presentation where the
    generators form an acyclic quiver. It includes a witness of acyclicity
    for the quiver structure provided by the base presentation. -/
structure AcyclicPresentation extends CategoryPresentation.{v, u} where
  /-- Witness that the generators form an acyclic quiver -/
  generatorAcyclicWitness :
    let _ := generatorQuiver
    AcyclicQuiverWitness generators (homSetOfQuiver generators)

namespace AcyclicPresentation

variable (P : AcyclicPresentation.{v, u})

/-- Provide the topological order instance from the acyclicity witness -/
instance : PartialOrder P.generators := P.generatorAcyclicWitness.order

/-- Provide the QuiverEdgesIncrease instance from the acyclicity witness -/
instance : QuiverEdgesIncrease P.generators (homSetOfQuiver P.generators) :=
  P.generatorAcyclicWitness.edgesIncrease

end AcyclicPresentation

/-- A finite acyclic category presentation is an acyclic presentation where
    the generators form a finite quiver. -/
structure FiniteAcyclicPresentation extends AcyclicPresentation.{v, u} where
  generatorFinQuiver : FinQuiverWitness generators (homSetOfQuiver generators)

namespace FiniteAcyclicPresentation

variable (P : FiniteAcyclicPresentation.{v, u})

/-- Make the vertex fintype instance available -/
instance : Fintype P.generators :=
  let data := P.generatorFinQuiver.fintypeVertex
  ⟨data.toFinset, data.complete⟩

/-- Make the edge fintype instance available -/
instance (X Y : P.generators) : Fintype (X ⟶ Y) :=
  let data := P.generatorFinQuiver.fintypeEdge X Y
  ⟨data.toFinset, data.complete⟩

end FiniteAcyclicPresentation

/-- A finite acyclic presentation with decidable generating relations.
    This extension is needed for constructive Fintype instances on the quotient
    category. -/
structure FiniteAcyclicDecidablePresentation extends FiniteAcyclicPresentation.{v, u} where
  /-- Decidability for the generating relations -/
  generatorRelationsDecEq : let _ := generatorQuiver;
    ∀ {a b : generators} (f g : Quiver.Path a b), Decidable (relations f g)

namespace FiniteAcyclicDecidablePresentation

variable (P : FiniteAcyclicDecidablePresentation.{v, u})

/-- Make the relation decidability available as an instance -/
instance : let _ := P.generatorQuiver;
    ∀ {a b : P.generators} (f g : Quiver.Path a b),
      Decidable (P.relations f g) :=
  P.generatorRelationsDecEq

/-!
### Constructive Decidability

For `FiniteAcyclicDecidablePresentation`, we provide a fully constructive
implementation of decidability for quotient morphism equality.

The current implementation is incomplete. The full approach would be:

1. **CompClosure decidability**: Enumerate all factorizations of paths and check
   if any match with related middle edges.

2. **EqvGen decidability**: Compute equivalence closure iteratively using
   fixed-point iteration on the finite set of paths. Since paths are bounded
   in finite acyclic quivers, this terminates.

3. **Quotient DecidableEq**: Use the decidable `EqvGen (CompClosure r)` to
   provide `DecidableEq` for `Quot (CompClosure r)`.

4. **Fintype.ofSurjective**: With decidable equality, use the standard
   constructive `Fintype.ofSurjective`.

This is left as future work, as the full implementation requires substantial
infrastructure for decidability of equivalence closure.-/

end FiniteAcyclicDecidablePresentation

/-!
## Fundamental properties of acyclic presentations

We prove that acyclicity and finiteness are preserved through the presentation
construction.

### Acyclic presentations produce acyclic categories

In an acyclic quiver, there are no non-trivial cycles. This means:
1. The free semicategory consists of non-empty paths (non-nil)
2. Adjoining identities (nil paths) gives the free category (all paths)
3. In the acyclic case, the free category is just `Paths V` from mathlib
4. Quotienting by relations preserves acyclicity

### Construction Steps

1. **Free semicategory**: Non-nil paths on acyclic quiver form acyclic semicategory
2. **Adjoin identities**: Adding nil paths preserves acyclicity (nil doesn't violate order)
3. **Quotient**: Quotienting preserves acyclicity (same objects, fewer morphisms)
4. **Result**: Presented category is acyclic
-/

/-- In an acyclic quiver, any non-empty path goes from a smaller to a larger vertex.
This uses path_increases from AcyclicQuiver.lean. -/
theorem path_increases_for_nonempty {V : Type u} [inst : AcyclicQuiver V]
    {a b : V} (p : Quiver.Path a b) :
    (∀ (h : a = b), p = Eq.recOn h Quiver.Path.nil) ∨ a < b := by
  cases p with
  | nil => left; intro h; rfl
  | cons p' f =>
    right
    have := @AcyclicQuiver.path_increases V inst _ _ _ p' f
    exact this

/-!
## Acyclic structures and semicategories

Acyclic structures naturally live at the semicategory level, not the category
level. The reason is that identity morphisms violate the `edgesIncrease`
condition since `a < a` is false (irreflexive). Thus the construction goes:

1. **Free semicategory**: Non-nil paths in an acyclic quiver form an acyclic
   semicategory. The `path_increases_for_nonempty` theorem shows that
   any non-empty path goes from a smaller to a larger vertex.

2. **Adjoin identities**: We adjoin nil paths (identities) to get the free
   category. In the acyclic case, this adjunction is trivial because there
   are no non-identity morphisms with the same domain and codomain.

3. **Isomorphism to mathlib's Paths**: The free category on an acyclic
   quiver (our semicategory + adjoined identities) should be isomorphic to
   mathlib's `Paths V`.

4. **Quotient preserves acyclicity**: Quotienting by relations preserves
   acyclicity because it only identifies morphisms, never creates new ones.
-/

/-- The category presented by an acyclic presentation inherits order on objects.

Note: Paths P.generators = P.generators definitionally, and P.generators has
a PartialOrder from P.generatorAcyclic. The quotient inherits this order.

This doesn't make it an AcyclicQuiver because identity morphisms exist.
We need to work at the semicategory level or redefine acyclic categories.
-/
instance acyclicPresentationOrder (P : AcyclicPresentation.{v, u}) :
    PartialOrder P.toCategory where
  le := fun x y => @LE.le P.generators P.generatorAcyclicWitness.order.toLE x.as y.as
  le_refl := fun x => @le_refl P.generators P.generatorAcyclicWitness.order.toPreorder x.as
  le_trans := fun x y z hxy hyz =>
    @le_trans P.generators P.generatorAcyclicWitness.order.toPreorder x.as y.as z.as hxy hyz
  le_antisymm := fun x y hxy hyx => by
    cases x; cases y
    congr
    exact @le_antisymm P.generators P.generatorAcyclicWitness.order _ _ hxy hyx

/-- The length of a path is the number of edges it contains. -/
def pathLength {V : Type u} [Quiver.{v + 1} V] {a b : V} :
    Quiver.Path a b → ℕ
  | .nil => 0
  | .cons p _ => pathLength p + 1

/-- Extract the list of vertices visited by a path (including start and end). -/
def pathVertices {V : Type u} [Quiver.{v + 1} V] {a b : V} :
    Quiver.Path a b → List V
  | .nil => [a]
  | .cons p _ => pathVertices p ++ [b]

/-- The vertices in a path from a to b include both a and b. -/
theorem pathVertices_nonempty {V : Type u} [Quiver.{v + 1} V] {a b : V}
    (p : Quiver.Path a b) : pathVertices p ≠ [] := by
  cases p <;> simp [pathVertices]

/-- All vertices in a path are at most the endpoint in the partial order. -/
theorem pathVertices_le_endpoint {V : Type u} [inst : AcyclicQuiver.{u, v} V]
    {a b : V} (p : Quiver.Path a b) (v : V) :
    v ∈ pathVertices p → v ≤ b := by
  induction p with
  | nil =>
    simp [pathVertices]
    intro h
    rw [h]
  | cons p' f ih =>
    simp [pathVertices]
    intro h
    cases h with
    | inl h' =>
      have v_le_mid : v ≤ _ := ih h'
      have mid_lt_b : _ := inst.edgesIncrease f
      exact le_trans v_le_mid (le_of_lt mid_lt_b)
    | inr h' =>
      rw [h']

/-- In an acyclic quiver, the vertices visited by a path are strictly increasing,
hence distinct. -/
theorem pathVertices_nodup {V : Type u} [inst : AcyclicQuiver.{u, v} V]
    {a b : V} (p : Quiver.Path a b) :
    (pathVertices p).Nodup := by
  induction p with
  | nil =>
    simp [pathVertices]
  | cons p' f ih =>
    rw [pathVertices]
    apply List.Nodup.append
    · exact ih
    · simp
    · intro v v_mem_p' v_mem_sing
      simp at v_mem_sing
      subst v_mem_sing
      have c_le_mid : _ ≤ _ := pathVertices_le_endpoint p' _ v_mem_p'
      have mid_lt_c : _ < _ := inst.edgesIncrease f
      exact lt_irrefl _ (lt_of_le_of_lt c_le_mid mid_lt_c)

/-- The length of pathVertices is pathLength + 1. -/
theorem pathVertices_length {V : Type u} [Quiver.{v + 1} V] {a b : V}
    (p : Quiver.Path a b) :
    (pathVertices p).length = pathLength p + 1 := by
  induction p with
  | nil => simp [pathVertices, pathLength]
  | cons p' _ ih =>
    rw [pathVertices, pathLength]
    simp only [List.length_append, List.length_singleton]
    rw [ih]

/-- In a finite acyclic quiver, any path has length bounded by the total
number of vertices.

This is because acyclicity means we cannot visit the same vertex twice,
so a path can visit at most all vertices, giving at most n-1 edges for
n vertices. -/
theorem path_length_bounded {V : Type u} [inst : AcyclicQuiver.{u, v} V]
    [Fintype V] {a b : V} (p : Quiver.Path a b) :
    pathLength p < Fintype.card V := by
  have h_nodup : (pathVertices p).Nodup := pathVertices_nodup p
  have h_len : (pathVertices p).length = pathLength p + 1 := pathVertices_length p
  have h_card : (pathVertices p).length ≤ Fintype.card V :=
    List.Nodup.length_le_card h_nodup
  omega

/-- Decidable instance for path length comparison. -/
instance pathLengthDecidable {V : Type u} [Quiver.{v + 1} V]
    {a b : V} (p : Quiver.Path a b) (n : ℕ) :
    Decidable (pathLength p ≤ n) :=
  inferInstanceAs (Decidable (pathLength p ≤ n))

/-- Decidability for subtype of paths with bounded length.

Note: Lean's standard library provides `Quiver.Path.instDecidableEq` for paths
(from `Mathlib.Combinatorics.Quiver.Path`), which this instance uses via `decEq`.
Subtype decidability then follows automatically. -/
instance decEqBoundedPath {V : Type u} [Quiver.{v + 1} V]
    [DecidableEq V] [∀ a b : V, DecidableEq (a ⟶ b)]
    {a b : V} (n : ℕ) :
    DecidableEq {p : Quiver.Path a b // pathLength p ≤ n} :=
  fun ⟨p₁, _⟩ ⟨p₂, _⟩ =>
    match decEq p₁ p₂ with
    | isTrue h => isTrue (by cases h; rfl)
    | isFalse h => isFalse (fun eq => h (by cases eq; rfl))

/-! ### Finset-based path enumeration

Following mathlib's pattern (see `Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting`),
we separate the computational content (Finset construction) from the typeclass
(Fintype instance).

The pattern:
1. Define recursive `Finset` function (no typeclass issues)
2. Prove the finset is complete
3. Derive non-recursive `Fintype` instance via `Fintype.ofFinset` -/

/-- Finset of paths of bounded length in a quiver. This function recursively
constructs the set of all paths from `a` to `b` with length at most `n`.

Following mathlib's approach (see `SimpleGraph.finsetWalkLength`), this is a
direct `Finset` construction with no typeclass synthesis in the recursion. -/
def finsetPathsBounded {V : Type u} [Quiver.{v + 1} V] [Fintype V] [DecidableEq V]
    [∀ a b : V, DecidableEq (a ⟶ b)] [∀ a b : V, Fintype (a ⟶ b)]
    (a b : V) (n : ℕ) : Finset {p : Quiver.Path a b // pathLength p ≤ n} :=
  match n with
  | 0 =>
    if h : a = b then
      {⟨h ▸ Quiver.Path.nil, by subst h; simp [pathLength]⟩}
    else
      ∅
  | n + 1 =>
    let baseCase : Finset {p : Quiver.Path a b // pathLength p ≤ n + 1} :=
      if h : a = b then
        {⟨h ▸ Quiver.Path.nil, by subst h; simp [pathLength]⟩}
      else
        ∅
    let consCase : Finset {p : Quiver.Path a b // pathLength p ≤ n + 1} :=
      Finset.univ.biUnion fun (c : V) =>
        (finsetPathsBounded a c n).biUnion fun ⟨p, hp⟩ =>
          (Finset.univ : Finset (c ⟶ b)).map
            ⟨fun f => ⟨Quiver.Path.cons p f, by simp [pathLength]; omega⟩,
             fun f₁ f₂ h => by cases h; rfl⟩
    baseCase ∪ consCase

/-- The finset contains exactly the paths of bounded length. -/
theorem mem_finsetPathsBounded_iff {V : Type u} [Quiver.{v + 1} V] [Fintype V] [DecidableEq V]
    [∀ a b : V, DecidableEq (a ⟶ b)] [∀ a b : V, Fintype (a ⟶ b)]
    {a b : V} {n : ℕ} (p : {p : Quiver.Path a b // pathLength p ≤ n}) :
    p ∈ finsetPathsBounded a b n := by
  match n with
  | 0 =>
    cases p with | mk p hp =>
    rw [finsetPathsBounded]
    split
    · next h =>
      have : p = h ▸ Quiver.Path.nil := by
        cases p with
        | nil => rfl
        | cons _ _ => simp [pathLength] at hp
      simp [this]
    · cases p with
      | nil => contradiction
      | cons _ _ => simp [pathLength] at hp
  | n + 1 =>
    cases p with | mk p hp =>
    rw [finsetPathsBounded]
    cases p with
    | nil =>
      simp only [Finset.mem_union]
      left
      split
      · simp
      · contradiction
    | cons p' f =>
      simp only [Finset.mem_union,
        Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_map]
      right
      refine ⟨_, ⟨p', by simp [pathLength] at hp; omega⟩,
        mem_finsetPathsBounded_iff ⟨p', by simp [pathLength] at hp; omega⟩, f, rfl⟩

/-- Fintype instance for paths of bounded length, derived from the finset. -/
instance fintypePathsBounded {V : Type u} [Quiver.{v + 1} V] [Fintype V] [DecidableEq V]
    [∀ a b : V, DecidableEq (a ⟶ b)] [∀ a b : V, Fintype (a ⟶ b)]
    (a b : V) (n : ℕ) : Fintype {p : Quiver.Path a b // pathLength p ≤ n} :=
  ⟨finsetPathsBounded a b n, fun p => mem_finsetPathsBounded_iff p⟩

/-- In a finite acyclic quiver, paths between any two vertices form a finite type.

This uses the fact that all paths have length bounded by the number of vertices
(acyclicity prevents revisiting vertices), combined with the constructive
enumeration of bounded-length paths.

Note: This uses `Fintype.ofEquiv` to transport the fintype instance from
bounded paths to all paths (they're equal by the bound). -/
def finite_paths_in_finite_acyclic_quiver
    (V : Type u) [inst : AcyclicQuiver.{u, v} V] (instFin : Fintype V)
    (decEqV : DecidableEq V) (fintypeEdge : ∀ a b : V, Fintype (a ⟶ b))
    (decEqEdge : ∀ a b : V, DecidableEq (a ⟶ b)) (a b : V) :
    Fintype (Quiver.Path a b) := by
  haveI := instFin
  haveI := decEqV
  haveI := fintypeEdge
  haveI := decEqEdge
  exact Fintype.ofEquiv {p : Quiver.Path a b // pathLength p ≤ Fintype.card V} {
    toFun := fun ⟨p, _⟩ => p
    invFun := fun p => ⟨p, Nat.le_of_lt (path_length_bounded p)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }

/-!
## Special properties and potential theorems

This section outlines properties that may be provable for acyclic presentations.
These are left as future work.

### Path length bounds

In an acyclic quiver with n vertices, any path has length at most n-1.
This could be formalized as:

```lean
theorem path_length_bounded (P : FiniteAcyclicPresentation) :
  ∀ {X Y : P.generators} (p : Path X Y),
    p.length < Fintype.card P.generators
```

### Decidable equality (with trivial relations)

For finite acyclic presentations with no relations (free category), morphism
equality should be decidable:

```lean
instance decidableEq_trivial (P : FiniteAcyclicPresentation)
    (h : P.relations = fun _ _ _ _ => False) :
  ∀ (X Y : P.toCategory), DecidableEq (X ⟶ Y)
```

### Normal form existence

In an acyclic presentation, we might be able to define a normal form for
morphisms and prove that every morphism has a unique normal form modulo
the relations.

-/

end GebLean

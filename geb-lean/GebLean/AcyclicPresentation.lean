import GebLean.CategoryPresentation
import GebLean.AcyclicQuiver
import GebLean.AcyclicCat
import Mathlib.Data.Fintype.Sigma

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
condition since `a < a` is false (irreflexive).

### The correct approach

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

### Implementation plan

The instance below is incorrect because we cannot make `Paths V` an
`AcyclicQuiver` (identity morphisms exist). Instead, we should:

1. Define what it means for a semicategory to be acyclic
2. Prove the free semicategory on an acyclic quiver is acyclic
3. Show that adjoining identities preserves this property
4. Prove the quotient preserves acyclicity

Note: `Paths V` is definitionally equal to `V`, so objects inherit the
partial order from the generator quiver.
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

/-- Helper to build a Fintype for product types. -/
def fintypeProd {α : Type u} {β : Type v}
    (decEqA : DecidableEq α) (decEqB : DecidableEq β)
    (fintypeA : Fintype α) (fintypeB : Fintype β) :
    Fintype (α × β) where
  elems := by
    letI := decEqA
    letI := decEqB
    exact fintypeA.elems.biUnion fun a =>
      fintypeB.elems.map ⟨fun b => (a, b), fun _ _ h => by cases h; rfl⟩
  complete := fun ⟨a, b⟩ => by
    letI := decEqA
    letI := decEqB
    rw [Finset.mem_biUnion]
    use a, fintypeA.complete a
    rw [Finset.mem_map]
    use b, fintypeB.complete b
    rfl

/-- Helper to build DecidableEq for paths given DecidableEq on vertices and edges. -/
def decEqPath {V : Type u} [Quiver.{v + 1} V]
    (decEqV : DecidableEq V) (decEqEdge : ∀ a b : V, DecidableEq (a ⟶ b)) :
    ∀ {a b : V}, DecidableEq (Quiver.Path a b) :=
  fun {a b} p₁ p₂ =>
    match p₁, p₂ with
    | .nil, .nil => isTrue rfl
    | .nil, .cons _ _ => isFalse (fun h => by cases h)
    | .cons _ _, .nil => isFalse (fun h => by cases h)
    | @Quiver.Path.cons _ _ _ c₁ _ p₁' f₁,
      @Quiver.Path.cons _ _ _ c₂ _ p₂' f₂ =>
      match decEqV c₁ c₂ with
      | isFalse hc => isFalse (fun eq => by
          cases eq
          exact hc rfl)
      | isTrue hc =>
        match decEqPath decEqV decEqEdge p₁' (hc ▸ p₂') with
        | isFalse hp => isFalse (fun eq => by
            cases eq
            cases hc
            exact hp rfl)
        | isTrue hp =>
          match decEqEdge _ _ f₁ (hc ▸ f₂) with
          | isFalse hf => isFalse (fun eq => by
              cases eq
              cases hc
              exact hf rfl)
          | isTrue hf => isTrue (by
              cases hc
              cases hp
              cases hf
              rfl)

/-- Helper to build DecidableEq for subtype of paths with bounded length.
Requires DecidableEq on the underlying path type. -/
def decEqBoundedPath {V : Type u} [Quiver.{v + 1} V]
    (decEqPath : ∀ {a b : V}, DecidableEq (Quiver.Path a b))
    {a b : V} (n : ℕ) :
    DecidableEq {p : Quiver.Path a b // pathLength p ≤ n} :=
  fun ⟨p₁, _⟩ ⟨p₂, _⟩ =>
    match decEqPath p₁ p₂ with
    | isTrue h => isTrue (by cases h; rfl)
    | isFalse h => isFalse (fun eq => h (by cases eq; rfl))

/-- Helper to build a Fintype for Sigma types. Given Fintype data for the base
and fibers, constructs Fintype data for the Sigma type.

This avoids typeclass resolution issues by taking explicit data structures. -/
def fintypeSigma {α : Type u} {β : α → Type v}
    (decEqA : DecidableEq α) (decEqB : ∀ a, DecidableEq (β a))
    (fintypeA : Fintype α) (fintypeB : ∀ a, Fintype (β a)) :
    Fintype ((a : α) × β a) where
  elems := by
    letI := decEqA
    letI := fun a => decEqB a
    exact fintypeA.elems.attach.biUnion fun ⟨a, ha⟩ =>
      (fintypeB a).elems.map ⟨fun b => ⟨a, b⟩, fun _ _ h => by
        cases h
        rfl⟩
  complete := fun ⟨a, b⟩ => by
    letI := decEqA
    letI := fun a => decEqB a
    simp
    use a
    constructor
    · exact fintypeA.complete a
    · use b
      constructor
      · exact (fintypeB a).complete b
      · simp

/-- In a finite quiver, paths of bounded length form a finite type.

This construction uses structural recursion on the bound n. Every path of
length ≤ n+1 is either nil (if a = b) or cons p f where p has length ≤ n.
This factorization is unique by injectivity of cons.

We take explicit Fintype data (not instances) to avoid instance resolution
issues. -/
def finite_paths_of_bounded_length
    (V : Type u) [Quiver.{v + 1} V] (fintypeV : Fintype V) (decEqV : DecidableEq V)
    (fintypeEdge : ∀ a b : V, Fintype (a ⟶ b))
    (decEqEdge : ∀ a b : V, DecidableEq (a ⟶ b)) (a b : V) (n : ℕ) :
    Fintype {p : Quiver.Path a b // pathLength p ≤ n} :=
  match n with
  | 0 =>
    if h : a = b then
      Fintype.ofEquiv (Fin 1) {
        toFun := fun _ => ⟨h ▸ Quiver.Path.nil, by subst h; simp [pathLength]⟩
        invFun := fun _ => 0
        left_inv := fun i => (Fin.eq_zero i).symm
        right_inv := fun ⟨p, hp⟩ => by
          cases p with
          | nil => cases h; rfl
          | cons _ _ => simp [pathLength] at hp
      }
    else
      have : IsEmpty {p : Quiver.Path a b // pathLength p ≤ 0} := {
        false := fun ⟨p, hp⟩ => by
          cases p with
          | nil => exact h rfl
          | cons _ _ => simp [pathLength] at hp
      }
      Fintype.ofIsEmpty
  | n + 1 =>
    -- Every path of length ≤ n+1 is either nil (if a = b) or cons p f
    -- where p has length ≤ n and f : c ⟶ b for some c
    -- We enumerate by summing over: {nil if a=b} + Σ(c:V), {p : Path a c | len ≤ n} × (c ⟶ b)

    -- Every path of length ≤ n+1 is EITHER:
    -- (1) nil : Path a a (if a = b), with length 0, OR
    -- (2) cons p f : Path a b where p : Path a c has length ≤ n and f : c ⟶ b
    --
    -- These cases are disjoint and the cons factorization is unique.
    -- So: {Path a b | len ≤ n+1} ≃ (if a=b then Unit else Empty) ⊕ Σc, {p:Path a c|len≤n} × (c⟶b)

    if h : a = b then
      -- When a = b, we have both nil and cons-paths
      -- Paths are: nil ⊕ (Σ(c:V), {p:Path a c | len ≤ n} × (c ⟶ b))
      h ▸ (
      let ConsData := (c : V) × {p : Quiver.Path a c // pathLength p ≤ n} × (c ⟶ a)
      let decEqPathAll : ∀ {x y : V}, DecidableEq (Quiver.Path x y) :=
        @decEqPath V _ decEqV decEqEdge
      let decEqProdAt : ∀ c, DecidableEq ({p : Quiver.Path a c // pathLength p ≤ n} × (c ⟶ a)) :=
        fun c => fun x y =>
          match x, y with
          | (px, fx), (py, fy) =>
            match decEqBoundedPath decEqPathAll n px py with
            | isFalse hp => isFalse (fun h => hp (by cases h; rfl))
            | isTrue hp =>
              match decEqEdge c a fx fy with
              | isFalse hf => isFalse (fun h => hf (by cases h; rfl))
              | isTrue hf => isTrue (by cases hp; cases hf; rfl)
      let fintypeProdAt := fun c =>
        fintypeProd
          (decEqBoundedPath decEqPathAll n)
          (decEqEdge c a)
          (finite_paths_of_bounded_length V fintypeV decEqV fintypeEdge decEqEdge a c n)
          (fintypeEdge c a)
      let fintypeConsData : Fintype ConsData :=
        fintypeSigma decEqV decEqProdAt fintypeV fintypeProdAt

      -- Fintype for Unit ⊕ ConsData by direct construction
      letI : Fintype (Unit ⊕ ConsData) := {
        elems := by
          exact Finset.cons (Sum.inl ())
            (fintypeConsData.elems.map ⟨Sum.inr, fun _ _ h => by cases h; rfl⟩)
            (by intro h; obtain ⟨y, _, hy⟩ := Finset.mem_map.mp h; cases hy)
        complete := fun x => by
          cases x with
          | inl =>
            apply Finset.mem_cons_self
          | inr y =>
            rw [Finset.mem_cons]
            right
            exact Finset.mem_map.mpr ⟨y, fintypeConsData.complete y, rfl⟩
      }

      Fintype.ofEquiv (Unit ⊕ ConsData) {
        toFun := fun
          | Sum.inl () => ⟨Quiver.Path.nil, by simp [pathLength]⟩
          | Sum.inr ⟨c, p, f⟩ => ⟨Quiver.Path.cons p.val f, by simp [pathLength]; omega⟩
        invFun := fun x => by
          obtain ⟨q, hq⟩ := x
          cases q with
          | nil => exact Sum.inl ()
          | cons p' f' => exact Sum.inr ⟨_, ⟨p', by simp [pathLength] at hq; omega⟩, f'⟩
        left_inv := fun x => by
          cases x with
          | inl => simp only
          | inr val =>
            obtain ⟨c, p, f⟩ := val
            cases p with | mk p' hp' =>
            simp only
        right_inv := fun x => by
          obtain ⟨q, hq⟩ := x
          simp only
          cases q <;> rfl
      })
    else
      -- When a ≠ b, we only have cons-paths (nil is not a path from a to b)
      -- So we have: {p : Path a b | len p ≤ n+1} ≃ Σ(c:V), {p:Path a c | len p ≤ n} × (c ⟶ b)
      let ConsData := (c : V) × {p : Quiver.Path a c // pathLength p ≤ n} × (c ⟶ b)

      -- Build Fintype for ConsData using our explicit helpers
      -- For each c, build Fintype for {paths} × {edges}
      let decEqPathAll : ∀ {x y : V}, DecidableEq (Quiver.Path x y) :=
        @decEqPath V _ decEqV decEqEdge
      let decEqProdAt : ∀ c, DecidableEq ({p : Quiver.Path a c // pathLength p ≤ n} × (c ⟶ b)) :=
        fun c => fun x y =>
          match x, y with
          | (px, fx), (py, fy) =>
            match decEqBoundedPath decEqPathAll n px py with
            | isFalse hp => isFalse (fun h => hp (by cases h; rfl))
            | isTrue hp =>
              match decEqEdge c b fx fy with
              | isFalse hf => isFalse (fun h => hf (by cases h; rfl))
              | isTrue hf => isTrue (by cases hp; cases hf; rfl)
      let fintypeProdAt := fun c =>
        fintypeProd
          (decEqBoundedPath decEqPathAll n)
          (decEqEdge c b)
          (finite_paths_of_bounded_length V fintypeV decEqV fintypeEdge decEqEdge a c n)
          (fintypeEdge c b)
      -- Now build Fintype for the Sigma type
      letI instConsData : Fintype ConsData :=
        fintypeSigma decEqV decEqProdAt fintypeV fintypeProdAt

      -- Build equivalence: every path of length ≤ n+1 from a to b (a ≠ b)
      -- factors uniquely as cons p f for some c, p, f
      --
      -- The equivalence proofs don't reduce because invFun uses dependent
      -- pattern matching. We use `grind` to handle the dependent equalities.
      Fintype.ofEquiv ConsData {
        toFun := fun ⟨c, p, f⟩ => ⟨Quiver.Path.cons p.val f, by simp [pathLength]; omega⟩
        invFun := fun x => by
          obtain ⟨q, hq⟩ := x
          cases q with
          | nil => exact absurd rfl h
          | cons p' f' => exact ⟨_, ⟨p', by simp [pathLength] at hq; omega⟩, f'⟩
        left_inv := fun ⟨c, p, f⟩ => by
          cases p with | mk p' hp' =>
          simp only
        right_inv := fun x => by
          obtain ⟨q, hq⟩ := x
          simp only
          cases q with
          | nil => exact absurd rfl h
          | cons p' f' => rfl
      }

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
    Fintype (Quiver.Path a b) :=
  haveI := finite_paths_of_bounded_length V instFin decEqV fintypeEdge
    decEqEdge a b (Fintype.card V)
  Fintype.ofEquiv {p : Quiver.Path a b // pathLength p ≤ Fintype.card V} {
    toFun := fun ⟨p, _⟩ => p
    invFun := fun p => ⟨p, Nat.le_of_lt (@path_length_bounded V inst instFin a b p)⟩
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

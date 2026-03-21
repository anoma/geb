import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic

/-!
# Comonad Bar Resolution

For a comonad `G` on a category `C` and an object
`X : C`, the bar resolution `B_•(G, X)` is a
simplicial object with `B_n = G^{n+1}(X)`.  Face maps
apply the counit `ε` at successive depths, and
degeneracy maps apply the comultiplication `δ`.  The
simplicial identities follow from the comonad laws.
-/

namespace CategoryTheory

universe v u

namespace SimplexCategory

/--
For an order-preserving map with a strictly smaller
domain, there is an element in the codomain not in
the range.
-/
theorem exists_not_mem_range_of_lt
    {m n : ℕ}
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (h : m < n) :
    ∃ j : Fin (n + 1),
      ∀ i : Fin (m + 1),
        f.toOrderHom i ≠ j := by
  by_contra hall
  push_neg at hall
  have hsurj : Function.Surjective f.toOrderHom :=
    fun j =>
      ⟨(hall j).choose, (hall j).choose_spec⟩
  have := Fintype.card_le_of_surjective _ hsurj
  simp at this
  omega

/--
For an order-preserving map with a strictly larger
domain, there exists a "flat spot": consecutive
elements with equal values.
-/
theorem exists_flatSpot_of_gt
    {m n : ℕ}
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (h : n < m) :
    ∃ i : Fin m,
      f.toOrderHom i.castSucc =
        f.toOrderHom i.succ := by
  by_contra hall
  push_neg at hall
  have hstrictMono : StrictMono f.toOrderHom :=
    Fin.strictMono_iff_lt_succ.mpr (fun i =>
      lt_of_le_of_ne
        (f.toOrderHom.monotone
          (Fin.castSucc_le_succ i))
        (hall i))
  have hinj : Function.Injective f.toOrderHom :=
    hstrictMono.injective
  have := Fintype.card_le_of_injective _ hinj
  simp at this
  omega

/--
Given `f : [m] → [n+1]` and `j` not in the range of
`f`, produce `[m] → [n]` by composing with the
degeneracy that collapses `j`.  Satisfies
`skipValue f j hj ≫ δ j = f`.
-/
def skipValue
    {m n : ℕ}
    (f : SimplexCategory.mk m ⟶
      SimplexCategory.mk (n + 1))
    (j : Fin (n + 2))
    (_ : ∀ i : Fin (m + 1),
      f.toOrderHom i ≠ j) :
    SimplexCategory.mk m ⟶ SimplexCategory.mk n :=
  SimplexCategory.factor_δ f j

/--
Given `f : [m+1] → [n]` and a flat spot `i` (where
`f(i) = f(i+1)`), produce `[m] → [n]` by merging
the consecutive equal values.
-/
def mergeFlat
    {m n : ℕ}
    (f : SimplexCategory.mk (m + 1) ⟶
      SimplexCategory.mk n)
    (i : Fin (m + 1))
    (_ : f.toOrderHom i.castSucc =
      f.toOrderHom i.succ) :
    SimplexCategory.mk m ⟶ SimplexCategory.mk n :=
  SimplexCategory.δ i.succ ≫ f

end SimplexCategory

variable {C : Type u} [Category.{v} C]

namespace Comonad

variable (G : Comonad C) (X : C)

/--
Iterated application of a comonad's underlying
endofunctor: `iterateObj G X n = G^n(X)`.
-/
def iterateObj : ℕ → C
  | 0 => X
  | n + 1 => G.toFunctor.obj (iterateObj n)

@[simp]
lemma iterateObj_zero :
    iterateObj G X 0 = X :=
  rfl

@[simp]
lemma iterateObj_succ (n : ℕ) :
    iterateObj G X (n + 1) =
      G.toFunctor.obj (iterateObj G X n) :=
  rfl

variable {X} {Y : C}

/--
Functoriality of iterated comonad application in the
object argument: given `f : X ⟶ Y`, produce
`G^n(f) : G^n(X) ⟶ G^n(Y)`.
-/
def iterateMap (f : X ⟶ Y) : (n : ℕ) →
    iterateObj G X n ⟶ iterateObj G Y n
  | 0 => f
  | n + 1 => G.toFunctor.map (iterateMap f n)

@[simp]
lemma iterateMap_zero (f : X ⟶ Y) :
    iterateMap G f 0 = f :=
  rfl

@[simp]
lemma iterateMap_succ (f : X ⟶ Y) (n : ℕ) :
    iterateMap G f (n + 1) =
      G.toFunctor.map (iterateMap G f n) :=
  rfl

variable (X)

/--
Face map for the bar resolution at depth `i`.
Applies the counit `ε` at the `i`-th position in
`G^{n+2}(X)`, producing `G^{n+1}(X)`.

The bar resolution level `n` is
`iterateObj G X (n + 1)`.
-/
def barFace :
    (n : ℕ) → Fin (n + 2) →
      (iterateObj G X (n + 2) ⟶
        iterateObj G X (n + 1))
  | _, ⟨0, _⟩ =>
    G.ε.app (iterateObj G X _)
  | 0, ⟨_ + 1, _⟩ =>
    G.toFunctor.map
      (G.ε.app (iterateObj G X 0))
  | n + 1, ⟨i + 1, hi⟩ =>
    G.toFunctor.map
      (barFace n
        ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

/--
Degeneracy map for the bar resolution at depth `i`.
Applies the comultiplication `δ` at the `i`-th
position in `G^{n+1}(X)`, producing `G^{n+2}(X)`.
-/
def barDegen :
    (n : ℕ) → Fin (n + 1) →
      (iterateObj G X (n + 1) ⟶
        iterateObj G X (n + 2))
  | _, ⟨0, _⟩ =>
    G.δ.app (iterateObj G X _)
  | n + 1, ⟨i + 1, hi⟩ =>
    G.toFunctor.map
      (barDegen n
        ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

/-! ### Simplicial identities -/

lemma barFace_zero (n : ℕ) :
    barFace G X n ⟨0, Nat.zero_lt_succ _⟩ =
      G.ε.app (iterateObj G X (n + 1)) :=
  by cases n <;> rfl

lemma barDegen_zero (n : ℕ) :
    barDegen G X n ⟨0, Nat.zero_lt_succ _⟩ =
      G.δ.app (iterateObj G X n) :=
  by cases n <;> rfl

lemma barFace_succ (n : ℕ)
    (i : ℕ) (hi : i + 1 < n + 1 + 2) :
    barFace G X (n + 1)
      ⟨i + 1, hi⟩ =
      G.toFunctor.map
        (barFace G X n
          ⟨i, by omega⟩) := by
  rfl

lemma barDegen_succ (n : ℕ)
    (i : ℕ) (hi : i + 1 < n + 1 + 1) :
    barDegen G X (n + 1)
      ⟨i + 1, hi⟩ =
      G.toFunctor.map
        (barDegen G X n
          ⟨i, by omega⟩) := by
  rfl

lemma barFace_comp_barFace (n : ℕ)
    (i j : ℕ) (hij : i ≤ j)
    (hi : i < n + 2) (hj : j < n + 2) :
    barFace G X (n + 1) ⟨j + 1, by omega⟩ ≫
      barFace G X n ⟨i, hi⟩ =
    barFace G X (n + 1) ⟨i, by omega⟩ ≫
      barFace G X n ⟨j, hj⟩ := by
  induction n generalizing i j with
  | zero =>
    cases i with
    | zero =>
      erw [barFace_succ, barFace_zero,
        barFace_zero]
      exact @Comonad.counit_naturality C _ G
        (iterateObj G X 2) (iterateObj G X 1)
        (barFace G X 0 ⟨j, hj⟩)
    | succ i =>
      have : i = 0 := by omega
      have : j = 1 := by omega
      subst_vars
      erw [barFace_succ, barFace_succ,
        ← G.toFunctor.map_comp,
        ← G.toFunctor.map_comp]
      congr 1
      exact @Comonad.counit_naturality C _ G
        (iterateObj G X 1)
        (iterateObj G X 0)
        (G.ε.app X)
  | succ n ih =>
    cases i with
    | zero =>
      erw [barFace_succ, barFace_zero,
        barFace_zero]
      exact @Comonad.counit_naturality C _ G
        (iterateObj G X (n + 3))
        (iterateObj G X (n + 2))
        (barFace G X (n + 1) ⟨j, hj⟩)
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        erw [barFace_succ, barFace_succ,
          barFace_succ, barFace_succ,
          ← G.toFunctor.map_comp,
          ← G.toFunctor.map_comp]
        congr 1
        exact ih i j (by omega)
          (by omega) (by omega)

lemma barDegen_comp_barDegen (n : ℕ)
    (i j : ℕ) (hij : i ≤ j)
    (hi : i < n + 1) (hj : j < n + 1) :
    barDegen G X n ⟨i, hi⟩ ≫
      barDegen G X (n + 1) ⟨j + 1, by omega⟩ =
    barDegen G X n ⟨j, hj⟩ ≫
      barDegen G X (n + 1) ⟨i, by omega⟩ := by
  induction n generalizing i j with
  | zero =>
    have : i = 0 := by omega
    have : j = 0 := by omega
    subst_vars
    erw [barDegen_zero, barDegen_zero,
      barDegen_succ, barDegen_zero]
    exact G.coassoc (iterateObj G X 0)
  | succ n ih =>
    cases i with
    | zero =>
      cases j with
      | zero =>
        erw [barDegen_zero, barDegen_zero,
          barDegen_succ, barDegen_zero]
        exact G.coassoc (iterateObj G X (n + 1))
      | succ j =>
        erw [barDegen_zero, barDegen_succ,
          barDegen_succ, barDegen_zero]
        exact (@Comonad.delta_naturality C _ G
          (iterateObj G X (n + 1))
          (iterateObj G X (n + 2))
          (barDegen G X n
            ⟨j, by omega⟩)).symm
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        erw [barDegen_succ, barDegen_succ,
          barDegen_succ, barDegen_succ,
          ← G.toFunctor.map_comp,
          ← G.toFunctor.map_comp]
        congr 1
        exact ih i j (by omega)
          (by omega) (by omega)

lemma barDegen_comp_barFace_self (n : ℕ)
    (j : ℕ) (hj : j < n + 1) :
    barDegen G X n ⟨j, hj⟩ ≫
      barFace G X n ⟨j, by omega⟩ =
    𝟙 (iterateObj G X (n + 1)) := by
  induction n generalizing j with
  | zero =>
    have : j = 0 := by omega
    subst_vars
    erw [barDegen_zero, barFace_zero]
    exact G.left_counit (iterateObj G X 0)
  | succ n ih =>
    cases j with
    | zero =>
      erw [barDegen_zero, barFace_zero]
      exact G.left_counit (iterateObj G X (n + 1))
    | succ j =>
      erw [barDegen_succ, barFace_succ,
        ← G.toFunctor.map_comp]
      rw [ih j (by omega)]
      exact G.toFunctor.map_id _

lemma barDegen_comp_barFace_succ (n : ℕ)
    (j : ℕ) (hj : j < n + 1) :
    barDegen G X n ⟨j, hj⟩ ≫
      barFace G X n ⟨j + 1, by omega⟩ =
    𝟙 (iterateObj G X (n + 1)) := by
  induction n generalizing j with
  | zero =>
    have : j = 0 := by omega
    subst_vars
    exact G.right_counit (iterateObj G X 0)
  | succ n ih =>
    cases j with
    | zero =>
      erw [barDegen_zero, barFace_succ,
        barFace_zero]
      exact G.right_counit
        (iterateObj G X (n + 1))
    | succ j =>
      erw [barDegen_succ, barFace_succ,
        ← G.toFunctor.map_comp]
      rw [ih j (by omega)]
      exact G.toFunctor.map_id _

lemma barFace_comp_barDegen_lt (n : ℕ)
    (i j : ℕ) (hij : i ≤ j)
    (hi : i < n + 2) (hj : j < n + 1) :
    barDegen G X (n + 1) ⟨j + 1, by omega⟩ ≫
      barFace G X (n + 1) ⟨i, by omega⟩ =
    barFace G X n ⟨i, hi⟩ ≫
      barDegen G X n ⟨j, hj⟩ := by
  induction n generalizing i j with
  | zero =>
    have : i = 0 := by omega
    have : j = 0 := by omega
    subst_vars
    erw [barDegen_succ, barFace_zero,
      barFace_zero]
    exact @Comonad.counit_naturality C _ G
      (iterateObj G X 1)
      (iterateObj G X 2)
      (barDegen G X 0
        ⟨0, by omega⟩)
  | succ n ih =>
    cases i with
    | zero =>
      erw [barDegen_succ, barFace_zero,
        barFace_zero]
      exact @Comonad.counit_naturality C _ G
        (iterateObj G X (n + 2))
        (iterateObj G X (n + 3))
        (barDegen G X (n + 1)
          ⟨j, by omega⟩)
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        erw [barDegen_succ, barFace_succ,
          barFace_succ, barDegen_succ,
          ← G.toFunctor.map_comp,
          ← G.toFunctor.map_comp]
        congr 1
        exact ih i j (by omega)
          (by omega) (by omega)

lemma barFace_comp_barDegen_gt (n : ℕ)
    (i j : ℕ) (hij : j < i)
    (hi : i < n + 2) (hj : j < n + 1) :
    barDegen G X (n + 1) ⟨j, by omega⟩ ≫
      barFace G X (n + 1) ⟨i + 1, by omega⟩ =
    barFace G X n ⟨i, hi⟩ ≫
      barDegen G X n ⟨j, hj⟩ := by
  induction n generalizing i j with
  | zero =>
    have : j = 0 := by omega
    have : i = 1 := by omega
    subst_vars
    erw [barDegen_zero, barFace_succ,
      barDegen_zero]
    exact (@Comonad.delta_naturality C _ G
      (iterateObj G X 1)
      (iterateObj G X 0)
      (G.ε.app (iterateObj G X 0))).symm
  | succ n ih =>
    cases j with
    | zero =>
      cases i with
      | zero => omega
      | succ i =>
        erw [barDegen_zero, barFace_succ,
          barFace_succ, barDegen_zero]
        exact (@Comonad.delta_naturality C _ G
          (iterateObj G X (n + 2))
          (iterateObj G X (n + 1))
          (barFace G X n
            ⟨i, by omega⟩)).symm
    | succ j =>
      cases i with
      | zero => omega
      | succ i =>
        erw [barDegen_succ, barFace_succ,
          ← G.toFunctor.map_comp,
          ih i j (by omega)
            (by omega) (by omega),
          G.toFunctor.map_comp,
          barFace_succ, barDegen_succ]

/-! ### Bar resolution map for arbitrary morphisms

The bar resolution map for a SimplexCategory morphism
is defined via the epi-mono factorization:
every morphism `f` factors uniquely as
`factorThruImage f ≫ image.ι f` (epi then mono).
The mono part composes face maps for missing codomain
values; the epi part composes degeneracy maps for flat
spots.
-/

/--
Bar resolution map for a morphism with `m ≤ n`:
composes face maps for missing codomain values.
-/
def barMapMono
    {m n : ℕ}
    (f : SimplexCategory.mk m ⟶
      SimplexCategory.mk n)
    (hle : m ≤ n) :
    iterateObj G X (n + 1) ⟶
      iterateObj G X (m + 1) :=
  if heq : m = n then
    eqToHom (by rw [heq])
  else
    have hlt : m < n := by omega
    match n, f with
    | n' + 1, f =>
      let hmiss :=
        SimplexCategory.exists_not_mem_range_of_lt
          f hlt
      let j := Fin.find
        (fun j => ∀ i, f.toOrderHom i ≠ j) hmiss
      have hj : ∀ i, f.toOrderHom i ≠ j :=
        Fin.find_spec hmiss
      barFace G X n' j ≫
        barMapMono
          (SimplexCategory.skipValue f j hj)
          (by omega)
termination_by n - m

/--
Bar resolution map for a morphism with `m ≥ n`:
composes degeneracy maps for flat spots.
-/
def barMapEpi
    {m n : ℕ}
    (f : SimplexCategory.mk m ⟶
      SimplexCategory.mk n)
    (hge : m ≥ n) :
    iterateObj G X (n + 1) ⟶
      iterateObj G X (m + 1) :=
  if heq : m = n then
    eqToHom (by rw [heq])
  else
    have hgt : n < m := by omega
    match m, f with
    | m' + 1, f =>
      let hflat :=
        SimplexCategory.exists_flatSpot_of_gt
          f hgt
      let i := Fin.find
        (fun i => f.toOrderHom i.castSucc =
          f.toOrderHom i.succ) hflat
      have hi : f.toOrderHom i.castSucc =
          f.toOrderHom i.succ :=
        Fin.find_spec hflat
      barMapEpi
        (SimplexCategory.mergeFlat f i hi)
        (by omega) ≫
        barDegen G X m' i
termination_by m - n

/--
The bar resolution map for an arbitrary SimplexCategory
morphism `f : [m] → [n]`, producing a morphism
`G^{n+1}(X) → G^{m+1}(X)`.

Defined by well-founded recursion on `m + n`:
- `m = n`: return `eqToHom` (identity transport)
- `m < n`: peel off a face map at the smallest
  missing value, then recurse
- `m > n`: peel off a degeneracy map at the smallest
  flat spot, then recurse
-/
def barSimplexMap
    {m n : ℕ}
    (f : SimplexCategory.mk m ⟶
      SimplexCategory.mk n) :
    iterateObj G X (n + 1) ⟶
      iterateObj G X (m + 1) :=
  if heq : m = n then
    eqToHom (by rw [heq])
  else if hlt : m < n then
    match n, f with
    | n' + 1, f =>
      let hmiss :=
        SimplexCategory.exists_not_mem_range_of_lt
          f hlt
      let j := Fin.find
        (fun j => ∀ i, f.toOrderHom i ≠ j) hmiss
      have hj := Fin.find_spec hmiss
      barFace G X n' j ≫
        barSimplexMap
          (SimplexCategory.skipValue f j hj)
  else
    have hgt : n < m := by omega
    match m, f with
    | m' + 1, f =>
      let hflat :=
        SimplexCategory.exists_flatSpot_of_gt
          f hgt
      let i := Fin.find
        (fun i => f.toOrderHom i.castSucc =
          f.toOrderHom i.succ) hflat
      have hi := Fin.find_spec hflat
      barSimplexMap
        (SimplexCategory.mergeFlat f i hi) ≫
        barDegen G X m' i
termination_by m + n
decreasing_by
  all_goals simp_all only [SimplexCategory.len_mk]
  all_goals omega

lemma barMapMono_eq_eqToHom
    {m n : ℕ}
    (f : SimplexCategory.mk m ⟶
      SimplexCategory.mk n)
    (hle : m ≤ n)
    (heq : m = n) :
    barMapMono G X f hle =
      eqToHom (by rw [heq]) := by
  unfold barMapMono
  simp [heq]

lemma barMapEpi_eq_eqToHom
    {m n : ℕ}
    (f : SimplexCategory.mk m ⟶
      SimplexCategory.mk n)
    (hge : m ≥ n)
    (heq : m = n) :
    barMapEpi G X f hge =
      eqToHom (by rw [heq]) := by
  unfold barMapEpi
  simp [heq]

lemma barSimplexMap_id (n : ℕ) :
    barSimplexMap G X
      (𝟙 (SimplexCategory.mk n)) =
      𝟙 (iterateObj G X (n + 1)) := by
  unfold barSimplexMap
  simp

/-! ### Bar resolution via generators and relations

The bar resolution is assembled as a functor from
`SimplexCategoryGenRelᵒᵖ` using `Quotient.lift`.
The face and degeneracy generators map to `barFace`
and `barDegen` (in `Cᵒᵖ`), and the simplicial
identities guarantee well-definedness on the quotient.
Functoriality (`map_comp`) is automatic.
-/

/--
Prefunctor from `FreeSimplexQuiver` to `Cᵒᵖ`
mapping `δ i` to `(barFace G X n i).op` and
`σ j` to `(barDegen G X n j).op`.
-/
def barQuiverMap :
    FreeSimplexQuiver ⥤q Cᵒᵖ where
  obj n :=
    Opposite.op (iterateObj G X (n.len + 1))
  map f := match f with
    | .δ i => (barFace G X _ i).op
    | .σ j => (barDegen G X _ j).op

/--
The bar resolution as a functor from
`SimplexCategoryGenRelᵒᵖ` to `C`, constructed
via `Quotient.lift`.  Functoriality (`map_comp`)
is guaranteed by the quotient construction; the
simplicial identities verify the quotient condition.
-/
def barResolution :
    SimplexCategoryGenRelᵒᵖ ⥤ C :=
  (Quotient.lift _
    (Paths.lift (barQuiverMap G X))
    (fun _ _ _ _ h => by
      set F := Paths.lift (barQuiverMap G X)
      match h with
      | FreeSimplexQuiver.homRel.δ_comp_δ H =>
        rw [F.map_comp, F.map_comp]
        dsimp [F]
        simp only [Paths.lift_toPath, barQuiverMap]
        rw [← op_comp, ← op_comp]
        exact congrArg Quiver.Hom.op
          (barFace_comp_barFace G X _ _ _
            (by exact H) (by exact Fin.is_lt _)
            (by exact Fin.is_lt _))
      | FreeSimplexQuiver.homRel.σ_comp_σ H =>
        rw [F.map_comp, F.map_comp]
        dsimp [F]
        simp only [Paths.lift_toPath,
          barQuiverMap]
        rw [← op_comp, ← op_comp]
        exact congrArg Quiver.Hom.op
          (barDegen_comp_barDegen G X _ _ _
            (by exact H) (by exact Fin.is_lt _)
            (by exact Fin.is_lt _)).symm
      | FreeSimplexQuiver.homRel.δ_comp_σ_self =>
        rw [F.map_comp, F.map_id]
        dsimp [F]
        simp only [Paths.lift_toPath,
          barQuiverMap]
        rw [← op_comp]
        exact congrArg Quiver.Hom.op
          (barDegen_comp_barFace_self G X _ _
            (by exact Fin.is_lt _))
      | FreeSimplexQuiver.homRel.δ_comp_σ_succ =>
        rw [F.map_comp, F.map_id]
        dsimp [F]
        simp only [Paths.lift_toPath,
          barQuiverMap]
        rw [← op_comp]
        exact congrArg Quiver.Hom.op
          (barDegen_comp_barFace_succ G X _ _
            (by exact Fin.is_lt _))
      | FreeSimplexQuiver.homRel.δ_comp_σ_of_le
            H =>
        rw [F.map_comp, F.map_comp]
        dsimp [F]
        simp only [Paths.lift_toPath,
          barQuiverMap]
        rw [← op_comp, ← op_comp]
        exact congrArg Quiver.Hom.op
          (barFace_comp_barDegen_lt G X _ _ _
            (by exact H) (by exact Fin.is_lt _)
            (by exact Fin.is_lt _))
      | FreeSimplexQuiver.homRel.δ_comp_σ_of_gt
            H =>
        rw [F.map_comp, F.map_comp]
        dsimp [F]
        simp only [Paths.lift_toPath,
          barQuiverMap]
        rw [← op_comp, ← op_comp]
        exact congrArg Quiver.Hom.op
          (barFace_comp_barDegen_gt G X _ _ _
            (by exact H) (by exact Fin.is_lt _)
            (by exact Fin.is_lt _))
      )).leftOp

end Comonad

end CategoryTheory

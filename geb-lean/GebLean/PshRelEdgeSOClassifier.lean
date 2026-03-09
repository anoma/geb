import GebLean.PshRelEdgeLimits
import Mathlib.CategoryTheory.Sites.Sieves

/-!
# Strong Subobject Classifier for the Edge Category

The vertical edge category `PshRelEdge C` is a
quasitopos: it does not have a full subobject
classifier, but it does have a strong subobject
classifier. A strong monomorphism in
`PshRelEdge C` is one where the relation on the
subobject is the restriction of the ambient
relation to the sub-presheaves. Such subobjects
are determined entirely by the pair of
source/target subfunctors.

The strong subobject classifier is
`(Ω, Ω, full)` where `Ω` is the sieve presheaf
(the subobject classifier of `PSh(C)`), and
`full` is the full relation on `Ω × Ω`. The
classifying morphism for a strong subobject
classifies the source and target subfunctors
independently.

## Main definitions

* `pshRelFullOf`: the full relation on any
  pair of presheaves
* `pshSievePresheaf`: the sieve presheaf
  `Ω : Cᵒᵖ ⥤ Type (max u v)`
* `pshSieveTrue`: the "true" morphism
  `1 → Ω` sending `* ↦ ⊤`
* `pshRelEdgeSOClassifier`: the strong
  subobject classifier edge `(Ω, Ω, full)`
* `pshRelEdgeSOTrue`: the "true" edge morphism
  from the terminal edge to the classifier
* `pshSieveClassifyingMap`: the classifying
  natural transformation for a subfunctor
* `pshRelEdgeSOClassify`: the classifying edge
  morphism for a strong sub-edge
-/

namespace GebLean

open CategoryTheory Limits

universe u v w

variable {C : Type u} [Category.{v} C]

/-- The full relation on a pair of presheaves:
all pairs are related at every stage. -/
def pshRelFullOf
    (P Q : Cᵒᵖ ⥤ Type w) :
    PshRel P Q where
  obj _ := Set.univ
  map _ _ _ := Set.mem_univ _

section SievePresheaf

variable (C : Type u) [Category.{v} C]

/-- The sieve presheaf
`Ω : Cᵒᵖ ⥤ Type (max u v)`. At each `c : Cᵒᵖ`,
this assigns the type of sieves on `c.unop` in
`C`. Given `f : c ⟶ d` in `Cᵒᵖ` (corresponding
to `f.unop : d.unop ⟶ c.unop` in `C`), the
action is pullback of sieves along `f.unop`. -/
def pshSievePresheaf :
    Cᵒᵖ ⥤ Type (max u v) where
  obj c := Sieve c.unop
  map f S := S.pullback f.unop
  map_id _ := by
    funext S
    simp [Sieve.pullback_id]
  map_comp {_ _ _} f g := by
    funext S
    simp [Sieve.pullback_comp]

/-- The "true" morphism `1 → Ω` in `PSh(C)`,
sending every element to the maximal sieve. -/
def pshSieveTrue :
    pshUnitPresheaf.{u, v, max u v} C ⟶
      pshSievePresheaf C where
  app c _ := (⊤ : Sieve c.unop)
  naturality _ _ _ := by
    funext _
    change (⊤ : Sieve _) = Sieve.pullback _ ⊤
    exact Sieve.pullback_top.symm

end SievePresheaf

section SOClassifier

variable (C : Type u) [Category.{v} C]

/-- The strong subobject classifier in
`PshRelEdge C`: the edge `(Ω, Ω, full)` where
`Ω` is the sieve presheaf and `full` is the
full relation (all pairs of sieves are
related). -/
def pshRelEdgeSOClassifier :
    PshRelEdge.{u, v, max u v} C :=
  { src := pshSievePresheaf C
    tgt := pshSievePresheaf C
    edge := pshRelFullOf
      (pshSievePresheaf C)
      (pshSievePresheaf C) }

/-- The "true" edge morphism from the terminal
edge to the strong subobject classifier. -/
def pshRelEdgeSOTrue :
    pshRelEdgeTerminal.{u, v, max u v} C ⟶
      pshRelEdgeSOClassifier C :=
  { srcMap := pshSieveTrue C
    tgtMap := pshSieveTrue C
    sq := fun _ _ _ _ => Set.mem_univ _ }

end SOClassifier

section ClassifyingMap

variable {C : Type u} [Category.{v} C]

/-- The classifying sieve for a subfunctor
`S : Subfunctor P` at an element `p : P.obj c`.
The sieve consists of all morphisms `f : d ⟶ c`
such that `P.map f p ∈ S.obj d`. -/
def pshClassifyingSieve
    {P : Cᵒᵖ ⥤ Type (max u v)}
    (S : Subfunctor P) (c : Cᵒᵖ)
    (p : P.obj c) : Sieve c.unop where
  arrows {d} f :=
    P.map f.op p ∈ S.obj (Opposite.op d)
  downward_closed {d e f} hf g := by
    rw [op_comp, FunctorToTypes.map_comp_apply]
    exact S.map g.op hf

/-- The classifying natural transformation for a
subfunctor `S : Subfunctor P`. Sends each element
`p : P.obj c` to its classifying sieve. -/
def pshClassifyingMap
    {P : Cᵒᵖ ⥤ Type (max u v)}
    (S : Subfunctor P) :
    P ⟶ pshSievePresheaf C where
  app c p := pshClassifyingSieve S c p
  naturality {c d} f := by
    funext p
    apply Sieve.ext
    intro e g
    simp only [types_comp_apply,
      pshClassifyingSieve, pshSievePresheaf,
      Sieve.pullback]
    have heq : P.map (g ≫ f.unop).op p =
        P.map g.op (P.map f p) := by
      simp [op_comp,
        FunctorToTypes.map_comp_apply]
    exact heq ▸ Iff.rfl

/-- The classifying sieve at `p` is maximal iff
`p` belongs to the subfunctor. -/
theorem pshClassifyingSieve_eq_top_iff
    {P : Cᵒᵖ ⥤ Type (max u v)}
    (S : Subfunctor P)
    (c : Cᵒᵖ) (p : P.obj c) :
    pshClassifyingSieve S c p = ⊤ ↔
      p ∈ S.obj c := by
  rw [← Sieve.id_mem_iff_eq_top]
  change P.map (𝟙 c.unop).op p ∈ S.obj _ ↔
    p ∈ S.obj c
  simp [FunctorToTypes.map_id_apply]

/-- The classifying edge morphism for a strong
sub-edge. Given subfunctors `SP ≤ E.src` and
`SQ ≤ E.tgt`, the classifying morphism sends
`E → (Ω, Ω, full)` by applying
`pshClassifyingMap` independently on source and
target. The relatedness condition is automatic
since the target edge has the full relation. -/
def pshRelEdgeSOClassify
    (E : PshRelEdge.{u, v, max u v} C)
    (SP : Subfunctor E.src)
    (SQ : Subfunctor E.tgt) :
    E ⟶ pshRelEdgeSOClassifier C :=
  { srcMap := pshClassifyingMap SP
    tgtMap := pshClassifyingMap SQ
    sq := fun _ _ _ _ => Set.mem_univ _ }

/-- The strong sub-edge of `E` determined by
subfunctors `SP ≤ E.src` and `SQ ≤ E.tgt`:
the edge whose source and target are restricted
to `SP` and `SQ`, and whose relation is the
restriction of `E.edge` to the sub-presheaves. -/
def pshRelEdgeStrongSub
    {E : PshRelEdge.{u, v, max u v} C}
    (SP : Subfunctor E.src)
    (SQ : Subfunctor E.tgt) :
    PshRelEdge.{u, v, max u v} C :=
  { src := SP.toFunctor
    tgt := SQ.toFunctor
    edge :=
      { obj := fun c =>
          { pq |
            (pq.1.val, pq.2.val) ∈
              E.edge.obj c }
        map := fun f ⟨⟨_, _⟩, ⟨_, _⟩⟩ h =>
          E.edge.map f h } }

/-- The inclusion from a strong sub-edge into the
ambient edge. -/
def pshRelEdgeStrongSubInclusion
    {E : PshRelEdge.{u, v, max u v} C}
    (SP : Subfunctor E.src)
    (SQ : Subfunctor E.tgt) :
    pshRelEdgeStrongSub SP SQ ⟶ E :=
  { srcMap := SP.ι
    tgtMap := SQ.ι
    sq := fun _ _ _ h => h }

/-- The classifying map sends the strong sub-edge
inclusion to "true": the inclusion composed with
the classifying map factors through the terminal
edge via the "true" morphism. -/
theorem pshRelEdgeSOClassify_pullback
    {E : PshRelEdge.{u, v, max u v} C}
    (SP : Subfunctor E.src)
    (SQ : Subfunctor E.tgt) :
    pshRelEdgeStrongSubInclusion SP SQ ≫
      pshRelEdgeSOClassify E SP SQ =
    pshRelEdgeTerminalMap _ ≫
      pshRelEdgeSOTrue C := by
  apply VertEdgeHom.ext
  · ext c ⟨p, hp⟩
    apply Sieve.ext
    intro d f
    simp only [
      pshRelEdgeStrongSubInclusion,
      pshRelEdgeSOClassify,
      pshClassifyingMap,
      pshRelEdgeTerminalMap,
      pshRelEdgeSOTrue,
      pshSieveTrue,
      pshClassifyingSieve, Subfunctor.ι]
    exact ⟨fun _ => trivial,
      fun _ => SP.map f.op hp⟩
  · ext c ⟨q, hq⟩
    apply Sieve.ext
    intro d f
    simp only [
      pshRelEdgeStrongSubInclusion,
      pshRelEdgeSOClassify,
      pshClassifyingMap,
      pshRelEdgeTerminalMap,
      pshRelEdgeSOTrue,
      pshSieveTrue,
      pshClassifyingSieve, Subfunctor.ι]
    exact ⟨fun _ => trivial,
      fun _ => SQ.map f.op hq⟩

end ClassifyingMap

end GebLean

import GebLean.PshRelEdgeExp

/-!
# Finite Limits and Colimits in the Edge Category

The vertical edge category `PshRelEdge C` has all
finite limits and finite colimits. This module
constructs them directly: terminal and initial
objects, binary coproducts, equalizers, and
coequalizers. Products are defined in
`PshRelEdgeExp.lean`.

## Main definitions

* `pshRelEdgeTerminal`: terminal object
* `pshRelEdgeInitial`: initial object
* `pshRelEdgeCoprod`: binary coproduct
* `pshRelEdgeEqualizer`: equalizer of two morphisms
* `pshRelEdgeCoequalizer`: coequalizer of two
  morphisms
-/

namespace GebLean

open CategoryTheory Limits

universe u v w

variable {C : Type u} [Category.{v} C]

section Terminal

/-- The constant presheaf at `ULift PUnit`,
serving as the terminal presheaf in
`Cᵒᵖ ⥤ Type w`. -/
abbrev pshUnitPresheaf (C : Type u)
    [Category.{v} C] :
    Cᵒᵖ ⥤ Type w :=
  (Functor.const Cᵒᵖ).obj (ULift.{w} PUnit)

/-- The unique natural transformation from any
presheaf to the unit presheaf. -/
def pshUnitMap (P : Cᵒᵖ ⥤ Type w) :
    P ⟶ pshUnitPresheaf C where
  app _ _ := ⟨PUnit.unit⟩

/-- The full relation on the unit presheaf:
all pairs are related. -/
def pshRelFull (C : Type u) [Category.{v} C] :
    PshRel (pshUnitPresheaf.{u, v, w} C)
      (pshUnitPresheaf C) where
  obj _ := Set.univ
  map _ _ _ := Set.mem_univ _

/-- The terminal object in `PshRelEdge C`. -/
def pshRelEdgeTerminal (C : Type u)
    [Category.{v} C] :
    PshRelEdge.{u, v, w} C :=
  { src := pshUnitPresheaf C
    tgt := pshUnitPresheaf C
    edge := pshRelFull C }

/-- The unique morphism from any edge to the
terminal edge. -/
def pshRelEdgeTerminalMap
    (E : PshRelEdge.{u, v, w} C) :
    E ⟶ pshRelEdgeTerminal C :=
  { srcMap := pshUnitMap E.src
    tgtMap := pshUnitMap E.tgt
    sq := fun _ _ _ _ =>
      show _ ∈ Set.univ from Set.mem_univ _ }

/-- The morphism to the terminal edge is
unique. -/
theorem pshRelEdgeTerminalMap_unique
    {E : PshRelEdge.{u, v, w} C}
    (f : E ⟶ pshRelEdgeTerminal C) :
    f = pshRelEdgeTerminalMap E := by
  apply VertEdgeHom.ext <;>
  · ext c p
    exact ULift.ext _ _
      (Subsingleton.elim _ _)

end Terminal

section Initial

/-- The constant presheaf at `ULift PEmpty`,
serving as the initial presheaf. -/
abbrev pshEmptyPresheaf (C : Type u)
    [Category.{v} C] :
    Cᵒᵖ ⥤ Type w :=
  (Functor.const Cᵒᵖ).obj (ULift.{w} PEmpty)

/-- The unique natural transformation from the
empty presheaf to any presheaf. -/
def pshEmptyMap (P : Cᵒᵖ ⥤ Type w) :
    pshEmptyPresheaf C ⟶ P where
  app _ e := (e.down).elim

/-- The empty relation on the empty presheaf. -/
def pshRelEmpty (C : Type u)
    [Category.{v} C] :
    PshRel (pshEmptyPresheaf.{u, v, w} C)
      (pshEmptyPresheaf C) where
  obj _ := ∅
  map _ _ h := h.elim

/-- The initial object in `PshRelEdge C`. -/
def pshRelEdgeInitial (C : Type u)
    [Category.{v} C] :
    PshRelEdge.{u, v, w} C :=
  { src := pshEmptyPresheaf C
    tgt := pshEmptyPresheaf C
    edge := pshRelEmpty C }

/-- The unique morphism from the initial edge
to any edge. -/
def pshRelEdgeInitialMap
    (E : PshRelEdge.{u, v, w} C) :
    pshRelEdgeInitial C ⟶ E :=
  { srcMap := pshEmptyMap E.src
    tgtMap := pshEmptyMap E.tgt
    sq := fun _ e _ _ => (e.down).elim }

/-- The morphism from the initial edge is
unique. -/
theorem pshRelEdgeInitialMap_unique
    {E : PshRelEdge.{u, v, w} C}
    (f : pshRelEdgeInitial C ⟶ E) :
    f = pshRelEdgeInitialMap E := by
  apply VertEdgeHom.ext <;>
  · ext c (e : ULift PEmpty)
    exact (e.down).elim

end Initial

section Coproduct

variable {P₁ Q₁ P₂ Q₂ : Cᵒᵖ ⥤ Type w}

/-- The coproduct presheaf, taking `Sum` at each
stage. -/
def pshCoprodPresheaf
    (P Q : Cᵒᵖ ⥤ Type w) :
    Cᵒᵖ ⥤ Type w where
  obj c := P.obj c ⊕ Q.obj c
  map f := Sum.map (P.map f) (Q.map f)
  map_id _ := by
    ext (x | x) <;> simp [Sum.map]
  map_comp f g := by
    ext (x | x) <;> simp [Sum.map]

/-- Left injection into the coproduct
presheaf. -/
def pshCoprodInl (P Q : Cᵒᵖ ⥤ Type w) :
    P ⟶ pshCoprodPresheaf P Q where
  app _ := Sum.inl

/-- Right injection into the coproduct
presheaf. -/
def pshCoprodInr (P Q : Cᵒᵖ ⥤ Type w) :
    Q ⟶ pshCoprodPresheaf P Q where
  app _ := Sum.inr

/-- Copairing of two natural transformations
into a map from the coproduct presheaf. -/
def pshCoprodDesc
    {P Q R : Cᵒᵖ ⥤ Type w}
    (f : P ⟶ R) (g : Q ⟶ R) :
    pshCoprodPresheaf P Q ⟶ R where
  app c := Sum.elim (f.app c) (g.app c)
  naturality {c d} h := by
    ext (x | x)
    · exact congr_fun (f.naturality h) x
    · exact congr_fun (g.naturality h) x

/-- The coproduct of two presheaf relations.
At stage `c`, `Sum.inl`-`Sum.inl` pairs are
related via `R₁`, `Sum.inr`-`Sum.inr` pairs
via `R₂`, and mixed pairs are unrelated. -/
def pshRelCoprod
    (R₁ : PshRel P₁ Q₁)
    (R₂ : PshRel P₂ Q₂) :
    PshRel (pshCoprodPresheaf P₁ P₂)
      (pshCoprodPresheaf Q₁ Q₂) where
  obj c :=
    { pq |
      match pq.1, pq.2 with
      | Sum.inl p₁, Sum.inl q₁ =>
        (p₁, q₁) ∈ R₁.obj c
      | Sum.inr p₂, Sum.inr q₂ =>
        (p₂, q₂) ∈ R₂.obj c
      | _, _ => False }
  map {c d} f := by
    intro ⟨p, q⟩ h
    dsimp [pshCoprodPresheaf]
    match p, q, h with
    | Sum.inl p₁, Sum.inl q₁, h =>
      exact R₁.map f h
    | Sum.inr p₂, Sum.inr q₂, h =>
      exact R₂.map f h

/-- Left injection preserves the coproduct
relation. -/
theorem pshRelCoprod_related_inl
    (R₁ : PshRel P₁ Q₁)
    (R₂ : PshRel P₂ Q₂) :
    pshRelRelated
      (pshCoprodInl P₁ P₂)
      (pshCoprodInl Q₁ Q₂)
      R₁ (pshRelCoprod R₁ R₂) :=
  fun _ _ _ h => h

/-- Right injection preserves the coproduct
relation. -/
theorem pshRelCoprod_related_inr
    (R₁ : PshRel P₁ Q₁)
    (R₂ : PshRel P₂ Q₂) :
    pshRelRelated
      (pshCoprodInr P₁ P₂)
      (pshCoprodInr Q₁ Q₂)
      R₂ (pshRelCoprod R₁ R₂) :=
  fun _ _ _ h => h

/-- The coproduct of two edges in
`PshRelEdge C`. -/
def pshRelEdgeCoprod
    (E₁ E₂ : PshRelEdge.{u, v, w} C) :
    PshRelEdge.{u, v, w} C :=
  { src := pshCoprodPresheaf E₁.src E₂.src
    tgt := pshCoprodPresheaf E₁.tgt E₂.tgt
    edge := pshRelCoprod E₁.edge E₂.edge }

/-- Left injection into the coproduct edge. -/
def pshRelEdgeCoprodInl
    (E₁ E₂ : PshRelEdge.{u, v, w} C) :
    E₁ ⟶ pshRelEdgeCoprod E₁ E₂ :=
  { srcMap := pshCoprodInl E₁.src E₂.src
    tgtMap := pshCoprodInl E₁.tgt E₂.tgt
    sq := pshRelCoprod_related_inl
      E₁.edge E₂.edge }

/-- Right injection into the coproduct edge. -/
def pshRelEdgeCoprodInr
    (E₁ E₂ : PshRelEdge.{u, v, w} C) :
    E₂ ⟶ pshRelEdgeCoprod E₁ E₂ :=
  { srcMap := pshCoprodInr E₁.src E₂.src
    tgtMap := pshCoprodInr E₁.tgt E₂.tgt
    sq := pshRelCoprod_related_inr
      E₁.edge E₂.edge }

/-- Copairing: given `f₁ : E₁ ⟶ B` and
`f₂ : E₂ ⟶ B`, produce a morphism from the
coproduct to `B`. -/
def pshRelEdgeCoprodDesc
    {E₁ E₂ B : PshRelEdge.{u, v, w} C}
    (f₁ : E₁ ⟶ B) (f₂ : E₂ ⟶ B) :
    pshRelEdgeCoprod E₁ E₂ ⟶ B :=
  { srcMap :=
      pshCoprodDesc f₁.srcMap f₂.srcMap
    tgtMap :=
      pshCoprodDesc f₁.tgtMap f₂.tgtMap
    sq := by
      intro c p q h
      dsimp [pshCoprodDesc]
      match p, q, h with
      | Sum.inl p₁, Sum.inl q₁, h =>
        exact f₁.sq c p₁ q₁ h
      | Sum.inr p₂, Sum.inr q₂, h =>
        exact f₂.sq c p₂ q₂ h }

end Coproduct

section Equalizer

variable {E₁ E₂ : PshRelEdge.{u, v, w} C}
  (f g : E₁ ⟶ E₂)

/-- The equalizer presheaf: at each stage, the
subtype of elements where the two natural
transformations agree. -/
@[reducible]
def pshEqualizerPresheaf
    {P Q : Cᵒᵖ ⥤ Type w}
    (α β : P ⟶ Q) :
    Cᵒᵖ ⥤ Type w where
  obj c :=
    { p : P.obj c // α.app c p = β.app c p }
  map h := fun ⟨p, hp⟩ =>
    ⟨P.map h p, by
      have hα := congr_fun (α.naturality h) p
      have hβ := congr_fun (β.naturality h) p
      simp only [types_comp_apply] at hα hβ
      rw [hα, hβ, hp]⟩
  map_id _ := by
    ext ⟨p, _⟩; simp
  map_comp _ _ := by
    ext ⟨p, _⟩
    simp [FunctorToTypes.map_comp_apply]

/-- The inclusion from the equalizer presheaf
into the domain presheaf. -/
def pshEqualizerInclusion
    {P Q : Cᵒᵖ ⥤ Type w}
    (α β : P ⟶ Q) :
    pshEqualizerPresheaf α β ⟶ P where
  app _ p := p.val

/-- The equalizer relation: restriction of
`E₁.edge` to pairs where both source and
target components lie in the equalizer. -/
def pshRelEqualizer :
    PshRel (pshEqualizerPresheaf
        f.srcMap g.srcMap)
      (pshEqualizerPresheaf
        f.tgtMap g.tgtMap) where
  obj c :=
    { pq |
      (pq.1.val, pq.2.val) ∈ E₁.edge.obj c }
  map {c d} h := by
    intro ⟨⟨p, _⟩, ⟨q, _⟩⟩ hpq
    exact E₁.edge.map h hpq

/-- The equalizer in `PshRelEdge C`. -/
def pshRelEdgeEqualizer :
    PshRelEdge.{u, v, w} C :=
  { src := pshEqualizerPresheaf
      f.srcMap g.srcMap
    tgt := pshEqualizerPresheaf
      f.tgtMap g.tgtMap
    edge := pshRelEqualizer f g }

/-- The inclusion morphism from the equalizer
into the domain. -/
def pshRelEdgeEqualizerInclusion :
    pshRelEdgeEqualizer f g ⟶ E₁ :=
  { srcMap := pshEqualizerInclusion
      f.srcMap g.srcMap
    tgtMap := pshEqualizerInclusion
      f.tgtMap g.tgtMap
    sq := fun _ _ _ h => h }

/-- The equalizer inclusion composes with `f`
and `g` to give the same result. -/
theorem pshRelEdgeEqualizer_condition :
    pshRelEdgeEqualizerInclusion f g ≫ f =
    pshRelEdgeEqualizerInclusion f g ≫ g := by
  apply VertEdgeHom.ext <;>
  · ext c ⟨p, hp⟩
    exact hp

/-- Given a morphism `h : D ⟶ E₁` with
`h ≫ f = h ≫ g`, lift to a morphism
`D ⟶ pshRelEdgeEqualizer f g`. -/
def pshRelEdgeEqualizerLift
    {D : PshRelEdge.{u, v, w} C}
    (h : D ⟶ E₁)
    (w : h ≫ f = h ≫ g) :
    D ⟶ pshRelEdgeEqualizer f g :=
  { srcMap :=
      { app := fun c d =>
          ⟨h.srcMap.app c d,
           congr_fun
            (NatTrans.congr_app
              (congrArg (·.srcMap) w) c) d⟩
        naturality := by
          intro c c' k; funext d
          exact Subtype.ext
            (congr_fun
              (h.srcMap.naturality k) d) }
    tgtMap :=
      { app := fun c d =>
          ⟨h.tgtMap.app c d,
           congr_fun
            (NatTrans.congr_app
              (congrArg (·.tgtMap) w) c) d⟩
        naturality := by
          intro c c' k; funext d
          exact Subtype.ext
            (congr_fun
              (h.tgtMap.naturality k) d) }
    sq := fun c p q hpq => h.sq c p q hpq }

end Equalizer

section Coequalizer

variable {E₁ E₂ : PshRelEdge.{u, v, w} C}
  (f g : E₁ ⟶ E₂)

/-- The generating relation for the coequalizer:
`x` and `y` are related if some element maps to
`x` under `α` and to `y` under `β`. -/
def pshCoequalizerRel
    {P Q : Cᵒᵖ ⥤ Type w}
    (α β : P ⟶ Q) (c : Cᵒᵖ) :
    Q.obj c → Q.obj c → Prop :=
  fun x y => ∃ p : P.obj c,
    α.app c p = x ∧ β.app c p = y

/-- The coequalizer presheaf: at each stage,
the quotient of the codomain by the relation
identifying images of `α` and `β`. -/
def pshCoequalizerPresheaf
    {P Q : Cᵒᵖ ⥤ Type w}
    (α β : P ⟶ Q) :
    Cᵒᵖ ⥤ Type w where
  obj c := Quot (pshCoequalizerRel α β c)
  map {c d} h := Quot.lift
    (fun q => Quot.mk _ (Q.map h q))
    (fun _ _ ⟨p, hx, hy⟩ => by
      subst hx; subst hy
      exact Quot.sound
        ⟨P.map h p,
         congr_fun (α.naturality h) p,
         congr_fun (β.naturality h) p⟩)
  map_id X := by
    funext q; induction q using Quot.ind with
    | mk x =>
      change Quot.mk _ (Q.map (𝟙 X) x) =
        Quot.mk _ x
      congr 1
      exact FunctorToTypes.map_id_apply Q x
  map_comp {X Y Z} f' g' := by
    funext q; induction q using Quot.ind with
    | mk x =>
      change Quot.mk _ (Q.map (f' ≫ g') x) =
        Quot.mk _ (Q.map g' (Q.map f' x))
      congr 1
      exact FunctorToTypes.map_comp_apply
        Q f' g' x

/-- The projection from the codomain presheaf
to the coequalizer presheaf. -/
def pshCoequalizerProjection
    {P Q : Cᵒᵖ ⥤ Type w}
    (α β : P ⟶ Q) :
    Q ⟶ pshCoequalizerPresheaf α β where
  app _ q := Quot.mk _ q

/-- The projection coequalizes: composing `α`
then projecting equals composing `β` then
projecting. -/
theorem pshCoequalizer_condition
    {P Q : Cᵒᵖ ⥤ Type w}
    (α β : P ⟶ Q) :
    α ≫ pshCoequalizerProjection α β =
    β ≫ pshCoequalizerProjection α β := by
  ext c p
  exact Quot.sound ⟨p, rfl, rfl⟩

/-- Descent from the coequalizer: given
`h : Q ⟶ R` with `α ≫ h = β ≫ h`, produce
a map from the coequalizer to `R`. -/
def pshCoequalizerDesc
    {P Q R : Cᵒᵖ ⥤ Type w}
    {α β : P ⟶ Q}
    (h : Q ⟶ R) (w : α ≫ h = β ≫ h) :
    pshCoequalizerPresheaf α β ⟶ R where
  app c := Quot.lift (h.app c)
    (fun _ _ ⟨p, hx, hy⟩ => by
      subst hx; subst hy
      exact congr_fun
        (NatTrans.congr_app w c) p)
  naturality {c d} k := by
    funext q; induction q using Quot.ind with
    | mk x =>
      exact congr_fun (h.naturality k) x

/-- The coequalizer relation: the image of
`E₂.edge` under the quotient maps. A pair of
quotient elements is related if it has
representatives related in `E₂.edge`. -/
def pshRelCoequalizer :
    PshRel (pshCoequalizerPresheaf
        f.srcMap g.srcMap)
      (pshCoequalizerPresheaf
        f.tgtMap g.tgtMap) where
  obj c :=
    { pq |
      ∃ s t, (s, t) ∈ E₂.edge.obj c ∧
        Quot.mk _ s = pq.1 ∧
        Quot.mk _ t = pq.2 }
  map {c d} h := by
    intro ⟨qs, qt⟩ ⟨s, t, hst, hs, ht⟩
    exact ⟨E₂.src.map h s, E₂.tgt.map h t,
      E₂.edge.map h hst,
      congrArg ((pshCoequalizerPresheaf
        f.srcMap g.srcMap).map h) hs,
      congrArg ((pshCoequalizerPresheaf
        f.tgtMap g.tgtMap).map h) ht⟩

/-- The coequalizer in `PshRelEdge C`. -/
def pshRelEdgeCoequalizer :
    PshRelEdge.{u, v, w} C :=
  { src := pshCoequalizerPresheaf
      f.srcMap g.srcMap
    tgt := pshCoequalizerPresheaf
      f.tgtMap g.tgtMap
    edge := pshRelCoequalizer f g }

/-- The projection morphism from the domain
to the coequalizer edge. -/
def pshRelEdgeCoequalizerProjection :
    E₂ ⟶ pshRelEdgeCoequalizer f g :=
  { srcMap := pshCoequalizerProjection
      f.srcMap g.srcMap
    tgtMap := pshCoequalizerProjection
      f.tgtMap g.tgtMap
    sq := fun _ s t hst =>
      ⟨s, t, hst, rfl, rfl⟩ }

/-- The coequalizer projection coequalizes: -/
theorem pshRelEdgeCoequalizer_condition :
    f ≫ pshRelEdgeCoequalizerProjection f g =
    g ≫ pshRelEdgeCoequalizerProjection f g := by
  apply VertEdgeHom.ext <;>
  · ext c p
    exact Quot.sound ⟨p, rfl, rfl⟩

/-- Given a morphism `h : E₂ ⟶ B` with
`f ≫ h = g ≫ h`, descend to a morphism
`pshRelEdgeCoequalizer f g ⟶ B`. -/
def pshRelEdgeCoequalizerDesc
    {B : PshRelEdge.{u, v, w} C}
    (h : E₂ ⟶ B)
    (w : f ≫ h = g ≫ h) :
    pshRelEdgeCoequalizer f g ⟶ B :=
  { srcMap := pshCoequalizerDesc h.srcMap
      (congrArg (·.srcMap) w)
    tgtMap := pshCoequalizerDesc h.tgtMap
      (congrArg (·.tgtMap) w)
    sq := by
      intro c qs qt ⟨s, t, hst, hs, ht⟩
      subst hs; subst ht
      exact h.sq c s t hst }

end Coequalizer

section CategoricalLimits

/-- The terminal edge is a terminal object in
`PshRelEdge C` in the sense of `IsTerminal`. -/
def pshRelEdgeIsTerminal (C : Type u)
    [Category.{v} C] :
    IsTerminal
      (pshRelEdgeTerminal.{u, v, w} C) :=
  IsTerminal.ofUniqueHom
    (fun E => pshRelEdgeTerminalMap E)
    (fun _ f => pshRelEdgeTerminalMap_unique f)

instance pshRelEdgeHasTerminal (C : Type u)
    [Category.{v} C] :
    HasTerminal (PshRelEdge.{u, v, w} C) :=
  (pshRelEdgeIsTerminal C).hasTerminal

/-- The product fan in `PshRelEdge C` is a limit
cone. -/
def pshRelEdgeProdIsLimit
    (E₁ E₂ : PshRelEdge.{u, v, w} C) :
    IsLimit (BinaryFan.mk
      (pshRelEdgeProdFst E₁ E₂)
      (pshRelEdgeProdSnd E₁ E₂)) :=
  BinaryFan.isLimitMk
    (fun s => pshRelEdgePair s.fst s.snd)
    (fun s => by
      apply VertEdgeHom.ext <;>
      · ext c p; rfl)
    (fun s => by
      apply VertEdgeHom.ext <;>
      · ext c p; rfl)
    (fun s m h₁ h₂ => by
      apply VertEdgeHom.ext
      · ext c p
        dsimp [pshRelEdgePair, pshProdLift,
          FunctorToTypes.prod.lift]
        exact Prod.ext
          (congrFun (congr_fun
            (congrArg NatTrans.app
              (congrArg VertEdgeHom.srcMap h₁))
            c) p)
          (congrFun (congr_fun
            (congrArg NatTrans.app
              (congrArg VertEdgeHom.srcMap h₂))
            c) p)
      · ext c p
        dsimp [pshRelEdgePair, pshProdLift,
          FunctorToTypes.prod.lift]
        exact Prod.ext
          (congrFun (congr_fun
            (congrArg NatTrans.app
              (congrArg VertEdgeHom.tgtMap h₁))
            c) p)
          (congrFun (congr_fun
            (congrArg NatTrans.app
              (congrArg VertEdgeHom.tgtMap h₂))
            c) p))

instance pshRelEdgeHasLimitPair
    {E₁ E₂ : PshRelEdge.{u, v, w} C} :
    HasLimit (pair E₁ E₂) :=
  HasLimit.mk
    ⟨_, pshRelEdgeProdIsLimit E₁ E₂⟩

instance pshRelEdgeHasBinaryProducts
    (C : Type u) [Category.{v} C] :
    HasBinaryProducts
      (PshRelEdge.{u, v, w} C) :=
  @hasBinaryProducts_of_hasLimit_pair
    _ _ (fun {_ _} => pshRelEdgeHasLimitPair)

instance pshRelEdgeHasFiniteProducts
    (C : Type u) [Category.{v} C] :
    HasFiniteProducts
      (PshRelEdge.{u, v, w} C) :=
  hasFiniteProducts_of_has_binary_and_terminal

end CategoricalLimits

end GebLean

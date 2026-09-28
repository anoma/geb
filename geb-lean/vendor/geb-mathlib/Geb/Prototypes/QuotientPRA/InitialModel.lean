/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.QuotientPRA.Congruence
public import Geb.Prototypes.QuotientPRA.W
public import Mathlib.Data.Fintype.Quotient


set_option doc.verso true in
/-!
# The quotient of a finitary functor with congruences is the initial model

Let {lit}`F` be a quotient presheaf polynomial functor over
{lit}`I × WalkingParallelPair` with free arities
({lit}`GebProto.QuotientPRA.FreeArity`), finitely many arguments per constructor,
term constructors whose arguments are terms, and a congruence for every term
constructor ({lit}`GebProto.QuotientPRA.HasCongruences`). Its quotient W-type
{lit}`quotient F`, a presheaf on the sorts {lit}`I`, is a model
({lit}`quotientModel`), and for every model {lit}`(P, α)` the eliminator
{lit}`GebProto.QuotientPRA.elim` is the unique morphism of models out of it
({lit}`existsUnique_isModelHom`). It is therefore the initial model: the quotient
inductive-inductive type of the constructors and witness constructors of {lit}`F`.

The algebra structure applies a term constructor to classes by choosing
representatives, through {name}`Quotient.listChoice` over an enumeration of the
arguments; the result does not depend on the choice because the term constructors
respect classes ({lit}`GebProto.QuotientPRA.unit_mk_congr`). On a node over a witness
object it takes the value of the node's source endpoint. The unit of the quotient,
the map sending a tree to its class, is then a morphism of algebras from the W-type
({lit}`quotientModel_unit`), and every node over the discrete graph on the quotient is
the image of a node over the W-type ({lit}`mapPresheaf_unit_surjective`): the term
arguments by choosing representatives, the witness arguments by choosing reflexivity
witnesses at representatives ({lit}`GebProto.QuotientPRA.exists_refl`). These two
facts give the naturality of the algebra, since the W-type's constructor and the unit
are natural, and the eliminator's commuting with the algebras, since the W-type's
eliminator is the eliminator of the quotient composed with the unit. Uniqueness is
induction on trees ({lit}`eq_elim`).

## Main definitions

* {lit}`algTerm` — a term constructor applied to classes.
* {lit}`quotientModel` — the model structure on the quotient.

## Main statements

* {lit}`FreeArity.mapPresheaf_freeNode` — a morphism of presheaves acts on a node by
  acting on its argument values.
* {lit}`quotientModel_unit` — the unit is a morphism of algebras.
* {lit}`mapPresheaf_unit_surjective` — every node over the quotient's discrete graph
  has a representative node over the W-type.
* {lit}`isModelHom_elim` — the eliminator is a morphism of models.
* {lit}`eq_elim` — it is the only one.
* {lit}`existsUnique_isModelHom` — the quotient is the initial model.

## Implementation notes

The finiteness of the arguments is an enumeration, {name}`FinEnum`, as in
{lit}`GebProto.QuotientPRA.Congruence`; with infinitely many arguments the choice of
representatives requires a choice principle (\[FiorePittsSteenkamp2020\]). The
arguments of term constructors are terms so that the classes of the arguments can be
represented by terms; the arguments of witness constructors are unrestricted.

## References

* \[AltenkirchCapriottiDijkstraKrausNordvallForsberg2018\]
* \[Dijkstra2017\]
* \[FiorePittsSteenkamp2020\]

## Tags

quotient inductive-inductive type, initial algebra, W-type, presheaf, congruence
-/

set_option doc.verso true

@[expose] public section

open CategoryTheory Limits

namespace GebProto.QuotientPRA

universe uI vI uA uB w

namespace FreeArity

variable {C : Type uI} [Category.{vI} C] {S : FreeArity.{uI, vI, uA, uB} C}
  {restr_id : S.toData.ShapeRestrId} {restr_comp : S.toData.ShapeRestrComp}
  {reindex_id : S.toData.ReindexId restr_id} {reindex_comp : S.toData.ReindexComp restr_comp}

/-- A morphism of presheaves acts on a node with given argument values by acting on the
values. -/
theorem mapPresheaf_freeNode {Z Z' : Cᵒᵖ ⥤ Type w} (τ : NatTrans Z Z') (a : S.A) {c : C}
    (hq : S.q a = c) (ts : (b : S.Gen a) → Z.obj ⟨S.gobj a b⟩) :
    ((S.toPresheaf restr_id restr_comp reindex_id reindex_comp).mapPresheaf τ).app ⟨c⟩
        (freeNode Z a hq ts) =
      freeNode Z' a hq fun b ↦ τ.app _ (ts b) :=
  Subtype.ext (Subtype.ext (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun d ↦
    Sigma.ext rfl (heq_of_eq (naturality_apply τ d.2.2.op (ts d.1))))))))

end FreeArity

/-- The image of a node under the functor's action on a morphism of presheaves that
factors pointwise through two others is the image under the two in turn. -/
theorem mapPresheaf_apply_of_apply {C : Type uI} [Category.{vI} C]
    (F : PresheafPFunctor.{uI, uI, uA, uB, vI, vI} C C) {Z Z' Z'' : Cᵒᵖ ⥤ Type w}
    {γ : NatTrans Z Z''} {ε : NatTrans Z Z'} {δ : NatTrans Z' Z''}
    (h : ∀ c t, γ.app c t = δ.app c (ε.app c t)) {c : Cᵒᵖ} (n : (F.objPresheaf Z).obj c) :
    (F.mapPresheaf γ).app c n = (F.mapPresheaf δ).app c ((F.mapPresheaf ε).app c n) :=
  Subtype.ext (Subtype.ext (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun _ ↦
    Sigma.ext rfl (heq_of_eq (h _ _)))))))

variable {I : Type uI} [Category.{vI} I] {S : FreeArity.{uI, vI, uA, uB} (I × WalkingParallelPair)}
  {restr_id : S.toData.ShapeRestrId} {restr_comp : S.toData.ShapeRestrComp}
  {reindex_id : S.toData.ReindexId restr_id} {reindex_comp : S.toData.ReindexComp restr_comp}

set_option hygiene false in
/-- The functor of the free-arity instance. -/
local notation "𝐅" => S.toPresheaf restr_id restr_comp reindex_id reindex_comp

section Kernel

variable (X : (I × WalkingParallelPair)ᵒᵖ ⥤ Type w)

/-- The kernel of the unit at an object: two elements with the same class. -/
abbrev unitSetoid (c : I × WalkingParallelPair) : Setoid (X.obj ⟨c⟩) where
  r u u' := (coeqUnit X).app ⟨c⟩ u = (coeqUnit X).app ⟨c⟩ u'
  iseqv := ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩

/-- An element of the discrete graph on the quotient at an object over the terms, a
class of terms, as a class of the kernel of the unit. -/
def toUnitQuot : (c : I × WalkingParallelPair) → c.2 = .zero →
    (discrete (coeq X)).obj ⟨c⟩ → Quotient (unitSetoid X c)
  | (_, .zero), _ => Quot.lift (Quotient.mk _) fun _ _ r ↦ Quotient.sound (Quot.sound r)
  | (_, .one), h => nomatch h

variable {X}

/-- The class of the unit's value on a term is the term's class. -/
theorem toUnitQuot_unit {c : I × WalkingParallelPair} (hc : c.2 = .zero) (u : X.obj ⟨c⟩) :
    toUnitQuot X c hc ((coeqUnit X).app ⟨c⟩ u) = Quotient.mk _ u := by
  obtain ⟨k, x⟩ := c
  obtain rfl : x = .zero := hc
  rfl

end Kernel

attribute [local instance] unitSetoid

variable [hfin : ∀ a, FinEnum (S.Gen a)] {ht : TermArguments S}
  (hcong : HasCongruences restr_id restr_comp reindex_id reindex_comp ht)
include hcong

/-- A term constructor applied to classes: the class of its application to
representatives, chosen through {name}`Quotient.listChoice` over an enumeration of its
arguments. -/
def algTerm (a : S.A) {c : I × WalkingParallelPair} (hq : S.q a = c) (hc : c.2 = .zero)
    (v : (b : S.Gen a) → (discrete (quotient 𝐅)).obj ⟨S.gobj a b⟩) :
    (discrete (quotient 𝐅)).obj ⟨c⟩ :=
  Quotient.lift (s := piSetoid)
    (fun g : (b : S.Gen a) → b ∈ FinEnum.toList (S.Gen a) → 𝐅.W.obj ⟨S.gobj a b⟩ ↦
      (coeqUnit 𝐅.W).app ⟨c⟩
        (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq fun b ↦ g b (FinEnum.mem_toList b))))
    (fun g g' hgg ↦ unit_mk_congr hcong a hq hc fun b ↦
      (show ∀ hb : b ∈ FinEnum.toList (S.Gen a),
          (coeqUnit 𝐅.W).app ⟨S.gobj a b⟩ (g b hb) = (coeqUnit 𝐅.W).app ⟨S.gobj a b⟩ (g' b hb)
        from hgg b) (FinEnum.mem_toList b))
    (Quotient.listChoice fun b _ ↦ toUnitQuot 𝐅.W _ (ht.gobj hq hc b) (v b))

/-- A term constructor applied to the classes of terms is the class of its application
to the terms. -/
theorem algTerm_unit (a : S.A) {c : I × WalkingParallelPair} (hq : S.q a = c)
    (hc : c.2 = .zero) (ts : (b : S.Gen a) → 𝐅.W.obj ⟨S.gobj a b⟩) :
    algTerm hcong a hq hc (fun b ↦ (coeqUnit 𝐅.W).app _ (ts b)) =
      (coeqUnit 𝐅.W).app ⟨c⟩ (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts)) :=
  congrArg (Quotient.lift (s := piSetoid) _ _)
    ((congrArg Quotient.listChoice (funext fun b ↦ funext fun _ ↦
      toUnitQuot_unit (ht.gobj hq hc b) (ts b))).trans (Quotient.listChoice_mk fun b _ ↦ ts b))

/-- The algebra on a node over the discrete graph on the quotient at an object over the
terms: its constructor applied to the classes it gives its arguments. -/
def algNode {c : I × WalkingParallelPair} (hc : c.2 = .zero)
    (x : (𝐅.objPresheaf (discrete (quotient 𝐅))).obj ⟨c⟩) : (discrete (quotient 𝐅)).obj ⟨c⟩ :=
  algTerm hcong x.1.1.1.1 x.2 hc fun b ↦
    PresheafDomPFunctorData.value _ x.1.1 ⟨⟨b, S.gobj x.1.1.1.1 b, 𝟙 _⟩, rfl⟩

/-- The algebra on the image of a node with given argument values is the class of the
tree the node builds. -/
theorem algNode_unit_freeNode (a : S.A) {c : I × WalkingParallelPair} (hq : S.q a = c)
    (hc : c.2 = .zero) (ts : (b : S.Gen a) → 𝐅.W.obj ⟨S.gobj a b⟩) :
    algNode hcong hc ((𝐅.mapPresheaf (coeqUnit 𝐅.W)).app ⟨c⟩ (FreeArity.freeNode 𝐅.W a hq ts)) =
      (coeqUnit 𝐅.W).app ⟨c⟩ (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts)) := by
  rw [FreeArity.mapPresheaf_freeNode]
  refine (congrArg (algTerm hcong a hq hc) (funext fun b ↦ ?_)).trans
    (algTerm_unit hcong a hq hc ts)
  exact FunctorToTypes.map_id_apply (discrete (quotient 𝐅)) _

/-- The algebra on the image of a node over the W-type is the class of the tree the node
builds. -/
theorem algNode_unit {c : I × WalkingParallelPair} (hc : c.2 = .zero)
    (n : (𝐅.objPresheaf 𝐅.W).obj ⟨c⟩) :
    algNode hcong hc ((𝐅.mapPresheaf (coeqUnit 𝐅.W)).app ⟨c⟩ n) =
      (coeqUnit 𝐅.W).app ⟨c⟩ (PresheafPFunctor.W.mk n) := by
  have key := algNode_unit_freeNode hcong n.1.1.1.1 n.2 hc fun b ↦
    PresheafDomPFunctorData.value _ n.1.1 ⟨⟨b, S.gobj n.1.1.1.1 b, 𝟙 _⟩, rfl⟩
  rwa [← FreeArity.eq_freeNode n] at key

/-- The algebra on the quotient: on a node over the terms, {lit}`algNode`; on a node over
the witnesses, the value of its source endpoint. -/
def algApp : (c : (I × WalkingParallelPair)ᵒᵖ) →
    (𝐅.objPresheaf (discrete (quotient 𝐅))).obj c → (discrete (quotient 𝐅)).obj c
  | ⟨(_, .zero)⟩, x => algNode hcong rfl x
  | ⟨(i, .one)⟩, x =>
    algNode hcong (c := termObj i) rfl ((𝐅.objPresheaf (discrete (quotient 𝐅))).map (srcHom i).op x)

/-- The unit is a morphism of algebras: the algebra on the image of a node over the
W-type is the class of the tree the node builds. -/
theorem algApp_unit (c : (I × WalkingParallelPair)ᵒᵖ) (n : (𝐅.objPresheaf 𝐅.W).obj c) :
    algApp hcong c ((𝐅.mapPresheaf (coeqUnit 𝐅.W)).app c n) =
      (coeqUnit 𝐅.W).app c (PresheafPFunctor.W.mk n) := by
  obtain ⟨⟨i, x⟩⟩ := c
  cases x with
  | zero => exact algNode_unit hcong rfl n
  | one =>
    change algNode hcong (c := termObj i) rfl ((𝐅.objPresheaf (discrete (quotient 𝐅))).map
        (srcHom i).op ((𝐅.mapPresheaf (coeqUnit 𝐅.W)).app _ n)) =
      coeqMk 𝐅.W (src 𝐅.W i (PresheafPFunctor.W.mk n))
    rw [← naturality_apply (𝐅.mapPresheaf (coeqUnit 𝐅.W)) (srcHom i).op n, algNode_unit]
    exact congrArg (coeqMk 𝐅.W) (PresheafPFunctor.carrier.mk_map (srcHom i) n)

/-- Every class at every object is the class of an element of the W-type: a term's
class of itself, a witness's of a reflexivity witness at a representative. -/
theorem unit_surjective (c : I × WalkingParallelPair) (q : (discrete (quotient 𝐅)).obj ⟨c⟩) :
    ∃ u : 𝐅.W.obj ⟨c⟩, (coeqUnit 𝐅.W).app ⟨c⟩ u = q := by
  obtain ⟨k, x⟩ := c
  cases x with
  | zero =>
    exact Quot.ind (β := fun q ↦ ∃ u, (coeqUnit 𝐅.W).app ⟨(k, .zero)⟩ u = q)
      (fun t ↦ ⟨t, rfl⟩) q
  | one =>
    refine Quot.ind (β := fun q ↦ ∃ u, (coeqUnit 𝐅.W).app ⟨(k, .one)⟩ u = q) (fun t ↦ ?_) q
    obtain ⟨e, he⟩ := exists_refl hcong (c := termObj k) rfl t
    exact ⟨e, congrArg (coeqMk 𝐅.W) (he false)⟩

/-- Every node over the discrete graph on the quotient is the image of a node over the
W-type: choose representatives of the classes it gives its arguments. -/
theorem mapPresheaf_unit_surjective (c : (I × WalkingParallelPair)ᵒᵖ)
    (x : (𝐅.objPresheaf (discrete (quotient 𝐅))).obj c) :
    ∃ n : (𝐅.objPresheaf 𝐅.W).obj c, (𝐅.mapPresheaf (coeqUnit 𝐅.W)).app c n = x := by
  let _ := hfin x.1.1.1.1
  obtain ⟨us, hus⟩ := exists_forall_of_finEnum fun b ↦ unit_surjective hcong (S.gobj x.1.1.1.1 b)
    (PresheafDomPFunctorData.value _ x.1.1 ⟨⟨b, S.gobj x.1.1.1.1 b, 𝟙 _⟩, rfl⟩)
  exact ⟨FreeArity.freeNode 𝐅.W x.1.1.1.1 x.2 us,
    (FreeArity.mapPresheaf_freeNode _ _ x.2 us).trans
      ((congrArg (FreeArity.freeNode _ x.1.1.1.1 x.2) (funext hus)).trans
        (FreeArity.eq_freeNode x).symm)⟩

/-- The model structure on the quotient. It is natural because the unit is a morphism
of algebras onto the nodes over the quotient's discrete graph, and the W-type's
constructor and the unit are natural. -/
def quotientModel :
    NatTrans (𝐅.objPresheaf (discrete (quotient 𝐅))) (discrete (quotient 𝐅)) where
  app c := ↾ algApp hcong c
  naturality c c' g := by
    ext x
    obtain ⟨n, rfl⟩ := mapPresheaf_unit_surjective hcong c x
    change algApp hcong c' ((𝐅.objPresheaf (discrete (quotient 𝐅))).map g
        ((𝐅.mapPresheaf (coeqUnit 𝐅.W)).app c n)) =
      (discrete (quotient 𝐅)).map g (algApp hcong c ((𝐅.mapPresheaf (coeqUnit 𝐅.W)).app c n))
    rw [← naturality_apply (𝐅.mapPresheaf (coeqUnit 𝐅.W)) g n, algApp_unit, algApp_unit]
    exact (congrArg ((coeqUnit 𝐅.W).app c') (PresheafPFunctor.carrier.mk_map g.unop n)).trans
      (naturality_apply (coeqUnit 𝐅.W) g _)

/-- The unit is a morphism of algebras from the W-type to the quotient's model. -/
theorem quotientModel_unit (c : (I × WalkingParallelPair)ᵒᵖ) (n : (𝐅.objPresheaf 𝐅.W).obj c) :
    (quotientModel hcong).app c ((𝐅.mapPresheaf (coeqUnit 𝐅.W)).app c n) =
      (coeqUnit 𝐅.W).app c (PresheafPFunctor.W.mk n) :=
  algApp_unit hcong c n

variable (P : Iᵒᵖ ⥤ Type (max uI vI uA uB)) (α : NatTrans (𝐅.objPresheaf (discrete P)) (discrete P))

/-- The eliminator is a morphism of models out of the quotient: on the image of a node
over the W-type it is the W-type's eliminator, which commutes with the algebras. -/
theorem isModelHom_elim : IsModelHom (quotientModel hcong) α (elim 𝐅 P α) := by
  intro c x
  obtain ⟨n, rfl⟩ := mapPresheaf_unit_surjective hcong c x
  rw [quotientModel_unit]
  exact (discreteMap_coeqDesc_unit _ c _).trans
    ((PresheafPFunctor.W.elim_mk 𝐅 (discrete P) α n).trans (congrArg (α.app c)
      (mapPresheaf_apply_of_apply 𝐅 (fun c t ↦ (discreteMap_coeqDesc_unit _ c t).symm) n)))

variable {P α}

/-- A morphism of models out of the quotient agrees with the eliminator on the class of
every tree, by induction on the tree. -/
theorem unit_eq_of_isModelHom {h : NatTrans (quotient 𝐅) P}
    (hh : IsModelHom (quotientModel hcong) α h) {c : I × WalkingParallelPair}
    (t : 𝐅.W.obj ⟨c⟩) :
    (discreteMap h).app ⟨c⟩ ((coeqUnit 𝐅.W).app ⟨c⟩ t) =
      (discreteMap (elim 𝐅 P α)).app ⟨c⟩ ((coeqUnit 𝐅.W).app ⟨c⟩ t) :=
  FreeArity.W_induction (S := S) (motive := fun c t ↦
      (discreteMap h).app ⟨c⟩ ((coeqUnit 𝐅.W).app ⟨c⟩ t) =
        (discreteMap (elim 𝐅 P α)).app ⟨c⟩ ((coeqUnit 𝐅.W).app ⟨c⟩ t))
    (fun a ts ih ↦ by
      beta_reduce
      rw [← quotientModel_unit hcong, hh, isModelHom_elim hcong P α,
        FreeArity.mapPresheaf_freeNode, FreeArity.mapPresheaf_freeNode,
        FreeArity.mapPresheaf_freeNode]
      exact congrArg (fun vs ↦ α.app _ (FreeArity.freeNode (discrete P) a rfl vs)) (funext ih))
    t

/-- The eliminator is the only morphism of models out of the quotient. -/
theorem eq_elim {h : NatTrans (quotient 𝐅) P} (hh : IsModelHom (quotientModel hcong) α h)
    (i : Iᵒᵖ) (q : (quotient 𝐅).obj i) : h.app i q = (elim 𝐅 P α).app i q :=
  Quot.ind (β := fun q ↦ h.app i q = (elim 𝐅 P α).app i q)
    (fun t ↦ unit_eq_of_isModelHom hcong hh (c := termObj i.unop) t) q

variable (P α)

/-- The quotient is the initial model: out of it into every model there is exactly one
morphism of models, the eliminator. -/
theorem existsUnique_isModelHom :
    ∃! h : NatTrans (quotient 𝐅) P, IsModelHom (quotientModel hcong) α h :=
  ⟨elim 𝐅 P α, isModelHom_elim hcong P α, fun _ hh ↦ by
    ext i q
    exact eq_elim hcong hh i q⟩

end GebProto.QuotientPRA

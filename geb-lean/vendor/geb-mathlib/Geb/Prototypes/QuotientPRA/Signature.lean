/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.QuotientPRA.FreeArity
public import Geb.Prototypes.QuotientPRA.W
public import Mathlib.CategoryTheory.Discrete.Basic


set_option doc.verso true in
/-!
# Quotient W-types of a signature with one-step equations

A signature is a polynomial functor {lit}`P`: an operation {lit}`a : P.A` takes
arguments indexed by {lit}`P.B a`. An equation is one-step when each side is a single
operation applied to variables, an element of {lit}`P.Obj V` for the equation's type
of variables {lit}`V`. Commutativity of a binary operation is one-step; unit and
associativity laws are not.

{lit}`qpra P eqns` is the quotient presheaf polynomial functor of such a system, over
the one-object base: terms are built by the operations; witnesses are built by the
equations, in both orientations, and by a congruence for every operation, whose
arguments are witnesses between the arguments of two applications of the operation.
The congruences and the reversed orientations are added to the equations given; they
are the part of the equivalence and congruence closure that witness constructors can
express ({lit}`GebProto.QuotientPRA.Obstruction`).

Every arity is free ({lit}`GebProto.QuotientPRA.FreeArity`): an operation's arguments
lie over the terms and a congruence's over the witnesses. Restriction of a congruence
to an endpoint sends each argument to the same argument along the endpoint morphism,
and restriction of an equation to an endpoint reads each argument of the side's
operation as the variable the side assigns it.

An algebra of the signature that satisfies the equations is a model of the quotient
functor ({lit}`model`): a node goes to the value of its source endpoint, and the two
endpoints of an equation's witness agree because the algebra satisfies the equation.
The eliminator {lit}`lift` into it and its computation rule {lit}`lift_intro` are those
of {lit}`GebProto.QuotientPRA.W` at that model.

## Main definitions

* {lit}`Equations` — a system of one-step equations over a signature.
* {lit}`Shape` — the operations, the congruences and the oriented equations.
* {lit}`freeArity` — their arguments and restrictions.
* {lit}`qpra` — the quotient presheaf polynomial functor of the system.
* {lit}`freeNode` — the node of a shape from its arguments.
* {lit}`Satisfies`, {lit}`model` — an algebra satisfying the equations, and the model
  it gives.
* {lit}`lift` — the eliminator into such an algebra.

## Main statements

* {lit}`restr_id`, {lit}`restr_comp`, {lit}`reindex_id`, {lit}`reindex_comp` — the laws
  of the shape restriction and argument reindexing.
* {lit}`src_mk_freeNode_eqn`, {lit}`tgt_mk_freeNode_eqn` — the endpoints of an
  equation's witness are its sides.
* {lit}`endpoint_mk_freeNode_cong` — the endpoints of a congruence's witness are the
  operation on the endpoints of its arguments.
* {lit}`lift_intro` — the computation rule of the eliminator.

## Implementation notes

The base is {lit}`Discrete PUnit × WalkingParallelPair`, whose first component is
trivial. Its objects are pairs, and {lit}`⟨⟨⟩⟩` is definitionally the only element of
{lit}`Discrete PUnit`, so every object is definitionally {lit}`objOf x` for its
{name}`CategoryTheory.Limits.WalkingParallelPair` component {lit}`x`. The restrictions
are defined by cases on the {name}`CategoryTheory.Limits.WalkingParallelPairHom`
component of a morphism, so the identity morphism acts by the identity definitionally
and the laws reduce to the category laws of the base after a case split.

## References

* \[FiorePittsSteenkamp2020\]
* \[Weber2007\]

## Tags

quotient inductive type, W-type, polynomial functor, equational theory, congruence
-/

set_option doc.verso true

@[expose] public section

open CategoryTheory Limits

namespace GebProto.QuotientPRA.Signature

universe uA uB

/-- A system of one-step equations over the signature {lit}`P`: named equations, each
with a type of variables and two sides, each side one operation applied to
variables. -/
structure Equations (P : PFunctor.{uA, uB}) : Type (max (uA + 1) (uB + 1)) where
  /-- The names of the equations. -/
  E : Type uA
  /-- The variables of each equation. -/
  V : E → Type uB
  /-- The left side of each equation. -/
  lhs : (e : E) → P.Obj (V e)
  /-- The right side of each equation. -/
  rhs : (e : E) → P.Obj (V e)

variable {P : PFunctor.{uA, uB}}

/-- The side of an equation at an orientation: the left side for {lit}`false`, the
right side for {lit}`true`. -/
def Equations.side (eqns : Equations P) (e : eqns.E) : Bool → P.Obj (eqns.V e)
  | false => eqns.lhs e
  | true => eqns.rhs e

/-- The base: the one-object category times the walking parallel pair. -/
abbrev Obj : Type := Discrete PUnit.{1} × WalkingParallelPair

/-- The object of the base over a {name}`CategoryTheory.Limits.WalkingParallelPair`
object. -/
abbrev objOf (x : WalkingParallelPair) : Obj := (⟨⟨⟩⟩, x)

/-- The morphism of the base over a {name}`CategoryTheory.Limits.WalkingParallelPair`
morphism. -/
abbrev homOf {x' x : WalkingParallelPair} (h : x' ⟶ x) : objOf x' ⟶ objOf x := (𝟙 _, h)

variable (P) (eqns : Equations P)

/-- The shapes: an operation, over terms; the congruence of an operation, and an
equation with an orientation, over witnesses. -/
def Shape : Type uA := P.A ⊕ P.A ⊕ eqns.E × Bool

variable {P eqns}

/-- The object of the walking parallel pair over which a shape lies. -/
def shapeObj : Shape P eqns → WalkingParallelPair
  | .inl _ => .zero
  | .inr _ => .one

/-- The arguments of a shape: those of the operation, for an operation and for its
congruence; the variables, for an equation. -/
def Gen : Shape P eqns → Type uB
  | .inl a => P.B a
  | .inr (.inl a) => P.B a
  | .inr (.inr p) => eqns.V p.1

/-- The object over which an argument lies: a witness, for a congruence; a term,
otherwise. -/
def genObj : (s : Shape P eqns) → Gen s → WalkingParallelPair
  | .inl _, _ => .zero
  | .inr (.inl _), _ => .one
  | .inr (.inr _), _ => .zero

/-- The shape an endpoint of a shape has: an operation, for an operation and for its
congruence; the operation of the side the orientation selects, for an equation. The
orientation {lit}`o` of the endpoint is combined with that of the equation, so the
target of an equation of orientation {lit}`o'` is the side {lit}`!o'`. -/
def endShape (o : Bool) : Shape P eqns → Shape P eqns
  | .inl a => .inl a
  | .inr (.inl a) => .inl a
  | .inr (.inr (e, o')) => .inl (eqns.side e (o ^^ o')).1

/-- The argument of a shape that an argument of its endpoint reads, with the morphism
between their objects: for a congruence, the same argument along the endpoint
morphism; for an equation, the variable the side assigns. -/
def endGen (o : Bool) : (s : Shape P eqns) → (b : Gen (endShape o s)) →
    Σ b' : Gen s, (objOf (genObj (endShape o s) b) ⟶ objOf (genObj s b'))
  | .inl _, b => ⟨b, 𝟙 _⟩
  | .inr (.inl _), b => ⟨b, homOf (endHom o)⟩
  | .inr (.inr (e, o')), b => ⟨(eqns.side e (o ^^ o')).2 b, 𝟙 _⟩

/-- The restriction of a shape along a morphism of the walking parallel pair. -/
def restrShape : {x' x : WalkingParallelPair} → (x' ⟶ x) → Shape P eqns → Shape P eqns
  | _, _, .id _, s => s
  | _, _, .left, s => endShape false s
  | _, _, .right, s => endShape true s

/-- The reindexing of a restricted shape's arguments along a morphism of the walking
parallel pair. -/
def restrGen : {x' x : WalkingParallelPair} → (h : x' ⟶ x) → (s : Shape P eqns) →
    (b : Gen (restrShape h s)) →
      Σ b' : Gen s, (objOf (genObj (restrShape h s) b) ⟶ objOf (genObj s b'))
  | _, _, .id _, _, b => ⟨b, 𝟙 _⟩
  | _, _, .left, s, b => endGen false s b
  | _, _, .right, s, b => endGen true s b

/-- An endpoint of a shape lies over the terms. -/
theorem shapeObj_endShape (o : Bool) (s : Shape P eqns) :
    shapeObj (endShape o s) = WalkingParallelPair.zero := by
  rcases s with _ | _ | ⟨e, o'⟩ <;> rfl

/-- A restricted shape lies over the source of the restricting morphism. -/
theorem shapeObj_restrShape {x' x : WalkingParallelPair} (h : x' ⟶ x) (s : Shape P eqns)
    (hs : shapeObj s = x) : shapeObj (restrShape h s) = x' := by
  cases h with
  | id => exact hs
  | left => exact shapeObj_endShape false s
  | right => exact shapeObj_endShape true s

variable (P eqns)

/-- The shapes and arguments of the system, with free arities. -/
def freeArity : FreeArity.{0, 0, uA, uB} Obj where
  A := Shape P eqns
  q s := objOf (shapeObj s)
  Gen := Gen
  gobj s b := objOf (genObj s b)
  restr g s := restrShape (Prod.snd g) s
  q_restr g s hs := Prod.ext rfl (shapeObj_restrShape (Prod.snd g) s (congrArg Prod.snd hs))
  reindex g s b := restrGen (Prod.snd g) s b

/-- Shape restriction along an identity is the identity. -/
theorem restr_id : (freeArity P eqns).toData.ShapeRestrId := fun _ ↦ rfl

/-- Shape restriction along a composite is the composite of restrictions. -/
theorem restr_comp : (freeArity P eqns).toData.ShapeRestrComp := by
  intro j j' j'' g h
  obtain ⟨_, x⟩ := j
  obtain ⟨_, x'⟩ := j'
  obtain ⟨_, x''⟩ := j''
  obtain ⟨_, g⟩ := g
  obtain ⟨_, h⟩ := h
  funext s
  cases g <;> cases h <;> rfl

/-- Argument reindexing along an identity is the identity. -/
theorem reindex_id : (freeArity P eqns).toData.ReindexId (restr_id P eqns) := by
  intro j s i d
  obtain ⟨⟨b, c, k⟩, hd⟩ := d
  exact Subtype.ext (Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq (Category.comp_id k)))))

/-- Argument reindexing along a composite is the composite of reindexings. -/
theorem reindex_comp : (freeArity P eqns).toData.ReindexComp (restr_comp P eqns) := by
  intro j j' j'' g h s i d
  obtain ⟨_, x⟩ := j
  obtain ⟨_, x'⟩ := j'
  obtain ⟨_, x''⟩ := j''
  obtain ⟨_, g⟩ := g
  obtain ⟨_, h⟩ := h
  obtain ⟨⟨b, c, k⟩, hd⟩ := d
  cases g <;> cases h <;>
    refine Subtype.ext (Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq ?_)))) <;>
    first
      | exact (Category.comp_id (k ≫ _)).symm
      | exact congrArg (· ≫ _) (Category.comp_id k).symm

/-- The quotient presheaf polynomial functor of a system of one-step equations: the
operations build terms, and the equations in both orientations and the congruences of
the operations build witnesses. -/
def qpra : PresheafPFunctor.{0, 0, uA, uB, 0, 0} Obj Obj :=
  (freeArity P eqns).toPresheaf (restr_id P eqns) (restr_comp P eqns) (reindex_id P eqns)
    (reindex_comp P eqns)

section Node

universe w

variable {P eqns}

/-- The node of a shape over a presheaf {lit}`Z`, from the values of its arguments. -/
abbrev freeNode (Z : Objᵒᵖ ⥤ Type w) (s : Shape P eqns)
    (ts : (b : Gen s) → Z.obj ⟨objOf (genObj s b)⟩) :
    ((qpra P eqns).objPresheaf Z).obj ⟨objOf (shapeObj s)⟩ :=
  FreeArity.freeNode (S := freeArity P eqns) Z s rfl ts

/-- Restriction of the W-type along an identity is the identity. -/
theorem W_map_id_apply {c : Obj} (t : (qpra P eqns).W.obj ⟨c⟩) :
    (qpra P eqns).W.map (𝟙 c).op t = t := by
  rw [op_id, FunctorToTypes.map_id_apply]

/-- The source of an equation's witness is the side its orientation selects, applied to
the witness's variables. -/
theorem src_mk_freeNode_eqn (e : eqns.E) (o : Bool)
    (ts : eqns.V e → (qpra P eqns).W.obj ⟨objOf .zero⟩) :
    src (qpra P eqns).W ⟨⟨⟩⟩ (PresheafPFunctor.W.mk (freeNode _ (.inr (.inr (e, o))) ts)) =
      PresheafPFunctor.W.mk (freeNode _ (.inl (eqns.side e (false ^^ o)).1)
        fun b ↦ ts ((eqns.side e (false ^^ o)).2 b)) :=
  (congrArg PresheafPFunctor.W.mk
    (FreeArity.map_freeNode (S := freeArity P eqns) _ (.inr (.inr (e, o))) rfl (homOf .left)
      ts)).trans
    (congrArg (fun ts ↦ PresheafPFunctor.W.mk (freeNode _ (.inl (eqns.side e (false ^^ o)).1) ts))
      (funext fun _ ↦ W_map_id_apply _))

/-- The target of an equation's witness is the other side, applied to the witness's
variables. -/
theorem tgt_mk_freeNode_eqn (e : eqns.E) (o : Bool)
    (ts : eqns.V e → (qpra P eqns).W.obj ⟨objOf .zero⟩) :
    tgt (qpra P eqns).W ⟨⟨⟩⟩ (PresheafPFunctor.W.mk (freeNode _ (.inr (.inr (e, o))) ts)) =
      PresheafPFunctor.W.mk (freeNode _ (.inl (eqns.side e (true ^^ o)).1)
        fun b ↦ ts ((eqns.side e (true ^^ o)).2 b)) :=
  (congrArg PresheafPFunctor.W.mk
    (FreeArity.map_freeNode (S := freeArity P eqns) _ (.inr (.inr (e, o))) rfl (homOf .right)
      ts)).trans
    (congrArg (fun ts ↦ PresheafPFunctor.W.mk (freeNode _ (.inl (eqns.side e (true ^^ o)).1) ts))
      (funext fun _ ↦ W_map_id_apply _))

/-- An endpoint of a congruence's witness is the operation applied to the same endpoint
of the witnesses between its arguments. -/
theorem endpoint_mk_freeNode_cong (o : Bool) (a : P.A)
    (ts : P.B a → (qpra P eqns).W.obj ⟨objOf .one⟩) :
    (qpra P eqns).W.map (homOf (endHom o)).op
        (PresheafPFunctor.W.mk (freeNode _ (.inr (.inl a)) ts)) =
      PresheafPFunctor.W.mk (freeNode _ (.inl a)
        fun b ↦ (qpra P eqns).W.map (homOf (endHom o)).op (ts b)) := by
  cases o
  · exact congrArg PresheafPFunctor.W.mk
      (FreeArity.map_freeNode (S := freeArity P eqns) _ (.inr (.inl a)) rfl
        (homOf (endHom false)) ts)
  · exact congrArg PresheafPFunctor.W.mk
      (FreeArity.map_freeNode (S := freeArity P eqns) _ (.inr (.inl a)) rfl
        (homOf (endHom true)) ts)

end Node

section Model

universe w

variable {P eqns}

/-- The constant presheaf on the one-object category at a type. -/
def constPsh (Y : Type w) : (Discrete PUnit.{1})ᵒᵖ ⥤ Type w where
  obj _ := Y
  map _ := 𝟙 Y

variable {Y : Type (max uA uB)} (S : P.Obj Y → Y)

/-- The value an algebra {lit}`S` of the signature gives a node from its arguments'
values: that of its source endpoint, an operation applied to arguments. -/
def algVal : (s : Shape P eqns) → ((freeArity P eqns).Dir s → Y) → Y
  | .inl a, v => S ⟨a, fun b ↦ v ⟨b, objOf .zero, 𝟙 _⟩⟩
  | .inr (.inl a), v => S ⟨a, fun b ↦ v ⟨b, objOf .zero, homOf .left⟩⟩
  | .inr (.inr (e, o)), v =>
    S ⟨(eqns.side e (false ^^ o)).1, fun b ↦ v ⟨(eqns.side e (false ^^ o)).2 b, objOf .zero, 𝟙 _⟩⟩

/-- An algebra of the signature satisfies the equations when both sides of each
equation receive the same value at every assignment of the variables. -/
def Satisfies : Prop :=
  ∀ (e : eqns.E) (ρ : eqns.V e → Y), S (P.map ρ (eqns.lhs e)) = S (P.map ρ (eqns.rhs e))

variable {S}

/-- Restriction preserves {lit}`algVal` on argument values that do not depend on the
morphism of a direction, given that the algebra satisfies the equations. -/
theorem algVal_restr (sat : Satisfies (eqns := eqns) S) {c c' : Obj} (g : c' ⟶ c)
    (s : Shape P eqns) (hs : objOf (shapeObj s) = c) (v : (freeArity P eqns).Dir s → Y)
    (hv : ∀ (b : Gen s) (c c' : Obj) (f : c' ⟶ c) (k : c ⟶ objOf (genObj s b)),
      v ⟨b, c', f ≫ k⟩ = v ⟨b, c, k⟩) :
    algVal S ((freeArity P eqns).restr g s) (v ∘ (freeArity P eqns).reindexDir g s) =
      algVal S s v := by
  obtain ⟨_, x⟩ := c
  obtain ⟨_, x'⟩ := c'
  obtain ⟨_, h⟩ := g
  have hx : shapeObj s = x := congrArg Prod.snd hs
  cases h with
  | id => rcases s with a | a | ⟨e, o⟩ <;> rfl
  | left =>
    rcases s with a | a | ⟨e, o⟩
    · cases hx
    · rfl
    · rfl
  | right =>
    rcases s with a | a | ⟨e, o⟩
    · cases hx
    · exact congrArg S (Sigma.ext rfl (heq_of_eq (funext fun b ↦
        (hv b (objOf .one) (objOf .zero) (homOf .right) (𝟙 _)).trans
          (hv b (objOf .one) (objOf .zero) (homOf .left) (𝟙 _)).symm)))
    · cases o with
      | false => exact (sat e fun b ↦ v ⟨b, objOf .zero, 𝟙 _⟩).symm
      | true => exact sat e fun b ↦ v ⟨b, objOf .zero, 𝟙 _⟩

variable (S)

/-- The value of the model's algebra on a node over the discrete graph. -/
def modelApp {c : Objᵒᵖ}
    (n : ((qpra P eqns).objPresheaf (discrete (constPsh Y))).obj c) : Y :=
  algVal S n.1.1.1.1 fun d ↦ (n.1.1.1.2 d).2

/-- The model of the quotient presheaf polynomial functor given by an algebra of the
signature that satisfies the equations: a node goes to the value of its source
endpoint. -/
def model (sat : Satisfies (eqns := eqns) S) :
    NatTrans ((qpra P eqns).objPresheaf (discrete (constPsh Y))) (discrete (constPsh Y)) where
  app c := ↾ modelApp S
  naturality c c' g := by
    ext n
    obtain ⟨⟨n, hn⟩, hq⟩ := n
    exact algVal_restr sat g.unop n.1.1 hq (fun d ↦ (n.1.2 d).2)
      fun b c c' f k ↦ hn f ⟨⟨b, c, k⟩, rfl⟩

/-- The eliminator of the quotient W-type of the system into an algebra of the
signature that satisfies the equations. -/
def lift (sat : Satisfies (eqns := eqns) S) :
    NatTrans (quotient (qpra P eqns)) (constPsh Y) :=
  elim (qpra P eqns) (constPsh Y) (model S sat)

/-- The computation rule of {lit}`lift`: an operation applied to terms goes to the
algebra applied to the terms' values. -/
theorem lift_intro (sat : Satisfies (eqns := eqns) S) (a : P.A)
    (ts : P.B a → (qpra P eqns).W.obj ⟨objOf .zero⟩) :
    (lift S sat).app ⟨⟨⟨⟩⟩⟩ (intro (qpra P eqns) (freeNode _ (.inl a) ts)) =
      S ⟨a, fun b ↦ (lift S sat).app ⟨⟨⟨⟩⟩⟩ (quotientMk (qpra P eqns) (ts b))⟩ :=
  (elim_intro (qpra P eqns) (constPsh Y) (model S sat) _).trans
    (congrArg S (Sigma.ext rfl (heq_of_eq (funext fun b ↦
      congrArg ((PresheafPFunctor.W.elim (qpra P eqns) _ (model S sat)).app _)
        (W_map_id_apply (ts b))))))

end Model

end GebProto.QuotientPRA.Signature

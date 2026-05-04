/-
Syntactic representation of the free topos with binary tree object (BTO).

The binary tree object is the initial algebra of the polynomial endofunctor
BT(X) = 1 + X², representing unlabeled binary trees.

This is an inductive-inductive definition with three mutually defined sorts:
- Objects: the objects of the free topos
- Morphisms: morphisms between objects, parameterized by source and target
- Equalities: proofs of equality between parallel morphisms

The interpretation maps objects to Type, morphisms to functions, and
equalities to proofs of function equality. The subobject classifier
interprets as Prop.

Since Lean 4's mutual inductives have restrictions on inductive-inductive
patterns, we use a two-level construction:
1. FTObjBase with Hom and HomEq (no equalizers/coequalizers)
2. FTObj extending FTObjBase with equalizers/coequalizers of base morphisms
-/

namespace GebLean

/-- Binary trees (unlabeled). -/
inductive BinTree : Type where
  | leaf : BinTree
  | node : BinTree → BinTree → BinTree
  deriving DecidableEq, Repr, Inhabited

/-- Fold for binary trees. -/
def BinTree.fold {A : Type} (a : Unit → A) (f : A × A → A) : BinTree → A
  | leaf => a ()
  | node l r => f (fold a f l, fold a f r)

/-- Objects of the free topos with binary tree object (without equalizers). -/
inductive FTObjBase : Type where
  | initial : FTObjBase
  | terminal : FTObjBase
  | prod : FTObjBase → FTObjBase → FTObjBase
  | coprod : FTObjBase → FTObjBase → FTObjBase
  | exp : FTObjBase → FTObjBase → FTObjBase
  | omega : FTObjBase
  | bt : FTObjBase
  deriving DecidableEq, Repr

namespace FTObjBase

/-- Morphisms of the free topos (base version without equalizers). -/
inductive Hom : FTObjBase → FTObjBase → Type where
  -- Identity and composition
  | id : (A : FTObjBase) → Hom A A
  | comp : {A B C : FTObjBase} → Hom B C → Hom A B → Hom A C

  -- Terminal object
  | toTerminal : (A : FTObjBase) → Hom A terminal

  -- Initial object
  | fromInitial : (A : FTObjBase) → Hom initial A

  -- Binary products
  | fst : {A B : FTObjBase} → Hom (prod A B) A
  | snd : {A B : FTObjBase} → Hom (prod A B) B
  | pair : {A B C : FTObjBase} → Hom C A → Hom C B → Hom C (prod A B)

  -- Binary coproducts
  | inl : {A B : FTObjBase} → Hom A (coprod A B)
  | inr : {A B : FTObjBase} → Hom B (coprod A B)
  | copair : {A B C : FTObjBase} → Hom A C → Hom B C → Hom (coprod A B) C

  -- Exponentials (internal hom)
  | eval : {A B : FTObjBase} → Hom (prod (exp A B) A) B
  | curry : {A B C : FTObjBase} → Hom (prod C A) B → Hom C (exp A B)

  -- Subobject classifier
  | true : Hom terminal omega
  | char : {A B : FTObjBase} → Hom A B → Hom B omega

  -- Binary tree object (initial algebra of X ↦ 1 + X²)
  | leaf : Hom terminal bt
  | node : Hom (prod bt bt) bt
  | fold : {A : FTObjBase} → Hom terminal A → Hom (prod A A) A → Hom bt A

/-- Equality of parallel morphisms in the free topos (base version). -/
inductive HomEq : {A B : FTObjBase} → Hom A B → Hom A B → Type where
  -- Equivalence relation
  | refl : {A B : FTObjBase} → (f : Hom A B) → HomEq f f
  | symm : {A B : FTObjBase} → {f g : Hom A B} → HomEq f g → HomEq g f
  | trans : {A B : FTObjBase} → {f g h : Hom A B} →
      HomEq f g → HomEq g h → HomEq f h

  -- Congruence for composition
  | compCong : {A B C : FTObjBase} →
      {f₁ f₂ : Hom B C} → {g₁ g₂ : Hom A B} →
      HomEq f₁ f₂ → HomEq g₁ g₂ → HomEq (Hom.comp f₁ g₁) (Hom.comp f₂ g₂)

  -- Category laws
  | idLeft : {A B : FTObjBase} → (f : Hom A B) →
      HomEq (Hom.comp (Hom.id B) f) f
  | idRight : {A B : FTObjBase} → (f : Hom A B) →
      HomEq (Hom.comp f (Hom.id A)) f
  | assoc : {A B C D : FTObjBase} → (h : Hom C D) → (g : Hom B C) →
      (f : Hom A B) →
      HomEq (Hom.comp h (Hom.comp g f)) (Hom.comp (Hom.comp h g) f)

  -- Terminal object universal property
  | terminalUniq : {A : FTObjBase} → (f : Hom A terminal) →
      HomEq f (Hom.toTerminal A)

  -- Initial object universal property
  | initialUniq : {A : FTObjBase} → (f : Hom initial A) →
      HomEq f (Hom.fromInitial A)

  -- Product universal property
  | fstPair : {A B C : FTObjBase} → (f : Hom C A) → (g : Hom C B) →
      HomEq (Hom.comp Hom.fst (Hom.pair f g)) f
  | sndPair : {A B C : FTObjBase} → (f : Hom C A) → (g : Hom C B) →
      HomEq (Hom.comp Hom.snd (Hom.pair f g)) g
  | pairUniq : {A B C : FTObjBase} → (h : Hom C (prod A B)) →
      HomEq (Hom.pair (Hom.comp Hom.fst h) (Hom.comp Hom.snd h)) h

  -- Coproduct universal property
  | copairInl : {A B C : FTObjBase} → (f : Hom A C) → (g : Hom B C) →
      HomEq (Hom.comp (Hom.copair f g) Hom.inl) f
  | copairInr : {A B C : FTObjBase} → (f : Hom A C) → (g : Hom B C) →
      HomEq (Hom.comp (Hom.copair f g) Hom.inr) g
  | copairUniq : {A B C : FTObjBase} → (h : Hom (coprod A B) C) →
      HomEq (Hom.copair (Hom.comp h Hom.inl) (Hom.comp h Hom.inr)) h

  -- Exponential universal property (curry/eval adjunction)
  | evalCurry : {A B C : FTObjBase} → (h : Hom (prod C A) B) →
      HomEq (Hom.comp Hom.eval
        (Hom.pair (Hom.comp (Hom.curry h) Hom.fst) Hom.snd)) h
  | curryUniq : {A B C : FTObjBase} → (k : Hom C (exp A B)) →
      HomEq (Hom.curry (Hom.comp Hom.eval
        (Hom.pair (Hom.comp k Hom.fst) Hom.snd))) k

  -- Congruence for pair
  | pairCong : {A B C : FTObjBase} →
      {f₁ f₂ : Hom C A} → {g₁ g₂ : Hom C B} →
      HomEq f₁ f₂ → HomEq g₁ g₂ → HomEq (Hom.pair f₁ g₁) (Hom.pair f₂ g₂)

  -- Congruence for copair
  | copairCong : {A B C : FTObjBase} →
      {f₁ f₂ : Hom A C} → {g₁ g₂ : Hom B C} →
      HomEq f₁ f₂ → HomEq g₁ g₂ →
      HomEq (Hom.copair f₁ g₁) (Hom.copair f₂ g₂)

  -- Congruence for curry
  | curryCong : {A B C : FTObjBase} →
      {h₁ h₂ : Hom (prod C A) B} →
      HomEq h₁ h₂ → HomEq (Hom.curry h₁) (Hom.curry h₂)

  -- Congruence for char
  | charCong : {A B : FTObjBase} →
      {m₁ m₂ : Hom A B} →
      HomEq m₁ m₂ → HomEq (Hom.char m₁) (Hom.char m₂)

  -- Congruence for fold
  | foldCong : {A : FTObjBase} →
      {a₁ a₂ : Hom terminal A} → {f₁ f₂ : Hom (prod A A) A} →
      HomEq a₁ a₂ → HomEq f₁ f₂ →
      HomEq (Hom.fold a₁ f₁) (Hom.fold a₂ f₂)

  -- Subobject classifier (pullback property for characteristic morphisms)
  | charPullback : {A B : FTObjBase} → (m : Hom A B) →
      HomEq (Hom.comp (Hom.char m) m)
        (Hom.comp Hom.true (Hom.toTerminal A))

  -- Binary tree object universal property (initial algebra)
  | foldLeaf : {A : FTObjBase} → (a : Hom terminal A) →
      (f : Hom (prod A A) A) →
      HomEq (Hom.comp (Hom.fold a f) Hom.leaf) a
  | foldNode : {A : FTObjBase} → (a : Hom terminal A) →
      (f : Hom (prod A A) A) →
      HomEq (Hom.comp (Hom.fold a f) Hom.node)
        (Hom.comp f (Hom.pair
          (Hom.comp (Hom.fold a f) Hom.fst)
          (Hom.comp (Hom.fold a f) Hom.snd)))
  | foldUniq : {A : FTObjBase} → (a : Hom terminal A) →
      (f : Hom (prod A A) A) → (h : Hom bt A) →
      HomEq (Hom.comp h Hom.leaf) a →
      HomEq (Hom.comp h Hom.node)
        (Hom.comp f (Hom.pair
          (Hom.comp h Hom.fst)
          (Hom.comp h Hom.snd))) →
      HomEq h (Hom.fold a f)

/-- Interpretation of base objects into Type. -/
def interp : FTObjBase → Type
  | initial => Empty
  | terminal => Unit
  | prod A B => A.interp × B.interp
  | coprod A B => A.interp ⊕ B.interp
  | exp A B => A.interp → B.interp
  | omega => Prop
  | bt => BinTree

/-- Interpretation of base morphisms into functions. -/
def Hom.interp : {A B : FTObjBase} → Hom A B → (A.interp → B.interp)
  | _, _, id _ => fun x => x
  | _, _, comp g f => fun x => g.interp (f.interp x)
  | _, _, toTerminal _ => fun _ => ()
  | _, _, fromInitial _ => fun e => Empty.elim e
  | _, _, fst => fun p => p.1
  | _, _, snd => fun p => p.2
  | _, _, pair f g => fun x => (f.interp x, g.interp x)
  | _, _, inl => fun x => Sum.inl x
  | _, _, inr => fun x => Sum.inr x
  | _, _, copair f g => fun s => match s with
    | Sum.inl a => f.interp a
    | Sum.inr b => g.interp b
  | _, _, eval => fun p => p.1 p.2
  | _, _, curry h => fun c => fun a => h.interp (c, a)
  | _, _, true => fun _ => True
  | _, _, char m => fun b => ∃ a, m.interp a = b
  | _, _, leaf => fun _ => BinTree.leaf
  | _, _, node => fun p => BinTree.node p.1 p.2
  | _, _, fold a f => BinTree.fold a.interp f.interp

end FTObjBase

/-- Full objects of the free topos including equalizers and coequalizers. -/
inductive FTObj : Type where
  | base : FTObjBase → FTObj
  | equalizer : {A B : FTObjBase} → FTObjBase.Hom A B → FTObjBase.Hom A B →
      FTObj
  | coequalizer : {A B : FTObjBase} → FTObjBase.Hom A B → FTObjBase.Hom A B →
      FTObj

namespace FTObj

/-- Embedding of base objects. -/
abbrev initial : FTObj := base FTObjBase.initial
abbrev terminal : FTObj := base FTObjBase.terminal
abbrev prod (A B : FTObjBase) : FTObj := base (FTObjBase.prod A B)
abbrev coprod (A B : FTObjBase) : FTObj := base (FTObjBase.coprod A B)
abbrev exp (A B : FTObjBase) : FTObj := base (FTObjBase.exp A B)
abbrev omega : FTObj := base FTObjBase.omega
abbrev bt : FTObj := base FTObjBase.bt

end FTObj

/-- Morphisms in the full free topos with equalizers and coequalizers. -/
inductive FTHom : FTObj → FTObj → Type where
  -- Lift morphisms from base
  | ofBase : {A B : FTObjBase} → FTObjBase.Hom A B →
      FTHom (FTObj.base A) (FTObj.base B)

  -- Identity on equalizer/coequalizer objects
  | eqId : {A B : FTObjBase} → {f g : FTObjBase.Hom A B} →
      FTHom (FTObj.equalizer f g) (FTObj.equalizer f g)
  | coeqId : {A B : FTObjBase} → {f g : FTObjBase.Hom A B} →
      FTHom (FTObj.coequalizer f g) (FTObj.coequalizer f g)

  -- Equalizer structure
  | eqInc : {A B : FTObjBase} → {f g : FTObjBase.Hom A B} →
      FTHom (FTObj.equalizer f g) (FTObj.base A)
  | eqUniv : {A B C : FTObjBase} → {f g : FTObjBase.Hom A B} →
      (h : FTObjBase.Hom C A) →
      FTObjBase.HomEq (FTObjBase.Hom.comp f h) (FTObjBase.Hom.comp g h) →
      FTHom (FTObj.base C) (FTObj.equalizer f g)

  -- Coequalizer structure
  | coeqProj : {A B : FTObjBase} → {f g : FTObjBase.Hom A B} →
      FTHom (FTObj.base B) (FTObj.coequalizer f g)
  | coeqUniv : {A B C : FTObjBase} → {f g : FTObjBase.Hom A B} →
      (h : FTObjBase.Hom B C) →
      FTObjBase.HomEq (FTObjBase.Hom.comp h f) (FTObjBase.Hom.comp h g) →
      FTHom (FTObj.coequalizer f g) (FTObj.base C)

  -- Composition: base ; equalizer-to-base
  | compBaseEqInc : {A B C : FTObjBase} → {f g : FTObjBase.Hom B C} →
      FTObjBase.Hom A B →
      FTHom (FTObj.equalizer f g) (FTObj.base B) →
      FTHom (FTObj.base A) (FTObj.base B)

  -- Composition: equalizer-to-base ; base
  | compEqIncBase : {A B C : FTObjBase} → {f g : FTObjBase.Hom A B} →
      FTHom (FTObj.equalizer f g) (FTObj.base A) →
      FTObjBase.Hom A C →
      FTHom (FTObj.equalizer f g) (FTObj.base C)

  -- Composition: base ; coequalizer-proj
  | compBaseCoeqProj : {A B C : FTObjBase} → {f g : FTObjBase.Hom B C} →
      FTObjBase.Hom A B →
      FTHom (FTObj.base B) (FTObj.coequalizer f g) →
      FTHom (FTObj.base A) (FTObj.coequalizer f g)

  -- Composition: coequalizer-univ ; base
  | compCoeqUnivBase : {A B C D : FTObjBase} → {f g : FTObjBase.Hom A B} →
      FTHom (FTObj.coequalizer f g) (FTObj.base C) →
      FTObjBase.Hom C D →
      FTHom (FTObj.coequalizer f g) (FTObj.base D)

/-- Equality of morphisms in the full free topos. -/
inductive FTEq : {A B : FTObj} → FTHom A B → FTHom A B → Type where
  -- Equivalence relation
  | refl : {A B : FTObj} → (f : FTHom A B) → FTEq f f
  | symm : {A B : FTObj} → {f g : FTHom A B} → FTEq f g → FTEq g f
  | trans : {A B : FTObj} → {f g h : FTHom A B} →
      FTEq f g → FTEq g h → FTEq f h

  -- Lift equalities from base
  | ofBaseEq : {A B : FTObjBase} → {f g : FTObjBase.Hom A B} →
      FTObjBase.HomEq f g → FTEq (FTHom.ofBase f) (FTHom.ofBase g)

  -- Equalizer: inclusion equalizes (f ∘ inc = g ∘ inc)
  | eqIncEqualizes : {A B : FTObjBase} → {f g : FTObjBase.Hom A B} →
      FTEq (FTHom.compEqIncBase FTHom.eqInc f)
        (FTHom.compEqIncBase FTHom.eqInc g)

  -- Equalizer: universal property factorization (inc ∘ univ h p = h)
  | eqUnivFactor : {A B C : FTObjBase} → {f g : FTObjBase.Hom A B} →
      (h : FTObjBase.Hom C A) →
      (p : FTObjBase.HomEq (FTObjBase.Hom.comp f h) (FTObjBase.Hom.comp g h)) →
      FTEq (FTHom.compBaseEqInc h FTHom.eqInc) (FTHom.ofBase h)

  -- Coequalizer: projection coequalizes (proj ∘ f = proj ∘ g)
  | coeqProjCoequalizes : {A B : FTObjBase} → {f g : FTObjBase.Hom A B} →
      FTEq (FTHom.compBaseCoeqProj f FTHom.coeqProj)
        (FTHom.compBaseCoeqProj g FTHom.coeqProj)

  -- Coequalizer: universal property factorization (univ h p ∘ proj = h)
  | coeqUnivFactor : {A B C : FTObjBase} → {f g : FTObjBase.Hom A B} →
      (h : FTObjBase.Hom B C) →
      (p : FTObjBase.HomEq (FTObjBase.Hom.comp h f) (FTObjBase.Hom.comp h g)) →
      FTEq (FTHom.compCoeqUnivBase (FTHom.coeqUniv h p) (FTObjBase.Hom.id C))
        (FTHom.coeqUniv h p)

end GebLean

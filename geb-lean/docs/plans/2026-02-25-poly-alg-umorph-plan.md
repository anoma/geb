# Polynomial Algebra/Coalgebra Combinators Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans
> to implement this plan task-by-task.

**Goal:** Create `GebLean/PolyAlgUMorph.lean` with combinators that
construct `Endofunctor.Algebra` and `Endofunctor.Coalgebra` instances
for polynomial endofunctors, using the universal morphisms from
`PolyUMorph.lean`.

**Architecture:** A morphism `α : P ⟶ Q` in `PolyEndo X` induces a
pointwise map on evaluation `P(A) ⟶ Q(A)` for any carrier `A`. By
precomposing or postcomposing structure maps with these pointwise maps,
we get algebra pullback (contravariant) and coalgebra pushforward
(covariant). Specialized combinators for products, coproducts,
equalizers, and coequalizers follow by applying these to the specific
universal morphisms from `PolyUMorph.lean`.

**Tech Stack:** Lean 4, mathlib (`Endofunctor.Algebra`,
`Endofunctor.Coalgebra`), `GebLean.PolyUMorph`, `GebLean.PolyAlg`

---

## Definitions reference

- `PolyEndo X` = `PolyFunctorBetweenCat X X` =
  `FamilyCat (CoprodCovarRepCat (Over X)) X`
- `polyEndoFunctor X P : Over X ⥤ Over X` =
  `polyBetweenEvalFunctor X X P`
- `PolyAlg P` = `Endofunctor.Algebra (polyEndoFunctor X P)`
  - Fields: `a : Over X`, `str : (polyEndoFunctor X P).obj a ⟶ a`
- `PolyCoalg P` = `Endofunctor.Coalgebra (polyEndoFunctor X P)`
  - Fields: `V : Over X`, `str : V ⟶ (polyEndoFunctor X P).obj V`
- `Endofunctor.Algebra.Hom.mk (f : A₀.a ⟶ A₁.a)
    (h : F.map f ≫ A₁.str = A₀.str ≫ f) : A₀.Hom A₁`
- `Endofunctor.Coalgebra.Hom.mk (f : V₀.V ⟶ V₁.V)
    (h : V₀.str ≫ F.map f = f ≫ V₁.str) : V₀.Hom V₁`

A morphism `α : P ⟶ Q` in `PolyEndo X` is `∀ x, P x ⟶ Q x` in
`CoprodCovarRepCat (Over X)`. At each `x`, it has:
- `ccrReindex (α x) : polyBetweenIndex P x → polyBetweenIndex Q x`
- `ccrFiberMor (α x) i :
    polyBetweenFamily Q x (ccrReindex (α x) i) ⟶
    polyBetweenFamily P x i`

Evaluation: `polyBetweenEval X X P A` has
`.left = Σ x, Σ (i : polyBetweenIndex P x),
  (polyBetweenFamily P x i ⟶ A)`.

So `α` induces a map on eval:
`(x, i, f) ↦ (x, ccrReindex (α x) i, ccrFiberMor (α x) i ≫ f)`.

## Code style notes

- Line length: 80 characters max
- All code under `namespace GebLean`
- `autoImplicit = false` -- write all binders explicitly
- No `sorry`, no warnings
- Follow existing naming: `polyAlg*` / `polyCoalg*` prefix
- One definition at a time, build and verify after each

---

### Task 1: Create skeleton file and add import

**Files:**
- Create: `GebLean/PolyAlgUMorph.lean`
- Modify: `GebLean.lean`

**Step 1: Create the file with imports and module docstring**

```lean
import GebLean.PolyAlg
import GebLean.PolyUMorph

/-!
# Algebra and Coalgebra Combinators for Polynomial Endofunctors

Combinators that construct `Endofunctor.Algebra` and
`Endofunctor.Coalgebra` instances for polynomial endofunctors,
using the universal morphisms from `PolyUMorph.lean`.

## Main definitions

### General combinators

* `polyEndoMorphEvalAt` - Pointwise evaluation of a morphism
  of polynomial endofunctors
* `polyEndoMorphEval` - Natural transformation induced by a
  morphism of polynomial endofunctors
* `algPullback` - Pull back an algebra along a morphism of
  polynomial endofunctors
* `coalgPushforward` - Push forward a coalgebra along a
  morphism of polynomial endofunctors

### Coproduct algebras

* `algCoprodDesc` - Algebra for a coproduct of endofunctors
  from algebras of each component
* `algCoprodDescHom` - Algebra homomorphism combinator for
  coproduct algebras

### Product coalgebras

* `coalgProdLift` - Coalgebra for a product of endofunctors
  from coalgebras of each component
* `coalgProdLiftHom` - Coalgebra homomorphism combinator for
  product coalgebras

### Equalizer algebras

* `algEqRestrict` - Restrict an algebra to an equalizer
  subfunctor
* `algEqRestrictHom` - Algebra homomorphism combinator for
  equalizer algebras

### Coequalizer coalgebras

* `coalgCoeqExtend` - Extend a coalgebra to a coequalizer
  quotient functor
* `coalgCoeqExtendHom` - Coalgebra homomorphism combinator
  for coequalizer coalgebras

### Functorial combinators

* `algPullbackFunctor` - Functor from Q-algebras to
  P-algebras given `P ⟶ Q`
* `coalgPushforwardFunctor` - Functor from P-coalgebras to
  Q-coalgebras given `P ⟶ Q`
-/

namespace GebLean

open CategoryTheory

universe u

end GebLean
```

**Step 2: Add import to GebLean.lean**

Add `import GebLean.PolyAlgUMorph` after `import GebLean.PolyAlg`
in `GebLean.lean`.

**Step 3: Build**

Run: `lake build`
Expected: PASS with no warnings

**Step 4: Commit**

```
feat: scaffold PolyAlgUMorph.lean
```

---

### Task 2: Pointwise evaluation of a morphism

A morphism `α : P ⟶ Q` in `PolyEndo X` induces a map
`P(A) ⟶ Q(A)` for each `A : Over X`. This is not a map of the
endofunctor applied to a morphism of carriers; rather, it is a
natural transformation component at `A`. We need to construct
this as a morphism in `Over X`.

**Files:**
- Modify: `GebLean/PolyAlgUMorph.lean`

**Step 1: Define polyEndoMorphEvalAt**

The pointwise map on `polyBetweenEvalFamily`:

```lean
section PolyEndoMorphEval

variable {X : Type u}

/--
Pointwise evaluation of a polynomial endofunctor morphism at
a fiber. Given `α : P ⟶ Q` and `A : Over X`, at fiber `x`
the map sends `(i, f)` to
`(ccrReindex (α x) i, ccrFiberMor (α x) i ≫ f)`.
-/
def polyEndoMorphEvalAt
    {P Q : PolyEndo X} (α : P ⟶ Q) (A : Over X)
    (x : X) :
    polyBetweenEvalFamily X X P A x →
    polyBetweenEvalFamily X X Q A x :=
  fun ev => ptoefMk X
    (ccrReindex (α x) (ptoefIndex X ev))
    (ccrFiberMor (α x) (ptoefIndex X ev) ≫
      ptoefMor X ev)
```

Build and verify. This should reduce to
`fun ⟨i, f⟩ => ⟨ccrReindex (α x) i, ccrFiberMor (α x) i ≫ f⟩`.

**Step 2: Define polyEndoMorphEval**

The full morphism `P(A) ⟶ Q(A)` in `Over X`:

```lean
/--
Evaluation of a polynomial endofunctor morphism. Given
`α : P ⟶ Q` and `A : Over X`, produce
`(polyEndoFunctor X P).obj A ⟶ (polyEndoFunctor X Q).obj A`.
-/
def polyEndoMorphEval
    {P Q : PolyEndo X} (α : P ⟶ Q) (A : Over X) :
    (polyEndoFunctor X P).obj A ⟶
    (polyEndoFunctor X Q).obj A :=
  (familySliceForward X).map
    (fun x => polyEndoMorphEvalAt α A x)
```

Build and verify.

**Step 3: Prove naturality**

The naturality square: for `f : A ⟶ B`,
`polyEndoMorphEval α A ≫ (polyEndoFunctor X Q).map f =
 (polyEndoFunctor X P).map f ≫ polyEndoMorphEval α B`.

```lean
theorem polyEndoMorphEval_natural
    {P Q : PolyEndo X} (α : P ⟶ Q)
    {A B : Over X} (f : A ⟶ B) :
    polyEndoMorphEval α A ≫
      (polyEndoFunctor X Q).map f =
    (polyEndoFunctor X P).map f ≫
      polyEndoMorphEval α B := by
  -- Both sides act on (x, i, g) by:
  -- LHS: (x, ccrReindex (α x) i, ccrFiberMor (α x) i ≫ g ≫ f)
  -- RHS: (x, ccrReindex (α x) i, ccrFiberMor (α x) i ≫ (g ≫ f))
  -- These are equal by associativity of ≫
  ext ⟨x, ev⟩
  simp only [polyEndoMorphEval, polyEndoMorphEvalAt,
    polyEndoFunctor, polyBetweenEvalFunctor,
    polyToOverFunctor, polyToOverEvalMap,
    familySliceForwardMap, polyToOverEvalFamilyMap,
    Over.comp_left, Function.comp, Functor.map_comp,
    ptoefMk, ptoefIndex, ptoefMor, ccrEvalMap,
    Category.assoc]
```

Build and verify. The proof may need adjustment based on what
`simp` can handle; the mathematical content is just
associativity.

**Step 4: Commit**

```
feat(PolyAlgUMorph): pointwise evaluation of endofunctor morphisms
```

---

### Task 3: Algebra pullback and coalgebra pushforward

**Files:**
- Modify: `GebLean/PolyAlgUMorph.lean`

**Step 1: Define algPullback**

```lean
end PolyEndoMorphEval

section AlgPullback

variable {X : Type u}

/--
Pull back an algebra along a morphism of polynomial
endofunctors. Given `α : P ⟶ Q` and a Q-algebra `a`,
produce a P-algebra with the same carrier by precomposing
the structure map with `polyEndoMorphEval α a.a`.
-/
def algPullback
    {P Q : PolyEndo X} (α : P ⟶ Q) (a : PolyAlg Q) :
    PolyAlg P where
  a := a.a
  str := polyEndoMorphEval α a.a ≫ a.str
```

Build and verify.

**Step 2: Define coalgPushforward**

```lean
/--
Push forward a coalgebra along a morphism of polynomial
endofunctors. Given `α : P ⟶ Q` and a P-coalgebra `c`,
produce a Q-coalgebra with the same carrier by
postcomposing the structure map with
`polyEndoMorphEval α c.V`.
-/
def coalgPushforward
    {P Q : PolyEndo X} (α : P ⟶ Q)
    (c : PolyCoalg P) :
    PolyCoalg Q where
  V := c.V
  str := c.str ≫ polyEndoMorphEval α c.V
```

Build and verify.

**Step 3: Commit**

```
feat(PolyAlgUMorph): algebra pullback and coalgebra pushforward
```

---

### Task 4: Algebra and coalgebra homomorphism combinators

**Files:**
- Modify: `GebLean/PolyAlgUMorph.lean`

**Step 1: Define algPullbackHom**

An algebra homomorphism `h : a₁ ⟶ a₂` (between Q-algebras)
is also a homomorphism between the pulled-back P-algebras.
The proof uses naturality of `polyEndoMorphEval`.

```lean
/--
An algebra homomorphism between Q-algebras is also a
homomorphism between the pulled-back P-algebras.
-/
def algPullbackHom
    {P Q : PolyEndo X} (α : P ⟶ Q)
    {a₁ a₂ : PolyAlg Q} (h : a₁ ⟶ a₂) :
    algPullback α a₁ ⟶ algPullback α a₂ :=
  Endofunctor.Algebra.Hom.mk h.f (by
    -- Need: F_P.map h.f ≫ (α_eval ≫ a₂.str)
    --      = (α_eval ≫ a₁.str) ≫ h.f
    simp only [algPullback]
    rw [Category.assoc,
        ← polyEndoMorphEval_natural α h.f]
    rw [← Category.assoc, ← Category.assoc]
    rw [h.h]
    rw [Category.assoc])
```

Build and verify. The proof uses naturality to commute
`polyEndoMorphEval` past `F_P.map h.f`, then the original
homomorphism condition `h.h`.

**Step 2: Define coalgPushforwardHom**

```lean
/--
A coalgebra homomorphism between P-coalgebras is also a
homomorphism between the pushed-forward Q-coalgebras.
-/
def coalgPushforwardHom
    {P Q : PolyEndo X} (α : P ⟶ Q)
    {c₁ c₂ : PolyCoalg P} (h : c₁ ⟶ c₂) :
    coalgPushforward α c₁ ⟶ coalgPushforward α c₂ :=
  Endofunctor.Coalgebra.Hom.mk h.f (by
    simp only [coalgPushforward]
    rw [← Category.assoc,
        h.h,
        Category.assoc,
        polyEndoMorphEval_natural α h.f,
        ← Category.assoc])
```

Build and verify.

**Step 3: Commit**

```
feat(PolyAlgUMorph): algebra/coalgebra homomorphism combinators
```

---

### Task 5: Functorial versions of pullback and pushforward

**Files:**
- Modify: `GebLean/PolyAlgUMorph.lean`

**Step 1: Define algPullbackFunctor**

```lean
/--
Functor from Q-algebras to P-algebras induced by
`α : P ⟶ Q`.
-/
def algPullbackFunctor
    {P Q : PolyEndo X} (α : P ⟶ Q) :
    PolyAlg Q ⥤ PolyAlg P where
  obj := algPullback α
  map := algPullbackHom α
  map_id := fun a => by
    apply Endofunctor.Algebra.Hom.ext; rfl
  map_comp := fun f g => by
    apply Endofunctor.Algebra.Hom.ext; rfl
```

Build and verify.

**Step 2: Define coalgPushforwardFunctor**

```lean
/--
Functor from P-coalgebras to Q-coalgebras induced by
`α : P ⟶ Q`.
-/
def coalgPushforwardFunctor
    {P Q : PolyEndo X} (α : P ⟶ Q) :
    PolyCoalg P ⥤ PolyCoalg Q where
  obj := coalgPushforward α
  map := coalgPushforwardHom α
  map_id := fun c => by
    apply Endofunctor.Coalgebra.Hom.ext; rfl
  map_comp := fun f g => by
    apply Endofunctor.Coalgebra.Hom.ext; rfl
```

Build and verify.

**Step 3: Prove these commute with the forgetful functors**

```lean
/--
Pulling back algebras commutes with forgetting to `Over X`.
-/
theorem algPullbackFunctor_forget
    {P Q : PolyEndo X} (α : P ⟶ Q) :
    algPullbackFunctor α ⋙ PolyAlg.forget P =
      PolyAlg.forget Q := by
  apply Functor.ext
  · intro a; rfl
  · intro a₁ a₂ f; rfl

/--
Pushing forward coalgebras commutes with forgetting to
`Over X`.
-/
theorem coalgPushforwardFunctor_forget
    {P Q : PolyEndo X} (α : P ⟶ Q) :
    coalgPushforwardFunctor α ⋙ PolyCoalg.forget Q =
      PolyCoalg.forget P := by
  apply Functor.ext
  · intro c; rfl
  · intro c₁ c₂ f; rfl
```

Build and verify.

**Step 4: Commit**

```
feat(PolyAlgUMorph): functorial pullback/pushforward
```

---

### Task 6: Coproduct algebra combinator

**Files:**
- Modify: `GebLean/PolyAlgUMorph.lean`

**Step 1: Define algCoprodDesc**

Given algebras `a_i : PolyAlg (F i)` all with the same
carrier, construct an algebra for `polyBetweenCoprod I F`.
The structure map uses `polyBetweenCoprodDesc` applied to
the individual structure maps, evaluated at the carrier.

```lean
end AlgPullback

section CoprodAlgebra

variable {X : Type u}

/--
Construct an algebra for a coproduct of polynomial
endofunctors from compatible algebras with a shared
carrier. Given a family `F : I → PolyEndo X`, a carrier
`A : Over X`, and structure maps `str_i : F_i(A) ⟶ A`
for each `i`, the coproduct algebra has structure map
`(∐ F_i)(A) ⟶ A` built from the coproduct descent.
-/
def algCoprodDesc
    {I : Type u} {F : I → PolyEndo X}
    (A : Over X)
    (strs : ∀ i, (polyEndoFunctor X (F i)).obj A ⟶ A) :
    PolyAlg (polyBetweenCoprod I F) :=
  algPullback
    (polyBetweenCoprodDesc I F
      (polyBetweenId (X := X))
      (fun i => polyBetweenInj I F i))
    _   -- placeholder; see note below
```

Wait -- this approach is wrong. The coproduct descent goes
*out of* the coproduct, not *into* it. Let me reconsider.

The correct approach: we have injections
`ι_i : F i ⟶ ∐ F_i`. Using algebra pullback, an algebra of
`∐ F_i` would give algebras of each `F i`. We want the
*reverse*: given algebras of each `F i`, produce an algebra
of `∐ F_i`.

We also have the descent `polyBetweenCoprodDesc I F Q m :
∐ F_i ⟶ Q` given `m : ∀ i, F i ⟶ Q`. But we don't have
a morphism of polynomial endofunctors to apply here.

The construction is direct: we need to build
`(∐ F_i)(A) ⟶ A`. Elements of `(∐ F_i)(A)` are tagged:
`⟨x, ⟨⟨i, p⟩, f⟩⟩` where `i : I`, `p` is a position of
`F i` at `x`, and `f : polyBetweenFamily (F i) x p ⟶ A`.
The structure map sends this to `strs i` applied to the
element `⟨x, ⟨p, f⟩⟩` of `F_i(A)`.

The correct implementation is:

```lean
/--
Construct an algebra for a coproduct of polynomial
endofunctors from compatible algebras with a shared
carrier. Given structure maps `str_i : F_i(A) ⟶ A` for
each `i`, the coproduct algebra has structure map
`(∐ F_i)(A) ⟶ A` that dispatches each tagged element
to the appropriate component's structure map.
-/
def algCoprodDesc
    {I : Type u} {F : I → PolyEndo X}
    (A : Over X)
    (strs : ∀ i,
      (polyEndoFunctor X (F i)).obj A ⟶ A) :
    PolyAlg (polyBetweenCoprod I F) where
  a := A
  str := Over.homMk
    (fun ⟨x, ⟨⟨i, p⟩, f⟩⟩ =>
      (strs i).left ⟨x, ⟨p, f⟩⟩)
    (by
      funext ⟨x, ⟨⟨i, p⟩, f⟩⟩
      exact congrFun (Over.w (strs i)) ⟨x, ⟨p, f⟩⟩)
```

Build and verify. The proof obligation is that the structure
map commutes over `X`, which follows from each `strs i`
commuting over `X`.

**Step 2: Build and verify**

Run: `lake build`
Expected: PASS

**Step 3: Commit**

```
feat(PolyAlgUMorph): coproduct algebra combinator
```

---

### Task 7: Coproduct algebra homomorphism combinator

**Files:**
- Modify: `GebLean/PolyAlgUMorph.lean`

**Step 1: Define algCoprodDescHom**

Given a morphism `h : A ⟶ B` that is simultaneously a
homomorphism for each `F i`-algebra, it is also a
homomorphism for the coproduct algebra.

```lean
/--
A morphism that is simultaneously a homomorphism for each
component algebra is a homomorphism for the coproduct
algebra.
-/
def algCoprodDescHom
    {I : Type u} {F : I → PolyEndo X}
    {A B : Over X}
    {strsA : ∀ i,
      (polyEndoFunctor X (F i)).obj A ⟶ A}
    {strsB : ∀ i,
      (polyEndoFunctor X (F i)).obj B ⟶ B}
    (h : A ⟶ B)
    (hcomm : ∀ i,
      (polyEndoFunctor X (F i)).map h ≫ strsB i =
        strsA i ≫ h) :
    algCoprodDesc A strsA ⟶
      algCoprodDesc B strsB :=
  Endofunctor.Algebra.Hom.mk h (by
    -- The coproduct structure map dispatches by tag;
    -- the proof follows from the component proofs.
    ext ⟨x, ⟨⟨i, p⟩, f⟩⟩
    -- Use the i-th component's commutativity
    have hi := hcomm i
    exact congrFun (congrArg CommaMorphism.left hi)
      ⟨x, ⟨p, f⟩⟩)
```

Build and verify. The proof strategy: both sides dispatch
by tag `i`, then the commutativity for tag `i` follows from
`hcomm i`.

**Step 2: Build and verify**

Run: `lake build`
Expected: PASS

**Step 3: Commit**

```
feat(PolyAlgUMorph): coproduct algebra homomorphism combinator
```

---

### Task 8: Product coalgebra combinator

**Files:**
- Modify: `GebLean/PolyAlgUMorph.lean`

**Step 1: Define coalgProdLift**

Dual to `algCoprodDesc`. Given coalgebras with the same
carrier for each component `F i`, construct a coalgebra for
`∏ F_i`. Elements of `(∏ F_i)(A)` at fiber `x` are tuples
`(p : ∀ i, polyBetweenIndex (F i) x, f : ∐_i
polyBetweenFamily (F i) x (p i) ⟶ A)`. The structure map
`A ⟶ (∏ F_i)(A)` assembles the individual structure maps.

```lean
end CoprodAlgebra

section ProdCoalgebra

variable {X : Type u}

/--
Construct a coalgebra for a product of polynomial
endofunctors from compatible coalgebras with a shared
carrier. Given structure maps `str_i : A ⟶ F_i(A)` for
each `i`, the product coalgebra has structure map
`A ⟶ (∏ F_i)(A)` that tuples the component structure
maps.
-/
def coalgProdLift
    {I : Type u} {F : I → PolyEndo X}
    (A : Over X)
    (strs : ∀ i,
      A ⟶ (polyEndoFunctor X (F i)).obj A) :
    PolyCoalg (polyBetweenProd I F) where
  V := A
  str := Over.homMk
    (fun a =>
      let x := A.hom a
      ⟨x, (fun i =>
          ptoefIndex X
            (ptoeLeftFiber X ((strs i).left a))),
        Over.homMk
          (fun ⟨i, e⟩ =>
            (ptoefMor X
              (ptoeLeftFiber X
                ((strs i).left a))).left e)
          (by
            funext ⟨i, e⟩
            exact congrFun
              (Over.w
                (ptoefMor X
                  (ptoeLeftFiber X
                    ((strs i).left a))))
              e)⟩)
    (by
      funext a
      simp only [Over.mk_hom, Function.comp]
      rfl)
```

This is more involved. The implementation constructs the
product tuple position-by-position, and assembles the
coproduct fiber morphism from the components. The proof
obligations are that things project correctly to `X`.

Build and verify. This definition may need adjustment based
on the exact types -- implement with underscores first to
discover the types, then fill in.

**Step 2: Build and verify**

Run: `lake build`
Expected: PASS (may need iteration)

**Step 3: Commit**

```
feat(PolyAlgUMorph): product coalgebra combinator
```

---

### Task 9: Product coalgebra homomorphism combinator

**Files:**
- Modify: `GebLean/PolyAlgUMorph.lean`

**Step 1: Define coalgProdLiftHom**

Dual to `algCoprodDescHom`.

```lean
/--
A morphism that is simultaneously a homomorphism for each
component coalgebra is a homomorphism for the product
coalgebra.
-/
def coalgProdLiftHom
    {I : Type u} {F : I → PolyEndo X}
    {A B : Over X}
    {strsA : ∀ i,
      A ⟶ (polyEndoFunctor X (F i)).obj A}
    {strsB : ∀ i,
      B ⟶ (polyEndoFunctor X (F i)).obj B}
    (h : A ⟶ B)
    (hcomm : ∀ i,
      strsA i ≫ (polyEndoFunctor X (F i)).map h =
        h ≫ strsB i) :
    coalgProdLift A strsA ⟶
      coalgProdLift B strsB :=
  Endofunctor.Coalgebra.Hom.mk h (by
    -- Proof: both sides map a to a tuple; component-
    -- wise they agree by hcomm i
    _)
```

The proof will require showing that the product structure
maps compose correctly. Use underscore to discover goal,
then apply component-wise reasoning using `hcomm`.

**Step 2: Build and verify**

Run: `lake build`
Expected: PASS (may need iteration)

**Step 3: Commit**

```
feat(PolyAlgUMorph): product coalgebra homomorphism combinator
```

---

### Task 10: Equalizer algebra restriction

**Files:**
- Modify: `GebLean/PolyAlgUMorph.lean`

**Step 1: Define algEqRestrict**

This is just `algPullback` applied to the equalizer
inclusion.

```lean
end ProdCoalgebra

section EqAlgebra

variable {X : Type u}

/--
Restrict an algebra to an equalizer subfunctor. Given
`f, g : P ⟶ Q` and a P-algebra, produce an algebra for
`polyBetweenEq f g` by pulling back along the equalizer
inclusion.
-/
def algEqRestrict
    {P Q : PolyEndo X} {f g : P ⟶ Q}
    (a : PolyAlg P) :
    PolyAlg (polyBetweenEq f g) :=
  algPullback (polyBetweenEqIncl f g) a
```

Build and verify.

**Step 2: Define algEqRestrictHom**

```lean
/--
An algebra homomorphism between P-algebras restricts to a
homomorphism between the equalizer algebras.
-/
def algEqRestrictHom
    {P Q : PolyEndo X} {f g : P ⟶ Q}
    {a₁ a₂ : PolyAlg P} (h : a₁ ⟶ a₂) :
    algEqRestrict a₁ ⟶ algEqRestrict (f := f) (g := g) a₂ :=
  algPullbackHom (polyBetweenEqIncl f g) h
```

Build and verify.

**Step 3: Commit**

```
feat(PolyAlgUMorph): equalizer algebra restriction
```

---

### Task 11: Coequalizer coalgebra extension

**Files:**
- Modify: `GebLean/PolyAlgUMorph.lean`

**Step 1: Define coalgCoeqExtend**

This is `coalgPushforward` applied to the coequalizer
projection.

```lean
end EqAlgebra

section CoeqCoalgebra

variable {X : Type u}

/--
Extend a coalgebra to a coequalizer quotient functor.
Given `s, t : P ⟶ Q` and a Q-coalgebra, produce a
coalgebra for `polyBetweenCoeq s t` by pushing forward
along the coequalizer projection.
-/
def coalgCoeqExtend
    {P Q : PolyEndo X} {s t : P ⟶ Q}
    (c : PolyCoalg Q) :
    PolyCoalg (polyBetweenCoeq s t) :=
  coalgPushforward (polyBetweenCoeqProj s t) c
```

Build and verify.

**Step 2: Define coalgCoeqExtendHom**

```lean
/--
A coalgebra homomorphism between Q-coalgebras extends to
a homomorphism between the coequalizer coalgebras.
-/
def coalgCoeqExtendHom
    {P Q : PolyEndo X} {s t : P ⟶ Q}
    {c₁ c₂ : PolyCoalg Q} (h : c₁ ⟶ c₂) :
    coalgCoeqExtend c₁ ⟶
      coalgCoeqExtend (s := s) (t := t) c₂ :=
  coalgPushforwardHom (polyBetweenCoeqProj s t) h
```

Build and verify.

**Step 3: Commit**

```
feat(PolyAlgUMorph): coequalizer coalgebra extension
```

---

### Task 12: Factorization properties

These theorems state that the specialized combinators
interact correctly with the universal morphisms.

**Files:**
- Modify: `GebLean/PolyAlgUMorph.lean`

**Step 1: Coproduct factorization**

Pulling back a coproduct algebra along `ι_j` recovers the
`j`-th component algebra.

```lean
end CoeqCoalgebra

section Factorization

variable {X : Type u}

/--
Pulling back a coproduct algebra along the `j`-th injection
recovers the `j`-th component algebra.
-/
theorem algCoprodDesc_pullback_inj
    {I : Type u} {F : I → PolyEndo X}
    (A : Over X)
    (strs : ∀ i,
      (polyEndoFunctor X (F i)).obj A ⟶ A)
    (j : I) :
    algPullback (polyBetweenInj I F j)
      (algCoprodDesc A strs) =
    ⟨A, strs j⟩ := by
  -- Both have carrier A and structure map strs j
  _
```

**Step 2: Product factorization**

Pushing forward a product coalgebra along `π_j` recovers
the `j`-th component coalgebra.

```lean
/--
Pushing forward a product coalgebra along the `j`-th
projection recovers the `j`-th component coalgebra.
-/
theorem coalgProdLift_pushforward_proj
    {I : Type u} {F : I → PolyEndo X}
    (A : Over X)
    (strs : ∀ i,
      A ⟶ (polyEndoFunctor X (F i)).obj A)
    (j : I) :
    coalgPushforward (polyBetweenProj I F j)
      (coalgProdLift A strs) =
    ⟨A, strs j⟩ := by
  _
```

These will require showing that the composition of the
universal morphism with the inclusion/projection
recovers the component. Build with underscores, examine
goals, then fill in proofs.

**Step 3: Build and verify**

Run: `lake build`
Expected: PASS (may need iteration on proof terms)

**Step 4: Commit**

```
feat(PolyAlgUMorph): factorization properties
```

---

### Task 13: Exponential combinator (stretch goal)

Investigate whether the curry/uncurry adjunction from
`PolyUMorph.lean` yields a clean algebra combinator. The
candidate: given a `(Q × P)`-algebra, curry the structure
map component to get a `[Q, P]`-related construction.

This task may be deferred if the types don't work out
cleanly. Evaluate by attempting the definition with
underscores and examining the resulting goals.

**Files:**
- Modify: `GebLean/PolyAlgUMorph.lean`

**Step 1: Explore the types**

Define with underscores:

```lean
section ExpAlgebra

variable {X : Type u}

def algCurry
    {P Q S : PolyEndo X}
    (a : PolyAlg (pbBinaryProdObj Q P)) :
    PolyAlg (polyBetweenHomObj Q S) := by
  exact _

end ExpAlgebra
```

Build, examine the goal, and determine whether a clean
combinator exists. If so, implement. If the types don't
align (the exponential of polynomial functors operates
at the functor level, not the carrier level), document
why and close this task.

**Step 2: Build and evaluate**

Run: `lake build`
Evaluate based on the goals.

**Step 3: Commit (if implemented)**

```
feat(PolyAlgUMorph): exponential algebra combinator
```

---

## Verification checklist

After all tasks:

1. `lake build` passes with zero warnings
2. `lake test` passes
3. All definitions have docstrings
4. Line length <= 80 characters
5. No `sorry`, no `_` placeholders
6. All section variables are used
7. File is imported in `GebLean.lean`

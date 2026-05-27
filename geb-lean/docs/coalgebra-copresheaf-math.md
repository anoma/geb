# Coalgebra-Copresheaf Equivalence: Mathematical Findings

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Sources](#sources)
- [Statement](#statement)
- [The Cofree Category](#the-cofree-category)
- [The Equivalence: Two-Step Decomposition](#the-equivalence-two-step-decomposition)
  - [Step A: Functor-Coalgebras ≌ Comonad-Coalgebras](#step-a-functor-coalgebras-%E2%89%8C-comonad-coalgebras)
  - [Step B: Comonad-Coalgebras ≌ Copresheaves](#step-b-comonad-coalgebras-%E2%89%8C-copresheaves)
- [Connection to Our Infrastructure](#connection-to-our-infrastructure)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Sources

- Adamek, Porst: "Algebra ∩ Coalgebra = Presheaves"
  (CALCO 2005, TCS 2006)
- Spivak: "The free monad, cofree comonad, and
  topological space associated to a polynomial" (2022)
- Libkind, Spivak: "Pattern runs on matter" (2024)
- Worrell: "A note on coalgebras and presheaves" (2002)
- `.claude/docs/two-topoi-associated-with-polynomials.md`

## Statement

For a polynomial endofunctor `P` on `Set/X`:

```text
Coalg(P) ≌ Set^{C_P}
```

where `C_P` is the cofree category (cofree comonoid)
on `P`, and `Set^{C_P}` denotes covariant functors
`C_P → Set` (copresheaves).

## The Cofree Category

In the monoidal category `(Poly, y, ◁)` where `◁`
is the substitution/composition product:

- Comonoids are categories (Ahman-Uustalu, Spivak)
- The cofree comonoid on `P` is the cofree comonad
  `c_P`, constructed as a limit of approximations
  `p^(i)` where:
  - `p^(0) = y` (identity)
  - `p^(i+1) = y × (P ◁ p^(i))`

In our codebase, this is `polyCofreeMPoly P` with:

- Objects: `PolyCofreeShape P x` (behavior trees)
- Morphisms: positions in the source shape tree,
  given by `PolyCofreeAnnotPos P s`
- Composition: path concatenation
  (`polyCofreeAnnotPosConcat`)
- This is `PolyCofreeCat P` with its `Category`
  instance

## The Equivalence: Two-Step Decomposition

### Step A: Functor-Coalgebras ≌ Comonad-Coalgebras

For an adjunction `L ⊣ R` with induced comonad
`D = R ∘ L`, the comparison functor `K` from the
original category to the Eilenberg-Moore category of
D-coalgebras is:

```text
K(α) = (U(α), U(η_α) : U(α) → DU(α))
```

where `U` is the forgetful functor and `η` is the
unit of the adjunction.

For `Forget ⊣ Cofree` on P-coalgebras:

- `K(V, str) = (V, polyCoalgUnit P (V, str))`
- The unit unfolds each element into its anamorphism
  tree

This is an equivalence when the adjunction is
comonadic: the forgetful functor `Forget : Coalg(P) →
Over X` creates equalizers of U-split (reflexive)
pairs.  For polynomial endofunctors on Set/X, this
holds because:

1. Over X has all equalizers
2. The forgetful functor reflects isomorphisms
3. The cofree coalgebra construction preserves the
   relevant limits

### Step B: Comonad-Coalgebras ≌ Copresheaves

A D-coalgebra is `(A, k : A → D(A))` where `D` is
the cofree comonad.  By `polyCofreeComonadIso`:

```text
D(A) ≅ polyBetweenEval (polyCofreeMPoly P) A
```

At each fiber `x`, this evaluation is:

```text
Σ (s : PolyCofreeShape P x),
  (polyCofreeFamily P x s ⟶ A)
```

The D-coalgebra structure `k` assigns to each element
of `A` at fiber `x` a pair `(shape, morphism)`.
The shape `s` determines the "behavior tree" of the
element, and the morphism provides the annotation data
at each position.

A copresheaf `F : PolyCofreeCat P ⥤ Type u` assigns
to each `⟨x, s⟩` a type `F(⟨x, s⟩)`, and to each
morphism (position) a function.

**Coalgebra to Copresheaf (Phi):**

The copresheaf at `⟨x, s⟩` is the set of elements
of `A` at fiber `x` whose behavior shape is `s`:

```text
Φ(A, k)(⟨x, s⟩) = { a : A.left | A.hom a = x ∧
    (k a).shape = s }
```

The functorial action on morphisms uses the position
structure: a morphism `⟨x, s⟩ → ⟨y, t⟩` (a position
`pos` in `s`) maps an element `a` (with shape `s`)
to the "child" at position `pos` (which has shape
`t`).

**Copresheaf to Coalgebra (Psi):**

The carrier is the Grothendieck construction:

```text
Ψ(F).left = Σ (obj : PolyCofreeCat P), F.obj obj
Ψ(F).hom ⟨obj, _⟩ = obj.fiber
```

The coalgebra structure uses the polynomial shape:
for `⟨⟨x, s⟩, v⟩`, the first level of `s`
(via `s.head`) determines the P-index, and
`F.map` applied to the depth-1 morphisms provides
the children.

**Roundtrips:**

- `Φ(Ψ(F)) ≅ F`: elements of `Σ obj, F.obj obj`
  with shape `s` at fiber `x` correspond to
  `F.obj ⟨x, s⟩` (the fiber decomposes the sigma)
- `Ψ(Φ(A,k)) ≅ (A,k)`: the Grothendieck construction
  on the sections of `A` recovers `A` by the
  polynomial evaluation equivalence

## Connection to Our Infrastructure

| Mathematical concept | Our definition |
| --- | --- |
| Cofree category C_P | `PolyCofreeCat P` |
| C_P objects | `⟨x, s⟩ : PolyCofreeCat P` |
| C_P morphisms | `PolyCofreeCatHom P` |
| Copresheaf | `Copresheaf (PolyCofreeCat P)` |
| Cofree comonad D | `polyCofreeComonad P` |
| D ≅ poly eval | `polyCofreeComonadIso P` |
| P-coalgebra | `PolyCoalg P` |
| Forget ⊣ Cofree | `polyForgetCofreeAdjunction P` |
| Anamorphism | `polyCoalgUnit P α` |
| Shape extraction | `polyCofreeToShape` |
| Poly family at s | `polyCofreeFamily P x s` |

# Universe Bump in (Co)end Constructions

This document analyzes why instantiating `HasAllHomToProfCoends`
for `Type v` (and more generally for presheaf categories `E ⥤ Type v`)
would violate universe constraints.

## 1. Restricted coends

`HasAllHomToProfCoends G` (WeightedAlg.lean:1283) requires
`HasRestrictedCoend G (HomToProf pt)` for every `pt : C`, where
`G : Cᵒᵖ ⥤ C ⥤ C`. Built on this class:

- `GExtFunctor G : C ⥤ C` (the G-extension endofunctor)
- `mendlerLambekEquiv` (equivalence between Mendler algebras and
  conventional `GExtFunctor G`-algebras)

We want to instantiate it for `C = Type v` (and `C = E ⥤ Type v` for
small `E`).

## 2. The universe inconsistency

### 2.1 How typeCoend works

`typeCoend` (EndsAndCoends.lean:110) constructs the coend of
`F : Jᵒᵖ ⥤ J ⥤ Type v` as:

```lean
typeCoend F := Quot (typeCoendRel F) : Type (max u v)
```

where `J : Type u` and `Category.{v} J`. The underlying type is
`Σ (j : J), (F.obj (op j)).obj j`. Since `j : J` ranges over
`Type u`, the sigma type lives in `Type (max u v)`.

When `u = v` (i.e., `J : Type v`), `typeCoend F : Type v`. This
matches `Type v`, so it can serve as a cowedge apex in `Type v`.

When `u > v`, `typeCoend F : Type (max u v) = Type u`, which is too
large for a cowedge apex in `Type v`.

### 2.2 Where the restriction appears

`typeCoendCowedge` (EndsAndCoends.lean:128) and
`typeCoendCowedge_isInitial` (EndsAndCoends.lean:153) both require:

```lean
variable {J : Type v} [Category.{v} J]
```

This ensures `typeCoend F : Type v`, which can serve as an apex in
`Type v`. The restriction is not removable: with `J : Type u` for
`u > v`, the quotient type genuinely lives in `Type u`.

### 2.3 Application to C = Type v

For `C = Type v`:

- `C : Type (v+1)` with `Category.{v} C`
- Setting `J = C` gives `u = v+1`
- `typeCoend (copowerProf (HomToProf pt) G) : Type (v+1)`
- This does not fit as an object of `C = Type v`

The same arithmetic applies to `C = E ⥤ Type v` for `E : Type v`:
`C : Type (v+1)`.

## 3. The Bump Is Symmetric

### 3.1 Ends

`typeEnd` (EndsAndCoends.lean:38) is defined as:

```lean
def typeEnd (F : Jᵒᵖ ⥤ J ⥤ Type v) : Type (max u v) :=
  { x : (j : J) → (F.obj (op j)).obj j // ... }
```

The Pi type `(j : J) → T j` for `J : Type u` and `T j : Type v`
lives in `Type (max u v)` by Lean's universe rules: the sort of
`(a : Sort (u+1)) → Sort (v+1)` is `Sort (imax (u+1) (v+1))`,
which equals `Sort (max u v + 1) = Type (max u v)` when `v > 0`.

`typeEndWedge` (EndsAndCoends.lean:56) has the same restriction
`{J : Type v} [Category.{v} J]`.

### 3.2 Nat trans (impredicative characterization)

`typeCoend.impredicative` (EndsAndCoends.lean:1555) gives:

```lean
(weightedLimitFunctor (homPre (C := J))
  (Functor.uncurry.obj P) ⟶ 𝟭 (Type v)) ≃ typeCoend P
```

This lives in the `NinjaYoneda` section (EndsAndCoends.lean:1083),
which requires `{J : Type v} [Category.{v} J]`.

The restriction is inherited from `weightedLimitFunctor`
(Weighted.lean:2240), which is defined in a section with
`{J : Type v} [Category.{v} J]` (Weighted.lean:2226).

The reason `weightedLimitFunctor` requires `J : Type v`: it is
defined as:

```lean
homToFunctorBifunctor.obj (op D) ⋙ coyoneda.obj (op W')
```

`coyoneda.obj (op W')` maps a presheaf `F : Jᵒᵖ ⥤ Type v` to the
hom-set `NatTrans(W', F)`. The nat trans type involves
`∀ (j : J), W'.obj j → F.obj j`, which for `J : Type u` lives in
`Type (max u v)`. For the output to land in `Type v` (matching the
declared return type `C ⥤ Type v`), we need `max u v = v`, hence
`u ≤ v`.

### 3.3 Summary table

| Construction | Defined for | Result universe | Cowedge/initiality |
| - | - | - | - |
| `typeCoend` (Sigma/Quot) | `J : Type u` | `Type (max u v)` | `J : Type v` |
| `typeEnd` (Pi/Subtype) | `J : Type u` | `Type (max u v)` | `J : Type v` |
| `typeCoend.impredicative` | `J : Type v` | `Type v` | `J : Type v` |
| `weightedLimitFunctor` | `J : Type v` | `C ⥤ Type v` | n/a |
| `typeCoend.endEquiv` | `J : Type u` | `Type (max u v)` | n/a |

The quantifier over `J` (whether Sigma, Pi, or universal in a nat
trans) produces the same universe bump. No existing characterization
avoids it.

## 4. Approaches Considered

### 4.1 Density reduction (co-Yoneda)

**Idea:** For `C = E ⥤ Type v`, express the coend
`∫^{A : C} (A ⟶ pt) · G(A, A)` as a coend over the small category
`E` using density (every presheaf is a colimit of representables).

**Why it fails:** The integrand `G(A, A)` is dinatural in `A`
(covariant in one argument, contravariant in the other). The
co-Yoneda lemma applies to functorial integrands, not dinatural ones.

Concretely, the co-Yoneda lemma says
`∫^A (A ⟶ pt) × F(A) ≅ F(pt)` when `F` is a functor (covariant in
`A`). But `A ↦ G(A, A)` is not a functor: given `f : A → B`, we
cannot coherently map `G(A, A) → G(B, B)` because `G` is
contravariant in the first argument and covariant in the second.

**Test case:** For `E = PUnit` (terminal category), `C ≅ Type v`, and
the "reduced" coend over `PUnit` has only one component
`pt × G(*, *)`, which cannot equal the full restricted coend
`∫^{A : Type v} (A → pt) × G(A, A)`.

### 4.2 Generalize target to D ≠ C

**Idea:** Allow `HasAllHomToProfCoends` to produce `GExtFunctor`
landing in a larger universe: `GExtFunctor G : C ⥤ D` where
`D = Type (max u v)`.

**Why it fails:** The Mendler-Lambek equivalence requires `GExtFunctor`
to be an endofunctor `C ⥤ C`, because conventional algebras are
defined for endofunctors: an `F`-algebra is `(pt, φ : F(pt) ⟶ pt)`,
requiring `F(pt)` and `pt` to live in the same category.

For `C = Type v`, this would give `GExtFunctor : Type v ⥤ Type (v+1)`,
which is not an endofunctor. The algebra structure `F(pt) ⟶ pt`
would require a morphism from `Type (v+1)` to `Type v`, which is
ill-typed.

### 4.3 Generalize impredicative characterization

**Idea:** Extend `typeCoend.impredicative` to `J : Type u` by
allowing `weightedLimitFunctor` to output values in
`Type (max u v)`.

**Why it doesn't help:** The generalized weighted limit functor
would produce `C ⥤ Type (max u v)`. The impredicative
characterization would then give nat trans between functors
`C ⥤ Type (max u v)`, which lives in `Type (max u v)` (not
`Type v`). The universe bump reappears in the nat trans type.

The existing characterization avoids the bump only because it
requires `J : Type v`, making `max u v = v` trivially.

### 4.4 Twisted arrow category / colimit formulation

**Idea:** Express the coend as a colimit over the twisted arrow
category `tw(C)`, then find a small cofinal subcategory.

**Why it fails:** For `C = Type v`, the twisted arrow category has
objects `(A : Type v, B : Type v, f : A → B)`, so
`tw(C) : Type (v+1)`. It is still large.

Finding a small cofinal subcategory would require reducing the
indexing to `Type v`, which encounters the same problem: the
coend integrand is dinatural, so the colimit diagram does not factor
through a small subcategory via co-Yoneda or density.

### 4.5 Slice category approach

**Idea:** Express the coend as a colimit over the slice category
`C / pt` (category of elements of `yoneda.obj pt`).

**Why it fails:** The coend `∫^A (A ⟶ pt) · G(A, A)` is NOT the
colimit of `G(A, A)` over `C / pt`. The colimit over `C / pt` would
give `∫^A (A ⟶ pt) ⊗ F(A)` for a FUNCTOR `F`, which by co-Yoneda
equals `F(pt)`. But `A ↦ G(A, A)` is not a functor (same dinatural
issue as Section 4.1).

## 5. Existing Pattern: sliceProfunctorPoly

The codebase already contains an instance of the same universe bump
pattern. `sliceProfunctorPoly` (Weighted.lean:3672) was created
because `sliceProfunctor` (Weighted.lean:3621) produces values in
`Type v`, but some applications need the hom-set `G(A, A) → c` for
`c : Type p` with `p ≠ v`:

```lean
def sliceProfunctorPoly
    (G : Cᵒᵖ ⥤ C ⥤ Type w) (c : Type p) :
    Cᵒᵖ ⥤ C ⥤ Type (max w p)
```

The docstring notes: "This is useful when the apex needs to be a
'large' type like `StructuralCoend F : Type (v+1)` even when `G` is
valued in `Type v`."

This confirms the universe bump is a known issue in the codebase, not
an oversight.

## 6. What RestrictedCowedge Does Not Require

`RestrictedCowedge` (Weighted.lean:4973) is defined with:

```lean
structure RestrictedCowedge
    {D : Type w} [Category.{v} D]
    (G : Cᵒᵖ ⥤ C ⥤ D) (H : Cᵒᵖ ⥤ C ⥤ Type v) where
  pt : D
  toRestrictedCowedgeOver : RestrictedCowedgeOver G H pt
```

The apex `pt : D` is an object of `D`; there is no universe
constraint forcing `pt` to be constructed via Sigma or Pi. The
_definition_ of restricted cowedges does not require a higher
universe level, but the _construction_ of an initial one
quantifies over `C` and bumps the universe.

## 7. The Chain of Equivalences

The existing infrastructure provides:

```text
RestrictedCowedge G (HomToProf pt)
  ≅ Cowedge (copowerProf (HomToProf pt) G)
                                  [homRestrictedCopowerIso]
```

So `HasRestrictedCoend G (HomToProf pt)` is equivalent to having an
initial cowedge of `copowerProf (HomToProf pt) G : Cᵒᵖ ⥤ C ⥤ C`.

For `C = Type v`, this profunctor sends `(A, B)` to:

```text
copower (A ⟶ pt) (G(op A, B))
  = (A → pt) × G(op A, B) : Type v
```

The coend of this profunctor would be the sigma-quotient:

```text
Quot (Σ (A : Type v), (A → pt) × G(op A, A))
  : Type (v+1)
```

which is one universe too large.

## 8. Open Questions

1. Is there a construction technique for initial restricted cowedges
   that does not quantify over the indexing category `C`?

2. Can the Mendler-Lambek equivalence be reformulated to avoid
   requiring the restricted coend to exist as an object of `C`?
   For instance, could the equivalence be stated in terms of the
   universal property directly, without reifying `GExtFunctor` as
   an endofunctor?

3. Is there a way to exploit the specific structure of
   `copowerProf (HomToProf pt) G` (as opposed to arbitrary
   profunctors) to construct a small coend? The weight
   `HomToProf pt` has the special property that
   `(HomToProf pt).obj(op A).obj(B) = (A ⟶ pt)` is independent
   of `B`.

4. Could a universe-polymorphic reformulation of `HasAllHomToProfCoends`
   work, where `GExtFunctor` maps between different universes but the
   algebra structure is defined via a universe-shifting adjunction?

5. In set-theoretic mathematics, this coend exists by
   replacement (the image of a class-indexed family
   under a set-valued function is a set). Is there a type-theoretic
   analog that avoids the universe bump?

## 9. File Reference

### EndsAndCoends.lean

- `typeCoend` (line 110): `J : Type u`,
  result `Type (max u v)`
- `typeCoendCowedge` (line 128): `J : Type v`
- `typeCoendCowedge_isInitial` (line 153):
  `J : Type v`
- `typeEnd` (line 38): `J : Type u`,
  result `Type (max u v)`
- `typeEndWedge` (line 56): `J : Type v`
- `typeCoend.impredicative` (line 1555):
  `J : Type v` (NinjaYoneda section)

### Weighted.lean

- `weightedLimitFunctor` (line 2240):
  `J : Type v`
- `sliceProfunctor` (line 3621):
  codomain `Type v`
- `sliceProfunctorPoly` (line 3672):
  codomain `Type (max w p)`
- `RestrictedCowedge` (line 4973):
  `D : Type w`, no constraint on `pt`
- `HasRestrictedCoend` (line 5731):
  inherits from `RestrictedCowedge`

### WeightedAlg.lean

- `HasAllHomToProfCoends` (line 1283):
  `G : Cᵒᵖ ⥤ C ⥤ C`
- `GExtFunctor` (line 1376): `C ⥤ C`
- `mendlerLambekEquiv` (line 1615):
  requires `HasAllHomToProfCoends G`

### RestrictedCoendAsColimit.lean

- `copowerProf` (line 390):
  `H : Cᵒᵖ ⥤ C ⥤ Type v`,
  `G : Cᵒᵖ ⥤ C ⥤ C`
- `homRestrictedCopowerIso` (line 978):
  no additional constraint

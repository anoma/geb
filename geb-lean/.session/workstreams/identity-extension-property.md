# Workstream: Identity Extension Property

## Status

Active

## Context

The Hermida/Reddy/Robinson paper "Logical Relations and
Parametricity" (ENTCS 303, 2014) formalizes parametricity
via reflexive graph categories. Our `PshRelSpanObj C` is
precisely the construction `rel(PSh(C))` from that paper.

The hypothesis (from the user): `PshRelSpanObj` embeds
parametric functors but also contains non-parametric ones.
The Identity Extension Property (IEP) from the paper
distinguishes them. PshTypeExpr-derived functors should
all satisfy IEP.

## Reference

- `.claude/docs/logical-relations-parametricity-reynolds-
  program-category-theory-programming-languages.pdf`
  (Hermida/Reddy/Robinson 2014)
- `docs/.claude/wadler89-theorems-for-free.pdf` (Wadler 1989)
- Milewski blog post on parametricity

## Mapping to our codebase

| Paper concept | Our formalization |
| - | - |
| Reflexive graph category G | `PshRelSpanObj C` |
| Vertex category G_v | `PSh(C)` |
| Edge category G_e | Relations `PshRel P Q` |
| Boundary ∂₀, ∂₁ | `fstProj`, `sndProj` |
| Identity section I | `pshRelId` |
| Graph functor ⟨−⟩ | `pshRelGraph` |
| Relational functor | `PshParametricFunctor` |
| Parametric nat trans | Nat trans in functor category |
| IEP: F(I_A) = I_{F(A)} | fstProj = sndProj and IsIso on pshRelId |
| Subsumptivity | pshRelGraph full and faithful |
| Fact 6.6 (param ⊃ nat) | Nat trans determined by typeNode components |
| Fibration | Pullback of relations along morphism pairs |

## Tasks

### Task 1: Define Identity Extension Property [DONE]

`HasIdentityExtension` in `SpanFamily.lean`.
`PshRelHasIdentityExtension` (abbrev) and
`pshRelIdRel` in `PshRelSpanDiagram.lean`.

### Task 2: PshTypeExpr-derived functors satisfy IEP [DONE]

- `PshTypeExpr.fullRelInterp_id` in `PshTypeExpr.lean`
  (by induction: `var` trivial, `app` by
  `pshBarrLiftRel_id`, `arrow` by `pshArrowRel_id`)
- `pshRelId_ι_fst_eq_snd` and `pshRelId_ι_fst_isIso`
  in `PshRelSpanDiagram.lean`
- `pshTypeExprSpanData` and `pshTypeExpr_iep` in
  `PshTypeExpr.lean`

### Task 3: Non-IEP counterexample [DONE]

`pshFullProductData` and `pshFullProductData_not_iep`
in `PshRelSpanDiagram.lean`.

### Task 4: Embedding IEP

File: `GebLean/PshRelSpanDiagram.lean`

Show functors in the image of `pshCovariantEmbedding` and
`pshContravariantEmbedding` satisfy IEP.

Requires: `pshBarrLiftSkel G (pshRelId P) ≅
pshRelId (G.obj P)`.

Dependencies: Task 1.

### Task 5: Graph functor subsumptivity

File: `GebLean/PshRelDouble.lean` or new file

Define the graph functor from `Arrow (PSh(C))` to the
edge category of `PshRelSpanObj C` (mapping `f : P ⟶ Q`
to `.relNode P Q (pshRelGraph f)`). Show it is full and
faithful (subsumptivity).

Existing: `pshRelGraph_ι_fst_iso` gives injectivity.
Need fullness.

Dependencies: none.

### Task 6: Parametricity subsumes naturality

File: `GebLean/PshRelSpanDiagram.lean`

For IEP-satisfying functors F, G : PshRelSpanObj C ⥤ D,
show nat trans η : F ⟶ G are determined by their
typeNode components:

```lean
η₁.app (.typeNode P) = η₂.app (.typeNode P) ∀ P
  → η₁ = η₂
```

This is Hermida Fact 6.6.

Dependencies: Tasks 1, 5.

### Task 7: Fibration structure

File: `GebLean/PshRelDouble.lean` or new file

Show the boundary functor
∂ : PshRelEdge C → PSh(C) × PSh(C) is a fibration:
pullback of relations along morphism pairs exists.

Dependencies: none.

### Task 8: Reflexive graph category formalization

File: new `GebLean/Utilities/ReflexiveGraph.lean`

Define `ReflexiveGraphCategoryData` structure and show
`PshRelSpanObj C` is one.

Dependencies: none.

## Recommended order

1 → 3 → 2 → 4 → 5 → 6 → (7, 8 independent)

## Notes

### IEP for general target category D

The paper's IEP applies to relational functors G → H
between reflexive graph categories. Our formulation
generalizes to arbitrary target D:

  fstProj (idRel v) = sndProj (idRel v) ∧ IsIso

When D is itself a reflexive graph category (e.g.,
`PshRelSpanObj C'`), this recovers the paper's IEP
via the SpanFamily decomposition.

### Identity condition (eq 14)

The paper's identity condition:
  (f, f') : I_A → I_B  ⟺  f = f'

In our PshRelSpanObj: a morphism from
.relNode P P (pshRelId P) to .relNode Q Q (pshRelId Q)
consists of compatible maps. The identity condition says
the two vertex maps must coincide. This follows from
subsumptivity (Task 5).

### Structural induction connection

The paper's Section 8 connects IEP to structural
induction: if T is a relational endofunctor satisfying
IEP, then the initial T-algebra μ(T) satisfies
I_{μ(T)} ≅ μ(T_e) (the initial algebra of the edge
part is the identity relation on the initial algebra
of the vertex part). This connects to our
`initialAlgebraParametricEquiv` at the Type level.

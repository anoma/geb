# Workstream: Exact Completion and PBTO Preservation

## Status

Research phase. No implementation started.

## Goal

Determine whether a combined "free exact completion of a
category with finite products" preserves parameterized
binary tree objects (PBTOs), and if so, formalize the
construction and the preservation proof.

## Background

### What we have

The free equalizer completion (Bunge/Pitts construction)
takes `LawvereBTQuotCat` (finite products + PBTO) to
`LawvereBTLexCat` (finite limits).  This construction is
complete and formalized in:

- `GebLean/EqualizerCompletion.lean` (671 lines)
- `GebLean/EqualizerCompletionLimits.lean` (894 lines)
- `GebLean/EqualizerCompletionPBTO.lean` (507 lines)
- `GebLean/LawvereBTEqCompletion.lean`

The PBTO of `LawvereBTQuotCat` is NOT preserved by the
free equalizer completion alone.  A counterexample in Set
shows that changing the step function of a fold by a
`CoreflexiveRelStep` can change the fold result in a way
not captured by the source coreflexive equivalence
("Lemma B failure").

### What we want

An exact category extending `LawvereBTQuotCat` with:

- Finite limits
- Regularity (coequalizers of kernel pairs, regular
  epis are coequalizers)
- Exactness (every internal equivalence relation is
  effective)
- A PBTO (the universal property of the parameterized
  binary tree object holds for ALL objects)

### The standard two-step approach

The literature (Carboni-Vitale 1998, Maietti 2010)
describes this as a composition of two left adjoints:

```text
LawvereBTQuotCat  (finite products + PBTO)
       |
       |  free equalizer completion (Bunge/Pitts)
       v
LawvereBTLexCat   (finite limits, PBTO lost)
       |
       |  ex/lex completion (Carboni-Vitale)
       v
LawvereBTExCat    (exact, PBTO status unknown)
```

The ex/lex completion preserves PBTOs of lex categories
that already have them.  But `LawvereBTLexCat` does not
have one (Lemma B failure), so the ex/lex step cannot
simply "preserve" what doesn't exist.

### Open question

Does the COMPOSED construction (free equalizer then
ex/lex) restore the PBTO?  That is: does the PBTO of
`LawvereBTQuotCat` survive the round trip through both
completions, even though it's lost at the intermediate
stage?

No published result addresses this directly.  The
research agent found that "no known direct, single-step
construction exists" for the free exact completion of a
category with finite products.

## Findings So Far

### The Lemma B counterexample

In Set with the PBTO being finite binary trees, consider
the coreflexive pair:

- `X.src = {a, b}`, `X.tgt = {0, 1, 2}`
- `X.left: a -> 0, b -> 1`
- `X.right: a -> 0, b -> 2`
- `X.retract: 0 -> a, 1 -> b, 2 -> b`

With `g = fst` (first projection), the reflexivity-derived
step functions `w_left = retract >> g >> left` and
`w_right = retract >> g >> right` give different fold
results for base `b = const 1`:

- `fold (const 1) w_left` = 1 everywhere
- `fold (const 1) w_right` = 1 at leaf, 2 at nodes

These are not `CoreflexiveEqv`-related (source is
trivially embedded, so `CoreflexiveEqv` = equality).

### Arrow directions

The Bunge construction and the ex/lex construction use
dual arrow conventions:

- Bunge (coreflexive pair): `left, right : X -> Y`
  (sections into witness space), `retract : Y -> X`
  (common retraction)
- Ex/lex (pseudo-equiv relation): `s, t : R -> X`
  (projections from relation space), `i : X -> R`
  (common section)

The Bunge construction is about equalizers (subobjects);
the ex/lex construction is about coequalizers (quotients).
These are dual concepts, and the arrow reversal reflects
this.

### Product-based transitivity fails

The ex/lex transitivity condition `c : R ×_X R -> R`
requires a pullback.  Replacing the pullback with the
product `R × R` trivializes the relation: taking
`c(i(x), i(y))` witnesses `x ~ y` for ALL `x, y`,
making the quotient collapse to a point.

The pullback constraint (composable pairs only) is
essential.  This is why the ex/lex completion requires
a lex starting category (for pullbacks to exist).

### The ex/lex morphism structure

In the ex/lex completion, morphisms carry EXPLICIT
LIFTS: a morphism `f : X -> Y` comes with `f_1 : R_X ->
R_Y` satisfying `s_Y . f_1 = f . s_X` and
`t_Y . f_1 = f . t_X`.  The morphism equivalence is
ONE-STEP (not `EqvGen`), because the pseudo-equiv
structure provides symmetry and transitivity.

This is analogous to `VertEdgeHom` in our double-category
framework (`PshRelEdge`): a morphism between two
"vertical edges" (objects with relation data) consists
of a pair of maps satisfying a "related" square condition.

### The fold-of-lift argument

For the PBTO in the ex/lex completion (IF we had valid
CPMor morphisms): given `f = (f_0, f_1)` and
`g = (g_0, g_1)` in the ex/lex completion, define:

- `phi_0 = elim f_0 g_0` (fold at the object level)
- `phi_1 = elim f_1 g_1` (fold at the relation level)

The "related" squares follow from:

1. `elim_naturality` (pre-composition commutes with fold)
2. `elim_algebra_morphism` (algebra morphisms commute
   with fold)
3. The "related" conditions on `f` and `g`

This argument does NOT need Lemma B.  It uses only the
naturality and algebra morphism properties (already
proved generically in `EqualizerCompletionPBTO.lean`).

### The obstacle

The fold-of-lift argument works at the ex/lex level
BUT requires `phi_0` to be a valid morphism in
`LawvereBTLexCat` (a CPMor, i.e., a premorphism).
The premorphism condition is where Lemma B fails.

The ex/lex quotient structure might absorb this failure
(two morphisms that differ by the Lemma B gap might
become identified in the ex/lex equivalence), but this
has not been proved.

## Proposed Combined Construction

### Idea

Instead of two separate steps, define a SINGLE
construction that combines the coreflexive pair
(equalizer/Bunge) and pseudo-equiv relation
(coequalizer/ex-lex) data into one structure.  An object
would have:

- `X : C` (base object)
- `Y : C` (outgoing witness space, for equalizers)
- `R : C` (incoming relation space, for quotients)
- `left, right : X -> Y` (coreflexive sections)
- `retract : Y -> X` (coreflexive retraction)
- `s, t : R -> X` (pseudo-equiv projections)
- `i : X -> R` (reflexivity section)
- `v : R -> R` (symmetry)
- `c : R ×_X R -> R` (transitivity)
- Linking conditions between the two structures

### The linking conditions problem

The linking conditions must express that the pseudo-equiv
quotient acts "on top of" the coreflexive equalizer
(distributivity of colimits over limits).

Direct conditions like `s >> left = s >> right` (relation
witnesses land in the equalizer of `left` and `right`)
are too strong: combined with reflexivity (`s . i = id`)
and `left` being a split mono, they force `left = right`
(trivializing the coreflexive pair).

The right conditions should involve the FULL coreflexive
structure (including `retract`), not just `left` and
`right` individually.  The "equalizer" in the Bunge
construction is not `{x | left(x) = right(x)}` but
rather the coreflexive-quotient structure defined by
`(left, right, retract)` together.  The pseudo-equiv
must interact with this quotient structure, which means
the linking conditions should involve premorphism-like
conditions: the pseudo-equiv projections `s, t` should be
premorphisms with respect to the coreflexive structure.

### Specific research questions

1. What are the correct linking conditions between the
   coreflexive and pseudo-equiv structures?  They should:
   - Not trivialize either structure
   - Encode the "coequalizer on top of equalizer"
     distributivity
   - Involve the retraction (not just the sections)
   - Be stated in terms of premorphism-like conditions

2. With the correct linking conditions, does the
   transitivity pullback `R ×_X R` become constructible
   from the combined data (using the coreflexive
   structure to provide the equalizer that defines the
   pullback)?

3. Does the combined construction give an exact category
   with finite limits?

4. Does the PBTO survive the combined construction?
   (The fold-of-lift argument should work if the
   morphism structure provides explicit lifts and the
   premorphism condition is absorbed by the combined
   equivalence.)

5. Is the combined construction the left adjoint to the
   forgetful functor from exact categories to categories
   with finite products?

### Four morphisms from R to Y

The four compositions `s >> left`, `s >> right`,
`t >> left`, `t >> right` from `R` to `Y` are natural
candidates for linking conditions.  However:

- `left` and `right` are split monomorphisms (since
  `left >> retract = id`), so equality conditions
  between pairs of these four morphisms propagate back
  and can trivialize structures.

- Conditions should probably be stated as PREMORPHISM
  conditions (existence of witnesses in Y connecting the
  compositions) rather than as equalities.

- The retraction `retract : Y -> X` is a split
  epimorphism (lossy), so conditions involving `retract`
  are weaker and may avoid trivialization.

## References

- Bunge & Carboni, "The Symmetric Topos" (JPAA 1995)
- Carboni & Vitale, "Regular and exact completions"
  (JPAA 1998)
- Maietti, "Joyal's arithmetic universe as
  list-arithmetic pretopos" (TAC 2010)
- Maietti & Rosolini, "Unifying exact completions"
  (Appl. Cat. Struct. 2015)
- Cockett, "List-arithmetic distributive categories:
  Localizability" (JPAA 1990)
- nLab, "regular and exact completions"
- nLab, "pseudo-equivalence relation"
- nLab, "exact completion"

## Dependencies

- `GebLean/EqualizerCompletion.lean` (category structure)
- `GebLean/EqualizerCompletionPBTO.lean` (generic
  naturality and algebra morphism lemmas)
- `GebLean/Utilities/DoubleCategory.lean` (VertEdge,
  VertEdgeHom pattern)

# Workstream: Weighted (Co)Ends vs Paranatural Transformations in Algebra

## Status

Active

## Context

This workstream investigates whether weighted (co)ends can provide equivalent
formalizations to the three main algebraic results that justify the use of
paranatural (strong dinatural) transformations in theoretical computer science.

### Background

Paranatural transformations (a.k.a. strong dinatural transformations), as
developed by researchers such as Uustalu and Neumann, have three primary
justifications in the context of algebraic data structures:

1. **Initial algebras**: The carrier of an initial F-algebra is isomorphic to
   the set of paranatural transformations from the algebra profunctor to the
   identity profunctor.

2. **Terminal coalgebras**: The carrier of a terminal F-coalgebra is isomorphic
   to the structural coend of the coalgebra profunctor.

3. **Church numerals**: The natural numbers are isomorphic to the set of
   endo-paranatural transformations of the hom-functor (a category-theoretic
   formalization of Church numerals).

### Research Question

We have developed a theory of "weighted (co)ends" in `Weighted.lean` which
generalizes both weighted (co)limits and (co)ends. This workstream investigates:

- Do weighted (co)end formulations exist for these three results?
- If so, are they equivalent to the paranatural formulations?
- If they are equivalent, can weighted (co)ends subsume paranatural
  transformations (since weighted (co)ends are more directly derived from
  established concepts and generalize to broader contexts)?

### Relevance

Neumann has discovered cases where paranatural transformations diverge from the
"parametricity" behavior expected in programming semantics. If weighted (co)ends
provide equivalent characterizations for the primary use cases while being more
general, they may be preferable as a foundational concept.

## Tasks

- [ ] Investigate weighted-coend formalization of initial algebra result
- [ ] Investigate weighted-coend formalization of terminal coalgebra result
- [ ] Investigate weighted-coend formalization of Church numerals result
- [ ] Document findings and implications
- [ ] Review existing WeightedAlg.lean patterns

## Relevant Source Files

### Paranatural Formulations

- `GebLean/Paranatural.lean` - Core paranatural transformation definitions
- `GebLean/ParanatAlg.lean` - Initial algebra and terminal coalgebra results
- `GebLean/DinaturalNumbers.lean` - Church numerals result

### Weighted (Co)End Theory

- `GebLean/Weighted.lean` - Weighted (co)end definitions
- `GebLean/WeightedAlg.lean` - Mendler-Lambek correspondence via restricted
  coends
- `GebLean/RestrictedCoendAsColimit.lean` - Restricted coend as colimit
- `GebLean/Utilities/PowersAndCopowers.lean` - Mathematical foundations for
  explicit weighted (co)end formulas

### Related Workstreams

- `.session/workstreams/paranatural-investigations.md` - Broader paranatural
  theory investigations
- `.session/workstreams/weighted-vs-strong-restricted.md` - WeightedCowedge vs
  StrongRestrictedCowedge relationship
- `.session/workstreams/mendler-lambek-correspondence.md` - Completed
  Mendler-Lambek equivalence

## Notes

### Existing Results

From `weighted-vs-strong-restricted.md`:

- The functor `WeightedCowedge → StrongRestrictedCowedge` is faithful but NOT
  full
- The functor `WeightedCowedge → RestrictedCowedge` is faithful but NOT full
- No inclusion exists from StrongRestrictedCowedge to WeightedCowedge
- Conclusion: WeightedCowedge cannot substitute for RestrictedCowedge in the
  general Mendler-Lambek correspondence

From `mendler-lambek-correspondence.md`:

- MendlerAlgebra for difunctors is equivalent to ConventionalAlgebra of the
  restricted coend functor (when coends exist)
- The correspondence is implemented in WeightedAlg.lean

### Mathematical References

- Uustalu, "Mendler-style Inductive Types, Categorically" (categorified Mendler)
- Neumann, "Paranatural Category Theory" (2023, arXiv:2307.09289)
- Vene, "Categorical Programming with Inductive and Coinductive Types"
  (Mendler-Lambek correspondence)
- Eppendahl, "Parametricity and Mulry's Strong Dinaturality" (1999)

### Approach

For each of the three results, we need to:

1. Identify the precise profunctors and weight involved
2. Formulate the weighted (co)end version
3. Determine whether there is an equivalence with the paranatural version
   (either prove there is an equivalence, or prove that there is a
   counterexample)
4. Document summaries of findings (equivalences, counterexamples, etc.)

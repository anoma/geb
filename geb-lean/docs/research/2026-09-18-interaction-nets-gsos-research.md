# Interaction nets, amb, and fair merge

**(as instances of the GSOS, lambda-bialgebra, and
pattern-runs-on-matter frameworks)**

Research note, 2026-09-18. Prototypes (core Lean, executable) in
`lean-prototypes/interaction-nets-gsos/`:
`InteractionNets.lean` (combinators as an interface-graded coalgebra with
the gluing algebra) and `FairMerge.lean` (fair merge as a synchronous
operator, with the tree-path obstruction).

## Summary

1. Interaction nets, hence interaction combinators and everything Lafont
   translates into them, are an instance of abstract GSOS and therefore of
   the lambda-bialgebra universal semantics, provided the instantiation
   category is the slice over interface arities (`Over ℕ`, or over typed
   interfaces for Lafont's typed nets). The syntax polynomial generates
   net presentations (cells, wires, juxtaposition, cut); the behaviour
   polynomial observes visible agents at the interface and performs the
   maximal parallel step. The repository's `PolyGSOSRule` over
   `PolyEndo ℕ` has exactly this type; the concrete instantiation is not
   built.
2. INAMB (interaction nets with amb) is an instance too: the scheduler's
   choices become directions of the behaviour polynomial, so the final
   semantics is the tree of runs (indexed nondeterminism).
3. Fair merge is representable, and the reason is precise: an abstract GSOS
   rule sees each argument's current-step behaviour including its silence
   (negative premises; positions of a polynomial). That is Keller's
   `poll`, which Panangaden and Shanbhogue prove interdefinable with fair
   merge. What remains impossible, in all three frameworks and anywhere
   else, is fair merge as the set of runs of a system whose choices are
   made step by step by an unconstrained scheduler: the set of fair
   schedules is not the path set of any tree. Fairness therefore lives
   either in synchronous observability (poll) or in the matter (a fair
   oracle taken as the coalgebra of variables of a free bialgebra, or as
   the cofree-comonad element the pattern runs on).

## 1. Interaction nets as an interface-graded GSOS instance

### The data

Lafont (1997, section 1.1) describes a net by a finite set `X` of free
ports, cells `C` with symbols, and wires partitioning the ports into pairs.
An alphabet with arities is the finitary polynomial `p(y) = Σ_α y^{ar α}`:
positions are symbols, directions are auxiliary ports, the principal port
is the output. This matches the observation that the signature "looks
like a finitary polynomial functor with conditions". The conditions are of
two kinds:

- The interaction system is a partial symmetric matrix of reduced nets
  `(ν_{i,j})` with `ar α_i + ar α_j` free ports (Lafont section 1.2). With
  the interface arity as the index of a slice, this is a dependent
  function whose typing enforces the interface condition.
- The wiring discipline (every port in exactly one wire). This is not a
  condition on the polynomial but on its algebra: nets are not the free
  algebra of `p` on `Set`. Lafont's Proposition 2 (reduced net = trees
  plus a wiring, uniquely) and the decomposition of a net with `k` cuts
  into a reduced net with `n + 2k` ports plus `k` cut wires (section 3.3)
  say exactly that the algebra of nets is trees (the free monad on `p`)
  closed under wirings and cuts, in the string-diagram sense.

### Syntax polynomial `P` on `Over ℕ`

Operators, with `X(n)` the states of interface size `n`:

- `cell α : 1 → X(ar α + 1)` (principal port at position 0);
- `wire : 1 → X(2)`;
- `par : X(n) × X(m) → X(n + m)`;
- `cut_{i,j} : X(n + 2) → X(n)` (connect two free ports; includes cuts
  between principal ports, cyclic wires, and vicious circles).

`T_P(0)(n)` is the set of presentations of nets with `n` free ports. Many
presentations denote one net; the identification is delivered by
bisimilarity in the final coalgebra, as usual in bialgebraic semantics.

### Behaviour polynomial `Q` on `Over ℕ`

`Q(X)(n) = Σ_{o : Fin n → 1 + Σ} X(n')` where `o` records, for each free
port, either silence (the port is wired to an auxiliary port or a free
port) or the symbol whose principal port it is wired to. In the simplest
form `n' = n` and the residual is the net after one maximal parallel
reduction step (well defined by Lafont's Proposition 1: active pairs are
pairwise disjoint). In the refined form the observed cells are removed and
their auxiliary ports join the interface, so that the final coalgebra is a
Böhm-tree-like head-observation tree. Mazza (LMCS 2009) proves full
abstraction for the symmetric combinators using edifices, which play the
role of Böhm trees; Lafont's section 3 execution formula is the
corresponding semantics for the original combinators. Whether
`Q`-bisimilarity coincides with Mazza's observational equivalence has not
been checked here.

### The rule `ρ : P(Id × Q) → Q T_P`

By cases on the operator:

- `cut_{i,j}` of a state whose observation shows symbols `α` at `i` and
  `β` at `j`: the residual is `ν_{α,β}` (a closed `T_P` term) plugged onto
  the residual state variable; the observation is the restriction of `o`.
- `cut_{i,j}` with a silent port: no interaction; the term is re-formed
  (in the refined form, an observed cell is put back with `par` and
  `cut`).
- `par`, `cell`, `wire`: componentwise.

Only the operator and the observations are consulted, so naturality in
`X` holds. Polynomials preserve weak pullbacks, so bisimilarity is a
congruence (Turi and Plotkin 1997, Corollary 7.5): contextual equivalence
of nets being a congruence is obtained for free; full abstraction is the
separate theorem.

### Universality

Lafont's Theorem 1 (any interaction system translates into the
combinators) transports along the encoding, but it is not needed: every
interaction system is directly an instance with its own signature
polynomial. Turing machines and cellular automata (Lafont section 1.3
and following) are therefore instances by either route.

### Cost of the actual instantiation

`PolyGSOSRule (P Q : PolyEndo ℕ)` in `GebLean/PolyGSOS.lean` has the
required type. Constructing the morphism
`polyBetweenComp P (polyIdBehaviorPoly Q) ⟶ polyBetweenComp Q (polyFreeMPoly P)`
requires fibre-level equivalences for each operator; the prototype
`InteractionNets.lean` gives the concrete coalgebra and algebra only.

### Pattern runs on matter

Libkind and Spivak's `Ξ : 𝔪_p ⊗ 𝔠_q → 𝔪_{p ⊗ q}` is the free
monad–cofree comonad interaction law of Katsumata, Rivas, and Uustalu
(LICS 2020), for the Dirichlet product `⊗`, that is, lockstep pairing of
pattern nodes with matter nodes. The GSOS distributive law is a law for
the substitution product. For nets, `Ξ` is the natural home of the token
(geometry-of-interaction) semantics: the pattern is a query (free port
plus stacks, a finite decision tree), the matter is the net as a
reversible machine (Lafont section 3.1). It is not the natural home of
the rewriting semantics.

## 2. amb

INAMB's amb (Fernández and Khalil 2002) has two principal ports and fires
on whichever is ready; with both ready the choice is nondeterministic.
In the encoding, the observation reports how many ambs have two ready
partners and the directions of `Q` at that position are the choice
vectors. `Q` stays polynomial: nondeterminism appears as indexed
branching, not as a powerset. The final semantics is then the tree of
runs, finer than the powerset semantics (two nets with equal outcome
sets but different choice trees are distinguished). The powerset
behaviour functor of Turi and Plotkin is available at the abstract
`GSOSRule` and `LambdaBialgebra` level but not in `PolyGSOS`.
Multiple principal ports (Alexiev's INMPP) are handled the same way. The
maximal-parallel step agrees with INAMB's asynchronous semantics under
fair scheduling of active pairs.

## 3. Fair merge

Panangaden and Shanbhogue (Inf. & Comp. 98, 1992):

- Fair merge is interdefinable with Keller's `poll` (a primitive that
  reports the absence of input): zipper plus poll on each input, then
  filter. "Fair merge requires sensitivity to the presence or absence of
  values at input ports."
- Theorem 9: no finite network of Hoare-monotone, limit-closed
  asynchronous processes implements any total subset of the fair-merge
  relation. Corollary 2: angelic merge cannot implement fair merge.
  Fernández and Khalil's remark that INAMB cannot implement fair merge is
  this result.

In abstract GSOS the rule for an operator receives, for every argument,
its behaviour in the current step. With `B = P_f(A × -)` an empty set of
transitions is a negative premise (Bloom, Istrail, and Meyer's format);
with a polynomial `Q` silence is a position. Either way the composite
observes absence: `poll` is built in. Consequently:

- `FairMerge.lean`, Part 1: `fairMerge` is a deterministic coalgebra for
  `Q X = Option A × X` on polled inputs; `fairMerge_fair` proves every
  offered value appears in the output, whatever the other input does.
- In the net encoding, an amb with a priority bit that alternates when
  both sides are ready is a deterministic GSOS operator serving each
  ready side within two steps. Interaction rules cannot express it
  because they fire only on active pairs and never observe non-readiness.
  This is the exact expressive gain over INAMB, and it is the gain
  Panangaden and Shanbhogue identify (poll, timeouts), not a violation of
  their theorem: GSOS composition is synchronous and not Hoare-monotone.

What no framework provides:

- `FairMerge.lean`, Part 2, `fair_not_paths`: for every prefix-closed set
  of finite schedules `T`, the set of infinite paths of `T` is not the set
  of fair schedules (if it contained all fair schedules it would contain
  `false^ω`). The runs of any coalgebra from a state form the path set of
  its unfolding tree. So fair merge is not the run set of a closed
  nondeterministic system with a step-wise unconstrained scheduler,
  whatever the branching (finite or countable). This is the tree form of
  the König's lemma argument behind Park (1980).

Where fairness can live instead:

- In the matter. Fair oracle streams are closed under `tail`, hence form
  a subcoalgebra `Ω` of the final coalgebra of `Y ↦ Bool × Y`, although
  not a closed set. `freeBialgebra law (Ω, tail)` in
  `GebLean/Utilities/LambdaBialgebra.lean` is the free bialgebra of merge
  terms over fair oracles, and `finalBialgebra_isTerminal` gives its
  universal semantics. In the pattern-runs-on-matter formulation, `Ω` is
  the matter the merge pattern runs on. This is Park's "fair schedules".
  No change to the existing code is needed; the choice of the coalgebra
  of variables carries the fairness.

## Ladder

interaction nets ⊂ INAMB ⊂ abstract GSOS over `Over ℕ`, the last step
being negative premises (synchronous observability of silence), which is
poll and therefore fair merge. All three frameworks accommodate all three
tiers; the lambda-bialgebra and pattern-runs-on-matter formulations add
the second location for fairness (the matter), and only the
lambda-bialgebra formulation contains the rewriting semantics of nets as
its distributive law.

## References

- Y. Lafont, Interaction combinators, Information and Computation 137
  (1997). Sections 1.1, 1.2, 1.6 (Prop. 2), 2.1 (Thm. 1), 3.1, 3.3.
- M. Fernández and L. Khalil, Interaction nets with McCarthy's amb,
  ENTCS 68 (2002).
- D. Mazza, Observational equivalence and full abstraction in the
  symmetric interaction combinators, LMCS 5(4:6) (2009).
- P. Panangaden and V. Shanbhogue, The expressive power of indeterminate
  dataflow primitives, Information and Computation 98 (1992). Poll:
  Example 2 and section 5; Theorem 9; Corollary 2.
- D. Park, On the semantics of fair parallelism, LNCS 86 (1980).
- D. Turi and G. Plotkin, Towards a mathematical operational semantics,
  LICS 1997. Theorem 1.1, Corollaries 7.3 to 7.5.
- S. Libkind and D. Spivak, Pattern runs on matter, arXiv:2404.16321.
  Section 3.2, Proposition 3.3, Theorem 3.4.
- S. Katsumata, E. Rivas, and T. Uustalu, Interaction laws of monads and
  comonads, LICS 2020.
- B. Bloom, S. Istrail, and A. Meyer, Bisimulation can't be traced, JACM
  42 (1995) (the GSOS format with negative premises).

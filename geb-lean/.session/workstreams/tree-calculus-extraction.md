# Workstream: Tree Calculus Source Extraction

## Status

Active

## Context

Extracting references to proofs, theorems, and
implementations from the tree calculus sources into
`docs/tree-calculus.md`. The sources are:

1. Book: *Reflective Programs in Tree Calculus* (Barry
   Jay, 2021) — 176 pages, `docs/reflective-programs-in-tree-calculus.pdf`
2. Paper: *Typed Program Analysis without Encodings*
   (Barry Jay, PEPM '25) — 13 pages,
   `docs/typed-program-analysis-without-encodings.pdf`
3. Coq formalization: 9 `.v` files at
   `https://github.com/barry-jay-personal/tree-calculus`

Extract piecemeal (because it will consume a lot of context)
and document extracted information in `docs/tree-calculus.md`
before marking that part of extraction complete in this document.

## Progress

### Paper (13 pages) — COMPLETE

13 pages read. Extracted results written to
`docs/tree-calculus.md` (Type System, Programs, and
Verified Theorems sections). Among the contents documented:

- Type system: tree types `T ::= L | S U | F U V | U -> V`
  with subtyping
- Type constants: `Bool`, `Nat`, `Omega_2` (fixpoint type)
- Typing rule: two rules suffice (leaf subtyping +
  application)
- Reduction preserves typing (Theorem 10.6)
- Self-interpreter `bf` has type
  `forall X. forall Y. (X -> Y) -> (X -> Y)`
- Programs: `size`, `equal`, `isLeaf`, `isStem`, `isFork`,
  `bf` (breadth-first evaluator, 877 nodes)
- Fixpoint functions via `Z{f}` combinator
- Generic queries typed via subtyping on triage
- Coq verification reference: [20] in paper

### Book — progress by chapter

- [ ] Front matter, TOC, list of figures (pp. i-x)
- [ ] Ch 1: Introduction (pp. 3-9)
- [x] Ch 2: Equational Reasoning (pp. 11-21) —
  pedagogical; arithmetic theorems 1-7, structural
  induction, translations. No tree calculus content.
- [x] Ch 3: Tree Calculus (pp. 23-37) — 3-rule
  equational presentation (K, S, F), derived combinators
  (K, I, D, S), booleans, pairs, natural numbers,
  isZero, predecessor, parametric query, fundamental
  queries (isLeaf, isStem, isFork). Written to doc.
- [x] Ch 4: Extensional Programs (pp. 39-51) —
  bracket abstraction (Thm 8), star abstraction (Thm 9),
  wait{x,y}, self_apply, Z{f}, swap{f}, Y_2{f}
  (Thm 10: fixpoint_function), plus, lists, strings,
  list_map, list_foldleft, list_foldright. Written.
- [x] Ch 5: Intensional Programs (pp. 53-62) —
  size, equal (Thm 11-12), tagging (Thm 13),
  triage_comb, simple types as trees, type_check,
  typed_app, pattern matching. Written.
- [x] Ch 6: Reflective Programs (pp. 63-71) — four
  evaluation strategies (branch-first, root,
  root-and-branch, root-first), self-evaluators bf/
  root/rb/rf, quotation, Thms 14-18. Written.
- [ ] Ch 7: Rewriting (pp. 77-90)
- [ ] Ch 8: Incompleteness of Combinatory Logic (pp. 91-99)
- [ ] Ch 9: Lambda-Abstraction in VA-Calculus (pp. 101-111)
- [ ] Ch 10: Divide-and-Conquer in SF-Calculus (pp. 113-121)
- [ ] Ch 11: Concluding Remarks (pp. 123-129)
- [ ] Appendix A: Church-Turing Thesis (pp. 131-149)

### Coq files — not yet read

- [ ] `Tree_Calculus.v`
- [ ] `Rewriting_partI.v`
- [ ] `Rewriting_theorems.v`
- [ ] `Extensional_Programs.v`
- [ ] `Intensional_Programs.v`
- [ ] `Reflective_Programs.v`
- [ ] `Divide_and_Conquer_in_SF_Calculus.v`
- [ ] `Incompleteness_of_Combinatory_Logic.v`
- [ ] `Lambda_Abstraction_in_VA_Calculus.v`

## Extracted Results

Results are accumulated here as they are read, then
transferred to `docs/tree-calculus.md`.

### From the paper

- **Theorem 3.1** (`confluence_tree_calculus`):
  Reduction of triage calculus is confluent.
- **Theorem 3.2** (`head_reduction_to_factorable_form`):
  Reduction to factorable form can always begin with
  head reduction.
- **Theorem 3.3** (`derive_basic`): K, S, I, and
  `swap{f}` are derivable with their expected types.
- **Theorem 3.4** (`programs_have_types`): Every
  program p has canonical type `progty(p)`.
- **Theorem 4.1** (`star_beta`): Lambda-abstraction
  satisfies beta reduction: `(lambda x.t)u --> {u/x}t`.
- **Theorem 4.2** (`derive_star`): Lambda-abstractions
  can be typed in context.
- **Theorem 6.1** (`Z_red`): `Z{f} x --> f (Z{f}) x`
  (fixpoint combinator reduction).
- **Theorem 6.2** (`derive_Z`): The fixpoint combinator
  can be typed.
- **Theorem 7.1** (`derive_size`): `size : forall X. X -> Nat`.
- **Theorem 7.2** (`equality_of_programs`): `equal M N`
  reduces to `tt` if `M = N`, else `ff`.
- **Theorem 7.3** (`derive_equal`):
  `equal : forall X. forall Y. X -> Y -> Bool`.
- **Theorem 8.1** (`branch_first_eval_iff_bf`):
  `t, u || p` iff `bf t u --> p` (self-interpreter
  correctness).
- **Theorem 9.1** (`derive_subtype`): Subtyping is
  admissible.
- **Theorem 10.1-10.5**: Subtyping lemmas for
  fork-of-leaf, fork-of-stem, fork-of-fork cases.
- **Theorem 10.6** (`reduction_preserves_typing`):
  If `Gamma |- t1 : T` and `t1 --> t2` then
  `Gamma |- t2 : T`.

### From the book (to be filled as chapters are read)

(empty — will be populated as extraction proceeds)

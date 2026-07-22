import VersoManual
import GebLeanDocs.Bibliography

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

/-! # Ramification and complexity

Part I chapter 6 of the ramified-recurrence manual. See
`docs/superpowers/specs/2026-07-22-verso-ramified-manual-design.md`
section 4.1.
-/

#doc (Manual) "Ramification and complexity" =>

Chapters 1 to 5 assembled the discipline: the recurrence schema, the growth it admits
unrestricted, the {tech}[r-type]s, the ramified schema, and the section 2.4 ladder. This
chapter states what the discipline buys. Leivant III's Table 1 records three cells, each
pairing a signature class and a type discipline with a complexity class
{citep leivant3}[]. Each is stated here with its citation and none is proved. The three
do not share a source: only the third is Leivant III's own theorem, and the two
first-order cells rest on companion literature.

# Monadic word algebras and linear space

Restrict the ramified schema to first-order recurrence — Leivant III section 2.4(3)'s
"recurrence restricted to object types of the form `Omega^m o`", that is, to the
{tech}[tier]-carrying {tech}[object type]s of chapter 3 — and take the base algebra to be
a {tech}[monadic word algebra]. The functions so defined are the second Grzegorczyk class
`E^2`, equivalently the functions computable in space linear in the length of the input's
binary representation.

This cell was never published on its own. The citable statement is Clote's survey of
computation models and function algebras, Definition 3.100 and Theorem 3.101
{citep clote}[]. The identification of `E^2` with linear space is Ritchie's: Theorem 5
and its corollary give `E^2 = F'`, the functions computable in space linear in the binary
input length {citep ritchie}[].

# Polyadic word algebras and polynomial time

Keep the first-order restriction and take the base algebra to be a {tech}[polyadic word
algebra]. The functions defined are those computable in polynomial time. Leivant I states
the characterization for free word algebras: two tiers suffice, and computability in time
`O(n^k)` corresponds to `k` nestings of ramified simultaneous recurrence
{citep leivant1}[]. Bellantoni and Cook reach the same class through the safe/normal
split — predicative recursion on notation together with safe composition, with polynomial
time obtained as the functions of their algebra on all-normal inputs (Theorems 3.3 and
4.2; Lemma 4.1 supplies the bound) {citep bellantoniCook}[]. The two vocabularies
translate: tier 1 is normal and tier 0 is safe (Clote, p. 50).

## The cost-model caveat

The cell above is stated over binary words, with the size of a value its length as a
string. Over a {tech}[tree algebra] it is not stated at all, and the reason is the cost
model. A signature admitting a constructor of arity above one lets first-order tiered
recursion produce an output of exponential term size — a full binary tree from a binary
word — so polynomial-time soundness at first order over tree algebras holds only under a
DAG or graph representation of values, under which that output occupies polynomial space.
Dal Lago, Martini and Zorzi record this, and record that the polynomial-time claim made
for arbitrary algebras in Leivant's 1993 POPL paper holds only for word algebras under
the string representation {citep dalLagoMartiniZorzi}[].

# Higher-type ramification and the elementary functions

Drop the first-order restriction, so that a recurrence may be taken at a function type as
chapter 5's `ramExp` is, and the class rises to the Kalmár elementary functions: those
computable within a tower of exponentials of fixed height in the size of the input. This
is Leivant III section 6.1, Theorem 14 {citep leivant3}[]. Items (1) and (2) of the
theorem state the equivalence between definability in the equational system and
elementary computability; items (3) to (5) restate that equivalence for the applicative
calculi of the paper's section 4.1.

What the theorem characterizes is the collapse of a ramified definition. Chapter 4's tier
erasure sends an identifier to a function on the base carrier, and Theorem 14 states that
the functions so obtained are exactly the elementary ones. Chapter 5's `ramTwoPow`
exhibits one direction's shape: for each fixed `m` it reaches height `m` of the tower by
composing `m` copies of a single second-order recurrence, and the height is fixed by the
identifier rather than driven by the input.

The bound here comes from the type discipline and not from the signature — the statement
holds for every non-trivial free algebra — so, unlike the two first-order cells, this one
does not turn on whether the base algebra is monadic, polyadic, or a tree algebra.

# Scope

No cell is proved in this document. The development formalizes the statement of the third
cell, relative to the repository's elementary-recursive reference class rather than to a
machine model; Part II chapter 5 presents it. The two first-order cells appear in the
development as sub-theory definitions only, with their complexity characterizations
deferred.

import VersoManual
import GebLeanDocs.Bibliography
import GebLean.Ramified.AlgSig
import GebLean.Ramified.Algebras
import GebLean.Ramified.SortedSig
import GebLean.Ramified.RType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

/-! # Signatures, free algebras, ramified types

Part II chapter 2 of the ramified-recurrence manual. See
`docs/superpowers/specs/2026-07-22-verso-ramified-manual-design.md`
section 4.2.
-/

#doc (Manual) "Signatures, free algebras, ramified types" =>

This chapter renders the declarations of `GebLean/Ramified/AlgSig.lean`,
`GebLean/Ramified/Algebras.lean`, `GebLean/Ramified/SortedSig.lean`, and
`GebLean/Ramified/RType.lean` that Part I chapter 1 and chapter 3
introduced by transcription. Each declaration's own doc comment states
its content; the prose here places each in relation to its neighbours.

# Free-algebra signatures

{docstring GebLean.Ramified.AlgSig}

{docstring GebLean.Ramified.AlgSig.polyEndo}

{docstring GebLean.Ramified.FreeAlg}

{docstring GebLean.Ramified.FreeAlg.mk}

# The recurrence over a free algebra

{docstring GebLean.Ramified.FreeAlg.recurse}

{docstring GebLean.Ramified.FreeAlg.recurse_mk}

# The monadic word algebra

{docstring GebLean.Ramified.natAlgSig}

{docstring GebLean.Ramified.natToFreeAlg}

{docstring GebLean.Ramified.freeAlgToNat}

Two theorems state that `natToFreeAlg` and `freeAlgToNat` are mutually inverse.

{docstring GebLean.Ramified.freeAlgToNat_natToFreeAlg}

{docstring GebLean.Ramified.natToFreeAlg_freeAlgToNat}

The pair packages as a single equivalence, whose two directions unfold to the
functions above.

{docstring GebLean.Ramified.natFreeAlgEquiv}

{docstring GebLean.Ramified.natFreeAlgEquiv_apply}

{docstring GebLean.Ramified.natFreeAlgEquiv_symm_apply}

# The polyadic word algebra and the tree algebra

`binWordAlgSig` and `treeAlgSig` are the {tech}[polyadic word algebra] and
{tech}[tree algebra] instances against which Part I chapter 6 states its
complexity readings, alongside the {tech}[monadic word algebra] `natAlgSig`
above.

{docstring GebLean.Ramified.binWordAlgSig}

{docstring GebLean.Ramified.treeAlgSig}

Each signature's carrier has constructors exhibited at the base object sort.

{docstring GebLean.Ramified.binEmpty}

{docstring GebLean.Ramified.binCons}

{docstring GebLean.Ramified.treeLeaf}

{docstring GebLean.Ramified.treeNode}

Each carrier also carries one {tech}[monotonic] recurrence and one
{tech}[flat] recurrence, built from
{name GebLean.Ramified.RIdent}`RIdent`, the schema-identifier type
{name GebLean.Ramified.RIdent.mrec}`RIdent.mrec` and
{name GebLean.Ramified.RIdent.frec}`RIdent.frec` construct — Part II
chapter 4's subject. `binLength` and `treeSize` are the monotonic instances;
`binTail` and `treeLeftChild` are the flat ones.

{docstring GebLean.Ramified.binLength}

{docstring GebLean.Ramified.binTail}

{docstring GebLean.Ramified.treeSize}

{docstring GebLean.Ramified.treeLeftChild}

# Morphisms of free-algebra signatures

A morphism of free-algebra signatures transports one carrier into another
along a constructor-label map that preserves arities.

{docstring GebLean.Ramified.AlgSigHom}

{docstring GebLean.Ramified.freeAlgMap}

# Multi-sorted signatures

`SortedSig` moves from the single-sorted free-algebra signatures above to
signatures over an explicit sort type, the format Part II chapter 3's
Lawvere-theory layer builds on. `constructorSig` is the bridge between the
two: it reads a free-algebra signature back as a multi-sorted one, with one
operation per {tech}[object type] and constructor label.

{docstring GebLean.Ramified.SortedSig}

{docstring GebLean.Ramified.SortedSig.sum}

{docstring GebLean.Ramified.constructorSig}

# Ramified types as a free algebra

The r-types themselves are generated as a free algebra over a
three-label signature, reusing every declaration of the first two
sections at a new instance.

{docstring GebLean.Ramified.RTypeShape}

{docstring GebLean.Ramified.rTypeSig}

{docstring GebLean.Ramified.RType}

{docstring GebLean.Ramified.RType.o}

{docstring GebLean.Ramified.RType.arrow}

{docstring GebLean.Ramified.RType.omega}

# Object sorts, tower sorts, and the standard denotation

{docstring GebLean.Ramified.RType.IsObj}

The tower sorts are the chain of {tech}[`Omega`-type]s built from `o` alone;
the {tech}[tier] of a tower sort is the iteration count.

{docstring GebLean.Ramified.RType.tower}

{docstring GebLean.Ramified.RType.IsTower}

A further predicate classifies the r-types with no `Omega` anywhere in their
structure, the simple types of Leivant III section 4.2.

{docstring GebLean.Ramified.RType.IsSimple}

The standard denotation sends every {tech}[object type] to a copy of a fixed
carrier and every function type to a function space; the theorem following it
states the object-type case.

{docstring GebLean.Ramified.RType.interp}

{docstring GebLean.Ramified.RType.interp_isObj}

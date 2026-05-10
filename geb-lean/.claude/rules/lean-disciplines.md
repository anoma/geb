# Lean disciplines

## Hole-marking discipline

Use `_` for unsolved goals: this surfaces the goal type as a build
error, which is what we want while a definition or proof is under
construction. The Lean keyword `sorry` is permitted as a transient
working tool only — committed code must build under
warnings-as-errors and therefore cannot contain `sorry`. The Lean
keyword `admit` is forbidden everywhere, always.

The warnings-as-errors mechanism is
`moreLeanArgs = ["-DwarningAsError=true"]` in `lakefile.toml`,
which promotes `declaration uses 'sorry'` (and every other
warning-class diagnostic) into a build error at the Lean kernel
level.

## Constructive-only Lean code

No `noncomputable`. No `axiom`. Minimise `Classical` usage. Use
the `Quotient` / `Quot` constructive API only; `Quot.out` and
`Quotient.out` (which require `Classical.choice`) are avoided.
The mechanical check for axiom dependencies is
`scripts/check-axioms.sh`.

## Literature-citation discipline

In transcription workstreams (for example the ER ↔ K^sim_2
equivalence, which transcribes Tourlakis 2018 / Wagner-Wong /
Grzegorczyk-hierarchy literature), every planned function,
definition, or theorem in a plan document carries a reference to
the literature proposition or in-codebase lemma it corresponds
to; every implemented function, definition, or theorem includes
the literature reference in its docstring.

Citations are specific (for example "Tourlakis 2018 §0.1.0.27
(3)") and reference the project's research documents in
`docs/research/` for the cross-reference network.

## Bottom-up named-composite discipline for categorical equivalences

When building a new categorical structure that is to be proven
equivalent to an existing one, never add a constructor or
morphism to the new category before its image in the target
category has been built and named as a `def` (with a `@[simp]`
interp lemma).

Workflow:

1. Identify the image in the target category that the new
   construct will translate to.
2. If it is not already present, build it bottom-up as a
   composition of atomic constructors of the target category.
3. Give it a name and prove its interp lemma in `Utilities/`.
4. Only then add the corresponding constructor (or helper) to
   the new category, with its translation function pointing
   directly at the named composite.

If a proposed construct cannot be built ultimately out of
compositions of the target category's atomic generators, that is
a signal not to add it — not to build a workaround.

## Non-negotiable interfaces for pre-existing mathematical objects

The interface of a Lean category formalising a pre-existing
mathematical object (its objects, its primitive constructors,
its generators) is fixed by the external mathematical source and
is not a design choice open to the implementation.

Implementation design (proof strategies, auxiliary inductives,
choice of named composites) may change freely. Interface
changes are not a valid response to implementation difficulty.
If implementation gets stuck, the correct moves are:

1. Re-examine the implementation strategy.
2. Strengthen supporting infrastructure in `Utilities/`.
3. Surface the obstruction for discussion before continuing.

Weakening or redefining the interface so the implementation
becomes easier is not a valid move.

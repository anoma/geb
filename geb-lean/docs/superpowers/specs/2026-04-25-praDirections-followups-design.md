# praDirections v2 Follow-Ups — Design

Bundles four small follow-up items deferred from the praDirections
v2 workstream (see `docs/superpowers/plans/2026-04-19-praDirections-naturality-v2.md`
and `.session/workstreams/presheaf-pra.md`).  All four items touch
the `GebLean/PresheafPRA.lean` and `GebLean/Utilities/Families.lean`
files.

## Status

Brainstorm complete 2026-04-25.  Ready for plan-writing.

## Items

### 1. `maxHeartbeats` tightening

**Files:** `GebLean/PresheafPRA.lean`.

Two `set_option maxHeartbeats 800000 in` declarations at the top of
the Task 7.9 helpers (`praPolyDirectionsData_baseHomComp_unwidened_aux`
and `praPolyDirectionsData_baseHomComp_unwidened`).  Tighten both to
`maxHeartbeats 400000`, which a code-review subagent established as
sufficient at the time of the Task 7.9 commit.

The accompanying linter-required explanatory comments stay; only the
numeric value changes.  If `400000` proves insufficient at build time,
escalate to `500000` first, then `600000`, then `800000` in order.

### 2. `catULiftFunctor` refactor as specialization of `catULiftFunctor2`

**Files:** `GebLean/Utilities/Families.lean`.

`catULiftFunctor : Cat.{v, u} ⥤ Cat.{max w v, max (w + 1) u}` is the
single-universe widening; `catULiftFunctor2 : Cat.{v, u} ⥤ Cat.{max v
w_v, max u w_u}` is the two-universe generalization (added later).
Setting `w_v := w` and `w_u := w + 1` recovers
`catULiftFunctor`'s output type.

Refactor: replace `catULiftFunctor`'s explicit `obj`/`map` body with
`catULiftFunctor2.{v, u, w, w + 1}` (universe-argument order to be
verified by the implementer).  The two existing callers
(`ccrNewFamilyNatTarget` at `Families.lean:3428` and the proof at
`Families.lean:3514`) continue to work because the bodies are
rfl-equivalent.

The proof at `Families.lean:3514` currently invokes `unfold
catULiftFunctor` followed by structural reasoning.  After the
refactor, that `unfold` exposes a `catULiftFunctor2` term; the
existing structural reasoning may need a follow-up `unfold
catULiftFunctor2` or be reworded as `simp only [catULiftFunctor,
catULiftFunctor2]`.  This is a localized fix; if more substantial
changes are needed, the refactor approach is reconsidered.

### 3. `uliftCategory` empirical scope narrowing

**Files:** `GebLean/PresheafPRA.lean`.

The file-scope `attribute [local instance] CategoryTheory.uliftCategory`
at line 36 is active throughout the file, including in sections that
may not need the instance (`presheafCatFunctor`, `presheafCat` at
lines 47–58, plus the three `section` blocks `PresheafPRADef`,
`PresheafPRAAccessors`, `PresheafPRAEvalAt`).

Refactor: remove the file-scope attribute, run `lake build`, and for
each section that fails to build, reintroduce the attribute as a
section-local declaration at the top of that section.

If empirically every section requires it, abandon the narrowing and
revert to file scope.  In that case the work is still informative —
it establishes that the broad scope is genuinely necessary.

### 4. Bridge theorem `praDirectionsAt_via_praPolyDirectionsFunctor`

**Files:** `GebLean/PresheafPRA.lean`,
`GebLeanTests/Utilities/PresheafPRADirNat.lean`.

Add a public `def` and a public `theorem` connecting the per-
component accessor `praDirectionsAt` to the natural-in-`(I, J, P)`
functor `praPolyDirectionsFunctor`.

#### Helper `praPolyDirectionsAtSourceObj`

Public `def` constructing a `praPolyDirectionsSource` object from a
per-component triple `(I, J, P, j, a)`.  Built via
`GrothendieckContraFunctor.mkObj` at the outer level (base = `((Cat.of
Jᵒᵖ, Cat.of Iᵒᵖ), P)`) and `Grothendieck.mk` at the inner level (fibre
= the widened element corresponding to `⟨j, a⟩`).

```lean
/--
Build a `praPolyDirectionsSource` object from a per-component
`(I, J, P, j, a)` triple.  Public packaging: callers can apply
`praPolyDirectionsFunctor` to this object to obtain the directions
presheaf in the natural-functor form.
-/
def praPolyDirectionsAtSourceObj
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (j : Jᵒᵖ) (a : praPositions I J P j) :
    praPolyDirectionsSource.{u_I, v_I, u_J, v_J, w_I, w'} :=
  …
```

#### Theorem `praDirectionsAt_via_praPolyDirectionsFunctor`

Public `@[simp] theorem` stating that the per-component accessor
agrees with the appropriately-unwidened fibre of
`praPolyDirectionsFunctor.obj` applied to the corresponding source
object.

```lean
/--
Bridge: `praDirectionsAt I J P j a` agrees with the unwidened-and-
unopped fibre of `praPolyDirectionsFunctor` applied to the
corresponding source object.  Connects the per-component accessor to
the natural-in-`(I, J, P)` functor.
-/
@[simp] theorem praDirectionsAt_via_praPolyDirectionsFunctor
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (j : Jᵒᵖ) (a : praPositions I J P j) :
    praDirectionsAt I J P j a = …
```

The exact RHS unwidening shape (whether `.unop`, `ULiftHom.down ⋙
ULift.downFunctor`, or a chain) is discovered at implementation time
via the LSP at an `_` placeholder for the RHS.

Proof aim: `rfl`.  Fallback: `simp only` with the Task 9 bridge
lemmas (`praPolyDirectionsFunctor_base`, `_fibre`, `_map_app`).  If
neither closes the proof, escalate to the user with a status report
on whether the proof seems doable at greater cost or whether the
proof approach is unclear.

#### Test

Append to `GebLeanTests/Utilities/PresheafPRADirNat.lean`:

```lean
/-! ## Bridge to praPolyDirectionsFunctor -/

section BridgeTest

example (I : Type 0) [Category.{0} I] (J : Type 0) [Category.{0} J]
    (P : PresheafPRACat.{0, 0, 0, 0, 0, 0} I J)
    (j : Jᵒᵖ) (a : praPositions I J P j) :
    praDirectionsAt I J P j a = … :=
  praDirectionsAt_via_praPolyDirectionsFunctor I J P j a

end BridgeTest
```

The `…` mirrors the RHS of the bridge theorem.

## Ordering and commits

Suggested execution order, cheapest first:

1. **`maxHeartbeats` tightening** — single commit.
2. **`catULiftFunctor` refactor** — single commit (plus possibly one
   localized proof-fix commit if the unfold site needs adjustment).
3. **`uliftCategory` empirical narrowing** — single commit.  Abandon
   if empirically every section needs the instance.
4. **Bridge theorem** — two commits:  one for
   `praPolyDirectionsAtSourceObj`, one for the theorem plus its test
   addition.

Total: 4–6 commits.

## Out of scope

The Phase 3–6 PRA universal-morphisms agenda
(`.session/workstreams/pra-universal-morphisms.md`) — identity PRA,
composition via Beck-Chevalley, factorization, products /
coproducts / equalizers / coequalizers via the presheaf decomposition,
algebras and coalgebras, double-category structure — is explicitly
deferred.  These follow-ups are localized cleanup; the larger agenda
is its own brainstorming/planning cycle.

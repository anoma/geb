# Workstream: PshInternal-Grothendieck Equivalence

## Status: In Progress (Task 9 partially complete)

## Completed (Task 8: Comparison Functor)

The comparison functor
`comparisonFunctor : PshInternalPresheaf X ⥤ (X.groth ⥤ Type w)`
is fully defined and compiles.

### Definitions in `GebLean/PshInternalGrothendieck.lean`

- `PshInternalCat.groth`: Grothendieck construction of
  `externalize X`, using mathlib's covariant `Grothendieck`.
- `comparisonFiber X P p`: the fiber
  `{ e : P.fiberAt p.base // P.projAt p.base e = p.fiber }`.
- `PshInternalPresheaf.projAt_naturality`: naturality of
  the projection map (base change commutes with projection).
- `PshInternalPresheaf.actionAt_naturality`: the action
  commutes with base change via `P.fiber.map f`.
- `PshInternalPresheaf.actionAt_congr_m`: `actionAt`
  depends only on the morphism value, not the proof.
- `comparisonPresheafMap`: the action on Grothendieck
  morphisms: restrict along `f`, then act by `phi`.
- `fiberHom_eqToHom_val`: eqToHom in the fiber category
  has underlying value equal to the identity morphism.
- `comparisonPresheafMap_id`: identity Grothendieck
  morphism acts as identity.
- `comparisonPresheafMap_comp`: composite Grothendieck
  morphism acts as composite (uses action naturality and
  associativity).
- `comparisonPresheaf P : X.groth ⥤ Type w`: the
  comparison presheaf for a single internal presheaf.
- `PshInternalPresheafHom.actionAt_comm`: a morphism
  of internal presheaves commutes with the action.
- `comparisonNatTrans`: the natural transformation
  induced by a morphism of internal presheaves.
- `comparisonFunctor`: the full comparison functor.
- `comparisonFib`: the fiber functor at a fixed base
  (previously defined, still present).

## Partially Complete (Task 9: Inverse Functor)

### Definitions added in `section Inverse`

- `grothBaseMor X c c' f x`: the Grothendieck morphism
  `⟨c, x⟩ ⟶ ⟨c', (fiberRestrict X f).obj x⟩` with
  identity fiber component, induced by base morphism `f`.
- `groth_eqToHom_fiber_comp_eqToHom`: a Grothendieck
  morphism `⟨id, eqToHom h⟩` between same-base objects
  composed with `eqToHom` yields the identity (proved
  using `subst` on the variable target fiber).
- `grothBaseMor_id_comp_eqToHom`: the specialization of
  the above for `grothBaseMor` at the identity.
- `groth_eqToHom_same_base_is_id`: the base component
  of `eqToHom` between same-base Grothendieck objects
  is the identity.
- `eqToHom_eq_cast`: in `Type w`, `eqToHom` equals `cast`.
- `inverseFiber X G c`: the sigma type
  `Sigma (x : fiberObj X c), G.obj ⟨c, x⟩`.
- `inverseFiberMap X G f p`: the restriction map on
  `inverseFiber`, using `grothBaseMor` and `G.map`.
- `inverseFiberMap_id`: the identity restriction is the
  identity function (proved using `Sigma.ext`,
  `heq_of_cast_eq`, and `grothBaseMor_id_comp_eqToHom`).
- `grothBaseMor_comp_fiber_val`: the `.val` of the fiber
  of a `grothBaseMor` composition equals `fiberId` at the
  composed restriction.

### Remaining for Task 9

1. `inverseFiberMap_comp`: composition of restriction maps.
   This requires proving a Grothendieck morphism equality
   `grothBaseMor (f ≫ g) x ≫ eqToHom = grothBaseMor f x ≫ grothBaseMor g _`.
   The proof approach is similar to `inverseFiberMap_id`:
   use `Grothendieck.ext` with base equality via
   `groth_eqToHom_same_base_is_id`, then `Subtype.ext` on
   the fiber, using `Grothendieck.comp_fiber`,
   `fiberHom_val_eqToHom_comp`, `fiberRestrict.map_id`, and
   `grothBaseMor_comp_fiber_val`.

   The main blocker is that after `Grothendieck.ext`, the
   fiber goal has nested `eqToHom`'s involving
   `((externalize X).map (eqToHom.base)).toFunctor.map`
   which requires rewriting `eqToHom.base` to `id` and then
   applying `fiberRestrict_id` and `Functor.map_id`. The
   rewrite chain is:
   - `groth_eqToHom_same_base_is_id` to get `eqToHom.base = id`
   - `eqToHom_map` or `Functor.map_comp` to simplify
     `(externalize X).map (eqToHom.base)`
   - `fiberRestrict_id` to replace `fiberRestrict X (id)` with `id`
   - `Functor.map_id` on the resulting identity functor

2. `inverseFiberPresheaf`: the functor `Cᵒᵖ ⥤ Type w`
   assembling `inverseFiber` and `inverseFiberMap` with
   `inverseFiberMap_id` and `inverseFiberMap_comp`.

3. The `PshInternalPresheaf` structure from the inverse
   functor: `proj`, `action`, and axioms.

4. The inverse functor on morphisms.

5. `inverseFunctor : (X.groth ⥤ Type w) ⥤ PshInternalPresheaf X`

### Remaining for Tasks 10+

- Unit isomorphism: `inverseFunctor ⋙ comparisonFunctor ≅ id`
- Counit isomorphism: `comparisonFunctor ⋙ inverseFunctor ≅ id`
- Equivalence assembly

## Proof patterns discovered

The transport proofs in the Grothendieck category are
intricate because:

- `(externalize X).map f).toFunctor` is definitionally
  `fiberRestrict X f`, but `simp`/`rw` sometimes cannot
  match through this definitional equality.
  Use `change` to rewrite the goal to use `fiberRestrict`.
- `eqToHom` between same-base Grothendieck objects has
  base component `eqToHom (rfl-like)`, which is
  propositionally (not definitionally) `id c`.
  Use `groth_eqToHom_same_base_is_id` followed by
  `fiberRestrict_id` to simplify.
- The `subst` trick for Grothendieck eqToHom proofs:
  parameterize the target fiber as a VARIABLE `y` with
  equality `h : y = x`, then `subst h` collapses the
  eqToHom to rfl/id. This was used in
  `groth_eqToHom_fiber_comp_eqToHom`.
- For sigma equality (`Sigma.ext`), the HEq component
  uses `heq_of_cast_eq` where the cast reduces to
  `G.map (eqToHom ...)` via `eqToHom_map` + `eqToHom_eq_cast`.

## File

`GebLean/PshInternalGrothendieck.lean`

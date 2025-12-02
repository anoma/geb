# Blockers and Open Questions

Items awaiting resolution. Check this at session start to see if any blockers
have been resolved or if input is needed.

## Format

```markdown
### [Workstream or Topic]

**Question/Blocker**: Description

**Context**: Why this matters, what was tried

**Status**: Awaiting input | Under investigation | Resolved
```

---

<!-- Add blockers below this line -->

### W-Type Category Equivalence - unitHom_unitInv proof (RESOLVED)

**Question/Blocker**: The proof of `unitHom_unitInv` (that `unitHom W ≫ unitInv W = id`)
was blocked by a transport issue in `WTypeDiagramHom.ext`.

**Solution**: Added `WTypePullback.transport_proj1` lemma showing that transport on
`WTypePullback` preserves `proj1`:

```lean
lemma WTypePullback.transport_proj1 {P Q : WTypeDiagram X Y}
    {onPos1 onPos2 : P.B → Q.B} (h : onPos1 = onPos2)
    (pb : WTypePullback P Q onPos1) : (h ▸ pb).proj1 = pb.proj1 := by
  cases h
  rfl
```

This allows rewriting `(hPos ▸ pb).proj1` to `pb.proj1` in the goal, after which
the nested match expressions reduce definitionally.

**Status**: Resolved

### W-Type Category Equivalence - counitHom_counitInv proof (RESOLVED)

**Question/Blocker**: The proof of `counitHom_counitInv` (that `counitHom P ≫ counitInv P = id`
on `wTypeToPolyBetween.obj (polyBetweenToWType.obj P)`) was blocked by fiber equality issues
involving `eqToHom` in opposite pi categories.

**Solution**: The proof was completed using two helper lemmas:

1. `eqToHom_catOp_pi_at_idx`: Shows that in `CategoryOp' (I → C)`, evaluating `eqToHom h` at
   index `i` equals `eqToHom (congrFun h i).symm`. Uses `Eq.recOn` to eliminate the function
   equality:
   ```lean
   private lemma eqToHom_catOp_pi_at_idx {I : Type*} {C : Type*} [Category C]
       {F G : I → C} (h : F = G) (i : I) :
       (eqToHom (C := CategoryOp' (I → C)) h) i =
         (eqToHom (congrFun h i).symm : G i ⟶ F i) :=
     Eq.recOn (motive := fun G' (h' : F = G') =>
       (eqToHom (C := CategoryOp' (I → C)) h') i =
         (eqToHom (congrFun h' i).symm : G' i ⟶ F i)) h rfl
   ```

2. `eqToHom_at_idx_left_eq_id`: Uses the above lemma combined with proof irrelevance. At the
   specific index `idx = ⟨⟨y', i⟩, rfl⟩`, the types are definitionally equal, so:
   - `congrFun h idx = rfl` (by `Subsingleton.elim`)
   - `(congrFun h idx).symm = rfl` (by rewriting)
   - `eqToHom rfl = 𝟙`, so `.left = id`

The full proof chains `counitHom_counitInv_lhs_step` (showing LHS.left e = e) with
`counitHom_counitInv_rhs_step` (showing RHS.left e = e) through `counitHom_counitInv_fiber_eq`.

**Key insight**: The trick is using `Eq.recOn` with an appropriate motive to eliminate the
function equality `h : F = G` from the goal. This bypasses the issue that `subst` cannot
handle non-variable equalities. The proof works because at the specific index, the pointwise
equality `congrFun h idx` is propositionally `rfl` due to definitional equality of the types.

**Status**: Resolved

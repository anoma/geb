# Cat-Copresheaf Adjunction Workstream

## Status: Complete

The adjunction L ⊣ Φ between categories and copresheaves on CategoryJudgments
has been fully constructed and verified.

## Completed

1. **Functor on quotients from CategoryQuotientMorphism** - Done
1. **Unit natural transformation (unitNatTrans)** - Done
   - `unitAppObj`, `unitAppMor`, `unitAppId`, `unitAppComp` defined
   - `unitNatTransData` structure complete with all naturality proofs
   - Fixed `naturality_composite` proof using `h_comp_move` lemma
1. **Counit natural transformation** - Done
   - `counitQuiverMor` - Quiver morphism from quotient quiver to original
   - `counitEvalQuot_quotId`, `counitEvalQuot_quotComp` - Helper theorems
   - `counit_map_id`, `counit_map_comp` - Functoriality proofs
   - `counitFunctorData` - Counit as OverFunctorData for each category C
   - `counitEval_natural`, `counitEvalQuot_natural` - Naturality at
     FreeMor and quotient levels
   - `inducedCategoryQuotientMorphism` - CategoryQuotientMorphism from functor
   - `inducedQuiverMor`, `inducedQuotFunctor` - Induced functor L(Φ(F))
   - `counitFunctor_natural_obj`, `counitFunctor_natural_mor` - Naturality
     of counit: F ∘ ε_C = ε_D ∘ L(Φ(F))
1. **Triangle identities** - Done
   - Second triangle (Φε) ∘ (ηΦ) = id_Φ:
     - `triangle2_mor` - morphism component
     - `triangle2_id` - identity witness component
     - `triangle2_comp` - composition witness component
   - First triangle (εL) ∘ (Lη) = id_L:
     - `categoryL F` - the category L(F) from copresheaf F
     - `derivedFromL F` - the double quotient L(Φ(L(F)))
     - `bundleQuotMorL`, `embedMorAsVar` - embedding morphisms as variables
     - `triangle1_obj` - objects map to themselves
     - `triangle1_mor`, `triangle1_mor_val` - morphisms map to themselves
1. **Adjunction structure** - Done
   - `CatCopresheafAdjunctionData` - Structure bundling L, Φ, unit, counit,
     and triangle identities
   - `catCopresheafAdjunction` - The canonical adjunction data instance
   - `adjunction_triangles_hold` - Verification theorem confirming triangles
1. **L functor on morphisms** - Done
   - `NatTransData.toCategoryQuotientMorphism` - CategoryQuotientMorphism from
     NatTransData (natural transformation between copresheaves)
   - `NatTransData.toQuotQuiverMor` - The quiver morphism on quotient quivers
   - `NatTransData.toOverFunctorData` - L acts on morphisms: NatTransData to
     OverFunctorData
   - Pattern: `have heq := hcomp` then `cases heq` to handle composability
     proofs without creating duplicate hypothesis names
1. **L functor functoriality** - Done
   - `CategoryQuotientMorphism.id` - Identity morphism on CategoryQuotientData
   - `FreeMor.mapQuiver_overQuiverId` - mapQuiver with identity is identity
   - `CategoryQuotientMorphism.quotMapMor_id_self` - quotMapMor with id is id
   - `toOverFunctorData_id` - L preserves identity:
     `(NatTransData.id F).toOverFunctorData = OverFunctorData.id F.toOverCategoryData`
   - `FreeMor.mapQuiver_cast_overQuiv` - mapQuiver commutes with cast
   - `FreeMor.mapQuiver_quiverComp` - mapQuiver respects composition
   - `CategoryQuotientMorphism.quotMapMor_quiverComp` - quotMapMor respects comp
   - `toOverFunctorData_comp` - L preserves composition:
     `(α.comp β).toOverFunctorData = α.toOverFunctorData.comp β.toOverFunctorData`

1. **Mathlib Adjunction** - Done
   - `instance : Category (CategoryJudgments.FunctorData (Type u))` with
     NatTransData as morphisms (id, comp, id_comp, comp_id, assoc)
   - `instance : Category BundledOverCategoryData` with OverFunctorData as
     morphisms
   - `LFunctor : Functor (FunctorData (Type u)) BundledOverCategoryData`
   - `PhiFunctor : Functor BundledOverCategoryData (FunctorData (Type u))`
   - `unitNT : NatTrans (Functor.id) (LFunctor ⋙ PhiFunctor)` with naturality
   - `counitNT : NatTrans (PhiFunctor ⋙ LFunctor) (Functor.id)` with naturality
   - `adjunctionCoreUnitCounit : Adjunction.CoreUnitCounit LFunctor PhiFunctor`
     with triangle identities proven via `aesop` for comp case
   - `catCopresheafMathlibAdjunction : LFunctor ⊣ PhiFunctor` constructed via
     `Adjunction.mkOfUnitCounit`

## Future Enhancements

None at this time. The mathlib adjunction L ⊣ Φ is complete.

## Key Files

- `/home/terence/git-workspaces/geb/geb-lean/GebLean/CatJudgmentAdjunction.lean`
  - Main file containing all adjunction code
  - `LFunctorMorphisms` section (lines ~966-1050): L functor on morphisms
  - `AdjunctionStructure` section (lines ~1050+): bundled adjunction data

## Key Definitions to Reference

- `CategoryQuotientData` - Structure bundling quiver with id/comp witnesses
- `FreeMor Q a b` - Free morphisms as binary trees
- `FreeMorEquiv` / `FreeMorEquivGen` - Equivalence relations for quotient
- `QuotMor` - Quotient type of free morphisms
- `quotMor` - Lifts FreeMor to QuotMor
- `quotComp` - Composition on QuotMor via Quotient.lift2
- `counitEval` / `counitEvalQuot` - Evaluate free/quotient morphisms in
  the original category
- `derivedQuotientData C` - The CategoryQuotientData derived from C
- `counitFunctorData C` - The counit ε_C : L(Φ(C)) → C as OverFunctorData
- `inducedQuotFunctor F` - The induced functor L(Φ(F)) from F : C → D
- `NatTransData.toOverFunctorData` - L functor on morphisms: α : F → G maps
  to OverFunctorData L(F) → L(G)
- `CategoryQuotientMorphism.id` - Identity CategoryQuotientMorphism
- `toOverFunctorData_id` - L preserves identity
- `toOverFunctorData_comp` - L preserves composition
- `LFunctor` - Mathlib Functor from copresheaves to categories
- `PhiFunctor` - Mathlib Functor from categories to copresheaves
- `unitNT` - Mathlib NatTrans for the unit η
- `counitNT` - Mathlib NatTrans for the counit ε
- `adjunctionCoreUnitCounit` - CoreUnitCounit data with triangle proofs
- `catCopresheafMathlibAdjunction` - The full mathlib Adjunction L ⊣ Φ

## Technical Notes

### Counit Naturality Pattern

For a functor F : C → D, naturality says F ∘ ε_C = ε_D ∘ L(Φ(F)).
This is proven in two parts:

- `counitFunctor_natural_obj`: Objects agree (both are F.objFn)
- `counitFunctor_natural_mor`: Morphisms agree via `counitEvalQuot_natural`

The proof uses `cases` on composability equalities to avoid transport issues.

### Triangle Identities Pattern

The triangle identities are proven component-wise:

- **Second triangle (Φε) ∘ (ηΦ) = id_Φ**: For a category C, embedding a
  morphism via η and then applying Φ(ε) returns the original.
  - Key insight: `counitEvalQuot(quotMor(var f)) = f`
- **First triangle (εL) ∘ (Lη) = id_L**: For a copresheaf F, embedding a
  quotient morphism as a variable in L(Φ(L(F))) and evaluating via ε returns
  the original.
  - Key insight: `embedMorAsVar` embeds qm as `quotMor(var(bundle qm))`
  - `counitEvalQuot` evaluates this back to `bundle qm`

### Composability Proof Pattern

When proving properties about composable pairs, the pattern is:

1. Use `rcases p with ⟨⟨g, f⟩, hcomp⟩` to destructure the pair
2. Use `have heq : g_tgt = f_src := hcomp` to convert Composable to Eq
3. Use `cases heq` to substitute and reduce to the reflexivity case
4. Now transports by `hcomp` become definitionally trivial

Do NOT use `simp at hcomp` as this creates a duplicate hypothesis `heq`
that the goal doesn't reference, preventing `subst`.

### Build Status

The file builds with no errors or warnings. Run `lake build` and `lake test`
to verify clean build.

## Mathematical Context

### Related Constructions

The adjunction L ⊣ Φ relates to several constructions in the literature.

**Category presentations.** The construction of categories by generators and
relations is classical (Mac Lane, Mitchell). Given a graph G and relations R,
one forms F(G)/R where F(G) is the free category on G. The adjunction L ⊣ Φ
is a type-theoretic reformulation: the copresheaf F on CategoryJudgments
bundles the graph and relation data into a single structure, with identity
and composition witnesses as first-class components.

**Essentially algebraic theories.** The category Cat of small categories is
locally finitely presentable (Adámek-Rosický). Categories are models of a
finitary essentially algebraic theory, and Gabriel-Ulmer duality relates
such theories to their model categories. The adjunction L ⊣ Φ provides a
computational presentation of this relationship: CategoryJudgments encodes
the signature, FunctorData encodes presentations with explicit witnesses,
L constructs the semantic category, and Φ extracts the presentation.

**Nerve-realization.** The nerve-realization adjunction N ⊣ τ₁ relates
categories to simplicial sets. The nerve encodes a category as a presheaf
on the simplex category Δ, where face maps encode composition and
degeneracies encode identities. The adjunction L ⊣ Φ uses explicit judgment
types (Obj, Mor, Id, Comp) rather than positional encoding, making the
construction more directly expressible in dependent type theory.

**Computads.** Computads (Street, Batanin) generalize category presentations
to higher dimensions by treating relations as 2-cells. CategoryJudgments can
be viewed as a 1-truncated computad where the identity and composition
witnesses play the role of generating 2-cells that are then quotiented.

**Type-theoretic categories.** FunctorData corresponds to the standard
type-theoretic representation of categories: a type of objects, a dependent
type of morphisms, identity and composition operations, with equations.
The adjunction formalizes the syntax-semantics relationship between such
presentations and actual categories, connecting to categorical semantics
of dependent type theory and Categories with Families.

### Potential Applications

**Categorical programming.** FunctorData can serve as source-level
representations of categories, with L as a compiler to semantic categories
and Φ as extraction of presentations. This parallels the use of polynomial
functors for data types in systems such as Geb.

**Coherence theorems.** The counit ε : L(Φ(C)) → C provides a canonicalization
map, and the unit η : F → Φ(L(F)) provides a quotient map. The triangle
identities establish coherence conditions. This structure may be applicable
to proving coherence theorems for monoidal categories, bicategories, and
related structures.

**Higher category presentations.** CategoryJudgments can be extended with
additional judgment types for 2-cells and higher coherences, providing a
systematic approach to presenting 2-categories and (∞,1)-categories via
dependent type-theoretic signatures.

**Proof assistant infrastructure.** FunctorData is naturally type-checkable,
making it suitable as a user-facing interface for defining categories in
proof assistants. The functor L constructs the verified mathematical object
from the presentation.

**Computational category theory.** Categories can be computed via their
presentations. The quotient construction (QuotMor) provides a representation
suitable for algorithmic manipulation, potentially enabling implementation
of categorical constructions such as limits, colimits, and adjunctions on
presentations.

**Categorical databases.** Related to functorial data migration (Spivak),
schemas can be presented as copresheaves, with L giving the free category
on the schema and Φ extracting the schema from a category of instances.

# Universal Property Investigations

## Status: Complete

Investigation of which universal properties are preserved by our adjunction
functors beyond the automatic ones (right adjoints preserve limits, left
adjoints preserve colimits).

## Investigations

### 1. Does PhiFunctor preserve coproducts?

**Status:** Complete - YES, Φ preserves coproducts

**Analysis:**

The coproduct of categories C and D is their disjoint union C ⊔ D:

- Objects: C.Obj ⊔ D.Obj (Sum type)
- Morphisms: C.Mor ⊔ D.Mor (no cross-morphisms between components)
- Composable pairs: C.CompPairs ⊔ D.CompPairs (pairs from different components
  cannot compose because cod(f) ≠ dom(g) when f, g are in different components)

Φ(C ⊔ D) produces a FunctorData with:

- objC = C.Obj ⊔ D.Obj
- morC = C.Mor ⊔ D.Mor
- idC = C.Obj ⊔ D.Obj
- compC = C.CompPairs ⊔ D.CompPairs

The pointwise coproduct Φ(C) ⊔ Φ(D) has identical structure, and all structure
maps (dom, cod, idMor, left, right, composite) match componentwise.

**Conclusion:** Φ(C ⊔ D) ≅ Φ(C) ⊔ Φ(D). The embedding Φ preserves coproducts
because the disjoint union of categories corresponds exactly to the pointwise
coproduct of their represented copresheaves.

**Formalization:** Would require setting up coproduct infrastructure in
BundledOverCategoryData. Could leverage the equivalence with Cat if mathlib
has coproducts for Cat.

### 2. Does LFunctor preserve products?

**Status:** Complete - YES, L preserves products

**Analysis:**

Products in FunctorData (copresheaves) are pointwise:

- (F × G).objC = F.objC × G.objC
- (F × G).morC = F.morC × G.morC
- (F × G).idC = F.idC × G.idC
- (F × G).compC = F.compC × G.compC
- All structure maps act componentwise

Products in BundledOverCategoryData (categories) are product categories:

- Objects: C.Obj × D.Obj
- Morphisms (a₁,b₁) → (a₂,b₂): C.Mor(a₁,a₂) × D.Mor(b₁,b₂)
- Composition: componentwise

**Key insight:** In F × G, the morphism type (F × G).morC = F.morC × G.morC
contains ALL pairs of morphisms, including (m, id) and (id, n) forms. This
allows "padding" shorter paths with identities.

**Why L(F × G) ≅ L(F) × L(G):**

1. Objects match: F.objC × G.objC
2. A morphism in L(F × G) from (a₁,b₁) to (a₂,b₂) is an equivalence class of
   paths using pairs from F.morC × G.morC
3. Any pair of independent paths (one in L(F), one in L(G)) can be represented
   in L(F × G) by padding the shorter path with identity morphisms
4. The equivalence relations match because composition relations in F × G
   decompose as pairs of composition relations
5. Composition is componentwise in both

**Conclusion:** L(F × G) ≅ L(F) × L(G). The reflector L preserves binary
products.

**Implication:** By nLab Theorem 4.1, since L preserves products and the
ambient category (copresheaves) is cartesian closed, categories form an
exponential ideal and Φ preserves exponentials.

### 3. Does product preservation imply exponential preservation?

**Status:** Complete - YES, with caveats on formalization

**What mathlib has:**

- `CategoryTheory.CartesianClosed` - cartesian closed categories
- `CategoryTheory.Exponentiable` - objects with exponentials
- `Mathlib.CategoryTheory.Closed.Functor` - cartesian closed functors that
  "naturally preserve exponentials"
- Exponential comparison morphisms and Frobenius morphism

**What mathlib may NOT have directly:**

The specific theorem "If L preserves products in a reflective adjunction into
a cartesian closed category, then Φ preserves exponentials" does not appear
to be stated explicitly.

**Theoretical result:**

By nLab Theorem 4.1, since:

1. The copresheaf category [CategoryJudgments, Type] is cartesian closed
   (as a presheaf/copresheaf topos)
2. L preserves binary products (Investigation 2)

We conclude:

- Categories (via BundledOverCategoryData) form an exponential ideal in
  copresheaves
- The inclusion Φ preserves exponentials
- The subcategory of categories is itself cartesian closed

**Concrete meaning:**

For categories C and D in BundledOverCategoryData, the exponential D^C in
the category of categories is the functor category [C, D]. The theorem says:

Φ(D^C) ≅ Φ(D)^{Φ(C)}

i.e., the copresheaf of the functor category equals the internal hom of
copresheaves.

**Formalization path:**

Would need to either use mathlib's Frobenius/exponential comparison machinery
or prove the specific theorem for our adjunction.

### 4. Does PhiFunctor preserve coequalizers?

**Status:** Complete - NO, Φ does not preserve coequalizers

**Counterexample:**

Let:

- A = 1 (terminal category: one object \*, one identity)
- B = 2 (two objects 0, 1 with one non-identity m : 0 → 1)
- F : 1 → 2 with F(\*) = 0
- G : 1 → 2 with G(\*) = 1

**Coequalizer in Cat:**

Q = coeq(F, G) identifies 0 with 1, producing a category with:

- One object (call it •)
- Morphisms: id, m, m², m³, ... (the free monoid on one generator)

The morphism m : 0 → 1 becomes m : • → • after identification, making m
composable with itself and generating infinitely many morphisms.

**Applying Φ:**

Φ(Q) has:

- objC = {•} (one element)
- morC = ℕ (countably infinite - all powers of m)

**Coequalizer in copresheaves (pointwise):**

coeq(Φ(F), Φ(G)) has:

- objC = {•} (quotient identifying 0 ~ 1)
- morC = {[id], m} (quotient identifying id₀ ~ id₁, leaving m distinct)

Only TWO morphisms!

**Why the difference:**

- In Cat, coequalizers create quotient CATEGORIES with induced composition,
  which can generate new morphisms
- In copresheaves, coequalizers are pointwise quotients of SETS - no new
  composites are generated

**Conclusion:** Φ(coeq(F, G)) ≇ coeq(Φ(F), Φ(G)). The coproduct preservation
was a special case; general colimits are not preserved.

### 5. Does LFunctor preserve equalizers?

**Status:** Complete - LIKELY YES (no counterexample found)

**Initial hypothesis:** Probably no - equalizers involve subobjects, which the
free category construction may not preserve.

**Analysis:**

Equalizers in copresheaves are computed pointwise:

- eq(α, β).objC = { x ∈ F.objC | α_Obj(x) = β_Obj(x) }
- eq(α, β).morC = { m ∈ F.morC | α_Mor(m) = β_Mor(m) }
- eq(α, β).compC = composable pairs from eq(α, β).morC

Equalizers in categories:

- Objects: { X ∈ C.Obj | F(X) = G(X) }
- Morphisms: { f ∈ C.Hom | F(f) = G(f) }

**The question:** Is L(eq(α, β)) ≅ eq(L(α), L(β))?

For objects: These match since L preserves objects.

For morphisms: The analysis reveals:

- In L(eq(α,β)), we have equivalence classes of paths where EACH STEP satisfies
  α = β
- In eq(L(α), L(β)), we have equivalence classes where L(α) and L(β) agree on
  THE WHOLE CLASS

**Forward direction (always works):** If each m_i satisfies α(m_i) = β(m_i),
then:

```text
L(α)([m_1, ..., m_n]) = [α(m_1), ..., α(m_n)]
                      = [β(m_1), ..., β(m_n)]
                      = L(β)([m_1, ..., m_n])
```

**Reverse direction (the critical question):** If L(α)([path]) = L(β)([path]),
can we represent [path] by morphisms that individually satisfy α = β?

Attempted counterexamples failed because NatTransData must preserve composition.
If [m_1, ..., m_n] reduces to [k] via composition, then L(α)([path]) = [α(k)]
and L(β)([path]) = [β(k)]. For these to be equal as single-morphism classes, we
need α(k) = β(k).

**Key insight:** The NatTransData structure (preservation of composition) forces
agreement on composites when the composition relation applies. This propagates
the equalizer condition through the quotient structure.

**Conclusion:** L likely preserves equalizers. Counterexamples would require
exotic constructions where the codomain's composition relation identifies
distinct images, but the NatTransData structure constrains this significantly.

**Formalization:** A formal proof would need to show:

1. The inclusion eq(α,β) → F induces a functor L(eq(α,β)) → L(F)
2. This functor is fully faithful with image exactly eq(L(α), L(β))

The argument would use the fact that NatTransData preserves composition to show
that morphism equivalence classes in L(eq(α,β)) correspond bijectively to those
in eq(L(α), L(β)).

### 6. Subobject classifiers for copresheaf categories

**Status:** Complete - Mathlib has infrastructure, construction is possible

**Questions answered:**

1. Does mathlib provide subobject classifiers for presheaf/copresheaf categories?
2. Can we use the equivalence with copresheaves to get a subobject classifier
   for FunctorData?
3. What does this look like concretely?

**What mathlib has:**

1. `CategoryTheory.Topos.Classifier` - General framework:
   - `Classifier C` structure with Ω, truth morphism, characteristic maps
   - `HasClassifier C` class
   - Representability theorem: C has classifier iff Subobject functor is
     representable

2. `CategoryTheory.Sites.Sieves` - Sieve infrastructure:
   - `Sieve X` = set of morphisms to X, closed under left-composition
   - Complete lattice structure on sieves
   - `Sieve.functor` - constructs presheaf from sieve
   - Pullback and pushforward operations

3. `CategoryTheory.Sites.Closed` - J-closed sieves:
   - `closedSieves` presheaf sends object to J-closed sieves on it
   - Proven to be a J-sheaf
   - Serves as subobject classifier for J-sheaves

**Theoretical construction:**

For presheaves [C^op, Set]:

- Ω(c) = sieves on c (downward-closed families of morphisms into c)
- true : 1 → Ω picks the maximal sieve at each object

For copresheaves [C, Set] (our case):

- Ω(c) = cosieves on c (upward-closed families of morphisms out of c)
- A cosieve on c is a set S of morphisms f : c → X such that if f ∈ S
  and g : X → Y, then g ∘ f ∈ S

**For FunctorData:**

Since FunctorData (Type u) ≃ (Obj ⥤ Type u) = [CategoryJudgments, Type], and this
is a functor category into Type (a topos), FunctorData has a subobject classifier:

- Ω.objC = cosieves on Obj in CategoryJudgments
- Ω.morC = cosieves on Mor in CategoryJudgments
- Ω.idC = cosieves on Id in CategoryJudgments
- Ω.compC = cosieves on Comp in CategoryJudgments

The structure maps are determined by how cosieves transform under the
morphisms dom, cod, idMor, idObj, left, right, composite of CategoryJudgments.

**Practical implications:**

- Mathlib's infrastructure could be instantiated for [CategoryJudgments, Type]
- The equivalence would transport the classifier to FunctorData
- For the reflective subcategory of categories, the classifier doesn't directly
  apply (categories form a subcategory, not a topos)

**Formalization path:**

1. Show [CategoryJudgments, Type u] satisfies `HasClassifier`
2. Construct the classifier explicitly or use mathlib's presheaf topos machinery
3. Transport via the equivalence FunctorData ≃ (Obj ⥤ Type)

**References:**

- [Mathlib.CategoryTheory.Topos.Classifier](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Topos/Classifier.html)
- [Mathlib.CategoryTheory.Sites.Sieves](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Sites/Sieves.html)
- [Mathlib.CategoryTheory.Sites.Closed](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Sites/Closed.html)

### 7. Comparison with nerve/realization adjunction

**Status:** Complete

**Questions answered:**

1. What are the structural similarities between our adjunction and the
   nerve-realization adjunction?
2. What are the differences?
3. Can insights from nerve-realization inform our understanding?

**The nerve-realization adjunction:**

```text
|-| ⊣ N : Cat ⇆ sSet = [Δ^op, Set]
```

- Δ = simplex category = {[0], [1], [2], ...} with order-preserving maps
- N is fully faithful (Kerodon Prop 1.2.2.1, Rezk Prop 4.10)
- N(C)_n = n-chains of composable morphisms in C
- |-| is the "free category" on a simplicial set
- Counit is an isomorphism (reflective adjunction)

**Our adjunction:**

```text
L ⊣ Φ : BundledOverCategoryData ⇆ FunctorData = [CategoryJudgments, Type]
```

- CategoryJudgments = {Obj, Mor, Id, Comp} with structure morphisms
- Φ is fully faithful (phiFunctorFullyFaithful)
- Φ(C) has objC, morC, idC, compC (fixed-arity data)
- L is the "free category" on a copresheaf
- Counit is an isomorphism (reflective adjunction)

**Structural similarities:**

1. Both are reflective adjunctions (fully faithful right adjoint)
2. Both have "categories" as the reflective subcategory
3. Both have "free category" as left adjoint
4. Both embed categories into a functor category
5. Both have isomorphic counits
6. Both are monadic (idempotent monads)

**Structural differences:**

| Aspect | Nerve-Realization | Our Adjunction |
|--------|-------------------|----------------|
| Variance | Presheaves (contravariant) | Copresheaves (covariant) |
| Index size | Δ (infinite objects) | CategoryJudgments (4 objects) |
| Data | All n-chains (any length) | Fixed components |
| Style | Simplicial/infinitary | Algebraic/finitary |

**Insights:**

1. **Computational advantage**: Our representation is more directly computational
   with finite components and fixed-arity structure maps. The simplicial approach
   requires handling arbitrary-length chains.

2. **Both achieve the same goal**: Both adjunctions show that categories can be
   recovered from their presentation data, with "free category" universally
   solving the presentation problem.

3. **Homotopy theory connection**: The nerve-realization adjunction is
   fundamental for quasi-categories and ∞-categories. Our adjunction might have
   analogous generalizations where "weak copresheaves" model higher categories.

4. **Density**: Both N and Φ are "nerves" arising from functors from small
   categories into Cat. The density of these functors determines adjunction
   properties.

5. **Preservation properties parallel**: Both right adjoints preserve limits
   (automatic) and likely preserve coproducts (special structure). Both left
   adjoints preserve colimits (automatic), and ours preserves products.

**For GEB project:**

The copresheaf representation captures exactly the algebraic structure of
categories in a form natural for computational interpretations. The finitary
nature benefits type-theoretic presentations compared to the infinitary
simplicial approach.

**References:**

- [nLab: nerve and realization](https://ncatlab.org/nlab/show/nerve+and+realization)
- [1Lab: Nerve and realisation](https://1lab.dev/Cat.Functor.Kan.Nerve.html)
- [Kerodon: Simplicial Categories](https://kerodon.net/tag/00JN)
- [Rezk: Introduction to Quasicategories](https://rezk.web.illinois.edu/quasicats.pdf)

## Completed Investigations

All 7 investigations complete:

1. **Φ preserves coproducts** - YES (disjoint union structure matches)
2. **L preserves products** - YES (padding with identities)
3. **Exponential preservation** - YES via nLab Theorem 4.1 (conditional on L
   preserving products)
4. **Φ preserves coequalizers** - NO (counterexample: free monoid generation)
5. **L preserves equalizers** - LIKELY YES (no counterexample found)
6. **Subobject classifiers** - Mathlib has infrastructure; construction possible
7. **Nerve comparison** - Structural analog with computational advantages

## Formalization Status

### Φ preserves binary coproducts - FORMALIZED

In `CatJudgmentAdjunction.lean`, section `BinaryCoproduct`:

- `OverQuiver.sum` - disjoint union of quivers
- `OverCategoryData.sum` - binary coproduct of categories
- `FunctorData.sum` - binary coproduct of copresheaves
- `phiFunctorPreservesCoproduct` - forward natural transformation
- `phiFunctorPreservesCoproductInv` - inverse natural transformation
- `phiFunctorPreservesCoproduct_comp_inv` - forward-inverse composition is id
- `phiFunctorPreservesCoproduct_inv_comp` - inverse-forward composition is id

### L preserves binary products - PARTIAL

In `CatJudgmentAdjunction.lean`, section `BinaryProduct`:

- `OverQuiver.prod` - product of quivers
- `OverCategoryData.prod` - binary product of categories (complete with all laws)
- `FunctorData.prod` - binary product of copresheaves
- `prodQuotData`, `quotData₁`, `quotData₂` - abbreviations for quotient data
- `prodQuiver_src_fst`, `prodQuiver_tgt_fst`, etc. - quiver src/tgt project to components
- `prodQuotData_idObj_fst`, `prodQuotData_idMor_fst`, etc. - idObj/idMor project
  to components
- `prodQuotData_id_src_fst`, `prodQuotData_id_tgt_fst` - id_src/id_tgt proofs project
- `freeMorProj₁`, `freeMorProj₂` - project FreeMor from product to components
- `freeMorProj₁_id` - projection preserves identity morphisms
- `freeMorProj₁_var_simple` - projection extracts first component of var
- `freeMorProj₁_respects_gen` - projection respects equivalence generators (PARTIAL)
- `freeMorProj₁_respects_equiv` - projection respects full equivalence

Remaining work for `L(F₁ × F₂) ≅ L(F₁) × L(F₂)`:

1. **id_witness and comp_witness cases** - The proof that `freeMorProj₁` respects
   equivalence has two remaining cases that require careful cast handling:
   - `id_witness`: Shows projection of identity witness equivalence holds
   - `comp_witness`: Shows projection of composition witness equivalence holds
   The challenge is that the `id_witness` generator involves a `cast` term:
   `cast (by rw [D.id_src i, D.id_tgt i]) (FreeMor.var (D.idMor i))`
   `~ FreeMor.id (D.idObj i)`
   When projected, `freeMorProj₁` pattern-matches on the cast term, but Lean
   cannot reduce `freeMorProj₁ (cast h x)` to `cast h' (freeMorProj₁ x)` automatically
   because pattern matching on cast requires the proof to reduce to `rfl`.
   The proof requires explicit `Eq.rec` reasoning or cast distribution lemmas.

2. **Backward pairing** - Define the pairing map `L(F₁) × L(F₂) → L(F₁ × F₂)`
   that combines two quotient morphisms into a single product morphism.

3. **Round-trip proofs** - Show the forward and backward maps compose to identity.

### Φ preserves initial objects - FORMALIZED

In `CatJudgmentAdjunction.lean`, section `TerminalAndInitial`:

- `OverQuiver.initial` - empty quiver (PEmpty objects and morphisms)
- `OverCategoryData.initial` - initial category (empty category)
- `FunctorData.initial` - initial copresheaf (maps everything to PEmpty)
- `phiOfInitial` - Φ applied to initial category
- `initialCompCMap`, `initialCompCMapInv` - maps between compC types
- `phiFunctorPreservesInitial` - forward natural transformation
- `phiFunctorPreservesInitialInv` - inverse natural transformation
- `phiFunctorPreservesInitial_comp_inv` - forward-inverse is id
- `phiFunctorPreservesInitial_inv_comp` - inverse-forward is id

### L preserves terminal objects - FORMALIZED

In `CatJudgmentAdjunction.lean`, section `TerminalAndInitial`:

- `OverQuiver.terminal` - terminal quiver (PUnit object and morphism)
- `OverCategoryData.terminal` - terminal category (one object, one morphism)
- `FunctorData.terminal` - terminal copresheaf (maps everything to PUnit)
- `lOfTerminal`, `bundledTerminal` - L(terminal) and the bundled terminal
- `lToTerminalFunctor` - forward functor L(terminal) → terminal
- `terminalQuotData`, `terminalQuiver` - quotient data for terminal
- `terminal_var_equiv_id_at_idObj` - identity witness gives var ~ id
- `terminal_freemor_equiv_id_aux` - all FreeMor equivalent to identity
- `terminal_quotmor_eq_id` - all quotient morphisms equal to quotId
- `terminalQuotMorSubsingleton` - subsingleton instance
- `terminalToLFunctor` - inverse functor terminal → L(terminal)
- `lTerminal_roundtrip_LtoL` - L → term → L is identity
- `lTerminal_roundtrip_termTerm` - term → L → term is identity

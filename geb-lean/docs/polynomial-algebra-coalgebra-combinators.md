# Polynomial Algebra/Coalgebra Combinators

This document surveys constructions from the literature that can be
built on our polynomial endofunctor infrastructure on slice
categories, with references to both the mathematical sources and
the corresponding code in our codebase.

## Existing Infrastructure

Our codebase provides the following for polynomial endofunctors
`P : PolyEndo X` on slice categories `Over X`:

**In `PolyAlg.lean`:**

- `PolyEndo X`, `polyEndoFunctor` -- polynomial endofunctors
- `WTypeEndo X`, `wTypeEndoFunctor` -- W-type diagrams
- `PolyAlg P` -- algebra category
- `PolyCoalg P` -- coalgebra category
- `PolyFix`, `polyFixAlg`, `polyFixAlg_isInitial` --
  initial algebra (W-type)
- `polyFixStr_iso` -- Lambek's lemma
- `PolyCofix`, `polyCofixCoalg` -- terminal coalgebra (M-type)
- `polyFreeMonad` -- free monad
- `polyCofreeComonad` -- cofree comonad
- `polyAlgMonadEquiv` -- monad algebra equivalence
- `polyCoalgComonadEquiv` -- comonad coalgebra equivalence
- `polyAlgHasLimitsOfSize` -- limits for algebras

**In `CofreeCategory.lean`:**

- `PolyCofreeCat P` -- cofree category (category instance)
- `polyCoalgCopresheafEquiv` -- copresheaf equivalence
- `polyCoalgHasLimitsOfSize` -- limits for coalgebras
- `polyCoalgHasColimitsOfSize` -- colimits for coalgebras

**In `PolyAlgUMorph.lean`:**

- `algPullback`, `algPullbackFunctor` -- algebra pullback
- `coalgPushforward`, `coalgPushforwardFunctor` --
  coalgebra pushforward
- `algCoprodDesc` -- coproduct algebras
- `coalgProdLift` -- product coalgebras
- `algEqRestrict` -- equalizer algebras
- `coalgCoeqExtend` -- coequalizer coalgebras

**In `Polynomial.lean`:**

- `polyToOverComp` -- polynomial composition

---

## A. Colimits for Polynomial Algebras

### A: References

- [nLab: colimits in categories of algebras](https://ncatlab.org/nlab/show/colimits+in+categories+of+algebras)
- Borceux, *Handbook of Categorical Algebra* Vol. 2, Prop 4.3.2
- Barr-Wells, *Toposes, Triples, and Theories*, Thm 3.9

### A: Mathematical Background

Limits in Eilenberg-Moore categories are straightforward: the
forgetful functor `U : C^T -> C` creates all limits that exist in
`C`. We already have this via `polyAlgHasLimitsOfSize`.

Colimits are more involved. The forgetful functor does not in general
create or preserve colimits. The results are:

**Linton's theorem.** If `C` is cocomplete and `C^T` has reflexive
coequalizers, then `C^T` is cocomplete.

**Colimit creation.** If the monad `T` preserves `J`-shaped colimits,
then `U : C^T -> C` creates `J`-shaped colimits.

**Finitary/accessible case.** If `C` is cocomplete and `T` preserves
filtered colimits (equivalently, `T` is finitary/accessible), then
`C^T` is cocomplete.

**Beck coequalizer.** Every T-algebra is a reflexive coequalizer of
free T-algebras. Concretely, any `(c, xi : Tc -> c)` is the
coequalizer of the reflexive fork `FUFUc => FUc -> (c, xi)`. The
underlying fork in `C` is a split coequalizer (hence absolute,
preserved by any functor).

### A: Application to Our Setting

Our polynomial endofunctors on `Over X` are finitary: each operation
has argument positions indexed by a fiber type, which is finite in the
finiteness sense relevant to filtered colimit preservation. The free
monad `polyFreeMonad X P` is thus an accessible monad on `Over X`.

The chain for deriving colimits:

1. `polyEndoFunctor` preserves filtered colimits (finitary)
2. `polyFreeMonad X P` preserves filtered colimits
3. `HasReflexiveCoequalizers ((polyFreeMonad X P).Algebra)` (from
   creation of preserved colimits)
4. `HasColimitsOfSize ((polyFreeMonad X P).Algebra)` (Linton)
5. `HasColimitsOfSize (PolyAlg P)` (transfer via `polyAlgMonadEquiv`)

### A: Mathlib Infrastructure

- `Mathlib.CategoryTheory.Limits.Shapes.Reflexive`:
  `IsReflexivePair`, `HasReflexiveCoequalizers`
- `Mathlib.CategoryTheory.Monad.Coequalizer`:
  `beckAlgebraCoequalizer`, `beckSplitCoequalizer`
- `Mathlib.CategoryTheory.Monad.Monadicity`: Beck's monadicity
  theorem uses reflexive coequalizers

### A: Proposals

**A1. `HasColimitsOfSize (PolyAlg P)`.** Prove cocompleteness of the
polynomial algebra category. The main work is showing the polynomial
endofunctor preserves filtered colimits.

**A2. Beck coequalizer instantiation.** Specialize
`beckAlgebraCoequalizer` to our polynomial free monad to get: for
any `alpha : PolyAlg P`, there is a reflexive coequalizer diagram
`F(F(U(alpha))) => F(U(alpha)) -> alpha` in `PolyAlg P`.

---

## B. The Algebra-Coalgebra-Presheaf Triangle

### B: References

- Adamek, "The intersection of algebra and coalgebra" (TCS 366,
  2006, pp. 82-97)
  - Full paper at `.claude/docs/intersection-algebra-coalgebra-equals-presheaves.pdf`
  - Conference version at `.claude/docs/algebra-intersect-coalgebra-equals-presheaves.pdf`
- Worrell, "A note on coalgebras and presheaves" (MSCS 2005)

### B: Mathematical Background

**Theorem (Adamek 5.2).** For a concrete category V over S-sorted
sets, the following are equivalent:

1. V is concretely equivalent both to a variety and to a covariety.
2. V is concretely equivalent to `Set^{A^op}` for a small category
   A with `S = obj A`.

The paper establishes three layers of results:

**Coalgebra side (Theorem 3.4).** For every signature Sigma, the
category of Sigma-coalgebras is concretely equivalent to the
presheaf category on the *tree category* `T_Sigma`:

> `Coalg H_Sigma ≃ Set^{T_Sigma^op}`

The tree category has Sigma-trees as objects and subtree inclusions
as morphisms. The equivalence functor sends a coalgebra `A` to the
presheaf `t ↦ h_A^{-1}(t)`, decomposing `A` into fibers over the
terminal coalgebra.

**Algebra side (Remark 4.2).** The presheaf category `Set^{A^op}` is
a variety of unary algebras: one unary operation per morphism of A,
with equations encoding identity and composition.

**Characterization (Theorem 3.9).** For a set functor H, `Coalg H`
is concretely equivalent to a presheaf category if and only if H
is a reduction of a polynomial functor (agrees with a polynomial
functor on all nonempty sets).

### B: Relation to Our Codebase

Our `PolyCofreeCat P` is the tree category `T_Sigma` (with the
convention that morphisms go from parent to child rather than child
to parent, so we get copresheaves rather than presheaves). The
objects are fiber+shape pairs (trees), and the morphisms are
depth+position pairs (subtree inclusions via `polyCofreeAnnotPos`).

Our `polyCoalgCopresheafEquiv` is the coalgebra-copresheaf
equivalence `PolyCoalg P ≌ (PolyCofreeCat P ⥤ Type u)`, which is
the covariant analogue of Adamek's Theorem 3.4.

### B: Proposals

**B1. Copresheaves as variety of unary algebras.** Show that
`(PolyCofreeCat P ⥤ Type u)` is equivalent to a variety of unary
algebras (one operation per morphism of the cofree category). This
completes the algebra side of the intersection theorem.

**B2. Fiber decomposition over terminal coalgebra.** Make explicit
that the copresheaf functor factors through the anamorphism to the
terminal coalgebra, giving the Adamek decomposition
`E(A)(t) = h_A^{-1}(t)`.

---

## C. Distributive Laws and Bialgebras

### C: References

- Turi and Plotkin, "Towards a mathematical operational semantics"
  (LICS 1997)
  - PDF at `.claude/docs/towards-mathematical-operational-semantics.pdf`
- Beck, "Distributive laws" (1969)

### C: Mathematical Background

**Distributive law.** Given a monad `T` and a comonad `D` on the
same category `C`, a distributive law is a natural transformation
`lambda : T . D => D . T` satisfying four coherence axioms:

1. `lambda . eta_D = D(eta)` (unit)
2. `lambda . mu_D = D(mu) . lambda_T . T(lambda)` (multiplication)
3. `T(epsilon) = epsilon_T . lambda` (counit)
4. `D(lambda) . lambda_D . T(delta) = delta_T . lambda` (comultiplication)

**Theorem (Turi-Plotkin 7.1).** The following are in bijection:

- Distributive laws `lambda : TD => DT`
- Liftings of T to D-coalgebras
- Liftings of D to T-algebras

**lambda-Bialgebras.** Given a distributive law lambda, a
lambda-bialgebra is a triple `(X, h : TX -> X, k : X -> DX)` where
`h` is a T-algebra, `k` is a D-coalgebra, and the pentagonal
compatibility law holds: `k . h = D(h) . lambda_X . T(k)`.

**Theorem (Turi-Plotkin 7.2, 7.3).** The category of
lambda-bialgebras has:

- An initial object (operational model): `F^lambda(0)`, the free
  bialgebra on the initial D-coalgebra
- A final object (denotational model): `G_lambda(1)`, the cofree
  bialgebra on the final T-algebra

The unique homomorphism from initial to final is *universal
semantics*: simultaneously initial algebra semantics and final
coalgebra semantics (Corollary 7.3). If B preserves weak pullbacks,
this semantics is fully abstract (Corollary 7.4) and bisimulation
is a congruence (Corollary 7.5).

### C: Mathlib Status

Mathlib has `Monad` and `Comonad` (`Monad.Basic`), and
`Monad.Algebra` and `Comonad.Coalgebra` (`Monad.Algebra`), but no
distributive law structure and no bialgebra structure. These would
be built from scratch.

### C: Proposals

**C1. Distributive law structure.** Define
`DistributiveLaw (T : Monad C) (D : Comonad C)` with the four
coherence axioms. This is the foundational structure.

**C2. lambda-Bialgebra category.** Given a distributive law, define
the category of lambda-bialgebras with the pentagonal compatibility
law. Construct the initial and final objects via the free/cofree
adjunctions.

**C3. Distributive law for poly free monad / cofree comonad.**
Construct the canonical distributive law
`lambda : polyFreeMonad X P . polyCofreeComonad X P =>
polyCofreeComonad X P . polyFreeMonad X P`
for our polynomial endofunctors. This gives every polynomial
endofunctor its canonical bialgebraic semantics.

---

## D. Interaction Laws ("Pattern Runs on Matter")

### D: References

- Libkind and Spivak, "Pattern runs on matter: The free monad monad
  as a module over the cofree comonad comonad" (arXiv:2404.16321v2,
  July 2024)
  - PDF at `.claude/docs/pattern-runs-on-matter-free-monad-cofree-comonad-polynomial-functors.pdf`

### D: Mathematical Background

The paper works in the category **Poly** of polynomial functors on
Set with two monoidal products: substitution `◁` (whose monoids
are monads) and the Dirichlet/parallel product `⊗` (pointwise).

**Free monad `m_p`.** For a kappa-small polynomial `p`, the free
monad is constructed by transfinite induction:

- `p_(0) = y` (identity)
- `p_(alpha+1) = y + p ◁ p_(alpha)`
- `p_(alpha) = colim_{alpha' < alpha} p_(alpha')` at limits

The inclusions are all cartesian. For finitary polynomials, the
construction stabilizes at omega.

**Cofree comonad `c_q`.** Constructed as a limit:

- `q^(0) = y`
- `q^(1+i) = y × (q ◁ q^(i))`
- `c_q = lim(... -> q^(2) -> q^(1) -> q^(0))`

Positions of `c_q` are possibly-infinite q-behavior trees.

**The interaction map (Proposition 3.3).** Natural transformations
`Xi_{p,q} : m_p ⊗ c_q -> m_{p ⊗ q}` pair a finite p-tree (from
the free monad, representing a program/pattern) with an infinite
q-tree (from the cofree comonad, representing an
environment/matter) to produce a finite (p⊗q)-tree (representing
the execution trace).

**Module structure (Theorem 3.4).** The free monad functor `m_-` is
a left module over the cofree comonad functor `c_-` via the
Dirichlet product, satisfying unit and associativity coherences.

### D: Relation to Our Codebase

Our `PolyFix P` corresponds to the positions of `m_p` (finite
P-trees), and our `PolyCofreeShape P` / `PolyCofix P` corresponds
to the positions of `c_p` (infinite P-trees). Our polynomial
composition infrastructure (`polyToOverComp`) handles the
substitution product. The Dirichlet product would be new.

### D: Proposals

**D1. Dirichlet/parallel product of polynomial endofunctors.** Define
`P ⊗ Q` for `P Q : PolyEndo X` where positions pair and directions
come from both.

**D2. Interaction map Xi.** Construct the map pairing free monad
elements with cofree comonad elements to produce execution traces.

**D3. Module structure.** Verify the unit and associativity
coherences for the module structure of `m_-` over `c_-`.

---

## E. Operational Semantics via Abstract GSOS

### E: References

- Turi and Plotkin, "Towards a mathematical operational semantics"
  (LICS 1997), Sections 1, 3, 5

### E: Mathematical Background

**Abstract GSOS rules.** A natural transformation
`rho : Sigma(Id × B) => B . T` where Sigma is the signature
endofunctor, B is the behavior endofunctor, and T is the free monad
on Sigma. The naturality condition accounts for syntactic
restrictions on meta-variables.

**Theorem 1.1.** There is a 1-1 correspondence between natural
transformations of type `Sigma(Id × B) => B . T` and image-finite
sets of GSOS rules for a signature Sigma.

**Operational monad (Proposition 5.1).** Given abstract rules rho,
the construction `k ↦ T_rho(k)` extends to a monad T_rho lifting T
to B-coalgebras. This uses structural recursion with accumulators
(Theorem 5.1).

**Structural recursion (Theorem 5.1).** For the free monad T on
Sigma over a cartesian category, given `f : X -> Y` and
`h : Sigma(TX × Y) -> Y`, there exists a unique `f^# : TX -> Y`
satisfying the structural recursion diagram. This generalizes
primitive recursion by allowing terms as parameters.

### E: Relation to Our Codebase

Our `polyFixFoldHom` is the catamorphism (fold) for the initial
algebra. The structural recursion with accumulators is an extension
that takes a product `TX × Y` rather than just `TX`. Our
`polyFixFold` could serve as the base for this extension.

### E: Proposals

**E1. Abstract GSOS rules.** Define the type of abstract GSOS rules
as natural transformations `rho : Sigma(Id × B) => B . T` for
given signature and behavior endofunctors.

**E2. Operational monad.** Construct the lifting of the syntax monad
to B-coalgebras via structural recursion with accumulators.

---

## F. Stone Topology and Second Topos

### F: References

- "Two topoi associated with polynomials" (notes from Spivak 2022
  lecture and "All Concepts are Cat" by Lynch, Shapiro, Spivak)
  - Markdown at `.claude/docs/two-topoi-associated-with-polynomials.md`

### F: Mathematical Background

Given a polynomial p, there are two topoi:

**First topos (copresheaf topos).** The copresheaf category
`Set^{C_p}` where `C_p` is the cofree category. Encodes
"combinatorial or algebraic aspects" of the polynomial. We have this
via `polyCoalgCopresheafEquiv`.

**Second topos (sheaf topos).** Constructed by:

1. The carrier `c_p(1)` of the cofree comonad (infinite p-trees)
   is given a topology whose basis of opens is determined by finite
   p-trees from `m_p(1)` (the initial algebra carrier).
2. Each finite tree t determines a basic open: the set of all
   infinite trees agreeing with t up to its leaves.
3. For finite polynomials, this is a Stone space (compact, totally
   disconnected, Hausdorff).
4. The sheaf topos `Sh(c_p(1))` encodes "dynamical or spatial
   aspects" of the polynomial.

### F: Relation to Our Codebase

We have `PolyFix P x` (finite trees) and `PolyCofreeShape P x`
(infinite trees). Mathlib has `TopologicalSpace` and
`Topology.Sheaves.Sheaf`.

### F: Proposals

**F1. Stone topology on M-types.** Define a `TopologicalSpace`
instance on `PolyCofreeShape P x` using finite tree approximations.

**F2. Stone space property.** For finite polynomials, prove
compactness, total disconnectedness, and the Hausdorff property.

**F3. Sheaf topos.** Construct `Sh(c_P(1))` and study its
relationship to the copresheaf topos.

---

## References

### Papers in `.claude/docs/`

- `intersection-algebra-coalgebra-equals-presheaves.pdf` -- Adamek,
  "The intersection of algebra and coalgebra" (TCS 2006)
- `algebra-intersect-coalgebra-equals-presheaves.pdf` -- Adamek,
  conference version (CALCO 2005)
- `pattern-runs-on-matter-free-monad-cofree-comonad-polynomial-functors.pdf`
  -- Libkind and Spivak (arXiv 2024)
- `towards-mathematical-operational-semantics.pdf` -- Turi and
  Plotkin (LICS 1997)
- `two-topoi-associated-with-polynomials.md` -- Notes from Spivak
  lecture / "All Concepts are Cat"

### External References

- [nLab: colimits in categories of algebras](https://ncatlab.org/nlab/show/colimits+in+categories+of+algebras)
- [nLab: reflexive coequalizer](https://ncatlab.org/nlab/show/reflexive+coequalizer)
- [nLab: sifted colimit](https://ncatlab.org/nlab/show/sifted+colimit)
- [nLab: finitary monad](https://ncatlab.org/nlab/show/finitary+monad)
- [nLab: polynomial monad](https://ncatlab.org/nlab/show/polynomial+monad)
- Borceux, *Handbook of Categorical Algebra* Vol. 2
- Barr and Wells, *Toposes, Triples, and Theories*
- Adamek and Rosicky, *Locally Presentable and Accessible Categories*
- Adamek, Rosicky, and Vitale, "What are sifted colimits?" (TAC 2010)

### Mathlib Modules

- `Mathlib.CategoryTheory.Monad.Basic` -- Monad, Comonad
- `Mathlib.CategoryTheory.Monad.Algebra` -- Monad.Algebra,
  Comonad.Coalgebra
- `Mathlib.CategoryTheory.Monad.Coequalizer` --
  `beckAlgebraCoequalizer`, `beckSplitCoequalizer`
- `Mathlib.CategoryTheory.Monad.Limits` -- `forgetCreatesLimits`,
  `hasLimits_of_reflective`
- `Mathlib.CategoryTheory.Monad.Monadicity` -- Beck's monadicity
  theorem
- `Mathlib.CategoryTheory.Limits.Shapes.Reflexive` --
  `IsReflexivePair`, `HasReflexiveCoequalizers`
- `Mathlib.CategoryTheory.Limits.Sifted` -- `IsSifted`
- `Mathlib.CategoryTheory.Adjunction.Limits` --
  `has_limits_of_equivalence`, `has_colimits_of_equivalence`
- `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic` --
  `functorCategoryHasLimitsOfSize`
- `Mathlib.CategoryTheory.Limits.Creates` --
  `hasLimits_of_hasLimits_createsLimits`

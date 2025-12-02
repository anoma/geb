# Characterizing Ends of Polynomial Profunctors

## Overview

This document summarizes a mathematical characterization of the **end** of a
specific polynomial profunctor, derived from work on PHOAS (Parametric
Higher-Order Abstract Syntax) representations. The characterization reveals
that elements of the end correspond to **closed term shapes with a selected
negative occurrence**, and we conjecture this pattern generalizes to a broad
class of polynomial profunctors.

## Background

### Profunctors

A **profunctor** $P : \mathcal{C}^{op} \times \mathcal{D} \to \mathbf{Set}$ is
a functor that is contravariant in its first argument and covariant in its
second. In programming terms, this means:

- The first parameter appears in **negative** (input) positions
- The second parameter appears in **positive** (output) positions

### Ends

The **end** of a profunctor $P : \mathcal{C}^{op} \times \mathcal{C} \to
\mathbf{Set}$ is:

$$\int_x P(x, x) = \left\{ e : \prod_{x \in \mathcal{C}} P(x, x) \;\middle|\;
\text{wedge condition} \right\}$$

The wedge condition requires that for any morphism $f : a \to b$:

$$P(f, \mathrm{id}_b) \circ e_b = P(\mathrm{id}_a, f) \circ e_a$$

Intuitively, an end element is a "polymorphic" element that behaves coherently
across all type instantiations.

### Connection to PHOAS

This work was motivated by Kmett's "PHOAS for Free" approach, where binding
structures are represented using profunctors. The end of such a profunctor
captures **closed terms** — terms with no free variables.

## The Specific Profunctor

### Definition

We study the profunctor $P : \mathbf{Set}^{op} \times \mathbf{Set} \to
\mathbf{Set}$ defined as the free monad:

$$P(x, y) = \mu t.\, (1 + (x \to t) \times t + y)$$

This arises from the base functor $F(x, t) = 1 + (x \to t) \times t$. Terms of
$P(x, y)$ are trees where:

- **Closed leaves**: The $1$ component — leaves carrying no data
- **Lambda nodes**: The $(x \to t) \times t$ component — nodes with a binding
  site for $x$ (contravariant through the function arrow) and a child subtree
- **Variable leaves**: The $y$ component — leaves carrying a value of type $y$
  (covariantly)

### Variance Structure

| Component | Type Parameter | Variance | Mechanism |
|-----------|----------------|----------|-----------|
| Lambda nodes | $x$ | Contravariant | Function domain |
| Variable leaves | $y$ | Covariant | Direct |
| Closed leaves | — | Constant | — |

## The Characterization Theorem

### Main Result

$$\int_x P(x, x) \;\cong\; \sum_{i \in \mathcal{I}}
\left( \mathrm{Closed}(i) \times \mathrm{Path}(i) \right)$$

Where:

- $\mathcal{I}$ = the type of **shapes** (tree structures, ignoring data)
- $\mathrm{Closed}(i)$ = a proof that shape $i$ has no variable leaves
- $\mathrm{Path}(i)$ = a path selecting one negative (contravariant) occurrence
  in $i$

### Interpretation

An element of the end consists of:

1. **A closed term shape** — a binary tree where all leaves are "closed"
   (no free variables in the positive/covariant sense)

2. **A selection of one negative occurrence** — a path through the tree
   pointing to one of the $x$-positions at internal nodes

### Why "Closed Terms with Focus"

This characterization says that polymorphic closed terms are essentially
**zippers** — a data structure together with a focus on one position. The
naturality (wedge) condition forces the "return value" of the polymorphic
term to come from exactly one of the negative positions.

## The Path Type

### Structure

For a shape $i$, the path type $\mathrm{Path}(i)$ is defined inductively:

```
Path(ClosedLeaf)     = Void        -- no path through a closed leaf
Path(VarLeaf)        = impossible  -- excluded by Closed(i) constraint
Path(Node(l, r))     = LeftChoice(l, r) × Path(r)
```

Where $\mathrm{LeftChoice}$ at a node specifies what happens in the left
subtree:

- **Forced**: Left subtree has no negative occurrences; must continue to right
- **Direct**: Left subtree has negative occurrences; select the one at this node
- **Recurse**: Left subtree has negative occurrences; continue into left with
  a sub-path

### The GADT Refinement

The choice type is a **GADT** that tracks whether
choices are meaningful:

```
data LeftChoice(hasPositions : Bool) where
  Forced  : LeftChoice False           -- no choice when empty
  Direct  : LeftChoice True            -- choose direct value
  Recurse : Path(left) -> LeftChoice True  -- choose to recurse
```

This refinement ensures the isomorphism is **strict** — each end element has
exactly one representation, with no quotient needed.

## Natural Transformations from Polynomial Functors

### Transformations to the identity

For a polynomial functor $Q(y) = \sum_{j \in J} (D_j \to y)$, natural
transformations to the identity functor are characterized by:

$$\mathrm{Nat}(Q, \mathrm{Id}) \;\cong\; \prod_{j \in J} D_j$$

Each natural transformation corresponds to choosing one "direction" for each
"position."

### Application to Our Profunctor

Given a closed shape $i$, the second component of an end element must be a
natural transformation:

$$\eta : \mathrm{DirPoly}_i \Rightarrow \mathrm{Id}$$

where $\mathrm{DirPoly}_i$ is the polynomial functor of "directions" determined
by $i$. By the lemma above, this is equivalent to choosing a direction — which
is precisely what our path type captures.

## Categorical Perspective

### Connection to Derivatives

The "direction type" at each position is analogous to the **derivative** of
the polynomial functor in the sense of container theory (Abbott-Altenkirch-
Ghani). A path through a term is like specifying "where to put the hole" in a
one-hole context.

### Connection to Linear Logic

The characterization has a linear logic flavor: exactly one negative occurrence
is "used" to produce the output. This connects to:

- **Focusing** in proof theory
- **Call-by-name** vs **call-by-value** evaluation strategies
- **Continuations** and their linear typing

### The End as a Representable

The end $\int_x P(x,x)$ can be viewed as:

$$\int_x P(x,x) \cong \mathrm{Nat}(\mathrm{Hom}(-,-), P)$$

Our characterization makes this concrete: natural transformations from the
hom-profunctor to $P$ are determined by closed shapes with focused negative
positions.

## Defining Polynomial Profunctors

### The Proposed Structure

A natural way to define "polynomial profunctor" uses the existing infrastructure
for polynomial functors and Dirichlet functors.

**Definition (Polynomial Profunctor):**
A *polynomial profunctor* $P : \mathbf{Set}^{op} \times \mathbf{Set} \to
\mathbf{Set}$ consists of:

1. A **positions type** $I$ (independent of $x$)

2. A **directions functor** $\mathrm{Dir} : \mathbf{Set} \to (I \to
   \mathbf{Set})$ that assigns to each position $i$ a direction type
   $\mathrm{Dir}(x, i)$ that is **covariant polynomial** in $x$

The profunctor is then:
$$P(x, y) = \sum_{i \in I} (\mathrm{Dir}(x, i) \to y)$$

The **contravariance in $x$ emerges from the function arrow**: $\mathrm{Dir}(x,
i)$ is covariant in $x$, but $\mathrm{Dir}(x, i) \to y$ is contravariant in $x$.

This matches the code structure exactly:

```idris
NegPosMaybePP : PolyPolyFunc
-- Positions: Fin 2 (constant)
-- Directions at FZ: Void
-- Directions at (FS FZ): x + 1 (covariant in x!)
```

The base functor interprets as:
$$F(x, y) = 1 + ((x + 1) \to y) = 1 + (x \to y) \times y$$

The $(x \to y)$ term is the PHOAS-style lambda abstraction.

### End Formula via Natural Transformations

For polynomial profunctors $P(x, y) = \sum_{i \in I} (\mathrm{Dir}(x, i) \to y)$:

$$\int_x P(x, x) = \sum_{i \in I} \int_x (\mathrm{Dir}(x, i) \to x)$$

The wedge condition for $f : a \to b$ requires:
$$f \circ h_a = h_b$$
where $h_x : \mathrm{Dir}(x, i) \to x$.

This says $h$ is a **natural transformation** from the functor $\mathrm{Dir}(-,
i)$ to the identity functor $\mathrm{Id}$.

**Key Lemma:** For a polynomial functor $Q(x) = \sum_{j \in J} (E_j \to x)$:
$$\mathrm{Nat}(Q, \mathrm{Id}) \cong \prod_{j \in J} E_j$$

Each natural transformation corresponds to choosing an element of each $E_j$.

**Theorem (End of Polynomial Profunctor):**
$$\int_x P(x, x) = \sum_{i \in I} \mathrm{Nat}(\mathrm{Dir}(-, i), \mathrm{Id})
\cong \sum_{i \in I} \prod_{j \in J_i} E_{i,j}$$

where $\mathrm{Dir}(x, i) = \sum_{j \in J_i} (E_{i,j} \to x)$.

### Application to Our Example

Our profunctor is the free monad:
$$P(x, y) = \mu t.\, (1 + (x \to t) \times t + y)$$

which comes from the base functor $F(x, y) = 1 + (x \to y) \times y$.

For the free monad, positions are **tree shapes** and directions at each shape
encode both $y$-leaves and $x$-binding sites. The direction functor
$\mathrm{Dir}(x, i)$ for a shape $i$ is:

$$\mathrm{Dir}(x, i) = V_i + (x \times N_i)$$

where $V_i$ = number of variable ($y$) leaves, $N_i$ = number of nodes.

The end formula becomes:
$$\int_x P(x, x) = \sum_{i : \text{shapes}} \mathrm{Nat}(\mathrm{Dir}(-, i),
\mathrm{Id})$$

For shapes with $V_i > 0$ (variable leaves), $\mathrm{Nat}(\mathrm{Dir}(-,i),
\mathrm{Id})$ is **empty** (no natural transformation from a constant functor).

For **closed shapes** ($V_i = 0$):
$$\mathrm{Dir}(x, i) = x \times N_i = x^{N_i}$$
$$\mathrm{Nat}(x^{N_i}, \mathrm{Id}) \cong N_i$$

This is exactly the **path type** — choosing one of the $N_i$ binding sites!

| Aspect | Formula |
|--------|---------|
| End | $\sum_{i : \text{closed shapes}} N_i$ |
| Closed shapes | Trees with no variable leaves |
| $N_i$ | Number of nodes = number of $x$-binding sites |
| Path | Selection of one binding site |

### Recursive Polynomial Profunctors

**Definition (Recursive Polynomial Profunctor):**
A *recursive polynomial profunctor* has the form:
$$P(x, y) = \mu t.\, (F(x, t) + y)$$

where $F(x, t)$ is a polynomial functor in $t$ whose coefficients depend on $x$
(making the result contravariant in $x$ through function arrows).

For our example:
$$F(x, t) = 1 + (x \to t) \times t$$

- The $1$ gives closed leaves
- The $(x \to t) \times t$ gives internal nodes with a lambda binding ($x$
  contravariant through the arrow) and a right child
- The free variable $y$ in the free monad gives variable leaves

### The General End Formula

**Theorem (End of Polynomial Profunctor, General Form):**
For $P(x, y) = \sum_{i \in I} (\mathrm{Dir}(x, i) \to y)$ where each
$\mathrm{Dir}(x, i)$ is a polynomial functor in $x$:

$$\int_x P(x, x) = \sum_{i \in I} \mathrm{Nat}(\mathrm{Dir}(-, i), \mathrm{Id})$$

For the recursive case $P(x, y) = \mu t.\, (F(x, t) + y)$:

$$\int_x P(x, x) = \sum_{i \in \mathrm{ClosedShapes}} \mathrm{Nat}(x^{N_i},
\mathrm{Id}) = \sum_{i \in \mathrm{ClosedShapes}} N_i$$

This is the **closed shapes × paths** characterization, now derived from the
general polynomial profunctor formula.

### Why This Works

The formula $\mathrm{Nat}(Q, \mathrm{Id})$ for
polynomial $Q$ gives:

1. **Empty** when $Q$ has any constant summands (like $V_i$ variable leaves)
2. **Product of exponents** when $Q = \sum_j (E_j \to x)$

For closed shapes ($V_i = 0$), $\mathrm{Dir}(x, i) = x^{N_i}$, so:
$$\mathrm{Nat}(x^{N_i}, \mathrm{Id}) = N_i$$

This is the type of **paths** — selections of one $x$-binding site from $N_i$
possibilities.

### Towards a General Definition

A fully general notion of "polynomial profunctor" might be:

**Definition (Polynomial Profunctor, General):**
A polynomial profunctor $P : \mathbf{Set}^{op} \times \mathbf{Set} \to
\mathbf{Set}$ is one that can be built from:

1. **Constants**: $P(x, y) = C$ for fixed $C$
2. **Contravariant representables**: $P(x, y) = x \to E$ for fixed $E$
3. **Covariant representables**: $P(x, y) = D \to y$ for fixed $D$
4. **Products**: $P_1 \times P_2$
5. **Coproducts**: $P_1 + P_2$
6. **Fixed points**: $\mu p.\, F(x, y, p)$ where $F$ is polynomial in all three
   arguments

The end formula would then be computed inductively:

| Constructor | End Formula |
|-------------|-------------|
| Constant $C$ | $C$ |
| $x \to E$ | (see interaction with other components) |
| $D \to y$ | (see interaction with other components) |
| $P_1 \times P_2$ | Computed from components + wedge |
| $P_1 + P_2$ | $\int P_1 + \int P_2$ |
| $\mu p.\, F$ | $\sum_{i \in \mathrm{Closed}} \mathrm{Path}(i)$ |

The tricky cases are products involving both contravariant and covariant
representables — these interact through the wedge condition.

## Generalization

### Conjectured General Pattern

The characterization should hold for profunctors of the form:

$$P(x, y) = \mu t.\, F(x, y, t)$$

where $F$ is a **polynomial trifunctor** built from constants, the parameters
$x$, $y$, $t$, and products/coproducts.

### General Theorem (Conjectured)

For any such polynomial profunctor:

$$\int_x P(x,x) \cong \sum_{i \in \mu s. F'(s)}
\mathrm{Nat}(\mathrm{Dir}_i, \mathrm{Id})$$

Where:

- $F'(s)$ is $F$ with $x$ and $y$ set to unit (just the shape functor)
- $\mathrm{Dir}_i$ is the polynomial functor of directions at shape $i$
- The sum ranges over closed shapes (where variable leaves don't occur)

### Conditions for the Pattern

1. **Polynomial structure**: $F$ must be polynomial (no exponentials)
2. **Well-founded recursion**: Initial algebra semantics (finite terms)
3. **Finite branching**: Each constructor has finitely many recursive positions

### Variations

| Variation | Effect on Characterization |
|-----------|---------------------------|
| Multiple negative occurrences per node | Paths must select among them |
| N-ary trees | Different branching in path type |
| Mutual recursion | System of interrelated ends |
| Coinductive (final coalgebra) | Open question — infinite paths? |

## Implementation Notes

### Idris2 Formalization

The characterization has been formalized in Idris2 in
`src/LanguageDef/Test/PolyDifuncTest.idr`. Components:

- `NegPosNatEndDirPath`: The path type
- `NpnpLeftChoice`: The GADT for left choices
- `closedPathToNatTrans`: Path → Natural transformation
- `natTransToPath`: Natural transformation → Path
- `NpnpIsClosed`: Predicate for closed shapes

## Open Questions

1. **Coalgebraic case**: Does a similar characterization hold for final
   coalgebras (infinite terms)? Would paths be infinite?

2. **Higher-order case**: What happens when $F$ includes exponentials
   (function types)?

3. **Coend characterization**: Can we similarly characterize $\int^x P(x,x)$?

4. **Computational content**: Is there a general algorithm for computing
   ends of polynomial profunctors, analogous to PRA functors?

5. **Dependently-typed generalization**: How does the characterization
   extend to polynomial functors on slice categories?

## References

- Kmett, E. "PHOAS for Free" (blog post)
- Abbott, M., Altenkirch, T., Ghani, N. "Containers: Constructing Strictly
  Positive Types"
- Gambino, N., Kock, J. "Polynomial Functors and Polynomial Monads"
- Spivak, D. "Polynomial Functors: A Mathematical Theory of Interaction"
- Hinze, R., Wu, N. "Unifying Structured Recursion Schemes"

## Summary

| Aspect | Result |
|--------|--------|
| **Object studied** | End of free monad on polynomial bifunctor |
| **Characterization** | Closed shapes × paths to negative occurrences |
| **Isomorphism type** | Strict (no quotient needed) |
| **Technique** | Nat trans from polynomials ≅ sections |
| **Generalization** | Conjectured for all polynomial profunctors |
| **Implementation** | Idris2 formalization |

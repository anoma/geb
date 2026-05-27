# Vene: Mendler-Style Inductive Types (Sections 5.3-5.7)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [5.3 Mendler-style inductive types: mixed variant case](#53-mendler-style-inductive-types-mixed-variant-case)
  - [Definition 5.6 (Mendler-style algebra for a difunctor)](#definition-56-mendler-style-algebra-for-a-difunctor)
  - [Definition 5.7 (Malgebra homomorphism)](#definition-57-malgebra-homomorphism)
  - [Definition 5.8 (Initial malgebra)](#definition-58-initial-malgebra)
  - [Corollary 5.11 (Laws for initial G-malgebra)](#corollary-511-laws-for-initial-g-malgebra)
- [5.4 Restricted existential types](#54-restricted-existential-types)
  - [Definition 5.9 (Restricted cowedge)](#definition-59-restricted-cowedge)
  - [Definition 5.10 (Restricted cowedge homomorphism)](#definition-510-restricted-cowedge-homomorphism)
  - [Definition 5.11 (Restricted coend)](#definition-511-restricted-coend)
  - [Corollary 5.12 (Laws for restricted coends)](#corollary-512-laws-for-restricted-coends)
  - [Example 5.3 (Coends)](#example-53-coends)
- [5.5 Mendler-style inductive types reduced to conventional inductive types](#55-mendler-style-inductive-types-reduced-to-conventional-inductive-types)
  - [The functor G^e](#the-functor-g%5Ee)
  - [Definition 5.12 (Floor translation)](#definition-512-floor-translation)
  - [Definition 5.13 (Ceiling translation)](#definition-513-ceiling-translation)
  - [Proposition 5.13](#proposition-513)
  - [Proposition 5.14](#proposition-514)
  - [Proposition 5.15](#proposition-515)
  - [Proposition 5.16](#proposition-516)
  - [Proposition 5.17](#proposition-517)
  - [Proposition 5.18](#proposition-518)
  - [Theorem 5.19](#theorem-519)
  - [Corollary 5.20](#corollary-520)
  - [Corollary 5.21](#corollary-521)
- [5.6 Mendler-style inductive types in Haskell](#56-mendler-style-inductive-types-in-haskell)
  - [Restricted coends in Haskell](#restricted-coends-in-haskell)
  - [The G^e functor](#the-g%5Ee-functor)
  - [Mendler-style inductive types](#mendler-style-inductive-types)
- [5.7 Related work](#57-related-work)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Summary of sections 5.3-5.7 from Varmo Vene's thesis "Categorical Programming
with Inductive and Coinductive Types" (2000).

## 5.3 Mendler-style inductive types: mixed variant case

Mendler-style inductive types generalize from covariant base functors
F : C -> C to **mixed variant functors** (difunctors) G : C^op x C -> C.

The covariant case is a degenerate case: for any F : C -> C, we can define
F' : C^op x C -> C by F'(Y, X) = F(X), padding F with a "dummy" contravariant
argument.

### Definition 5.6 (Mendler-style algebra for a difunctor)

Let G : C^op x C -> C be an endodifunctor. A **Mendler-style G-algebra** (or
**G-malgebra**) is a pair (C, Phi) where:

- C is an object of C
- Phi : Id^i/C -> G/C is a dinatural transformation

Here Id^i/C is the identity profunctor restricted to C, and G/C is the
slice profunctor. Concretely, Phi is a family {Phi_A}_{A in C} of functions:

```text
Phi_A : C(A, C) -> C(G(A, A), C)
```

satisfying the **dinaturality condition**: for any g : A -> B and
beta : B -> C, alpha : A -> C with alpha = beta . g:

```text
Phi_A(beta . g) . G(g, id_A) = Phi_B(beta) . G(id_B, g)     (equation 5.6)
```

Diagrammatically, for any triangle (g, alpha, beta) with alpha = beta . g:

```text
        G(B, A)
       /       \
G(g,id_A)     G(id_B,g)
     /           \
G(A,A)          G(B,B)
    \            /
  Phi_A(alpha) Phi_B(beta)
      \        /
         C
```

When the contravariant argument is "dummy" (G(X,Y) = F(Y) for some F),
dinaturality reduces to the naturality condition of Definition 5.1.

### Definition 5.7 (Malgebra homomorphism)

A **homomorphism** from G-malgebra (C, Phi) to (D, Psi) is an arrow
h : C -> D such that for any object A and arrow gamma : A -> C:

```text
h . Phi_A(gamma) = Psi_A(h . gamma)     (equation 5.7)
```

G-malgebras and their homomorphisms form a category Alg(G)^m.

### Definition 5.8 (Initial malgebra)

A Mendler-style G-algebra (mu^m G, in^m) is the **initial G-malgebra** if for
any G-malgebra (C, Phi) there exists a unique arrow (| Phi |)^m : mu^m G -> C
satisfying:

```text
f . in^m_{mu^m G}(id) = Phi(f)   iff   f = (| Phi |)^m     (cataM-CHARN)
```

The initial malgebra (mu^m G, in^m) is an initial object in Alg(G)^m.

### Corollary 5.11 (Laws for initial G-malgebra)

Let (mu^m G, in^m) be an initial G-malgebra.

- **Cancellation**: (| Phi |)^m . in^m_{mu^m G}(id) = Phi_{mu^m G}((| Phi |)^m)
- **Reflection**: id = (| in^m |)^m
- **Fusion**: f . Phi_C(id) = Psi_C(f) implies f . (| Phi |)^m = (| Psi |)^m

## 5.4 Restricted existential types

Reducing Mendler-style inductive types to conventional inductive types
requires certain restricted existential types (restricted coends).

### Definition 5.9 (Restricted cowedge)

Let G : C^op x C -> C be an endodifunctor and H : C^op x C -> Set a difunctor
to Set. An **H-restricted G-cowedge** (cowedge from G) is a pair (C, Phi)
consisting of:

- An object C of C
- A dinatural transformation Phi from H to G/C

Concretely, Phi is a family {Phi_A}_{A in C} of functions:

```text
Phi_A : H(A, A) -> C(G(A, A), C)
```

satisfying: for any g : A -> B and x in H(B, A):

```text
Phi_A(H(g, id_A)(x)) . G(g, id_A) = Phi_B(H(id_B, g)(x)) . G(id_B, g)
```

### Definition 5.10 (Restricted cowedge homomorphism)

An **H-restricted G-cowedge homomorphism** between (C, Phi) and (D, Psi) is
an arrow h : C -> D such that for any A and a in H(A, A):

```text
h . Phi_A(a) = Psi_A(a)
```

H-restricted G-cowedges and homomorphisms form a category Cow_G^H.

### Definition 5.11 (Restricted coend)

An H-restricted G-cowedge (Sigma(H, G), inj_G^H) is an **H-restricted G-coend**
if it is an initial object of Cow_G^H. For any H-restricted G-cowedge (C, Phi)
there exists a unique f = [ Phi ]_G^H : Sigma(H, G) -> C satisfying:

```text
for all A, a in H(A,A): f . (inj_G^H)_A(a) = Phi_A(a)     (case-CHARN)
```

### Corollary 5.12 (Laws for restricted coends)

Let (Sigma(H, G), inj_G^H) be an H-restricted G-coend.

- **Cancellation**: [ Phi ]_G^H . (inj_G^H)_A(a) = Phi_A(a)
- **Reflection**: id_{Sigma(H,G)} = [ inj_G^H ]_G^H
- **Fusion**: (forall A, a. h . Phi_A(a) = Psi_A(a)) implies
  h . [ Phi ]_G^H = [ Psi ]_G^H

### Example 5.3 (Coends)

When H = 1 (constant functor to singleton set), a 1-restricted G-cowedge
(C, Phi) is a **cowedge of G** in the ordinary sense: Phi is a dinatural
transformation from G to the constant functor C.

A 1-restricted G-coend is the **coend of G**, written integral^c G(c, c).

## 5.5 Mendler-style inductive types reduced to conventional inductive types

Given existence of certain restricted coends, Mendler-style inductive types
reduce to conventional inductive types.

Let G : C^op x C -> C be an endodifunctor. Assume for any object C of C,
there exists an Id^i/C-restricted G-coend (Sigma(Id^i/C, G), inj_G^{Id^i/C}).

### The functor G^e

Define an endofunctor **G^e** on C:

```text
G^e(C) = Sigma(Id^i/C, G)
G^e(h : C -> D) =
  [ lambda A, gamma : A -> C. (inj_G^{Id^i/D})_A(h . gamma) ]_G^{Id^i/C}
```

G^e is functorial (proof follows from restricted coend properties).

### Definition 5.12 (Floor translation)

Given a Mendler-style G-algebra (C, Phi), define the **conventional G^e-algebra**:

```text
floor(Phi) = [ Phi ]_G^{Id^i/C} : G^e(C) -> C
```

### Definition 5.13 (Ceiling translation)

Given a conventional G^e-algebra (C, phi), define the **Mendler-style G-algebra**:

```text
ceil(phi)_A(gamma : A -> C) = phi . (inj_G^{Id^i/C})_A(gamma)
```

### Proposition 5.13

If (C, phi) is a conventional G^e-algebra, then (C, ceil(phi)) is a
Mendler-style G-algebra.

*Proof*: Must verify ceil(phi) is dinatural. For g : A -> B and beta : B -> C:

```text
ceil(phi)_A(beta . g) . G(g, id_A)
= phi . (inj_G^{Id^i/C})_A(beta . g) . G(g, id_A)
= phi . (inj_G^{Id^i/C})_B(beta) . G(id_B, g)     [by inj dinaturality]
= ceil(phi)_B(beta) . G(id_B, g)
```

### Proposition 5.14

If (C, Phi) is a Mendler-style G-algebra, then (C, floor(Phi)) is a
conventional G^e-algebra.

*Proof*: Trivial (floor(Phi) is just a morphism G^e(C) -> C).

### Proposition 5.15

If (C, phi) is a conventional G^e-algebra, then floor(ceil(phi)) = phi.

*Proof*:

```text
floor(ceil(phi))
= [ ceil(phi) ]_G^{Id^i/C}
= [ lambda A, gamma. phi . (inj_G)_A(gamma) ]_G^{Id^i/C}
= phi . [ inj_G ]_G^{Id^i/C}     [case fusion]
= phi                            [case reflection]
```

### Proposition 5.16

If (C, Phi) is a Mendler-style G-algebra, then ceil(floor(Phi)) = Phi.

*Proof*: For any A and gamma : A -> C:

```text
ceil(floor(Phi))_A(gamma)
= floor(Phi) . (inj_G)_A(gamma)
= [ Phi ]_G . (inj_G)_A(gamma)
= Phi_A(gamma)                   [case cancellation]
```

### Proposition 5.17

If h is a conventional G^e-algebra homomorphism between (C, phi) and (D, psi),
then h is also a Mendler-style G-algebra homomorphism between
(C, ceil(phi)) and (D, ceil(psi)).

*Proof*: For any A and gamma : A -> C:

```text
h . ceil(phi)_A(gamma)
= h . phi . (inj_G^{Id^i/C})_A(gamma)
= psi . G^e(h) . (inj_G^{Id^i/C})_A(gamma)     [h is G^e-alg hom]
= psi . (inj_G^{Id^i/D})_A(h . gamma)          [G^e definition]
= ceil(psi)_A(h . gamma)
```

### Proposition 5.18

If h is a Mendler-style G-algebra homomorphism between (C, Phi) and (D, Psi),
then h is also a conventional G^e-algebra homomorphism between
(C, floor(Phi)) and (D, floor(Psi)).

*Proof*: Need h . floor(Phi) = floor(Psi) . G^e(h).

```text
h . floor(Phi)
= h . [ Phi ]_G^{Id^i/C}
= [ lambda A, gamma. h . Phi_A(gamma) ]_G^{Id^i/C}   [A := A, gamma := gamma]
= [ lambda A, gamma. Psi_A(h . gamma) ]_G^{Id^i/C}   [h is malgebra hom]
= [ Psi ]_G^{Id^i/D} . G^e(h)                        [case fusion + G^e def]
= floor(Psi) . G^e(h)
```

### Theorem 5.19

The categories Alg(G^e) and Alg(G)^m are isomorphic.

### Corollary 5.20

If (mu G^e, in) is an initial (conventional) G^e-algebra, then
(mu G^e, ceil(in)) is an initial G-malgebra. For any G-malgebra (C, Phi),
the catamorphism (| floor(Phi) |) : mu G^e -> C is the unique homomorphism
from (mu G^e, in) to (C, Phi).

### Corollary 5.21

If (mu^m G, in^m) is an initial Mendler-style G-algebra, then
(mu^m G, floor(in^m)) is an initial conventional G^e-algebra. For any
conventional G^e-algebra (C, phi), the Mendler-style catamorphism
(| ceil(phi) |)^m : mu^m G -> C is the unique conventional homomorphism
from (mu^m G, in^m) to (C, phi).

## 5.6 Mendler-style inductive types in Haskell

Mendler-style inductive types can be modeled in Haskell using existential
types and rank-2 type signatures.

### Restricted coends in Haskell

```haskell
data RCoEnd h g = forall a. InjRCE (h a) (g a)

caseRCE :: (forall a. h a -> g a -> c) -> RCoEnd h g -> c
caseRCE phi (InjRCE ha ga) = phi ha ga
```

### The G^e functor

```haskell
newtype Fun c a = Fun (a -> c)
newtype Ext g c = Ext (RCoEnd (Fun c) g)

injExt :: (a -> c) -> g a -> Ext g c
injExt h x = Ext (InjRCE (Fun h) x)

caseExt :: (forall a. (a -> c) -> g a -> d) -> Ext g c -> d
caseExt phi (Ext (InjRCE (Fun h) x)) = phi h x

instance Functor (Ext g) where
  fmap f = caseExt (\h -> injExt (f . h))
```

### Mendler-style inductive types

```haskell
type MuM g = Mu (Ext g)

inM :: (a -> MuM g) -> g a -> MuM g
inM h x = In (injExt h x)

cataM :: (forall a. (a -> c) -> g a -> c) -> MuM g -> c
cataM phi = cata (caseExt phi)
```

## 5.7 Related work

The concept of Mendler-style inductive type comes from N. P. Mendler's work
on an extension of system F (2nd-order simply-typed lambda-calculus) with
inductive and coinductive types. This system supported iteration and
coiteration through unusual operators whose beta-reduction rules did not
mention the arrow mapping component of the base functor of the (co)inductive
type.

In [UV97, UV00b, Uus98, Mat98, Mat00], it was observed that the system does
not lose any desirable meta-theoretic properties if the base functor is
permitted to be non-covariant. It was also shown how to interpret the
liberalized system in lattice theory (mu F is not necessarily a (pre-)fixed
point of F if F is non-monotonic).

The category-theoretic account given here is a "glorification" of the
lattice-theoretic semantics.

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Restricted Coends in Categorical Programming](#restricted-coends-in-categorical-programming)
  - [1. Formal Definition of a Restricted Cowedge](#1-formal-definition-of-a-restricted-cowedge)
  - [2. Formal Definition of a Restricted Coend](#2-formal-definition-of-a-restricted-coend)
  - [3. Calculational Laws](#3-calculational-laws)
  - [4. Relationship to Ordinary Coends](#4-relationship-to-ordinary-coends)
  - [5. Implementation in Functional Programming](#5-implementation-in-functional-programming)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Restricted Coends in Categorical Programming

Based on **Varmo Vene's thesis** (2000), the concept of a **restricted
coend** is developed as a tool for handling **inductive and coinductive
types**, particularly in the context of **Mendler-style recursion**.

## 1. Formal Definition of a Restricted Cowedge

Before defining the restricted coend, Vene identifies the **restricted
cowedge** as the underlying structure.

**Definition 5.9 (Restricted Cowedge):**
Let $G : \mathcal{C}^{\text{op}} \times \mathcal{C} \to \mathcal{C}$ be an
**endodifunctor** and
$H : \mathcal{C}^{\text{op}} \times \mathcal{C} \to \text{Set}$ a
**difunctor to Set**. An **$H$-restricted $G$-cowedge** (or cowedge from
$G$) is a pair $(C, \Phi)$ consisting of:

* An object $C$ of $\mathcal{C}$ (the carrier/summit).
* A **dinatural transformation** $\Phi$ between the difunctors $H$ and
  $G/C$.

This $\Phi$ is defined as a family of functions $\{\Phi_A\}_{A \in
\mathcal{C}}$ between the sets $H(A, A)$ and $\mathcal{C}(G(A, A), C)$
such that for any arrow $g : A \to B$, the following diagram commutes:

$$
\begin{CD}
H(B, A) @>{H(g, \text{id}_A)}>> H(A, A) @>{\Phi_A}>> \mathcal{C}(G(A, A), C) \\
@V{H(\text{id}_B, g)}VV @. @VV{\text{pre-comp by } G(g, \text{id}_A)}V \\
H(B, B) @>{\Phi_B}>> \mathcal{C}(G(B, B), C)
  @>{\text{pre-comp by } G(\text{id}_B, g)}>> \mathcal{C}(G(B, A), C)
\end{CD}
$$

**Restricted Cowedge Homomorphism:**

An **$H$-restricted $G$-cowedge homomorphism** between two $H$-restricted
$G$-cowedges $(C, \Phi)$ and $(D, \Psi)$ is an arrow $h : C \to D$ of
$\mathcal{C}$ with the property that, for any object $A$ of $\mathcal{C}$,
the following diagram commutes in $\text{Set}$:

$$
\begin{CD}
H(A, A) @>{\Phi_A}>> \mathcal{C}(G(A, A), C) \\
@| @VV{\mathcal{C}(G(A, A), h)}V \\
H(A, A) @>{\Psi_A}>> \mathcal{C}(G(A, A), D)
\end{CD}
$$

In the above diagram, the vertical arrow $\mathcal{C}(G(A, A), h)$ represents
**post-composition** by $h$ (mapping $f \mapsto h \circ f$).

**Equivalent Pointwise Condition:**
The condition for the homomorphism can be expressed more simply in terms of
the elements of the sets involved. An arrow $h$ is a homomorphism if, for
any object $A$ of $\mathcal{C}$ and any element $a \in H(A, A)$, the
following holds in $\mathcal{C}$:

$$h \circ \Phi_A(a) = \Psi_A(a)$$

This equality is represented by the following commuting diagram in the base
category $\mathcal{C}$:

$$
\begin{CD}
G(A, A) @>{\Phi_A(a)}>> C \\
@V{\Psi_A(a)}VV @VV{h}V \\
D @= D
\end{CD}
$$

**Formation of a Category:**

With these definitions established, the collection of $H$-restricted
$G$-cowedges and the homomorphisms between them form the category
**$\text{Cow}_G^H$**:

* **Identities:** The identity morphism for an object $(C, \Phi)$ is the
  identity arrow $\text{id}_C$ of the base category.
* **Composition:** Composition of homomorphisms is inherited from the
  composition of arrows in the base category $\mathcal{C}$.

---

## 2. Formal Definition of a Restricted Coend

The **restricted coend** is characterised by its **universal property**
as the initial object in the category of restricted cowedges.

**Definition 5.11 (Restricted Coend):**
An $H$-restricted $G$-cowedge $(\Sigma(H, G), \text{inj}_G^H)$ is an
**$H$-restricted $G$-coend** if it is an **initial object** of
$\text{Cow}_G^H$.

This means that for any other $H$-restricted $G$-cowedge $(C, \Phi)$,
there exists a **unique arrow** $f = [\Phi]_G^H : \Sigma(H, G) \to C$
satisfying the universal property:

$$
(\forall A, a \in H(A, A) \cdot f \circ (\text{inj}_G^H)_A(a) =
\Phi_A(a)) \equiv f = [\Phi]_G^H
$$

---

## 3. Calculational Laws

The restricted coend satisfies three fundamental laws derived from its
initiality:

* **Cancellation:** For any $H$-restricted $G$-cowedge $(C, \Phi)$:
  $$\forall A, a \in H(A, A) \cdot [\Phi]_G^H \circ
  (\text{inj}_G^H)_A(a) = \Phi_A(a)$$
* **Reflection:**
  $$\text{id}_{\Sigma(H, G)} = [\text{inj}_G^H]_G^H$$
* **Fusion:** For any $H$-restricted $G$-cowedges $(C, \Phi)$ and
  $(D, \Psi)$ and an arrow $h : C \to D$:
  $$(\forall A, a \in H(A, A) \cdot h \circ \Phi_A(a) = \Psi_A(a))
  \implies h \circ [\Phi]_G^H = [\Psi]_G^H$$

---

## 4. Relationship to Ordinary Coends

Vene explains that **ordinary coends** are a special case of this
construction.

* If $H$ is the **constant terminal functor** $1$ (which sends everything
  to a singleton set), a **1-restricted $G$-cowedge** is exactly a family
  of arrows $\Phi_A : G(A, A) \to C$ that makes the standard coend
  diagram commute.
* Consequently, the **1-restricted $G$-coend** is isomorphic to the
  **ordinary coend** $\int^A G(A, A)$.

---

## 5. Implementation in Functional Programming

In **Haskell**, restricted coends are implemented using **existential
quantification** to hide the index type $a$.

```haskell
-- Formal representation of a Restricted Coend
data RCoEnd h g = forall a . InjRCE (h a) (g a)

-- The universal cowedge homomorphism (the case operator)
caseRCE :: (forall a . h a -> g a -> d) -> RCoEnd h g -> d
caseRCE phi (InjRCE x y) = phi x y
```

Vene further refines this to define **existential types** used for
Mendler-style induction:

```haskell
newtype Fun c a = Fun (a -> c)
newtype Ext g c = Ext (RCoEnd (Fun c) g)

injExt :: (a -> c) -> g a -> Ext g c
injExt h x = Ext (InjRCE (Fun h) x)
```

This allows the construction of **least fixed points** for functors of
mixed variance.

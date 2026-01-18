# Wedges and cones via the twisted-arrow category

This note spells out, componentwise and symbolically, the correspondence between:

- wedges for a profunctor P : Cᵒᵖ × C → Set and cones for the derived
  functor P′ : Tw(C) → Set, and

- cowedges for P and cocones for the derived functor
  P″ : Tw(Cᵒᵖ)ᵒᵖ → Set.

---

## 1. Conventions for a profunctor

Let P : Cᵒᵖ × C → Set.

For u : c → c′ in C (so u is in the first, contravariant slot) and
v : d → d′ in C (second, covariant slot), functoriality gives a function:

```text
P(u, v) : P(c′, d) → P(c, d′).
```

In particular:

```text
P(u, 1) : P(c′, d) → P(c, d)
P(1, v) : P(c, d) → P(c, d′).
```

---

## 2. The twisted-arrow category Tw(C) and the forgetful functor π

A concrete presentation of Tw(C):

### 2.1 Objects

An object of Tw(C) is an arrow f : c → d in C.

We will write it simply as f : c → d.

### 2.2 Morphisms

A morphism in Tw(C):

```text
(u, v) : (f : c → d) → (g : c′ → d′)
```

is a pair of arrows in C:

```text
u : c′ → c
v : d → d′
```

such that:

```text
v ∘ f ∘ u = g.
```

So the domain component goes "backwards" (c′ → c), while the codomain
component goes "forwards" (d → d′).

### 2.3 The forgetful functor

Define:

```text
π : Tw(C) → Cᵒᵖ × C
```

by:

- on objects: π(f : c → d) = (c, d)

- on morphisms: for (u, v) as above,

```text
π(u, v) = (uᵒᵖ, v) : (c, d) → (c′, d′).
```

---

## 3. Wedges for P and cones for P′ = P ∘ π

Define the derived functor:

```text
P′ = P ∘ π : Tw(C) → Set.
```

Then:

- on an object f : c → d,

```text
P′(f) = P(c, d)
```

- on a morphism (u, v) : f → g (with u : c′ → c and v : d → d′),

```text
P′(u, v) = P(u, v) : P(c, d) → P(c′, d′).
```

---

## 4. Wedges for P

A wedge for P with apex X ∈ Set is:

- a family of functions

```text
ω_c : X → P(c, c)    (for each object c of C)
```

- such that for every arrow f : c → d in C, the wedge (dinaturality) equation holds:

```text
P(1, f) ∘ ω_c = P(f, 1) ∘ ω_d : X → P(c, d).
```

A morphism of wedges (X, ω) → (Y, ω′) is a function h : X → Y such that:

```text
ω′_c ∘ h = ω_c    for all objects c.
```

Let Wdg(P) denote the category of wedges for P.

---

## 5. Cones for P′

A cone on P′ with apex X is a natural transformation:

```text
λ : ΔX ⇒ P′
```

where ΔX : Tw(C) → Set is the constant functor at X.

Concretely, it is:

- a family of functions, one for each arrow f : c → d in C,

```text
λ_f : X → P′(f) = P(c, d)
```

- such that for every morphism (u, v) : f → g in Tw(C),

```text
P′(u, v) ∘ λ_f = λ_g.
```

Unpacking P′(u, v) = P(u, v), the condition is:

```text
P(u, v) ∘ λ_f = λ_g.
```

A morphism of cones (X, λ) → (Y, λ′) is a function h : X → Y such that:

```text
λ′_f ∘ h = λ_f    for all objects f of Tw(C).
```

Let Cone(P′) denote the category of cones on P′.

---

## 6. From a wedge to a cone

Given a wedge (X, ω), define a cone (X, λ) on P′ by setting, for each
arrow f : c → d:

```text
λ_f = P(f, 1) ∘ ω_d : X → P(c, d).
```

Equivalently, by the wedge equation, one can also write:

```text
λ_f = P(1, f) ∘ ω_c.
```

### 6.1 Naturality in Tw(C)

Let (u, v) : f → g in Tw(C), so u : c′ → c and v : d → d′ with v ∘ f ∘ u = g.

We check the cone condition:

```text
P(u, v) ∘ λ_f = λ_g.
```

Compute:

```text
P(u, v) ∘ λ_f
= P(u, v) ∘ P(f, 1) ∘ ω_d
= P(f ∘ u, v) ∘ ω_d
```

(using functoriality of P in the product category).

Now apply the wedge equation to v : d → d′:

```text
P(1, v) ∘ ω_d = P(v, 1) ∘ ω_{d′}.
```

Postcompose both sides with P(f ∘ u, 1) to get:

```text
P(f ∘ u, v) ∘ ω_d = P(v ∘ f ∘ u, 1) ∘ ω_{d′}.
```

Since v ∘ f ∘ u = g, the right-hand side is:

```text
P(g, 1) ∘ ω_{d′} = λ_g.
```

So naturality holds.

### 6.2 On morphisms

If h : (X, ω) → (Y, ω′) is a morphism of wedges, then the same function
h : X → Y is a morphism of cones because:

```text
λ′_f ∘ h
= (P(f, 1) ∘ ω′_d) ∘ h
= P(f, 1) ∘ (ω′_d ∘ h)
= P(f, 1) ∘ ω_d
= λ_f.
```

Thus we obtain a functor:

```text
F : Wdg(P) → Cone(P′).
```

---

## 7. From a cone to a wedge

Given a cone (X, λ) on P′, define a wedge (X, ω) by restricting to identities:

```text
ω_c = λ_{1_c} : X → P(c, c).
```

### 7.1 The wedge equation from cone naturality

Fix f : c → d in C.

There are canonical morphisms in Tw(C):

1. (1_c, f) : (1_c : c → c) → (f : c → d)

because:

```text
f ∘ 1_c ∘ 1_c = f.
```

- (f, 1_d) : (1_d : d → d) → (f : c → d)

because in Tw(C) the domain component goes backwards, so for a map into f
we need u : c → d, and we may take u = f and v = 1_d, giving:

```text
1_d ∘ 1_d ∘ f = f.
```

Apply cone naturality to these:

- along (1_c, f):

```text
λ_f = P(1, f) ∘ λ_{1_c} = P(1, f) ∘ ω_c
```

- along (f, 1_d):

```text
λ_f = P(f, 1) ∘ λ_{1_d} = P(f, 1) ∘ ω_d
```

Equating the two expressions for λ_f yields exactly the wedge equation:

```text
P(1, f) ∘ ω_c = P(f, 1) ∘ ω_d.
```

### 7.2 On morphisms

If h : (X, λ) → (Y, λ′) is a morphism of cones, then:

```text
ω′_c ∘ h
= λ′_{1_c} ∘ h
= λ_{1_c}
= ω_c,
```

so h is a morphism of wedges.

Thus we obtain a functor:

```text
G : Cone(P′) → Wdg(P).
```

---

## 8. They are inverse on the nose

### 8.1 G ∘ F = id on Wdg(P)

Start with a wedge (X, ω), build λ via:

```text
λ_f = P(f, 1) ∘ ω_d.
```

Then restrict back:

```text
(GF)(ω)_c = λ_{1_c} = P(1_c, 1) ∘ ω_c = ω_c.
```

### 8.2 F ∘ G = id on Cone(P′)

Start with a cone (X, λ), restrict to ω_c = λ_{1_c}, then rebuild:

```text
(FG)(λ)_f = P(f, 1) ∘ ω_d = P(f, 1) ∘ λ_{1_d}.
```

But cone naturality along (f, 1_d) : (1_d) → f already implies:

```text
λ_f = P(f, 1) ∘ λ_{1_d}.
```

So (FG)(λ)_f = λ_f for all f.

Therefore Wdg(P) and Cone(P′) are isomorphic categories (with these explicit constructions).

---

## 9. Dual: cowedges for P and cocones for P″ : Tw(Cᵒᵖ)ᵒᵖ → Set

This section is the dual correspondence, arranged so that the component
equations match the naturality equations for a cocone.

### 9.1 Cowedges for P

A cowedge for P with apex X is:

- a family of functions

```text
β_c : P(c, c) → X
```

- such that for every arrow f : c → d in C, the cowedge (dinaturality) equation holds:

```text
β_d ∘ P(1, f) = β_c ∘ P(f, 1) : P(d, c) → X.
```

A morphism of cowedges (X, β) → (Y, β′) is a function h : X → Y such that:

```text
h ∘ β_c = β′_c    for all objects c.
```

Let CoWdg(P) denote the category of cowedges for P.

### 9.2 The diagram P″

Define:

```text
P″ : Tw(Cᵒᵖ)ᵒᵖ → Set
```

so that:

- objects can be identified with arrows f : c → d in C

- on such an object, set:

```text
P″(f : c → d) = P(d, c).
```

On morphisms, one can unpack Tw(Cᵒᵖ)ᵒᵖ so that a morphism:

```text
(u, v) : (f : c → d) → (g : c′ → d′)
```

corresponds to arrows in C:

```text
u : c → c′
v : d′ → d
```

satisfying:

```text
v ∘ g ∘ u = f.
```

Then:

```text
P″(u, v) = P(v, u) : P(d, c) → P(d′, c′).
```

(Here the pair (v, u) appears because P is contravariant in the first slot
and covariant in the second slot, and P″ is arranged to land on P(d, c).)

### 9.3 Cocones for P″

A cocone on P″ with apex X is a natural transformation:

```text
μ : P″ ⇒ ΔX
```

i.e. functions:

```text
μ_f : P″(f) = P(d, c) → X
```

natural in f with respect to morphisms in Tw(Cᵒᵖ)ᵒᵖ.

Let Cocone(P″) denote the category of cocones on P″.

---

## 10. Cowedge ↔ cocone (explicitly)

### 10.1 From a cowedge to a cocone

Given a cowedge (X, β), define a cocone (X, μ) by:

```text
μ_{(f : c → d)} = β_c ∘ P(1, f) : P(d, c) → X.
```

Equivalently (by the cowedge equation), also:

```text
μ_{(f : c → d)} = β_d ∘ P(f, 1) : P(d, c) → X.
```

Naturality in Tw(Cᵒᵖ)ᵒᵖ follows by a calculation dual to the wedge-to-cone
case, using functoriality of P together with the cowedge dinaturality
equation.

This gives a functor:

```text
Fᵈ : CoWdg(P) → Cocone(P″).
```

### 10.2 From a cocone to a cowedge

Given a cocone (X, μ) on P″, define:

```text
β_c = μ_{(1_c : c → c)} : P(c, c) → X.
```

Then the cowedge equation for f : c → d is obtained by applying cocone
naturality along the two canonical morphisms in Tw(Cᵒᵖ)ᵒᵖ connecting f
with identities, exactly as in the cone case.

This gives a functor:

```text
Gᵈ : Cocone(P″) → CoWdg(P).
```

### 10.3 They are inverse on the nose

As before:

- restricting a cocone to identities and rebuilding recovers the original
  components by naturality, and

- building from a cowedge and then restricting to identities recovers the
  original β_c.

Hence CoWdg(P) and Cocone(P″) are isomorphic categories.

---

## 11. Summary dictionary

### Wedge side

- Data: ω_c : X → P(c, c)

- Law: for f : c → d,

```text
P(1, f) ∘ ω_c = P(f, 1) ∘ ω_d : X → P(c, d)
```

- Cone component: for f : c → d,

```text
λ_f = P(f, 1) ∘ ω_d = P(1, f) ∘ ω_c : X → P(c, d)
```

### Cowedge side

- Data: β_c : P(c, c) → X

- Law: for f : c → d,

```text
β_d ∘ P(1, f) = β_c ∘ P(f, 1) : P(d, c) → X
```

- Cocone component: for f : c → d,

```text
μ_f = β_c ∘ P(1, f) = β_d ∘ P(f, 1) : P(d, c) → X
```

---

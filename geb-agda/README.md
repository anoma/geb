# Geb Formal Verification

This repository is concerned with formally proving the categorical properties of Geb without dependent types, specifically focusing on the conjecture that Geb's core category is equivalent to **FinSet**

The overall framework used is MLTT + fun-ext + UIP


## Content outline
- `HoTT` file contains basic type-theoretic constructions with an added Univalence module not used for verification purposes
- `uip-cat` contains formalization of category theory using UIP
- `geb` contains all the relevant code of the formal verification process, as well as properties of finite sets
- `Lambek` contains a compact proof of the equivalence of the category of simply typed $\lambda$-calculi and the category of Cartesian Closed Categories lifted from *Introduction to Higher Order Categorical Logic* while using some results from the study of essentially algebraic theories
- `exp` presents all the computations needed for the verification of Geb's cartesian closedness as instantiated in the Idris code
- `Geb Hom` contains the mathematical proof of cartesian closedness of Geb, piggybacking on the computations in `exp` 

## Core constructions

- `FinSet` is defined as 
```
Σ[ A-n ∶ ((Type lzero) × ℕ) ] (Fin (pr₂ A-n) ≃ pr₁ A-n)
```  
where `Fin n` is defined by pattern-matching:

    Fin : (n : ℕ) → Type lzero
    Fin zero = 𝟘
    Fin (succ zero) = 𝟙
    Fin (succ (succ n)) = (Fin (succ n)) + 𝟙

Hence we define a finite set as a type alongisde a proof that it is equivalent to some finite type. Interpreting MLTT in **Set**, equivalences manifest as bijections while `Σ[ n : ℕ ] Fin n` as $\omega$. We do not care for (-1)-truncating the equivalence proofs since up to (1-categorical) equivalence this will serve the exact same purpose.

We make these into objects of a category by making morphisms the $\Pi$-types between underlying types.

- `ω-cat` is a representation of the canonical skeleton of **FinSet** by taking its objects to be natural numbers and taking
```
Morω : (n m : ℕ) → Type lzero
Morω n m = Fin n → Fin m
```
- `ObjGebCat` and `MorGebCat` mimic the core constructions of the Idris Geb code while making it more readable by getting rid of one of the constructors. In paticular, we establish `ObjGebCat` without using `Subst`.

Note this indeed forms category data after adding appropriate axioms, e.g. :

    postulate

      InitMorAx : {x : ObjGEBCat} (f : Init ↦ x) → (f ≡ InitMor x)
for the universal property of the initial object.

- `GebSkel-cat` is a skeleton of `Geb-cat` where objects are natural numbers and morphisms **GebSkel-cat**$(n, m) :=$  **Geb-cat**$(\bigoplus_{n}$ Term $, \bigoplus_{m}$ Term $)$ 

## Proof outline
We define appropriate categories `FinSet-cat`, `Geb-cat` as described above, after which we establish `ω-cat`, the skeleton of `the former.

Next, use the fact that distributive categories have strict initial objects, which paves a way to proving that `GebSkel-cat` is the skeleton of `Geb-cat`. Next, we prove coherency of Geb, with the use of the evident functor `GF-obj, GF-mor` defined by pattern-matching classifying maps from `Term` into coproducts. 

Then the map sending $\bigoplus_n$ Term to Fin $n$ can be improved to an equivalence between our skeleta.

## Current milestones

  - Geb has a strict initial object
  - Geb is a positive coherent category
  - Geb is spanned by the coproducts of the terminal object 
  - Instantiations of proofs of (co)limit properties established

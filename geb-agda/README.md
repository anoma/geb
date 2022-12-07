# Geb Formal Verification

This repository is concerned with formally proving the categorical properties of Geb without dependent types. 


## Files
- `HoTT` file contains basic type-theoretic constructions with an added Univalence module
- `uip-cat` contains formalization of category theory using UIP
- `geb` contains all the relevant code of the formal verification process, as well as properties of FinSet.
- `Lambek` contains a compact proof of the equivalence of the category of simply typed $\lambda$-calculi and the category of Cartesian Closed Categories lifted from *Introduction to Higher Order Categorical Logic* while using some theory of essentially algebraic theories.

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

Hence we define a finite set as a type alongisde a proof that it is equivalent to some finite type. Interpreting MLTT in **Set** equivalences manifest as bijections while `Σ[ n : ℕ ] Fin n` as a class of cardinals. We do not care for (-1)-truncating the equivalence proofs since up to (1-categorical) equivalence this will serve the exact same purpose for us.

We make these into objects of a category by making morphisms the $\Pi$-types between underlying types.

- `ω` is a representation of the canonical skeleton of **FinSet** by taking its objects to be natural numbers and taking
```
Morω : (x y : ℕ) → Type lzero
Morω x y = Fin x → Fin y
```
- `ObjGebCat` and `MorGebCat` mimic the core constructions of the Idris Geb code while making it more readable by getting rid of one of the constructors. In paticular, we establish `ObjGebCat` without using `Subst`.

Note this indeed forms a category info after adding appropriate axioms, e.g. :

    postulate

      InitMorAx : {x : ObjGEBCat} (f : Init ↦ x) → (f ≡ InitMor x)

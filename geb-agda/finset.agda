{-# OPTIONS --with-K --exact-split --cumulativity #-}
 
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)

module finset where

  import HoTT

  open HoTT.Basics

-- We first introduce the standard definition of FinSet as well as a structure of what will later proven to be the morphisms

  Fin : (n : ℕ) → Type lzero
  Fin zero = 𝟘
  Fin (succ zero) = 𝟙
  Fin (succ (succ n)) = (Fin (succ n)) + 𝟙

-- Read as: elements of FinSet are types A with some proof that there exists a natural number n with a n equivalence (working with UIP+funext think of it as a bijection) of Fin n and A.
-- We need not care in this context about (-1)-truncating. On the categorical level it will make no diffrence up to equivalence.

  FinSet : Type (lsuc lzero)
  FinSet = Σ[ A-n ∶ ((Type lzero) × ℕ) ] (Fin (pr₂ A-n) ≃ pr₁ A-n)

-- Fin k for every k is actually a decidable type, which is important for our purposes. In order to establish that, we need observation equality of the finite types

  Eq-Fin : (k : ℕ) → Fin k → Fin k → Type lzero
  Eq-Fin zero = λ x x₁ → 𝟘
  Eq-Fin (succ zero) = λ x x₁ → 𝟙
  Eq-Fin (succ (succ k)) = λ { (inl x) (inl y) → Eq-Fin (succ k) x y ;
                              (inl x) (inr y) → 𝟘
                              ;
                              (inr x) (inl y) → 𝟘 ; 
                              (inr x) (inr y) → 𝟙}

  Eq-Fin-refl : (k : ℕ) (x : Fin k) → Eq-Fin k x x
  Eq-Fin-refl (succ zero) x = pt
  Eq-Fin-refl (succ (succ k)) (inl x) = Eq-Fin-refl (succ k) x 
  Eq-Fin-refl (succ (succ k)) (inr x) = pt

  ≡-Eq-Fin : (k : ℕ) (x y : Fin k) → (x ≡ y) → Eq-Fin k x y
  ≡-Eq-Fin k x .x (refl .x) = Eq-Fin-refl k x

  Eq-Fin-≡ : (k : ℕ) (x y : Fin k) → (Eq-Fin k x y) → (x ≡ y)
  Eq-Fin-≡ (succ zero) pt pt = λ x → refl _
  Eq-Fin-≡ (succ (succ k)) (inl x) (inl y) = (fun-ap inl) ∘ (Eq-Fin-≡ _ x y)
  Eq-Fin-≡ (succ (succ k)) (inl x) (inr y) = λ x₁ → rec𝟘 _ x₁
  Eq-Fin-≡ (succ (succ k)) (inr x) (inl y) = λ x₁ → rec𝟘 _ x₁
  Eq-Fin-≡ (succ (succ k)) (inr pt) (inr pt) = λ x → refl _

  Eq-Fin-decidable : (k : ℕ) (x y : Fin k) → decidable (Eq-Fin k x y)
  Eq-Fin-decidable (succ zero) x y = 𝟙-decidable
  Eq-Fin-decidable (succ (succ k)) (inl x) (inl y) = Eq-Fin-decidable _ x y
  Eq-Fin-decidable (succ (succ k)) (inl x) (inr y) = 𝟘-decidable
  Eq-Fin-decidable (succ (succ k)) (inr x) (inl y) = 𝟘-decidable
  Eq-Fin-decidable (succ (succ k)) (inr x) (inr y) = 𝟙-decidable

  Fin-decidable-eq : (k : ℕ) → decidable-eq (Fin k)
  Fin-decidable-eq k x y = decidable-bi (Eq-Fin-≡ k x y) (≡-Eq-Fin k x y) (Eq-Fin-decidable k x y)
  
-- Now we specify the morphisms
                             
  MorFinSet : FinSet → FinSet → Type (lzero)
  MorFinSet A B =  pr₁ (proj₁ A) → pr₁ (proj₁ B)

  -- We also introduce appropriate notions of products and coproducts

  sum-of-finsets : (n m : ℕ) → ( ((Fin n) + (Fin m)) ≃ (Fin (n +ℕ m)))
  sum-of-finsets zero m = +-with-𝟘-is-hom-id _
  sum-of-finsets (succ zero) zero = is-equiv-trans (+-is-hom-comm _ _) (+-with-𝟘-is-hom-id _)
  sum-of-finsets (succ zero) (succ m) = +-is-hom-comm _ _
  sum-of-finsets (succ (succ n)) zero = is-equiv-trans (+-is-hom-comm _ _) (is-equiv-trans (+-with-𝟘-is-hom-id _) (equiv-symm (is-equiv-trans (+-is-hom-comm _ _)
                                        (transp (λ k → ((𝟙 + Fin (succ k)) ≃ (Fin (succ (succ n))))) ((right-unit-law-add-ℕ _) ⁻¹) (+-is-hom-comm _ _)))))
  sum-of-finsets (succ (succ n)) (succ zero) = transp (λ k → (((Fin (succ n) + 𝟙) + 𝟙) ≃ (Fin (succ k) + 𝟙))) ((right-succ-law-add-ℕ _ _) ⁻¹)
                                               (transp (λ k → (((Fin (succ n) + 𝟙) + 𝟙) ≃ ((Fin (succ k) + 𝟙) + 𝟙))) ((right-unit-law-add-ℕ _) ⁻¹) (equiv-refl _))
  sum-of-finsets (succ (succ n)) (succ (succ m)) = transp
                                                     (λ k →
                                                        ((Fin (succ n) + 𝟙) + (Fin (succ m) + 𝟙)) ≃ (Fin (succ k) + 𝟙))
                                                     (right-succ-law-add-ℕ _ _ ⁻¹) (is-equiv-trans ((+-hom-assoc (Fin (succ n)) 𝟙 (Fin (succ m) + 𝟙)))
                                                     (is-equiv-trans (+-preserves-equivs (equiv-refl _) (+-is-hom-comm 𝟙 (Fin (succ m) + 𝟙)))
                                                     (is-equiv-trans (equiv-symm (+-hom-assoc (Fin (succ n)) (Fin (succ m) + 𝟙) 𝟙))
                                                     (is-equiv-trans (+-preserves-equivs (equiv-symm (+-hom-assoc (Fin (succ n)) (Fin (succ m)) 𝟙)) (refl-to-equiv (refl 𝟙)))
                                                     (+-preserves-equivs (+-preserves-equivs (sum-of-finsets (succ n) (succ m)) (refl-to-equiv (refl 𝟙))) (refl-to-equiv (refl 𝟙)))))))


  
  prod-of-finsets : (n m : ℕ) → ( ((Fin n) × (Fin m)) ≃ (Fin (n ·ℕ m)))
  prod-of-finsets zero m = ×-with-𝟘-is-hom-id
  prod-of-finsets (succ zero) m = is-equiv-trans (×-hom-comm _ _) (×-with-𝟙-is-hom-id _)
  prod-of-finsets (succ (succ n)) m = is-equiv-trans (×-hom-comm _ _) (is-equiv-trans (×-hom-distrib-over-+ (Fin m) (Fin (succ n)) 𝟙)
                                     (is-equiv-trans (+-preserves-equivs (is-equiv-trans (×-hom-comm (Fin m) (Fin (succ n))) (prod-of-finsets (succ n) m))
                                     (×-with-𝟙-is-hom-id (Fin m))) (sum-of-finsets ((succ n) ·ℕ m) m)))

  _⊕F_ : FinSet → FinSet → FinSet
  ((A , n) ,, x) ⊕F ((B , m) ,, y) = ((A + B) , (n +ℕ m)) ,, is-equiv-trans (equiv-symm (sum-of-finsets n m)) (+-preserves-equivs (x) y)

  _⊗F_ : FinSet → FinSet → FinSet
  ( (A , n) ,, x) ⊗F ((B , m) ,, y) = ((A × B) , (n ·ℕ m)) ,, is-equiv-trans (equiv-symm (prod-of-finsets n m)) (×-preserves-equivs x y)

  -- We show the fact that these indeed define (co)product of types up to propositional equality

  ⊕F-gives-coprod : (x y : FinSet) → Σ[ A ∶ Type lzero ] (Σ[ B ∶ Type lzero ] (pr₁ (proj₁ (x ⊕F y)) ≡ (A + B)))
  ⊕F-gives-coprod ((A , x₁) ,, x₂) ((B , x₃) ,, x₄) = A ,, (B ,, refl _)

  ⊗F-gives-prod : (x y : FinSet) → Σ[ A ∶ Type lzero ] (Σ[ B ∶ Type lzero ] (pr₁ (proj₁ (x ⊗F y)) ≡ (A × B)))
  ⊗F-gives-prod ((A , x₁) ,, x₂) ((B , x₄) ,, x₅) = A ,, (B ,, (refl _))

  -- As well as give categorical names to universal morphisms given by induction

  u-mor-+-FinSet : (x y z : FinSet) → MorFinSet x z → MorFinSet y z → MorFinSet (x ⊕F y) z
  u-mor-+-FinSet ((A , x₁) ,, x₄) ((B , x₃) ,, x₅) z f g = λ { (inl x) → f x ; (inr x) → g x}

  u-mor-×-FinSet : (x y z : FinSet) → MorFinSet z x → MorFinSet z y → MorFinSet z (x ⊗F y)
  u-mor-×-FinSet ((A , x₁) ,, x₄) ((B , x₃) ,, x₅) z f g = λ x → f x , g x

  lleg-+-FinSet : (x y : FinSet) → MorFinSet (x) (x ⊕F y)
  lleg-+-FinSet ((A , x₁) ,, x₄) ((B , x₃) ,, x₅) = inl

  rleg-+-FinSet : (x y : FinSet) → MorFinSet y (x ⊕F y)
  rleg-+-FinSet ((A , x₁) ,, x₄) ((B , x₃) ,, x₅) = inr

  lleg-×-Finset : (x y : FinSet) → MorFinSet (x ⊗F y) x
  lleg-×-Finset ((A , x₁) ,, x₄) ((B , x₃) ,, x₅) = pr₁
  
  rleg-×-Finset : (x y : FinSet) → MorFinSet (x ⊗F y) y
  rleg-×-Finset ((A , x₁) ,, x₄) ((B , x₃) ,, x₅) = pr₂

-- ...and distribution

  distribution-Finset : (x y z : FinSet) → MorFinSet (x ⊗F (y ⊕F z)) ((x ⊗F y) ⊕F (x ⊗F z))
  distribution-Finset ((A , x₁) ,, x₄) ((B , x₃) ,, x₅) ((C , n) ,, e) = λ { (x , inl y') → inl (x ,  y') ; (x , inr z') → inr (x , z')}

-- Below are some additional functions to play with concerning establishig the skeleton of FinSet up to propositional equivalence. We supply the proper skeleton in the sections below

  ⨁F-one : (n : ℕ) → FinSet
  ⨁F-one = n-ary-binary-fun (uncurry (_⊕F_)) ((𝟘 , zero) ,, refl-to-equiv (refl _)) ((𝟙 , one) ,, refl-to-equiv (refl 𝟙))

  Fin-as-obj-of-FinSet : (n : ℕ) → FinSet
  Fin-as-obj-of-FinSet n = ((Fin n) , n) ,, (refl-to-equiv (refl _) )

  descent-to-skeleton : {x y : FinSet} → MorFinSet x y → MorFinSet (Fin-as-obj-of-FinSet (pr₂ (proj₁ x))) (Fin-as-obj-of-FinSet (pr₂ (proj₁ y)))
  descent-to-skeleton {(x , n) ,, (f1 ,, (h1 , h2))} {(y , m) ,, (f2 ,, ((g ,, h3) , h4))} f = (g ∘ f) ∘ f1


-- Also need decidability for the exponential object:

  exp-prod-Fin : (n m : ℕ) → Fin (expℕ n (succ (succ m))) → Fin (expℕ (n) (succ m)) × Fin n
  exp-prod-Fin n m = ≃-qinv (prod-of-finsets _ n)

  Fin-exp-fun : (n m : ℕ) → Fin (expℕ n m) → (Fin m → Fin n)
  Fin-exp-fun n zero y = λ x → rec𝟘 _ x
  Fin-exp-fun n (succ zero) = λ { x y → x}
  Fin-exp-fun n (succ (succ m)) = λ { x (inl y) → rec× {_} {_} {_} {Fin (expℕ n (succ m))} {Fin n} (Fin n) (λ x₁ x₂ → Fin-exp-fun n (succ m) x₁ y) (exp-prod-Fin n m x)
                                    ; x (inr y) → rec× {_} {_} {_} {Fin (expℕ n (succ m))} {Fin n} (Fin n) (λ x₁ x₂ →  x₂) (exp-prod-Fin n m x)}

  fun-exp-Fin : (n m : ℕ) → (Fin m → Fin n) → Fin (expℕ n m)
  fun-exp-Fin n zero = λ x → pt
  fun-exp-Fin n (succ zero) = λ f → f pt
  fun-exp-Fin n (succ (succ m)) = ((≃-qinv (equiv-symm (prod-of-finsets (expℕ n (succ m)) n))) ∘ < fun-exp-Fin n (succ m) ∘ pr₁ , (λ f → f pt) ∘ pr₂ >) ∘ u-mor-coprod-qinverse

-- We define observational equalities for Fin n → Fin m which will rely on decidable types
-- Alternatively, one may construct embeddings via proving that the above maps are equivalences

  EqFinMor : (n m : ℕ) (f g : Fin n → Fin m) → Type lzero
  EqFinMor zero m f g = 𝟙
  EqFinMor (succ zero) m f g = f pt ≡ g pt
  EqFinMor (succ (succ n)) m f g = (EqFinMor _ _ (pr₁ (u-mor-coprod-qinverse f)) (pr₁ (u-mor-coprod-qinverse g))) × (EqFinMor _ _ (pr₂ (u-mor-coprod-qinverse f)) (pr₂ (u-mor-coprod-qinverse g)) )

  EqFinMor-≡ : (n m : ℕ) (f g : Fin n → Fin m) → EqFinMor n m f g → f ≡ g
  EqFinMor-≡ zero m f g k = is-Contr-then-is-Prop _ initial-mor-contr _ _
  EqFinMor-≡ (succ zero) m f g k = funext _ _ λ { pt → k}
  EqFinMor-≡ (succ (succ n)) m f g (a , b) = (+-qinv-eq f) ·
                                             ((fun-ap (λ k → [ k , pr₂ (u-mor-coprod-qinverse f) ]) (EqFinMor-≡ _ _ _ _ a) ·
                                             fun-ap (λ k → [ pr₁ (u-mor-coprod-qinverse g) , k ]) (EqFinMor-≡ _ _ _ _ b))
                                             · ((+-qinv-eq g) ⁻¹)) 

  EqFinMor-refl : (n  m : ℕ) (f : Fin n → Fin m) → EqFinMor n m f f
  EqFinMor-refl zero m f = pt
  EqFinMor-refl (succ zero) m f = refl _
  EqFinMor-refl (succ (succ n)) m f = EqFinMor-refl (succ n) m _ , refl _

  ≡-EqFinMor : (n m : ℕ) (f g : Fin n → Fin m) → f ≡ g → EqFinMor n m f g
  ≡-EqFinMor n m f .f (refl .f) = EqFinMor-refl _ _ f 

  EqFinMor-decidable : (n m : ℕ) (f g : Fin n → Fin m) → decidable (EqFinMor n m f g)
  EqFinMor-decidable zero m f g = 𝟙-decidable
  EqFinMor-decidable (succ zero) m f g = Fin-decidable-eq m (f pt) (g pt)
  EqFinMor-decidable (succ (succ n)) m f g = decidable-prod
                                                            (EqFinMor-decidable (succ n) m (pr₁ (u-mor-coprod-qinverse f)) (pr₁ (u-mor-coprod-qinverse g)))
                                                            (EqFinMor-decidable one m (pr₂ (u-mor-coprod-qinverse f)) (pr₂ (u-mor-coprod-qinverse g)))


  FinMor-decidable-eq : (n m : ℕ) → decidable-eq (Fin n → Fin m)
  FinMor-decidable-eq n m f g = decidable-bi (EqFinMor-≡ n m f g) (≡-EqFinMor n m f g) (EqFinMor-decidable n m f g)

-- And finally use Hedberg's theorem for the core result 

  FinMor-is-Set : (n m : ℕ) → is-Set (Fin n → Fin m)
  FinMor-is-Set n m = Hedberg (FinMor-decidable-eq n m)

-- This is a function establishing an extension property: each type dependent on the skeleton can be extended canonically to the one of the entire FinSet, if one wants to work with this

  FinSet-skel : Type (lsuc lzero)
  FinSet-skel = Σ[ X ∶ ((Type lzero) × ℕ) ] ((Fin (pr₂ X)) ≡ (pr₁ X))

  MorFinSet-skel : FinSet-skel → FinSet-skel → Type lzero
  MorFinSet-skel ((A , n) ,, x) ((B , m) ,, y) = A → B

  FinSet-collapse : FinSet → FinSet-skel
  FinSet-collapse ((A , n) ,, e) = ((Fin n) , n) ,, (refl _)

  extend-from-skeleton : {l1 : Level} (P : FinSet-skel → Type l1) → (FinSet → Type l1)
  extend-from-skeleton P = P ∘ FinSet-collapse

-- Similarly we have a way to canonically restrict types over FinSet to the types over skeleton
  
  skel-into-FinSet : FinSet-skel → FinSet
  skel-into-FinSet ((A , n) ,, eq) = (A , n) ,, refl-to-equiv eq

  restrict-to-skeleton : {l1 : Level} (P : FinSet → Type l1) → (FinSet-skel → Type l1)
  restrict-to-skeleton P = P ∘ skel-into-FinSet

  open import uip-cat

  FinSet-cat : cat-w-level (lsuc lzero) (lzero)
  FinSet-cat = FinSet ,,
                    (MorFinSet ,,
                    (_∘_ ,,
                    ((λ A → id _) ,,
                    ((λ A B f g → refl _ , refl _) , λ A B C D f g h → refl _))))

-- We use the representation of the skeleton of FinSet as ω, the ordinal category

  Morω : (x y : ℕ) → Type lzero
  Morω x y = Fin x → Fin y

  ω-cat : cat-w-level lzero lzero
  ω-cat = ℕ ,, (Morω ,, (_∘_ ,, ((λ A x → x) ,, ((λ A B f g → refl _ , refl _) , λ A B C D f g h → refl _))))

  ω-to-FinSet-obj : ℕ → FinSet
  ω-to-FinSet-obj n = Fin-as-obj-of-FinSet n

  ω-to-FinSet-mor : (n m : ℕ) → (Morω n m) → (MorFinSet (ω-to-FinSet-obj n) (ω-to-FinSet-obj m))
  ω-to-FinSet-mor n m f = f

  FinSet-to-ω-obj : FinSet → ℕ
  FinSet-to-ω-obj ((A , n) ,, y) = n

  FinSet-to-ω-mor : (x y : FinSet) → (MorFinSet x y) → (Morω (FinSet-to-ω-obj x) (FinSet-to-ω-obj y))
  FinSet-to-ω-mor ((A , n) ,, e) ((B , m) ,, e2) f = proj₁ (equiv-symm e2) ∘ (f ∘ proj₁ e)

  distrib-Fin : (n m k : ℕ) → (Fin (n ·ℕ (m +ℕ k))) → (Fin ((n ·ℕ m) +ℕ (n ·ℕ k)))
  distrib-Fin n m k = (proj₁ (sum-of-finsets (n ·ℕ m) (n ·ℕ k))
                      ∘  (([ inl ∘  (proj₁ (prod-of-finsets n m)) , inr ∘  (proj₁ (prod-of-finsets n k)) ]
                      ∘ distribution-Finset (Fin-as-obj-of-FinSet n) (Fin-as-obj-of-FinSet m) (Fin-as-obj-of-FinSet k))
                      ∘ < pr₁ , ((≃-qinv (sum-of-finsets m k)) ∘  pr₂) >))
                      ∘ ≃-qinv (prod-of-finsets (n) (m +ℕ k))

-- Density of Geb-into-FinSet. Recall that by definition of morphisms of FinSet as underlying functions of types,
-- the isomorphisms of the category are equivalences of underlying types, assuming funext.

  FinSet-skel-iso : (A : FinSet) → (pr₁ (proj₁ A)) ≃ (Fin (pr₂ (proj₁ (A))))
  FinSet-skel-iso ((A , n) ,, p) = equiv-symm p

-- We are looking at the density of the inclusion of Geb into FinSet. In particular, that means, given the above result, that every Fin (succ (succ n))
-- will be isomorphic to Fin (⨁ₙ 1) but this follows from basic arithmetic and reflexivity of equivalences, as initial and terminal objects will be hit.

  pluses-1 : (n : ℕ) → ℕ
  pluses-1 zero = zero
  pluses-1 (succ zero) = one
  pluses-1 (succ (succ n)) = (pluses-1 (succ n)) +ℕ one

  ℕ-as-plus-one : (n : ℕ) → n ≡ (pluses-1 n)
  ℕ-as-plus-one zero = refl _
  ℕ-as-plus-one (succ zero) = refl _
  ℕ-as-plus-one (succ (succ n)) = ((fun-ap (λ k → add-ℕ k one) ((ℕ-as-plus-one (succ n)) ⁻¹)) · ((fun-ap (λ k → succ k) (right-succ-law-add-ℕ n zero))
                                                                                               · fun-ap (λ k → succ (succ k)) (right-unit-law-add-ℕ _))) ⁻¹

-- In particular, suppose (A ,, n), p is a finite set. Then it will be isomorphic to, firstly Fin n with evident proofs of equivalence and this in turn
-- will be isomorphic to Fin (⨁ₙ 1) := ⨁Fₙ (Fin 1) := ⨁Fₙ (𝟙) via refl-to-equiv

  density-lemma-Geb-FinSet : (n : ℕ) → Fin n ≃ (Fin (pluses-1 n))
  density-lemma-Geb-FinSet n = refl-to-equiv (fun-ap (λ k → Fin k) (ℕ-as-plus-one n))

  ⊕F-func : (A B : FinSet) → ( (pr₁ (proj₁ (A ⊕F B))) ≡ ((pr₁ (proj₁ A)) + (pr₁ (proj₁ B))))
  ⊕F-func ((A , n) ,, pA) ((B , m) ,, pB) = refl _

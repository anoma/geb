{-# OPTIONS --with-K --exact-split --cumulativity #-}
 
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)

module geb-test where

  import HoTT

  open HoTT.Basics

-- We first introduce the definition of FinSet as well as a structure of what will later proven to be the morphisms

  Fin : (n : ℕ) → Type lzero
  Fin zero = 𝟘
  Fin (succ zero) = 𝟙
  Fin (succ (succ n)) = (Fin (succ n)) + 𝟙

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
  



-- Read as: elements of FinSet are types A with some proof that there exists a natural number n with a n equivalence (working with UIP think of it as a bijection) of Fin n and A. We need not care in this context about truncating. On the categorical level it will make no diffrence up to equivalence.
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

-- This is a function establishing an extension property: each type dependent on the skeleton can be extended canonically to the one of the entire FinSet

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

-- Point choice equality

-- We now introduce the canonical representation of the initial category of Geb 


  data ObjGEBCat : Type lzero where
    Init : ObjGEBCat                                 
    Term : ObjGEBCat                                     
    _⊕G_ : ObjGEBCat → ObjGEBCat → ObjGEBCat   
    _⊗G_ : ObjGEBCat → ObjGEBCat → ObjGEBCat


  data _↦_ : ObjGEBCat → ObjGEBCat → Type lzero where
    _●_ : {x y z : ObjGEBCat} → (y ↦ z) → (x ↦ y) → (x ↦ z)
    IdMor : (x : ObjGEBCat) → (x ↦ x)
    InitMor : (x : ObjGEBCat) → (Init ↦ x)
    TermMor : (x : ObjGEBCat) → (x ↦ Term)
    CoProdMor : {x y z : ObjGEBCat} → (x ↦ z) → (y ↦ z) → ((x ⊕G y) ↦ z)
    ProdMor : {x y z : ObjGEBCat} → (z ↦ x) → (z ↦ y) → ( z ↦ (x ⊗G y))
    DistribMor : {x y z : ObjGEBCat} → ( (x ⊗G (y ⊕G z)) ↦ ( (x ⊗G y) ⊕G (x ⊗G z) ))
    inlG : {x y : ObjGEBCat} → (x ↦ (x ⊕G y))
    inrG : {x y : ObjGEBCat} → (y ↦ (x ⊕G y))
    p1G : {x y : ObjGEBCat} → ((x ⊗G y) ↦ x)
    p2G : {x y : ObjGEBCat} → ((x ⊗G y) ↦ y)

-- We make this into a type by moving the variables out of the context

  data GebMorphType : Type lzero where
    HomGeb : (x y : ObjGEBCat) (f : x ↦ y) → (GebMorphType)

-- Note that this is a Σ-type (using η). This is equivalent to Σ[ x : ObjGEBCat ] (Σ [ y : ObjGEBCat ] (x ↦ y)) which essentially covers all the info regarding the homsets. 

  Comp : {x y z : ObjGEBCat} → (x ↦ y) → (y ↦ z) → (x ↦ z)
  Comp f g = g ● f

  [_,_]G :  {x y z : ObjGEBCat} → (x ↦ z) → (y ↦ z) → ((x ⊕G y) ↦ z)
  [ f , g ]G = CoProdMor f g

  <_,_>G :  {x y z : ObjGEBCat} → (z ↦ x) → (z ↦ y) → ( z ↦ (x ⊗G y))
  < f , g >G = ProdMor f g

  prod-cone : {x y z :  ObjGEBCat} → Type lzero
  prod-cone {x} {y} {z} = (z ↦ x) × (z ↦ y)

  data MorCollGEBCat : Type lzero where
    coll : (x y : ObjGEBCat) → (x ↦ y) → MorCollGEBCat


  is-an-intern-iso : {x y : ObjGEBCat} →  (x ↦ y)  → Type lzero  
  is-an-intern-iso {x} {y} f = Σ[ g ∶ y ↦ x ] (((g ● f) ≡ (IdMor x) ) × ((f ● g) ≡ (IdMor y)))


  _≃G_ : ObjGEBCat → ObjGEBCat → Type (lzero)
  x ≃G y = Σ[ f ∶ x ↦ y ] (is-an-intern-iso f)
  
-- We add freely the axioms making the above a category with needed universal properties. As our formalization of category theory happens in MLTT+UIP these do not introduce extra structure.

  postulate
    InitMorAx : {x : ObjGEBCat} (f : Init ↦ x) → (f ≡ InitMor x)
    TermMorAx : {x : ObjGEBCat} (f : x ↦ Term) → (f ≡ TermMor x)
    IdMorAx : {x y : ObjGEBCat} (f : x ↦ y) → ( (IdMor y) ● f ≡ f ) × ( f ● (IdMor x) ≡ f)
    CompAssocAx : {A B C D : ObjGEBCat} (f : A ↦ B) (g : B ↦ C) (h : C ↦ D) → (h ● (g ● f)) ≡ ((h ● g) ● f)
    CoProdMorAx : {x y z : ObjGEBCat} → is-Contr-fib (uncurry ([_,_]G {x} {y} {z}))
    ProdMorAx : {x y z : ObjGEBCat} → is-Contr-fib (uncurry (<_,_>G {x} {y} {z}))
    CoProdMorLegAx : {x y z : ObjGEBCat} → (f : x ↦ z) → (g : y ↦ z) → ( [ f , g ]G ● inlG ≡ f ) × ( [ f , g ]G ● inrG ≡ g)
    ProdMorLegAx : {x y z : ObjGEBCat} → (f : z ↦ x) → (g : z ↦ y) → ( (p1G ● < f , g >G) ≡ f) × ( p2G ● < f , g >G ≡ g)
    DistribAx : {x y z : ObjGEBCat} → is-an-intern-iso (DistribMor {x} {y} {z})

  IdMor-is-iso : {x : ObjGEBCat} → is-an-intern-iso (IdMor x)
  IdMor-is-iso {x} = deppair (IdMor x) (IdMorAx (IdMor x))

-- Iso props

  iniso-comp : {x y z : ObjGEBCat} (f : x ↦ y) (g : y ↦ z) → is-an-intern-iso (f) → is-an-intern-iso (g) → is-an-intern-iso (g ● f)
  iniso-comp f g (f' ,, (p1 , p2)) (g' ,, (pg1 , pg2)) = (f' ● g') ,,
                                                         ((CompAssocAx _ _ _ · (fun-ap (λ k → k ● f) ((CompAssocAx _ _ _) ⁻¹)
                                                         · (fun-ap (λ k → (f' ● k) ● f) pg1 · ((fun-ap (λ k → k ● f) (pr₂ (IdMorAx _))) · p1))))
                                                         ,
                                                         ((CompAssocAx _ _ _ ) · ((fun-ap (λ k → k ● g') ((CompAssocAx _ _ _) ⁻¹))
                                                         · ((fun-ap (λ k → (g ● k) ● g') p2) · (fun-ap (λ k → k ● g') (pr₂ (IdMorAx _)) · pg2)))))

  ≃G-trans : {x y z : ObjGEBCat} → (x ≃G y) → (y ≃G z) → (x ≃G z)
  ≃G-trans (f ,, (f' ,, (pf1 , pf2))) (g ,, (g' ,, (pg1 , pg2))) = (g ● f) ,, iniso-comp f g ((f' ,, (pf1 , pf2))) ((g' ,, (pg1 , pg2)))


-- A needed property will be the instantiation that the colimit legs are jointly epi as well as some usual composition lemmas for universal morphisms

  mors-from-⊕G-come-from-coprod : {x y z : ObjGEBCat} (f : (x ⊕G y) ↦ z) → Σ[ fg ∶ ((x ↦ z) × (y ↦ z))] (uncurry ([_,_]G) fg ≡ f)
  mors-from-⊕G-come-from-coprod f = proj₁ (proj₁ (CoProdMorAx f)) ,,  (proj₂ (proj₁ (CoProdMorAx f)))

  ⊕G-mor-fib : {x y z : ObjGEBCat} (f : (x ⊕G y) ↦ z) → Σ[ fg ∶ ((x ↦ z) × (y ↦ z))]  ([ (pr₁ fg) , (pr₂ fg) ]G ≡ f)
  ⊕G-mor-fib f = ( proj₁ (proj₁ (CoProdMorAx f))) ,, (curry-pointwise ([_,_]G) (( proj₁ (proj₁ (CoProdMorAx f)))) · (proj₂ (mors-from-⊕G-come-from-coprod f)))

  coprod-mor-to-uni : {x y z : ObjGEBCat} → ( (x ⊕G y) ↦ z ) → ( (x ⊕G y) ↦ z)
  coprod-mor-to-uni f =  [ pr₁ ( proj₁ (proj₁ (CoProdMorAx f))) , pr₂ ( proj₁ (proj₁ (CoProdMorAx f))) ]G 

  

  inx-are-joint-epi : {x y z : ObjGEBCat} (f g : (x ⊕G y) ↦ z) → ((f ● inlG ≡ g ● inlG) × (f ● inrG ≡ g ● inrG)) → (f ≡ g)
  inx-are-joint-epi f g (p1 , p2) = ((proj₂ (mors-from-⊕G-come-from-coprod f)) ⁻¹) ·
                                    (fun-ap (uncurry ([_,_]G))
                                    (prod-id-to-×-id ((proj₁ (mors-from-⊕G-come-from-coprod f))) ((proj₁ (mors-from-⊕G-come-from-coprod g)))
                                    (((pr₁ (CoProdMorLegAx (pr₁ ((proj₁ (mors-from-⊕G-come-from-coprod f)))) (pr₂ ((proj₁ (mors-from-⊕G-come-from-coprod f)))))) ⁻¹) ·
                                    (fun-ap (λ F → F ● inlG) ((curry-pr-eq (uncurry [_,_]G) (proj₁ (mors-from-⊕G-come-from-coprod f)) ⁻¹) ·
                                    proj₂ (mors-from-⊕G-come-from-coprod f )) ·
                                    (p1 · (fun-ap (λ G → G ● inlG) ((proj₂ (mors-from-⊕G-come-from-coprod g)) ⁻¹) ·
                                    (fun-ap (λ G → G ● inlG) (curry-pr-eq ((uncurry [_,_]G)) (proj₁ (mors-from-⊕G-come-from-coprod g))) ·
                                    pr₁ (CoProdMorLegAx (pr₁ ((proj₁ (mors-from-⊕G-come-from-coprod g)))) (pr₂ ((proj₁ (mors-from-⊕G-come-from-coprod g))))))))))
                                    ((((pr₂ (CoProdMorLegAx (pr₁ ((proj₁ (mors-from-⊕G-come-from-coprod f)))) (pr₂ ((proj₁ (mors-from-⊕G-come-from-coprod f)))))) ⁻¹)) ·
                                    (fun-ap (λ F → F ● inrG) ((curry-pr-eq (uncurry [_,_]G) ((proj₁ (mors-from-⊕G-come-from-coprod f)))) ⁻¹) ·
                                    ((fun-ap (λ F → F ● inrG) (proj₂ (mors-from-⊕G-come-from-coprod f))) ·
                                    (p2 ·
                                    ((fun-ap (λ G → G ● inrG) ( ((proj₂ (mors-from-⊕G-come-from-coprod g)) ⁻¹))) ·
                                    ((fun-ap (λ G → G ● inrG) (curry-pr-eq ((uncurry [_,_]G)) (proj₁ (mors-from-⊕G-come-from-coprod g)))) ·
                                    pr₂ ((CoProdMorLegAx (pr₁ ((proj₁ (mors-from-⊕G-come-from-coprod g)))) (pr₂ ((proj₁ (mors-from-⊕G-come-from-coprod g))))))
                                     ))))))) ·
                                    proj₂ (mors-from-⊕G-come-from-coprod g))

  inl-as-coprod : {x y z : ObjGEBCat} → inlG {x ⊕G y} {z} ≡ [ inlG ● inlG , inlG ● inrG ]G
  inl-as-coprod = inx-are-joint-epi _ _ (((pr₁ (CoProdMorLegAx _ _)) ⁻¹) , ((pr₂ (CoProdMorLegAx _ _)) ⁻¹))

  comp-with-coprod-mor : {x y z z' : ObjGEBCat} (f : x ↦ z) (g : y ↦ z) (h : z ↦ z') → (h ● [ f , g ]G ) ≡ ([ h ● f , h ● g ]G)
  comp-with-coprod-mor f g h = inx-are-joint-epi _ _
                                                ((((CompAssocAx _ _ _) ⁻¹) · (fun-ap (λ H → h ● H) (pr₁ (CoProdMorLegAx _ _)) · ((pr₁ (CoProdMorLegAx _ _)) ⁻¹)))
                                                ,
                                                ((((CompAssocAx _ _ _) ⁻¹)) · (fun-ap (λ H → h ● H) (pr₂ (CoProdMorLegAx _ _)) · ((pr₂ (CoProdMorLegAx _ _)) ⁻¹))))

-- We provide a definition of the internal hom object the same way as in the source code to check the universal property

  InHom : ObjGEBCat → ObjGEBCat → ObjGEBCat
  InHom Init y = Term
  InHom Term y = y
  InHom (x ⊕G x') y = (InHom x y) ⊗G InHom x' y
  InHom (x ⊗G x') y = InHom x (InHom x' y)

-- We use the same function as the source code does

  mid-prod-forg : {x y z : ObjGEBCat} → ((x ⊗G y) ⊗G z) ↦ (x ⊗G z)
  mid-prod-forg = < p1G ● p1G , p2G >G

  l-prod-forg : {x y z : ObjGEBCat} → ((x ⊗G y) ⊗G z) ↦ (y ⊗G z)
  l-prod-forg = < p2G ● p1G , p2G >G

  r-prod-forg : {x y z : ObjGEBCat} → ((x ⊗G y) ⊗G z) ↦ (x ⊗G y)
  r-prod-forg = p1G

  r-prod-forg-r : {x y z : ObjGEBCat} → (x ⊗G (y ⊗G z)) ↦ (x ⊗G y)
  r-prod-forg-r = < p1G , p1G ● p2G >G


  prod-1-assoc-rl : {x y z : ObjGEBCat} → (x ⊗G (y ⊗G z)) ↦ ((x ⊗G y) ⊗G z)
  prod-1-assoc-rl = < < p1G , (p1G ● p2G) >G , p2G ● p2G >G

  prod-1-assoc-lr : {x y z : ObjGEBCat} → ((x ⊗G y) ⊗G z) ↦  (x ⊗G (y ⊗G z))
  prod-1-assoc-lr = < (p1G ● p1G) , < (p2G ● p1G) , p2G >G >G

  evalG : (x y : ObjGEBCat) → ( ((InHom x y) ⊗G x) ↦ y )
  evalG Init y = InitMor _ ● p2G
  evalG Term y = p1G
  evalG (x ⊕G x') y = [ (evalG _ _) ● mid-prod-forg , (evalG _ _) ● l-prod-forg ]G ● DistribMor
  evalG (x ⊗G x') y = (evalG x' y) ● (< evalG x (InHom x' y) ● r-prod-forg-r , (p2G ● p2G) >G)   -- or (evalG _ _ ● < evalG _ _ ● p1G , p2G >G) ● prod-1-assoc-rl

-- We now check whether the universal property is satisfied

  λG : {x y z : ObjGEBCat} → (f : (z ⊗G x) ↦ y) → (z ↦ InHom x y) 
  λG {Init} f = TermMor _
  λG {Term} f = f ● < (IdMor _) , TermMor _ >G
  λG {x ⊕G x'} {y} {z} f = < λG {x} {y} {z} (pr₁ (proj₁ (⊕G-mor-fib (f ● (proj₁ (DistribAx {z} {x} {x'}))) )))
                           ,
                              λG {x'} {y} {z} (pr₂ (proj₁ (⊕G-mor-fib (f ● (proj₁ (DistribAx {z} {x} {x'}))) ))) >G    
  λG {x ⊗G x'} {y} {z} f = λG {x} {InHom x' y} (λG {x'} (f ● prod-1-assoc-lr))

-- We also need to prove the identity preservaton and composition preservation of the above function to use in the functoriality proof

  
  IdMor-is-coprod-of-inj : {x y : ObjGEBCat} → IdMor (x ⊕G y) ≡ [ inlG , inrG ]G
  IdMor-is-coprod-of-inj = inx-are-joint-epi _ _ ((pr₁ (IdMorAx inlG) · ((pr₁ (CoProdMorLegAx _ _)) ⁻¹)) , (pr₁ (IdMorAx inrG) · ((pr₂ (CoProdMorLegAx _ _)) ⁻¹)))




-- Moreover, we need the notions of n-ary coproducts to make sure the equivalence works well due to FinSet being spanned by 𝟘, 𝟙, and +

  ⨁G : (x : ObjGEBCat) (n : ℕ) → ObjGEBCat
  ⨁G x zero = Init
  ⨁G x (succ zero) = x
  ⨁G x (succ (succ n)) = (⨁G x (succ n)) ⊕G x

--  We now check that this definition coincides with the one given by the Idris implementation of Geb. One may easily see that the categories formed are isomorphic if needed universal properties are postulated. 

  data SubstObjF (A : Type lzero) : Type lzero where
    SO0 :  SubstObjF A 
    SO1 : SubstObjF A
    _!+_ :  (x y : A) → SubstObjF A
    _!*_ : (x y : A) → SubstObjF A


  data SubstObjMu : Type lzero where
    InSO : SubstObjF (SubstObjMu) → SubstObjMu

  data SubstMorph : SubstObjMu → SubstObjMu → Type lzero where
    SMId : (x : SubstObjMu) → (SubstMorph x x)
    SMComp : {x y z : SubstObjMu} → (SubstMorph y z) → (SubstMorph x y) → (SubstMorph x z)
    SMFromInit : (x : SubstObjMu) → (SubstMorph (InSO SO0) x)
    SMToTerminal : (x : SubstObjMu) → (SubstMorph x (InSO SO1))
    SMInjLeft : (x y : SubstObjMu) → (SubstMorph x ( InSO (x !+ y)))
    SMInjRight : (x y : SubstObjMu) → (SubstMorph y (InSO (x !+ y)))
    SMCase : {x y z : SubstObjMu} → (SubstMorph x z) → (SubstMorph y z) → (SubstMorph (InSO (x !+ y)) z)
    SMPair : {x y z : SubstObjMu} → (SubstMorph x y) → (SubstMorph x z) → (SubstMorph x (InSO (y !* z)))
    SMProjLeft : (x y : SubstObjMu) → (SubstMorph (InSO (x !* y)) x)
    SMProjRight : (x y : SubstObjMu) → (SubstMorph (InSO (x !* y)) y)
    SMDistrib : (x y z : SubstObjMu) → (SubstMorph (InSO (x !* ( InSO (y !+ z)))) (InSO ( (InSO (x !* y)) !+ (InSO (x !* z)))))

-- We make this into a type getting the object variables out of the context 

  data SubstMorphType : Type lzero where 
    HomSubst : (x y : SubstObjMu) (f : SubstMorph x y) → SubstMorphType



-- With this and the formalization of basic category theory in MLTT + UIP + funext we are able to produce the claim that the initial model of Geb is equivalent to FinSet

  open import uip-cat

  FinSet-cat : cat-w-level (lsuc lzero) (lzero)
  FinSet-cat = FinSet ,,
                    (MorFinSet ,,
                    (_∘_ ,,
                    ((λ A → id _) ,,
                    ((λ A B f g → refl _ , refl _) , λ A B C D f g h → refl _))))

  Geb-cat : cat-w-level (lsuc lzero) (lzero)
  Geb-cat = ObjGEBCat ,,
                      (_↦_ ,,
                      (_●_ ,,
                      (IdMor ,,
                      ((λ A B f g → (pr₁ (IdMorAx g)) , pr₂ (IdMorAx f)) , λ A B C D → CompAssocAx ))))


-- We use the representation of the skeleton of FinSet as ω, the ordinal category

  Morω : (x y : ℕ) → Type lzero
  Morω x y = Fin x → Fin y

  ω-cat : cat-w-level lzero lzero
  ω-cat = ℕ ,, (Morω ,, (_∘_ ,, ((λ A x → x) ,, ((λ A B f g → refl _ , refl _) , λ A B C D f g h → refl _))))

  ω-to-Geb-obj : ℕ → ObjGEBCat
  ω-to-Geb-obj n = ⨁G Term n

  obj-of-FinSet-to-⨁G-Term : (n : ℕ) → (Fin n) → (Term ↦ (⨁G Term n))
  obj-of-FinSet-to-⨁G-Term zero ()
  obj-of-FinSet-to-⨁G-Term (succ zero) x = IdMor Term
  obj-of-FinSet-to-⨁G-Term (succ (succ n)) (inl x) = inlG ● (obj-of-FinSet-to-⨁G-Term (succ n) x)
  obj-of-FinSet-to-⨁G-Term (succ (succ n)) (inr x) = inrG
  
  ω-to-Geb-mor : (n m : ℕ) (f : Morω n m) → (ω-to-Geb-obj n ↦ ω-to-Geb-obj m)
  ω-to-Geb-mor zero m f = InitMor _
  ω-to-Geb-mor (succ zero) m f = obj-of-FinSet-to-⨁G-Term m (f pt)
  ω-to-Geb-mor (succ (succ n)) m f = [ ω-to-Geb-mor (succ n) m (pr₁ (proj₁ (functions-from-+-from-uni-prop f)))
                                                    , obj-of-FinSet-to-⨁G-Term m ((pr₂ (proj₁ (functions-from-+-from-uni-prop f))) pt )]G

-- The problem with the above definition is that it will not give us enough information about what is happening on left inclusions
-- However, using decidability, we can establish this explicitly:

  case-inl-eq : {n : ℕ} (f : Morω (succ n) (succ (succ n))) → (f ≡ inl) → (ω-to-Geb-obj (succ n) ↦ ω-to-Geb-obj (succ (succ n)))
  case-inl-eq f p = inlG

  case-inl-neq : {n : ℕ} (f : Morω (succ n) (succ (succ n))) → (¬ (f ≡ inl)) → (ω-to-Geb-obj (succ n) ↦ ω-to-Geb-obj (succ (succ n)))
  case-inl-neq f np =  ω-to-Geb-mor _ _ f

  case-ℕ-eq : (n m : ℕ) (f : Morω (succ n) m) → ((m ≡ (succ (succ n)))) → (ω-to-Geb-obj (succ n) ↦ ω-to-Geb-obj m)
  case-ℕ-eq n .(succ (succ n)) f (refl .(succ (succ n))) = [ case-inl-eq f , case-inl-neq f ] (FinMor-decidable-eq _ _ f inl)

  case-ℕ-neq : (n m : ℕ) (f : Morω (succ n) m) → (¬ (m ≡ (succ (succ n)))) → (ω-to-Geb-obj (succ n) ↦ ω-to-Geb-obj m)
  case-ℕ-neq n m f np = ω-to-Geb-mor _ _ f

  ω-Geb-mor-inl : (n m : ℕ) (f : Morω n m) → (ω-to-Geb-obj n ↦ ω-to-Geb-obj m)
  ω-Geb-mor-inl zero m f = ω-to-Geb-mor zero m f
  ω-Geb-mor-inl (succ n) m f = cases _ (ℕ-decidable-eq m (succ (succ n))) (case-ℕ-eq n m f) (case-ℕ-neq n m f)


-- function as before but make it consider whether it is an injection i.e. whether m = n + 2 

  Geb-to-ω-obj : ObjGEBCat → ℕ
  Geb-to-ω-obj Init = zero
  Geb-to-ω-obj Term = succ zero
  Geb-to-ω-obj (x ⊕G y) = (Geb-to-ω-obj x) +ℕ (Geb-to-ω-obj y)
  Geb-to-ω-obj (x ⊗G y) = (Geb-to-ω-obj x) ·ℕ (Geb-to-ω-obj y)

  Geb-into-FinSet-obj : ObjGEBCat → FinSet
  Geb-into-FinSet-obj Init = (𝟘 , zero) ,, refl-to-equiv (refl _)
  Geb-into-FinSet-obj Term = (𝟙 , one) ,,  refl-to-equiv (refl _)
  Geb-into-FinSet-obj (x ⊕G y) = (Geb-into-FinSet-obj x) ⊕F Geb-into-FinSet-obj y
  Geb-into-FinSet-obj (x ⊗G y) = (Geb-into-FinSet-obj x) ⊗F (Geb-into-FinSet-obj y)

  Geb-into-FinSet-mor : (a b : ObjGEBCat) → (f : a ↦ b) → (MorFinSet (Geb-into-FinSet-obj a) (Geb-into-FinSet-obj b))
  Geb-into-FinSet-mor a b (f ● f₁) = (Geb-into-FinSet-mor _ _ f) ∘ Geb-into-FinSet-mor _ _ f₁
  Geb-into-FinSet-mor a .a (IdMor .a) = λ x → x
  Geb-into-FinSet-mor .Init b (InitMor .b) = λ {()}
  Geb-into-FinSet-mor a .Term (TermMor .a) = λ x → pt
  Geb-into-FinSet-mor (a ⊕G a') b (CoProdMor f g) = u-mor-+-FinSet (Geb-into-FinSet-obj a) (Geb-into-FinSet-obj a') (Geb-into-FinSet-obj b) (Geb-into-FinSet-mor _ _ f) (Geb-into-FinSet-mor _ _ g)
  Geb-into-FinSet-mor a (b ⊗G b') (ProdMor f g) = u-mor-×-FinSet (Geb-into-FinSet-obj b) (Geb-into-FinSet-obj b') (Geb-into-FinSet-obj a) (Geb-into-FinSet-mor _ _ f) (Geb-into-FinSet-mor _ _ g)
  Geb-into-FinSet-mor (x ⊗G (y ⊕G z)) .((_ ⊗G _) ⊕G (_ ⊗G _)) DistribMor = distribution-Finset (Geb-into-FinSet-obj x) (Geb-into-FinSet-obj y) (Geb-into-FinSet-obj z)
  Geb-into-FinSet-mor a .(a ⊕G _) inlG = lleg-+-FinSet (Geb-into-FinSet-obj a) _
  Geb-into-FinSet-mor a (x ⊕G a) inrG = rleg-+-FinSet (Geb-into-FinSet-obj x) (Geb-into-FinSet-obj a)
  Geb-into-FinSet-mor .(b ⊗G _) b p1G = lleg-×-Finset (Geb-into-FinSet-obj b) _
  Geb-into-FinSet-mor (x ⊗G b) b p2G = rleg-×-Finset (Geb-into-FinSet-obj x) (Geb-into-FinSet-obj b)
  
  FinSet-to-Geb-obj : FinSet → ObjGEBCat
  FinSet-to-Geb-obj ((A , n) ,, e) = ⨁G Term n

  FinSet-to-Geb-mor : (a b : FinSet) (f : MorFinSet a b) → ( (FinSet-to-Geb-obj a) ↦ (FinSet-to-Geb-obj b))
  FinSet-to-Geb-mor ((A , n) ,, (f1 ,, e1)) ((B , m) ,, (f2 ,, ((g1 ,, h1) , g2h))) f = ω-to-Geb-mor n m ((g1 ∘ f) ∘ f1)

  ω-to-FinSet-obj : ℕ → FinSet
  ω-to-FinSet-obj n = Fin-as-obj-of-FinSet n

  ω-to-FinSet-mor : (n m : ℕ) → (Morω n m) → (MorFinSet (ω-to-FinSet-obj n) (ω-to-FinSet-obj m))
  ω-to-FinSet-mor n m f = f

  FinSet-to-ω-obj : FinSet → ℕ
  FinSet-to-ω-obj ((A , n) ,, y) = n

  FinSet-to-ω-mor : (x y : FinSet) → (MorFinSet x y) → (Morω (FinSet-to-ω-obj x) (FinSet-to-ω-obj y))
  FinSet-to-ω-mor ((A , n) ,, e) ((B , m) ,, e2) f = proj₁ (equiv-symm e2) ∘ (f ∘ proj₁ e)

  FinSet-to-Geb-fact :  FinSet → ObjGEBCat
  FinSet-to-Geb-fact = (ω-to-Geb-obj ∘ FinSet-to-ω-obj)

  FinSet-to-Geb-mor-fact : {x y : FinSet} (f : MorFinSet x y) → ((FinSet-to-Geb-fact x) ↦ (FinSet-to-Geb-fact y))
  FinSet-to-Geb-mor-fact {x} {y} f = (ω-to-Geb-mor) _ _ (FinSet-to-ω-mor x y f)

  distrib-Fin : (n m k : ℕ) → (Fin (n ·ℕ (m +ℕ k))) → (Fin ((n ·ℕ m) +ℕ (n ·ℕ k)))
  distrib-Fin n m k = (proj₁ (sum-of-finsets (n ·ℕ m) (n ·ℕ k))
                      ∘  (([ inl ∘  (proj₁ (prod-of-finsets n m)) , inr ∘  (proj₁ (prod-of-finsets n k)) ]
                      ∘ distribution-Finset (Fin-as-obj-of-FinSet n) (Fin-as-obj-of-FinSet m) (Fin-as-obj-of-FinSet k))
                      ∘ < pr₁ , ((≃-qinv (sum-of-finsets m k)) ∘  pr₂) >))
                      ∘ ≃-qinv (prod-of-finsets (n) (m +ℕ k)) 

{-  Geb-to-ω-mor : {x y : ObjGEBCat} (f : x ↦ y) → (Morω (Geb-to-ω-obj x) (Geb-to-ω-obj y))
  Geb-to-ω-mor (f ● g) = (Geb-to-ω-mor f) ∘ (Geb-to-ω-mor g)
  Geb-to-ω-mor (IdMor x) = id _
  Geb-to-ω-mor (InitMor _) = λ { ()}
  Geb-to-ω-mor (TermMor _) = λ x₁ → pt
  Geb-to-ω-mor (CoProdMor {x} {y} {z} f g) = [ Geb-to-ω-mor f , Geb-to-ω-mor g ] ∘ ≃-qinv ((sum-of-finsets (Geb-to-ω-obj x) (Geb-to-ω-obj y)))
  Geb-to-ω-mor (ProdMor f g) = proj₁ (prod-of-finsets _ _) ∘ < (Geb-to-ω-mor f) , Geb-to-ω-mor g >
  Geb-to-ω-mor (DistribMor {x} {y} {z}) = distrib-Fin (Geb-to-ω-obj x) (Geb-to-ω-obj y) (Geb-to-ω-obj z)
  Geb-to-ω-mor (inlG {x} {y}) = proj₁ (sum-of-finsets _ _) ∘ inl
  Geb-to-ω-mor (inrG {x} {y}) = proj₁ (sum-of-finsets _ _) ∘ inr
  Geb-to-ω-mor (p1G {x} {y}) = pr₁ ∘ ≃-qinv ((prod-of-finsets (Geb-to-ω-obj x) (Geb-to-ω-obj y)))
  Geb-to-ω-mor (p2G {x} {y}) = pr₂ ∘ ≃-qinv ((prod-of-finsets (Geb-to-ω-obj x) (Geb-to-ω-obj y))) -}


-- Properties of coproducts and products with initial/terminal objects

  Init-coprod-iso : (x : ObjGEBCat) → (Init ⊕G x) ≃G x
  Init-coprod-iso x = [ InitMor _ , IdMor _ ]G ,, (inrG ,,
                                              ((((comp-with-coprod-mor _ _ _ · fun-ap (λ f → [ inrG ● InitMor x , f ]G) (pr₂ (IdMorAx _)))
                                              · (fun-ap (λ f → [ f , inrG ]G) (InitMorAx (inrG ● (InitMor _)) · ((InitMorAx _) ⁻¹)))) · (IdMor-is-coprod-of-inj ⁻¹))
                                              ,
                                              pr₂ (CoProdMorLegAx _ _)))

-- Here is a basic observation about the morphism assignment

  term-to-mor : (n : ℕ) (x : Fin n) → obj-of-FinSet-to-⨁G-Term n x ≡ ω-to-Geb-mor (succ zero) (n) (λ t → x)
  term-to-mor n x = refl _

-- The lemma below provides one of the main ingredients for the (n := succ (succ n)) step in the functoriality proof

  Lemma-ω-to-Geb-mor-preserves-comp : (m k : ℕ) (f : Morω m k) (g : Morω one m) → ω-to-Geb-mor (one) k (f ∘ g ) ≡  (ω-to-Geb-mor m k f) ● (ω-to-Geb-mor (one) m g)
  Lemma-ω-to-Geb-mor-preserves-comp = indℕ (λ m →  (k : ℕ) (f : Morω m k) (g : Morω (one) m) →
                                                  ω-to-Geb-mor (one) k (f ∘ g) ≡
                                                  (ω-to-Geb-mor m k f ● ω-to-Geb-mor (one) m g))
                                                  (λ k f g → rec𝟘 _ (g (pt)) )
                                                  λ m IH → indℕ (λ (m : ℕ) → (k : ℕ) (f : Morω (succ m) k) (g : Morω (one) (succ m)) →
                                                  ω-to-Geb-mor (one) k (f ∘ g) ≡
                                                  (ω-to-Geb-mor (succ m) k f ● ω-to-Geb-mor (one) (succ m) g))
                                                  (λ k f g → transp (λ x → (obj-of-FinSet-to-⨁G-Term k (f (x))) ≡ (ω-to-Geb-mor (succ zero) k f))    
                                                              ((proj₂ (𝟙-is-Contr)) (g pt)) (refl _) · ((pr₂ (IdMorAx _)) ⁻¹))
                                                  (λ m IHsm1 → λ k f g → rec+ (λ {(x ,, p1) → transp
                                                                                          ((λ t →
                                                                                              obj-of-FinSet-to-⨁G-Term k (f t) ≡
                                                                                              (CoProdMor (ω-to-Geb-mor (succ m) k (λ x₁ → f (inl x₁)))
                                                                                               (obj-of-FinSet-to-⨁G-Term k (f (inr pt)))
                                                                                               ● obj-of-FinSet-to-⨁G-Term (succ (succ m)) t)))
                                                                                               (p1 ⁻¹) (IHsm1 _ ((f ∘ inl)) ((λ t → x)) ·
                                                                                               (fun-ap (λ F → F ● obj-of-FinSet-to-⨁G-Term (succ m) x) ((pr₁ (CoProdMorLegAx _ _)) ⁻¹)
                                                                                               · (((CompAssocAx _ _ _) ⁻¹))))})
                                                                                           (λ {(x ,, p1) →  transp
                                                                                          (λ t →
                                                                                             obj-of-FinSet-to-⨁G-Term k (f t) ≡
                                                                                             (CoProdMor (ω-to-Geb-mor (succ m) k (λ x₁ → f (inl x₁)))
                                                                                              (obj-of-FinSet-to-⨁G-Term k (f (inr pt)))
                                                                                              ● obj-of-FinSet-to-⨁G-Term (succ (succ m)) t))
                                                                                          (p1 ⁻¹) (fun-ap (λ l → obj-of-FinSet-to-⨁G-Term k (f (inr l))) (constructor-el-𝟙 x) · ((pr₂ (CoProdMorLegAx _ _)) ⁻¹))})
                                                                                           ((constructor-el-+ (g pt)))) m

  

  ω-to-Geb-mor-preserves-comp : (n m k : ℕ) (f : Morω m k) (g : Morω n m) → ω-to-Geb-mor n k (f ∘ g ) ≡  (ω-to-Geb-mor m k f) ● (ω-to-Geb-mor n m g)
  ω-to-Geb-mor-preserves-comp n = indℕ (λ n → (m k : ℕ) (f : Morω m k) (g : Morω n m) →  ω-to-Geb-mor n k (f ∘ g) ≡  (ω-to-Geb-mor m k f) ● (ω-to-Geb-mor n m g) )
                                  (λ m k f g → (InitMorAx _) ⁻¹)    -- Base case on n :=0
                                  (λ n IHs → indℕ                  -- Double induction on n
                                               (λ (n : ℕ) →
                                                  (m k : ℕ) (f : Morω m k) (g : Morω (succ n) m) →
                                                  ω-to-Geb-mor (succ n) k (f ∘ g) ≡
                                                  (ω-to-Geb-mor m k f ● ω-to-Geb-mor (succ n) m g))
                                               ( indℕ (λ (m : ℕ) → (k : ℕ) (f : Morω m k) (g : Morω (succ zero) m) →                                           -- We now induct on m -- The middle layer corresponds to the Lemma proof
                                                            ω-to-Geb-mor (succ zero) k (f ∘ g ) ≡  (ω-to-Geb-mor m k f) ● (ω-to-Geb-mor (succ zero) m g))
                                                 (λ (k : ℕ) f g → rec𝟘 _ (g (pt)))                                                                              -- Base case for n := 1, m := 0
                                                 λ (m : ℕ) (IHsm0) → indℕ                                                                                       -- IHsm0 inductiv h-s
                                                               (λ (m : ℕ) →
                                                                  (k : ℕ) (f : Morω (succ m) k) (g : Morω (succ zero) (succ m)) →
                                                                  ω-to-Geb-mor (succ zero) k (f ∘ g) ≡
                                                                  (ω-to-Geb-mor (succ m) k f ● ω-to-Geb-mor (succ zero) (succ m) g))
                                                               (λ k f g → transp (λ x → (obj-of-FinSet-to-⨁G-Term k (f (x))) ≡ (ω-to-Geb-mor (succ zero) k f))    
                                                              ((proj₂ (𝟙-is-Contr)) (g pt)) (refl _) · ((pr₂ (IdMorAx _)) ⁻¹))
                                                               (λ m IHsm1 → λ k f g → rec+ (λ {(x ,, p1) → transp
                                                                                          ((λ t →
                                                                                              obj-of-FinSet-to-⨁G-Term k (f t) ≡
                                                                                              (CoProdMor (ω-to-Geb-mor (succ m) k (λ x₁ → f (inl x₁)))
                                                                                               (obj-of-FinSet-to-⨁G-Term k (f (inr pt)))
                                                                                               ● obj-of-FinSet-to-⨁G-Term (succ (succ m)) t)))
                                                                                               (p1 ⁻¹) (IHsm1 _ ((f ∘ inl)) ((λ t → x)) ·
                                                                                               (fun-ap (λ F → F ● obj-of-FinSet-to-⨁G-Term (succ m) x) ((pr₁ (CoProdMorLegAx _ _)) ⁻¹)
                                                                                               · (((CompAssocAx _ _ _) ⁻¹))))})
                                                                                           (λ {(x ,, p1) →  transp
                                                                                          (λ t →
                                                                                             obj-of-FinSet-to-⨁G-Term k (f t) ≡
                                                                                             (CoProdMor (ω-to-Geb-mor (succ m) k (λ x₁ → f (inl x₁)))
                                                                                              (obj-of-FinSet-to-⨁G-Term k (f (inr pt)))
                                                                                              ● obj-of-FinSet-to-⨁G-Term (succ (succ m)) t))
                                                                                          (p1 ⁻¹) (fun-ap (λ l → obj-of-FinSet-to-⨁G-Term k (f (inr l))) (constructor-el-𝟙 x) · ((pr₂ (CoProdMorLegAx _ _)) ⁻¹))})
                                                                                           ((constructor-el-+ (g pt)))) m)
                                               (λ n IHsn1 → λ m k f g → inx-are-joint-epi _ _
                                               ((((pr₁ (CoProdMorLegAx _ _))) · (IHsn1 m k f ((g ∘ inl)) · ((((CompAssocAx _ _ _) ⁻¹) · fun-ap (λ F → ω-to-Geb-mor m k f ● F) (pr₁ (CoProdMorLegAx _ _))) ⁻¹)))
                                               ,
                                               ((pr₂ (CoProdMorLegAx _ _)) · ((Lemma-ω-to-Geb-mor-preserves-comp m k (f) (g ∘ inr) · ((pr₂ (CoProdMorLegAx _ _)) ⁻¹)) · fun-ap (λ F → F ● inrG) ((comp-with-coprod-mor _ _ _) ⁻¹))))) n) n  -- Note the Lemma       


-- One may also look at the commented-out composition preservation proof below. Agda did not recognize the recursive calls in the (n := succ zero) case

{-
  ω-to-Geb-mor-preserves-comp : (n m k : ℕ) (f : Morω m k) (g : Morω n m) → ω-to-Geb-mor n k (f ∘ g ) ≡  (ω-to-Geb-mor m k f) ● (ω-to-Geb-mor n m g)
  ω-to-Geb-mor-preserves-comp zero m k f g = (InitMorAx _) ⁻¹
  ω-to-Geb-mor-preserves-comp (succ zero) zero k f g = rec𝟘 _ (g (pt))
  ω-to-Geb-mor-preserves-comp (succ zero) (succ zero) k f g = transp (λ x → (obj-of-FinSet-to-⨁G-Term k (f (x))) ≡ (ω-to-Geb-mor (succ zero) k f))
                                                              ((proj₂ (𝟙-is-Contr)) (g pt)) (refl _) · ((pr₂ (IdMorAx _)) ⁻¹) 
  ω-to-Geb-mor-preserves-comp (succ zero) (succ (succ m)) k f g = rec+  (λ { (x ,, p1) → transp
                                                                                           (λ t →
                                                                                              obj-of-FinSet-to-⨁G-Term k (f t) ≡
                                                                                              (CoProdMor (ω-to-Geb-mor (succ m) k (λ x₁ → f (inl x₁)))
                                                                                               (obj-of-FinSet-to-⨁G-Term k (f (inr pt)))
                                                                                               ● obj-of-FinSet-to-⨁G-Term (succ (succ m)) t))
                                                                                           (p1 ⁻¹) (((refl _ ·
                                                                                           ω-to-Geb-mor-preserves-comp (succ zero) (succ m) k (f ∘ inl) (λ t → x))
                                                                                           · fun-ap (λ F → F ● obj-of-FinSet-to-⨁G-Term (succ m) x)
                                                                                           (pr₁ (CoProdMorLegAx _ _) ⁻¹))
                                                                                           · ((CompAssocAx _ _ _ _ _ _ _) ⁻¹))})
                                                                        (λ {(x ,, p1) → transp
                                                                                          (λ t →
                                                                                             obj-of-FinSet-to-⨁G-Term k (f t) ≡
                                                                                             (CoProdMor (ω-to-Geb-mor (succ m) k (λ x₁ → f (inl x₁)))
                                                                                              (obj-of-FinSet-to-⨁G-Term k (f (inr pt)))
                                                                                              ● obj-of-FinSet-to-⨁G-Term (succ (succ m)) t))
                                                                                          (p1 ⁻¹) (fun-ap (λ l → obj-of-FinSet-to-⨁G-Term k (f (inr l))) (constructor-el-𝟙 x) · ((pr₂ (CoProdMorLegAx _ _)) ⁻¹))})
                                                                        (constructor-el-+ (g pt))
  ω-to-Geb-mor-preserves-comp (succ (succ n)) m k f g =  inx-are-joint-epi _ _
                                                           ((pr₁ (CoProdMorLegAx _ _) · (ω-to-Geb-mor-preserves-comp (succ n) m k (f) (g ∘ inl) · ((pr₁ (CoProdMorLegAx _ _)) ⁻¹)))
                                                           , ((pr₂ (CoProdMorLegAx _ _)) · (ω-to-Geb-mor-preserves-comp (succ (zero)) m k (f) (g ∘ inr) · ((pr₂ (CoProdMorLegAx _ _)) ⁻¹))))
                                                           · ((comp-with-coprod-mor _ _ _) ⁻¹)
-}

-- A good indication for the equivalence to actually suceed is that the coproduct structure is preserved. For that we need some extra lemmas

  ω-to-Geb-mor-preserves-coprod-mor : (n m : ℕ) (f : Fin (succ n) → Fin m) (g : 𝟙 → Fin m) → ω-to-Geb-mor (succ (succ n)) m ([ f , g ]) ≡ [ ω-to-Geb-mor _ _ f , ω-to-Geb-mor _ _ g ]G
  ω-to-Geb-mor-preserves-coprod-mor n m f g = inx-are-joint-epi _ _
                                                               ((((pr₁ (CoProdMorLegAx _ _))  · ((pr₁ (CoProdMorLegAx _ _)) ⁻¹)))
                                                               ,
                                                               ((pr₂ (CoProdMorLegAx _ _)) · ((pr₂ (CoProdMorLegAx _ _)) ⁻¹)))

  ω-Geb-mor-inl-pres :  (n : ℕ) → ω-Geb-mor-inl (succ n) (succ (succ n)) inl ≡ inlG
  ω-Geb-mor-inl-pres zero = refl _
  ω-Geb-mor-inl-pres (succ n) = fun-ap (λ k → cases _ k (case-ℕ-eq (succ n) (succ (succ (succ n))) inl) (case-ℕ-neq _ _ inl ))
                                       (prop-decidable (ℕ-is-Set (succ (succ (succ n))) (succ (succ (succ n)))) (ℕ-decidable-eq _ _) (inl (refl _)))
                               · (fun-ap (λ k → [ case-inl-eq inl , case-inl-neq inl ] k)
                                         (prop-decidable (FinMor-is-Set _ _ inl inl) (FinMor-decidable-eq _ _ _ _) (inl (refl inl))))



  ω-to-Geb-mor-preserves-id : (n : ℕ) → ω-to-Geb-mor n n (id _) ≡ IdMor (⨁G Term n)
  ω-to-Geb-mor-preserves-id zero = (InitMorAx _) ⁻¹
  ω-to-Geb-mor-preserves-id (succ n) = {!!}

{-# OPTIONS --with-K --exact-split --cumulativity #-}
 
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)

module geb where

  import HoTT

  open HoTT.Basics

-- We first introduce the definition of FinSet as well as a structure of what will later proven to be the morphisms

  Fin : (n : ℕ) → Type lzero
  Fin zero = 𝟘
  Fin (succ n) = (Fin n) + 𝟙

  FinSet : Type (lsuc lzero)
  FinSet = Σ[ A-n ∶ ((Type lzero) × ℕ) ] (Fin (pr₂ A-n) ≃ pr₁ A-n)

-- Read as: elements of FinSet are types A with some proof that there exists a natural number n with a n equivalence (working with UIP think of it as a bijection) of Fin n and A
-- Now we specify the morphisms
                             
  MorFinSet : FinSet → FinSet → Type (lzero)
  MorFinSet A B =  pr₁ (proj₁ A) → pr₁ (proj₁ B)

-- We also introduce appropriate notions of products and coproducts

  sum-of-finsets : (n m : ℕ) → ( ((Fin n) + (Fin m)) ≃ (Fin (n +ℕ m)))
  sum-of-finsets zero zero = 𝟘-+-are-equiv
  sum-of-finsets zero (succ m) = +-with-𝟘-is-hom-id _
  sum-of-finsets (succ n) m = is-equiv-trans (is-equiv-trans (+-hom-assoc (Fin n) (𝟙) (Fin m))
                            (is-equiv-trans (((id (Fin n)) +fun (+-switch)) ,,
                            +fun-pres-equivs id-is-an-equiv (proj₂ (+-is-hom-comm _ _))) (equiv-symm (+-hom-assoc _ _ _)))) (+-preserves-equivs (sum-of-finsets n m) (refl-to-equiv (refl _))) 

  prod-of-finsets : (n m : ℕ) → ( ((Fin n) × (Fin m)) ≃ (Fin (n ·ℕ m)))
  prod-of-finsets zero m = ×-with-𝟘-is-hom-id
  prod-of-finsets (succ n) m = (is-equiv-trans (is-equiv-trans (is-equiv-trans (×-hom-comm _ _) (×-hom-distrib-over-+ _ _ _)) (+-preserves-equivs (is-equiv-trans (×-hom-comm _ _)
                           (prod-of-finsets n m)) (×-with-𝟙-is-hom-id _))) (sum-of-finsets (n ·ℕ m) m))

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
  ⨁F-one = n-ary-binary-fun (uncurry (_⊕F_)) ((𝟘 , zero) ,, refl-to-equiv (refl _)) ((𝟙 , one) ,, +-with-𝟘-is-hom-id 𝟙)

  Fin-as-obj-of-FinSet : (n : ℕ) → FinSet
  Fin-as-obj-of-FinSet n = ((Fin n) , n) ,, (refl-to-equiv (refl _) ) 

  descent-to-skeleton : {x y : FinSet} → MorFinSet x y → MorFinSet (Fin-as-obj-of-FinSet (pr₂ (proj₁ x))) (Fin-as-obj-of-FinSet (pr₂ (proj₁ y)))
  descent-to-skeleton {(x , n) ,, (f1 ,, (h1 , h2))} {(y , m) ,, (f2 ,, ((g ,, h3) , h4))} f = (g ∘ f) ∘ f1

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
    CompAssocAx : (A B C D : ObjGEBCat) (f : A ↦ B) (g : B ↦ C) (h : C ↦ D) → (h ● (g ● f)) ≡ ((h ● g) ● f)
    CoProdMorAx : {x y z : ObjGEBCat} → is-Contr-fib (uncurry ([_,_]G {x} {y} {z}))
    ProdMorAx : {x y z : ObjGEBCat} → is-Contr-fib (uncurry (<_,_>G {x} {y} {z}))
    CoProdMorLegAx : {x y z : ObjGEBCat} → (f : x ↦ z) → (g : y ↦ z) → ( [ f , g ]G ● inlG ≡ f ) × ( [ f , g ]G ● inrG ≡ g)
    ProdMorLegAx : {x y z : ObjGEBCat} → (f : z ↦ x) → (g : z ↦ y) → ( (p1G ● < f , g >G) ≡ f) × ( p2G ● < f , g >G ≡ g)
    DistribAx : {x y z : ObjGEBCat} → is-an-intern-iso (DistribMor {x} {y} {z})

  IdMor-is-iso : {x : ObjGEBCat} → is-an-intern-iso (IdMor x)
  IdMor-is-iso {x} = deppair (IdMor x) (IdMorAx (IdMor x))

-- A needed property will be the instantiation that the colimit legs are jointly epi as well as some usual composition lemmas for universal morphisms

  mors-from-⊕G-come-from-coprod : {x y z : ObjGEBCat} (f : (x ⊕G y) ↦ z) → Σ[ fg ∶ ((x ↦ z) × (y ↦ z))] (uncurry ([_,_]G) fg ≡ f)
  mors-from-⊕G-come-from-coprod f = proj₁ (proj₁ (CoProdMorAx f)) ,,  (proj₂ (proj₁ (CoProdMorAx f)))

  

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

  comp-with-coprod-mor : {x y z z' : ObjGEBCat} (f : x ↦ z) (g : y ↦ z) (h : z ↦ z') → (h ● [ f , g ]G ) ≡ ([ h ● f , h ● g ]G)
  comp-with-coprod-mor f g h = inx-are-joint-epi _ _
                                                ((((CompAssocAx _ _ _ _ _ _ _) ⁻¹) · (fun-ap (λ H → h ● H) (pr₁ (CoProdMorLegAx _ _)) · ((pr₁ (CoProdMorLegAx _ _)) ⁻¹)))
                                                ,
                                                ((((CompAssocAx _ _ _ _ _ _ _) ⁻¹)) · (fun-ap (λ H → h ● H) (pr₂ (CoProdMorLegAx _ _)) · ((pr₂ (CoProdMorLegAx _ _)) ⁻¹))))

-- Moreover, we need the notions of n-ary coproducts to make sure the equivalence works well due to FinSet being spanned by 𝟘, 𝟙, and +

  ⨁G : (x : ObjGEBCat) (n : ℕ) → ObjGEBCat
  ⨁G x zero = Init
  ⨁G x (succ n) = (⨁G x n) ⊕G x

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
                      ((λ A B f g → (pr₁ (IdMorAx g)) , pr₂ (IdMorAx f)) , CompAssocAx))))


-- We use the representation of the skeleton of FinSet as ω, the ordinal category

  Morω : (x y : ℕ) → Type lzero
  Morω x y = Fin x → Fin y

  ω-cat : cat-w-level lzero lzero
  ω-cat = ℕ ,, (Morω ,, (_∘_ ,, ((λ A x → x) ,, ((λ A B f g → refl _ , refl _) , λ A B C D f g h → refl _))))
  
  ω-to-Geb-obj : ℕ → ObjGEBCat
  ω-to-Geb-obj n = ⨁G Term n

  obj-of-FinSet-to-⨁G-Term : (n : ℕ) → (Fin n) → (Term ↦ (⨁G Term n))
  obj-of-FinSet-to-⨁G-Term zero ()
  obj-of-FinSet-to-⨁G-Term (succ n) (inl x) = inlG ● (obj-of-FinSet-to-⨁G-Term n x)
  obj-of-FinSet-to-⨁G-Term (succ n) (inr x) = inrG

  ω-to-Geb-mor : (n m : ℕ) (f : Morω n m) → (ω-to-Geb-obj n ↦ ω-to-Geb-obj m)
  ω-to-Geb-mor zero m f = InitMor _
  ω-to-Geb-mor (succ n) m f = [ ω-to-Geb-mor n m (pr₁ (proj₁ (functions-from-+-from-uni-prop f))) , obj-of-FinSet-to-⨁G-Term m ((pr₂ (proj₁ (functions-from-+-from-uni-prop f))) pt )]G

-- We also need to prove the identity preservaton and composition preservation of the above function to use in the functoriality proof

--  ω-to-Geb-mor-gives-inj-coprod : (n : ℕ) → ω-to-Geb-mor (succ n) (succ n) (id _) ≡ [ inlG ,

  IdMor-is-coprod-of-inj : {x y : ObjGEBCat} → IdMor (x ⊕G y) ≡ [ inlG , inrG ]G
  IdMor-is-coprod-of-inj = inx-are-joint-epi _ _ ((pr₁ (IdMorAx inlG) · ((pr₁ (CoProdMorLegAx _ _)) ⁻¹)) , (pr₁ (IdMorAx inrG) · ((pr₂ (CoProdMorLegAx _ _)) ⁻¹)))

  ω-to-Geb-mor-preserves-inl : (n : ℕ) → ω-to-Geb-mor n (succ n) inl ≡ inlG
  ω-to-Geb-mor-preserves-inl zero = (InitMorAx _) ⁻¹
  ω-to-Geb-mor-preserves-inl (succ n) = {!!}  -- the LHS should be the composition of two inlG using inductive hypotheses (use comp preservation)

  ω-to-Geb-mor-preserves-id : (n : ℕ) → ω-to-Geb-mor n n (id _) ≡ IdMor (⨁G Term n)
  ω-to-Geb-mor-preserves-id zero = (InitMorAx _) ⁻¹
  ω-to-Geb-mor-preserves-id (succ n) = inx-are-joint-epi (ω-to-Geb-mor (succ n) (succ n) (id (Fin (succ n)))) (IdMor (⨁G Term (succ n)))
                                                         ((pr₁ (CoProdMorLegAx _ _) · ({!!} · ((pr₁ (IdMorAx _)) ⁻¹)))
                                                         ,
                                                         ((pr₂ (CoProdMorLegAx _ _)) · ((pr₁ (IdMorAx inrG)) ⁻¹)))

  ω-to-Geb-mor-preserves-comp : (n m k : ℕ) (f : Morω m k) (g : Morω n m) → ω-to-Geb-mor n k (f ∘ g ) ≡  (ω-to-Geb-mor m k f) ● (ω-to-Geb-mor n m g)
  ω-to-Geb-mor-preserves-comp zero m k f g = (InitMorAx _) ⁻¹
  ω-to-Geb-mor-preserves-comp (succ n) zero k f g = rec𝟘 _ (g (inr pt))   -- Could instead use: any morphism factoring through 0 is unique up to ≡
  ω-to-Geb-mor-preserves-comp (succ n) (succ m) k f g = inx-are-joint-epi _ _
                                                        (((pr₁ (CoProdMorLegAx _ _)) · (ω-to-Geb-mor-preserves-comp n (succ m) k f _ · ((pr₁ (CoProdMorLegAx _ _)) ⁻¹)))  
                                                        ,
                                                        ((pr₂ (CoProdMorLegAx _ _)) · (({!!} · {!!}) · ((pr₂ (CoProdMorLegAx _ _)) ⁻¹))))
                                                        · ((comp-with-coprod-mor _ _ _) ⁻¹)

-- The practical problem here is that the usual notion of (co)products easily used in FinSet do not behave well here, as + is associative up to iso
-- So expand the overall equivalence from the skeleton

  Geb-into-FinSet-obj : ObjGEBCat → FinSet
  Geb-into-FinSet-obj Init = (𝟘 , zero) ,, refl-to-equiv (refl _)
  Geb-into-FinSet-obj Term = (𝟙 , one) ,,  +-with-𝟘-is-hom-id 𝟙
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
 
  Geb-into-FinSet-functor-struct : functor-struct Geb-cat FinSet-cat Geb-into-FinSet-obj
  Geb-into-FinSet-functor-struct = Geb-into-FinSet-mor ,,
                                   ((λ a → refl _)
                                   ,
                                   λ a b c f g →  refl _)

  FinSet-to-Geb-functor-struct : functor-struct FinSet-cat Geb-cat FinSet-to-Geb-obj
  FinSet-to-Geb-functor-struct = FinSet-to-Geb-mor ,,
                                 ((λ { ((A , zero) ,, e) → InitMorAx _ · ((InitMorAx _) ⁻¹) ; ((A , succ n) ,, e) → {!!}})
                                 , λ a b c f g → {!!})

      




-- WORK IN PROGRESS
-- We also try to show the underlying type equivalence using univalence


  I-to-A-Obj : SubstObjMu → ObjGEBCat
  I-to-A-Obj (InSO SO0) = Init
  I-to-A-Obj (InSO SO1) = Term
  I-to-A-Obj (InSO (x !+ y)) = (I-to-A-Obj x) ⊕G (I-to-A-Obj y) 
  I-to-A-Obj (InSO (x !* y)) = (I-to-A-Obj x) ⊗G (I-to-A-Obj y)
  
  A-to-I-Obj : ObjGEBCat → SubstObjMu
  A-to-I-Obj Init = InSO SO0
  A-to-I-Obj Term = InSO SO1
  A-to-I-Obj (x ⊕G x₁) = InSO ((A-to-I-Obj x) !+ (A-to-I-Obj x₁))
  A-to-I-Obj (x ⊗G x₁) = InSO ((A-to-I-Obj x) !* (A-to-I-Obj x₁))

  binary-fun-eq-pointwise : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} (f : A → B → C) (a1 a2 : A) (b1 b2 : B) → (a1 ≡ a2) → (b1 ≡ b2) → ((f a1 b1) ≡ (f a2 b2))
  binary-fun-eq-pointwise f a1 .a1 b1 .b1 (refl .a1) (refl .b1) = refl _


  l-homotopy-ObjGEB : (I-to-A-Obj ∘ A-to-I-Obj) ∼ (id _)
  l-homotopy-ObjGEB Init = refl _
  l-homotopy-ObjGEB Term = refl _
  l-homotopy-ObjGEB (x ⊕G y) = binary-fun-eq-pointwise _⊕G_ _ _ _ _ (l-homotopy-ObjGEB x) (l-homotopy-ObjGEB y)
  l-homotopy-ObjGEB (x ⊗G y) = binary-fun-eq-pointwise _⊗G_ ((I-to-A-Obj (A-to-I-Obj x))) x ((I-to-A-Obj (A-to-I-Obj y))) y (l-homotopy-ObjGEB x) (l-homotopy-ObjGEB y)

  r-homotopy-ObjGEB : (A-to-I-Obj ∘ I-to-A-Obj) ∼ (id _)
  r-homotopy-ObjGEB (InSO SO0) = refl _
  r-homotopy-ObjGEB (InSO SO1) = refl _
  r-homotopy-ObjGEB (InSO (x !+ y)) = fun-ap InSO (binary-fun-eq-pointwise _!+_ _ _ _ _ (r-homotopy-ObjGEB x) (r-homotopy-ObjGEB y))
  r-homotopy-ObjGEB (InSO (x !* y)) = fun-ap InSO (binary-fun-eq-pointwise (_!*_) ((A-to-I-Obj (I-to-A-Obj x))) x ((A-to-I-Obj (I-to-A-Obj y))) y (r-homotopy-ObjGEB x) (r-homotopy-ObjGEB y)) 

  Agda-and-Idris-GEB-Obj-equiv :  SubstObjMu ≃ ObjGEBCat
  Agda-and-Idris-GEB-Obj-equiv = I-to-A-Obj ,, ((A-to-I-Obj ,, l-homotopy-ObjGEB) , (A-to-I-Obj ,, r-homotopy-ObjGEB))

  I-to-A-Mor : (x y : SubstObjMu) → SubstMorph x y →  ((I-to-A-Obj x) ↦ (I-to-A-Obj y))
  I-to-A-Mor x x (SMId x) = IdMor (I-to-A-Obj x)
  I-to-A-Mor x y (SMComp F F₁) = I-to-A-Mor _ _ (F) ● I-to-A-Mor _ _ (F₁)
  I-to-A-Mor .(InSO SO0) y (SMFromInit .y) = InitMor (I-to-A-Obj y)
  I-to-A-Mor x .(InSO SO1) (SMToTerminal .x) = TermMor (I-to-A-Obj x)
  I-to-A-Mor x .(InSO (x !+ y)) (SMInjLeft .x y) = inlG
  I-to-A-Mor x .(InSO (x₁ !+ x)) (SMInjRight x₁ .x) = inrG
  I-to-A-Mor .(InSO (_ !+ _)) y (SMCase F F₁) = [ (I-to-A-Mor _ _ F) , I-to-A-Mor _ _ F₁ ]G
  I-to-A-Mor x .(InSO (_ !* _)) (SMPair F F₁) = < (I-to-A-Mor _ _ F) , (I-to-A-Mor _ _ F₁) >G
  I-to-A-Mor .(InSO (y !* y₁)) y (SMProjLeft .y y₁) = p1G
  I-to-A-Mor .(InSO (x !* y)) y (SMProjRight x .y) = p2G
  I-to-A-Mor .(InSO (x !* InSO (y !+ z))) .(InSO (InSO (x !* y) !+ InSO (x !* z))) (SMDistrib x y z) = DistribMor

  A-to-I-Mor : (x y : ObjGEBCat) → (x ↦ y) → (SubstMorph (A-to-I-Obj x) (A-to-I-Obj y))
  A-to-I-Mor x y (_●_ {x} {z} {y} F F₁)  = SMComp (A-to-I-Mor z y F) (A-to-I-Mor x z F₁)
  A-to-I-Mor x .x (IdMor .x) = SMId (A-to-I-Obj x)
  A-to-I-Mor .Init y (InitMor .y) = SMFromInit (A-to-I-Obj y)
  A-to-I-Mor x .Term (TermMor .x) = SMToTerminal (A-to-I-Obj x)
  A-to-I-Mor .(_ ⊕G _) y (CoProdMor f g) = SMCase (A-to-I-Mor _ y f) (A-to-I-Mor _ y g)
  A-to-I-Mor x .(_ ⊗G _) (ProdMor f g) = SMPair (A-to-I-Mor x _ f) (A-to-I-Mor x _ g)
  A-to-I-Mor .(_ ⊗G (_ ⊕G _)) .((_ ⊗G _) ⊕G (_ ⊗G _)) DistribMor = SMDistrib _ _ _
  A-to-I-Mor x .(x ⊕G _) inlG = SMInjLeft (A-to-I-Obj x) _
  A-to-I-Mor x .(_ ⊕G x) inrG = SMInjRight _ (A-to-I-Obj x)
  A-to-I-Mor .(y ⊗G _) y p1G = SMProjLeft (A-to-I-Obj y) _     
  A-to-I-Mor .(_ ⊗G y) y p2G = SMProjRight _ (A-to-I-Obj y)    


-- This establishes the equivalence of underlying objects 
-- Lets go on to the equivalence of underlying types representing homsets
-- Once again, as any context is isomorphic to a Σ-type (allowing for η) this indeed gives all the necessary information about what one can do with Geb 

  Geb-Subst : GebMorphType → SubstMorphType
  Geb-Subst (HomGeb x y (f ● f₁)) = HomSubst (A-to-I-Obj x) (A-to-I-Obj y) (SMComp (A-to-I-Mor _ _ f) (A-to-I-Mor _ _ f₁))
  Geb-Subst (HomGeb x .x (IdMor .x)) = HomSubst (A-to-I-Obj x) _ (SMId (A-to-I-Obj x))
  Geb-Subst (HomGeb .Init y (InitMor .y)) = HomSubst (InSO SO0) (A-to-I-Obj y) (SMFromInit _)
  Geb-Subst (HomGeb x .Term (TermMor .x)) = HomSubst (A-to-I-Obj x) (InSO SO1) (SMToTerminal _)
  Geb-Subst (HomGeb (x ⊕G z) y (CoProdMor f f₁)) = HomSubst (A-to-I-Obj (x ⊕G z)) (A-to-I-Obj y) (SMCase (A-to-I-Mor _ _ f) (A-to-I-Mor _ _ f₁))
  Geb-Subst (HomGeb x (y ⊗G z) (ProdMor f f₁)) = HomSubst (A-to-I-Obj x) (A-to-I-Obj (y ⊗G z)) (SMPair (A-to-I-Mor _ _ f) (A-to-I-Mor _ _ f₁))
  Geb-Subst (HomGeb (x ⊗G (y ⊕G z)) ((x ⊗G y) ⊕G (x ⊗G z)) DistribMor) = HomSubst _ _ (SMDistrib (A-to-I-Obj x) (A-to-I-Obj y) (A-to-I-Obj z))
  Geb-Subst (HomGeb x (x ⊕G y) inlG) = HomSubst (A-to-I-Obj x) (A-to-I-Obj (x ⊕G y)) (SMInjLeft (A-to-I-Obj x) (A-to-I-Obj y))
  Geb-Subst (HomGeb y (x ⊕G y) inrG) = HomSubst (A-to-I-Obj y) (A-to-I-Obj (x ⊕G y)) (SMInjRight (A-to-I-Obj x) (A-to-I-Obj y))
  Geb-Subst (HomGeb (x ⊗G y) x p1G) = HomSubst (A-to-I-Obj (x ⊗G y)) (A-to-I-Obj x) (SMProjLeft _ _)
  Geb-Subst (HomGeb (x ⊗G y) y p2G) = HomSubst (A-to-I-Obj (x ⊗G y)) (A-to-I-Obj y) (SMProjRight _ _)


  Subst-Geb : SubstMorphType → GebMorphType
  Subst-Geb (HomSubst x x (SMId x)) = HomGeb _ _ (I-to-A-Mor x x (SMId x))
  Subst-Geb (HomSubst x y (SMComp f f₁)) = HomGeb _ _ (I-to-A-Mor _ _ (SMComp f f₁))
  Subst-Geb (HomSubst (InSO SO0) y (SMFromInit y)) = HomGeb _ _ (I-to-A-Mor _ _ (SMFromInit y))
  Subst-Geb (HomSubst x .(InSO SO1) (SMToTerminal x)) = HomGeb _ _ (I-to-A-Mor _ _ (SMToTerminal x))
  Subst-Geb (HomSubst x .(InSO (x !+ y)) (SMInjLeft .x y)) = HomGeb _ _ (I-to-A-Mor _ _ (SMInjLeft x y))
  Subst-Geb (HomSubst x .(InSO (x₁ !+ x)) (SMInjRight x₁ .x)) = HomGeb _ _ (I-to-A-Mor x _ (SMInjRight x₁ _))
  Subst-Geb (HomSubst .(InSO (_ !+ _)) y (SMCase f f₁)) = HomGeb _ _ (I-to-A-Mor _ _ (SMCase f f₁))
  Subst-Geb (HomSubst x .(InSO (_ !* _)) (SMPair f f₁)) = HomGeb _ _ (I-to-A-Mor _ _ (SMPair f f₁))
  Subst-Geb (HomSubst .(InSO (y !* y₁)) y (SMProjLeft .y y₁)) = HomGeb _ _ (I-to-A-Mor _ _ (SMProjLeft y y₁))
  Subst-Geb (HomSubst .(InSO (x !* y)) y (SMProjRight x .y)) = HomGeb _ _ (I-to-A-Mor _ _ (SMProjRight x y))
  Subst-Geb (HomSubst .(InSO (x !* InSO (y !+ z))) .(InSO (InSO (x !* y) !+ InSO (x !* z))) (SMDistrib x y z)) = HomGeb _ _ (I-to-A-Mor _ _ (SMDistrib x y z))

-- Here are the important functoriality statements concentrating on compositions which follow by definition

  I-to-A-Mor-comp : {x y z : SubstObjMu} (f : SubstMorph y z) (g : SubstMorph x y) → ( (I-to-A-Mor (x) (z) (SMComp f g)) ≡ ( (I-to-A-Mor y z f) ● (I-to-A-Mor x y g) ) )
  I-to-A-Mor-comp f g = refl _

  A-to-I-Mor-comp : {x y z : ObjGEBCat} (f : y ↦ z) (g : x ↦ y) →  A-to-I-Mor x z (f ● g) ≡ SMComp (A-to-I-Mor y z f) (A-to-I-Mor x y g)
  A-to-I-Mor-comp f g = refl _


  SubstMorphType-constr-eq : (x : SubstMorphType) → Σ[ y ∶ SubstObjMu ] ( Σ[ z ∶ SubstObjMu ] (Σ[ f ∶ SubstMorph y z ] (HomSubst y z f ≡ x  ) ) ) 
  SubstMorphType-constr-eq  (HomSubst x y f) = x ,, (y ,, (f ,, refl _))

  SubstMorphType-morph : (x : SubstMorphType) → (SubstMorph (proj₁ (SubstMorphType-constr-eq x)) (proj₁ (proj₂ (SubstMorphType-constr-eq x))))
  SubstMorphType-morph (HomSubst x y f) = f

{-  Gebequiv-l-comp : (x y z : SubstObjMu) (f : SubstMorph y z) ( g : SubstMorph x y) →
                                         ((Geb-Subst ∘ Subst-Geb) (HomSubst x z (SMComp f g))) ≡ HomSubst _ _
                                                                         (SMComp  (SubstMorphType-morph (HomSubst y z f)) (SubstMorphType-morph (HomSubst x y g)) )
  Gebequiv-l-comp x y z f g = {!!} 



  GEBequiv-l-hom : (Geb-Subst ∘ Subst-Geb) ∼ (id _)
  GEBequiv-l-hom (HomSubst x x (SMId x)) = transp (λ y → HomSubst y y (SMId y) ≡ HomSubst x x (SMId x)) (r-homotopy-ObjGEB x ⁻¹) (refl _)
  GEBequiv-l-hom (HomSubst x y (SMComp f g)) = {!!} 


  GEBequiv-l-hom (HomSubst .(InSO SO0) y (SMFromInit .y)) = transp (λ x → (HomSubst (InSO SO0) x (SMFromInit x)) ≡ (HomSubst (InSO SO0) y (SMFromInit y))) ((r-homotopy-ObjGEB y) ⁻¹) (refl _)
  GEBequiv-l-hom (HomSubst x .(InSO SO1) (SMToTerminal .x)) = transp (λ y → ((HomSubst y (InSO SO1) (SMToTerminal y))) ≡ (HomSubst x (InSO SO1) (SMToTerminal x))) ((r-homotopy-ObjGEB x) ⁻¹) (refl _)
  GEBequiv-l-hom (HomSubst x (InSO (x !+ y)) (SMInjLeft .x y)) = transp (λ z → (HomSubst z (InSO (z !+ (A-to-I-Obj (I-to-A-Obj y)))) (SMInjLeft z (A-to-I-Obj (I-to-A-Obj y)))) ≡ (HomSubst x (InSO (x !+ y)) (SMInjLeft x y)))
                                                                           ((r-homotopy-ObjGEB x) ⁻¹)
                                                                           (transp (λ w → (HomSubst x (InSO (x !+ w)) (SMInjLeft x w)) ≡ (HomSubst x (InSO (x !+ y)) (SMInjLeft x y))) ((r-homotopy-ObjGEB y) ⁻¹) (refl _))
  GEBequiv-l-hom (HomSubst y (InSO (x !+ y)) (SMInjRight x y)) = transp (λ z → HomSubst z (InSO ((A-to-I-Obj (I-to-A-Obj x)) !+ z)) (SMInjRight _ _) ≡ ( HomSubst y (InSO (x !+ y)) (SMInjRight x y))) ((r-homotopy-ObjGEB y) ⁻¹)
                                                                       (transp (λ z → (HomSubst y (InSO (z !+ y)) (SMInjRight z y)) ≡ (HomSubst y (InSO (x !+ y)) (SMInjRight x y))) ((r-homotopy-ObjGEB x) ⁻¹) (refl _))
  GEBequiv-l-hom (HomSubst .(InSO (_ !+ _)) y (SMCase f f₁)) = {!!}
  GEBequiv-l-hom (HomSubst x .(InSO (_ !* _)) (SMPair f f₁)) = {!!}
  GEBequiv-l-hom (HomSubst .(InSO (y !* y₁)) y (SMProjLeft .y y₁)) = {!!}
  GEBequiv-l-hom (HomSubst .(InSO (x !* y)) y (SMProjRight x .y)) = {!!}
  GEBequiv-l-hom (HomSubst .(InSO (x !* InSO (y !+ z))) .(InSO (InSO (x !* y) !+ InSO (x !* z))) (SMDistrib x y z)) = {!!} -}


  open HoTT.Univalence
  
  Agda-and-Idris-GEB-Obj-eq-Univ : ObjGEBCat ≡ SubstObjMu
  Agda-and-Idris-GEB-Obj-eq-Univ = ua (equiv-symm Agda-and-Idris-GEB-Obj-equiv) 

  prop-eq-id : {l1 : Level} {A B : Type l1} (p : A ≡ B) → A → B
  prop-eq-id (refl _) a = a

  fun-over-path : {l1 l2 : Level} {A : Type l1} {B : Type l2} {C : Type l2} (f : A → B) → (B ≡ C) → A → C
  fun-over-path f (refl _) = f

  qinverse-MorGEB : (x y : SubstObjMu) → (((I-to-A-Obj x) ↦ (I-to-A-Obj y) )) → (SubstMorph x y)
  qinverse-MorGEB x y = ( ((prop-eq-id (binary-fun-eq-pointwise SubstMorph _ _ _ _ (r-homotopy-ObjGEB x) (r-homotopy-ObjGEB y))) ∘ (A-to-I-Mor (I-to-A-Obj x) (I-to-A-Obj y))))


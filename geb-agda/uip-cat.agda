{-# OPTIONS --without-K --exact-split #-} 
 

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)

module uip-cat where

  import HoTT
  open HoTT.Basics

  postulate
    UIP : {l1 : Level} {A : Type l1} {a1 a2 : A} → (is-Prop (a1 ≡ a2))

  cat-struct : (l1 l2 : Level) → Type l1 → Type ((l1 ⊔ lsuc l2))
  cat-struct l1 l2 ObjC =                                                              -- Class of objects 
                (Σ[ HomC ∶ (ObjC → ObjC → Type l2) ]                                 -- Class of morphisms 
                (Σ[ _∘C_ ∶ ({A B C : ObjC} → (HomC B C) → (HomC A B) → (HomC A C)) ]  -- Composition operation
                (Σ[ i ∶ ((A : ObjC) → (HomC A A)) ]                                   -- Choice of identities  
                (((A B : ObjC) (f : HomC A B) (g : HomC B A)
                → ( (i A) ∘C g ≡ g) × ( f ∘C (i A) ≡ f)) ×
                ((A B C D : ObjC) → (f : HomC A B) → (g : HomC B C) → (h : HomC C D) → (h ∘C (g ∘C f) ≡ (h ∘C g) ∘C f ) )))))

  

  cat-w-level : (l1 l2 : Level) → Type (lsuc l1 ⊔ lsuc l2)
  cat-w-level l1 l2  = Σ[ x ∶ Type l1 ] (cat-struct l1 l2 x)

  _-obj : {l1 l2 : Level} (C : cat-w-level l1 l2) → Type l1
  _-obj (x ,, x₁) = x

  _-homset : {l1 l2 : Level} (C : cat-w-level l1 l2) → (C -obj → C -obj → Type l2)
  _-homset (x ,, (x₁ ,, x₂)) = x₁

  cat-id : {l1 l2 : Level} (C : cat-w-level l1 l2) → ( A : C -obj) → ((C -homset) A A)
  cat-id (x ,, (y ,, (z ,, (x₁ ,, x₂)))) A = x₁ A

  cat-comp : {l1 l2 : Level} (C1 : cat-w-level l1 l2) {A B C : C1 -obj} → ( (_-homset C1) B C) → ( (C1 -homset) A B) → ((C1 -homset) A C) 
  cat-comp (x ,, (x₁ ,, (x₂ ,, x₃))) f1 f2 = x₂ f1 f2

  functor-struct : {l1 l2 : Level} (C1 C2 : cat-w-level l1 l2) → (C1 -obj → C2 -obj) → Type (l1 ⊔ l2)
  functor-struct C1 C2 f-obj = Σ[ f-mor ∶ ((a b : C1 -obj) → ((C1 -homset) a b) → ((C2 -homset) (f-obj a) (f-obj b))) ]                                                      -- Assignment on morphism of C1(a , b) to C2(f(a), f(b))
                               (( (a : C1 -obj) → ( f-mor a a (cat-id C1 a)  ≡ cat-id C2 (f-obj a)) )                                                                         -- identity morphism preservation
                                 ×
                               ((a b c : (C1 -obj)) (f : (C1 -homset) b c) (g : (C1 -homset) a b) → (f-mor _ _ (cat-comp C1 f g )) ≡ cat-comp C2 (f-mor _ _ f) (f-mor _ _ g))) -- composition preservation


  functor : {l1 l2 : Level} (C1 C2 : cat-w-level l1 l2) → Type (l1 ⊔ l2)
  functor C1 C2 = Σ[ f ∶ ( (C1 -obj) → (C2 -obj) ) ] (functor-struct C1 C2 f)

  iso-struct : {l1 l2 : Level} (C1 : cat-w-level l1 l2) {a b : C1 -obj} (f : (C1 -homset) a b) → Type l2
  iso-struct C1 {a} {b} f = Σ[ g ∶ ((C1 -homset) b a) ] ((cat-comp C1 g f) ≡ (cat-id C1 a)) × ((cat-comp C1 f g) ≡ (cat-id C1 b))
  
  cat-iso : {l1 l2 : Level} (C1 : cat-w-level l1 l2) {a b : C1 -obj} → Type l2
  cat-iso C1 {a} {b} = Σ[ f ∶ (C1 -homset) a b ] (iso-struct C1 f)

  functor-on-obj : {l1 l2 : Level} (C1 C2 : cat-w-level l1 l2) (F : functor C1 C2) →  ( (C1 -obj) → (C2 -obj) )
  functor-on-obj C1 C2 F = proj₁ F

  functor-on-mor : {l1 l2 : Level} (C1 C2 : cat-w-level l1 l2) (F : functor C1 C2) →  (a b : C1 -obj) → (C1 -homset) a b → ((C2 -homset) ((functor-on-obj C1 C2 F) a) ((functor-on-obj C1 C2 F) b)) 
  functor-on-mor C1 C2 (f-obj ,, (f-mor ,, x)) = f-mor

  id-preserv-functor : {l1 l2 : Level} (C1 C2 : cat-w-level l1 l2) (F : functor C1 C2) → ( (a : C1 -obj) → ( (functor-on-mor C1 C2 F) a a (cat-id C1 a)  ≡ cat-id C2 ((functor-on-obj C1 C2 F) a)) )
  id-preserv-functor C1 C2 (f-obj ,, (f-mor ,, (x , y))) = x

  comp-preserv-functor : {l1 l2 : Level} (C1 C2 : cat-w-level l1 l2) (F : functor C1 C2) →
                         ((a b c : (C1 -obj)) (f : (C1 -homset) b c) (g : (C1 -homset) a b) → ((functor-on-mor C1 C2 F) _ _ (cat-comp C1 f g )) ≡ cat-comp C2 ((functor-on-mor C1 C2 F) _ _ f) ((functor-on-mor C1 C2 F) _ _ g))
  comp-preserv-functor C1 C2 (f-obj ,, (f-mor ,, (x , y))) = y

  nat-trans-mor-choice : {l1 l2 : Level} {C1 C2 : cat-w-level l1 l2} (F G : functor C1 C2) → Type (l1 ⊔ l2)
  nat-trans-mor-choice {_} {_} {C1} {C2} F G = (a : C1 -obj) →  (C2 -homset) ((functor-on-obj C1 C2 F) a) ( (functor-on-obj C1 C2 G) a)

  nat-trans-naturality :  {l1 l2 : Level} {C1 C2 : cat-w-level l1 l2} (F G : functor C1 C2) (α : nat-trans-mor-choice {_} {_} {C1} {C2} F G)
                           → Type (l1 ⊔ l2)
  nat-trans-naturality {_} {_} {C1} {C2} F G α = (a b : C1 -obj) (f : (C1 -homset) a b) → cat-comp C2 ((functor-on-mor C1 C2 G) a b f) (α a) ≡ cat-comp C2 (α b) ((functor-on-mor C1 C2 F) a b f)

  nat-trans :  {l1 l2 : Level} {C1 C2 : cat-w-level l1 l2} → Type (l1 ⊔ l2)
  nat-trans {_} {_} {C1} {C2} = Σ[ F ∶ functor C1 C2 ] Σ[ G ∶ functor C1 C2 ] Σ[ α ∶ nat-trans-mor-choice {_} {_} {C1} {C2} F G ] (nat-trans-naturality {_} {_} {C1} {C2} F G α)

  _⇒_ : {l1 l2 : Level} {C1 C2 : cat-w-level l1 l2} (F : functor C1 C2) (G : functor C1 C2) → Type (l1 ⊔ l2)
  _⇒_ {_} {_} {C1} {C2} F G =  Σ[ α ∶ nat-trans-mor-choice {_} {_} {C1} {C2} F G ] (nat-trans-naturality {_} {_} {C1} {C2} F G α)

  nat-trans-instance-mor-choice :  {l1 l2 : Level} {C1 C2 : cat-w-level l1 l2} (F G : functor C1 C2) (α : _⇒_ {_} {_} {C1} {C2} F G) → nat-trans-mor-choice {_} {_} {C1} {C2} (F) (G)
  nat-trans-instance-mor-choice F G (x ,, x₁) = x

  nat-iso-struct : {l1 l2 : Level} {C1 C2 : cat-w-level l1 l2} (F G : functor C1 C2) (α : _⇒_ {_} {_} {C1} {C2} F G) → Type (l1 ⊔ l2)
  nat-iso-struct {_} {_} {C1} {C2} F G α = (a : C1 -obj) →
                                           iso-struct {_} {_} C2 (nat-trans-instance-mor-choice {_} {_} {C1} {C2} F G α a)

  id-functor : {l1 l2 : Level} (C1 : cat-w-level l1 l2) → functor C1 C1
  id-functor C1 = id _ ,,
                  ( (λ a b f → f) ,,
                       ((λ a → refl _) ,
                           λ a b c f g → refl _))

  _∘Cat_ : {l1 l2 : Level} {C1 C2 C3 : cat-w-level l1 l2} (F : functor C2 C3) (G : functor C1 C2) → (functor C1 C3)
  _∘Cat_ {_} {_} {C1} {C2} {C3} F G = (functor-on-obj C2 C3 F ∘ functor-on-obj C1 C2 G) ,,
                                                           ((λ a b f → (functor-on-mor C2 C3 F ((functor-on-obj C1 C2 G) a) (((functor-on-obj C1 C2 G)) b) ∘ functor-on-mor C1 C2 G a b) f) ,,
                                                           ((λ a → fun-ap (functor-on-mor C2 C3 F (proj₁ G a) (proj₁ G a)) (id-preserv-functor C1 C2 G a) · id-preserv-functor C2 C3 F _)
                                                           , λ a b c f g →
                                                             (fun-ap (functor-on-mor C2 C3 F (proj₁ G a) (proj₁ G c)) (comp-preserv-functor C1 C2 G a b c f g))
                                                             · comp-preserv-functor C2 C3 F _ _ _ _ _))

  _≃Cat_ : {l1 l2 : Level} (C1 C2 : cat-w-level l1 l2) → Type (l1 ⊔ l2)
  C1 ≃Cat C2 = Σ[ F ∶ (functor C1 C2) ] (Σ[ G ∶ (functor C2 C1)]
                 (( Σ[ α ∶ ( _⇒_ {_} {_} {C2} {C2} (_∘Cat_ {_} {_} {C2} {C1} {C2} F G) (id-functor C2) ) ]
                         (nat-iso-struct {_} {_} {C2} {C2} ( (_∘Cat_ {_} {_} {C2} {C1} {C2} F G) ) (id-functor C2) α))
                         ×
                         (Σ[ α ∶ (( _⇒_ {_} {_} {C1} {C1} (_∘Cat_ {_} {_} {C1} {C2} {C1} G F) (id-functor C1) ) ) ]
                          (nat-iso-struct {_} {_} {C1} {C1} ( (_∘Cat_ {_} {_} {C1} {C2} {C1} G F) ) (id-functor C1) α)))) 

  

-- Basic (co)limits

  terminal-obj-struct : {l1 l2 : Level} (C : cat-w-level l1 l2) (x : C -obj) → Type (l1 ⊔ l2)
  terminal-obj-struct C x = (Σ[ t-mor ∶ ({y : C -obj} → ((C -homset) y x)) ] ((z : C -obj) (f : (C -homset) z x) → f ≡ t-mor) )  
  
  initial-obj-struct : {l1 l2 : Level} (C : cat-w-level l1 l2) (x : C -obj) → Type (l1 ⊔ l2)
  initial-obj-struct C x = (Σ[ i-mor ∶ ({y : C -obj} → ((C -homset) x y)) ] ((z : C -obj) (f : (C -homset) x z) → f ≡ i-mor) ) 

{-  coprod-obj-struct : {l1 l2 : Level} (C : cat-w-level l1 l2) (x y x-plus-y : C -obj) → Type (l1 ⊔ l2)
  coprod-obj-struct C x y x-plus-y = Σ[ fg ∶ ((C -homset) x x-plus-y) × ((C -homset) y x-plus-y) ]
                                        ({z : C -obj} (f : (C -homset) x z) (g : ((C -homset) y z)) →
                                        Σ[ f-or-g ∶ ((C -homset) x-plus-y z) ] ({!!} × ({!!} × {!!}))  ) -}

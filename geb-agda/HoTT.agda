{-# OPTIONS --without-K --exact-split #-}


-- This is the formalization of basic type-theoretic constructions. Almost everything is a formalization of claims/exercises as stated either in Rijke's or the HoTT books. A separate library was made for stability purposes of the formal verification procedure. 
 

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)

module HoTT where

  module Basics where

    Type : (i : Level) → Set (lsuc i)
    Type i = Set i

    const-type-fam : {l1 l2 : Level} {A : Type l1} (C : Type l2)  → (A → Type l2)
    const-type-fam C = λ a → C

    data ℕ : Type lzero where
      zero : ℕ 
      succ : ℕ → ℕ


    indℕ :  {l : Level} (C : ℕ → Type l) → (C (zero)) → ( (n : ℕ) → (C n → (C (succ n)))) → ( (n : ℕ) → C n)
    indℕ C p f zero = p 
    indℕ C p f (succ n) = f n (indℕ C p f n)

    indℕ-Frob : {l1 l2 : Level} (C : ℕ → Type l1) (D : (n : ℕ) → C n → Type l2) (p : (n : ℕ) → C n) → (D zero (p zero)) →  ( (n : ℕ) → (D n (p n)  → D (succ n) ((p (succ n))))) → ((n : ℕ) → D n (p n))
    indℕ-Frob C D p = indℕ λ x → D x (p x)

    data Bool : Type lzero where
      true : Bool
      false : Bool

    ind𝟚 : ∀ {l} {C : Bool → Type l} → (C true) → (C false) → (∀ (c : Bool) → C c)
    ind𝟚 p q true = p
    ind𝟚 p q false = q

    data Empty : Type lzero where

    ind𝟘 : ∀ {l} (C : Empty → Type l) → ((x : Empty) → C x)
    ind𝟘 C ()

    rec𝟘 : {l : Level} (C : Type l) → Empty → C
    rec𝟘 C ()

    𝟘 : Type lzero
    𝟘 = Empty

    data 𝟙 : Type lzero where
       pt : 𝟙

    ind𝟙 : {l : Level} (C : 𝟙 → Type l) → (C pt) → (∀ (x : 𝟙) → C x)
    ind𝟙 C H pt = H

    data _+_ {l1 l2}(A : Type l1) (B : Type l2) : Set (l1 ⊔ l2) where
         inl : A → A + B
         inr : B → A + B

    rec+ : {l1 l2 l3 : Level}  {A : Type l1} {B : Type l2 } {C : Type l3 } →
      (A → C) → (B → C) → (A + B → C)
    rec+ f g (inl x) = f x
    rec+ f g (inr x) = g x

    ind+ : {l1 l2 l3 : Level} {A : Type l1 } {B : Type l2 } (C :  A + B  → Type l3 ) → 
         ( (a : A) → C (inl a)) → ( (b : B) → (C (inr b)) ) → ((c : A + B) → (C c))
    ind+ C f g (inl x) = f x
    ind+ C f g (inr x) = g x


    data _×_ {l1 l2} (A : Type l1) (B : Type l2) : Type (l1 ⊔ l2) where
      _,_ : A → B → A × B

    pair : {l1 l2 : Level} {A : Type l1} {B : Type l2} → A → B → A × B
    pair a b = a , b

    rec× : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} (C : Type l3) → 
         (A → B → C) → (A × B → C)
    rec× C f (x , x₁) = f x x₁

    ind× : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} (C : A × B → Type l3) → 
      ( (a : A) → ∀ (b : B) → C(pair a b)) → ( (x : A × B) → C(x))
    ind× C f (x , x₁) = f x x₁
  
    pr₁ : {l1 l2 : Level} {A : Type l1} {B : Type l2} (x : A × B) → A
    pr₁ (x , x₁) = x
  
    pr₂ : {l1 l2 : Level} {A : Type l1} {B : Type l2} (x : A × B) → B
    pr₂ (x , x₁) = x₁

    data Σ {l1 l2 : Level} (A : Type l1) (B : A → Type l2) : Type (l1 ⊔ l2) where
      _,,_ :  (x : A) → B x → Σ A B

    deppair :  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (x : A) → B x → Σ A B
    deppair x y = x ,, y

    Σ-recursion :  {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} (C : Type l3) → 
                                                 (∀ (a : A) → B a → C) → (Σ A B → C)
    Σ-recursion C f (x ,, x₁) = f x x₁


    Σ-induction : {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} (C : (Σ A B) → Type l3) → 
                                     (∀ (a : A) → ∀ (b : B a) → (C (deppair a b))) → (∀ (x : Σ A B) → C x)
    Σ-induction C f (x ,, x₁) = f x x₁

    proj₁ : {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (x : Σ A B) →  A
    proj₁ (x ,, x₁) = x

    proj₂ :  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (x : Σ A B) → B (proj₁ x)
    proj₂ (x ,, x₁) = x₁


    Σ-syntax = Σ
    infix 2 Σ-syntax
    syntax Σ-syntax A (λ x → B) = Σ[ x ∶ A ] B {- ths colum is gotten by -backdash- + : -} 

    data Con : Type lzero
    data Ty : Con → Type lzero

    data Con where
      ⊥ : Con
      _,,,_ : (Γ : Con) → Ty Γ → Con 

    data Ty where 
      U : ∀ {Γ} → Ty Γ
      Π : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ ,,, A)) → Ty Γ

    data _≡_ {l1} {A : Type l1} :  A → A → Type l1  where
      refl : ∀ (a : A) →  a ≡ a

    ind≡ : {l1 l2 : Level}  {A : Type l1 } (C : ∀ {x y : A} -> ( (x ≡ y) -> (Type l2) )) → ( ∀ (z : A) → (C (refl z)) ) → ({a b : A}  (p : a ≡ b) → (C p) )
    ind≡ C f (refl x) = f x

    rec≡ : {l1 l2 : Level} {A : Type l1 } (C : Type l2) → ( ∀ (x : A) → C ) → (( a b : A)  (p : a ≡ b) → C )
    rec≡ C x a .a (refl .a) = x a

    inv-path : {l1 : Level} {A : Type l1} {a b : A} (p : a ≡ b)  →  b ≡ a
    inv-path (refl _) = refl _

    _⁻¹ : {l1 : Level} {A : Type l1} {a b : A} (p : a ≡ b) → b ≡ a
    (refl _)⁻¹ = refl _ 

    concat : {l1 : Level} {A : Type l1} {x y z : A} →  x ≡ y → y ≡ z → x ≡ z
    concat (refl _) q = q

    add-ℕ :  ℕ  →  ℕ  →  ℕ 
    add-ℕ zero m = m
    add-ℕ (succ n) m = succ (add-ℕ n m)

    mult-ℕ : ℕ → ℕ → ℕ
    mult-ℕ zero m = zero
    mult-ℕ (succ n) m = add-ℕ (mult-ℕ n m) m

    max-ℕ : ℕ → ℕ → ℕ
    max-ℕ zero m = m
    max-ℕ (succ n) zero = succ n
    max-ℕ (succ n) (succ m) = succ (max-ℕ n m) 

    min-ℕ : ℕ → ℕ → ℕ
    min-ℕ zero m = zero
    min-ℕ (succ n) zero = zero
    min-ℕ (succ n) (succ m) = succ (min-ℕ n m)

    pred : ℕ → ℕ
    pred zero = zero
    pred (succ n) = n

    ¬_ : {l1 : Level} → Type l1 → Type l1
    ¬ A = A → Empty

    neg-Bool : Bool → Bool
    neg-Bool true = false
    neg-Bool false = true

    _∧_ : Bool → Bool → Bool
    false ∧ b2 = false
    true ∧ true = true
    true ∧ false = false

    _∨_ : Bool → Bool → Bool
    true ∨ b2 = true
    false ∨ true = true
    false ∨ false = false

    _↔_ : {l1 l2 : Level} →  Type l1 → Type l2 → Type (l1 ⊔ l2)
    A ↔ B = (A → B) × (B → A)

    data list {l1 : Level} (A : Type l1) :  Type l1  where
      nil :  list A
      cons : A → (list A) → (list A)


    fold-list : {l1 : Level} {A B : Type l1} → B →  (A → B → B) → (list A → B)
    fold-list b μ nil = b
    fold-list b μ (cons x l) = μ x (fold-list b μ l)

    map-list : {l1 : Level} {A B : Type l1} → (A → B) → (list A → list B)
    map-list f nil = nil
    map-list f (cons x l) = cons (f x) (map-list f l)

    concat-list : {l1 : Level} {A : Type l1} → list A → list A → list A
    concat-list nil l2 = l2
    concat-list (cons x l1) l2 = cons x (concat-list l1 l2)

    flatten-list : {l1 : Level} {A : Type l1} → list (list A) → list A
    flatten-list nil = nil
    flatten-list (cons nil l₁) = flatten-list l₁
    flatten-list (cons (cons x l) l₁) = cons x (flatten-list (cons l l₁))

    _·_ : {l1 : Level} {A : Type l1}  {x y z : A} →  (x ≡ y) → (y ≡ z) → (x ≡ z)
    p · q = concat p q

    concat-assoc : {l1 : Level} {A : Type l1} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (t : z ≡ w) →  (( (p · q ) · t ) ≡  ( p · (q · t)))
    concat-assoc (refl _) (refl _) t = refl t

    refl-l : {l1 : Level} {A : Type l1} {x y  : A } (p : x  ≡ y) →  ((refl x) · p) ≡ p
    refl-l (refl _) = refl _

    refl-r :  {l1 : Level} {A : Type l1} {x y : A} (p : x ≡ y) → (p · (refl y)) ≡ p
    refl-r (refl _) = refl _

    left-inv :  {l1 : Level} {A : Type l1} {x y : A} (p : x ≡ y) → ((inv-path p) ·  p) ≡ (refl _)
    left-inv (refl _) = refl _

    right-inv :   {l1 : Level} {A : Type l1} {x y : A} (p : x ≡ y) → (p · (inv-path p)) ≡ (refl _)
    right-inv (refl _) = refl _

    fun-ap :  {l1 l2 : Level} {A : Type l1} {B : Type l2} {x y : A} (f : A → B) (p : x ≡ y) → (f x) ≡ (f y)
    fun-ap f (refl _) = refl _

    _∘_ : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} → (B → C) → (A → B) → (A → C)
    (g ∘ f) x = g (f x)

    fun-comp-assoc :  {l1 l2 l3 l4 : Level} {A : Type l1} {B : Type l2} {C : Type l3} {D : Type l4} (f : A → B) (g : B → C) (h : C → D) (a : A) →
                                                                                                   (h ∘ (g ∘ f)) a ≡ ((h ∘ g) ∘ f )a
    fun-comp-assoc f g h a = refl _

    id : {l1 : Level} (A : Type l1) → A → A
    id A x = x

    ap-id :  {l1 : Level} {A : Type l1} {x y : A} (p : x ≡ y) → p ≡ (fun-ap (id A ) p)
    ap-id (refl x) = refl _

    ap-comp :  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} {x y : A} (p : x ≡ y) (f : A → B) (g : B → C) →
                                                                                              (fun-ap g (fun-ap f p)) ≡ (fun-ap (g ∘ f) p)
    ap-comp (refl x) f g = refl _


    ap-refl :  {l1 l2 : Level} {A : Type l1} {B : Type l2} {x : A} (f : A → B) → (fun-ap f (refl x)) ≡ (refl (f x))
    ap-refl f = refl _

    ap-inv :  {l1 l2 : Level} {A : Type l1} {B : Type l2} {x y : A} (p : x ≡ y) (f : A → B) → (fun-ap f (inv-path p)) ≡ (inv-path (fun-ap f p))
    ap-inv (refl _) f = refl _

    ap-concat :  {l1 l2 : Level} {A : Type l1} {B : Type l2} {x y z : A} (p : x ≡ y) (q : y ≡ z) (f : A → B)  → (fun-ap f (p · q)) ≡ ( (fun-ap f p) · (fun-ap f q))
    ap-concat (refl _) q f = refl _

    transp :  {l1 l2 : Level} {A : Type l1} (B : A → Type l2)  {x y : A}  →  (x ≡ y) → B x → B y
    transp B (refl x) z = z

    fun-ap-dep :  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (f : ∀ (x : A) → B x) {x y : A}  (p : x ≡ y) →
                                                                                    (transp B p (f x)) ≡ (f y)
    fun-ap-dep f (refl _) = refl _ 

    id-Σ-type-endpoint :  {l1 : Level} {A : Type l1} (a : A) (y : Σ A (λ x → a ≡ x))   →  (deppair a (refl a)) ≡ y
    id-Σ-type-endpoint a ( .a ,, (refl .a)) = refl _

    _+ℕ_ : ℕ → ℕ → ℕ
    n +ℕ m = add-ℕ n m

    infixl 1 _≡_

    left-unit-law-add-ℕ : (n : ℕ) → ((zero +ℕ n) ≡ n)
    left-unit-law-add-ℕ n = refl _ 


    right-unit-law-add-ℕ : ( n : ℕ) → (n +ℕ zero ≡ n)
    right-unit-law-add-ℕ zero = refl _
    right-unit-law-add-ℕ (succ n) = fun-ap succ (right-unit-law-add-ℕ n)

    left-succ-law-add-ℕ :  (m n : ℕ) → ((succ m) +ℕ n ≡ succ (m +ℕ n))
    left-succ-law-add-ℕ m n = refl _

    right-succ-law-add-ℕ : (m n : ℕ) → (m +ℕ (succ n) ≡ succ (m +ℕ n))
    right-succ-law-add-ℕ zero n =  fun-ap succ (inv-path (left-unit-law-add-ℕ n)) 
    right-succ-law-add-ℕ (succ m) n = fun-ap succ (right-succ-law-add-ℕ m n)

    assoc-add-ℕ : (m n k : ℕ) → (m +ℕ n) +ℕ k ≡ m +ℕ (n +ℕ k)
    assoc-add-ℕ zero n k = refl _
    assoc-add-ℕ (succ m) n k = fun-ap succ (assoc-add-ℕ m n k)


    commutative-add-ℕ : (m n : ℕ) → m +ℕ n ≡ n +ℕ m
    commutative-add-ℕ zero n = inv-path (right-unit-law-add-ℕ n)
    commutative-add-ℕ (succ m) n = concat (fun-ap succ (commutative-add-ℕ m n))  (inv-path (right-succ-law-add-ℕ n m))

    distributive-inv-concat : {A : Set} {x y z : A} (p : x ≡ y) (q : y ≡ z) → inv-path (p · q) ≡ (inv-path q) · (inv-path p)
    distributive-inv-concat (refl _) q = concat (refl-l (inv-path (q))) (concat (refl _) (inv-path  (refl-r (inv-path q))))

    inv-con :  {l1 : Level} {A : Type l1} {x y z : A} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z) → (p · q ≡ r) → (q ≡ (inv-path p) · r)
    inv-con (refl x) q r t = concat t (refl r)

    path-uniq-inv :  {l1 : Level} {A : Type l1} {x y : A} (p : x ≡ y) (q : y ≡ x) → (p · q ≡ (refl _)) → (q ≡ inv-path p)
    path-uniq-inv (refl _) q r = concat r (refl _)

    con-inv :   {l1 : Level} {A : Type l1} (x y z : A) (p : x ≡ y) (q : y ≡ z) (r : x ≡ z) → (p · q ≡ r) → (p ≡ r · (inv-path q))
    con-inv x y z (refl x) q r t = concat (inv-path (right-inv q)) (fun-ap (λ l → (l · (inv-path q))) t)

    lift :  {l1 l2 : Level} {A : Type l1} (B : A → Type l2) {a x : A} (p : a ≡ x) (b : B a) → deppair a b ≡ deppair x (transp B p b)
    lift B (refl x) b = refl _

    _·ℕ_ : ℕ → ℕ → ℕ
    m ·ℕ n = mult-ℕ m n

    zero-mult-r-ℕ : (m : ℕ) → m ·ℕ zero ≡ zero
    zero-mult-r-ℕ zero = refl _
    zero-mult-r-ℕ (succ m) = concat (right-unit-law-add-ℕ (m ·ℕ zero)) (zero-mult-r-ℕ m)

    zero-mult-l-ℕ : (m : ℕ) → zero ·ℕ m ≡ zero
    zero-mult-l-ℕ m = refl _

    one : ℕ
    one = succ zero

    one-mult-r-ℕ : (m : ℕ) → m ·ℕ one ≡ m
    one-mult-r-ℕ zero = zero-mult-l-ℕ one
    one-mult-r-ℕ (succ m) = concat (right-succ-law-add-ℕ (m ·ℕ one) (zero))
                       (fun-ap succ (concat (right-unit-law-add-ℕ (m ·ℕ one)) (one-mult-r-ℕ m)))

    one-mult-l-ℕ : (m : ℕ) → one ·ℕ m ≡ m
    one-mult-l-ℕ zero = zero-mult-r-ℕ one
    one-mult-l-ℕ (succ m) = concat (fun-ap (λ (x : ℕ) → x +ℕ succ m) (zero-mult-l-ℕ (succ m)))
                       (left-unit-law-add-ℕ (succ m))

    succ-mult-right : (m n : ℕ) → m ·ℕ (succ n) ≡ m +ℕ (m ·ℕ n)
    succ-mult-right zero n = concat (inv-path (right-unit-law-add-ℕ zero))
                         (inv-path (zero-mult-l-ℕ n))
    succ-mult-right (succ m) n = concat (right-succ-law-add-ℕ (m ·ℕ (succ n)) n)
                          (fun-ap succ (concat (concat (fun-ap (λ x → x +ℕ n) (succ-mult-right m n))
                                                       (assoc-add-ℕ m (m ·ℕ n) n)) (refl _)))

-- One extra concat, need to remove

    succ-mult-left : (m n : ℕ) → (succ m) ·ℕ n ≡ (m ·ℕ n) +ℕ n
    succ-mult-left m n = refl _

    mult-ℕ-commutative : (m n : ℕ) → m ·ℕ n ≡ n ·ℕ m
    mult-ℕ-commutative zero n = inv-path (zero-mult-r-ℕ n)
    mult-ℕ-commutative (succ m) n = concat (concat (fun-ap (λ x → x +ℕ n) (mult-ℕ-commutative m n))
                                               (commutative-add-ℕ (n ·ℕ m) n))
                         (inv-path (succ-mult-right n m))

    mult-ℕ-distrib-left : (m n k : ℕ) → m ·ℕ (n +ℕ k) ≡ (m ·ℕ n) +ℕ (m ·ℕ k)
    mult-ℕ-distrib-left zero n k = right-unit-law-add-ℕ zero
    mult-ℕ-distrib-left (succ m) n k = ((((fun-ap (λ x → ( x +ℕ (n +ℕ k))) (mult-ℕ-distrib-left m n k )) ·
                    inv-path (assoc-add-ℕ ( (m ·ℕ n) +ℕ (m ·ℕ k)) n k)) ·
                    ((fun-ap (λ x → x +ℕ k) (assoc-add-ℕ (m ·ℕ n) (m ·ℕ k) n)) ·
                    (fun-ap (λ x → ((m ·ℕ n) +ℕ x) +ℕ k) (commutative-add-ℕ ((m ·ℕ k)) n)))) ·
                    fun-ap (λ x → x +ℕ k) ( inv-path (assoc-add-ℕ (m ·ℕ n) (n) (m ·ℕ k)))) ·
                    assoc-add-ℕ ((m ·ℕ n) +ℕ n) (m ·ℕ k) k


    mult-ℕ-distrib-right : (m n k : ℕ) → (m +ℕ n) ·ℕ k ≡ (m ·ℕ k) +ℕ (n ·ℕ k)
    mult-ℕ-distrib-right m n k = mult-ℕ-commutative (m +ℕ n) k  ·
                           (mult-ℕ-distrib-left k m n ·
                           (fun-ap (λ x → x +ℕ (k ·ℕ n)) (mult-ℕ-commutative k m) ·
                           fun-ap (λ x → (m ·ℕ k) +ℕ x) (mult-ℕ-commutative k n)))


    mult-ℕ-assoc : (m n k : ℕ) → (m ·ℕ n) ·ℕ k ≡ m ·ℕ (n ·ℕ k)
    mult-ℕ-assoc zero n k = refl _
    mult-ℕ-assoc (succ m) n k = (mult-ℕ-distrib-right (m ·ℕ n) n k) ·
                          (fun-ap (λ x → x +ℕ (n ·ℕ k)) (mult-ℕ-assoc m n k))

    expℕ : (n m : ℕ) → ℕ
    expℕ n zero = one
    expℕ n (succ m) = (expℕ n m) ·ℕ n

    zero-exp : (m : ℕ) → expℕ zero (succ m) ≡ zero
    zero-exp m = zero-mult-r-ℕ (expℕ zero m)
    
    Eqℕ : ∀ (n m : ℕ) → Type lzero
    Eqℕ zero zero = 𝟙
    Eqℕ zero (succ m) = 𝟘
    Eqℕ (succ n) zero = 𝟘
    Eqℕ (succ n) (succ m) = Eqℕ n m

    refl-Eqℕ : ∀ (n : ℕ) → Eqℕ n n
    refl-Eqℕ zero = pt
    refl-Eqℕ (succ n) = refl-Eqℕ n

    Eqℕ-≡ : (n m : ℕ) → ( (n ≡ m) → (Eqℕ n m))
    Eqℕ-≡ n .n (refl .n) = refl-Eqℕ n

    ≡-Eqℕ : (n m : ℕ) → Eqℕ n m → n ≡ m
    ≡-Eqℕ zero zero = λ x → refl _
    ≡-Eqℕ zero (succ m) = λ x → rec𝟘 _ x
    ≡-Eqℕ (succ n) zero = λ x → rec𝟘 _ x
    ≡-Eqℕ (succ n) (succ m) = fun-ap succ ∘ ≡-Eqℕ n m

    true-to-one-false-to-zero : Bool → Type lzero
    true-to-one-false-to-zero true = 𝟙
    true-to-one-false-to-zero false = 𝟘

    true-not-false : ¬ (true ≡ false)
    true-not-false = λ (x : true ≡ false) → transp true-to-one-false-to-zero x pt


{- HoTT Core Definitions -}


    _∼_ : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) (g : A → B) → Type (l1 ⊔ l2)
    f ∼ g  = (x : _) → f x ≡ g x

    is-an-equiv :  {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) → Type ((l1 ⊔ l2))
    is-an-equiv {_} {_} {A} {B} f = ( Σ[ g ∶ (B → A) ] ((f ∘ g) ∼ (id _)) ) × ( Σ[ g ∶ (B → A) ] ((g ∘ f) ∼ (id _)) )

    _≃_ : {l1 l2 : Level} (A : Type l1) (B : Type l2) → Type (l1 ⊔ l2)
    A ≃ B = Σ[ f ∶ (A → B) ] (is-an-equiv f)

    postulate
      funext : {l1 l2 : Level} {A : Type l1} {B : Type l2} ( f g : A → B) → (f ∼ g) → (f ≡ g)
      funext-is-an-equiv : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f g : A → B) → is-an-equiv (funext f g)

    qinverses-are-equal-with-funext :  {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) → (Q : is-an-equiv f) → (proj₁ (pr₁ Q)) ≡ (proj₁ (pr₂ Q))
    qinverses-are-equal-with-funext f ((g ,, x) , (g' ,, y)) = funext g g' λ b → ((y (g b))⁻¹ ) · ((fun-comp-assoc g f g' b ⁻¹) · fun-ap g' (x b))

    has-inv : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) → Type (l1 ⊔ l2)
    has-inv {_} {_} {A} {B} f = Σ[ g ∶ (B → A) ] (((f ∘ g) ∼ id _) × ((g ∘ f) ∼ id _))

    has-inv-then-equiv :  {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) → has-inv f → is-an-equiv f
    has-inv-then-equiv f (g ,, (p1 , p2)) = (g ,, p1) , (g ,, p2)

    equiv-has-inv-funext :   {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) → is-an-equiv f → has-inv f
    equiv-has-inv-funext f ((g1 ,, p1) , (g2 ,, p2)) = g1 ,, (p1 , (transp (λ g → (g ∘ f) ∼ id _) ((qinverses-are-equal-with-funext f (((g1 ,, p1) , (g2 ,, p2)))) ⁻¹) p2))

    inv-has-inv :  {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) (p : has-inv f) → has-inv (proj₁ p)
    inv-has-inv f (g ,, (p1 , p2)) = f ,, (p2 , p1)

    qinv-are-equivs : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) (p : is-an-equiv f) → is-an-equiv (proj₁ (pr₁ p))
    qinv-are-equivs f ((g1 ,, p1) , (g2 ,, p2) )= (f ,, λ x → transp (λ g → (g (f x)) ≡ x) ((qinverses-are-equal-with-funext f (((g1 ,, p1) , (g2 ,, p2) ))) ⁻¹) (p2 x)) , (f ,, p1)

    fib : {l1 l2 : Level} {A : Type l1} {B  : Type l2} (f : A → B) (b : B) → Type (l1 ⊔ l2)
    fib {_} {_} {A} {_} f b = Σ[ a ∶ A ] (f a ≡ b)

    is-Contr : {l1 : Level} (A : Type l1) → Type l1
    is-Contr A = Σ[ a ∶ A ] ( (a' : A) → (a ≡ a') )

    is-Contr-fib :  {l1 l2 : Level} {A : Type l1} {B  : Type l2} (f : A → B) → Type (l1 ⊔ l2)
    is-Contr-fib {_} {_} {_} {B} f = (b : B) → is-Contr (fib f b)

    is-Contr-fib-qinverse :  {l1 l2 : Level} (A : Type l1) (B  : Type l2) (f : A → B) → (is-Contr-fib f) → (B → A)
    is-Contr-fib-qinverse A B f P b = proj₁ (proj₁ (P b))

    is-Prop : {l1 : Level} (A : Type l1) → Type l1
    is-Prop A = (x y : A) → x ≡ y

    is-Set : {l1 : Level} (A : Type l1) → Type l1
    is-Set A = (a1 a2 : A ) → is-Prop (a1 ≡ a2)

    is-Contr-then-is-Prop : {l1 : Level} (A : Type l1) → (is-Contr A) → (is-Prop A)
    is-Contr-then-is-Prop A P a1 a2 = ((proj₂ P a1) ⁻¹) · proj₂ P a2

    is-Prop-equiv : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) (p : is-Prop A) → is-an-equiv f → is-Prop B
    is-Prop-equiv f p ((g1 ,, p1) , (g2 ,, p2)) = λ x y → ((p1 x) ⁻¹) · (fun-ap f (p _ _) · p1 y)

    is-Prop-inh-Contr : {l1 : Level} {A : Type l1} (p : is-Prop A) (a : A) → is-Contr A
    is-Prop-inh-Contr p a = a ,, λ a' → p _ _

    is-Contr-equiv : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) (p : is-Contr A) → is-an-equiv f → is-Contr B
    is-Contr-equiv f p e = is-Prop-inh-Contr (is-Prop-equiv f (is-Contr-then-is-Prop _ p) e) (f (proj₁ p))

    map-Contr-equiv :  {l1 l2 : Level} {A : Type l1} {B : Type l2} (p : is-Contr A) (q : is-Contr B) (f : A → B) → is-an-equiv f
    map-Contr-equiv (c1 ,, p1) (c2 ,, p2) f = ((λ x → c1) ,, (λ x → is-Contr-then-is-Prop _ ((c2 ,, p2)) _ _))
                                              ,
                                              ((λ x → c1) ,, λ x → is-Contr-then-is-Prop _ ((c1 ,, p1)) _ _)

    is-Contr-fib-to-is-an-equiv : {l1 l2 : Level} (A : Type l1) (B : Type l2) (f : A → B) → (is-Contr-fib f) → (is-an-equiv f)
    is-Contr-fib-to-is-an-equiv A B f (P {-: is-Contr-fib f-}) = ((is-Contr-fib-qinverse _ _ f P) ,, (λ (b : B) → proj₂ (proj₁ (P b))))
                                                                                                                         ,
                                                             (((is-Contr-fib-qinverse _ _ f P)) ,,   (λ (a : A) → fun-ap proj₁ ( (proj₂ (P (f a))) (a ,, (refl (f a))) )))

    Σ-id-to-prod-id : {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (x1 x2 : Σ A B) → (p : x1 ≡ x2) → ( (transp B (fun-ap (proj₁) p) (proj₂ x1)) ≡ (proj₂ x2) )
    Σ-id-to-prod-id x1 x1 (refl x1) = refl _

    prod-id-to-Σ-id :  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (x1 x2 : Σ A B) → (Σ[ (p) ∶ (proj₁ x1 ≡ proj₁ x2) ] (transp B p (proj₂ x1) ≡ proj₂ x2)) → (x1 ≡ x2)
    prod-id-to-Σ-id (a1 ,, b1) (a1 ,, .b1) ((refl a1) ,, (refl b1)) = refl _
    Σ-eq-left-equiv :  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (x1 x2 : Σ A B) →
                                                 ( ((λ p → ( (fun-ap proj₁ p) ,, (Σ-id-to-prod-id x1 x2 p)  )) ∘ (prod-id-to-Σ-id x1 x2)) ∼ (id (_) ))
    Σ-eq-left-equiv (x ,, x₁) (x ,, .x₁)  ((refl x) ,, refl .(x₁)) = refl _

    Σ-eq-right-equiv :  {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (x1 x2 : Σ A B) →  ( ( (prod-id-to-Σ-id x1 x2) ∘ (λ p → ( (fun-ap proj₁ p) ,, (Σ-id-to-prod-id x1 x2 p)  )) ) ∼ (id _))
    Σ-eq-right-equiv (x ,, x₁) (x ,, x₁) (refl (x ,, x₁)) = refl _


    Σ-id-equiv : {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (x1 x2 : Σ A B) → ( (x1 ≡ x2) ≃ (Σ[ (p) ∶ (proj₁ x1 ≡ proj₁ x2) ] (transp B p (proj₂ x1) ≡ proj₂ x2)))
    Σ-id-equiv x1 x2 = (λ p → ( (fun-ap proj₁ p)
                            ,, (Σ-id-to-prod-id x1 x2 p)  )) ,, (((prod-id-to-Σ-id x1 x2) ,, Σ-eq-left-equiv x1 x2 )
                                                                                                                    ,
                                                                                                       ((prod-id-to-Σ-id x1 x2) ,, Σ-eq-right-equiv x1 x2))

    Σ-dep-prop-id : {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (x1 x2 : Σ A B) → ((a : A) → is-Prop (B a)) → (proj₁ (x1) ≡ proj₁ (x2)) → x1 ≡ x2
    Σ-dep-prop-id (a1 ,, b1) (a2 ,, b2) Q p = prod-id-to-Σ-id ((a1 ,, b1)) ((a2 ,, b2)) (p ,, Q _ _ _)

   {- Σ-nondep-pair : {l1 l2 l3} (A : Type l1) (B : Type l2) (C : A → B → Type l3) → (Σ[ a ∶ A ] (Σ[ b ∶ B ] (C a b))) ≃ (Σ[ x ∶ (A × B) ] (C (pr₁ x) (pr₂ x))) -}

    
    is-embed : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) → Type (l1 ⊔ l2)
    is-embed f = (x y : _) → is-an-equiv (fun-ap {_} {_} {_} {_} {x} {y} f)

    ishae : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) → Type (l1 ⊔ l2)
    ishae {_} {_} {A} {B} f = Σ[ g ∶ (B → A) ] Σ[ η-ϵ ∶ (((g ∘ f) ∼ (id A)) × ((f ∘ g) ∼ (id B)))  ] ((a : A) → fun-ap f ((pr₁ η-ϵ) a) ≡ (pr₂ η-ϵ) (f a) )

    ishae-to-is-equiv : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) → ishae f → is-an-equiv f
    ishae-to-is-equiv f (g ,, ((η , ϵ) ,, F)) = (g ,, ϵ) , (g ,, η)

    Eqfib : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) (b : B) (x, y : fib f b) → Type (l1 ⊔ l2)
    Eqfib f b (x1 ,, x2) (y1 ,, y2) = Σ[ α ∶ (x1 ≡ y1) ] (x2 ≡ ((fun-ap f α) · y2))

    
    homotopy-naturality : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f g : A → B) (H : f ∼ g) {x y : A} (p : x ≡ y) → (H x) · (fun-ap g p) ≡ (fun-ap f p) · (H y)
    homotopy-naturality f g H (refl _) = refl-r _

    homotopy-whiskering : {l1 l2 : Level} {A : Type l1} (f : A → A) (H : f ∼ (id A)) (x : A) → H (f x) ≡ fun-ap f (H x)
    homotopy-whiskering {l1} {l2} {A} f H x = ((refl-r (H (f x))) ⁻¹) · (fun-ap (λ p → (H (f x) · p)) (right-inv (H x) ⁻¹) ·
                                (((concat-assoc (H (f x)) (H x) (inv-path (H x)) ) ⁻¹) · ( fun-ap (λ p → (p) · (inv-path (H x)))
                                (fun-ap (λ q → (H (f x)) · q ) (ap-id (H x)) · homotopy-naturality f (id A) H (H x)) 
                               · (concat-assoc (fun-ap f (H x)) (H (id A x)) (inv-path (H x)) ·
                               (fun-ap (λ q → (fun-ap f (H x)) · q) (right-inv (H x))
                               · refl-r _)))))

    Σ-eq-is-contr : {l1 : Level} (A : Type l1) (a : A) → is-Contr (Σ[ x ∶ A ] (a ≡ x))
    Σ-eq-is-contr A a = (a ,, refl a) ,, λ { (x ,, refl .x) → refl _}

 {-   is-an-equiv-to-is-Contr-fib : {l1 l2 : Level} (A : Type l1) (B : Type l2) (f : A → B) → (is-an-equiv f) → (is-Contr-fib f)
    is-an-equiv-to-is-Contr-fib A B f ((g1 ,, h1) , (g2 ,, h2)) b = ((g1 b) ,, (h1 b)) ,, λ { (a ,, refl .(f a)) → {!!}}  -}


    l-homotopy : {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B} (P :  is-an-equiv f) → ( ((f ∘ (proj₁ ( pr₁ P))) ∼ (id _) ))
    l-homotopy P = proj₂ (pr₁ P)

    r-homotopy : {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B} (P :  is-an-equiv f) → ( (((proj₁ ( pr₂ P)) ∘ f) ∼ (id _) ))
    r-homotopy P = proj₂ (pr₂ P)

    equiv-qinv : {l1 l2 : Level} {A : Type l1} {B : Type l2} {f : A → B} (P :  is-an-equiv f) → (B → A)
    equiv-qinv ((g ,, x₃) , y) = g

    ≃-qinv : {l1 l2 : Level} {A : Type l1} {B : Type l2} → (A ≃ B) → (B → A)
    ≃-qinv (x ,, ((g ,, x₃) , x₂)) = g


    functions-into-𝟘-give-equivs : {l : Level} {A : Type l} → (f : A → 𝟘) → (is-an-equiv f) 
    functions-into-𝟘-give-equivs f = is-Contr-fib-to-is-an-equiv _ _ f λ { ()}


    equiv-to-𝟘-given-func : {l : Level} {A : Type l} → (f : A → 𝟘) → (A ≃ 𝟘)
    equiv-to-𝟘-given-func f = f ,, (functions-into-𝟘-give-equivs f)

    𝟘-+-are-equiv : (𝟘 + 𝟘) ≃ 𝟘
    𝟘-+-are-equiv = (λ { (inl x) → x ; (inr x) → x}) ,, functions-into-𝟘-give-equivs _

    +-with-𝟘-is-hom-id : {l : Level} (A : Type l) → (𝟘 + A) ≃ A
    +-with-𝟘-is-hom-id A = (λ { (inl x) → ind𝟘 _ x ; (inr x) → x}) ,, ((inr ,, λ a → refl _) , (inr ,, (λ {(inr x) → refl _})))

    +-switch : {l1 l2 : Level} {A : Type l1} {B : Type l2} → (A + B) → (B + A)
    +-switch (inl x) = inr x
    +-switch (inr x) = inl x

    +-is-hom-comm : {l1 l2 : Level} (A : Type l1) (B : Type l2) → ( (A + B) ≃ (B + A))
    +-is-hom-comm A B = +-switch ,, ((+-switch ,, (λ { (inl x) → refl _ ; (inr x) → refl _})) , (+-switch  ,, (λ { (inl x) → refl _ ; (inr x) → refl _})))

    +-hom-assoc : {l1 l2 l3 : Level} (A : Type l1) (B : Type l2) (C : Type l3) → ((A + B) + C) ≃ (A + (B + C))
    +-hom-assoc A B C = (λ {  (inl (inl x)) → inl x ; (inl (inr x)) → inr (inl x) ; (inr x) → inr (inr x)})
                      ,, (((λ { (inl x) → inl ( inl x) ; (inr (inl x)) → inl (inr x) ; (inr (inr x)) → inr x}) ,, λ { (inl x) → refl _ ; (inr (inl x)) → refl _ ; (inr (inr x)) → refl _}) ,
                      (((λ { (inl x) → inl ( inl x) ; (inr (inl x)) → inl (inr x) ; (inr (inr x)) → inr x})) ,, (λ { (inl (inl x)) → refl _ ; (inl (inr x)) → refl _ ; (inr x) → refl _})))

    id-comp-is-id : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) {a : A} → (f ∘ (id _)) a ≡ f a
    id-comp-is-id f = refl _

    comp-of-equiv-is-an-equiv : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} (f : A → B) (g : B → C) → (is-an-equiv f) → (is-an-equiv g) → (is-an-equiv (g ∘ f))
    comp-of-equiv-is-an-equiv f g ((f1 ,, p1) , (f2 ,, p2)) ((g1 ,, q1) , (g2 ,, q2)) = (( f1 ∘ g1 ) ,, λ c →
                                                                                  (fun-comp-assoc (g1) (f1) (g ∘ f) c · (((fun-comp-assoc f1 f g (g1 c)) ⁻¹) · (fun-ap g (p1 (g1 c)) · (fun-ap g ((id-comp-is-id g1) ) · q1 c))))) ,
                                                                                  ((f2 ∘ g2) ,, λ a → ((fun-comp-assoc f g (f2 ∘ g2) a · ( ((fun-comp-assoc g g2 f2 (f a)))⁻¹)) · (fun-ap f2 (q2 (f a)) · p2 a)))



    is-equiv-trans : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} → (A ≃ B) → (B ≃ C) → (A ≃ C)
    is-equiv-trans (f ,, x₁) (g ,, x₃) = (g ∘ f) ,, comp-of-equiv-is-an-equiv f g x₁ x₃

    equiv-refl : {l1 : Level} (A : Type l1) → A ≃ A
    equiv-refl A = (id _) ,, (((id _) ,, (λ x → refl _)) , ((id _) ,, (λ x → refl _)))

    equiv-symm : {l1 l2 : Level} {A : Type l1} {B : Type l2} → (A ≃ B) → (B ≃ A)
    equiv-symm {_} {_} {A} {B} (f ,, ((g1 ,, hg1) , (g2 ,, hg2))) = g2 ,, ((f ,, (λ x → hg2 x)) ,
                                              (f ,, (λ (x : B) →  transp  (λ (h : B → A) → (f ∘ h) x ≡ (id B) x)
                                              (qinverses-are-equal-with-funext f ( ((g1 ,, hg1) , (g2 ,, hg2)))) (hg1 x))))

    refl-to-equiv : {l1 : Level} {A B : Type l1} → (A ≡ B) → (A ≃ B)
    refl-to-equiv {l1} {A} {A} (refl _) = equiv-refl {l1} A 

    id-is-an-equiv : {l1 : Level} {A : Type l1} → is-an-equiv (id A)
    id-is-an-equiv = (id _ ,, λ x → refl _) , ((id _) ,, (λ x → refl _))

    _+fun_ : {l1 l2 l3 l4 : Level} {A : Type l1} {B : Type l2} {C : Type l3} {D : Type l4} (f : A → B) (g : C → D) → ( (A + C) → (B + D) )
    f +fun g = λ { (inl x) → inl (f x) ; (inr x) → inr (g x)}

    hom-refl : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) → f ∼ f
    hom-refl f x = refl _

    hom-sym : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f g : A → B) → f ∼ g  → g ∼ f
    hom-sym f g H x = (H x) ⁻¹

    hom-trans : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f g h : A → B) → f ∼ g → g ∼ h → f ∼ h
    hom-trans f g h H1 H2 x = H1 x · H2 x

    hom-hor-comp : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} (f g : A → B) (h k : B → C) → f ∼ g → h ∼ k → (h ∘ f) ∼ (k ∘ g)
    hom-hor-comp f g h k H1 H2 x = transp (λ y → h (f x) ≡ h y) (H1 x) (refl _) · transp {_} {_} {_ → _}  (λ (y : _ → _) →  ((y (g x) ≡ ((k ∘ g)) x ))) {k} {h} (funext _ _ (λ x₁ → H2 _) ⁻¹) (refl _)

    +fun-pres-equivs : {l1 l2 l3 l4 : Level} {A : Type l1} {B : Type l2} {C : Type l3} {D : Type l4} {f : A → B} {g : C → D} → (is-an-equiv f) → (is-an-equiv g) → (is-an-equiv (f +fun g))
    +fun-pres-equivs ((f1 ,, hf1) , (f2 ,, hf2)) ((g1 ,, hg1) , (g2 ,, hg2)) = ((f1 +fun g1) ,, λ { (inl x) → fun-ap inl (hf1 x) ; (inr x) → fun-ap inr (hg1 x)}) ,
                                                                           ((f2 +fun g2) ,, λ { (inl x) → fun-ap inl (hf2 x) ; (inr x) → fun-ap inr (hg2 x)})

    +-preserves-equivs : {l1 l2 l3 l4 : Level} {A : Type l1} {B : Type l2} {C : Type l3} {D : Type l4} → (A ≃ B) → (C ≃ D) → (A + C) ≃ (B + D)
    +-preserves-equivs (f1 ,, p1) (f2 ,, p2) = (f1 +fun f2) ,, (+fun-pres-equivs p1 p2)

    ×-with-𝟘-is-hom-id : {l1 : Level} {A : Type l1} → (𝟘 × A) ≃ 𝟘
    ×-with-𝟘-is-hom-id = equiv-to-𝟘-given-func (λ { (() , x₁)})

    _×fun_ : {l1 l2 l3 l4 : Level} {A : Type l1} {B : Type l2} {C : Type l3} {D : Type l4} (f : A → B) (g : C → D) → ( (A × C) → (B × D) )
    f ×fun g = λ { (x , x₁) → (f x) , (g x₁)}

    ×-switch : {l1 l2 : Level} {A : Type l1} {B : Type l2} → (A × B) → (B × A)
    ×-switch (x , x₁) = x₁ , x

    prod-id-to-×-id : {l1 l2 : Level} {A : Type l1} {B : Type l2} → (x y : A × B) → (pr₁ x ≡ pr₁ y) → (pr₂ x ≡ pr₂ y) → x ≡ y
    prod-id-to-×-id (x1 , x2) (.(pr₁ (x1 , x2)) , .(pr₂ (x1 , x2))) (refl .(pr₁ (pr₁ (x1 , x2) , pr₂ (x1 , x2)))) (refl .(pr₂ (pr₁ (x1 , x2) , pr₂ (x1 , x2)))) = refl _

    ×fun-pres-equivs : {l1 l2 l3 l4 : Level} {A : Type l1} {B : Type l2} {C : Type l3} {D : Type l4} {f : A → B} {g : C → D} → (is-an-equiv f) → (is-an-equiv g) → (is-an-equiv (f ×fun g))
    ×fun-pres-equivs ((f1 ,, hf1) , (f2 ,, hf2)) ((g1 ,, hg1) , (g2 ,, hg2)) = ((f1 ×fun g1) ,, (λ { (x , y) → prod-id-to-×-id _ _ (hf1 x) (hg1 y)})) ,
                                                                                ((f2 ×fun g2) ,, (λ { (x , y) → prod-id-to-×-id _ _ (hf2 x) (hg2 y)}))

    ×-preserves-equivs : {l1 l2 l3 l4 : Level} {A : Type l1} {B : Type l2} {C : Type l3} {D : Type l4} → (A ≃ B) → (C ≃ D) → (A × C) ≃ (B × D)
    ×-preserves-equivs (f ,, p1) (g ,, p2) = (f ×fun g) ,, ×fun-pres-equivs p1 p2

    ×-hom-comm : {l1 l2 : Level} (A : Type l1) (B : Type l2) → ( (A × B) ≃ (B × A))
    ×-hom-comm A B = ×-switch ,, ((×-switch ,, (λ { (x , x₁) → refl _})) , (×-switch ,, (λ { (x , x₁) → refl _})))

    ×-hom-assoc :  {l1 l2 l3 : Level} (A : Type l1) (B : Type l2) (C : Type l3) → ((A × B) × C) ≃ (A × (B × C))
    ×-hom-assoc A B C = (λ { ((a , b) , c) → (a , (b , c))}) ,, (((λ { (a , (b , c)) → ((a , b) , c)}) ,, λ { (a , (b , c)) → refl _}) ,
                                                              (((λ { (a , (b , c)) → ((a , b) , c)})) ,, (λ { ((x , x₂) , x₁) → refl _})))

    ×-hom-distrib-over-+ :  {l1 l2 l3 : Level} (A : Type l1) (B : Type l2) (C : Type l3) → (A × (B + C)) ≃ ((A × B) + (A × C))
    ×-hom-distrib-over-+ A B C = (λ { (x , inl x₁) → inl (x , x₁) ; (x , inr x₁) → inr ( x , x₁)}) ,,
                           (((λ { (inl (x , x₁)) →  ( x , inl x₁) ; (inr (x , x₁)) → (x , inr x₁)}) ,, λ { (inl (x , x₁)) → refl _ ; (inr (x , x₁)) → refl _}) ,
                           (((λ { (inl (x , x₁)) →  ( x , inl x₁) ; (inr (x , x₁)) → (x , inr x₁)})) ,, (λ { (x , inl x₁) → refl _ ; (x , inr x₁) → refl _})))

    ×-with-𝟙-is-hom-id : {l1 : Level} (C : Type l1) → (C × 𝟙) ≃ C
    ×-with-𝟙-is-hom-id C = (λ { (x , pt) → x}) ,, (((λ x → (x , pt)) ,, λ x → refl _) , (((λ x → (x , pt))) ,, λ { (x , pt) → refl _}))


    refl-to-id : {l1 : Level} {A B : Type l1} → (A ≡ B) → (A ≃ B)
    refl-to-id (refl _) = equiv-refl _

-- Universal properties section

    u-mor-coprod : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} → (A → C) → (B → C) → (A + B → C)
    u-mor-coprod f g (inl x) = f x
    u-mor-coprod f g (inr x) = g x

    [_,_] : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} → (A → C) → (B → C) → (A + B → C)
    [ f , g ] = u-mor-coprod f g

    u-mor-coprod-up-to-eq :  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} {D : Type (l1 ⊔ l2)} (p : A + B ≡ D) → (D → C) → (D → C) → (D → C)
    u-mor-coprod-up-to-eq (refl .(_ + _)) f g = [ f ∘ inl , g ∘ inr ]

    constructor-el-+ : {l1 l2 : Level} {A : Type l1} {B : Type l2} (x : A + B) → (Σ[ a ∶ A ] ( x ≡ inl a)) + (Σ[ b ∶ B ] (x ≡ inr b))
    constructor-el-+ (inl x) = inl (x ,, refl _)
    constructor-el-+ (inr x) = inr (x ,, (refl _))

    constructor-el-𝟙 : (x : 𝟙) → (x ≡ pt)
    constructor-el-𝟙 pt = refl _
    
    l-type-+ :  {l1 l2 : Level} (A : Type l1) (B : Type l2) {D : Type (l1 ⊔ l2)} (p : A + B ≡ D) → Type l1
    l-type-+ A B (refl .(_ + _)) = A

    r-type-+ :  {l1 l2 : Level} (A : Type l1) (B : Type l2) {D : Type (l1 ⊔ l2)} (p : A + B ≡ D) → Type l2
    r-type-+ A B (refl .(A + B)) = B

    id-up-to-eq : {l1 : Level} {A B : Type l1} (p : A ≡ B) → A → B
    id-up-to-eq (refl _) = id _
    
    u-mor-coprod-qinverse : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} → (A + B → C) → ((A → C) × (B → C))
    u-mor-coprod-qinverse f = (λ x → f (inl x)) , λ x → f (inr x)

    functions-from-+-from-uni-prop : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} (f : A + B → C) → Σ[ F ∶ ((A → C) × (B → C)) ] (f ≡ [ (pr₁ F) , (pr₂ F) ])
    functions-from-+-from-uni-prop f = (u-mor-coprod-qinverse f) ,, funext _ _ λ { (inl x) → refl _ ; (inr x) → refl _}

    +-qinv-eq :  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {D : Type l3} (f : A + B → D) → f ≡ [ pr₁ (u-mor-coprod-qinverse f) , pr₂ (u-mor-coprod-qinverse f) ]
    +-qinv-eq f = funext _ _ λ { (inl x) → refl _ ; (inr x) → refl _}

    id-from-uni-prop-gives-inl : {l1 l2 : Level} {A : Type l1} {B : Type l2} → (pr₁ (proj₁ (functions-from-+-from-uni-prop (id (A + B))))) ≡ (inl)
    id-from-uni-prop-gives-inl = refl _

    inl-from-uni-prop-gives-inl :  {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} →
                                   (pr₁ (proj₁ (functions-from-+-from-uni-prop {_} {_} {_} {A} {B} {(A + B) + C}  (inl)))) ≡ inl ∘ inl
    inl-from-uni-prop-gives-inl = refl _

    comp-with-+-mor : {l1 l2 l3 l4 : Level} {A : Type l1} {B : Type l2} {C : Type l3} {D : Type l4} (g : A + B → C) (f : C → D) → (pr₁ (proj₁ (functions-from-+-from-uni-prop (f ∘ g)))) ≡  (f ∘ pr₁ (proj₁ (functions-from-+-from-uni-prop g)))
    comp-with-+-mor g f = refl _

--  functions-from-+-up-to-eq-from-uni-prop : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {D : Type (l1 ⊔ l2)} {C : Type l3} (p : A + B ≡ D) (f : D → C) → Σ[ F ∶ (((l-type-+ A B D) → C) × ((r-type-+ A B D) → C)) ] (f ≡ )

    u-mor-prod : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} → (C → A) → (C → B) → (C → A × B)
    u-mor-prod f g c = (f c) , (g c)

    <_,_> : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} → (C → A) → (C → B) → (C → A × B)
    < f , g > = λ c → u-mor-prod f g c

    u-mor-prod-qinverse : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} →  (C → A × B) →  ((C → A) × (C → B))
    u-mor-prod-qinverse  f = (λ x → pr₁ (f x)) , λ x → pr₂ (f x)

    functions-from-×-from-uni-prop : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} (f : C → A × B) → Σ[ F ∶ ((C → A) × (C → B)) ] (f ≡ < (pr₁ F) , (pr₂ F) >)
    functions-from-×-from-uni-prop f = u-mor-prod-qinverse f ,, funext _ _ λ c → ind× (λ x → x ≡ ((pr₁ x , pr₂ x))) (λ a b → refl _) (f c)

    𝟙-is-Contr : is-Contr 𝟙
    𝟙-is-Contr = pt ,, λ { pt → refl _}

    𝟘-is-Prop : is-Prop 𝟘
    𝟘-is-Prop = λ { ()}

    𝟘-fun-Prop : {l : Level} {A : Type l} → is-Prop (𝟘 → A)
    𝟘-fun-Prop = λ {x y → funext x y λ { ()}}

    𝟙-fun-Prop : {l : Level} {A : Type l} → is-Prop (A → 𝟙)
    𝟙-fun-Prop = λ x y → funext x y (λ x₁ → is-Contr-then-is-Prop _ 𝟙-is-Contr (x x₁) (y x₁))

    n-ary-binary-fun : {l1 : Level} {A : Type l1} (f : A × A → A) (z : A) (x : A) (n : ℕ) → A
    n-ary-binary-fun f z x zero = z
    n-ary-binary-fun f z x (succ n) = f ((n-ary-binary-fun f z x n) , x)

    curry : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} → (A × B → C) → (A → (B → C))
    curry f a b = f (a , b)

    uncurry : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} → (A → (B → C)) →  (A × B → C)
    uncurry f (a , b) = f a b

    curry-pr-eq : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} (g : A × B → C) (x : A × B) →
                  (g x ≡ curry g (pr₁ x) (pr₂ x))
    curry-pr-eq g (x , y) = refl _

    curry-pointwise : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} (f : A → B → C) (x : A × B) →
                                                                                   f (pr₁ x) (pr₂ x) ≡ (uncurry f) x
    curry-pointwise f (x , y) = refl _
    


-- A type is characterized by the homset from the terminal object

    type-equiv-homset : {l : Level} {A : Type l} → ((𝟙 → A) ≃ A)
    type-equiv-homset = (λ f → f pt) ,, (((λ { a x → a}) ,, λ x → refl _) ,
                                       ((λ a x → a) ,, λ x → funext (λ x₁ → x pt) (x) λ { pt → refl _}))

-- Left coleg of a double coproduct is the universal morphism from the left coleg and identity

    uni-mor-inl : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} → inl {l1 ⊔ l2} {l3} {A + B} {C} ≡ [ (inl ∘ inl) , inl ∘ inr ]
    uni-mor-inl = funext _ _ λ { (inl x) → refl _ ; (inr x) → refl _}

-- Discrimination on constructors for +

    inl-𝟙-inr-𝟘 : {l1 l2 : Level} {A : Type l1} {B : Type l2} → (A + B) → Type lzero
    inl-𝟙-inr-𝟘 (inl x) = 𝟙
    inl-𝟙-inr-𝟘 (inr x) = 𝟘

    inl-not-inr : {l1 l2 : Level} {A : Type l1} {B : Type l2} (a : A) (b : B) → (¬ (inl a ≡ inr b))
    inl-not-inr a b = λ x → rec𝟘 _ (transp (λ k → inl-𝟙-inr-𝟘 k) x pt)

-- Contractibility of initial morphisms

    initial-mor-contr : {l1 : Level} {A : Type l1} → is-Contr (𝟘 → A)
    initial-mor-contr = (λ { ()}) ,, λ a' → funext _ _ λ { ()}

-- Decidability

    decidable : {l1 : Level} (A : Type l1) → Type l1
    decidable A = A + (¬ A)

    decidable-eq : {l1 : Level} (A : Type l1) → Type l1
    decidable-eq A = (x y : A) → ((x ≡ y) + (¬ (x ≡ y)))

    decidable-bi : {l1 : Level} {A B : Type l1} (f : A → B) (g : B → A) → (decidable A) → (decidable B)
    decidable-bi f g = f +fun λ k b → k (g b)

    𝟙-decidable : decidable 𝟙
    𝟙-decidable = inl pt

    𝟘-decidable : decidable 𝟘
    𝟘-decidable = inr (id _)

    Eqℕ-decidable : (n m : ℕ) → decidable (Eqℕ n m)
    Eqℕ-decidable zero zero = 𝟙-decidable
    Eqℕ-decidable zero (succ m) = 𝟘-decidable
    Eqℕ-decidable (succ n) zero = 𝟘-decidable
    Eqℕ-decidable (succ n) (succ m) = Eqℕ-decidable n m

    ℕ-decidable-eq : decidable-eq ℕ
    ℕ-decidable-eq n m = decidable-bi (≡-Eqℕ n m) (Eqℕ-≡ n m) (Eqℕ-decidable n m)

    decidable-prod : {l1 l2 : Level} {A : Type l1} {B : Type l2} (p1 : decidable A) (p2 : decidable B) → decidable (A × B)
    decidable-prod (inl x) (inl y) = inl (x , y)
    decidable-prod (inl x) (inr f) = inr λ { (a , b) →  f b}
    decidable-prod (inr f) p2 = inr (λ { (a , x₁) → f a})

    cases : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} (C : Type l3) (p : A + B) → (A → C) → (B → C) → C
    cases C p f g = [ f , g ] p

-- We need cases evaluation proofs

    cases-inl : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} (C : Type l3) (f : A → C) (g : B → C) (a : A) → (cases _ (inl a) f g) ≡ f a
    cases-inl C f g a = refl _

-- Total maps and fundamental theorem of identity types

    tot : {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {C : A → Type l3} (f : (x : A) → B x → C x) → Σ[ x ∶ A ] (B x) → Σ[ x ∶ A ] (C x)
    tot f (a ,, b_a) = a ,, (f a b_a)

    fibtot-equiv-map : {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {C : A → Type l3} (f : (x : A) → B x → C x) (t : Σ[ x ∶ A ] (C x)) → fib (tot f) t → fib (f (proj₁ t)) (proj₂ t)
    fibtot-equiv-map f .(tot f (x ,, y)) ((x ,, y) ,, refl .(tot f (x ,, y))) = y ,, refl _

    fibtot-equiv-qinv : {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {C : A → Type l3} (f : (x : A) → B x → C x) (t : Σ[ x ∶ A ] (C x)) →  fib (f (proj₁ t)) (proj₂ t) → fib (tot f) t
    fibtot-equiv-qinv {_} {_} {_} {_} {_} {C} f (x₁ ,, .(f x₁ x)) (x ,, refl .(proj₂ {_} {_} {_} {C} (x₁ ,, f x₁ x))) = ((x₁ ,, x)) ,, (refl _)

    fibtot-left-hom : {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {C : A → Type l3} (f : (x : A) → B x → C x) (t : Σ[ x ∶ A ] (C x))
                                                                                           → ((fibtot-equiv-qinv f t) ∘ (fibtot-equiv-map f t)) ∼ id _
    fibtot-left-hom f (x₂ ,, .(f x₂ x₁)) ((.x₂ ,, x₁) ,, refl .(x₂ ,, f x₂ x₁)) = refl _

    fibtot-r-hom : {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {C : A → Type l3} (f : (x : A) → B x → C x) (t : Σ[ x ∶ A ] (C x))
                                                                                           → ((fibtot-equiv-map f t) ∘ (fibtot-equiv-qinv f t)) ∼ id _
    fibtot-r-hom {_} {_} {_} {_} {_} {C} f (x₁ ,, .(f x₁ x)) (x ,, refl .(proj₂ {_} {_} {_} {C} (x₁ ,, f x₁ x))) = refl _

    fibtot-equiv : {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {C : A → Type l3} (f : (x : A) → B x → C x) (t : Σ[ x ∶ A ] (C x)) → fib (tot f) t ≃ fib (f (proj₁ t)) (proj₂ t)
    fibtot-equiv f t = (fibtot-equiv-map f t) ,, (((fibtot-equiv-qinv f t) ,, (fibtot-r-hom f t)) , ((fibtot-equiv-qinv f t) ,, (fibtot-left-hom f t)))

-- FINISH UP THE PROOF FOR THE POSTULATE

    postulate
      equiv-is-Contr : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) → is-an-equiv f → is-Contr-fib f

    fam-tot-equiv : {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {C : A → Type l3} (f : (x : A) → B x → C x) → ((x : A) → is-an-equiv (f x)) → (is-an-equiv (tot f))
    fam-tot-equiv f g = is-Contr-fib-to-is-an-equiv _ _ (tot f) λ t →
                                                  is-Contr-equiv (fibtot-equiv-qinv f t) (equiv-is-Contr _ (g _) _) (qinv-are-equivs (fibtot-equiv-map f t) (proj₂ (fibtot-equiv f t)))

    tot-fam-equiv : {l1 l2 l3 : Level} {A : Type l1} {B : A → Type l2} {C : A → Type l3} (f : (x : A) → B x → C x) → (is-an-equiv (tot f)) →  ((x : A) → is-an-equiv (f x))
    tot-fam-equiv f g a = is-Contr-fib-to-is-an-equiv _ _ (f a) (λ b →
                                                     is-Contr-equiv (fibtot-equiv-map f ((a ,, b))) (equiv-is-Contr _ g _) (proj₂ (fibtot-equiv f (a ,, b))))

-- Hedberg's Theorem

    refl-rel : {l1 l2 : Level} (A : Type l1) (R : A → A → Type l2) → Type (l1 ⊔ l2)
    refl-rel A R = ((a1 a2 : A) → (is-Prop (R a1 a2))) × ( (a : A) → R a a)

    Hedberg-lemma-set :  {l1 l2 : Level} {A : Type l1} (R : A → A → Type l2) → refl-rel A R  → ((a1 a2 : A) → (R a1 a2 ≃ (a1 ≡ a2))) → is-Set A
    Hedberg-lemma-set R refl-r eq-prf = λ a1 a2 p1 p2 → is-Prop-equiv (proj₁ (eq-prf a1 a2)) ((pr₁ refl-r) a1 a2) (proj₂ (eq-prf a1 a2)) p1 p2

    Hedberg-lemma : {l1 l2 : Level} {A : Type l1} (R : A → A → Type l2) → refl-rel A R → ((a1 a2 : A) → R a1 a2 → (a1 ≡ a2))  → ((a1 a2 : A) → (R a1 a2 ≃ (a1 ≡ a2)))
    Hedberg-lemma R refl-R R-id a1 a2 = R-id a1 a2 ,, tot-fam-equiv (R-id a1)
                                                      (map-Contr-equiv ((a1 ,, (pr₂ (refl-R)) a1 ) ,,
                                                                                 λ {(a' ,, p) → Σ-dep-prop-id _ _ ((pr₁ refl-R) a1) (R-id _ _ p )})
                                                      (Σ-eq-is-contr _ _) _) a2

    Hedberg-rel-set : {l1 l2 : Level} {A : Type l1} (R : A → A → Type l2) → refl-rel A R → ((a1 a2 : A) → R a1 a2 → (a1 ≡ a2)) → is-Set A
    Hedberg-rel-set R refl-r R-id = Hedberg-lemma-set R refl-r (Hedberg-lemma _ refl-r R-id)


    double-neg-rel : {l1 : Level} {A : Type l1} → refl-rel A (λ x y → (¬ (¬ (x ≡ y))))
    double-neg-rel = (λ a3 a4 x y → funext _ _ λ x₁ → 𝟘-is-Prop _ _)
                           ,
                           (λ a f → f (refl _))

    
    double-neg-to-set : {l1 : Level} {A : Type l1} → ((a1 a2 : A) → ((¬ (¬ (a1 ≡ a2)))) → a1 ≡ a2) → is-Set A
    double-neg-to-set id-impl = Hedberg-rel-set (λ x x₁ → ¬(¬ (x ≡ x₁))) (double-neg-rel) id-impl

    decid-double-neg : {l1 : Level} {A : Type l1} → decidable A → (¬ (¬ A) → A)
    decid-double-neg (inl x) f = x
    decid-double-neg (inr x) f = rec𝟘 _ (f x)

    Hedberg : {l1 : Level} {A : Type l1} → decidable-eq A → is-Set A
    Hedberg decid = double-neg-to-set (λ a1 a2 → decid-double-neg (decid a1 a2))

    ℕ-is-Set : is-Set ℕ
    ℕ-is-Set = Hedberg ℕ-decidable-eq

-- Lemma for β-computation of case analysis

    prop-decidable : {l1 : Level} {A : Type l1} → is-Prop A → is-Prop (decidable A)
    prop-decidable P (inl x) (inl y) = fun-ap inl (P x y)
    prop-decidable P (inl x) (inr f) = rec𝟘 _ (f x)
    prop-decidable P (inr f) (inl x) = rec𝟘 _ (f x)
    prop-decidable P (inr f) (inr g) = fun-ap inr (funext f g λ x → rec𝟘 _ (f x))
    
 
-- Observational equality for ℕ addtional lemmas

    Eqℕ-Prop : (n m : ℕ) → is-Prop (Eqℕ n m)
    Eqℕ-Prop zero zero = is-Contr-then-is-Prop 𝟙 𝟙-is-Contr
    Eqℕ-Prop (succ n) zero ()
    Eqℕ-Prop (succ n) (succ m) = Eqℕ-Prop n m

    constr-dep-ℕ : ℕ → Type lzero
    constr-dep-ℕ zero = 𝟘
    constr-dep-ℕ (succ n) = 𝟙

    succ-not-zero : (n : ℕ) → (¬ (zero ≡ (succ n)))
    succ-not-zero n x = transp constr-dep-ℕ (x ⁻¹) pt


    eval : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) (a : A) → B
    eval f a = f a

    dep-eval : {l1 l2 : Level} {A : Type l1} {B : A → Type l2} (f : (a : A) → B a) (a : A) → B a
    dep-eval f a = f a

    succ-not-dsucc : (n : ℕ) → (¬ (n ≡ succ n))
    succ-not-dsucc zero = succ-not-zero zero
    succ-not-dsucc (succ n) p {- succ n == succ succ n -} = rec𝟘 _ (eval ((succ-not-dsucc n ∘ ≡-Eqℕ n (succ n)) ∘ (Eqℕ-≡ (succ n) (succ (succ n)))) p)

    feq-ptfeq : {l1 l2 : Level} {A : Type l1} {B : Type l2} (f g : A → B) → (f ≡ g) → (f ∼ g)
    feq-ptfeq f .f (refl .f) = λ x → refl _

-- Disjointness of products

    Type-disjoint : {l1 l2 l3 : Level} {A : Type l1} {B : Type l2} {C : Type l3} (f : C → A) (g : C → B) → (inl ∘ f ≡ inr ∘ g) → (C → 𝟘)
    Type-disjoint f g p c = rec𝟘 _ (inl-not-inr (f c) (g c) (feq-ptfeq _ _ p c))
    

-- Univalence module. Note that it will not be used to prove the FinSet equivalence as our formulation of the type of leveled categories uses UIP

  module Univalence where
    open Basics public

    postulate
      Univalence : {l1 : Level} {A B : Type l1} → (is-an-equiv (refl-to-id {l1} {A} {B}))

    ua : {l1 : Level} {A B : Type l1} → (A ≃ B) → (A ≡ B)
    ua = proj₁ (pr₁ Univalence)

    postulate
      Univalence-elim : {l1 : Level} {A B : Type l1} → ( (refl-to-id {l1} {A} {B}) ≡ (λ p → (transp (λ X → A ≃ X) p (equiv-refl A))))
      Univalence-compeq : {l1 : Level} {A B : Type l1} (p : A ≡ B) → ( p ≡ (ua( (λ p → (transp (λ X → A ≃ X) p (equiv-refl A))) p) ))
      Univalence-compfun : {l1 l2 : Level} {A B : Type l1} (f : A → B) (P : is-an-equiv f) (a : A) → (proj₁ ((refl-to-id {l1} {A} {B}) (ua (f ,, P))) a) ≡ f   a 

  


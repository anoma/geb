{-# OPTIONS --with-K --exact-split --cumulativity #-}
 
open import Agda.Primitive using (Level; lzero; lsuc; _β_; SetΟ)

module finset where

  import HoTT

  open HoTT.Basics

-- We first introduce the standard definition of FinSet as well as a structure of what will later proven to be the morphisms

  Fin : (n : β) β Type lzero
  Fin zero = π
  Fin (succ zero) = π
  Fin (succ (succ n)) = (Fin (succ n)) + π

-- Read as: elements of FinSet are types A with some proof that there exists a natural number n with a n equivalence (working with UIP+funext think of it as a bijection) of Fin n and A.
-- We need not care in this context about (-1)-truncating. On the categorical level it will make no diffrence up to equivalence.

  FinSet : Type (lsuc lzero)
  FinSet = Ξ£[ A-n βΆ ((Type lzero) Γ β) ] (Fin (prβ A-n) β prβ A-n)

-- Fin k for every k is actually a decidable type, which is important for our purposes. In order to establish that, we need observation equality of the finite types

  Eq-Fin : (k : β) β Fin k β Fin k β Type lzero
  Eq-Fin zero = Ξ» x xβ β π
  Eq-Fin (succ zero) = Ξ» x xβ β π
  Eq-Fin (succ (succ k)) = Ξ» { (inl x) (inl y) β Eq-Fin (succ k) x y ;
                              (inl x) (inr y) β π
                              ;
                              (inr x) (inl y) β π ; 
                              (inr x) (inr y) β π}

  Eq-Fin-refl : (k : β) (x : Fin k) β Eq-Fin k x x
  Eq-Fin-refl (succ zero) x = pt
  Eq-Fin-refl (succ (succ k)) (inl x) = Eq-Fin-refl (succ k) x 
  Eq-Fin-refl (succ (succ k)) (inr x) = pt

  β‘-Eq-Fin : (k : β) (x y : Fin k) β (x β‘ y) β Eq-Fin k x y
  β‘-Eq-Fin k x .x (refl .x) = Eq-Fin-refl k x

  Eq-Fin-β‘ : (k : β) (x y : Fin k) β (Eq-Fin k x y) β (x β‘ y)
  Eq-Fin-β‘ (succ zero) pt pt = Ξ» x β refl _
  Eq-Fin-β‘ (succ (succ k)) (inl x) (inl y) = (fun-ap inl) β (Eq-Fin-β‘ _ x y)
  Eq-Fin-β‘ (succ (succ k)) (inl x) (inr y) = Ξ» xβ β recπ _ xβ
  Eq-Fin-β‘ (succ (succ k)) (inr x) (inl y) = Ξ» xβ β recπ _ xβ
  Eq-Fin-β‘ (succ (succ k)) (inr pt) (inr pt) = Ξ» x β refl _

  Eq-Fin-decidable : (k : β) (x y : Fin k) β decidable (Eq-Fin k x y)
  Eq-Fin-decidable (succ zero) x y = π-decidable
  Eq-Fin-decidable (succ (succ k)) (inl x) (inl y) = Eq-Fin-decidable _ x y
  Eq-Fin-decidable (succ (succ k)) (inl x) (inr y) = π-decidable
  Eq-Fin-decidable (succ (succ k)) (inr x) (inl y) = π-decidable
  Eq-Fin-decidable (succ (succ k)) (inr x) (inr y) = π-decidable

  Fin-decidable-eq : (k : β) β decidable-eq (Fin k)
  Fin-decidable-eq k x y = decidable-bi (Eq-Fin-β‘ k x y) (β‘-Eq-Fin k x y) (Eq-Fin-decidable k x y)
  
-- Now we specify the morphisms
                             
  MorFinSet : FinSet β FinSet β Type (lzero)
  MorFinSet A B =  prβ (projβ A) β prβ (projβ B)

  -- We also introduce appropriate notions of products and coproducts

  sum-of-finsets : (n m : β) β ( ((Fin n) + (Fin m)) β (Fin (n +β m)))
  sum-of-finsets zero m = +-with-π-is-hom-id _
  sum-of-finsets (succ zero) zero = is-equiv-trans (+-is-hom-comm _ _) (+-with-π-is-hom-id _)
  sum-of-finsets (succ zero) (succ m) = +-is-hom-comm _ _
  sum-of-finsets (succ (succ n)) zero = is-equiv-trans (+-is-hom-comm _ _) (is-equiv-trans (+-with-π-is-hom-id _) (equiv-symm (is-equiv-trans (+-is-hom-comm _ _)
                                        (transp (Ξ» k β ((π + Fin (succ k)) β (Fin (succ (succ n))))) ((right-unit-law-add-β _) β»ΒΉ) (+-is-hom-comm _ _)))))
  sum-of-finsets (succ (succ n)) (succ zero) = transp (Ξ» k β (((Fin (succ n) + π) + π) β (Fin (succ k) + π))) ((right-succ-law-add-β _ _) β»ΒΉ)
                                               (transp (Ξ» k β (((Fin (succ n) + π) + π) β ((Fin (succ k) + π) + π))) ((right-unit-law-add-β _) β»ΒΉ) (equiv-refl _))
  sum-of-finsets (succ (succ n)) (succ (succ m)) = transp
                                                     (Ξ» k β
                                                        ((Fin (succ n) + π) + (Fin (succ m) + π)) β (Fin (succ k) + π))
                                                     (right-succ-law-add-β _ _ β»ΒΉ) (is-equiv-trans ((+-hom-assoc (Fin (succ n)) π (Fin (succ m) + π)))
                                                     (is-equiv-trans (+-preserves-equivs (equiv-refl _) (+-is-hom-comm π (Fin (succ m) + π)))
                                                     (is-equiv-trans (equiv-symm (+-hom-assoc (Fin (succ n)) (Fin (succ m) + π) π))
                                                     (is-equiv-trans (+-preserves-equivs (equiv-symm (+-hom-assoc (Fin (succ n)) (Fin (succ m)) π)) (refl-to-equiv (refl π)))
                                                     (+-preserves-equivs (+-preserves-equivs (sum-of-finsets (succ n) (succ m)) (refl-to-equiv (refl π))) (refl-to-equiv (refl π)))))))


  
  prod-of-finsets : (n m : β) β ( ((Fin n) Γ (Fin m)) β (Fin (n Β·β m)))
  prod-of-finsets zero m = Γ-with-π-is-hom-id
  prod-of-finsets (succ zero) m = is-equiv-trans (Γ-hom-comm _ _) (Γ-with-π-is-hom-id _)
  prod-of-finsets (succ (succ n)) m = is-equiv-trans (Γ-hom-comm _ _) (is-equiv-trans (Γ-hom-distrib-over-+ (Fin m) (Fin (succ n)) π)
                                     (is-equiv-trans (+-preserves-equivs (is-equiv-trans (Γ-hom-comm (Fin m) (Fin (succ n))) (prod-of-finsets (succ n) m))
                                     (Γ-with-π-is-hom-id (Fin m))) (sum-of-finsets ((succ n) Β·β m) m)))

  _βF_ : FinSet β FinSet β FinSet
  ((A , n) ,, x) βF ((B , m) ,, y) = ((A + B) , (n +β m)) ,, is-equiv-trans (equiv-symm (sum-of-finsets n m)) (+-preserves-equivs (x) y)

  _βF_ : FinSet β FinSet β FinSet
  ( (A , n) ,, x) βF ((B , m) ,, y) = ((A Γ B) , (n Β·β m)) ,, is-equiv-trans (equiv-symm (prod-of-finsets n m)) (Γ-preserves-equivs x y)

  -- We show the fact that these indeed define (co)product of types up to propositional equality

  βF-gives-coprod : (x y : FinSet) β Ξ£[ A βΆ Type lzero ] (Ξ£[ B βΆ Type lzero ] (prβ (projβ (x βF y)) β‘ (A + B)))
  βF-gives-coprod ((A , xβ) ,, xβ) ((B , xβ) ,, xβ) = A ,, (B ,, refl _)

  βF-gives-prod : (x y : FinSet) β Ξ£[ A βΆ Type lzero ] (Ξ£[ B βΆ Type lzero ] (prβ (projβ (x βF y)) β‘ (A Γ B)))
  βF-gives-prod ((A , xβ) ,, xβ) ((B , xβ) ,, xβ) = A ,, (B ,, (refl _))

  -- As well as give categorical names to universal morphisms given by induction

  u-mor-+-FinSet : (x y z : FinSet) β MorFinSet x z β MorFinSet y z β MorFinSet (x βF y) z
  u-mor-+-FinSet ((A , xβ) ,, xβ) ((B , xβ) ,, xβ) z f g = Ξ» { (inl x) β f x ; (inr x) β g x}

  u-mor-Γ-FinSet : (x y z : FinSet) β MorFinSet z x β MorFinSet z y β MorFinSet z (x βF y)
  u-mor-Γ-FinSet ((A , xβ) ,, xβ) ((B , xβ) ,, xβ) z f g = Ξ» x β f x , g x

  lleg-+-FinSet : (x y : FinSet) β MorFinSet (x) (x βF y)
  lleg-+-FinSet ((A , xβ) ,, xβ) ((B , xβ) ,, xβ) = inl

  rleg-+-FinSet : (x y : FinSet) β MorFinSet y (x βF y)
  rleg-+-FinSet ((A , xβ) ,, xβ) ((B , xβ) ,, xβ) = inr

  lleg-Γ-Finset : (x y : FinSet) β MorFinSet (x βF y) x
  lleg-Γ-Finset ((A , xβ) ,, xβ) ((B , xβ) ,, xβ) = prβ
  
  rleg-Γ-Finset : (x y : FinSet) β MorFinSet (x βF y) y
  rleg-Γ-Finset ((A , xβ) ,, xβ) ((B , xβ) ,, xβ) = prβ

-- ...and distribution

  distribution-Finset : (x y z : FinSet) β MorFinSet (x βF (y βF z)) ((x βF y) βF (x βF z))
  distribution-Finset ((A , xβ) ,, xβ) ((B , xβ) ,, xβ) ((C , n) ,, e) = Ξ» { (x , inl y') β inl (x ,  y') ; (x , inr z') β inr (x , z')}

-- Below are some additional functions to play with concerning establishig the skeleton of FinSet up to propositional equivalence. We supply the proper skeleton in the sections below

  β¨F-one : (n : β) β FinSet
  β¨F-one = n-ary-binary-fun (uncurry (_βF_)) ((π , zero) ,, refl-to-equiv (refl _)) ((π , one) ,, refl-to-equiv (refl π))

  Fin-as-obj-of-FinSet : (n : β) β FinSet
  Fin-as-obj-of-FinSet n = ((Fin n) , n) ,, (refl-to-equiv (refl _) )

  descent-to-skeleton : {x y : FinSet} β MorFinSet x y β MorFinSet (Fin-as-obj-of-FinSet (prβ (projβ x))) (Fin-as-obj-of-FinSet (prβ (projβ y)))
  descent-to-skeleton {(x , n) ,, (f1 ,, (h1 , h2))} {(y , m) ,, (f2 ,, ((g ,, h3) , h4))} f = (g β f) β f1


-- Also need decidability for the exponential object:

  exp-prod-Fin : (n m : β) β Fin (expβ n (succ (succ m))) β Fin (expβ (n) (succ m)) Γ Fin n
  exp-prod-Fin n m = β-qinv (prod-of-finsets _ n)

  Fin-exp-fun : (n m : β) β Fin (expβ n m) β (Fin m β Fin n)
  Fin-exp-fun n zero y = Ξ» x β recπ _ x
  Fin-exp-fun n (succ zero) = Ξ» { x y β x}
  Fin-exp-fun n (succ (succ m)) = Ξ» { x (inl y) β recΓ {_} {_} {_} {Fin (expβ n (succ m))} {Fin n} (Fin n) (Ξ» xβ xβ β Fin-exp-fun n (succ m) xβ y) (exp-prod-Fin n m x)
                                    ; x (inr y) β recΓ {_} {_} {_} {Fin (expβ n (succ m))} {Fin n} (Fin n) (Ξ» xβ xβ β  xβ) (exp-prod-Fin n m x)}

  fun-exp-Fin : (n m : β) β (Fin m β Fin n) β Fin (expβ n m)
  fun-exp-Fin n zero = Ξ» x β pt
  fun-exp-Fin n (succ zero) = Ξ» f β f pt
  fun-exp-Fin n (succ (succ m)) = ((β-qinv (equiv-symm (prod-of-finsets (expβ n (succ m)) n))) β < fun-exp-Fin n (succ m) β prβ , (Ξ» f β f pt) β prβ >) β u-mor-coprod-qinverse

-- We define observational equalities for Fin n β Fin m which will rely on decidable types
-- Alternatively, one may construct embeddings via proving that the above maps are equivalences

  EqFinMor : (n m : β) (f g : Fin n β Fin m) β Type lzero
  EqFinMor zero m f g = π
  EqFinMor (succ zero) m f g = f pt β‘ g pt
  EqFinMor (succ (succ n)) m f g = (EqFinMor _ _ (prβ (u-mor-coprod-qinverse f)) (prβ (u-mor-coprod-qinverse g))) Γ (EqFinMor _ _ (prβ (u-mor-coprod-qinverse f)) (prβ (u-mor-coprod-qinverse g)) )

  EqFinMor-β‘ : (n m : β) (f g : Fin n β Fin m) β EqFinMor n m f g β f β‘ g
  EqFinMor-β‘ zero m f g k = is-Contr-then-is-Prop _ initial-mor-contr _ _
  EqFinMor-β‘ (succ zero) m f g k = funext _ _ Ξ» { pt β k}
  EqFinMor-β‘ (succ (succ n)) m f g (a , b) = (+-qinv-eq f) Β·
                                             ((fun-ap (Ξ» k β [ k , prβ (u-mor-coprod-qinverse f) ]) (EqFinMor-β‘ _ _ _ _ a) Β·
                                             fun-ap (Ξ» k β [ prβ (u-mor-coprod-qinverse g) , k ]) (EqFinMor-β‘ _ _ _ _ b))
                                             Β· ((+-qinv-eq g) β»ΒΉ)) 

  EqFinMor-refl : (n  m : β) (f : Fin n β Fin m) β EqFinMor n m f f
  EqFinMor-refl zero m f = pt
  EqFinMor-refl (succ zero) m f = refl _
  EqFinMor-refl (succ (succ n)) m f = EqFinMor-refl (succ n) m _ , refl _

  β‘-EqFinMor : (n m : β) (f g : Fin n β Fin m) β f β‘ g β EqFinMor n m f g
  β‘-EqFinMor n m f .f (refl .f) = EqFinMor-refl _ _ f 

  EqFinMor-decidable : (n m : β) (f g : Fin n β Fin m) β decidable (EqFinMor n m f g)
  EqFinMor-decidable zero m f g = π-decidable
  EqFinMor-decidable (succ zero) m f g = Fin-decidable-eq m (f pt) (g pt)
  EqFinMor-decidable (succ (succ n)) m f g = decidable-prod
                                                            (EqFinMor-decidable (succ n) m (prβ (u-mor-coprod-qinverse f)) (prβ (u-mor-coprod-qinverse g)))
                                                            (EqFinMor-decidable one m (prβ (u-mor-coprod-qinverse f)) (prβ (u-mor-coprod-qinverse g)))


  FinMor-decidable-eq : (n m : β) β decidable-eq (Fin n β Fin m)
  FinMor-decidable-eq n m f g = decidable-bi (EqFinMor-β‘ n m f g) (β‘-EqFinMor n m f g) (EqFinMor-decidable n m f g)

-- And finally use Hedberg's theorem for the core result 

  FinMor-is-Set : (n m : β) β is-Set (Fin n β Fin m)
  FinMor-is-Set n m = Hedberg (FinMor-decidable-eq n m)

-- This is a function establishing an extension property: each type dependent on the skeleton can be extended canonically to the one of the entire FinSet, if one wants to work with this

  FinSet-skel : Type (lsuc lzero)
  FinSet-skel = Ξ£[ X βΆ ((Type lzero) Γ β) ] ((Fin (prβ X)) β‘ (prβ X))

  MorFinSet-skel : FinSet-skel β FinSet-skel β Type lzero
  MorFinSet-skel ((A , n) ,, x) ((B , m) ,, y) = A β B

  FinSet-collapse : FinSet β FinSet-skel
  FinSet-collapse ((A , n) ,, e) = ((Fin n) , n) ,, (refl _)

  extend-from-skeleton : {l1 : Level} (P : FinSet-skel β Type l1) β (FinSet β Type l1)
  extend-from-skeleton P = P β FinSet-collapse

-- Similarly we have a way to canonically restrict types over FinSet to the types over skeleton
  
  skel-into-FinSet : FinSet-skel β FinSet
  skel-into-FinSet ((A , n) ,, eq) = (A , n) ,, refl-to-equiv eq

  restrict-to-skeleton : {l1 : Level} (P : FinSet β Type l1) β (FinSet-skel β Type l1)
  restrict-to-skeleton P = P β skel-into-FinSet

  open import uip-cat

  FinSet-cat : cat-w-level (lsuc lzero) (lzero)
  FinSet-cat = FinSet ,,
                    (MorFinSet ,,
                    (_β_ ,,
                    ((Ξ» A β id _) ,,
                    ((Ξ» A B f g β refl _ , refl _) , Ξ» A B C D f g h β refl _))))

-- We use the representation of the skeleton of FinSet as Ο, the ordinal category

  MorΟ : (x y : β) β Type lzero
  MorΟ x y = Fin x β Fin y

  Ο-cat : cat-w-level lzero lzero
  Ο-cat = β ,, (MorΟ ,, (_β_ ,, ((Ξ» A x β x) ,, ((Ξ» A B f g β refl _ , refl _) , Ξ» A B C D f g h β refl _))))

  Ο-to-FinSet-obj : β β FinSet
  Ο-to-FinSet-obj n = Fin-as-obj-of-FinSet n

  Ο-to-FinSet-mor : (n m : β) β (MorΟ n m) β (MorFinSet (Ο-to-FinSet-obj n) (Ο-to-FinSet-obj m))
  Ο-to-FinSet-mor n m f = f

  FinSet-to-Ο-obj : FinSet β β
  FinSet-to-Ο-obj ((A , n) ,, y) = n

  FinSet-to-Ο-mor : (x y : FinSet) β (MorFinSet x y) β (MorΟ (FinSet-to-Ο-obj x) (FinSet-to-Ο-obj y))
  FinSet-to-Ο-mor ((A , n) ,, e) ((B , m) ,, e2) f = projβ (equiv-symm e2) β (f β projβ e)

  distrib-Fin : (n m k : β) β (Fin (n Β·β (m +β k))) β (Fin ((n Β·β m) +β (n Β·β k)))
  distrib-Fin n m k = (projβ (sum-of-finsets (n Β·β m) (n Β·β k))
                      β  (([ inl β  (projβ (prod-of-finsets n m)) , inr β  (projβ (prod-of-finsets n k)) ]
                      β distribution-Finset (Fin-as-obj-of-FinSet n) (Fin-as-obj-of-FinSet m) (Fin-as-obj-of-FinSet k))
                      β < prβ , ((β-qinv (sum-of-finsets m k)) β  prβ) >))
                      β β-qinv (prod-of-finsets (n) (m +β k))

-- Density of Geb-into-FinSet. Recall that by definition of morphisms of FinSet as underlying functions of types,
-- the isomorphisms of the category are equivalences of underlying types, assuming funext.

  FinSet-skel-iso : (A : FinSet) β (prβ (projβ A)) β (Fin (prβ (projβ (A))))
  FinSet-skel-iso ((A , n) ,, p) = equiv-symm p

-- We are looking at the density of the inclusion of Geb into FinSet. In particular, that means, given the above result, that every Fin (succ (succ n))
-- will be isomorphic to Fin (β¨β 1) but this follows from basic arithmetic and reflexivity of equivalences, as initial and terminal objects will be hit.

  pluses-1 : (n : β) β β
  pluses-1 zero = zero
  pluses-1 (succ zero) = one
  pluses-1 (succ (succ n)) = (pluses-1 (succ n)) +β one

  β-as-plus-one : (n : β) β n β‘ (pluses-1 n)
  β-as-plus-one zero = refl _
  β-as-plus-one (succ zero) = refl _
  β-as-plus-one (succ (succ n)) = ((fun-ap (Ξ» k β add-β k one) ((β-as-plus-one (succ n)) β»ΒΉ)) Β· ((fun-ap (Ξ» k β succ k) (right-succ-law-add-β n zero))
                                                                                               Β· fun-ap (Ξ» k β succ (succ k)) (right-unit-law-add-β _))) β»ΒΉ

-- In particular, suppose (A ,, n), p is a finite set. Then it will be isomorphic to, firstly Fin n with evident proofs of equivalence and this in turn
-- will be isomorphic to Fin (β¨β 1) := β¨Fβ (Fin 1) := β¨Fβ (π) via refl-to-equiv

  density-lemma-Geb-FinSet : (n : β) β Fin n β (Fin (pluses-1 n))
  density-lemma-Geb-FinSet n = refl-to-equiv (fun-ap (Ξ» k β Fin k) (β-as-plus-one n))

  βF-func : (A B : FinSet) β ( (prβ (projβ (A βF B))) β‘ ((prβ (projβ A)) + (prβ (projβ B))))
  βF-func ((A , n) ,, pA) ((B , m) ,, pB) = refl _

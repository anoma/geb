{-# OPTIONS --with-K --exact-split --cumulativity #-}
 
open import Agda.Primitive using (Level; lzero; lsuc; _β_; SetΟ)

module geb where

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

-- Point choice equality

-- We now introduce the canonical representation of the initial category of Geb 


  data ObjGEBCat : Type lzero where
    Init : ObjGEBCat                                 
    Term : ObjGEBCat                                     
    _βG_ : ObjGEBCat β ObjGEBCat β ObjGEBCat   
    _βG_ : ObjGEBCat β ObjGEBCat β ObjGEBCat


  data _β¦_ : ObjGEBCat β ObjGEBCat β Type lzero where
    _β_ : {x y z : ObjGEBCat} β (y β¦ z) β (x β¦ y) β (x β¦ z)
    IdMor : (x : ObjGEBCat) β (x β¦ x)
    InitMor : (x : ObjGEBCat) β (Init β¦ x)
    TermMor : (x : ObjGEBCat) β (x β¦ Term)
    CoProdMor : {x y z : ObjGEBCat} β (x β¦ z) β (y β¦ z) β ((x βG y) β¦ z)
    ProdMor : {x y z : ObjGEBCat} β (z β¦ x) β (z β¦ y) β ( z β¦ (x βG y))
    DistribMor : {x y z : ObjGEBCat} β ( (x βG (y βG z)) β¦ ( (x βG y) βG (x βG z) ))
    inlG : {x y : ObjGEBCat} β (x β¦ (x βG y))
    inrG : {x y : ObjGEBCat} β (y β¦ (x βG y))
    p1G : {x y : ObjGEBCat} β ((x βG y) β¦ x)
    p2G : {x y : ObjGEBCat} β ((x βG y) β¦ y)

-- We make this into a type by moving the variables out of the context

  data GebMorphType : Type lzero where
    HomGeb : (x y : ObjGEBCat) (f : x β¦ y) β (GebMorphType)

-- Note that this is a Ξ£-type (using Ξ·). This is equivalent to Ξ£[ x : ObjGEBCat ] (Ξ£ [ y : ObjGEBCat ] (x β¦ y)) which essentially covers all the info regarding the homsets. 

  Comp : {x y z : ObjGEBCat} β (x β¦ y) β (y β¦ z) β (x β¦ z)
  Comp f g = g β f

  [_,_]G :  {x y z : ObjGEBCat} β (x β¦ z) β (y β¦ z) β ((x βG y) β¦ z)
  [ f , g ]G = CoProdMor f g

  <_,_>G :  {x y z : ObjGEBCat} β (z β¦ x) β (z β¦ y) β ( z β¦ (x βG y))
  < f , g >G = ProdMor f g

  prod-cone : {x y z :  ObjGEBCat} β Type lzero
  prod-cone {x} {y} {z} = (z β¦ x) Γ (z β¦ y)

  data MorCollGEBCat : Type lzero where
    coll : (x y : ObjGEBCat) β (x β¦ y) β MorCollGEBCat


  is-an-intern-iso : {x y : ObjGEBCat} β  (x β¦ y)  β Type lzero  
  is-an-intern-iso {x} {y} f = Ξ£[ g βΆ y β¦ x ] (((g β f) β‘ (IdMor x) ) Γ ((f β g) β‘ (IdMor y)))


  _βG_ : ObjGEBCat β ObjGEBCat β Type (lzero)
  x βG y = Ξ£[ f βΆ x β¦ y ] (is-an-intern-iso f)
  
-- We add freely the axioms making the above a category with needed universal properties. As our formalization of category theory happens in MLTT+UIP these do not introduce extra structure.

  postulate
    InitMorAx : {x : ObjGEBCat} (f : Init β¦ x) β (f β‘ InitMor x)
    TermMorAx : {x : ObjGEBCat} (f : x β¦ Term) β (f β‘ TermMor x)
    IdMorAx : {x y : ObjGEBCat} (f : x β¦ y) β ( (IdMor y) β f β‘ f ) Γ ( f β (IdMor x) β‘ f)
    CompAssocAx : {A B C D : ObjGEBCat} (f : A β¦ B) (g : B β¦ C) (h : C β¦ D) β (h β (g β f)) β‘ ((h β g) β f)
    CoProdMorAx : {x y z : ObjGEBCat} β is-Contr-fib (uncurry ([_,_]G {x} {y} {z}))
    ProdMorAx : {x y z : ObjGEBCat} β is-Contr-fib (uncurry (<_,_>G {x} {y} {z}))
    CoProdMorLegAx : {x y z : ObjGEBCat} β (f : x β¦ z) β (g : y β¦ z) β ( [ f , g ]G β inlG β‘ f ) Γ ( [ f , g ]G β inrG β‘ g)
    ProdMorLegAx : {x y z : ObjGEBCat} β (f : z β¦ x) β (g : z β¦ y) β ( (p1G β < f , g >G) β‘ f) Γ ( p2G β < f , g >G β‘ g)
    DistribAx : {x y z : ObjGEBCat} β is-an-intern-iso (DistribMor {x} {y} {z})

  IdMor-is-iso : {x : ObjGEBCat} β is-an-intern-iso (IdMor x)
  IdMor-is-iso {x} = deppair (IdMor x) (IdMorAx (IdMor x))

-- Iso props

  iniso-comp : {x y z : ObjGEBCat} (f : x β¦ y) (g : y β¦ z) β is-an-intern-iso (f) β is-an-intern-iso (g) β is-an-intern-iso (g β f)
  iniso-comp f g (f' ,, (p1 , p2)) (g' ,, (pg1 , pg2)) = (f' β g') ,,
                                                         ((CompAssocAx _ _ _ Β· (fun-ap (Ξ» k β k β f) ((CompAssocAx _ _ _) β»ΒΉ)
                                                         Β· (fun-ap (Ξ» k β (f' β k) β f) pg1 Β· ((fun-ap (Ξ» k β k β f) (prβ (IdMorAx _))) Β· p1))))
                                                         ,
                                                         ((CompAssocAx _ _ _ ) Β· ((fun-ap (Ξ» k β k β g') ((CompAssocAx _ _ _) β»ΒΉ))
                                                         Β· ((fun-ap (Ξ» k β (g β k) β g') p2) Β· (fun-ap (Ξ» k β k β g') (prβ (IdMorAx _)) Β· pg2)))))

  βG-trans : {x y z : ObjGEBCat} β (x βG y) β (y βG z) β (x βG z)
  βG-trans (f ,, (f' ,, (pf1 , pf2))) (g ,, (g' ,, (pg1 , pg2))) = (g β f) ,, iniso-comp f g ((f' ,, (pf1 , pf2))) ((g' ,, (pg1 , pg2)))


-- A needed property will be the instantiation that the colimit legs are jointly epi as well as some usual composition lemmas for universal morphisms

  mors-from-βG-come-from-coprod : {x y z : ObjGEBCat} (f : (x βG y) β¦ z) β Ξ£[ fg βΆ ((x β¦ z) Γ (y β¦ z))] (uncurry ([_,_]G) fg β‘ f)
  mors-from-βG-come-from-coprod f = projβ (projβ (CoProdMorAx f)) ,,  (projβ (projβ (CoProdMorAx f)))

  βG-mor-fib : {x y z : ObjGEBCat} (f : (x βG y) β¦ z) β Ξ£[ fg βΆ ((x β¦ z) Γ (y β¦ z))]  ([ (prβ fg) , (prβ fg) ]G β‘ f)
  βG-mor-fib f = ( projβ (projβ (CoProdMorAx f))) ,, (curry-pointwise ([_,_]G) (( projβ (projβ (CoProdMorAx f)))) Β· (projβ (mors-from-βG-come-from-coprod f)))

  coprod-mor-to-uni : {x y z : ObjGEBCat} β ( (x βG y) β¦ z ) β ( (x βG y) β¦ z)
  coprod-mor-to-uni f =  [ prβ ( projβ (projβ (CoProdMorAx f))) , prβ ( projβ (projβ (CoProdMorAx f))) ]G 

  

  inx-are-joint-epi : {x y z : ObjGEBCat} (f g : (x βG y) β¦ z) β ((f β inlG β‘ g β inlG) Γ (f β inrG β‘ g β inrG)) β (f β‘ g)
  inx-are-joint-epi f g (p1 , p2) = ((projβ (mors-from-βG-come-from-coprod f)) β»ΒΉ) Β·
                                    (fun-ap (uncurry ([_,_]G))
                                    (prod-id-to-Γ-id ((projβ (mors-from-βG-come-from-coprod f))) ((projβ (mors-from-βG-come-from-coprod g)))
                                    (((prβ (CoProdMorLegAx (prβ ((projβ (mors-from-βG-come-from-coprod f)))) (prβ ((projβ (mors-from-βG-come-from-coprod f)))))) β»ΒΉ) Β·
                                    (fun-ap (Ξ» F β F β inlG) ((curry-pr-eq (uncurry [_,_]G) (projβ (mors-from-βG-come-from-coprod f)) β»ΒΉ) Β·
                                    projβ (mors-from-βG-come-from-coprod f )) Β·
                                    (p1 Β· (fun-ap (Ξ» G β G β inlG) ((projβ (mors-from-βG-come-from-coprod g)) β»ΒΉ) Β·
                                    (fun-ap (Ξ» G β G β inlG) (curry-pr-eq ((uncurry [_,_]G)) (projβ (mors-from-βG-come-from-coprod g))) Β·
                                    prβ (CoProdMorLegAx (prβ ((projβ (mors-from-βG-come-from-coprod g)))) (prβ ((projβ (mors-from-βG-come-from-coprod g))))))))))
                                    ((((prβ (CoProdMorLegAx (prβ ((projβ (mors-from-βG-come-from-coprod f)))) (prβ ((projβ (mors-from-βG-come-from-coprod f)))))) β»ΒΉ)) Β·
                                    (fun-ap (Ξ» F β F β inrG) ((curry-pr-eq (uncurry [_,_]G) ((projβ (mors-from-βG-come-from-coprod f)))) β»ΒΉ) Β·
                                    ((fun-ap (Ξ» F β F β inrG) (projβ (mors-from-βG-come-from-coprod f))) Β·
                                    (p2 Β·
                                    ((fun-ap (Ξ» G β G β inrG) ( ((projβ (mors-from-βG-come-from-coprod g)) β»ΒΉ))) Β·
                                    ((fun-ap (Ξ» G β G β inrG) (curry-pr-eq ((uncurry [_,_]G)) (projβ (mors-from-βG-come-from-coprod g)))) Β·
                                    prβ ((CoProdMorLegAx (prβ ((projβ (mors-from-βG-come-from-coprod g)))) (prβ ((projβ (mors-from-βG-come-from-coprod g))))))
                                     ))))))) Β·
                                    projβ (mors-from-βG-come-from-coprod g))

  inl-as-coprod : {x y z : ObjGEBCat} β inlG {x βG y} {z} β‘ [ inlG β inlG , inlG β inrG ]G
  inl-as-coprod = inx-are-joint-epi _ _ (((prβ (CoProdMorLegAx _ _)) β»ΒΉ) , ((prβ (CoProdMorLegAx _ _)) β»ΒΉ))

  comp-with-coprod-mor : {x y z z' : ObjGEBCat} (f : x β¦ z) (g : y β¦ z) (h : z β¦ z') β (h β [ f , g ]G ) β‘ ([ h β f , h β g ]G)
  comp-with-coprod-mor f g h = inx-are-joint-epi _ _
                                                ((((CompAssocAx _ _ _) β»ΒΉ) Β· (fun-ap (Ξ» H β h β H) (prβ (CoProdMorLegAx _ _)) Β· ((prβ (CoProdMorLegAx _ _)) β»ΒΉ)))
                                                ,
                                                ((((CompAssocAx _ _ _) β»ΒΉ)) Β· (fun-ap (Ξ» H β h β H) (prβ (CoProdMorLegAx _ _)) Β· ((prβ (CoProdMorLegAx _ _)) β»ΒΉ))))

-- We provide a definition of the internal hom object the same way as in the source code to check the universal property

  InHom : ObjGEBCat β ObjGEBCat β ObjGEBCat
  InHom Init y = Term
  InHom Term y = y
  InHom (x βG x') y = (InHom x y) βG InHom x' y
  InHom (x βG x') y = InHom x (InHom x' y)

-- We use the same function as the source code does

  mid-prod-forg : {x y z : ObjGEBCat} β ((x βG y) βG z) β¦ (x βG z)
  mid-prod-forg = < p1G β p1G , p2G >G

  l-prod-forg : {x y z : ObjGEBCat} β ((x βG y) βG z) β¦ (y βG z)
  l-prod-forg = < p2G β p1G , p2G >G

  r-prod-forg : {x y z : ObjGEBCat} β ((x βG y) βG z) β¦ (x βG y)
  r-prod-forg = p1G

  r-prod-forg-r : {x y z : ObjGEBCat} β (x βG (y βG z)) β¦ (x βG y)
  r-prod-forg-r = < p1G , p1G β p2G >G


  prod-1-assoc-rl : {x y z : ObjGEBCat} β (x βG (y βG z)) β¦ ((x βG y) βG z)
  prod-1-assoc-rl = < < p1G , (p1G β p2G) >G , p2G β p2G >G

  prod-1-assoc-lr : {x y z : ObjGEBCat} β ((x βG y) βG z) β¦  (x βG (y βG z))
  prod-1-assoc-lr = < (p1G β p1G) , < (p2G β p1G) , p2G >G >G

  evalG : (x y : ObjGEBCat) β ( ((InHom x y) βG x) β¦ y )
  evalG Init y = InitMor _ β p2G
  evalG Term y = p1G
  evalG (x βG x') y = [ (evalG _ _) β mid-prod-forg , (evalG _ _) β l-prod-forg ]G β DistribMor
  evalG (x βG x') y = (evalG x' y) β (< evalG x (InHom x' y) β r-prod-forg-r , (p2G β p2G) >G)   -- or (evalG _ _ β < evalG _ _ β p1G , p2G >G) β prod-1-assoc-rl

-- We now check whether the universal property is satisfied

  Ξ»G : {x y z : ObjGEBCat} β (f : (z βG x) β¦ y) β (z β¦ InHom x y) 
  Ξ»G {Init} f = TermMor _
  Ξ»G {Term} f = f β < (IdMor _) , TermMor _ >G
  Ξ»G {x βG x'} {y} {z} f = < Ξ»G {x} {y} {z} (prβ (projβ (βG-mor-fib (f β (projβ (DistribAx {z} {x} {x'}))) )))
                           ,
                              Ξ»G {x'} {y} {z} (prβ (projβ (βG-mor-fib (f β (projβ (DistribAx {z} {x} {x'}))) ))) >G    
  Ξ»G {x βG x'} {y} {z} f = Ξ»G {x} {InHom x' y} (Ξ»G {x'} (f β prod-1-assoc-lr))

-- We also need to prove the identity preservaton and composition preservation of the above function to use in the functoriality proof

  
  IdMor-is-coprod-of-inj : {x y : ObjGEBCat} β IdMor (x βG y) β‘ [ inlG , inrG ]G
  IdMor-is-coprod-of-inj = inx-are-joint-epi _ _ ((prβ (IdMorAx inlG) Β· ((prβ (CoProdMorLegAx _ _)) β»ΒΉ)) , (prβ (IdMorAx inrG) Β· ((prβ (CoProdMorLegAx _ _)) β»ΒΉ)))




-- Moreover, we need the notions of n-ary coproducts to make sure the equivalence works well due to FinSet being spanned by π, π, and +

  β¨G : (x : ObjGEBCat) (n : β) β ObjGEBCat
  β¨G x zero = Init
  β¨G x (succ zero) = x
  β¨G x (succ (succ n)) = (β¨G x (succ n)) βG x

--  We now check that this definition coincides with the one given by the Idris implementation of Geb. One may easily see that the categories formed are isomorphic if needed universal properties are postulated. 

  data SubstObjF (A : Type lzero) : Type lzero where
    SO0 :  SubstObjF A 
    SO1 : SubstObjF A
    _!+_ :  (x y : A) β SubstObjF A
    _!*_ : (x y : A) β SubstObjF A


  data SubstObjMu : Type lzero where
    InSO : SubstObjF (SubstObjMu) β SubstObjMu

  data SubstMorph : SubstObjMu β SubstObjMu β Type lzero where
    SMId : (x : SubstObjMu) β (SubstMorph x x)
    SMComp : {x y z : SubstObjMu} β (SubstMorph y z) β (SubstMorph x y) β (SubstMorph x z)
    SMFromInit : (x : SubstObjMu) β (SubstMorph (InSO SO0) x)
    SMToTerminal : (x : SubstObjMu) β (SubstMorph x (InSO SO1))
    SMInjLeft : (x y : SubstObjMu) β (SubstMorph x ( InSO (x !+ y)))
    SMInjRight : (x y : SubstObjMu) β (SubstMorph y (InSO (x !+ y)))
    SMCase : {x y z : SubstObjMu} β (SubstMorph x z) β (SubstMorph y z) β (SubstMorph (InSO (x !+ y)) z)
    SMPair : {x y z : SubstObjMu} β (SubstMorph x y) β (SubstMorph x z) β (SubstMorph x (InSO (y !* z)))
    SMProjLeft : (x y : SubstObjMu) β (SubstMorph (InSO (x !* y)) x)
    SMProjRight : (x y : SubstObjMu) β (SubstMorph (InSO (x !* y)) y)
    SMDistrib : (x y z : SubstObjMu) β (SubstMorph (InSO (x !* ( InSO (y !+ z)))) (InSO ( (InSO (x !* y)) !+ (InSO (x !* z)))))

-- We make this into a type getting the object variables out of the context 

  data SubstMorphType : Type lzero where 
    HomSubst : (x y : SubstObjMu) (f : SubstMorph x y) β SubstMorphType



-- With this and the formalization of basic category theory in MLTT + UIP + funext we are able to produce the claim that the initial model of Geb is equivalent to FinSet

  open import uip-cat

  FinSet-cat : cat-w-level (lsuc lzero) (lzero)
  FinSet-cat = FinSet ,,
                    (MorFinSet ,,
                    (_β_ ,,
                    ((Ξ» A β id _) ,,
                    ((Ξ» A B f g β refl _ , refl _) , Ξ» A B C D f g h β refl _))))

  Geb-cat : cat-w-level (lsuc lzero) (lzero)
  Geb-cat = ObjGEBCat ,,
                      (_β¦_ ,,
                      (_β_ ,,
                      (IdMor ,,
                      ((Ξ» A B f g β (prβ (IdMorAx g)) , prβ (IdMorAx f)) , Ξ» A B C D β CompAssocAx ))))


-- We use the representation of the skeleton of FinSet as Ο, the ordinal category

  MorΟ : (x y : β) β Type lzero
  MorΟ x y = Fin x β Fin y

  Ο-cat : cat-w-level lzero lzero
  Ο-cat = β ,, (MorΟ ,, (_β_ ,, ((Ξ» A x β x) ,, ((Ξ» A B f g β refl _ , refl _) , Ξ» A B C D f g h β refl _))))

  Ο-to-Geb-obj : β β ObjGEBCat
  Ο-to-Geb-obj n = β¨G Term n

  obj-of-FinSet-to-β¨G-Term : (n : β) β (Fin n) β (Term β¦ (β¨G Term n))
  obj-of-FinSet-to-β¨G-Term zero ()
  obj-of-FinSet-to-β¨G-Term (succ zero) x = IdMor Term
  obj-of-FinSet-to-β¨G-Term (succ (succ n)) (inl x) = inlG β (obj-of-FinSet-to-β¨G-Term (succ n) x)
  obj-of-FinSet-to-β¨G-Term (succ (succ n)) (inr x) = inrG
  
  Ο-to-Geb-mor : (n m : β) (f : MorΟ n m) β (Ο-to-Geb-obj n β¦ Ο-to-Geb-obj m)
  Ο-to-Geb-mor zero m f = InitMor _
  Ο-to-Geb-mor (succ zero) m f = obj-of-FinSet-to-β¨G-Term m (f pt)
  Ο-to-Geb-mor (succ (succ n)) m f = [ Ο-to-Geb-mor (succ n) m (prβ (projβ (functions-from-+-from-uni-prop f)))
                                                    , obj-of-FinSet-to-β¨G-Term m ((prβ (projβ (functions-from-+-from-uni-prop f))) pt )]G

  case-inl-eq : {n : β} (f : MorΟ (succ n) (succ (succ n))) β (f β‘ inl) β (Ο-to-Geb-obj (succ n) β¦ Ο-to-Geb-obj (succ (succ n)))
  case-inl-eq f p = inlG

-- The problem with the above definition is that it will not give us enough information about what is happening on left inclusions
-- However, using decidability, we can establish this explicitly:

  case-inl-neq : {n : β} (f : MorΟ (succ n) (succ (succ n))) β (Β¬ (f β‘ inl)) β (Ο-to-Geb-obj (succ n) β¦ Ο-to-Geb-obj (succ (succ n)))
  case-inl-neq f np =  Ο-to-Geb-mor _ _ f

  case-β-eq : (n m : β) (f : MorΟ (succ n) m) β ((m β‘ (succ (succ n)))) β (Ο-to-Geb-obj (succ n) β¦ Ο-to-Geb-obj m)
  case-β-eq n .(succ (succ n)) f (refl .(succ (succ n))) = [ case-inl-eq f , case-inl-neq f ] (FinMor-decidable-eq _ _ f inl)

  case-β-neq : (n m : β) (f : MorΟ (succ n) m) β (Β¬ (m β‘ (succ (succ n)))) β (Ο-to-Geb-obj (succ n) β¦ Ο-to-Geb-obj m)
  case-β-neq n m f np = Ο-to-Geb-mor _ _ f

  Ο-Geb-mor-inl : (n m : β) (f : MorΟ n m) β (Ο-to-Geb-obj n β¦ Ο-to-Geb-obj m)
  Ο-Geb-mor-inl zero m f = Ο-to-Geb-mor zero m f
  Ο-Geb-mor-inl (succ n) m f = cases _ (β-decidable-eq m (succ (succ n))) (case-β-eq n m f) (case-β-neq n m f)


-- Check if needed extra 

  Ο-Geb-mor-inl' : (n m : β) (f : MorΟ n m) β (Ο-to-Geb-obj n β¦ Ο-to-Geb-obj m)
  Ο-Geb-mor-inl' zero m f =  Ο-to-Geb-mor zero m f
  Ο-Geb-mor-inl' (succ zero) m f = cases _ (β-decidable-eq m (succ (succ zero))) (case-β-eq zero m f) (case-β-neq zero m f)
  Ο-Geb-mor-inl' (succ (succ n)) m f = cases _ (β-decidable-eq m (succ (succ (succ n)))) (case-β-eq (succ n) m f) (case-β-neq (succ n) m f)


-- function as before but make it consider whether it is an injection i.e. whether m = n + 2 

  Geb-to-Ο-obj : ObjGEBCat β β
  Geb-to-Ο-obj Init = zero
  Geb-to-Ο-obj Term = succ zero
  Geb-to-Ο-obj (x βG y) = (Geb-to-Ο-obj x) +β (Geb-to-Ο-obj y)
  Geb-to-Ο-obj (x βG y) = (Geb-to-Ο-obj x) Β·β (Geb-to-Ο-obj y)

  Geb-into-FinSet-obj : ObjGEBCat β FinSet
  Geb-into-FinSet-obj Init = (π , zero) ,, refl-to-equiv (refl _)
  Geb-into-FinSet-obj Term = (π , one) ,,  refl-to-equiv (refl _)
  Geb-into-FinSet-obj (x βG y) = (Geb-into-FinSet-obj x) βF Geb-into-FinSet-obj y
  Geb-into-FinSet-obj (x βG y) = (Geb-into-FinSet-obj x) βF (Geb-into-FinSet-obj y)

  Geb-into-FinSet-mor : (a b : ObjGEBCat) β (f : a β¦ b) β (MorFinSet (Geb-into-FinSet-obj a) (Geb-into-FinSet-obj b))
  Geb-into-FinSet-mor a b (f β fβ) = (Geb-into-FinSet-mor _ _ f) β Geb-into-FinSet-mor _ _ fβ
  Geb-into-FinSet-mor a .a (IdMor .a) = Ξ» x β x
  Geb-into-FinSet-mor .Init b (InitMor .b) = Ξ» {()}
  Geb-into-FinSet-mor a .Term (TermMor .a) = Ξ» x β pt
  Geb-into-FinSet-mor (a βG a') b (CoProdMor f g) = u-mor-+-FinSet (Geb-into-FinSet-obj a) (Geb-into-FinSet-obj a') (Geb-into-FinSet-obj b) (Geb-into-FinSet-mor _ _ f) (Geb-into-FinSet-mor _ _ g)
  Geb-into-FinSet-mor a (b βG b') (ProdMor f g) = u-mor-Γ-FinSet (Geb-into-FinSet-obj b) (Geb-into-FinSet-obj b') (Geb-into-FinSet-obj a) (Geb-into-FinSet-mor _ _ f) (Geb-into-FinSet-mor _ _ g)
  Geb-into-FinSet-mor (x βG (y βG z)) .((_ βG _) βG (_ βG _)) DistribMor = distribution-Finset (Geb-into-FinSet-obj x) (Geb-into-FinSet-obj y) (Geb-into-FinSet-obj z)
  Geb-into-FinSet-mor a .(a βG _) inlG = lleg-+-FinSet (Geb-into-FinSet-obj a) _
  Geb-into-FinSet-mor a (x βG a) inrG = rleg-+-FinSet (Geb-into-FinSet-obj x) (Geb-into-FinSet-obj a)
  Geb-into-FinSet-mor .(b βG _) b p1G = lleg-Γ-Finset (Geb-into-FinSet-obj b) _
  Geb-into-FinSet-mor (x βG b) b p2G = rleg-Γ-Finset (Geb-into-FinSet-obj x) (Geb-into-FinSet-obj b)
  
  FinSet-to-Geb-obj : FinSet β ObjGEBCat
  FinSet-to-Geb-obj ((A , n) ,, e) = β¨G Term n

  FinSet-to-Geb-mor : (a b : FinSet) (f : MorFinSet a b) β ( (FinSet-to-Geb-obj a) β¦ (FinSet-to-Geb-obj b))
  FinSet-to-Geb-mor ((A , n) ,, (f1 ,, e1)) ((B , m) ,, (f2 ,, ((g1 ,, h1) , g2h))) f = Ο-to-Geb-mor n m ((g1 β f) β f1)

  Ο-to-FinSet-obj : β β FinSet
  Ο-to-FinSet-obj n = Fin-as-obj-of-FinSet n

  Ο-to-FinSet-mor : (n m : β) β (MorΟ n m) β (MorFinSet (Ο-to-FinSet-obj n) (Ο-to-FinSet-obj m))
  Ο-to-FinSet-mor n m f = f

  FinSet-to-Ο-obj : FinSet β β
  FinSet-to-Ο-obj ((A , n) ,, y) = n

  FinSet-to-Ο-mor : (x y : FinSet) β (MorFinSet x y) β (MorΟ (FinSet-to-Ο-obj x) (FinSet-to-Ο-obj y))
  FinSet-to-Ο-mor ((A , n) ,, e) ((B , m) ,, e2) f = projβ (equiv-symm e2) β (f β projβ e)

  FinSet-to-Geb-fact :  FinSet β ObjGEBCat
  FinSet-to-Geb-fact = (Ο-to-Geb-obj β FinSet-to-Ο-obj)

  FinSet-to-Geb-mor-fact : {x y : FinSet} (f : MorFinSet x y) β ((FinSet-to-Geb-fact x) β¦ (FinSet-to-Geb-fact y))
  FinSet-to-Geb-mor-fact {x} {y} f = (Ο-to-Geb-mor) _ _ (FinSet-to-Ο-mor x y f)

  distrib-Fin : (n m k : β) β (Fin (n Β·β (m +β k))) β (Fin ((n Β·β m) +β (n Β·β k)))
  distrib-Fin n m k = (projβ (sum-of-finsets (n Β·β m) (n Β·β k))
                      β  (([ inl β  (projβ (prod-of-finsets n m)) , inr β  (projβ (prod-of-finsets n k)) ]
                      β distribution-Finset (Fin-as-obj-of-FinSet n) (Fin-as-obj-of-FinSet m) (Fin-as-obj-of-FinSet k))
                      β < prβ , ((β-qinv (sum-of-finsets m k)) β  prβ) >))
                      β β-qinv (prod-of-finsets (n) (m +β k)) 

{-  Geb-to-Ο-mor : {x y : ObjGEBCat} (f : x β¦ y) β (MorΟ (Geb-to-Ο-obj x) (Geb-to-Ο-obj y))
  Geb-to-Ο-mor (f β g) = (Geb-to-Ο-mor f) β (Geb-to-Ο-mor g)
  Geb-to-Ο-mor (IdMor x) = id _
  Geb-to-Ο-mor (InitMor _) = Ξ» { ()}
  Geb-to-Ο-mor (TermMor _) = Ξ» xβ β pt
  Geb-to-Ο-mor (CoProdMor {x} {y} {z} f g) = [ Geb-to-Ο-mor f , Geb-to-Ο-mor g ] β β-qinv ((sum-of-finsets (Geb-to-Ο-obj x) (Geb-to-Ο-obj y)))
  Geb-to-Ο-mor (ProdMor f g) = projβ (prod-of-finsets _ _) β < (Geb-to-Ο-mor f) , Geb-to-Ο-mor g >
  Geb-to-Ο-mor (DistribMor {x} {y} {z}) = distrib-Fin (Geb-to-Ο-obj x) (Geb-to-Ο-obj y) (Geb-to-Ο-obj z)
  Geb-to-Ο-mor (inlG {x} {y}) = projβ (sum-of-finsets _ _) β inl
  Geb-to-Ο-mor (inrG {x} {y}) = projβ (sum-of-finsets _ _) β inr
  Geb-to-Ο-mor (p1G {x} {y}) = prβ β β-qinv ((prod-of-finsets (Geb-to-Ο-obj x) (Geb-to-Ο-obj y)))
  Geb-to-Ο-mor (p2G {x} {y}) = prβ β β-qinv ((prod-of-finsets (Geb-to-Ο-obj x) (Geb-to-Ο-obj y))) -}

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

  density-Geb-FinSet : (A : FinSet) β Ξ£[ a βΆ ObjGEBCat ] ((prβ (projβ A)) β (prβ (projβ (Geb-into-FinSet-obj a))))
  density-Geb-FinSet ((A , zero) ,, p) = Init ,, FinSet-skel-iso (((A , zero) ,, p))
  density-Geb-FinSet ((A , succ n) ,, p) = dep-eval {lsuc lzero} {lsuc lzero}
                                               (dep-eval {lsuc lzero} {lsuc lzero} (indβ (Ξ» k β (B : Type lzero) (q : (Fin (succ k) β B)) β
                                                                       Ξ£ {_} {lzero} (ObjGEBCat)
                                                                                ( Ξ» a β ((prβ {_} {lzero} {_} {_} (projβ {_} {_} {_} {Ξ» t β (Fin (prβ t)) β prβ t}
                                                                                                                         ((B , succ k) ,, q ))) β (prβ (projβ (Geb-into-FinSet-obj a))))))
                                                          (Ξ» B q β Term ,, (FinSet-skel-iso (((B , one) ,, q))))
                                                          (Ξ» n' IHs B q β ((projβ {_} {_} {_} {Ξ» a β ((prβ (projβ (Fin-as-obj-of-FinSet (succ n')))) β (prβ (projβ (Geb-into-FinSet-obj a))))}
                                                                                  (IHs (Fin (succ n')) (refl-to-equiv (refl _)))) βG Term) ,,
                                                                          is-equiv-trans (FinSet-skel-iso ((B , (succ (succ n'))) ,, q))
                                                                          (is-equiv-trans
                                                                                        (+-preserves-equivs (projβ {_} {_} {_} {Ξ» a β ((prβ (projβ (Fin-as-obj-of-FinSet (succ n')))) β (prβ (projβ (Geb-into-FinSet-obj a))))}
                                                                                                                  (IHs (Fin (succ n')) (refl-to-equiv (refl _))))
                                                                                                            (refl-to-equiv (refl π))) 
                                                                           (equiv-symm (refl-to-equiv
                                                                             (βF-func (Geb-into-FinSet-obj (projβ {_} {_} {_} {Ξ» a β ((prβ (projβ (Fin-as-obj-of-FinSet (succ n')))) β (prβ (projβ (Geb-into-FinSet-obj a))))}
                                                                                                                  (IHs (Fin (succ n')) (refl-to-equiv (refl _))))) (Fin-as-obj-of-FinSet one))))))
                                                          n)
                                               A)
                                            p

-- Note that this does not just say that our functor is essentially surjective but that it is split essentially surjective. We get structure rather then properties, so that the equivalence is rescued constructively
-- after proving that the assignment is full and faithful. 

-- Properties of coproducts and products with initial/terminal objects

  Init-coprod-iso : (x : ObjGEBCat) β (Init βG x) βG x
  Init-coprod-iso x = [ InitMor _ , IdMor _ ]G ,, (inrG ,,
                                              ((((comp-with-coprod-mor _ _ _ Β· fun-ap (Ξ» f β [ inrG β InitMor x , f ]G) (prβ (IdMorAx _)))
                                              Β· (fun-ap (Ξ» f β [ f , inrG ]G) (InitMorAx (inrG β (InitMor _)) Β· ((InitMorAx _) β»ΒΉ)))) Β· (IdMor-is-coprod-of-inj β»ΒΉ))
                                              ,
                                              prβ (CoProdMorLegAx _ _)))

-- Here is a basic observation about the morphism assignment

  term-to-mor : (n : β) (x : Fin n) β obj-of-FinSet-to-β¨G-Term n x β‘ Ο-to-Geb-mor (succ zero) (n) (Ξ» t β x)
  term-to-mor n x = refl _

-- The lemma below provides one of the main ingredients for the (n := succ (succ n)) step in the functoriality proof

  Lemma-Ο-to-Geb-mor-preserves-comp : (m k : β) (f : MorΟ m k) (g : MorΟ one m) β Ο-to-Geb-mor (one) k (f β g ) β‘  (Ο-to-Geb-mor m k f) β (Ο-to-Geb-mor (one) m g)
  Lemma-Ο-to-Geb-mor-preserves-comp = indβ (Ξ» m β  (k : β) (f : MorΟ m k) (g : MorΟ (one) m) β
                                                  Ο-to-Geb-mor (one) k (f β g) β‘
                                                  (Ο-to-Geb-mor m k f β Ο-to-Geb-mor (one) m g))
                                                  (Ξ» k f g β recπ _ (g (pt)) )
                                                  Ξ» m IH β indβ (Ξ» (m : β) β (k : β) (f : MorΟ (succ m) k) (g : MorΟ (one) (succ m)) β
                                                  Ο-to-Geb-mor (one) k (f β g) β‘
                                                  (Ο-to-Geb-mor (succ m) k f β Ο-to-Geb-mor (one) (succ m) g))
                                                  (Ξ» k f g β transp (Ξ» x β (obj-of-FinSet-to-β¨G-Term k (f (x))) β‘ (Ο-to-Geb-mor (succ zero) k f))    
                                                              ((projβ (π-is-Contr)) (g pt)) (refl _) Β· ((prβ (IdMorAx _)) β»ΒΉ))
                                                  (Ξ» m IHsm1 β Ξ» k f g β rec+ (Ξ» {(x ,, p1) β transp
                                                                                          ((Ξ» t β
                                                                                              obj-of-FinSet-to-β¨G-Term k (f t) β‘
                                                                                              (CoProdMor (Ο-to-Geb-mor (succ m) k (Ξ» xβ β f (inl xβ)))
                                                                                               (obj-of-FinSet-to-β¨G-Term k (f (inr pt)))
                                                                                               β obj-of-FinSet-to-β¨G-Term (succ (succ m)) t)))
                                                                                               (p1 β»ΒΉ) (IHsm1 _ ((f β inl)) ((Ξ» t β x)) Β·
                                                                                               (fun-ap (Ξ» F β F β obj-of-FinSet-to-β¨G-Term (succ m) x) ((prβ (CoProdMorLegAx _ _)) β»ΒΉ)
                                                                                               Β· (((CompAssocAx _ _ _) β»ΒΉ))))})
                                                                                           (Ξ» {(x ,, p1) β  transp
                                                                                          (Ξ» t β
                                                                                             obj-of-FinSet-to-β¨G-Term k (f t) β‘
                                                                                             (CoProdMor (Ο-to-Geb-mor (succ m) k (Ξ» xβ β f (inl xβ)))
                                                                                              (obj-of-FinSet-to-β¨G-Term k (f (inr pt)))
                                                                                              β obj-of-FinSet-to-β¨G-Term (succ (succ m)) t))
                                                                                          (p1 β»ΒΉ) (fun-ap (Ξ» l β obj-of-FinSet-to-β¨G-Term k (f (inr l))) (constructor-el-π x) Β· ((prβ (CoProdMorLegAx _ _)) β»ΒΉ))})
                                                                                           ((constructor-el-+ (g pt)))) m

  

  Ο-to-Geb-mor-preserves-comp : (n m k : β) (f : MorΟ m k) (g : MorΟ n m) β Ο-to-Geb-mor n k (f β g ) β‘  (Ο-to-Geb-mor m k f) β (Ο-to-Geb-mor n m g)
  Ο-to-Geb-mor-preserves-comp n = indβ (Ξ» n β (m k : β) (f : MorΟ m k) (g : MorΟ n m) β  Ο-to-Geb-mor n k (f β g) β‘  (Ο-to-Geb-mor m k f) β (Ο-to-Geb-mor n m g) )
                                  (Ξ» m k f g β (InitMorAx _) β»ΒΉ)    -- Base case on n :=0
                                  (Ξ» n IHs β indβ                  -- Double induction on n
                                               (Ξ» (n : β) β
                                                  (m k : β) (f : MorΟ m k) (g : MorΟ (succ n) m) β
                                                  Ο-to-Geb-mor (succ n) k (f β g) β‘
                                                  (Ο-to-Geb-mor m k f β Ο-to-Geb-mor (succ n) m g))
                                               ( indβ (Ξ» (m : β) β (k : β) (f : MorΟ m k) (g : MorΟ (succ zero) m) β                                           -- We now induct on m -- The middle layer corresponds to the Lemma proof
                                                            Ο-to-Geb-mor (succ zero) k (f β g ) β‘  (Ο-to-Geb-mor m k f) β (Ο-to-Geb-mor (succ zero) m g))
                                                 (Ξ» (k : β) f g β recπ _ (g (pt)))                                                                              -- Base case for n := 1, m := 0
                                                 Ξ» (m : β) (IHsm0) β indβ                                                                                       -- IHsm0 inductiv h-s
                                                               (Ξ» (m : β) β
                                                                  (k : β) (f : MorΟ (succ m) k) (g : MorΟ (succ zero) (succ m)) β
                                                                  Ο-to-Geb-mor (succ zero) k (f β g) β‘
                                                                  (Ο-to-Geb-mor (succ m) k f β Ο-to-Geb-mor (succ zero) (succ m) g))
                                                               (Ξ» k f g β transp (Ξ» x β (obj-of-FinSet-to-β¨G-Term k (f (x))) β‘ (Ο-to-Geb-mor (succ zero) k f))    
                                                              ((projβ (π-is-Contr)) (g pt)) (refl _) Β· ((prβ (IdMorAx _)) β»ΒΉ))
                                                               (Ξ» m IHsm1 β Ξ» k f g β rec+ (Ξ» {(x ,, p1) β transp
                                                                                          ((Ξ» t β
                                                                                              obj-of-FinSet-to-β¨G-Term k (f t) β‘
                                                                                              (CoProdMor (Ο-to-Geb-mor (succ m) k (Ξ» xβ β f (inl xβ)))
                                                                                               (obj-of-FinSet-to-β¨G-Term k (f (inr pt)))
                                                                                               β obj-of-FinSet-to-β¨G-Term (succ (succ m)) t)))
                                                                                               (p1 β»ΒΉ) (IHsm1 _ ((f β inl)) ((Ξ» t β x)) Β·
                                                                                               (fun-ap (Ξ» F β F β obj-of-FinSet-to-β¨G-Term (succ m) x) ((prβ (CoProdMorLegAx _ _)) β»ΒΉ)
                                                                                               Β· (((CompAssocAx _ _ _) β»ΒΉ))))})
                                                                                           (Ξ» {(x ,, p1) β  transp
                                                                                          (Ξ» t β
                                                                                             obj-of-FinSet-to-β¨G-Term k (f t) β‘
                                                                                             (CoProdMor (Ο-to-Geb-mor (succ m) k (Ξ» xβ β f (inl xβ)))
                                                                                              (obj-of-FinSet-to-β¨G-Term k (f (inr pt)))
                                                                                              β obj-of-FinSet-to-β¨G-Term (succ (succ m)) t))
                                                                                          (p1 β»ΒΉ) (fun-ap (Ξ» l β obj-of-FinSet-to-β¨G-Term k (f (inr l))) (constructor-el-π x) Β· ((prβ (CoProdMorLegAx _ _)) β»ΒΉ))})
                                                                                           ((constructor-el-+ (g pt)))) m)
                                               (Ξ» n IHsn1 β Ξ» m k f g β inx-are-joint-epi _ _
                                               ((((prβ (CoProdMorLegAx _ _))) Β· (IHsn1 m k f ((g β inl)) Β· ((((CompAssocAx _ _ _) β»ΒΉ) Β· fun-ap (Ξ» F β Ο-to-Geb-mor m k f β F) (prβ (CoProdMorLegAx _ _))) β»ΒΉ)))
                                               ,
                                               ((prβ (CoProdMorLegAx _ _)) Β· ((Lemma-Ο-to-Geb-mor-preserves-comp m k (f) (g β inr) Β· ((prβ (CoProdMorLegAx _ _)) β»ΒΉ)) Β· fun-ap (Ξ» F β F β inrG) ((comp-with-coprod-mor _ _ _) β»ΒΉ))))) n) n  -- Note the Lemma


-- One may also look at the commented-out composition preservation proof below. Agda did not recognize the recursive calls in the (n := succ zero) case

{-
  Ο-to-Geb-mor-preserves-comp : (n m k : β) (f : MorΟ m k) (g : MorΟ n m) β Ο-to-Geb-mor n k (f β g ) β‘  (Ο-to-Geb-mor m k f) β (Ο-to-Geb-mor n m g)
  Ο-to-Geb-mor-preserves-comp zero m k f g = (InitMorAx _) β»ΒΉ
  Ο-to-Geb-mor-preserves-comp (succ zero) zero k f g = recπ _ (g (pt))
  Ο-to-Geb-mor-preserves-comp (succ zero) (succ zero) k f g = transp (Ξ» x β (obj-of-FinSet-to-β¨G-Term k (f (x))) β‘ (Ο-to-Geb-mor (succ zero) k f))
                                                              ((projβ (π-is-Contr)) (g pt)) (refl _) Β· ((prβ (IdMorAx _)) β»ΒΉ) 
  Ο-to-Geb-mor-preserves-comp (succ zero) (succ (succ m)) k f g = rec+  (Ξ» { (x ,, p1) β transp
                                                                                           (Ξ» t β
                                                                                              obj-of-FinSet-to-β¨G-Term k (f t) β‘
                                                                                              (CoProdMor (Ο-to-Geb-mor (succ m) k (Ξ» xβ β f (inl xβ)))
                                                                                               (obj-of-FinSet-to-β¨G-Term k (f (inr pt)))
                                                                                               β obj-of-FinSet-to-β¨G-Term (succ (succ m)) t))
                                                                                           (p1 β»ΒΉ) (((refl _ Β·
                                                                                           Ο-to-Geb-mor-preserves-comp (succ zero) (succ m) k (f β inl) (Ξ» t β x))
                                                                                           Β· fun-ap (Ξ» F β F β obj-of-FinSet-to-β¨G-Term (succ m) x)
                                                                                           (prβ (CoProdMorLegAx _ _) β»ΒΉ))
                                                                                           Β· ((CompAssocAx _ _ _ _ _ _ _) β»ΒΉ))})
                                                                        (Ξ» {(x ,, p1) β transp
                                                                                          (Ξ» t β
                                                                                             obj-of-FinSet-to-β¨G-Term k (f t) β‘
                                                                                             (CoProdMor (Ο-to-Geb-mor (succ m) k (Ξ» xβ β f (inl xβ)))
                                                                                              (obj-of-FinSet-to-β¨G-Term k (f (inr pt)))
                                                                                              β obj-of-FinSet-to-β¨G-Term (succ (succ m)) t))
                                                                                          (p1 β»ΒΉ) (fun-ap (Ξ» l β obj-of-FinSet-to-β¨G-Term k (f (inr l))) (constructor-el-π x) Β· ((prβ (CoProdMorLegAx _ _)) β»ΒΉ))})
                                                                        (constructor-el-+ (g pt))
  Ο-to-Geb-mor-preserves-comp (succ (succ n)) m k f g =  inx-are-joint-epi _ _
                                                           ((prβ (CoProdMorLegAx _ _) Β· (Ο-to-Geb-mor-preserves-comp (succ n) m k (f) (g β inl) Β· ((prβ (CoProdMorLegAx _ _)) β»ΒΉ)))
                                                           , ((prβ (CoProdMorLegAx _ _)) Β· (Ο-to-Geb-mor-preserves-comp (succ (zero)) m k (f) (g β inr) Β· ((prβ (CoProdMorLegAx _ _)) β»ΒΉ))))
                                                           Β· ((comp-with-coprod-mor _ _ _) β»ΒΉ)
-}

-- A good indication for the equivalence to actually suceed is that the coproduct structure is preserved. For that we need some extra lemmas

  Ο-to-Geb-mor-preserves-coprod-mor : (n m : β) (f : Fin (succ n) β Fin m) (g : π β Fin m) β Ο-to-Geb-mor (succ (succ n)) m ([ f , g ]) β‘ [ Ο-to-Geb-mor _ _ f , Ο-to-Geb-mor _ _ g ]G
  Ο-to-Geb-mor-preserves-coprod-mor n m f g = inx-are-joint-epi _ _
                                                               ((((prβ (CoProdMorLegAx _ _))  Β· ((prβ (CoProdMorLegAx _ _)) β»ΒΉ)))
                                                               ,
                                                               ((prβ (CoProdMorLegAx _ _)) Β· ((prβ (CoProdMorLegAx _ _)) β»ΒΉ)))

  Ο-Geb-mor-inl-pres :  (n : β) β Ο-Geb-mor-inl (succ n) (succ (succ n)) inl β‘ inlG
  Ο-Geb-mor-inl-pres zero = refl _
  Ο-Geb-mor-inl-pres (succ n) = fun-ap (Ξ» k β cases _ k (case-β-eq (succ n) (succ (succ (succ n))) inl) (case-β-neq _ _ inl ))
                                       (prop-decidable (β-is-Set (succ (succ (succ n))) (succ (succ (succ n)))) (β-decidable-eq _ _) (inl (refl _)))
                               Β· (fun-ap (Ξ» k β [ case-inl-eq inl , case-inl-neq inl ] k)
                                         (prop-decidable (FinMor-is-Set _ _ inl inl) (FinMor-decidable-eq _ _ _ _) (inl (refl inl))))

-- Proofs that the Geb category is spanned by coproducts of TermMor

  βG-pres-iso : {a b c d : ObjGEBCat} (iso1 : a βG b) (iso2 : c βG d) β (a βG c) βG (b βG d)
  βG-pres-iso iso1 iso2 = [ (inlG β (projβ (iso1))) , (inrG β (projβ (iso2))) ]G ,,
                                   ([ (inlG β (projβ (projβ iso1))) , (inrG β (projβ (projβ iso2))) ]G ,,
                                       ((((comp-with-coprod-mor _ _ _) Β· inx-are-joint-epi _ _
                                                                        ((prβ (CoProdMorLegAx _ _) Β·
                                                                        (((CompAssocAx _ _ _) Β·
                                                                        ((fun-ap (Ξ» f β f β projβ iso1) (prβ (CoProdMorLegAx _ _))) Β·
                                                                        (((CompAssocAx _ _ _) β»ΒΉ) Β·
                                                                        (fun-ap (Ξ» f β inlG β f) (prβ (projβ (projβ iso1)))
                                                                        Β· prβ (IdMorAx _)))))
                                                                        Β· ((prβ (CoProdMorLegAx _ _)) β»ΒΉ)))
                                                                        ,
                                                                        (prβ (CoProdMorLegAx _ _) Β·
                                                                        (CompAssocAx _ _ _ Β·
                                                                        ((fun-ap (Ξ» f β f β projβ iso2) (prβ (CoProdMorLegAx _ _)) Β·
                                                                        (((CompAssocAx _ _ _) β»ΒΉ) Β·
                                                                        (fun-ap (Ξ» f β inrG β f) (prβ (projβ (projβ (iso2))))
                                                                        Β· prβ (IdMorAx _)))) Β·
                                                                        ((prβ (CoProdMorLegAx _ _)) β»ΒΉ))))))
                                              Β· (IdMor-is-coprod-of-inj β»ΒΉ))
                                      ,
                                         (((comp-with-coprod-mor _ _ _) Β· inx-are-joint-epi _ _
                                                                          (((prβ (CoProdMorLegAx _ _)) Β· (CompAssocAx _ _ _
                                                                          Β· ((fun-ap (Ξ» f β f β projβ (projβ iso1)) (prβ (CoProdMorLegAx _ _))
                                                                          Β· (((CompAssocAx _ _ _) β»ΒΉ)
                                                                          Β· ((fun-ap (Ξ» f β inlG β f) (prβ (projβ (projβ iso1))))
                                                                          Β· prβ (IdMorAx _))))
                                                                          Β· ((prβ (CoProdMorLegAx _ _)) β»ΒΉ))))
                                                                          ,
                                                                          (((prβ (CoProdMorLegAx _ _))
                                                                          Β· (CompAssocAx _ _ _
                                                                          Β· ((fun-ap (Ξ» f β f β projβ (projβ iso2)) (prβ (CoProdMorLegAx _ _)))
                                                                          Β· (((CompAssocAx _ _ _) β»ΒΉ)
                                                                          Β· ((fun-ap (Ξ» f β inrG β f) (prβ (projβ (projβ (iso2)))))
                                                                          Β· prβ (IdMorAx _))))))
                                                                          Β· ((prβ (CoProdMorLegAx _ _)) β»ΒΉ))))
                                         Β· (IdMor-is-coprod-of-inj β»ΒΉ))))

  βG-refl : {a : ObjGEBCat} β a βG a
  βG-refl = (IdMor _) ,, IdMor-is-iso

  βG-symm : {a b : ObjGEBCat} β (a βG b) β (b βG a)
  βG-symm (f ,, (g ,, (p1 , p2))) = g ,, (f ,, (p2 , p1))

  βG-1comm : {a b : ObjGEBCat} β ((a βG b) βG (b βG a))
  βG-1comm = [ inrG , inlG ]G ,,
               ([ inrG , inlG ]G ,,
                  ((inx-are-joint-epi _ _
                                         ((((CompAssocAx _ _ _) β»ΒΉ) Β· ((fun-ap (Ξ» f β [ inrG , inlG ]G β f) (prβ (CoProdMorLegAx _ _)))
                                         Β· ((prβ (CoProdMorLegAx _ _)) Β· (prβ (IdMorAx _) β»ΒΉ))))
                                         ,
                                         (((CompAssocAx _ _ _) β»ΒΉ) Β· ((fun-ap (Ξ» f β [ inrG , inlG ]G β f) (prβ (CoProdMorLegAx _ _)))
                                         Β· ((prβ (CoProdMorLegAx _ _)) Β· ((prβ (IdMorAx _)) β»ΒΉ))))))
                  ,
                  inx-are-joint-epi _ _
                                        ((((CompAssocAx _ _ _) β»ΒΉ) Β· ((fun-ap (Ξ» f β [ inrG , inlG ]G β f) (prβ (CoProdMorLegAx _ _)))
                                        Β· ((prβ (CoProdMorLegAx _ _)) Β· ((prβ (IdMorAx _)) β»ΒΉ))))
                                        ,
                                        (((CompAssocAx _ _ _) β»ΒΉ) Β· ((fun-ap (Ξ» f β [ inrG , inlG ]G β f) (prβ (CoProdMorLegAx _ _)))
                                        Β· ((prβ (CoProdMorLegAx _ _)) Β· ((prβ (IdMorAx _)) β»ΒΉ)))))))

  βG-1assoc : {a b c : ObjGEBCat} β (((a βG b) βG c) βG (a βG (b βG c)))
  βG-1assoc = [ [ inlG , inrG β inlG ]G , (inrG β inrG) ]G ,,
                 ([ (inlG β inlG) , [ (inlG β inrG) , inrG ]G ]G ,,
                     (((comp-with-coprod-mor _ _ _) Β· inx-are-joint-epi _ _
                                                                       (((prβ (CoProdMorLegAx _ _)) Β· ((comp-with-coprod-mor _ _ _)
                                                                       Β· inx-are-joint-epi _ _
                                                                                           (((prβ (CoProdMorLegAx _ _)) Β· (prβ (CoProdMorLegAx _ _)
                                                                                           Β· transp (Ξ» k β (inlG β inlG) β‘ (k β inlG))
                                                                                                    ((prβ (IdMorAx _)) β»ΒΉ) (refl _)))
                                                                                           ,
                                                                                           (prβ (CoProdMorLegAx _ _) Β· (CompAssocAx _ _ _
                                                                                           Β· ((fun-ap (Ξ» f β f β inlG) (prβ (CoProdMorLegAx _ _)))
                                                                                           Β· ((prβ (CoProdMorLegAx _ _))
                                                                                           Β· transp (Ξ» k β (inlG β inrG) β‘ (k β inrG)) ((prβ (IdMorAx _)) β»ΒΉ) (refl _))))))))
                                                                       ,
                                                                       ((prβ (CoProdMorLegAx _ _)) Β· ((CompAssocAx _ _ _) Β· ((fun-ap (Ξ» f β f β inrG) (prβ (CoProdMorLegAx _ _)))
                                                                       Β· ((prβ (CoProdMorLegAx _ _)) Β· ((prβ (IdMorAx _)) β»ΒΉ)))))))
                     ,
                     (comp-with-coprod-mor _ _ _ Β· inx-are-joint-epi _ _
                                                                    ((prβ (CoProdMorLegAx _ _) Β· ((CompAssocAx _ _ _) Β· ((fun-ap (Ξ» f β f β inlG) (prβ (CoProdMorLegAx _ _)))
                                                                    Β· (prβ (CoProdMorLegAx _ _) Β· ((prβ (IdMorAx _)) β»ΒΉ)))))
                                                                    ,
                                                                    inx-are-joint-epi _ _
                                                                                      (((fun-ap (Ξ» f β f β inlG) (prβ (CoProdMorLegAx _ _))) Β· (fun-ap (Ξ» f β f β inlG) (comp-with-coprod-mor _ _ _)
                                                                                      Β· ((prβ (CoProdMorLegAx _ _)) Β· ((CompAssocAx _ _ _) Β· ((fun-ap (Ξ» f β f β inrG) (prβ (CoProdMorLegAx _ _)))
                                                                                      Β· ((prβ (CoProdMorLegAx _ _)) Β· (transp (Ξ» k β (inrG β inlG) β‘ ((k) β inlG)) ((prβ (IdMorAx _)) β»ΒΉ) (refl _))))))))
                                                                                      ,
                                                                                      ((fun-ap (Ξ» f β f β inrG) (prβ (CoProdMorLegAx _ _))) Β· (fun-ap (Ξ» f β f β inrG) (comp-with-coprod-mor _ _ _)
                                                                                      Β· ((prβ (CoProdMorLegAx _ _)) Β· ((prβ (CoProdMorLegAx _ _)) Β· (transp (Ξ» k β (inrG β inrG) β‘ (k β inrG)) ((prβ (IdMorAx _)) β»ΒΉ) (refl _)))))))))))
 
  Gebskel-βG-lemma : {a b : ObjGEBCat} (n m : β) (iso1 : a βG β¨G Term n) (iso2 : b βG β¨G Term m) β ( (a βG b) βG (β¨G Term (n +β m)))
  Gebskel-βG-lemma zero m  iso1 iso2 = βG-trans (βG-pres-iso iso1 iso2) (Init-coprod-iso _)
  Gebskel-βG-lemma (succ zero) zero iso1 iso2 = βG-trans (βG-pres-iso iso1 iso2)
                                                          (βG-trans βG-1comm (Init-coprod-iso Term))
  Gebskel-βG-lemma (succ zero) (succ m) iso1 iso2 = βG-trans (βG-pres-iso iso1 iso2) βG-1comm
  Gebskel-βG-lemma (succ (succ n)) m iso1 iso2 = βG-trans (βG-pres-iso iso1 iso2)
                                                           (βG-trans βG-1assoc
                                                                      (βG-trans (βG-pres-iso βG-refl βG-1comm)
                                                                                 (βG-trans (βG-symm βG-1assoc) (βG-pres-iso (Gebskel-βG-lemma (succ n) m βG-refl βG-refl)
                                                                                                                               βG-refl))))

  βG-mor' : {x y z : ObjGEBCat} (f : z β¦ (x βG y)) β Ξ£[ fg βΆ ((z β¦ x) Γ (z β¦ y))] (uncurry (<_,_>G) fg β‘ f)
  βG-mor' f = (projβ (projβ (ProdMorAx f))) ,, (projβ (projβ (ProdMorAx f)))

-- Add more natural axioms for universal properties

  postulate
    ProdUniAx : {x y z : ObjGEBCat} (f1 : z β¦ x) (f2 : z β¦ y) (g : z β¦ (x βG y)) β ( f1 β‘ p1G β g) β ( f2 β‘ p2G β g) β < f1 , f2 >G β‘ g
    CoProdUniAx : {x y z : ObjGEBCat} (f1 : x β¦ z) (f2 : y β¦ z) (g : (x βG y) β¦ z) β (f1 β‘ g β inlG) β (f2 β‘ g β inrG) β [ f1 , f2 ]G β‘ g

  βG-mor-fun :  {x y z : ObjGEBCat} β (g : z β¦ (x βG y)) β (z β¦ (x βG y))
  βG-mor-fun g = < (p1G β g) , (p2G β g) >G

  βG-mor-eq : {x y z : ObjGEBCat} β (g : z β¦ (x βG y)) β (βG-mor-fun g β‘ g)
  βG-mor-eq g = ProdUniAx _ _ _ (refl _) (refl _)

  pr-joint-mono : {x y z : ObjGEBCat} ( f g : z β¦ (x βG y)) β ((p1G β f) β‘ (p1G β g)) Γ ((p2G β f) β‘ (p2G β g)) β (f β‘ g)
  pr-joint-mono f g (p1 , p2) = ((βG-mor-eq f) β»ΒΉ) Β· ProdUniAx _ _ _ p1 p2

  prod-comp : {x y z z' : ObjGEBCat} (f : z β¦ z') (f1 : z' β¦ x) (f2 : z' β¦ y)  β < f1 , f2 >G β f β‘ < f1 β f , f2 β f >G
  prod-comp f f1 f2 = pr-joint-mono _ _
                                    (((CompAssocAx _ _ _) Β· ((fun-ap (Ξ» k β k β f) (prβ (ProdMorLegAx _ _))) Β· ((prβ (ProdMorLegAx _ _)) β»ΒΉ)))
                                    ,
                                    ((CompAssocAx _ _ _) Β· ((fun-ap (Ξ» k β k β f) (prβ (ProdMorLegAx _ _))) Β· ((prβ (ProdMorLegAx _ _)) β»ΒΉ))))

  βG-pres-iso : {a b c d : ObjGEBCat} (iso1 : a βG b) (iso2 : c βG d) β (a βG c) βG (b βG d)
  βG-pres-iso iso1 iso2 = < projβ (iso1) β p1G , projβ (iso2) β p2G >G ,,
                              (< projβ (projβ (iso1 )) β p1G  , (projβ (projβ (iso2))) β p2G >G
                                    ,,   (((prod-comp _ _ _) Β· pr-joint-mono _ _
                                                                            (((prβ (ProdMorLegAx _ _)) Β· (((CompAssocAx _ _ _) β»ΒΉ)
                                                                               Β· ((fun-ap (Ξ» k β projβ (projβ iso1) β k) (prβ (ProdMorLegAx _ _)))
                                                                               Β· ((CompAssocAx _ _ _) Β· (fun-ap (Ξ» k β k β p1G) (prβ (projβ (projβ iso1)))
                                                                               Β· ((prβ (IdMorAx _)) Β· ((prβ (IdMorAx _)) β»ΒΉ)))))))
                                                                            , ((prβ (ProdMorLegAx _ _)) Β· (((CompAssocAx _ _ _) β»ΒΉ)
                                                                                Β· ((fun-ap (Ξ» k β projβ (projβ iso2) β k) (prβ (ProdMorLegAx _ _)))
                                                                                Β· ((CompAssocAx _ _ _) Β· ((fun-ap (Ξ» k β k β p2G) (prβ (projβ (projβ iso2))))
                                                                                Β· ((prβ (IdMorAx _)) Β· ((prβ (IdMorAx _)) β»ΒΉ)))))))))
                                        ,
                                         ((prod-comp _ _ _) Β· (pr-joint-mono _ _
                                                                              ((((prβ (ProdMorLegAx _ _))) Β· ((((CompAssocAx _ _ _) β»ΒΉ))
                                                                                Β· (fun-ap (Ξ» k β projβ iso1 β k) ((prβ (ProdMorLegAx _ _)))
                                                                                Β· (((CompAssocAx _ _ _) Β· (fun-ap (Ξ» k β k β p1G) (prβ (projβ (projβ iso1)))
                                                                               Β· ((prβ (IdMorAx _)) Β· ((prβ (IdMorAx _)) β»ΒΉ))))))))
                                                                            ,
                                                                              (((prβ (ProdMorLegAx _ _)) Β· (((CompAssocAx _ _ _) β»ΒΉ)
                                                                                Β· ((fun-ap (Ξ» k β projβ iso2 β k) (prβ (ProdMorLegAx _ _)))
                                                                                Β· ((CompAssocAx _ _ _) Β· ((fun-ap (Ξ» k β k β p2G) (prβ (projβ (projβ iso2))))
                                                                                Β· ((prβ (IdMorAx _)) Β· ((prβ (IdMorAx _)) β»ΒΉ)))))))))))))

  βG-1comm : {a b : ObjGEBCat} β ((a βG b) βG (b βG a))
  βG-1comm = < p2G , p1G >G
                    ,, (< p2G , p1G >G
                       ,,   (((prod-comp _ _ _) Β· pr-joint-mono _ _
                                                                (((prβ (ProdMorLegAx _ _)) Β· ((prβ (ProdMorLegAx _ _)) Β· ((prβ (IdMorAx _)) β»ΒΉ)))
                                                               ,
                                                                ((prβ (ProdMorLegAx _ _)) Β· ((prβ (ProdMorLegAx _ _)) Β· ((prβ (IdMorAx _)) β»ΒΉ)))))
                          , ((prod-comp _ _ _) Β· (pr-joint-mono _ _
                                                                ((((prβ (ProdMorLegAx _ _)) Β· ((prβ (ProdMorLegAx _ _)) Β· ((prβ (IdMorAx _)) β»ΒΉ)))
                                                               ,
                                                                ((prβ (ProdMorLegAx _ _)) Β· ((prβ (ProdMorLegAx _ _)) Β· ((prβ (IdMorAx _)) β»ΒΉ)))))))))

  βG-1assoc : {a b c : ObjGEBCat} β ((a βG b) βG c) βG (a βG (b βG c))
  βG-1assoc = < (p1G β p1G) , < (p2G β p1G) , p2G >G >G
                  ,, (< < p1G , (p1G β p2G) >G , (p2G β p2G) >G
                          ,, (((prod-comp _ _ _) Β· (pr-joint-mono _ _
                                                                  (((prβ (ProdMorLegAx _ _)) Β· (prod-comp _ _ _
                                                                  Β· pr-joint-mono _ _
                                                                                     (((prβ (ProdMorLegAx _ _)) Β· ((prβ (ProdMorLegAx _ _))
                                                                                     Β· transp (Ξ» k β (p1G β p1G) β‘ (p1G β k)) (prβ (IdMorAx _) β»ΒΉ) (refl _)))
                                                                                   ,
                                                                                     ((prβ (ProdMorLegAx _ _)) Β· (((CompAssocAx _ _ _) β»ΒΉ)
                                                                                     Β· ((fun-ap (Ξ» k β p1G β k) (prβ (ProdMorLegAx _ _)))
                                                                                     Β· ((prβ (ProdMorLegAx _ _)) Β· (transp (Ξ» k β (p2G β p1G) β‘ (p2G β k)) ((prβ (IdMorAx _)) β»ΒΉ) (refl _)))))))))
                                                                ,
                                                                  ((prβ (ProdMorLegAx _ _)) Β· (((CompAssocAx _ _ _) β»ΒΉ)
                                                                  Β· ((fun-ap (Ξ» k β p2G β k) (prβ (ProdMorLegAx _ _))) Β· ((prβ (ProdMorLegAx _ _))
                                                                  Β· ((prβ (IdMorAx _)) β»ΒΉ))))))))
                            ,
                              ((prod-comp _ _ _) Β· (pr-joint-mono _ _
                                                                    (((prβ (ProdMorLegAx _ _)) Β· (((CompAssocAx _ _ _) β»ΒΉ)
                                                                    Β· ((fun-ap (Ξ» k β p1G β k) (prβ (ProdMorLegAx _ _)))
                                                                    Β· ((prβ (ProdMorLegAx _ _)) Β· ((prβ (IdMorAx _)) β»ΒΉ)))))
                                                                  ,
                                                                    ((prβ (ProdMorLegAx _ _)) Β· ((prod-comp _ _ _)
                                                                    Β· (pr-joint-mono _ _
                                                                                         (((prβ (ProdMorLegAx _ _)) Β· (((CompAssocAx _ _ _) β»ΒΉ)
                                                                                         Β· ((fun-ap (Ξ» k β p2G β k) (prβ (ProdMorLegAx _ _)))
                                                                                         Β· ((prβ (ProdMorLegAx _ _))
                                                                                         Β· (fun-ap (Ξ» k β p1G β k) ((prβ (IdMorAx _)) β»ΒΉ))))))
                                                                                       ,
                                                                                         ((prβ (ProdMorLegAx _ _)) Β· ((prβ (ProdMorLegAx _ _))
                                                                                         Β· (fun-ap (Ξ» k β p2G β k) ((prβ (IdMorAx _)) β»ΒΉ)))))))))))))

-- We formalize the proofs of the strictness of the initial objects in distributive categories

  distrib-c : {a b c : ObjGEBCat} β (((a βG b) βG (a βG c)) β¦ (a βG ((b βG c))))
  distrib-c = [ < p1G , (inlG β p2G) >G , < p1G , (inrG β p2G) >G ]G

  postulate
    distrib-c-iso : {a b c : ObjGEBCat} β projβ (DistribAx {a} {b} {c}) β‘ distrib-c

  inv-iso : {a b : ObjGEBCat} (f : a β¦ b) (P : is-an-intern-iso f) β (is-an-intern-iso (projβ P))
  inv-iso f (g ,, (p1 , p2)) = f ,, (p2 , p1)

  distrib-c-is-iso : {a b c : ObjGEBCat} β is-an-intern-iso (distrib-c {a} {b} {c})
  distrib-c-is-iso = DistribMor ,, ((transp (Ξ» k β (DistribMor β k) β‘ IdMor _) distrib-c-iso (prβ (projβ DistribAx)))
                                   , transp (Ξ» k β (k β DistribMor) β‘ IdMor _) distrib-c-iso (prβ (projβ DistribAx)))
 
  Init-coprod : (Init βG Init) βG Init
  Init-coprod = Init-coprod-iso Init

  iso-mono : {a b c : ObjGEBCat} (f g : a β¦ b ) (m : b β¦ c) β (is-an-intern-iso m) β (m β f β‘ m β g) β (f β‘ g)
  iso-mono f g m (k ,, (p1 , p2)) q = (((prβ (IdMorAx _))) β»ΒΉ) Β· ((fun-ap (Ξ» x β x β f) (p1 β»ΒΉ)) Β· (((CompAssocAx _ _ _) β»ΒΉ)
                                      Β· ((fun-ap (Ξ» x β k β x) q) Β· ((CompAssocAx _ _ _) Β· ((fun-ap (Ξ» x β x β g) p1)
                                      Β· (prβ (IdMorAx _)))))))

  InitCoprod-inx-eq : inlG {Init} {Init} β‘ inrG {Init} {Init}
  InitCoprod-inx-eq = iso-mono inlG inrG [ (InitMor _) , (IdMor _) ]G (projβ (Init-coprod-iso Init))
                               ((InitMorAx _) Β· ((InitMorAx _) β»ΒΉ))

  Init-strict-lemma : {a : ObjGEBCat} β inlG {a βG Init} {a βG Init} β‘ inrG
  Init-strict-lemma = iso-mono inlG inrG distrib-c distrib-c-is-iso
                                                                   ((prβ (CoProdMorLegAx _ _)) Β· (fun-ap (Ξ» k β < p1G , k β p2G >G) InitCoprod-inx-eq
                                                                   Β· ((prβ (CoProdMorLegAx _ _)) β»ΒΉ)))

  Init-βG-uniprop : {a b : ObjGEBCat} β is-Contr ((a βG Init) β¦ b)
  Init-βG-uniprop {a} {b} = (InitMor _ β p2G)
                                      ,, (Ξ» f β ((prβ (CoProdMorLegAx f (InitMor _ β p2G)) β»ΒΉ) Β· fun-ap (Ξ» k β [ f , InitMor b β p2G ]G β k) (Init-strict-lemma β»ΒΉ))
                                         Β· prβ (CoProdMorLegAx {a βG Init} {a βG Init} (f) (InitMor _ β p2G)))

  iso-epi :  {a b c : ObjGEBCat} (f g : a β¦ b ) (e : c β¦ a) β (is-an-intern-iso e) β (f β e β‘ g β e) β f β‘ g
  iso-epi f g e (k ,, (p1 , p2)) q = ((((prβ (IdMorAx _))) β»ΒΉ)) Β· (fun-ap (Ξ» x β f β x) (p2 β»ΒΉ) Β· ((CompAssocAx _ _ _)
                                     Β· (((fun-ap (Ξ» x β x β k) q)) Β· (((CompAssocAx _ _ _) β»ΒΉ) Β· ((fun-ap (Ξ» x β g β x) p2) Β· prβ (IdMorAx _))))))

  Init-βG-uniprop-symm : {a b : ObjGEBCat} β is-Contr ((Init βG a) β¦ b)
  Init-βG-uniprop-symm {a} {b} = (InitMor _ β p1G) ,, Ξ» f β iso-epi _ _ (projβ (βG-1comm)) (projβ (βG-1comm)) (is-Contr-then-is-Prop _ Init-βG-uniprop _ _)
  
  Init-βG-ann : {a : ObjGEBCat} β (Init βG a) βG Init
  Init-βG-ann = p1G ,, ((InitMor _)
                                 ,,  (is-Contr-then-is-Prop _ Init-βG-uniprop-symm _ _
                                    ,
                                     ((InitMorAx _) Β· ((InitMorAx _) β»ΒΉ))))

  Init-strict-fact : {a : ObjGEBCat} (f : a β¦ Init) β (a βG (a βG Init))
  Init-strict-fact f = < (IdMor _) , f >G ,, (p1G ,, ((prβ (ProdMorLegAx _ _)) , (is-Contr-then-is-Prop _ Init-βG-uniprop _ _)))

  Init-strict : {a : ObjGEBCat} (f : a β¦ Init) β a βG Init
  Init-strict f = βG-trans (Init-strict-fact f) (βG-trans βG-1comm Init-βG-ann)

  βG-Term : {a : ObjGEBCat} β ((Term βG a) βG a)
  βG-Term = p2G
                ,, (< TermMor _ , IdMor _ >G ,,
                          ((pr-joint-mono _ _
                                            (((CompAssocAx _ _ _) Β· (fun-ap (Ξ» k β k β p2G) (prβ (ProdMorLegAx _ _))
                                            Β· ((TermMorAx _) Β· ((TermMorAx _) β»ΒΉ))))
                                          ,
                                            ((CompAssocAx _ _ _) Β· ((fun-ap (Ξ» k β k β p2G) (prβ (ProdMorLegAx _ _)))
                                            Β· ((prβ (IdMorAx _)) Β· ((prβ (IdMorAx _)) β»ΒΉ))))))
                        ,
                          prβ (ProdMorLegAx _ _)))

  Gebskel-βG-lemma : {a b : ObjGEBCat} (n m : β) (iso1 : a βG β¨G Term n) (iso2 : b βG β¨G Term m) β ( (a βG b) βG (β¨G Term (n Β·β m)))
  Gebskel-βG-lemma zero m isoa isob = βG-trans (βG-pres-iso isoa isob) Init-βG-ann
  Gebskel-βG-lemma (succ zero) m isoa isob = βG-trans (βG-pres-iso isoa isob) βG-Term
  Gebskel-βG-lemma (succ (succ n)) m isoa isob = βG-trans (βG-pres-iso isoa isob)
                                                    (βG-trans βG-1comm
                                                        (βG-trans (DistribMor  ,, DistribAx)
                                                          (βG-trans (βG-pres-iso βG-1comm βG-1comm)
                                                            (βG-trans (βG-pres-iso (Gebskel-βG-lemma (succ n) m βG-refl βG-refl) βG-Term)
                                                              (Gebskel-βG-lemma _ m βG-refl βG-refl)))))

  GebSkel : (a : ObjGEBCat) β Ξ£[ n βΆ β ] (a βG β¨G Term n)
  GebSkel Init = zero ,, βG-refl
  GebSkel Term = one ,, βG-refl
  GebSkel (a βG b) = ((projβ (GebSkel a)) +β (projβ (GebSkel b)))
                                         ,, (Gebskel-βG-lemma ((projβ (GebSkel a))) ((projβ (GebSkel b))) (projβ (GebSkel a)) (projβ (GebSkel b)))
  GebSkel (a βG b) = (((projβ (GebSkel a)) Β·β (projβ (GebSkel b))))
                                         ,, (Gebskel-βG-lemma ((projβ (GebSkel a))) ((projβ (GebSkel b))) ((projβ (GebSkel a))) ((projβ (GebSkel b))))

-- This establishes an evident skeleton of the Geb category, which we will not prove is equivalent to Ο
  
  
  GebSkel-cat : cat-w-level (lsuc lzero) (lzero)
  GebSkel-cat = β
                  ,, ((Ξ» n m β β¨G Term n β¦ β¨G Term m)
                      ,, (_β_
                      ,, ((Ξ» A β IdMor _)
                      ,, (((Ξ» A B f g β (prβ (IdMorAx g)) , prβ (IdMorAx f))) , Ξ» A B C D β CompAssocAx ))))

  GS-F-obj : (n : β) β FinSet
  GS-F-obj n = Fin-as-obj-of-FinSet n
                                                                         
-- Any distributive category on a category is extensive and as 1 has two subobjects - namely 0 and 1 - we have the fact that for all f : 1 β¦ a βG b it is either inl β fa or inr β fb
-- Explicit proofs will be added later

  postulate
    coprod-term : {a b : ObjGEBCat} (f : Term β¦ (a βG b)) β (Ξ£[ ga βΆ (Term β¦ a) ] (f β‘ inlG β ga)) + (Ξ£[ gb βΆ (Term β¦ b) ] (f β‘ inrG β gb))

  GS-Ο-lemma-one : (m : β) (f : (Term) β¦ (β¨G Term m)) β (π β Fin m)
  GS-Ο-lemma-one zero f = recπ _ (eval (Geb-into-FinSet-mor Term Init f) pt)
  GS-Ο-lemma-one (succ m) f = eval (indβ (Ξ» n β (Term β¦ (β¨G Term (succ n)) ) β (π β Fin (succ n)))
                                                           (Ξ» f' β id _)
                                                           (Ξ» n IHs f' β cases _ (coprod-term f')
                                                                                                 ((Ξ» { (ga ,, p) β inl β IHs ga}))
                                                                                                 (Ξ» p β inr))
                                                           m) f

  GS-Ο : (n m : β) (f : (β¨G Term n) β¦ (β¨G Term m)) β (Fin n β Fin m)
  GS-Ο zero m f =  Ξ» { ()}
  GS-Ο (succ n) m f = eval
                          (indβ (Ξ» n' β ((β¨G Term (succ n')) β¦ (β¨G Term m)) β (Fin ((succ n')) β Fin m ))
                                                                                 (GS-Ο-lemma-one m)                 -- We use the lemma here
                                                                                 (Ξ» n' {-β-} IHs f' β
                                                                                             [ (IHs ((prβ (projβ (βG-mor-fib f')))))
                                                                                             ,
                                                                                             GS-Ο-lemma-one m (((prβ (projβ (βG-mor-fib f'))))) ])
                       n) f

  _βF_ : (A B : FinSet) β Type lzero
  A βF B = (prβ (projβ (A))) β (prβ (projβ (B)))

  βF-coprod : (X Y : FinSet) β prβ (projβ (X βF Y)) β‘ (prβ (projβ X)) + (prβ (projβ Y))
  βF-coprod ((A , n) ,, ea) ((B , m) ,, eb) = refl _
  
  GF-β¨G-pres : (n : β) β prβ (projβ (Geb-into-FinSet-obj (β¨G Term n))) β‘ (prβ (projβ (Fin-as-obj-of-FinSet n)))
  GF-β¨G-pres zero = refl _
  GF-β¨G-pres (succ zero) = refl _
  GF-β¨G-pres (succ (succ n)) = (βF-coprod (Geb-into-FinSet-obj (β¨G Term (succ n))) (Fin-as-obj-of-FinSet one))
                                Β· fun-ap (Ξ» K β K + π) (GF-β¨G-pres (succ n))

-- Usual property of isomorphism preservation for functors

  GF-iso-pres : {a b : ObjGEBCat} β (a βG b) β (Geb-into-FinSet-obj a) βF (Geb-into-FinSet-obj b)
  GF-iso-pres (f ,, (g ,, (p1 , p2)))= (Geb-into-FinSet-mor _ _ f) ,,
                                                                  has-inv-then-equiv _
                                                                  ((Geb-into-FinSet-mor _ _ g)
                                                                        ,, (feq-ptfeq _ (id _) (fun-ap (Geb-into-FinSet-mor _ _) p2)
                                                                                ,
                                                                            feq-ptfeq _ (id _) (fun-ap ((Geb-into-FinSet-mor _ _)) p1)))

-- Now we establish the fact that Geb is coherent

  coh-lemma : (a b c : ObjGEBCat) (f : c β¦ a) (g : c β¦ b) β (inlG β f β‘ inrG β g) β ((inl {lzero} {lzero} {prβ (projβ (Geb-into-FinSet-obj a))} { prβ (projβ (Geb-into-FinSet-obj b))} β
     Geb-into-FinSet-mor (β¨G Term (projβ (GebSkel c))) a
     (f β projβ (projβ (projβ (GebSkel c)))))
    β‘
    (inr {_} {_} {prβ (projβ (Geb-into-FinSet-obj a))} { prβ (projβ (Geb-into-FinSet-obj b))} β
     Geb-into-FinSet-mor (β¨G Term (projβ (GebSkel c))) b
     (g β projβ (projβ (projβ (GebSkel c))))))
  coh-lemma a b c f g ()     

  Geb-coherency : (a b c : ObjGEBCat) (f : c β¦ a) (g : c β¦ b) β (inlG β f β‘ inrG β g) β (c β¦ Init)
  Geb-coherency a b c f g p = eval ((Ο-to-Geb-mor _ zero)) (transp {_} {_} {Type lzero} (Ξ» A β A β π) ( (GF-β¨G-pres (projβ (GebSkel c))))
                                                                                         (Type-disjoint ((Geb-into-FinSet-mor _ a (f β ( projβ (projβ (projβ (GebSkel c)))))))
                                                                                                         ((Geb-into-FinSet-mor _ b (g β ( projβ (projβ (projβ (GebSkel c)))))))
                                                                                                         (coh-lemma a b c f g p)))
                              β ((projβ (projβ (GebSkel _))))

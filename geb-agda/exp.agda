{-# OPTIONS --with-K --exact-split --cumulativity #-}
 
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)

module exp where

  open import geb
  import HoTT
  open HoTT.Basics

  GF-obj : ObjGEBCat → (Type lzero)
  GF-obj Init = 𝟘
  GF-obj Term = 𝟙
  GF-obj (x ⊕G y) = (GF-obj x) + GF-obj y
  GF-obj (x ⊗G y) = (GF-obj x) × (GF-obj y)

  GF-mor : {x y : ObjGEBCat} → (x ↦ y) → ((GF-obj x) → (GF-obj y))
  GF-mor (f ● g) = GF-mor f ∘ GF-mor g
  GF-mor (IdMor _) = id _
  GF-mor (InitMor _) = λ { ()}
  GF-mor (TermMor _) = λ x₁ → pt
  GF-mor (CoProdMor f g) = [ (GF-mor f) , (GF-mor g) ]
  GF-mor (ProdMor f g) = < (GF-mor f) , (GF-mor g) >
  GF-mor DistribMor = proj₁ (×-hom-distrib-over-+ _ _ _)
  GF-mor inlG = inl
  GF-mor inrG = inr
  GF-mor p1G = pr₁
  GF-mor p2G = pr₂

  exp-fun : {x y : ObjGEBCat} → (GF-obj (InHom x y)) → ((GF-obj x) → (GF-obj y))
  exp-fun {Init} {y} pt ()
  exp-fun {Term} {y} = λ x x₁ → x
  exp-fun {x ⊕G y} {z} (f , g) (inl GFx) = (exp-fun f) GFx
  exp-fun {x ⊕G y} {z} (f , g) (inr GFy) = exp-fun g GFy
  exp-fun {x ⊗G y} {z} f (xx , yy) = exp-fun ((exp-fun f) xx) yy

  exp-fun-eq : {x y : ObjGEBCat} → is-an-equiv (exp-fun {x} {y})
  exp-fun-eq {Init} {y} = ((λ x → pt) ,, ( λ x → funext _ _ λ { ()}))
                                           ,
                          ( ((λ x → pt) ,, λ x → is-Contr-then-is-Prop 𝟙 𝟙-is-Contr _ _))
  exp-fun-eq {Term} {y} = (((λ f → f pt) ,, λ f → funext _ _ λ x → fun-ap f (is-Contr-then-is-Prop 𝟙 𝟙-is-Contr _ _))
                                       ,
                          ( (λ f → f pt) ,, λ f → refl _))
  exp-fun-eq (x ⊗G y) z = ((λ (f : (GF-obj x × GF-obj y → GF-obj z)) → (proj₁ (pr₁ (exp-fun-eq x (InHom y z))))
                                  ((proj₁ (pr₁ (exp-fun-eq y z)))  ∘ (curry {lzero} {lzero} {lzero} f)))
                                  ,, λ (f : (GF-obj x × GF-obj y → GF-obj z) )
                                           → funext _ _
                                                   λ {(xx , yy) → transp
                                                                    (λ k →
                                                                       exp-fun y z
                                                                       (exp-fun x (InHom y z)
                                                                        (proj₁ (pr₁ (exp-fun-eq x (InHom y z)))
                                                                         (λ x₁ → proj₁ (pr₁ (exp-fun-eq y z)) (λ b → f (x₁ , b))))
                                                                        xx)
                                                                       yy
                                                                       ≡
                                                                       exp-fun y z
                                                                       (k (λ x₁ → proj₁ (pr₁ (exp-fun-eq y z)) (λ b → f (x₁ , b))) xx) yy)
                                                                    (funext _ _ (proj₂ (pr₁ (exp-fun-eq x (InHom y z))))) (refl _)
                                                                  · transp (λ k → (k (λ b → f (xx , b)) yy) ≡ f (xx , yy))
                                                                    (funext _ _ (hom-sym _ _ (proj₂ (pr₁ (exp-fun-eq y z))))) (refl _)})
                             ,
                             ((λ f →  (proj₁ (pr₂ (exp-fun-eq x (InHom y z))))
                                  ((proj₁ (pr₂ (exp-fun-eq y z)))  ∘ (curry {lzero} {lzero} {lzero} f)))
                                 ,, λ (f : (GF-obj (InHom x (InHom y z)))) →
                                            transp
                                              (λ k →
                                                 proj₁ (pr₂ (exp-fun-eq x (InHom y z)))
                                                 (λ x₁ →
                                                    proj₁ (pr₂ (exp-fun-eq y z))
                                                    (λ b → exp-fun y z (exp-fun x (InHom y z) f x₁) b))
                                                 ≡ proj₁ (pr₂ (exp-fun-eq x (InHom y z))) (λ x₁ →  k (exp-fun x (InHom y z) f x₁)))
                                              (funext _ _ (proj₂ (pr₂ (exp-fun-eq y z)))) (refl _)
                                            · (proj₂ (pr₂ (exp-fun-eq x (InHom y z)))) f)

  eval-iso : (x y : ObjGEBCat) → (GF-mor (evalG x y)) ∼ (((λ (fx : (((GF-obj x) → (GF-obj y)) × (GF-obj x))) → (pr₁ fx) (pr₂ fx) )) ∘ ( (exp-fun x y) ×fun (id (GF-obj x))))
  eval-iso Init y = λ { (x , ())}
  eval-iso Term y (f , x) = refl _
  eval-iso (x ⊕G y) z ((f , g) , inl xx) = eval-iso _ _ ((f , xx))
  eval-iso (x ⊕G y) z ((f , g) , inr yy) = eval-iso _ _ (g , yy)
  eval-iso (x ⊗G y) z (f , (xx , yy)) = transp
                                          (λ k →
                                             GF-mor (evalG y z) (GF-mor (evalG x (InHom y z)) (f , xx) , yy) ≡
                                             GF-mor (evalG y z) (k , yy))
                                          (eval-iso x (InHom y z) ((f , xx))) (refl _)
                                          · eval-iso y z (exp-fun x (InHom y z) f xx , yy)

  

  curry-iso : (x y z : ObjGEBCat) (f : (x ⊗G y) ↦ z) → (exp-fun y z ∘ (GF-mor (λG x y z f))) ∼ (curry (GF-mor f))
  curry-iso x Init z f xx = 𝟘-fun-Prop _ _
  curry-iso x Term z f xx = funext _ _ λ {pt → refl _}
  curry-iso x (y1 ⊕G y2) z f xx = funext _ _ λ { (inl yy1) → transp (λ k → k yy1 ≡ GF-mor f (xx , inl yy1))
                                                                    ((curry-iso x y1 z _ xx) ⁻¹) (refl _)
                                                 ;
                                                  (inr yy2) → transp (λ k → k yy2 ≡ GF-mor f (xx , inr yy2))
                                                                     ((curry-iso x y2 z _ xx) ⁻¹) (refl _) } 
  curry-iso x (y1 ⊗G y2) z f xx = funext _ _ λ {(yy1 , yy2) → transp (λ k1 → exp-fun y2 z k1 yy2 ≡ GF-mor f (xx , (yy1 , yy2)))
                                                                (fun-ap (λ k → k yy1) (curry-iso x y1 (InHom y2 z) _ xx) ⁻¹)
                                                                (transp (λ k2 → k2 yy2 ≡ GF-mor f (xx , (yy1 , yy2)))
                                                                        ((curry-iso (x ⊗G y1) y2 z _ ((xx , yy1))) ⁻¹) (refl _)) }

import GebLean.PshRelDouble

open CategoryTheory

namespace GebLean

universe u v

variable {C : Type u} [Category.{v} C]

/-- Given a characteristic map `χ : X ⟶ Ω` (where
`Ω = pshSieveFunctor C` is the subobject classifier),
the diagonal relation on `X` restricted to the
subobject classified by `χ`.  At stage `c`, the
relation consists of pairs `(x, x)` where `x` lies
in the classified subobject, i.e.,
`χ(c)(x) = ⊤` (the maximal sieve). -/
def pshRelFromSieveMap
    {X : Cᵒᵖ ⥤ Type (max u v)}
    (χ : X ⟶ pshSieveFunctor C) :
    PshRel X X where
  obj c := { pp | pp.1 = pp.2 ∧
    χ.app c pp.1 = (⊤ : Sieve c.unop) }
  map f := by
    rintro ⟨a, b⟩ ⟨heq, htop⟩
    dsimp at heq htop
    refine ⟨congrArg (X.map f) heq, ?_⟩
    change χ.app _ (X.map f a) = (⊤ : Sieve _)
    have nat := congrFun (χ.naturality f) a
    dsimp at nat
    rw [nat, htop]
    exact Sieve.pullback_top

/-- The embedding from `Over Ω` (where
`Ω = pshSieveFunctor C` is the subobject
classifier in `PSh(C)`) into the edge category
of presheaf relations.  Sends `(X, χ : X ⟶ Ω)`
to `(X, X, pshRelFromSieveMap χ)`. -/
def pshOverOmegaEdgeFunctor :
    Over (pshSieveFunctor C) ⥤
    PshRelEdge.{u, v, max u v} C where
  obj S :=
    { src := S.left
      tgt := S.left
      edge := pshRelFromSieveMap S.hom }
  map {S T} f :=
    { srcMap := f.left
      tgtMap := f.left
      sq := by
        intro c p p' ⟨heq, htop⟩
        dsimp at heq htop
        refine ⟨congrArg (f.left.app c) heq, ?_⟩
        change T.hom.app c (f.left.app c p) =
          (⊤ : Sieve c.unop)
        have w := congr_fun
          (congrFun (congrArg NatTrans.app
            (Over.w f)) c) p
        dsimp at w
        rw [w, htop] }
  map_id _ := VertEdgeHom.ext rfl rfl
  map_comp _ _ := VertEdgeHom.ext rfl rfl

/-- The dependent-sum functor `true_!` along the
truth morphism `⊤ : 1 → Ω`.  Sends a presheaf
`X` to `(X, true ∘ !_X)` where `!_X : X → 1`
is the unique map and `true : 1 → Ω` classifies
the maximal sieve.  This labels every element of
`X` as belonging to the subobject. -/
def pshTruthLabelFunctor :
    (Cᵒᵖ ⥤ Type (max u v)) ⥤
    Over (pshSieveFunctor C) where
  obj X := Over.mk
    (default ≫ pshSieveTruth C :
      X ⟶ pshSieveFunctor C)
  map α := Over.homMk α (by
    change α ≫ default ≫ pshSieveTruth C =
      default ≫ pshSieveTruth C
    simp only [← Category.assoc]
    congr 1)
  map_id _ := by
    apply Over.OverMorphism.ext; simp
  map_comp _ _ := by
    apply Over.OverMorphism.ext; simp

/-- When `χ = true ∘ !_X`, every element is in the
classified subobject, so the restricted diagonal
equals the full diagonal (the identity
relation). -/
theorem pshRelFromSieveMap_truth
    (X : Cᵒᵖ ⥤ Type (max u v)) :
    pshRelFromSieveMap
      (default ≫ pshSieveTruth C :
        X ⟶ pshSieveFunctor C) =
      pshRelId X := by
  apply Subfunctor.ext
  funext c
  ext ⟨a, b⟩
  simp only [pshRelFromSieveMap, pshRelId,
    Set.mem_setOf_eq]
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, rfl⟩⟩

private theorem pshRelEdgeHom_heq_of_edge_eq
    {A B : Cᵒᵖ ⥤ Type (max u v)}
    {R₁ R₂ : PshRel A A}
    {S₁ S₂ : PshRel B B}
    (hR : R₁ = R₂) (hS : S₁ = S₂)
    {f : VertEdgeHom pshRelSQS
      ⟨A, A, R₁⟩ ⟨B, B, S₁⟩}
    {g : VertEdgeHom pshRelSQS
      ⟨A, A, R₂⟩ ⟨B, B, S₂⟩}
    (hsrc : f.srcMap = g.srcMap)
    (htgt : f.tgtMap = g.tgtMap) :
    HEq f g := by
  subst hR; subst hS
  exact heq_of_eq (VertEdgeHom.ext hsrc htgt)

/-- The identity section functor factorizes as
`true_! ⋙ embed`, where `true_!` labels every
element with the maximal sieve and `embed` sends
the resulting `Over Ω` object to the corresponding
diagonal relation. -/
theorem pshRelIdentFunctor_factorization :
    pshTruthLabelFunctor ⋙
      pshOverOmegaEdgeFunctor =
    (pshRelIdentFunctor :
      (Cᵒᵖ ⥤ Type (max u v)) ⥤
      PshRelEdge.{u, v, max u v} C) := by
  exact Functor.hext
    (fun X => congrArg (VertEdge.mk X X)
      (pshRelFromSieveMap_truth X))
    (fun X Y f => by
      simp only [Functor.comp_map]
      dsimp only [pshTruthLabelFunctor,
        pshOverOmegaEdgeFunctor,
        pshRelIdentFunctor]
      exact pshRelEdgeHom_heq_of_edge_eq
        (pshRelFromSieveMap_truth X)
        (pshRelFromSieveMap_truth Y)
        rfl rfl)

end GebLean

import GebLean.PolyAlg

/-!
# Cofree Category of a Polynomial Endofunctor

For a polynomial endofunctor `P : PolyEndo X`, the cofree
category `C_P` is the category corresponding to the cofree
comonoid on `P`.  It is constructed from the comonad
arising from the `Forget ⊣ Cofree` adjunction on
P-coalgebras, transported through the equivalence between
the cofree comonad and polynomial evaluation.

The category of P-coalgebras is equivalent to the
copresheaf topos `Set^{C_P}` (Adamek-Porst 2005/2006,
Spivak 2021).

The comonad, natural isomorphism, and comonoid structure
are defined in `PolyAlg.lean` as they apply to all cofree
comonads.
-/

namespace GebLean

open CategoryTheory

universe u

variable {X : Type u}

/-! ## Objects -/

@[ext]
structure PolyCofreeCat (P : PolyEndo X) where
  fiber : X
  shape : PolyCofreeShape P fiber

/-! ## Morphisms -/

@[ext]
structure PolyCofreeCatHom
    (P : PolyEndo X)
    (src tgt : PolyCofreeCat P) where
  depth : Nat
  pos : PolyCofreeAnnotPosAt P src.shape depth
  fiber_eq :
    PolyCofreeAnnotFiberAt P src.shape
      depth pos = tgt.fiber
  subtree_eq :
    HEq (polyCofreeSubtreeAt P src.shape
      depth pos) tgt.shape

/-! ## Path Concatenation Lemmas -/

theorem polyCofreeAnnotPosConcat_id_right
    (P : PolyEndo X) {x : X}
    (s : PolyCofreeShape P x)
    (n : Nat)
    (pos : PolyCofreeAnnotPosAt P s n) :
    polyCofreeAnnotPosConcat P s n pos
      ⟨0, PUnit.unit⟩ = ⟨n, pos⟩ := by
  induction n generalizing x s with
  | zero => rfl
  | succ n ih =>
    obtain ⟨e, rest⟩ := pos
    simp only [polyCofreeAnnotPosConcat]
    rw [ih (s.children e) rest]

theorem polyCofreeSubtreeAt_concat
    (P : PolyEndo X) {x : X}
    (s : PolyCofreeShape P x)
    (n : Nat)
    (pos : PolyCofreeAnnotPosAt P s n)
    (subpos : PolyCofreeAnnotPos P
      (polyCofreeSubtreeAt P s n pos)) :
    HEq
      (polyCofreeSubtreeAt P s
        (polyCofreeAnnotPosConcat P s
          n pos subpos).1
        (polyCofreeAnnotPosConcat P s
          n pos subpos).2)
      (polyCofreeSubtreeAt P
        (polyCofreeSubtreeAt P s n pos)
        subpos.1 subpos.2) := by
  induction n generalizing x s with
  | zero => exact HEq.rfl
  | succ n ih =>
    obtain ⟨e, rest⟩ := pos
    exact ih (s.children e) rest subpos

/-! ## Identity: Components -/

def polyCofreeCatId_depth
    (P : PolyEndo X)
    (_ : PolyCofreeCat P) : Nat := 0

def polyCofreeCatId_pos
    (P : PolyEndo X)
    (obj : PolyCofreeCat P) :
    PolyCofreeAnnotPosAt P obj.shape
      (polyCofreeCatId_depth P obj) :=
  PUnit.unit

def PolyCofreeCatHom.id (P : PolyEndo X)
    (obj : PolyCofreeCat P) :
    PolyCofreeCatHom P obj obj :=
  { depth := polyCofreeCatId_depth P obj
    pos := polyCofreeCatId_pos P obj
    fiber_eq := rfl
    subtree_eq := HEq.rfl }

/-! ## Composition: Components -/

def polyCofreeCatComp_castPos
    {P : PolyEndo X}
    {src : PolyCofreeCat P}
    (fn : Nat)
    (fp : PolyCofreeAnnotPosAt P
      src.shape fn)
    {mid : PolyCofreeCat P}
    (hff : PolyCofreeAnnotFiberAt P
      src.shape fn fp = mid.fiber)
    (hfs : HEq (polyCofreeSubtreeAt P
      src.shape fn fp) mid.shape)
    {m : Nat}
    (pos : PolyCofreeAnnotPosAt P
      mid.shape m) :
    PolyCofreeAnnotPosAt P
      (polyCofreeSubtreeAt P src.shape
        fn fp) m :=
  cast (polyCofreeAnnotPosAt_cast_fiber
    hff hfs m).symm pos

def polyCofreeCatComp_subpos
    {P : PolyEndo X}
    {src mid tgt : PolyCofreeCat P}
    (f : PolyCofreeCatHom P src mid)
    (g : PolyCofreeCatHom P mid tgt) :
    PolyCofreeAnnotPos P
      (polyCofreeSubtreeAt P src.shape
        f.depth f.pos) :=
  ⟨g.depth, polyCofreeCatComp_castPos
    f.depth f.pos f.fiber_eq f.subtree_eq
    g.pos⟩

def polyCofreeCatComp_result
    {P : PolyEndo X}
    {src mid tgt : PolyCofreeCat P}
    (f : PolyCofreeCatHom P src mid)
    (g : PolyCofreeCatHom P mid tgt) :
    PolyCofreeAnnotPos P src.shape :=
  polyCofreeAnnotPosConcat P src.shape
    f.depth f.pos
    (polyCofreeCatComp_subpos f g)

def polyCofreeCatComp_depth
    {P : PolyEndo X}
    {src mid tgt : PolyCofreeCat P}
    (f : PolyCofreeCatHom P src mid)
    (g : PolyCofreeCatHom P mid tgt) :
    Nat :=
  (polyCofreeCatComp_result f g).1

def polyCofreeCatComp_pos
    {P : PolyEndo X}
    {src mid tgt : PolyCofreeCat P}
    (f : PolyCofreeCatHom P src mid)
    (g : PolyCofreeCatHom P mid tgt) :
    PolyCofreeAnnotPosAt P src.shape
      (polyCofreeCatComp_depth f g) :=
  (polyCofreeCatComp_result f g).2

theorem polyCofreeCatComp_fiber_eq
    {P : PolyEndo X}
    {src mid tgt : PolyCofreeCat P}
    (f : PolyCofreeCatHom P src mid)
    (g : PolyCofreeCatHom P mid tgt) :
    PolyCofreeAnnotFiberAt P src.shape
      (polyCofreeCatComp_depth f g)
      (polyCofreeCatComp_pos f g) =
    tgt.fiber := by
  change PolyCofreeAnnotFiber P src.shape
    (polyCofreeCatComp_result f g) = tgt.fiber
  rw [show polyCofreeCatComp_result f g =
    polyCofreeAnnotPosConcat P src.shape
      f.depth f.pos
      (polyCofreeCatComp_subpos f g) from rfl]
  rw [polyCofreeAnnotFiber_concat]
  obtain ⟨_, _⟩ := mid
  obtain ⟨fn, fp, hff, hfs⟩ := f
  dsimp at hff hfs
  subst hff
  cases eq_of_heq hfs
  exact g.fiber_eq

theorem polyCofreeCatComp_subtree_eq
    {P : PolyEndo X}
    {src mid tgt : PolyCofreeCat P}
    (f : PolyCofreeCatHom P src mid)
    (g : PolyCofreeCatHom P mid tgt) :
    HEq (polyCofreeSubtreeAt P src.shape
      (polyCofreeCatComp_depth f g)
      (polyCofreeCatComp_pos f g))
    tgt.shape := by
  exact (polyCofreeSubtreeAt_concat P
    src.shape f.depth f.pos
    (polyCofreeCatComp_subpos f g)).trans (by
      obtain ⟨_, _⟩ := mid
      obtain ⟨fn, fp, hff, hfs⟩ := f
      dsimp at hff hfs
      subst hff
      cases eq_of_heq hfs
      exact g.subtree_eq)

def PolyCofreeCatHom.comp {P : PolyEndo X}
    {src mid tgt : PolyCofreeCat P}
    (f : PolyCofreeCatHom P src mid)
    (g : PolyCofreeCatHom P mid tgt) :
    PolyCofreeCatHom P src tgt :=
  { depth := polyCofreeCatComp_depth f g
    pos := polyCofreeCatComp_pos f g
    fiber_eq := polyCofreeCatComp_fiber_eq f g
    subtree_eq :=
      polyCofreeCatComp_subtree_eq f g }

/-! ## Category Laws -/

theorem PolyCofreeCatHom.id_comp
    {P : PolyEndo X}
    {src tgt : PolyCofreeCat P}
    (g : PolyCofreeCatHom P src tgt) :
    (PolyCofreeCatHom.id P src).comp g = g := by
  obtain ⟨_, _⟩ := tgt
  obtain ⟨gn, gp, hgf, hgs⟩ := g
  dsimp at hgf hgs
  subst hgf
  cases eq_of_heq hgs
  rfl

theorem PolyCofreeCatHom.comp_id
    {P : PolyEndo X}
    {src tgt : PolyCofreeCat P}
    (f : PolyCofreeCatHom P src tgt) :
    f.comp (PolyCofreeCatHom.id P tgt) = f := by
  obtain ⟨_, _⟩ := tgt
  obtain ⟨fn, fp, hff, hfs⟩ := f
  dsimp at hff hfs
  subst hff
  cases eq_of_heq hfs
  simp only [PolyCofreeCatHom.comp,
    polyCofreeCatComp_depth,
    polyCofreeCatComp_pos,
    polyCofreeCatComp_result,
    polyCofreeCatComp_subpos,
    polyCofreeCatComp_castPos,
    PolyCofreeCatHom.id,
    polyCofreeCatId_depth,
    polyCofreeCatId_pos,
    cast_eq]
  have comm := polyCofreeAnnotPosConcat_id_right
    P src.shape fn fp
  ext
  · exact congrArg Sigma.fst comm
  · exact (Sigma.ext_iff.mp comm).2


/--
Associativity of path concatenation, stated as an
equality of `PolyCofreeAnnotPos` sigma pairs.
Proved by induction on the first position's depth.
-/
theorem polyCofreeAnnotPosConcat_assoc
    {P : PolyEndo X} {x : X}
    (s : PolyCofreeShape P x) :
    ∀ (n1 : Nat)
    (p1 : PolyCofreeAnnotPosAt P s n1)
    (n2 : Nat)
    (p2 : PolyCofreeAnnotPosAt P
      (polyCofreeSubtreeAt P s n1 p1) n2)
    (n3 : Nat)
    (p3 : PolyCofreeAnnotPosAt P
      (polyCofreeSubtreeAt P
        (polyCofreeSubtreeAt P s n1 p1)
        n2 p2) n3),
    polyCofreeAnnotPosConcat P s n1 p1
      (polyCofreeAnnotPosConcat P
        (polyCofreeSubtreeAt P s n1 p1)
        n2 p2 ⟨n3, p3⟩) =
    polyCofreeAnnotPosConcat P s
      (polyCofreeAnnotPosConcat P s
        n1 p1 ⟨n2, p2⟩).1
      (polyCofreeAnnotPosConcat P s
        n1 p1 ⟨n2, p2⟩).2
      ⟨n3, cast
        (polyCofreeAnnotPosAt_cast_fiber
          (polyCofreeAnnotFiber_concat P s
            n1 p1 ⟨n2, p2⟩)
          (polyCofreeSubtreeAt_concat P s
            n1 p1 ⟨n2, p2⟩)
          n3).symm p3⟩ := by
  intro n1
  induction n1 generalizing x s with
  | zero =>
    intro _ n2 p2 n3 p3
    simp only [polyCofreeAnnotPosConcat,
      polyCofreeSubtreeAt, cast_eq]
  | succ n1 ih =>
    intro ⟨e, rest⟩ n2 p2 n3 p3
    change PolyCofreeAnnotPosAt P
      (polyCofreeSubtreeAt P
        (s.children e) n1 rest) n2 at p2
    change PolyCofreeAnnotPosAt P
      (polyCofreeSubtreeAt P
        (polyCofreeSubtreeAt P
          (s.children e) n1 rest)
        n2 p2) n3 at p3
    simp only [polyCofreeAnnotPosConcat,
      polyCofreeSubtreeAt]
    exact congrArg
      (fun (r : PolyCofreeAnnotPos P
        (s.children e)) =>
        (⟨r.1 + 1, ⟨e, r.2⟩⟩ :
          PolyCofreeAnnotPos P s))
      (ih (s.children e) rest n2 p2 n3 p3)

theorem PolyCofreeCatHom.comp_assoc
    {P : PolyEndo X}
    {a b c d : PolyCofreeCat P}
    (f : PolyCofreeCatHom P a b)
    (g : PolyCofreeCatHom P b c)
    (h : PolyCofreeCatHom P c d) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  obtain ⟨_, _⟩ := b
  obtain ⟨_, _⟩ := c
  obtain ⟨_, _⟩ := d
  obtain ⟨fn, fp, hff, hfs⟩ := f
  obtain ⟨gn, gp, hgf, hgs⟩ := g
  obtain ⟨hn, hp, hhf, hhs⟩ := h
  dsimp at hff hfs hgf hgs hhf hhs
  subst hff hgf hhf
  cases eq_of_heq hfs
  cases eq_of_heq hgs
  cases eq_of_heq hhs
  have comm := (polyCofreeAnnotPosConcat_assoc
    a.shape fn fp gn gp hn hp).symm
  simp only [PolyCofreeCatHom.comp,
    polyCofreeCatComp_depth,
    polyCofreeCatComp_pos,
    polyCofreeCatComp_result,
    polyCofreeCatComp_subpos,
    polyCofreeCatComp_castPos,
    cast_eq] at comm ⊢
  ext
  · exact congrArg Sigma.fst comm
  · exact (Sigma.ext_iff.mp comm).2

/-! ## Category Instance -/

instance polyCofreeCatCategory
    (P : PolyEndo X) :
    Category (PolyCofreeCat P) where
  Hom := PolyCofreeCatHom P
  id := PolyCofreeCatHom.id P
  comp := PolyCofreeCatHom.comp
  id_comp := PolyCofreeCatHom.id_comp
  comp_id := PolyCofreeCatHom.comp_id
  assoc := PolyCofreeCatHom.comp_assoc

/-! ## Connection Lemmas -/

/--
The target object determined by a position in a shape.
-/
def PolyCofreeCat.tgtAt {P : PolyEndo X}
    (obj : PolyCofreeCat P)
    (n : Nat)
    (pos : PolyCofreeAnnotPosAt P
      obj.shape n) :
    PolyCofreeCat P :=
  ⟨PolyCofreeAnnotFiberAt P obj.shape n pos,
    polyCofreeSubtreeAt P obj.shape n pos⟩

/--
Every depth-position pair in the source shape
determines a morphism in the cofree category.
-/
def polyCofreeCatHomOfPos {P : PolyEndo X}
    (obj : PolyCofreeCat P)
    (n : Nat)
    (pos : PolyCofreeAnnotPosAt P
      obj.shape n) :
    PolyCofreeCatHom P obj (obj.tgtAt n pos) :=
  { depth := n
    pos := pos
    fiber_eq := rfl
    subtree_eq := HEq.rfl }

/--
Every morphism in the cofree category arises from a
position in the source shape via `polyCofreeCatHomOfPos`.
-/
theorem polyCofreeCatHom_eq_homOfPos
    {P : PolyEndo X}
    {src tgt : PolyCofreeCat P}
    (f : PolyCofreeCatHom P src tgt) :
    tgt = src.tgtAt f.depth f.pos ∧
    HEq f (polyCofreeCatHomOfPos src
      f.depth f.pos) := by
  obtain ⟨_, _⟩ := tgt
  obtain ⟨n, pos, hff, hfs⟩ := f
  dsimp at hff hfs
  subst hff
  cases eq_of_heq hfs
  exact ⟨rfl, HEq.rfl⟩

/--
The total space of morphisms out of an object is
equivalent to the annotation positions in its shape.
This is the hom-set correspondence:
`(Σ tgt, Hom obj tgt) ≃ PolyCofreeAnnotPos P obj.shape`.
-/
def polyCofreeCatHomEquiv {P : PolyEndo X}
    (obj : PolyCofreeCat P) :
    (Σ tgt, PolyCofreeCatHom P obj tgt) ≃
    PolyCofreeAnnotPos P obj.shape where
  toFun := fun ⟨_, f⟩ => ⟨f.depth, f.pos⟩
  invFun := fun ⟨n, pos⟩ =>
    ⟨obj.tgtAt n pos,
      polyCofreeCatHomOfPos obj n pos⟩
  left_inv := fun ⟨tgt, f⟩ => by
    obtain ⟨_, _⟩ := tgt
    obtain ⟨n, pos, hff, hfs⟩ := f
    dsimp at hff hfs
    subst hff
    cases eq_of_heq hfs
    rfl
  right_inv := fun ⟨_, _⟩ => rfl

/--
The family of the cofree polynomial at a shape `s`
has positions `PolyCofreeAnnotPos P s` and fiber map
`PolyCofreeAnnotFiber P s`.  A morphism in the cofree
category from `⟨x, s⟩` to `⟨y, t⟩` is a position
`pos` in this family such that
`PolyCofreeAnnotFiber P s pos = y` and the subtree at
`pos` is `t`.
-/
theorem polyCofreeCatHom_as_family_element
    {P : PolyEndo X}
    {src : PolyCofreeCat P}
    (n : Nat)
    (pos : PolyCofreeAnnotPosAt P
      src.shape n) :
    (polyCofreeFamily P src.fiber
      src.shape).hom ⟨n, pos⟩ =
    (src.tgtAt n pos).fiber := rfl

end GebLean

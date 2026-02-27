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

/-! ## Transport Lemmas for PolyCofreeCat -/

/--
Transport lemma for `polyCofreeSubtreeAt`:
the subtree at a position is preserved when
transporting along fiber equality and shape HEq,
with the position cast accordingly.
-/
lemma polyCofreeSubtreeAt_transport
    {P : PolyEndo X} {y1 y2 : X}
    (hfiber : y1 = y2)
    {s1 : PolyCofreeShape P y1}
    {s2 : PolyCofreeShape P y2}
    (hshape : HEq s1 s2)
    (n : Nat)
    (pos : PolyCofreeAnnotPosAt P s1 n) :
    HEq
      (polyCofreeSubtreeAt P s1 n pos)
      (polyCofreeSubtreeAt P s2 n
        (cast (polyCofreeAnnotPosAt_cast_fiber
          hfiber hshape n) pos)) := by
  subst hfiber
  have h := eq_of_heq hshape
  subst h
  exact HEq.rfl

/--
The `tgtAt` function is preserved when
transporting along a `PolyCofreeCat` equality:
if `obj1 = obj2`, then `tgtAt` at any position
in `obj1` equals `tgtAt` at the cast position
in `obj2`.
-/
lemma PolyCofreeCat.tgtAt_transport
    {P : PolyEndo X}
    {obj1 obj2 : PolyCofreeCat P}
    (h : obj1 = obj2)
    (n : Nat)
    (pos : PolyCofreeAnnotPosAt P
      obj1.shape n) :
    obj1.tgtAt n pos =
    obj2.tgtAt n
      (cast (congrArg
        (fun obj => PolyCofreeAnnotPosAt P
          obj.shape n) h) pos) := by
  subst h
  rfl

/-! ## Coalgebra Copresheaf -/

/--
The shape of the M-type tree associated to an element
of a comonad coalgebra, transported to the element's
fiber.  For `a : c.A.left`, the coalgebra structure
map `c.a` produces an M-type tree
`(c.a.left a).2 : PolyCofreeM c.A P (c.a.left a).1`.
This extracts its shape and transports it along the
fiber equality `(c.a.left a).1 = c.A.hom a`.
-/
def coalgCopresheafShapeAt {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left) :
    PolyCofreeShape P (c.A.hom a) :=
  (comonadCoalgFiberEq c a) ▸
    polyCofreeToShape c.A P (c.a.left a).2

/--
The cofree category object determined by an element
of a comonad coalgebra: the pair of its fiber and
transported shape.
-/
def coalgCopresheafTarget {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left) : PolyCofreeCat P :=
  ⟨c.A.hom a, coalgCopresheafShapeAt c a⟩

/--
The copresheaf value at a cofree category object
`obj`: the set of elements `a` of the coalgebra
carrier whose fiber and shape match `obj`.
-/
def coalgCopresheafObj {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (obj : PolyCofreeCat P) : Type u :=
  { a : c.A.left //
    coalgCopresheafTarget c a = obj }

/--
The transported shape is HEq to the raw M-type shape.
-/
lemma coalgCopresheafShapeAt_heq
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left) :
    HEq (coalgCopresheafShapeAt c a)
      (polyCofreeToShape c.A P
        (c.a.left a).2) := by
  let h := comonadCoalgFiberEq c a
  change HEq (h ▸ polyCofreeToShape c.A P
    (c.a.left a).2)
    (polyCofreeToShape c.A P (c.a.left a).2)
  exact eqRec_heq h _

/--
Cast a position from the transported shape to the
raw M-type shape.
-/
def coalgCopresheafCastPos
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left) (n : Nat)
    (pos : PolyCofreeAnnotPosAt P
      (coalgCopresheafShapeAt c a) n) :
    PolyCofreeAnnotPosAt P
      (polyCofreeToShape c.A P
        (c.a.left a).2) n :=
  cast (polyCofreeAnnotPosAt_cast_fiber
    (comonadCoalgFiberEq c a).symm
    (coalgCopresheafShapeAt_heq c a) n)
    pos

/--
Extract the annotation value from an element's M-type
tree at a position given in terms of the transported
shape.
-/
def coalgCopresheafExtractVal
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left) (n : Nat)
    (pos : PolyCofreeAnnotPosAt P
      (coalgCopresheafShapeAt c a) n) :
    c.A.left :=
  (polyCofreeGetAnnotAt c.A P
    (c.a.left a).2 n
    (coalgCopresheafCastPos c a n pos)).val

/--
The fiber of the extracted annotation equals the
annotation fiber at the given position.
-/
lemma coalgCopresheafExtractVal_fiber
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left) (n : Nat)
    (pos : PolyCofreeAnnotPosAt P
      (coalgCopresheafShapeAt c a) n) :
    c.A.hom
      (coalgCopresheafExtractVal c a n pos) =
    PolyCofreeAnnotFiberAt P
      (coalgCopresheafShapeAt c a) n pos := by
  simp only [coalgCopresheafExtractVal]
  rw [polyCofreeAnnotFiberAt_transport
    (comonadCoalgFiberEq c a).symm
    (coalgCopresheafShapeAt_heq c a)
    n pos]
  exact (polyCofreeGetAnnotAt c.A P
    (c.a.left a).2 n
    (coalgCopresheafCastPos c a n pos)).property

/--
The depth-1 child annotation: given an edge
`e_m` in the M-type tree's children, extract
the root annotation of the child subtree.
-/
def coalgCopresheafChild
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left)
    (e_m : (polyBetweenFamily X X
      (polyScale c.A P) (c.a.left a).1
      (c.a.left a).2.head).left) :
    c.A.left :=
  (polyCofreeExtract c.A P
    ((c.a.left a).2.children e_m)).val

/--
Self-consistency at depth 1: the coalgebra
structure map applied to the child annotation
gives back the child M-type subtree.
-/
lemma coalgCopresheafChild_consistent
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left)
    (e_m : (polyBetweenFamily X X
      (polyScale c.A P) (c.a.left a).1
      (c.a.left a).2.head).left) :
    c.a.left (coalgCopresheafChild c a e_m) =
    ⟨(polyBetweenFamily X X
      (polyScale c.A P) (c.a.left a).1
      (c.a.left a).2.head).hom e_m,
      (c.a.left a).2.children e_m⟩ :=
  comonadCoalgSelfconsistent c a e_m

/--
The fiber of the child annotation, derived from
the self-consistency property.
-/
lemma coalgCopresheafChild_fiber
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left)
    (e_m : (polyBetweenFamily X X
      (polyScale c.A P) (c.a.left a).1
      (c.a.left a).2.head).left) :
    (c.a.left
      (coalgCopresheafChild c a e_m)).1 =
    (polyBetweenFamily X X
      (polyScale c.A P) (c.a.left a).1
      (c.a.left a).2.head).hom e_m :=
  congrArg Sigma.fst
    (coalgCopresheafChild_consistent c a e_m)

/--
The M-type tree of the child annotation is
the parent's child subtree.
-/
lemma coalgCopresheafChild_mtype
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left)
    (e_m : (polyBetweenFamily X X
      (polyScale c.A P) (c.a.left a).1
      (c.a.left a).2.head).left) :
    HEq (c.a.left
      (coalgCopresheafChild c a e_m)).2
    ((c.a.left a).2.children e_m) := by
  have h := coalgCopresheafChild_consistent
    c a e_m
  exact (Sigma.ext_iff.mp h).2

/--
The copresheaf shape at the child annotation
is HEq to the shape of the parent's child
M-type subtree.
-/
lemma coalgCopresheafChild_shape_heq
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left)
    (e_m : (polyBetweenFamily X X
      (polyScale c.A P) (c.a.left a).1
      (c.a.left a).2.head).left) :
    HEq
      (polyCofreeToShape c.A P
        (c.a.left
          (coalgCopresheafChild c a e_m)).2)
      (polyCofreeToShape c.A P
        ((c.a.left a).2.children e_m)) := by
  let toShape :=
    fun (p : Σ x, PolyCofreeM c.A P x) =>
      (⟨p.1, polyCofreeToShape c.A P p.2⟩ :
        Σ x, PolyCofreeShape P x)
  have h := congrArg toShape
    (coalgCopresheafChild_consistent c a e_m)
  exact (Sigma.ext_iff.mp h).2

-- The copresheaf morphism action and functor laws
-- require the depth-1 target equality
-- (coalgCopresheafChild_depth1_target) which relates
-- the child annotation's copresheaf target to the
-- parent's child shape. This is developed below
-- using the sigma-pair infrastructure.

/--
The "raw shape pair" function: maps the
coalgebra structure output to a sigma pair
of fiber and shape, without the
`comonadCoalgFiberEq` transport.
-/
def coalgCopresheafTargetRaw {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left) : Σ x, PolyCofreeShape P x :=
  ⟨(c.a.left a).1,
    polyCofreeToShape c.A P (c.a.left a).2⟩

/--
The raw target equals the transported target
as a sigma pair via the fiber equality.
-/
lemma coalgCopresheafTargetRaw_eq
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left) :
    coalgCopresheafTargetRaw c a =
    ⟨c.A.hom a,
      coalgCopresheafShapeAt c a⟩ :=
  Sigma.ext (congrFun (Over.w c.a) a)
    (coalgCopresheafShapeAt_heq c a).symm

/--
The raw shape pair of the child annotation at
M-type edge `e_m` equals the pair consisting of
the child fiber and the shape of the parent's
child M-type subtree.
-/
lemma coalgCopresheafChild_rawTarget
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left)
    (e_m : (polyBetweenFamily X X
      (polyScale c.A P) (c.a.left a).1
      (c.a.left a).2.head).left) :
    coalgCopresheafTargetRaw c
      (coalgCopresheafChild c a e_m) =
    ⟨(polyBetweenFamily X X (polyScale c.A P)
        (c.a.left a).1
        (c.a.left a).2.head).hom e_m,
      polyCofreeToShape c.A P
        ((c.a.left a).2.children e_m)⟩ := by
  simp only [coalgCopresheafTargetRaw]
  let toShape :=
    fun (p : Σ x, PolyCofreeM c.A P x) =>
      (⟨p.1, polyCofreeToShape c.A P p.2⟩ :
        Σ x, PolyCofreeShape P x)
  exact congrArg toShape
    (coalgCopresheafChild_consistent c a e_m)

/--
The transported target of the child annotation,
stated in terms of the raw shape pair.
Combines `coalgCopresheafChild_rawTarget` with
`coalgCopresheafTargetRaw_eq` to give the
transported target as a sigma pair equality.
-/
lemma coalgCopresheafChild_target_sigma
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left)
    (e_m : (polyBetweenFamily X X
      (polyScale c.A P) (c.a.left a).1
      (c.a.left a).2.head).left) :
    (⟨c.A.hom (coalgCopresheafChild c a e_m),
      coalgCopresheafShapeAt c
        (coalgCopresheafChild c a e_m)⟩ :
      Σ x, PolyCofreeShape P x) =
    ⟨(polyBetweenFamily X X (polyScale c.A P)
        (c.a.left a).1
        (c.a.left a).2.head).hom e_m,
      polyCofreeToShape c.A P
        ((c.a.left a).2.children e_m)⟩ :=
  (coalgCopresheafTargetRaw_eq c
    (coalgCopresheafChild c a e_m)).symm.trans
    (coalgCopresheafChild_rawTarget c a e_m)

/--
Fiber component of the child target sigma
equality: the fiber of the child annotation
equals the hom of the M-type edge.
-/
lemma coalgCopresheafChild_target_fiber
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left)
    (e_m : (polyBetweenFamily X X
      (polyScale c.A P) (c.a.left a).1
      (c.a.left a).2.head).left) :
    c.A.hom (coalgCopresheafChild c a e_m) =
    (polyBetweenFamily X X (polyScale c.A P)
      (c.a.left a).1
      (c.a.left a).2.head).hom e_m :=
  congrArg Sigma.fst
    (coalgCopresheafChild_target_sigma c a e_m)

/--
Shape component of the child target sigma
equality: the transported shape of the child
annotation is HEq to the shape of the parent's
child M-type subtree.
-/
lemma coalgCopresheafChild_target_shape
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left)
    (e_m : (polyBetweenFamily X X
      (polyScale c.A P) (c.a.left a).1
      (c.a.left a).2.head).left) :
    HEq
      (coalgCopresheafShapeAt c
        (coalgCopresheafChild c a e_m))
      (polyCofreeToShape c.A P
        ((c.a.left a).2.children e_m)) :=
  (Sigma.ext_iff.mp
    (coalgCopresheafChild_target_sigma
      c a e_m)).2

/--
The shape of the parent's child M-type subtree
is HEq to the children of the raw M-type shape.
This is just `polyCofreeToShape_children_heq`
applied to the specific M-type edge `e_m` obtained
from the shape edge via `polyCofreeShapePosToMPos`.
-/
lemma coalgCopresheafChild_rawShape_heq
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left)
    (e_raw : (polyBetweenFamily X X P
      (c.a.left a).1
      (polyCofreeToShape c.A P
        (c.a.left a).2).head.2).left) :
    let m := (c.a.left a).2
    let e_m := polyCofreeShapePosToMPos
      c.A P m e_raw
    HEq
      (polyCofreeToShape c.A P
        (m.children e_m))
      ((polyCofreeToShape c.A P m).children
        e_raw) :=
  (polyCofreeToShape_children_heq c.A P
    (c.a.left a).2 e_raw).symm

/--
The children of the transported shape at edge
`e_shape` are HEq to the children of the raw
M-type shape at the corresponding edge.
-/
lemma coalgCopresheafShapeAt_children_heq
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left)
    (e_shape : (polyBetweenFamily X X P (c.A.hom a)
      (coalgCopresheafShapeAt c a).head.2).left)
    (e_raw : (polyBetweenFamily X X P (c.a.left a).1
      (polyCofreeToShape c.A P
        (c.a.left a).2).head.2).left)
    (he : HEq e_shape e_raw) :
    HEq
      ((coalgCopresheafShapeAt c a).children
        e_shape)
      ((polyCofreeToShape c.A P
        (c.a.left a).2).children e_raw) := by
  let h_fib := comonadCoalgFiberEq c a
  let h_shape := coalgCopresheafShapeAt_heq c a
  exact PolyCofix.children_heq h_fib.symm
    h_shape he

/--
The M-type child shape pair (fiber + shape of
`m.children e_m`) equals the raw shape children
pair (fiber + children at `e_raw`), as sigma pairs.
-/
lemma coalgCopresheafChild_rawToShape
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left)
    (e_raw : (polyBetweenFamily X X P (c.a.left a).1
      (polyCofreeToShape c.A P
        (c.a.left a).2).head.2).left) :
    let m := (c.a.left a).2
    let e_m := polyCofreeShapePosToMPos
      c.A P m e_raw
    (⟨(polyBetweenFamily X X (polyScale c.A P)
        (c.a.left a).1 m.head).hom e_m,
      polyCofreeToShape c.A P
        (m.children e_m)⟩ :
      Σ x, PolyCofreeShape P x) =
    ⟨(polyBetweenFamily X X P (c.a.left a).1
        (polyCofreeToShape c.A P m).head.2
        ).hom e_raw,
      (polyCofreeToShape c.A P m).children
        e_raw⟩ := by
  let m := (c.a.left a).2
  let e_m := polyCofreeShapePosToMPos
    c.A P m e_raw
  exact Sigma.ext
    (polyCofreeShapePosToMPos_fiber c.A P
      m e_raw).symm
    (coalgCopresheafChild_rawShape_heq
      c a e_raw)

/--
The raw shape children pair equals the transported
shape children pair, via the fiber equality.
-/
lemma coalgCopresheafChild_shapeToTransported
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left)
    (e_shape : (polyBetweenFamily X X P (c.A.hom a)
      (coalgCopresheafShapeAt c a).head.2).left)
    (e_raw : (polyBetweenFamily X X P (c.a.left a).1
      (polyCofreeToShape c.A P
        (c.a.left a).2).head.2).left)
    (he : HEq e_shape e_raw) :
    let m := (c.a.left a).2
    (⟨(polyBetweenFamily X X P (c.a.left a).1
        (polyCofreeToShape c.A P m).head.2
        ).hom e_raw,
      (polyCofreeToShape c.A P m).children
        e_raw⟩ :
      Σ x, PolyCofreeShape P x) =
    ⟨(polyBetweenFamily X X P (c.A.hom a)
        (coalgCopresheafShapeAt c a).head.2
        ).hom e_shape,
      (coalgCopresheafShapeAt c a).children
        e_shape⟩ := by
  -- Generalize c.a.left a to collapse the
  -- fiber transport. First revert everything
  -- that depends on it.
  revert e_raw he
  generalize hca : c.a.left a = ca
  obtain ⟨xv, mv⟩ := ca
  intro e_raw he
  have hfib : xv = c.A.hom a :=
    (congrArg Sigma.fst hca).symm.trans
      (comonadCoalgFiberEq c a)
  subst hfib
  -- Now mv : PolyCofix ... (c.A.hom a).
  -- Prove coalgCopresheafShapeAt c a =
  -- polyCofreeToShape c.A P mv using hca.
  have hmv_heq :
      HEq (c.a.left a).2 mv :=
    (Sigma.ext_iff.mp hca).2
  have h_shapeAt_eq :
      coalgCopresheafShapeAt c a =
      polyCofreeToShape c.A P mv := by
    -- Use the sigma pair chain:
    -- ⟨c.A.hom a, polyCofreeToShape mv⟩
    -- = toShape ⟨c.A.hom a, mv⟩
    -- = toShape (c.a.left a)    [by hca.symm]
    -- = coalgCopresheafTargetRaw_eq
    -- = ⟨c.A.hom a, coalgCopresheafShapeAt c a⟩
    let toShape := fun (p :
        Σ x, PolyCofreeM c.A P x) =>
      (⟨p.1, polyCofreeToShape c.A P p.2⟩ :
        Σ x, PolyCofreeShape P x)
    have h1 : toShape (c.a.left a) =
        (⟨c.A.hom a,
          polyCofreeToShape c.A P mv⟩ :
          Σ x, PolyCofreeShape P x) :=
      congrArg toShape hca
    have h2 := coalgCopresheafTargetRaw_eq c a
    -- h2 : ⟨(c.a.left a).1, toShape...⟩ =
    --   ⟨c.A.hom a, coalgCopresheafShapeAt c a⟩
    have h3 : (⟨c.A.hom a,
        polyCofreeToShape c.A P mv⟩ :
        Σ x, PolyCofreeShape P x) =
      ⟨c.A.hom a,
        coalgCopresheafShapeAt c a⟩ :=
      h1.symm.trans h2
    exact (eq_of_heq
      (Sigma.ext_iff.mp h3).2).symm
  -- Set coalgCopresheafShapeAt c a as a variable
  -- so we can subst it.
  dsimp only at e_raw
  revert e_shape he
  rw [h_shapeAt_eq]
  intro e_shape he
  -- Now e_shape and e_raw have the same type.
  have he_eq := eq_of_heq he
  subst he_eq
  rfl

-- The depth-1 target equality
-- (`coalgCopresheafChild_depth1_target`) is the
-- remaining blocker. It requires relating the
-- child annotation's copresheaf target to the
-- parent's tgtAt at depth 1. The sigma pair
-- chain (target_sigma + rawToShape +
-- shapeToTransported) gives the equality, but
-- the edge HEq between the transported shape edge
-- and the raw shape edge requires extracting
-- `.fst` from a cast sigma pair, which Lean's
-- `cast` doesn't reduce for.
-- The `revert + generalize + subst + rw` technique
-- handles this for standalone lemmas but the
-- `generalize` fails here because the transport
-- proof in `coalgCopresheafShapeAt` creates a
-- dependency on `a` that survives the
-- generalization.

end GebLean

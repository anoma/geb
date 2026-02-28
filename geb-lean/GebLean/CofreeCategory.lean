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

/-! ### Sigma-Pair Infrastructure -/

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
  -- Generalize `c.a.left a`, decompose into
  -- fiber and M-type, subst the fiber equality,
  -- derive the shape equality, rw to collapse
  -- the transport, then `rfl`.
  revert e_raw he
  generalize hca : c.a.left a = ca
  obtain ⟨xv, mv⟩ := ca
  intro e_raw he
  have hfib : xv = c.A.hom a :=
    (congrArg Sigma.fst hca).symm.trans
      (comonadCoalgFiberEq c a)
  subst hfib
  have h_shapeAt_eq :
      coalgCopresheafShapeAt c a =
      polyCofreeToShape c.A P mv := by
    let toShape := fun (p :
        Σ x, PolyCofreeM c.A P x) =>
      (⟨p.1, polyCofreeToShape c.A P p.2⟩ :
        Σ x, PolyCofreeShape P x)
    have h1 := congrArg toShape hca
    have h3 := h1.symm.trans
      (coalgCopresheafTargetRaw_eq c a)
    exact (eq_of_heq
      (Sigma.ext_iff.mp h3).2).symm
  dsimp only at e_raw
  revert e_shape he
  rw [h_shapeAt_eq]
  intro e_shape he
  have he_eq := eq_of_heq he
  subst he_eq
  rfl

/--
The `CastPos` at depth 1 is HEq to the input
position. The cast between the transported and
raw position types is an identity up to HEq.
-/
lemma coalgCopresheafCastPos1_collapse
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left)
    (e_shape : (polyBetweenFamily X X P (c.A.hom a)
      (coalgCopresheafShapeAt c a).head.2).left) :
    HEq
      (coalgCopresheafCastPos c a 1
        ⟨e_shape, PUnit.unit⟩)
      (⟨e_shape, PUnit.unit⟩ :
        PolyCofreeAnnotPosAt P
          (coalgCopresheafShapeAt c a) 1) :=
  by simp only [coalgCopresheafCastPos]
     exact cast_heq _ _

/--
The depth-1 target equality: the copresheaf
target of the child annotation at a shape edge
equals `tgtAt 1` of the parent's target.
Chains `target_sigma`, `rawToShape`, and
`tgtAt_transport`, using `CastPos1_collapse`
for the cast round-trip.
-/
lemma coalgCopresheafChild_depth1_target
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left)
    (e_shape : (polyBetweenFamily X X P (c.A.hom a)
      (coalgCopresheafShapeAt c a).head.2).left) :
    let e_raw := (coalgCopresheafCastPos c a 1
      ⟨e_shape, PUnit.unit⟩).1
    let e_m := polyCofreeShapePosToMPos c.A P
      (c.a.left a).2 e_raw
    coalgCopresheafTarget c
      (coalgCopresheafChild c a e_m) =
    (coalgCopresheafTarget c a).tgtAt 1
      ⟨e_shape, PUnit.unit⟩ := by
  intro e_raw e_m
  have h_collapse :=
    coalgCopresheafCastPos1_collapse c a e_shape
  -- The raw target object (using the M-type
  -- fiber instead of c.A.hom a).
  let rawObj : PolyCofreeCat P :=
    ⟨(c.a.left a).1,
      polyCofreeToShape c.A P (c.a.left a).2⟩
  have h_raw_eq : rawObj =
      coalgCopresheafTarget c a := by
    let h := coalgCopresheafTargetRaw_eq c a
    exact PolyCofreeCat.ext
      (congrArg Sigma.fst h)
      (Sigma.ext_iff.mp h).2
  -- Chain `target_sigma` and `rawToShape` to
  -- get the child target in raw coordinates.
  have h_raw_tgt :
      coalgCopresheafTarget c
        (coalgCopresheafChild c a e_m) =
      rawObj.tgtAt 1
        ⟨e_raw, PUnit.unit⟩ := by
    simp only [coalgCopresheafTarget,
      PolyCofreeCat.tgtAt, PolyCofreeAnnotFiberAt,
      polyCofreeSubtreeAt]
    have h_chain :=
      (coalgCopresheafChild_target_sigma
        c a e_m).trans
      (coalgCopresheafChild_rawToShape
        c a e_raw)
    exact PolyCofreeCat.ext
      (congrArg Sigma.fst h_chain)
      (Sigma.ext_iff.mp h_chain).2
  -- Convert from raw to transported coordinates
  -- using `tgtAt_transport`.
  rw [h_raw_tgt,
    PolyCofreeCat.tgtAt_transport h_raw_eq]
  congr 1
  -- The `CastPos` (transported → raw) composed
  -- with `tgtAt_transport` (raw → transported)
  -- is the identity, by `cast_cast` + `cast_eq`.
  -- ⟨e_raw, ()⟩ = CastPos c a 1 ⟨e_shape, ()⟩
  -- because e_raw = (.1) and .2 = PUnit.unit.
  have h_era :
      (⟨e_raw, PUnit.unit⟩ :
        PolyCofreeAnnotPosAt P rawObj.shape 1) =
      coalgCopresheafCastPos c a 1
        ⟨e_shape, PUnit.unit⟩ := by
    rfl
  simp only [h_era, coalgCopresheafCastPos,
    cast_cast, cast_eq]

/-! ### Copresheaf Morphism Action -/

/--
The copresheaf morphism action at a given depth
and position, defined by induction on depth.
At depth 0, the element is returned unchanged.
At depth n+1, the child annotation is extracted
via self-consistency, and the function recurses
at depth n.
-/
def coalgCopresheafMapByDepth {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left) :
    (n : Nat) →
    (pos : PolyCofreeAnnotPosAt P
      (coalgCopresheafShapeAt c a) n) →
    coalgCopresheafObj c
      ((coalgCopresheafTarget c a).tgtAt
        n pos)
  | 0, _ => ⟨a, rfl⟩
  | n + 1, ⟨e_shape, rest⟩ => by
    let m := (c.a.left a).2
    let e_raw := (coalgCopresheafCastPos c a 1
      ⟨e_shape, PUnit.unit⟩).1
    let e_m := polyCofreeShapePosToMPos
      c.A P m e_raw
    let child := coalgCopresheafChild c a e_m
    have h_child_target :=
      coalgCopresheafChild_depth1_target
        c a e_shape
    let rest_child :
        PolyCofreeAnnotPosAt P
          (coalgCopresheafShapeAt c child)
          n :=
      cast (congrArg
        (fun obj => PolyCofreeAnnotPosAt P
          obj.shape n)
        h_child_target.symm) rest
    let ⟨a', h'⟩ :=
      coalgCopresheafMapByDepth c child n
        rest_child
    exact ⟨a', h'.trans
      ((PolyCofreeCat.tgtAt_transport
        h_child_target n rest_child).trans
        (by simp only [rest_child, cast_cast,
          cast_eq]; rfl))⟩

/--
The copresheaf morphism action: given a morphism
`f : src ⟶ tgt` in the cofree category and an
element of the copresheaf at `src`, extract the
annotation at the position determined by `f`.
-/
def coalgCopresheafMap {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    {src tgt : PolyCofreeCat P}
    (f : src ⟶ tgt)
    (elem : coalgCopresheafObj c src) :
    coalgCopresheafObj c tgt :=
  let ⟨a, ha⟩ := elem
  let posInShape :
      PolyCofreeAnnotPosAt P
        (coalgCopresheafShapeAt c a)
        f.depth :=
    cast (congrArg (fun obj =>
      PolyCofreeAnnotPosAt P obj.shape
        f.depth) ha.symm)
      f.pos
  let ⟨a', h'⟩ :=
    coalgCopresheafMapByDepth c a
      f.depth posInShape
  ⟨a', h'.trans (by
    -- (target c a).tgtAt f.depth posInShape = tgt
    -- posInShape = cast ha.symm f.pos, so
    -- (target c a).tgtAt posInShape
    -- = src.tgtAt f.pos  (by tgtAt_transport)
    -- = tgt  (by f.fiber_eq + f.subtree_eq)
    rw [PolyCofreeCat.tgtAt_transport
      ha f.depth posInShape]
    simp only [posInShape, cast_cast, cast_eq]
    exact PolyCofreeCat.ext f.fiber_eq
      f.subtree_eq)⟩

/--
Composition law for the copresheaf map:
extraction at a composed morphism equals
sequential extraction.
-/
lemma coalgCopresheafMap_comp {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    {src mid tgt : PolyCofreeCat P}
    (f : src ⟶ mid) (g : mid ⟶ tgt)
    (elem : coalgCopresheafObj c src) :
    (coalgCopresheafMap c (f ≫ g) elem).val =
    (coalgCopresheafMap c g
      (coalgCopresheafMap c f elem)).val := by
  obtain ⟨a, ha⟩ := elem
  -- Induction on f.depth, relating composed
  -- extraction to sequential extraction via
  -- the recursive structure.
  -- At depth 0: f is the identity, and
  -- f ≫ g = g, so both sides equal
  -- coalgCopresheafMap c g elem.
  -- At depth n+1: f decomposes into a child
  -- step + depth-n recursion.
  obtain ⟨_, _⟩ := mid
  obtain ⟨_, _⟩ := tgt
  obtain ⟨fn, fp, hff, hfs⟩ := f
  obtain ⟨gn, gp, hgf, hgs⟩ := g
  dsimp at hff hfs hgf hgs
  subst hff hgf
  cases eq_of_heq hfs
  cases eq_of_heq hgs
  -- After subst, f and g have rfl proofs.
  -- The composition uses path concatenation.
  -- Induction on fn (depth of f).
  induction fn generalizing src a with
  | zero => rfl
  | succ fn ih =>
    subst ha
    obtain ⟨e_shape, rest_fp⟩ := fp
    let e_raw := (coalgCopresheafCastPos c a 1
      ⟨e_shape, PUnit.unit⟩).1
    let e_m := polyCofreeShapePosToMPos
      c.A P (c.a.left a).2 e_raw
    let child := coalgCopresheafChild c a e_m
    let h_child :=
      coalgCopresheafChild_depth1_target
        c a e_shape
    exact ih child h_child rest_fp
      HEq.rfl gp HEq.rfl

/--
Identity law for the copresheaf map:
mapping by the identity morphism returns the
original element.
-/
lemma coalgCopresheafMap_id {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (obj : PolyCofreeCat P)
    (elem : coalgCopresheafObj c obj) :
    coalgCopresheafMap c (𝟙 obj) elem = elem := by
  obtain ⟨a, ha⟩ := elem
  subst ha
  rfl

/--
Functorial composition law: mapping by `f ≫ g`
equals the composition of mapping by `f` then `g`.
-/
lemma coalgCopresheaf_map_comp {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    {src mid tgt : PolyCofreeCat P}
    (f : src ⟶ mid) (g : mid ⟶ tgt)
    (elem : coalgCopresheafObj c src) :
    coalgCopresheafMap c (f ≫ g) elem =
    coalgCopresheafMap c g
      (coalgCopresheafMap c f elem) :=
  Subtype.ext (coalgCopresheafMap_comp c f g elem)

/--
The copresheaf functor for a P-coalgebra `c`:
a functor from the cofree category to `Type u`
sending each object to the fiber of the
coalgebra carrier over that object, and each
morphism to the extraction map.
-/
def coalgCopresheaf {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P)) :
    PolyCofreeCat P ⥤ Type u where
  obj := coalgCopresheafObj c
  map f := coalgCopresheafMap c f
  map_id obj := by
    ext elem
    exact coalgCopresheafMap_id c obj elem
  map_comp f g := by
    ext elem
    exact coalgCopresheaf_map_comp c f g elem

/-! ## Copresheaf Functor: Morphism Action -/

/--
A comonad coalgebra morphism preserves the fiber
component of the copresheaf target: if `h : c₁ ⟶ c₂`
is a coalgebra morphism, then `c₂.A.hom (h.f.left a)`
equals `c₁.A.hom a`.
-/
lemma coalgCopresheafFunctor_fiber {P : PolyEndo X}
    {c₁ c₂ : Comonad.Coalgebra
      (polyCofreeComonad X P)}
    (h : c₁ ⟶ c₂) (a : c₁.A.left) :
    c₂.A.hom (h.f.left a) = c₁.A.hom a := by
  have := congrFun (Over.w h.f) a
  simp only [types_comp_apply] at this
  exact this

/--
The coalgebra morphism condition evaluated at an
element: `c₂.a` applied to `h.f.left a` equals the
comonad map of `h.f` applied to `c₁.a.left a`.
The comonad map sends `⟨x, m⟩` to
`⟨x, polyCofreeMapAt m⟩`.
-/
lemma coalgMorphism_structure_eq {P : PolyEndo X}
    {c₁ c₂ : Comonad.Coalgebra
      (polyCofreeComonad X P)}
    (h : c₁ ⟶ c₂) (a : c₁.A.left) :
    c₂.a.left (h.f.left a) =
    polyCofreeMapLeft c₁.A c₂.A P h.f
      (c₁.a.left a) := by
  have hcomm := congrFun
    (Over.OverMorphism.ext_iff.mp h.h) a
  simp only [Over.comp_left, types_comp_apply,
    polyCofreeComonad, Adjunction.toComonad]
      at hcomm
  change
    ((polyCofreeFunctor P ⋙
      polyCoalgForgetFunctor P).map h.f).left
      (c₁.a.left a) =
    c₂.a.left (h.f.left a) at hcomm
  simp only [Functor.comp_map,
    polyCofreeFunctor,
    Endofunctor.Coalgebra.forget,
    polyCofreeCoalgMap,
    polyCofreeMap] at hcomm
  exact hcomm.symm

/--
The `.1` component of the structure equation:
`(c₂.a.left (h.f.left a)).1 = (c₁.a.left a).1`.
-/
lemma coalgMorphism_structure_fst {P : PolyEndo X}
    {c₁ c₂ : Comonad.Coalgebra
      (polyCofreeComonad X P)}
    (h : c₁ ⟶ c₂) (a : c₁.A.left) :
    (c₂.a.left (h.f.left a)).1 =
    (c₁.a.left a).1 :=
  congrArg Sigma.fst
    (coalgMorphism_structure_eq h a)

/--
The `.2` component of the structure equation:
the M-type of `h.f.left a` under `c₂` is HEq to the
mapped M-type of `a` under `c₁`.
-/
lemma coalgMorphism_structure_snd {P : PolyEndo X}
    {c₁ c₂ : Comonad.Coalgebra
      (polyCofreeComonad X P)}
    (h : c₁ ⟶ c₂) (a : c₁.A.left) :
    HEq (c₂.a.left (h.f.left a)).2
      (polyCofreeMapAt c₁.A c₂.A P h.f
        (c₁.a.left a).2) :=
  (Sigma.ext_iff.mp
    (coalgMorphism_structure_eq h a)).2

/--
The raw target sigma pair is preserved by a
coalgebra morphism: applying the raw shape
extraction to `h.f.left a` under `c₂` gives the
same sigma pair as applying it to `a` under `c₁`.
-/
lemma coalgMorphism_rawTarget_eq {P : PolyEndo X}
    {c₁ c₂ : Comonad.Coalgebra
      (polyCofreeComonad X P)}
    (h : c₁ ⟶ c₂) (a : c₁.A.left) :
    coalgCopresheafTargetRaw c₂ (h.f.left a) =
    coalgCopresheafTargetRaw c₁ a := by
  simp only [coalgCopresheafTargetRaw]
  have h_eq := coalgMorphism_structure_eq h a
  have h_fst := coalgMorphism_structure_fst h a
  have h_snd := coalgMorphism_structure_snd h a
  have h_map := polyCofreeToShape_map
    c₁.A c₂.A P h.f (c₁.a.left a).2
  -- The raw targets are both sigma pairs
  -- (fiber, shape). We show each component:
  -- fst: by coalgMorphism_structure_fst
  -- snd: by transport through the mapped M-type
  --   and polyCofreeToShape_map.
  have h_shape_heq : HEq
      (polyCofreeToShape c₂.A P
        (c₂.a.left (h.f.left a)).2)
      (polyCofreeToShape c₁.A P
        (c₁.a.left a).2) := by
    have : (c₂.a.left (h.f.left a)) =
        polyCofreeMapLeft c₁.A c₂.A P h.f
          (c₁.a.left a) := h_eq
    rw [this]
    simp only [polyCofreeMapLeft]
    exact heq_of_eq h_map
  exact Sigma.ext h_fst h_shape_heq

/--
A coalgebra morphism preserves the copresheaf
target: `coalgCopresheafTarget c₂ (h.f.left a)`
equals `coalgCopresheafTarget c₁ a`.
-/
lemma coalgMorphism_target_eq {P : PolyEndo X}
    {c₁ c₂ : Comonad.Coalgebra
      (polyCofreeComonad X P)}
    (h : c₁ ⟶ c₂) (a : c₁.A.left) :
    coalgCopresheafTarget c₂ (h.f.left a) =
    coalgCopresheafTarget c₁ a := by
  have h1 := coalgCopresheafTargetRaw_eq c₂
    (h.f.left a)
  have h2 := coalgCopresheafTargetRaw_eq c₁ a
  have h3 := coalgMorphism_rawTarget_eq h a
  simp only [coalgCopresheafTarget]
  exact (PolyCofreeCat.ext
    (congrArg Sigma.fst (h1.symm.trans h3 |>.trans h2))
    ((Sigma.ext_iff.mp
      (h1.symm.trans h3 |>.trans h2)).2))

/--
The component of the natural transformation induced
by a coalgebra morphism: sends `⟨a, ha⟩` to
`⟨h.f.left a, ...⟩`.
-/
def coalgCopresheafFunctor_app {P : PolyEndo X}
    {c₁ c₂ : Comonad.Coalgebra
      (polyCofreeComonad X P)}
    (h : c₁ ⟶ c₂)
    (obj : PolyCofreeCat P) :
    coalgCopresheafObj c₁ obj →
    coalgCopresheafObj c₂ obj :=
  fun ⟨a, ha⟩ =>
    ⟨h.f.left a,
      (coalgMorphism_target_eq h a).trans ha⟩

/--
A coalgebra morphism preserves the copresheaf
shape: the transported shape at `h.f.left a`
under `c₂` equals the transported shape at `a`
under `c₁`.
-/
lemma coalgMorphism_shape_eq {P : PolyEndo X}
    {c₁ c₂ : Comonad.Coalgebra
      (polyCofreeComonad X P)}
    (h : c₁ ⟶ c₂) (a : c₁.A.left) :
    HEq (coalgCopresheafShapeAt c₂
        (h.f.left a))
      (coalgCopresheafShapeAt c₁ a) := by
  have h_eq := coalgMorphism_target_eq h a
  simp only [coalgCopresheafTarget] at h_eq
  exact ((PolyCofreeCat.mk.injEq _ _ _ _).mp
    h_eq).2

/--
`coalgCopresheafMapByDepth` at `.val` is invariant
under transport of the carrier element along an
equality: if `a₁ = a₂` and positions are HEq,
then the extracted values coincide.
-/
lemma coalgCopresheafMapByDepth_cast_a
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    {a₁ a₂ : c.A.left} (ha : a₁ = a₂)
    (n : Nat)
    (pos₁ : PolyCofreeAnnotPosAt P
      (coalgCopresheafShapeAt c a₁) n)
    (pos₂ : PolyCofreeAnnotPosAt P
      (coalgCopresheafShapeAt c a₂) n)
    (hpos : HEq pos₁ pos₂) :
    (coalgCopresheafMapByDepth c a₁ n pos₁).val =
    (coalgCopresheafMapByDepth c a₂ n pos₂).val := by
  subst ha
  exact congrArg
    (fun pos =>
      (coalgCopresheafMapByDepth c a₁ n pos).val)
    (eq_of_heq hpos)

/--
A coalgebra morphism maps the child annotation
of `c₁` at `a` to the child annotation of `c₂`
at `h.f.left a`, when the M-type edges are HEq.
This follows from the coalgebra morphism condition
(structure equation), `polyCofreeExtract_mapAt_val`,
and `polyCofreeMapAt_children_heq`.
-/
lemma coalgMorphism_child_val_eq {P : PolyEndo X}
    {c₁ c₂ : Comonad.Coalgebra
      (polyCofreeComonad X P)}
    (h : c₁ ⟶ c₂) (a : c₁.A.left)
    (e₁ : (polyBetweenFamily X X
      (polyScale c₁.A P) (c₁.a.left a).1
      (c₁.a.left a).2.head).left)
    (e₂ : (polyBetweenFamily X X
      (polyScale c₂.A P)
      (c₂.a.left (h.f.left a)).1
      (c₂.a.left (h.f.left a)).2.head).left)
    (he : HEq e₁ e₂) :
    h.f.left (coalgCopresheafChild c₁ a e₁) =
    coalgCopresheafChild c₂ (h.f.left a) e₂ := by
  simp only [coalgCopresheafChild]
  rw [← polyCofreeExtract_mapAt_val c₁.A c₂.A P
    h.f ((c₁.a.left a).2.children e₁)]
  -- Generalize the sigma pairs and subst the
  -- structure equation to expose polyCofreeMapAt.
  revert e₁ e₂ he
  have h_str := coalgMorphism_structure_eq h a
  generalize c₁.a.left a = ca₁ at h_str ⊢
  generalize c₂.a.left (h.f.left a) = ca₂ at *
  subst h_str
  obtain ⟨x₁, m₁⟩ := ca₁
  simp only [polyCofreeMapLeft]
  intro e₁ e₂ he
  apply polyCofreeExtract_val_of_heq c₂.A P
    (overType_hom_heq
      (congrArg (polyBetweenFamily X X P x₁)
        (polyCofreeMapAt_head_snd c₁.A c₂.A P
          h.f m₁).symm) e₁ e₂ he)
    (polyCofreeMapAt_children_heq c₁.A c₂.A P
      h.f m₁ e₁ e₂ he)

/--
The `.fst` of a cast of `⟨e, PUnit.unit⟩`
through `polyCofreeAnnotPosAt_cast_fiber` at
depth 1 is HEq to `e`.
-/
lemma polyCofreeAnnotPosAt_cast_fst_heq
    {P : PolyEndo X} {y₁ y₂ : X}
    (hfiber : y₁ = y₂)
    {s₁ : PolyCofreeShape P y₁}
    {s₂ : PolyCofreeShape P y₂}
    (hshape : HEq s₁ s₂)
    (e : (polyBetweenFamily X X P y₁
      s₁.head.2).left) :
    HEq
      (cast (polyCofreeAnnotPosAt_cast_fiber
        hfiber hshape 1)
        ⟨e, PUnit.unit⟩).fst
      e := by
  subst hfiber
  have hs_eq := eq_of_heq hshape
  subst hs_eq
  rfl

/--
The shape-to-M-type edge conversion preserves
HEq: a shape edge is HEq to the M-type edge
obtained by applying `coalgCopresheafCastPos`
and `polyCofreeShapePosToMPos`.
-/
lemma coalgCopresheafShapeToMEdge_heq
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left)
    (e_shape : (polyBetweenFamily X X P
      (c.A.hom a)
      (coalgCopresheafShapeAt c
        a).head.2).left) :
    HEq e_shape
      (polyCofreeShapePosToMPos c.A P
        (c.a.left a).2
        ((coalgCopresheafCastPos c a 1
          ⟨e_shape, PUnit.unit⟩).1)) :=
  (polyCofreeAnnotPosAt_cast_fst_heq
    (comonadCoalgFiberEq c a).symm
    (coalgCopresheafShapeAt_heq c a)
    e_shape).symm.trans
  (polyCofreeShapePosToMPos_heq c.A P
    (c.a.left a).2 _)

lemma coalgMorphism_child_val_eq_shape
    {P : PolyEndo X}
    {c₁ c₂ : Comonad.Coalgebra
      (polyCofreeComonad X P)}
    (h : c₁ ⟶ c₂) (a : c₁.A.left)
    (e₁ : (polyBetweenFamily X X P (c₁.A.hom a)
      (coalgCopresheafShapeAt c₁ a).head.2).left)
    (e₂ : (polyBetweenFamily X X P
      (c₂.A.hom (h.f.left a))
      ((coalgCopresheafShapeAt c₂
        (h.f.left a)).head.2)).left)
    (he : HEq e₁ e₂) :
    let e_raw₁ := (coalgCopresheafCastPos
      c₁ a 1 ⟨e₁, PUnit.unit⟩).1
    let e_m₁ := polyCofreeShapePosToMPos
      c₁.A P (c₁.a.left a).2 e_raw₁
    let e_raw₂ := (coalgCopresheafCastPos
      c₂ (h.f.left a) 1
      ⟨e₂, PUnit.unit⟩).1
    let e_m₂ := polyCofreeShapePosToMPos
      c₂.A P (c₂.a.left (h.f.left a)).2
      e_raw₂
    h.f.left
      (coalgCopresheafChild c₁ a e_m₁) =
    coalgCopresheafChild c₂
      (h.f.left a) e_m₂ := by
  dsimp only []
  apply coalgMorphism_child_val_eq h a
  exact (coalgCopresheafShapeToMEdge_heq
    c₁ a e₁).symm.trans
    (he.trans
      (coalgCopresheafShapeToMEdge_heq
        c₂ (h.f.left a) e₂))

/--
Extract the first component HEq from a
sigma-typed position HEq at successor depth.
-/
lemma polyCofreeAnnotPosAt_succ_fst_heq
    {P : PolyEndo X} {y₁ y₂ : X}
    {s₁ : PolyCofreeShape P y₁}
    {s₂ : PolyCofreeShape P y₂}
    (hy : y₁ = y₂) (hs : HEq s₁ s₂)
    {n : Nat}
    {p₁ : PolyCofreeAnnotPosAt P s₁ (n + 1)}
    {p₂ : PolyCofreeAnnotPosAt P s₂ (n + 1)}
    (hp : HEq p₁ p₂) :
    HEq p₁.1 p₂.1 := by
  subst hy
  have hs_eq := eq_of_heq hs; subst hs_eq
  have hp_eq := eq_of_heq hp; subst hp_eq
  rfl

/--
Extract the second component HEq from a
sigma-typed position HEq at successor depth.
-/
lemma polyCofreeAnnotPosAt_succ_snd_heq
    {P : PolyEndo X} {y₁ y₂ : X}
    {s₁ : PolyCofreeShape P y₁}
    {s₂ : PolyCofreeShape P y₂}
    (hy : y₁ = y₂) (hs : HEq s₁ s₂)
    {n : Nat}
    {p₁ : PolyCofreeAnnotPosAt P s₁ (n + 1)}
    {p₂ : PolyCofreeAnnotPosAt P s₂ (n + 1)}
    (hp : HEq p₁ p₂) :
    HEq p₁.2 p₂.2 := by
  subst hy
  have hs_eq := eq_of_heq hs; subst hs_eq
  have hp_eq := eq_of_heq hp; subst hp_eq
  rfl

/--
The coalgebra morphism commutes with
applying `h.f.left` to the result of extracting
from `c₁`'s tree equals extracting from `c₂`'s
tree (with transported position).
-/
lemma coalgCopresheafFunctor_nat_byDepth
    {P : PolyEndo X}
    {c₁ c₂ : Comonad.Coalgebra
      (polyCofreeComonad X P)}
    (h : c₁ ⟶ c₂) (a : c₁.A.left)
    (n : Nat)
    (pos₁ : PolyCofreeAnnotPosAt P
      (coalgCopresheafShapeAt c₁ a) n)
    (pos₂ : PolyCofreeAnnotPosAt P
      (coalgCopresheafShapeAt c₂
        (h.f.left a)) n)
    (hpos : HEq pos₁ pos₂) :
    h.f.left
      (coalgCopresheafMapByDepth c₁ a
        n pos₁).val =
    (coalgCopresheafMapByDepth c₂
      (h.f.left a) n pos₂).val := by
  induction n generalizing a with
  | zero =>
    simp only [coalgCopresheafMapByDepth]
  | succ n ih =>
    obtain ⟨e₁, rest₁⟩ := pos₁
    obtain ⟨e₂, rest₂⟩ := pos₂
    -- c₁ side: mirror the MapByDepth definition
    let m₁ := (c₁.a.left a).2
    let e_raw₁ := (coalgCopresheafCastPos c₁ a 1
      ⟨e₁, PUnit.unit⟩).1
    let e_m₁ := polyCofreeShapePosToMPos
      c₁.A P m₁ e_raw₁
    let child₁ := coalgCopresheafChild c₁ a e_m₁
    let h_child₁ :=
      coalgCopresheafChild_depth1_target c₁ a e₁
    -- c₂ side
    let m₂ := (c₂.a.left (h.f.left a)).2
    let e_raw₂ := (coalgCopresheafCastPos c₂
      (h.f.left a) 1 ⟨e₂, PUnit.unit⟩).1
    let e_m₂ := polyCofreeShapePosToMPos
      c₂.A P m₂ e_raw₂
    let child₂ := coalgCopresheafChild
      c₂ (h.f.left a) e_m₂
    let h_child₂ :=
      coalgCopresheafChild_depth1_target c₂
        (h.f.left a) e₂
    let rest₁' : PolyCofreeAnnotPosAt P
        (coalgCopresheafShapeAt c₁ child₁) n :=
      cast (congrArg (fun obj =>
        PolyCofreeAnnotPosAt P obj.shape n)
        h_child₁.symm) rest₁
    have h_lhs_reduce :
        (coalgCopresheafMapByDepth c₁ a
          (n + 1) ⟨e₁, rest₁⟩).val =
        (coalgCopresheafMapByDepth c₁ child₁ n
          rest₁').val := by
      rfl
    let rest₂' : PolyCofreeAnnotPosAt P
        (coalgCopresheafShapeAt c₂ child₂) n :=
      cast (congrArg (fun obj =>
        PolyCofreeAnnotPosAt P obj.shape n)
        h_child₂.symm) rest₂
    have h_rhs_reduce :
        (coalgCopresheafMapByDepth c₂
          (h.f.left a) (n + 1) ⟨e₂, rest₂⟩).val =
        (coalgCopresheafMapByDepth c₂ child₂ n
          rest₂').val := by
      rfl
    rw [h_lhs_reduce, h_rhs_reduce]
    -- Extract edge HEq from position HEq
    have he : HEq e₁ e₂ :=
      polyCofreeAnnotPosAt_succ_fst_heq
        ((congrFun (Over.w h.f) a).symm)
        ((coalgMorphism_shape_eq h a).symm)
        hpos
    -- Child equality from edge HEq
    have h_child_eq :=
      coalgMorphism_child_val_eq_shape
        h a e₁ e₂ he
    -- Extract rest HEq from position HEq
    have h_rest_heq : HEq rest₁ rest₂ :=
      polyCofreeAnnotPosAt_succ_snd_heq
        ((congrFun (Over.w h.f) a).symm)
        ((coalgMorphism_shape_eq h a).symm)
        hpos
    -- Cast rest₂' to h.f.left child₁
    let rest₂_h : PolyCofreeAnnotPosAt P
        (coalgCopresheafShapeAt c₂
          (h.f.left child₁)) n :=
      cast (congrArg (fun b =>
        PolyCofreeAnnotPosAt P
          (coalgCopresheafShapeAt c₂ b) n)
        h_child_eq.symm) rest₂'
    -- Chain cast_heq for rest positions
    have h_rest_ih : HEq rest₁' rest₂_h :=
      (cast_heq _ rest₁).trans
        (h_rest_heq.trans
          ((cast_heq _ rest₂).symm.trans
            (cast_heq _ rest₂').symm))
    -- Combine IH at child₁ with cast_a
    calc h.f.left
          (coalgCopresheafMapByDepth c₁
            child₁ n rest₁').val
        = (coalgCopresheafMapByDepth c₂
            (h.f.left child₁) n rest₂_h).val :=
          ih child₁ rest₁' rest₂_h h_rest_ih
      _ = (coalgCopresheafMapByDepth c₂
            child₂ n rest₂').val :=
          coalgCopresheafMapByDepth_cast_a c₂
            h_child_eq n rest₂_h rest₂'
            (cast_heq _ rest₂')

/--
Naturality of the copresheaf transformation
induced by a coalgebra morphism: the `.val`
component of the result commutes with the
copresheaf map action.
-/
lemma coalgCopresheafFunctor_naturality_val
    {P : PolyEndo X}
    {c₁ c₂ : Comonad.Coalgebra
      (polyCofreeComonad X P)}
    (h : c₁ ⟶ c₂)
    {src tgt : PolyCofreeCat P}
    (f : src ⟶ tgt)
    (elem : coalgCopresheafObj c₁ src) :
    (coalgCopresheafFunctor_app h tgt
      (coalgCopresheafMap c₁ f elem)).val =
    (coalgCopresheafMap c₂ f
      (coalgCopresheafFunctor_app h src
        elem)).val := by
  obtain ⟨a, ha⟩ := elem
  exact coalgCopresheafFunctor_nat_byDepth
    h a f.depth _ _
    ((cast_heq _ f.pos).trans
      (cast_heq _ f.pos).symm)

/--
A coalgebra morphism induces a natural
transformation between the copresheaf functors.
-/
def coalgCopresheafFunctor_natTrans
    {P : PolyEndo X}
    {c₁ c₂ : Comonad.Coalgebra
      (polyCofreeComonad X P)}
    (h : c₁ ⟶ c₂) :
    coalgCopresheaf c₁ ⟶ coalgCopresheaf c₂ where
  app obj := coalgCopresheafFunctor_app h obj
  naturality src tgt f := by
    ext elem
    exact Subtype.ext
      (coalgCopresheafFunctor_naturality_val
        h f elem)

/--
The copresheaf functor from the category of
P-coalgebras to the copresheaf topos on the
cofree category.
-/
def coalgCopresheafFunctor (P : PolyEndo X) :
    Comonad.Coalgebra (polyCofreeComonad X P) ⥤
    (PolyCofreeCat P ⥤ Type u) where
  obj c := coalgCopresheaf c
  map h := coalgCopresheafFunctor_natTrans h
  map_id c := by
    ext obj elem
    simp only [CategoryStruct.id]
    exact Subtype.ext rfl
  map_comp f g := by
    ext obj elem
    simp only [CategoryStruct.comp]
    exact Subtype.ext rfl

/-! ## Copresheaf to Coalgebra (Inverse) -/

/--
The carrier of the coalgebra associated to a
copresheaf: the total space over all cofree
category objects.
-/
def copresheafCoalgCarrier (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u) :
    Over X :=
  Over.mk (fun ⟨obj, _⟩ => obj.fiber :
    (Σ obj : PolyCofreeCat P, F.obj obj) → X)

/--
The child object in the cofree category at a
given edge of the root shape.
-/
def polyCofreeCatChild (P : PolyEndo X)
    (obj : PolyCofreeCat P)
    (e : (polyBetweenFamily X X P obj.fiber
      obj.shape.head.2).left) :
    PolyCofreeCat P where
  fiber := (polyBetweenFamily X X P obj.fiber
    obj.shape.head.2).hom e
  shape := obj.shape.children e

/--
The depth-1 morphism in the cofree category
from an object to its child at a given edge.
-/
def polyCofreeCatEdge (P : PolyEndo X)
    (obj : PolyCofreeCat P)
    (e : (polyBetweenFamily X X P obj.fiber
      obj.shape.head.2).left) :
    obj ⟶ polyCofreeCatChild P obj e where
  depth := 1
  pos := ⟨e, PUnit.unit⟩
  fiber_eq := rfl
  subtree_eq := HEq.rfl

/--
The approximation at depth n for the M-type tree
constructed from a copresheaf. At each node, the
annotation is a copresheaf element pushed forward
along the edge morphism.
-/
def copresheafCoalgApprox (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (elem : F.obj obj) :
    ∀ n, PolyCofixApprox
      (polyScale (copresheafCoalgCarrier P F) P)
      n obj.fiber
  | 0 => .continue obj.fiber
  | n + 1 => .intro obj.fiber
      ⟨⟨⟨obj, elem⟩, rfl⟩, obj.shape.head.2⟩
      (fun e => copresheafCoalgApprox P F
        (polyCofreeCatChild P obj e)
        (F.map (polyCofreeCatEdge P obj e) elem)
        n)

/--
Successive approximations from a copresheaf agree.
-/
lemma copresheafCoalgApprox_agree (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (elem : F.obj obj) :
    ∀ n, PolyCofixAgree
      (polyScale (copresheafCoalgCarrier P F) P)
      (copresheafCoalgApprox P F obj elem n)
      (copresheafCoalgApprox P F obj elem (n + 1))
  | 0 => .continue _ _
  | n + 1 => .intro _ _
      (fun e => copresheafCoalgApprox_agree P F
        (polyCofreeCatChild P obj e)
        (F.map (polyCofreeCatEdge P obj e) elem)
        n)

/--
The M-type tree constructed from a copresheaf
element. Each node is annotated with the
copresheaf element pushed forward along the path
from the root.
-/
def copresheafCoalgMType (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (elem : F.obj obj) :
    PolyCofreeM (copresheafCoalgCarrier P F) P
      obj.fiber where
  approx := copresheafCoalgApprox P F obj elem
  consistent :=
    copresheafCoalgApprox_agree P F obj elem

/--
The head of the copresheaf M-type is the
copresheaf index.
-/
lemma copresheafCoalgMType_head (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (elem : F.obj obj) :
    (copresheafCoalgMType P F obj elem).head =
    ⟨⟨⟨obj, elem⟩, rfl⟩, obj.shape.head.2⟩ := rfl

/--
The child approximation of the copresheaf M-type
at position `e` and depth `n` equals the copresheaf
approximation for the child.
-/
lemma copresheafCoalgMType_childApprox
    (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (elem : F.obj obj)
    (e : (polyBetweenFamily X X P obj.fiber
      obj.shape.head.2).left)
    (n : Nat) :
    (copresheafCoalgMType P F obj elem
      ).childApproxAt e n =
    copresheafCoalgApprox P F
      (polyCofreeCatChild P obj e)
      (F.map (polyCofreeCatEdge P obj e) elem)
      n := by
  match n with
  | 0 => rfl
  | n + 1 =>
    simp only [PolyCofix.childApproxAt,
      PolyCofix.childApproxAt_succ]
    let m := copresheafCoalgMType P F obj elem
    have h :=
      PolyCofix.childApproxAt_succ_aux_proof_irrel
        m.head (m.approx (n + 2))
        (m.index_eq_head (n + 1)) rfl e
    rw [h]
    rfl

/--
The children of the copresheaf M-type at position
`e` equals the copresheaf M-type for the child.
-/
lemma copresheafCoalgMType_children
    (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (elem : F.obj obj)
    (e : (polyBetweenFamily X X P obj.fiber
      obj.shape.head.2).left) :
    (copresheafCoalgMType P F obj elem
      ).children e =
    copresheafCoalgMType P F
      (polyCofreeCatChild P obj e)
      (F.map (polyCofreeCatEdge P obj e) elem)
    := by
  apply PolyCofix.ext
  intro n
  exact copresheafCoalgMType_childApprox
    P F obj elem e n

/--
Extracting the child annotation from the copresheaf
M-type at position `e` yields the child copresheaf
element.
-/
lemma copresheafCoalgMType_extract
    (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (elem : F.obj obj)
    (e : (polyBetweenFamily X X P obj.fiber
      obj.shape.head.2).left) :
    (polyCofreeExtract
      (copresheafCoalgCarrier P F) P
      ((copresheafCoalgMType P F obj elem
        ).children e)).val =
    ⟨polyCofreeCatChild P obj e,
      F.map (polyCofreeCatEdge P obj e)
        elem⟩ := by
  simp only [polyCofreeExtract,
    copresheafCoalgMType_children,
    copresheafCoalgMType_head]

/--
The underlying function of the structure map
for the comonad coalgebra constructed from a
copresheaf.
-/
def copresheafCoalgStrLeft (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u) :
    (copresheafCoalgCarrier P F).left →
    (polyCofreeCarrier
      (copresheafCoalgCarrier P F) P).left :=
  fun ⟨obj, elem⟩ =>
    ⟨obj.fiber, copresheafCoalgMType P F obj elem⟩

/--
The structure map commutes with projections to X.
-/
lemma copresheafCoalgStr_comm (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u) :
    copresheafCoalgStrLeft P F ≫
    (polyCofreeCarrier
      (copresheafCoalgCarrier P F) P).hom =
    (copresheafCoalgCarrier P F).hom := rfl

/--
The structure map as a morphism in Over X,
targeting the comonad's carrier.
-/
def copresheafCoalgStr (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u) :
    copresheafCoalgCarrier P F ⟶
    (polyCofreeComonad X P).toFunctor.obj
      (copresheafCoalgCarrier P F) :=
  Over.homMk (copresheafCoalgStrLeft P F)
    (copresheafCoalgStr_comm P F)

/-! ### P-Coalgebra from Copresheaf

Given a copresheaf `F : PolyCofreeCat P ⥤ Type u`,
the total space `copresheafCoalgCarrier P F` carries
a natural P-coalgebra structure: the shape at
`⟨obj, elem⟩` is the shape of `obj` in the cofree
category, and children are obtained by applying
`F.map` along edge morphisms.
-/

/--
The children morphism for the P-coalgebra structure
map: at each edge of the root shape, the child
carrier element is the cofree category child object
paired with the pushed-forward copresheaf element.
-/
def copresheafPolyCoalgChildrenMor
    (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (elem : F.obj obj) :
    polyBetweenFamily X X P obj.fiber
      obj.shape.head.2 ⟶
    copresheafCoalgCarrier P F :=
  Over.homMk
    (fun e => ⟨polyCofreeCatChild P obj e,
      F.map (polyCofreeCatEdge P obj e) elem⟩)
    rfl

/--
The evaluation family for the P-coalgebra structure
map at a carrier element.
-/
def copresheafPolyCoalgStrFamily
    (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (elem : F.obj obj) :
    polyBetweenEvalFamily X X P
      (copresheafCoalgCarrier P F) obj.fiber :=
  ⟨obj.shape.head.2,
    copresheafPolyCoalgChildrenMor P F obj elem⟩

/--
The P-coalgebra structure map on the copresheaf
carrier.
-/
def copresheafPolyCoalgStr
    (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u) :
    copresheafCoalgCarrier P F ⟶
    (polyEndoFunctor X P).obj
      (copresheafCoalgCarrier P F) :=
  Over.homMk
    (fun ⟨obj, elem⟩ =>
      ⟨obj.fiber,
        copresheafPolyCoalgStrFamily P F
          obj elem⟩)
    rfl

/--
The P-coalgebra constructed from a copresheaf.
-/
def copresheafToPolyCoalg
    (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u) :
    PolyCoalg P where
  V := copresheafCoalgCarrier P F
  str := copresheafPolyCoalgStr P F

/--
The comonad coalgebra constructed from a copresheaf,
via the comparison functor applied to the
P-coalgebra.
-/
def copresheafToComonadCoalg
    (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u) :
    Comonad.Coalgebra (polyCofreeComonad X P) :=
  (polyCoalgToComonadCoalg X P).obj
    (copresheafToPolyCoalg P F)

/--
A natural transformation between copresheaves
induces a morphism of Over X objects on the
carriers.
-/
def copresheafNatTransMor
    (P : PolyEndo X)
    {F G : PolyCofreeCat P ⥤ Type u}
    (η : F ⟶ G) :
    copresheafCoalgCarrier P F ⟶
    copresheafCoalgCarrier P G :=
  Over.homMk
    (fun ⟨obj, elem⟩ => ⟨obj, η.app obj elem⟩)
    rfl

/--
The morphism induced by a natural transformation
is a P-coalgebra homomorphism.
-/
lemma copresheafNatTransMor_comm
    (P : PolyEndo X)
    {F G : PolyCofreeCat P ⥤ Type u}
    (η : F ⟶ G) :
    copresheafPolyCoalgStr P F ≫
    (polyEndoFunctor X P).map
      (copresheafNatTransMor P η) =
    copresheafNatTransMor P η ≫
    copresheafPolyCoalgStr P G := by
  apply Over.OverMorphism.ext
  funext ⟨obj, elem⟩
  simp only [Over.comp_left, types_comp_apply,
    copresheafPolyCoalgStr, Over.homMk_left,
    copresheafNatTransMor,
    copresheafPolyCoalgStrFamily]
  dsimp only [polyEndoFunctor,
    polyBetweenEvalFunctor, polyBetweenEvalMap,
    polyToOverEvalMap, polyToOverFunctor,
    familySliceForward, familySliceForwardMap,
    polyToOverEval, polyToOverEvalFamilyMap,
    ccrEvalMap, Functor.comp_map,
    Functor.comp_obj, Over.homMk_left]
  congr 1; congr 1
  apply Over.OverMorphism.ext
  funext e
  simp only [Over.comp_left, Over.homMk_left,
    types_comp_apply,
    copresheafPolyCoalgChildrenMor]
  congr 1
  exact congrFun
    (η.naturality
      (polyCofreeCatEdge P obj e)) elem

/--
A natural transformation between copresheaves induces
a P-coalgebra homomorphism on the corresponding
carriers.
-/
def copresheafNatTransHom
    (P : PolyEndo X)
    {F G : PolyCofreeCat P ⥤ Type u}
    (η : F ⟶ G) :
    copresheafToPolyCoalg P F ⟶
    copresheafToPolyCoalg P G :=
  Endofunctor.Coalgebra.Hom.mk
    (copresheafNatTransMor P η)
    (copresheafNatTransMor_comm P η)

/--
The identity natural transformation maps to the
identity coalgebra homomorphism.
-/
lemma copresheafNatTransHom_id
    (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u) :
    copresheafNatTransHom P (𝟙 F) =
    𝟙 (copresheafToPolyCoalg P F) := by
  apply Endofunctor.Coalgebra.Hom.ext
  apply Over.OverMorphism.ext
  funext ⟨_, _⟩
  rfl

/--
Composition of natural transformations maps to
composition of coalgebra homomorphisms.
-/
lemma copresheafNatTransHom_comp
    (P : PolyEndo X)
    {F G H : PolyCofreeCat P ⥤ Type u}
    (η : F ⟶ G) (θ : G ⟶ H) :
    copresheafNatTransHom P (η ≫ θ) =
    copresheafNatTransHom P η ≫
    copresheafNatTransHom P θ := by
  apply Endofunctor.Coalgebra.Hom.ext
  apply Over.OverMorphism.ext
  funext ⟨_, _⟩
  rfl

/-! ### Copresheaf-to-Coalgebra Functor

The assignment `F ↦ copresheafToPolyCoalg P F` is
functorial: copresheaves on the cofree category map
to P-coalgebras contravariantly (natural
transformations go to coalgebra homomorphisms in the
same direction because the carrier total space
construction is covariant in the copresheaf).
-/

/--
The functor from copresheaves on the cofree
category to P-coalgebras.
-/
def copresheafToPolyCoalgFunctor
    (P : PolyEndo X) :
    (PolyCofreeCat P ⥤ Type u) ⥤
    PolyCoalg P where
  obj := copresheafToPolyCoalg P
  map := copresheafNatTransHom P
  map_id F := copresheafNatTransHom_id P F
  map_comp η θ := copresheafNatTransHom_comp P η θ

/-! ### Composed Functors -/

/--
The composed functor from P-coalgebras to
copresheaves: apply the comparison functor to
get a comonad coalgebra, then construct the
copresheaf.
-/
def polyCoalgToCopresheafFunctor
    (P : PolyEndo X) :
    PolyCoalg P ⥤
    (PolyCofreeCat P ⥤ Type u) :=
  polyCoalgToComonadCoalg X P ⋙
    coalgCopresheafFunctor P

/-! ### Forward-Backward Roundtrip

Starting with a P-coalgebra `α`, applying the
forward functor (comparison then copresheaf) and
then the backward functor (copresheaf to P-coalgebra)
yields a P-coalgebra isomorphic to `α`.  The
carrier isomorphism is the sigma-subtype fiber
decomposition.
-/

/--
The forward map of the carrier isomorphism for the
forward-backward roundtrip: sends `a : α.V.left`
to the pair of its target cofree category object
and the element with its membership proof.
-/
def roundtripFBCarrierFwd (P : PolyEndo X)
    (α : PolyCoalg P) :
    α.V.left →
    (copresheafCoalgCarrier P
      ((polyCoalgToCopresheafFunctor P).obj α)
    ).left :=
  fun a =>
    let c := (polyCoalgToComonadCoalg X P).obj α
    ⟨coalgCopresheafTarget c a, ⟨a, rfl⟩⟩

/--
The backward map of the carrier isomorphism:
projects out the element from the sigma-subtype
pair.
-/
def roundtripFBCarrierBwd (P : PolyEndo X)
    (α : PolyCoalg P) :
    (copresheafCoalgCarrier P
      ((polyCoalgToCopresheafFunctor P).obj α)
    ).left →
    α.V.left :=
  fun ⟨_, ⟨a, _⟩⟩ => a

lemma roundtripFBCarrier_comm_fwd (P : PolyEndo X)
    (α : PolyCoalg P) :
    roundtripFBCarrierFwd P α ≫
    (copresheafCoalgCarrier P
      ((polyCoalgToCopresheafFunctor P).obj α)
    ).hom = α.V.hom := rfl

lemma roundtripFBCarrier_comm_bwd (P : PolyEndo X)
    (α : PolyCoalg P) :
    roundtripFBCarrierBwd P α ≫ α.V.hom =
    (copresheafCoalgCarrier P
      ((polyCoalgToCopresheafFunctor P).obj α)
    ).hom := by
  funext ⟨_, ⟨a, ha⟩⟩
  simp only [types_comp_apply,
    roundtripFBCarrierBwd,
    copresheafCoalgCarrier, Over.mk_hom]
  exact ha.symm ▸ rfl

lemma roundtripFBCarrier_bwd_fwd (P : PolyEndo X)
    (α : PolyCoalg P) (a : α.V.left) :
    roundtripFBCarrierBwd P α
      (roundtripFBCarrierFwd P α a) = a := rfl

/--
The carrier of the forward-backward roundtrip
result.
-/
abbrev roundtripFBResultCarrier
    (P : PolyEndo X) (α : PolyCoalg P) : Over X :=
  copresheafCoalgCarrier P
    ((polyCoalgToCopresheafFunctor P).obj α)

lemma roundtripFBCarrier_fwd_bwd (P : PolyEndo X)
    (α : PolyCoalg P)
    (x : (roundtripFBResultCarrier P α).left) :
    roundtripFBCarrierFwd P α
      (roundtripFBCarrierBwd P α x) = x := by
  obtain ⟨obj, ⟨a, rfl⟩⟩ := x
  rfl

/--
The forward Over X morphism for the
forward-backward roundtrip carrier isomorphism.
-/
def roundtripFBCarrierMorFwd (P : PolyEndo X)
    (α : PolyCoalg P) :
    α.V ⟶ roundtripFBResultCarrier P α :=
  Over.homMk (roundtripFBCarrierFwd P α)
    (roundtripFBCarrier_comm_fwd P α)

/--
The backward Over X morphism for the
forward-backward roundtrip carrier isomorphism.
-/
def roundtripFBCarrierMorBwd (P : PolyEndo X)
    (α : PolyCoalg P) :
    roundtripFBResultCarrier P α ⟶ α.V :=
  Over.homMk (roundtripFBCarrierBwd P α)
    (roundtripFBCarrier_comm_bwd P α)

/--
The carrier morphisms form an isomorphism.
-/
def roundtripFBCarrierIso (P : PolyEndo X)
    (α : PolyCoalg P) :
    α.V ≅ roundtripFBResultCarrier P α where
  hom := roundtripFBCarrierMorFwd P α
  inv := roundtripFBCarrierMorBwd P α
  hom_inv_id := by
    apply Over.OverMorphism.ext
    funext a
    exact roundtripFBCarrier_bwd_fwd P α a
  inv_hom_id := by
    apply Over.OverMorphism.ext
    funext x
    exact roundtripFBCarrier_fwd_bwd P α x

/--
The forward carrier morphism is a P-coalgebra
homomorphism.
-/
-- To prove this, we need to relate the
-- comparison functor's output to the original
-- P-coalgebra structure.
-- Factor out: the first component of the
-- target matches the structure map's first
-- component.
lemma roundtripFB_target_fiber
    (P : PolyEndo X) (α : PolyCoalg P)
    (a : α.V.left) :
    (coalgCopresheafTarget
      ((polyCoalgToComonadCoalg X P).obj α)
      a).fiber = (α.str.left a).1 := by
  simp only [coalgCopresheafTarget]
  -- Goal: c.A.hom a = (α.str.left a).1
  -- where c = comparison.obj α, so c.A = L.obj α
  -- L = polyForgetFunctor, so c.A.hom = α.V.hom
  change α.V.hom a = (α.str.left a).1
  exact (congrFun (Over.w α.str) a).symm

-- The structure map equality for the
-- forward-backward roundtrip at a point.
-- This expresses that reading the copresheaf
-- structure from the M-type tree (which the
-- anamorphism builds from α.str) and projecting
-- back gives α.str.
-- The copresheaf-derived P-coalgebra structure
-- agrees with polyComonadCoalgStr (which extracts
-- the P-structure from a comonad coalgebra via
-- c.a ≫ cofreeStr ≫ P.map(counit)).
-- By polyCoalgComonad_forward_str, the latter
-- equals α.str for comparison outputs.
-- So it suffices to show:
-- copresheafPolyCoalgStr composed with bwd
-- = roundtripFBCarrierBwd composed with
--   polyComonadCoalgStr c
-- That is, reading the P-structure from the
-- copresheaf (via M-type head/children) and
-- projecting back gives the same as projecting
-- first and then reading from the comonad
-- coalgebra's extracted P-structure.
--
-- An alternative approach: use the Phase 1 result
-- polyCoalgComonad_forward_str to avoid unfolding
-- the M-type tree entirely.  Instead, show the
-- backward map is a P-coalgebra homomorphism by
-- relating it to the Phase 1 inverse comparison.
lemma coalgCopresheafMap_edge_val
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left) :
    let target := coalgCopresheafTarget c a
    let m := (c.a.left a).2
    let e_m := fun (e : (polyBetweenFamily X X
        P (c.A.hom a)
        target.shape.head.2).left) =>
      polyCofreeShapePosToMPos c.A P m
        ((coalgCopresheafCastPos c a 1
          ⟨e, PUnit.unit⟩).1)
    ∀ (e : (polyBetweenFamily X X P (c.A.hom a)
        target.shape.head.2).left),
    ((coalgCopresheaf c).map
      (polyCofreeCatEdge P target e)
      ⟨a, rfl⟩).val =
    coalgCopresheafChild c a (e_m e) := by
  intro target m e_m e
  simp only [coalgCopresheaf, coalgCopresheafMap,
    coalgCopresheafChild, polyCofreeCatEdge]
  rfl

lemma polyCofreeAnnotPosAt1_cast_fst_heq
    {P : PolyEndo X} {x : X}
    {s1 s2 : PolyCofreeShape P x}
    (h : s1 = s2)
    (e : (polyBetweenFamily X X P x
      s1.head.2).left) :
    HEq
      (cast (polyCofreeAnnotPosAt_cast h 1)
        ⟨e, PUnit.unit⟩).fst
      e := by
  subst h
  rfl

lemma polyCofreeAnnotPosAt1_cast_fiber_fst_heq
    {P : PolyEndo X} {x y : X}
    (hxy : x = y)
    {s1 : PolyCofreeShape P x}
    {s2 : PolyCofreeShape P y}
    (hs : HEq s1 s2)
    (e : (polyBetweenFamily X X P x
      s1.head.2).left) :
    HEq
      (cast (polyCofreeAnnotPosAt_cast_fiber
        hxy hs 1) ⟨e, PUnit.unit⟩).fst
      e := by
  subst hxy
  exact polyCofreeAnnotPosAt1_cast_fst_heq
    (eq_of_heq hs) e

lemma coalgCopresheafCastPos1_fst_heq
    {P : PolyEndo X}
    (c : Comonad.Coalgebra
      (polyCofreeComonad X P))
    (a : c.A.left) :
    let target := coalgCopresheafTarget c a
    ∀ (e : (polyBetweenFamily X X P
        (c.A.hom a)
        target.shape.head.2).left),
    HEq (coalgCopresheafCastPos c a 1
      ⟨e, PUnit.unit⟩).fst e := by
  intro target e
  exact polyCofreeAnnotPosAt1_cast_fiber_fst_heq
    (comonadCoalgFiberEq c a).symm
    (coalgCopresheafShapeAt_heq c a) e

lemma roundtripFBStr_eq
    (P : PolyEndo X) (α : PolyCoalg P)
    (a : α.V.left) :
    let c := (polyCoalgToComonadCoalg X P).obj α
    let target := coalgCopresheafTarget c a
    let F :=
      (polyCoalgToCopresheafFunctor P).obj α
    (⟨target.fiber,
      ⟨(PolyCofix.head target.shape).2,
        copresheafPolyCoalgChildrenMor P F
            target ⟨a, rfl⟩ ≫
          Over.homMk
            (roundtripFBCarrierBwd P α)
            (roundtripFBCarrier_comm_bwd
              P α)⟩⟩ :
      (x : X) ×
        polyBetweenEvalFamily X X P α.V x) =
    α.str.left a := by
  intro c target F
  -- Rewrite α.str using the Phase 1 result:
  -- polyCoalgComonad_forward_str shows that
  -- extracting the P-structure from c gives α.str.
  rw [show α.str =
    polyComonadCoalgStr c from
    (polyCoalgComonad_forward_str α).symm]
  simp only [polyComonadCoalgStr, Over.comp_left,
    types_comp_apply]
  simp only [polyCofreeCoalg, polyCofreeStr,
    polyCofreeStrLeft, Over.homMk_left]
  dsimp only [polyEndoFunctor,
    polyBetweenEvalFunctor, polyBetweenEvalMap,
    polyToOverEvalMap, polyToOverFunctor,
    familySliceForward, familySliceForwardMap,
    polyToOverEval, polyToOverEvalFamilyMap,
    ccrEvalMap, Functor.comp_map,
    Functor.comp_obj, Over.homMk_left]
  set ca := c.a.left a with hca_def
  obtain ⟨x_fib, m_tree⟩ := ca
  simp only [polyCofreeStrFamily]
  have hfib : x_fib = c.A.hom a := by
    have h := comonadCoalgFiberEq c a
    rw [show c.a.left a = ⟨x_fib, m_tree⟩
      from hca_def.symm] at h
    exact h
  subst hfib
  congr 1
  -- Goal: inner pair equality
  -- First need to show target.shape relates to m_tree
  have hshape : target.shape =
      polyCofreeToShape c.A P m_tree := by
    simp only [target, coalgCopresheafTarget,
      coalgCopresheafShapeAt]
    -- coalgCopresheafShapeAt c a =
    -- (comonadCoalgFiberEq c a) ▸
    --   polyCofreeToShape c.A P (c.a.left a).2
    -- After subst, comonadCoalgFiberEq c a is
    -- a proof of c.A.hom a = c.A.hom a. Use
    -- proof irrelevance to replace it by rfl,
    -- making the transport trivial.
    conv_lhs =>
      rw [show comonadCoalgFiberEq c a =
        rfl from Subsingleton.elim _ _]
    -- Now the ▸ rfl reduces away
    -- Still need (c.a.left a).2 = m_tree
    -- Since hca_def : ⟨c.A.hom a, m_tree⟩ = c.a.left a
    -- we get (c.a.left a).2 ≍ m_tree by Sigma.mk.inj
    exact congrArg (polyCofreeToShape c.A P)
      (eq_of_heq (Sigma.mk.inj hca_def).2.symm)
  apply Sigma.ext
  · -- First component: index equality
    change (PolyCofix.head target.shape).2 =
      m_tree.head.2
    rw [hshape,
      polyCofreeToShape_head_index c.A P m_tree]
  · -- Second component: children HEq
    dsimp only
    have hsrc :
        polyBetweenFamily X X P (c.A.hom a)
          (PolyCofix.head target.shape).2 =
        polyBetweenFamily X X P (c.A.hom a)
          m_tree.head.2 := by
      congr 1
      rw [hshape,
        polyCofreeToShape_head_index c.A P
          m_tree]
    apply overHomHEqOfSrcEq hsrc
    -- HEq of .left functions
    simp only [Over.comp_left, Over.homMk_left]
    apply funext_heq
      (congrArg (·.left) hsrc) rfl
    intro e e' hee'
    simp only [copresheafPolyCoalgChildrenMor,
      Over.homMk_left,
      polyCofreeChildrenMor]
    simp only [heq_iff_eq]
    simp only [types_comp_apply]
    change (F.map (polyCofreeCatEdge P target e)
          ⟨a, rfl⟩).val =
        ((polyCofreeComonad X P).ε.app c.A).left
          ⟨(polyBetweenFamily X X P (c.A.hom a)
              m_tree.head.2).hom e',
            m_tree.children e'⟩
    simp only [polyCofreeComonad,
      Adjunction.toComonad,
      polyForgetCofreeAdjunction,
      Adjunction.mkOfUnitCounit,
      polyCofreeCounitNat,
      polyCofreeCounit, Over.homMk_left,
      polyCofreeCounitLeft]
    change ((coalgCopresheaf c).map
        (polyCofreeCatEdge P
          (coalgCopresheafTarget c a) e)
        ⟨a, rfl⟩).val =
      (polyCofreeExtract c.A P
        (m_tree.children e')).val
    rw [coalgCopresheafMap_edge_val c a e]
    simp only [coalgCopresheafChild]
    -- Goal: polyCofreeExtract at
    --   (c.a.left a).snd.children e_m
    -- = polyCofreeExtract at
    --   m_tree.children e'
    -- Related by h_snd_heq and position HEq.
    have h_snd_heq :
        HEq (c.a.left a).2 m_tree :=
      (Sigma.ext_iff.mp hca_def.symm).2
    have h_snd_eq := eq_of_heq h_snd_heq
    subst h_snd_eq
    have h_pos_eq :
        polyCofreeShapePosToMPos c.A P
          (c.a.left a).snd
          (coalgCopresheafCastPos c a 1
            ⟨e, PUnit.unit⟩).fst =
        e' := by
      exact eq_of_heq
        (((polyCofreeShapePosToMPos_heq c.A P
          (c.a.left a).snd
          (coalgCopresheafCastPos c a 1
            ⟨e, PUnit.unit⟩).fst).symm.trans
          (coalgCopresheafCastPos1_fst_heq
            c a e)).trans hee')
    rw [h_pos_eq]

-- The backward carrier morphism is a P-coalgebra
-- homomorphism: the structure map of the roundtrip
-- result, composed with the backward projection,
-- equals the backward projection composed with the
-- original structure map.
-- We prove this first, then derive the forward.
lemma roundtripFBCarrierMorBwd_comm
    (P : PolyEndo X) (α : PolyCoalg P) :
    copresheafPolyCoalgStr P
      ((polyCoalgToCopresheafFunctor P).obj α) ≫
    (polyEndoFunctor X P).map
      (roundtripFBCarrierMorBwd P α) =
    roundtripFBCarrierMorBwd P α ≫ α.str := by
  apply Over.OverMorphism.ext
  funext ⟨obj, ⟨a, ha⟩⟩
  simp only [Over.comp_left, types_comp_apply]
  simp only [copresheafPolyCoalgStr,
    roundtripFBCarrierMorBwd,
    roundtripFBCarrierBwd, Over.homMk_left,
    copresheafPolyCoalgStrFamily]
  dsimp only [polyEndoFunctor,
    polyBetweenEvalFunctor, polyBetweenEvalMap,
    polyToOverEvalMap, polyToOverFunctor,
    familySliceForward, familySliceForwardMap,
    polyToOverEval, polyToOverEvalFamilyMap,
    ccrEvalMap, Functor.comp_map,
    Functor.comp_obj, Over.homMk_left]
  subst ha
  -- The goal says the copresheaf-derived structure
  -- at a, projected back, equals α.str.left a.
  -- We need to relate the copresheaf structure
  -- (which reads from the M-type tree) to α.str.
  -- The M-type tree is built by the anamorphism.
  -- The first level of the anamorphism encodes
  -- α.str by polyCofixUnfold_coalg_comm_eq.
  exact roundtripFBStr_eq P α a

-- The forward carrier morphism is a P-coalgebra
-- homomorphism.  Derived from backward commutativity
-- and the carrier isomorphism: precomposing the
-- backward comm with `fwd` and postcomposing with
-- `F.map fwd`, then cancelling via the iso.
lemma roundtripFBCarrierMorFwd_comm
    (P : PolyEndo X) (α : PolyCoalg P) :
    α.str ≫ (polyEndoFunctor X P).map
      (roundtripFBCarrierMorFwd P α) =
    roundtripFBCarrierMorFwd P α ≫
    copresheafPolyCoalgStr P
      ((polyCoalgToCopresheafFunctor P).obj α) := by
  have h_bwd := roundtripFBCarrierMorBwd_comm P α
  have h_hom_inv :
      roundtripFBCarrierMorFwd P α ≫
      roundtripFBCarrierMorBwd P α = 𝟙 _ :=
    (roundtripFBCarrierIso P α).hom_inv_id
  have h_inv_hom :
      roundtripFBCarrierMorBwd P α ≫
      roundtripFBCarrierMorFwd P α = 𝟙 _ :=
    (roundtripFBCarrierIso P α).inv_hom_id
  have step1 :
      roundtripFBCarrierMorFwd P α ≫
      copresheafPolyCoalgStr P
        ((polyCoalgToCopresheafFunctor P).obj α) ≫
      (polyEndoFunctor X P).map
        (roundtripFBCarrierMorBwd P α) =
      α.str := by
    rw [h_bwd, ← Category.assoc,
      h_hom_inv, Category.id_comp]
  calc α.str ≫ (polyEndoFunctor X P).map
        (roundtripFBCarrierMorFwd P α)
      = (roundtripFBCarrierMorFwd P α ≫
        copresheafPolyCoalgStr P
          ((polyCoalgToCopresheafFunctor P).obj α) ≫
        (polyEndoFunctor X P).map
          (roundtripFBCarrierMorBwd P α)) ≫
        (polyEndoFunctor X P).map
          (roundtripFBCarrierMorFwd P α) := by
        rw [step1]
    _ = roundtripFBCarrierMorFwd P α ≫
        copresheafPolyCoalgStr P
          ((polyCoalgToCopresheafFunctor P).obj
            α) := by
        simp only [Category.assoc,
          ← (polyEndoFunctor X P).map_comp,
          h_inv_hom,
          (polyEndoFunctor X P).map_id,
          Category.comp_id]

/--
The forward coalgebra homomorphism for the
forward-backward roundtrip: `α ⟶ Psi(Phi(α))`.
-/
def roundtripFBCoalgHomFwd (P : PolyEndo X)
    (α : PolyCoalg P) :
    α ⟶ copresheafToPolyCoalg P
      ((polyCoalgToCopresheafFunctor P).obj α) :=
  Endofunctor.Coalgebra.Hom.mk
    (roundtripFBCarrierMorFwd P α)
    (roundtripFBCarrierMorFwd_comm P α)

/--
The backward coalgebra homomorphism for the
forward-backward roundtrip: `Psi(Phi(α)) ⟶ α`.
-/
def roundtripFBCoalgHomBwd (P : PolyEndo X)
    (α : PolyCoalg P) :
    copresheafToPolyCoalg P
      ((polyCoalgToCopresheafFunctor P).obj α) ⟶
    α :=
  Endofunctor.Coalgebra.Hom.mk
    (roundtripFBCarrierMorBwd P α)
    (roundtripFBCarrierMorBwd_comm P α)

/--
The coalgebra isomorphism for the forward-backward
roundtrip: `α ≅ Psi(Phi(α))` in `PolyCoalg P`.
-/
def roundtripFBCoalgIso (P : PolyEndo X)
    (α : PolyCoalg P) :
    α ≅ copresheafToPolyCoalg P
      ((polyCoalgToCopresheafFunctor P).obj α) where
  hom := roundtripFBCoalgHomFwd P α
  inv := roundtripFBCoalgHomBwd P α
  hom_inv_id := by
    apply Endofunctor.Coalgebra.Hom.ext
    exact (roundtripFBCarrierIso P α).hom_inv_id
  inv_hom_id := by
    apply Endofunctor.Coalgebra.Hom.ext
    exact (roundtripFBCarrierIso P α).inv_hom_id

/-! ### M-type Approximation Reconstruction

An M-type approximation at depth n+1 decomposes as an
`.intro` node whose index is the head and whose children
are the child approximations.
-/

/--
An M-type approximation at depth `n + 1` equals the
`.intro` node with the head index and children given by
the child approximations at depth `n`.
-/
lemma polyCofixApprox_succ_eq
    {Q : PolyEndo X} {x : X}
    (m : PolyCofix Q x) (n : Nat) :
    m.approx (n + 1) = .intro x m.head
      (fun e => (m.children e).approx n) := by
  have hhead :
      (m.approx (n + 1)).getIndex = m.head :=
    m.index_eq_head n
  generalize ha : m.approx (n + 1) = a
  match a with
  | .intro _ idx ch =>
    have hidx : idx = m.head := by
      rw [ha] at hhead; exact hhead
    subst hidx
    congr 1
    funext e
    match n with
    | 0 =>
      match ch e with
      | .continue _ => rfl
    | n + 1 =>
      simp only [PolyCofix.children,
        PolyCofix.childApproxAt,
        PolyCofix.childApproxAt_succ]
      conv_rhs =>
        rw [PolyCofix.childApproxAt_succ_aux_proof_irrel
          m.head (m.approx (n + 2))
          (m.index_eq_head (n + 1))
          (by rw [ha]; rfl) e]
      simp only [ha,
        PolyCofix.childApproxAt_succ_aux_intro]

/-! ### Backward-Forward Roundtrip

Starting with a copresheaf `F : PolyCofreeCat P ⥤ Type u`,
applying the backward functor (copresheaf to P-coalgebra)
and then the forward functor (comparison then copresheaf)
yields a copresheaf isomorphic to `F`. The pointwise
isomorphism sends `elem : F.obj obj` to the pair
`⟨⟨obj, elem⟩, target_self_eq⟩` where `target_self_eq`
proves the copresheaf target recovers `obj`.
-/

/--
The unit approximation for the copresheaf P-coalgebra
equals the directly-constructed copresheaf approximation
at each depth.
-/
lemma copresheafUnitApproxEq (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (elem : F.obj obj) :
    ∀ n, polyCoalgUnitApprox P
      (copresheafToPolyCoalg P F) n
      obj.fiber ⟨⟨obj, elem⟩, rfl⟩ =
    copresheafCoalgApprox P F obj elem n := by
  intro n
  induction n generalizing obj elem with
  | zero => rfl
  | succ n ih =>
    simp only [polyCoalgUnitApprox,
      copresheafCoalgApprox]
    congr 1
    funext e
    exact ih (polyCofreeCatChild P obj e)
      (F.map (polyCofreeCatEdge P obj e) elem)

/--
The M-type built by the unit construction from a
copresheaf P-coalgebra equals the directly-constructed
copresheaf M-type.
-/
lemma copresheafUnitMTypeEq (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (elem : F.obj obj) :
    polyCoalgUnitAt P (copresheafToPolyCoalg P F)
      obj.fiber ⟨⟨obj, elem⟩, rfl⟩ =
    copresheafCoalgMType P F obj elem := by
  apply PolyCofix.ext
  intro n
  exact copresheafUnitApproxEq P F obj elem n

/--
The head of the M-type built by the unit construction
from a copresheaf P-coalgebra equals the copresheaf
index at the root.
-/
lemma copresheafUnitHead (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (elem : F.obj obj) :
    (polyCoalgUnitAt P (copresheafToPolyCoalg P F)
      obj.fiber ⟨⟨obj, elem⟩, rfl⟩).head =
    ⟨⟨⟨obj, elem⟩, rfl⟩, obj.shape.head.2⟩ := by
  change (polyCoalgUnitApprox P
    (copresheafToPolyCoalg P F) 1
    obj.fiber ⟨⟨obj, elem⟩, rfl⟩).getIndex = _
  rw [copresheafUnitApproxEq P F obj elem 1]
  rfl

/--
Congruence: if two annotated M-types are equal,
extraction from their children at HEq positions
gives equal `.val` results.
-/
lemma polyCofreeExtract_children_val_congr
    (A : Over X) (P : PolyEndo X) {x : X}
    {m1 m2 : PolyCofreeM A P x}
    (h : m1 = m2)
    {e1 : (polyBetweenFamily X X
      (polyScale A P) x m1.head).left}
    {e2 : (polyBetweenFamily X X
      (polyScale A P) x m2.head).left}
    (he : HEq e1 e2) :
    (polyCofreeExtract A P
      (m1.children e1)).val =
    (polyCofreeExtract A P
      (m2.children e2)).val := by
  subst h
  have := eq_of_heq he
  subst this
  rfl

/--
Extracting the child annotation from the unit
M-type at position `e` yields the child copresheaf
element.
-/
lemma copresheafUnitExtract (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (elem : F.obj obj)
    (e : (polyBetweenFamily X X P obj.fiber
      obj.shape.head.2).left) :
    (polyCofreeExtract
      (copresheafCoalgCarrier P F) P
      ((polyCoalgUnitAt P
        (copresheafToPolyCoalg P F) obj.fiber
        ⟨⟨obj, elem⟩, rfl⟩).children
        e)).val =
    ⟨polyCofreeCatChild P obj e,
      F.map (polyCofreeCatEdge P obj e)
        elem⟩ :=
  (polyCofreeExtract_children_val_congr
    (copresheafCoalgCarrier P F) P
    (copresheafUnitMTypeEq P F obj elem)
    HEq.rfl).trans
    (copresheafCoalgMType_extract
      P F obj elem e)

/--
The shape of the M-type built by `polyCoalgUnitApprox`
from a copresheaf P-coalgebra, after stripping annotations,
agrees with the original shape at each approximation depth.
-/
lemma copresheafUnitShapeApprox (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (elem : F.obj obj) :
    ∀ n, polyCofreeApproxToShape
      (copresheafCoalgCarrier P F) P
      (polyCoalgUnitApprox P
        (copresheafToPolyCoalg P F) n
        obj.fiber ⟨⟨obj, elem⟩, rfl⟩) =
    obj.shape.approx n := by
  intro n
  induction n generalizing obj elem with
  | zero =>
    simp only [polyCoalgUnitApprox,
      polyCofreeApproxToShape]
    cases h : obj.shape.approx 0
    · rfl
  | succ n ih =>
    simp only [polyCoalgUnitApprox,
      polyCofreeApproxToShape]
    rw [polyCofixApprox_succ_eq obj.shape n]
    congr 1
    · exact Prod.ext
        (Subtype.ext obj.shape.head.1.property.symm)
        rfl
    · funext e
      exact ih (polyCofreeCatChild P obj e)
        (F.map (polyCofreeCatEdge P obj e) elem)

/--
The shape of the M-type built by `polyCoalgUnit`
from a copresheaf P-coalgebra, after stripping
annotations, equals the original shape.
-/
lemma copresheafUnitShapeEq (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (elem : F.obj obj) :
    polyCofreeToShape (copresheafCoalgCarrier P F)
      P (polyCoalgUnitAt P
        (copresheafToPolyCoalg P F)
        obj.fiber ⟨⟨obj, elem⟩, rfl⟩) =
    obj.shape := by
  apply PolyCofix.ext
  intro n
  exact copresheafUnitShapeApprox P F obj elem n

/--
The copresheaf target of the comparison coalgebra at
a copresheaf carrier element `⟨obj, elem⟩` recovers
`obj` itself.
-/
lemma copresheafTargetSelfEq (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (elem : F.obj obj) :
    coalgCopresheafTarget
      ((polyCoalgToComonadCoalg X P).obj
        (copresheafToPolyCoalg P F))
      ⟨obj, elem⟩ = obj := by
  simp only [coalgCopresheafTarget,
    coalgCopresheafShapeAt]
  ext
  · rfl
  · exact heq_of_eq
      (copresheafUnitShapeEq P F obj elem)

/-! ### Backward-Forward Roundtrip

Starting from a copresheaf `F : PolyCofreeCat P ⥤ Type u`,
applying the backward functor (copresheaf to P-coalgebra)
then the forward functor (comparison then copresheaf
functor) yields a copresheaf pointwise isomorphic to `F`.
The copresheaf value at `obj` is `coalgCopresheafObj c obj`,
which is the subtype of `c.A.left` projecting to `obj`.
Since `c.A.left = Σ obj', F.obj obj'` and
`copresheafTargetSelfEq` shows the target is always `obj'`
itself, this subtype collapses to `F.obj obj`.
-/

/--
The forward component of the BF roundtrip isomorphism:
sends `elem : F.obj obj` to the pair `⟨obj, elem⟩`
together with the proof that its copresheaf target
is `obj`.
-/
def copresheafBFRoundtripFwd (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P) :
    F.obj obj →
    coalgCopresheafObj
      ((polyCoalgToComonadCoalg X P).obj
        (copresheafToPolyCoalg P F)) obj :=
  fun elem =>
    ⟨⟨obj, elem⟩, copresheafTargetSelfEq P F obj elem⟩

/--
The backward component of the BF roundtrip isomorphism:
given a subtype element `⟨⟨obj', elem'⟩, h⟩` where
`h : coalgCopresheafTarget c ⟨obj', elem'⟩ = obj`,
derives `obj' = obj` from `copresheafTargetSelfEq` and
transports `elem'` along this equality.
-/
def copresheafBFRoundtripBwd (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P) :
    coalgCopresheafObj
      ((polyCoalgToComonadCoalg X P).obj
        (copresheafToPolyCoalg P F)) obj →
    F.obj obj :=
  fun ⟨⟨obj', elem'⟩, h⟩ =>
    let p : obj' = obj :=
      (copresheafTargetSelfEq P F obj' elem').symm
        |>.trans h
    F.map (eqToHom p) elem'

/--
Forward then backward is the identity.
-/
lemma copresheafBFRoundtrip_fwd_bwd
    (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (elem : F.obj obj) :
    copresheafBFRoundtripBwd P F obj
      (copresheafBFRoundtripFwd P F obj elem) =
    elem := by
  simp only [copresheafBFRoundtripFwd,
    copresheafBFRoundtripBwd,
    eqToHom_refl, F.map_id,
    CategoryTheory.types_id_apply]

/--
Backward then forward is the identity.
-/
lemma copresheafBFRoundtrip_bwd_fwd
    (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    (obj : PolyCofreeCat P)
    (x : coalgCopresheafObj
      ((polyCoalgToComonadCoalg X P).obj
        (copresheafToPolyCoalg P F)) obj) :
    copresheafBFRoundtripFwd P F obj
      (copresheafBFRoundtripBwd P F obj x) =
    x := by
  obtain ⟨⟨obj', elem'⟩, h⟩ := x
  simp only [copresheafBFRoundtripBwd,
    copresheafBFRoundtripFwd]
  have p : obj' = obj :=
    (copresheafTargetSelfEq P F obj' elem').symm
      |>.trans h
  subst p
  simp only [eqToHom_refl, F.map_id,
    CategoryTheory.types_id_apply]

/--
Naturality of the BF roundtrip forward map at
the `.val` level: extraction from the unit M-type
at a morphism `f` yields the copresheaf applied
to `f`.
-/
lemma copresheafBF_naturality_val
    (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    {obj₁ obj₂ : PolyCofreeCat P}
    (f : obj₁ ⟶ obj₂)
    (elem : F.obj obj₁) :
    (coalgCopresheafMap
      ((polyCoalgToComonadCoalg X P).obj
        (copresheafToPolyCoalg P F)) f
      (copresheafBFRoundtripFwd
        P F obj₁ elem)).val =
    (copresheafBFRoundtripFwd P F obj₂
      (F.map f elem)).val := by
  simp only [copresheafBFRoundtripFwd]
  obtain ⟨_, _⟩ := obj₂
  obtain ⟨fn, fp, hff, hfs⟩ := f
  dsimp at hff hfs
  subst hff
  cases eq_of_heq hfs
  let c := (polyCoalgToComonadCoalg X P).obj
    (copresheafToPolyCoalg P F)
  induction fn generalizing obj₁ elem with
  | zero =>
    cases fp
    -- The depth-0 morphism is the identity.
    let f₀ : obj₁ ⟶ obj₁ :=
      ⟨0, PUnit.unit, rfl, hfs⟩
    change (coalgCopresheafMap c f₀
      ⟨⟨obj₁, elem⟩, _⟩).val =
      ⟨obj₁, F.map f₀ elem⟩
    have hf_id : f₀ = 𝟙 obj₁ := by
      apply PolyCofreeCatHom.ext <;> rfl
    rw [hf_id, coalgCopresheafMap_id]
    simp only [F.map_id,
      CategoryTheory.types_id_apply]
  | succ fn ih =>
    obtain ⟨e_shape, rest_fp⟩ := fp
    let childObj :=
      polyCofreeCatChild P obj₁ e_shape
    let edge := polyCofreeCatEdge P obj₁ e_shape
    let childElem := F.map edge elem
    let tgt : PolyCofreeCat P :=
      ⟨PolyCofreeAnnotFiberAt P obj₁.shape
          (fn + 1) ⟨e_shape, rest_fp⟩,
        polyCofreeSubtreeAt P obj₁.shape
          (fn + 1) ⟨e_shape, rest_fp⟩⟩
    let rest : childObj ⟶ tgt :=
      ⟨fn, rest_fp, rfl, HEq.rfl⟩
    let f₁ : obj₁ ⟶ tgt :=
      ⟨fn + 1, ⟨e_shape, rest_fp⟩, rfl, hfs⟩
    let ha := copresheafTargetSelfEq
      P F obj₁ elem
    let ha_child := copresheafTargetSelfEq
      P F childObj childElem
    have hf_eq : f₁ = edge ≫ rest := by
      apply PolyCofreeCatHom.ext <;> rfl
    have h_edge_val :
        (coalgCopresheafMap c edge
          ⟨⟨obj₁, elem⟩, ha⟩).val =
        ⟨childObj, childElem⟩ :=
      rfl
    have h_edge_eq :
        coalgCopresheafMap c edge
          ⟨⟨obj₁, elem⟩, ha⟩ =
        ⟨⟨childObj, childElem⟩, ha_child⟩ :=
      Subtype.ext h_edge_val
    have h_fmap :
        F.map f₁ elem =
        F.map rest childElem := by
      change F.map f₁ elem =
        F.map rest (F.map edge elem)
      conv_lhs => rw [hf_eq]
      exact congrFun
        (F.map_comp edge rest) elem
    change (coalgCopresheafMap c f₁
      ⟨⟨obj₁, elem⟩, ha⟩).val =
      ⟨tgt, F.map f₁ elem⟩
    rw [h_fmap]
    calc (coalgCopresheafMap c f₁
            ⟨⟨obj₁, elem⟩, ha⟩).val
        = (coalgCopresheafMap c (edge ≫ rest)
            ⟨⟨obj₁, elem⟩, ha⟩).val := by
          simp only [hf_eq]
      _ = (coalgCopresheafMap c rest
            (coalgCopresheafMap c edge
              ⟨⟨obj₁, elem⟩, ha⟩)).val :=
          coalgCopresheafMap_comp
            c edge rest ⟨⟨obj₁, elem⟩, ha⟩
      _ = (coalgCopresheafMap c rest
            ⟨⟨childObj, childElem⟩,
              ha_child⟩).val := by
          rw [h_edge_eq]
      _ = ⟨tgt,
            F.map rest childElem⟩ :=
          ih childElem rest_fp HEq.rfl

/--
Naturality of the backward-forward roundtrip
forward map: given `f : obj₁ ⟶ obj₂`, applying
`f` via the copresheaf then extracting equals
extracting then applying `F.map f`.
-/
lemma copresheafBF_naturality (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u)
    {obj₁ obj₂ : PolyCofreeCat P}
    (f : obj₁ ⟶ obj₂)
    (elem : F.obj obj₁) :
    let c := (polyCoalgToComonadCoalg X P).obj
      (copresheafToPolyCoalg P F)
    coalgCopresheafMap c f
      (copresheafBFRoundtripFwd P F obj₁ elem) =
    copresheafBFRoundtripFwd P F obj₂
      (F.map f elem) :=
  Subtype.ext
    (copresheafBF_naturality_val P F f elem)

/--
The backward-forward roundtrip natural
isomorphism: `F ≅ coalgCopresheaf (Psi(F))`
where `Psi = copresheafToComonadCoalg`.
-/
def copresheafBFNatIso (P : PolyEndo X)
    (F : PolyCofreeCat P ⥤ Type u) :
    F ≅ coalgCopresheaf
      ((polyCoalgToComonadCoalg X P).obj
        (copresheafToPolyCoalg P F)) :=
  CategoryTheory.NatIso.ofComponents
    (fun obj => {
      hom := copresheafBFRoundtripFwd P F obj
      inv := copresheafBFRoundtripBwd P F obj
      hom_inv_id := by
        ext elem
        exact copresheafBFRoundtrip_fwd_bwd
          P F obj elem
      inv_hom_id := by
        ext x
        exact copresheafBFRoundtrip_bwd_fwd
          P F obj x
    })
    (fun f => by
      ext elem
      exact (copresheafBF_naturality
        P F f elem).symm)

/--
The counit of the copresheaf equivalence:
`Psi ⋙ Phi ≅ 𝟭 _` where
`Phi = polyCoalgToCopresheafFunctor P` and
`Psi = copresheafToPolyCoalgFunctor P`.
The naturality in `F` holds because the forward
map `copresheafBFRoundtripFwd` acts independently
of the coalgebra structure.
-/
def polyCoalgCopresheafCounit (P : PolyEndo X) :
    copresheafToPolyCoalgFunctor P ⋙
      polyCoalgToCopresheafFunctor P ≅
    𝟭 (PolyCofreeCat P ⥤ Type u) :=
  CategoryTheory.NatIso.ofComponents
    (fun F => (copresheafBFNatIso P F).symm)
    (fun {F G} η => by
      ext obj ⟨⟨obj', elem'⟩, h⟩
      subst h
      simp only [CategoryTheory.Iso.symm_hom,
        CategoryTheory.NatIso.ofComponents_inv_app,
        CategoryTheory.Functor.id_map,
        CategoryTheory.FunctorToTypes.comp,
        copresheafBFNatIso]
      simp only [copresheafBFRoundtripBwd]
      dsimp [polyCoalgToCopresheafFunctor,
        copresheafToPolyCoalgFunctor,
        CategoryTheory.Functor.comp_map,
        coalgCopresheafFunctor,
        coalgCopresheafFunctor_natTrans,
        coalgCopresheafFunctor_app,
        copresheafNatTransHom,
        copresheafNatTransMor]
      exact (congrFun
        (η.naturality (eqToHom _)) elem').symm)

/--
The unit of the copresheaf equivalence:
`𝟭 (PolyCoalg P) ≅ Phi ⋙ Psi` where
`Phi = polyCoalgToCopresheafFunctor P` and
`Psi = copresheafToPolyCoalgFunctor P`.
-/
def polyCoalgCopresheafUnit (P : PolyEndo X) :
    𝟭 (PolyCoalg P) ≅
    polyCoalgToCopresheafFunctor P ⋙
      copresheafToPolyCoalgFunctor P :=
  CategoryTheory.NatIso.ofComponents
    (fun α => roundtripFBCoalgIso P α)
    (fun {α β} f => by
      apply Endofunctor.Coalgebra.Hom.ext
      apply Over.OverMorphism.ext
      funext a
      dsimp [roundtripFBCoalgIso,
        roundtripFBCoalgHomFwd,
        roundtripFBCarrierMorFwd,
        roundtripFBCarrierFwd,
        copresheafToPolyCoalgFunctor,
        polyCoalgToCopresheafFunctor,
        copresheafNatTransHom,
        copresheafNatTransMor,
        coalgCopresheafFunctor,
        coalgCopresheafFunctor_natTrans,
        coalgCopresheafFunctor_app]
      have h_tgt := coalgMorphism_target_eq
        ((polyCoalgToComonadCoalg X P).map f)
        a
      have h_tgt' :
          coalgCopresheafTarget
            ((polyCoalgToComonadCoalg X P).obj β)
            (f.f.left a) =
          coalgCopresheafTarget
            ((polyCoalgToComonadCoalg X P).obj α)
            a := by
        convert h_tgt using 2
      have comm : ∀ (t : PolyCofreeCat P)
          (p : coalgCopresheafTarget
            ((polyCoalgToComonadCoalg X P).obj β)
            (f.f.left a) = t),
          (⟨coalgCopresheafTarget
              ((polyCoalgToComonadCoalg X P).obj β)
              (f.f.left a),
            ⟨f.f.left a, rfl⟩⟩ :
            Σ obj, coalgCopresheafObj
              ((polyCoalgToComonadCoalg X P).obj β)
              obj) =
          ⟨t, ⟨f.f.left a, p⟩⟩ := by
        intro t p; subst p; rfl
      exact comm _ h_tgt')

/--
The category of P-coalgebras is equivalent to the
copresheaf topos on the cofree category of P.
-/
def polyCoalgCopresheafEquiv (P : PolyEndo X) :
    PolyCoalg P ≌ (PolyCofreeCat P ⥤ Type u) :=
  CategoryTheory.Equivalence.mk
    (polyCoalgToCopresheafFunctor P)
    (copresheafToPolyCoalgFunctor P)
    (polyCoalgCopresheafUnit P)
    (polyCoalgCopresheafCounit P)

/--
The Eilenberg-Moore coalgebra category of the cofree
comonad is equivalent to the copresheaf topos on the
cofree category. Composed from `polyCoalgComonadEquiv`
and `polyCoalgCopresheafEquiv`.
-/
def comonadCoalgCopresheafEquiv (P : PolyEndo X) :
    Comonad.Coalgebra (polyCofreeComonad X P) ≌
    (PolyCofreeCat P ⥤ Type u) :=
  (polyCoalgComonadEquiv P).symm.trans
    (polyCoalgCopresheafEquiv P)

end GebLean

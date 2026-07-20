import Geb.Mathlib.Data.PFunctor.Slice.W
import GebLean.SliceW.Translate

/-!
# The free-monad carrier and constructors on a slice endofunctor

The free monad on a slice endofunctor `F` over `I`, with leaves `Y` glued in
along `v : Y → I`, is the W-type of the translate augmentation
`translate v F` (Gambino–Kock 2013), restricted to a fixed index `i` by its
fiber. `FreeM v F i` is that fiber; `pure` and `node` are the two shapes of
`translate v F` read back as the free monad's leaf and node constructors.

## Main definitions

* `SlicePFunctor.FreeM` — the free-monad carrier: the fiber of
  `(translate v F).wIndex` over `i`.
* `SlicePFunctor.FreeM.pure` — the leaf constructor, from a leaf datum lying
  over `i`.
* `SlicePFunctor.FreeM.node` — the node constructor, from an `F`-shape and a
  family of subtrees indexed by its positions.
* `SlicePFunctor.FreeM.bindW` — the grafting substitution on the underlying
  `translate`-trees: a single `W.elim` replacing each leaf by its substitute.
* `SlicePFunctor.FreeM.bind` — the free-monad bind, `bindW` on the underlying
  tree with the index-preservation witness.

## Main statements

* `SlicePFunctor.FreeM.val_pure` / `SlicePFunctor.FreeM.val_node` — the
  underlying-tree characterization of `pure` and `node`, as `W.mk` on the
  corresponding summand of `translate v F`.
* `SlicePFunctor.FreeM.pure_bind` / `SlicePFunctor.FreeM.bind_node` — the
  computation rules for `bind`: the left-unit law on `pure`, and recursion into
  children on `node`.
* `SlicePFunctor.FreeM.bindW_pure` / `SlicePFunctor.FreeM.bind_pure` — the
  right-unit law, at the underlying-tree level and wrapped for `bind`.
* `SlicePFunctor.FreeM.bindW_bindW` / `SlicePFunctor.FreeM.bind_assoc` — the
  associativity law, at the underlying-tree level and wrapped for `bind`.
* `SlicePFunctor.FreeM.pure_transport` / `SlicePFunctor.FreeM.bind_transport` —
  compatibility of index transport with `pure` and `bind`.

## References

N. Gambino and J. Kock, "Polynomial functors and polynomial monads",
Mathematical Proceedings of the Cambridge Philosophical Society 154 (2013)
153-192, DOI `10.1017/S0305004112000394`.

## Tags

free monad, W-type, initial algebra, polynomial functor, slice category,
container, PFunctor
-/

namespace SlicePFunctor

universe uY uY' uY'' uA uB uI

variable {I : Type uI} {Y : Type uY} {Y' : Type uY'} {Y'' : Type uY''}
variable {v : Y → I} {v' : Y' → I} {v'' : Y'' → I}
variable {F : SlicePFunctor.{uA, uB, uI, uI} I I}

/-- The free-monad carrier at `i`: the fiber of `(translate v F).wIndex` over
`i`, i.e. the `translate v F`-trees indexed at `i`. -/
def FreeM (v : Y → I) (F : SlicePFunctor.{uA, uB, uI, uI} I I) (i : I) :=
  { w : (translate v F).W // (translate v F).wIndex w = i }

namespace FreeM

/-- The leaf constructor: a leaf datum `a` lying over `i` (i.e. `v a.1 = i`)
gives the nullary `Sum.inl` node of `translate v F`. -/
def pure {i : I} (a : { y : Y // v y = i }) : FreeM v F i :=
  ⟨W.mk ⟨⟨Sum.inl a.1, fun e => e.elim⟩, funext fun e => e.elim⟩, by
    rw [W.wIndex_mk]
    exact a.2⟩

/-- The node constructor: an `F`-shape `a` together with a family of subtrees
`c`, one per position of `a`, each lying over the direction-input map's value
at that position, gives the `Sum.inr` node of `translate v F`. -/
def node (a : F.A) (c : (b : F.B a) → FreeM v F (F.rCurried a b)) : FreeM v F (F.q a) :=
  ⟨W.mk ⟨⟨Sum.inr a, fun b => (c b).1⟩,
      ((translate v F).toSliceDomPFunctor.compatible_iff _ _ _).mpr fun b => (c b).2⟩, by
    rw [W.wIndex_mk]
    exact translate_q_inr a⟩

/-- The underlying tree of `pure a` is the `Sum.inl` node of `translate v F`
at `a.1`, with vacuous (`PEmpty`) children. -/
@[simp]
theorem val_pure {i : I} (a : { y : Y // v y = i }) :
    (pure a).1 = W.mk (F := translate v F) ⟨⟨Sum.inl a.1, fun e => e.elim⟩,
      funext fun e => e.elim⟩ :=
  rfl

/-- The underlying tree of `node a c` is the `Sum.inr` node of `translate v F`
at `a`, with children `c` reduced to their underlying trees. -/
@[simp]
theorem val_node (a : F.A) (c : (b : F.B a) → FreeM v F (F.rCurried a b)) :
    (node a c).1 = W.mk (F := translate v F) ⟨⟨Sum.inr a, fun b => (c b).1⟩,
      ((translate v F).toSliceDomPFunctor.compatible_iff _ _ _).mpr fun b => (c b).2⟩ :=
  rfl

/-- The grafting substitution on `translate v F`-trees underlying `bind`: a
single `W.elim` into `(translate v' F).W`. A leaf `Sum.inl y` is replaced by
the underlying tree of the substitute `f (v y) ⟨y, rfl⟩`; a node `Sum.inr a` is
rebuilt with the same shape and already-substituted children, its compatibility
re-read for `translate v' F` (whose positions and direction-input map agree
with those of `translate v F` at `Sum.inr`). -/
def bindW (f : ∀ j, { a : Y // v a = j } → FreeM v' F j) :
    (translate v F).W → (translate v' F).W :=
  W.elim (translate v F) ((translate v' F).W) (translate v' F).wIndex
    (fun z => match z with
      | ⟨⟨Sum.inl y, _⟩, _⟩ => (f (v y) ⟨y, rfl⟩).1
      | ⟨⟨Sum.inr a, c⟩, hc⟩ =>
          W.mk (F := translate v' F) ⟨⟨Sum.inr a, c⟩,
            ((translate v' F).toSliceDomPFunctor.compatible_iff _ _ _).mpr
              (((translate v F).toSliceDomPFunctor.compatible_iff _ _ _).mp hc)⟩)
    (funext fun z => match z with
      | ⟨⟨Sum.inl y, _⟩, _⟩ => (f (v y) ⟨y, rfl⟩).2
      | ⟨⟨Sum.inr _, _⟩, _⟩ => rfl)

/-- The free-monad bind: substitute along `f` into the tree `t`. The index is
preserved, since both the leaf substitutes and the rebuilt nodes lie over the
same index as the shape they replace. -/
def bind {i : I} (t : FreeM v F i)
    (f : ∀ j, { a : Y // v a = j } → FreeM v' F j) : FreeM v' F i :=
  ⟨bindW f t.1,
    (congrFun (W.comp_elim (translate v F) ((translate v' F).W)
      (translate v' F).wIndex _ _) t.1).trans t.2⟩

/-- Left unit: binding a leaf `pure a` applies the substitution `f` at `a`. -/
theorem pure_bind {i : I} (a : { y : Y // v y = i })
    (f : ∀ j, { a : Y // v a = j } → FreeM v' F j) :
    (FreeM.pure a).bind f = f i a := by
  obtain ⟨y, hy⟩ := a
  subst hy
  exact Subtype.ext rfl

/-- Binding commutes with `node`: it recurses into each child. -/
theorem bind_node (a : F.A) (c : (b : F.B a) → FreeM v F (F.rCurried a b))
    (f : ∀ j, { a : Y // v a = j } → FreeM v' F j) :
    (FreeM.node a c).bind f = FreeM.node a (fun b => (c b).bind f) :=
  Subtype.ext rfl

/-- Right unit at the tree level: grafting each leaf to its own `pure` is the
identity on `translate v F`-trees. Structural induction with a `Sum` shape
split; the leaf branch collapses to the `pure` tree (children into `PEmpty`
agree by elimination) and the node branch recurses through the hypotheses. -/
theorem bindW_pure (z : (translate v F).W) :
    bindW (fun _ a => FreeM.pure a) z = z :=
  W.induction (F := translate v F)
    (motive := fun z => bindW (fun _ a => FreeM.pure a) z = z)
    (fun x ih => by
      obtain ⟨⟨a, c⟩, hc⟩ := x
      cases a with
      | inl y =>
          exact congrArg W.mk
            (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun e => e.elim))))
      | inr a' =>
          exact congrArg W.mk
            (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun b => ih b)))))
    z

/-- Right unit: binding a tree with the identity substitution returns it. -/
theorem bind_pure {i : I} (t : FreeM v F i) :
    t.bind (fun _ a => FreeM.pure a) = t :=
  Subtype.ext (bindW_pure t.1)

/-- Associativity at the tree level: grafting along `f` then `g` equals grafting
along the pointwise composite `fun j a => (f j a).bind g`. Structural induction
with a `Sum` shape split; the leaf branch reduces both sides to
`((f (v y) ⟨y, rfl⟩).bind g).1` and the node branch recurses through the
hypotheses. -/
theorem bindW_bindW (f : ∀ j, { a : Y // v a = j } → FreeM v' F j)
    (g : ∀ j, { b : Y' // v' b = j } → FreeM v'' F j) (z : (translate v F).W) :
    bindW g (bindW f z) = bindW (fun j a => (f j a).bind g) z :=
  W.induction (F := translate v F)
    (motive := fun z => bindW g (bindW f z) = bindW (fun j a => (f j a).bind g) z)
    (fun x ih => by
      obtain ⟨⟨a, c⟩, hc⟩ := x
      cases a with
      | inl y => rfl
      | inr a' =>
          exact congrArg W.mk
            (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun b => ih b)))))
    z

/-- Associativity: rebinding `t` along `f` then `g` factors through the
pointwise composite. -/
theorem bind_assoc {i : I} (t : FreeM v F i)
    (f : ∀ j, { a : Y // v a = j } → FreeM v' F j)
    (g : ∀ j, { b : Y' // v' b = j } → FreeM v'' F j) :
    (t.bind f).bind g = t.bind (fun j a => (f j a).bind g) :=
  Subtype.ext (bindW_bindW f g t.1)

/-- Transporting a `pure` leaf along an index equality re-reads its fiber
witness: it is the `pure` of the same datum lying over the target index. -/
theorem pure_transport {i i' : I} (h : i = i') (y : Y) (hy : v y = i) :
    h ▸ (FreeM.pure ⟨y, hy⟩ : FreeM v F i) = FreeM.pure ⟨y, hy.trans h⟩ := by
  subst h
  rfl

/-- Transport commutes with `bind`: binding a transported tree equals
transporting the bind. -/
theorem bind_transport {i i' : I} (h : i = i') (t : FreeM v F i)
    (f : ∀ j, { a : Y // v a = j } → FreeM v' F j) :
    (h ▸ t).bind f = h ▸ (t.bind f) := by
  subst h
  rfl

end FreeM

end SlicePFunctor

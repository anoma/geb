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
* `SlicePFunctor.FreeM.elimAlg` — the algebra of the `elim` fold at the sigma
  carrier `Σ i, C i`, the leaf and node cases of `W.elim`'s target algebra.
* `SlicePFunctor.FreeM.elim` — the free-monad fold: a leaf function and a
  node algebra into a sort-indexed family `C`, realized by a single `W.elim`.

## Main statements

* `SlicePFunctor.FreeM.val_pure` / `SlicePFunctor.FreeM.val_node` — the
  underlying-tree characterization of `pure` and `node`, as `W.mk` on the
  corresponding summand of `translate v F`.
* `SlicePFunctor.FreeM.induction` — structural induction over the free monad: a
  leaf case at `pure`, a node case at `node` with the children's hypotheses.
* `SlicePFunctor.FreeM.pure_bind` / `SlicePFunctor.FreeM.bind_node` — the
  computation rules for `bind`: the left-unit law on `pure`, and recursion into
  children on `node`.
* `SlicePFunctor.FreeM.bindW_pure` / `SlicePFunctor.FreeM.bind_pure` — the
  right-unit law, at the underlying-tree level and wrapped for `bind`.
* `SlicePFunctor.FreeM.bindW_bindW` / `SlicePFunctor.FreeM.bind_assoc` — the
  associativity law, at the underlying-tree level and wrapped for `bind`.
* `SlicePFunctor.FreeM.pure_transport` / `SlicePFunctor.FreeM.bind_transport` —
  compatibility of index transport with `pure` and `bind`.
* `SlicePFunctor.FreeM.elimAlg_over` — `elimAlg` lies over `I`, the algebra
  condition `W.elim` requires.
* `SlicePFunctor.FreeM.elim_pure` / `SlicePFunctor.FreeM.elim_node` — the
  computation rules for `elim`: the leaf case and recursion into children on
  `node`.
* `SlicePFunctor.FreeM.elim_transport` — compatibility of index transport
  with `elim`.

## References

N. Gambino and J. Kock, "Polynomial functors and polynomial monads",
Mathematical Proceedings of the Cambridge Philosophical Society 154 (2013)
153-192, DOI `10.1017/S0305004112000394`.

## Tags

free monad, W-type, initial algebra, polynomial functor, slice category,
container, PFunctor
-/

namespace SlicePFunctor

universe uY uY' uY'' uA uB uI uC

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

/-- Structural induction for the free monad: a predicate on the sort-indexed
family `FreeM v F` holds everywhere once it holds of every leaf `pure a` and is
inherited by every node `node a c` from its children. The fibrewise form of
`SlicePFunctor.W.induction`: the motive is generalized over the fiber witness,
and the two branches of the `translate` shape split are re-read as `pure` and
`node`. -/
theorem induction {motive : ∀ i, FreeM v F i → Prop}
    (leaf : ∀ (i : I) (a : { y : Y // v y = i }), motive i (FreeM.pure a))
    (nd : ∀ (a : F.A) (c : (b : F.B a) → FreeM v F (F.rCurried a b)),
      (∀ b, motive (F.rCurried a b) (c b)) → motive (F.q a) (FreeM.node a c))
    {i : I} (t : FreeM v F i) : motive i t := by
  have key : ∀ w : (translate v F).W,
      ∀ (x : I) (hx : (translate v F).wIndex w = x), motive x ⟨w, hx⟩ := by
    refine W.induction (F := translate v F) ?_
    intro z ih x hx
    subst hx
    obtain ⟨⟨a, c⟩, hc⟩ := z
    cases a with
    | inl y =>
        have hleaf : (⟨W.mk ⟨⟨Sum.inl y, c⟩, hc⟩, rfl⟩ : FreeM v F _)
            = FreeM.pure ⟨y, rfl⟩ :=
          Subtype.ext (congrArg W.mk
            (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun e => e.elim)))))
        rw [hleaf]
        exact leaf _ ⟨y, rfl⟩
    | inr a' =>
        have hpf := ((translate v F).toSliceDomPFunctor.compatible_iff
          (translate v F).wIndex (Sum.inr a') c).mp hc
        have hnode : (⟨W.mk ⟨⟨Sum.inr a', c⟩, hc⟩, rfl⟩ : FreeM v F _)
            = FreeM.node a' (fun b => ⟨c b, hpf b⟩) :=
          Subtype.ext rfl
        rw [hnode]
        exact nd a' _ fun b => ih b _ (hpf b)
  exact key t.1 i t.2

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
identity on `translate v F`-trees. `FreeM.induction` at the tautological fiber
of the tree; the leaf branch collapses definitionally and the node branch
recurses through the hypotheses. -/
theorem bindW_pure (z : (translate v F).W) :
    bindW (fun _ a => FreeM.pure a) z = z :=
  induction (motive := fun _ t => bindW (fun _ a => FreeM.pure a) t.1 = t.1)
    (fun _ _ => rfl)
    (fun _ _ ih => congrArg W.mk
      (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun b => ih b)))))
    (⟨z, rfl⟩ : FreeM v F _)

/-- Right unit: binding a tree with the identity substitution returns it. -/
theorem bind_pure {i : I} (t : FreeM v F i) :
    t.bind (fun _ a => FreeM.pure a) = t :=
  Subtype.ext (bindW_pure t.1)

/-- Associativity at the tree level: grafting along `f` then `g` equals grafting
along the pointwise composite `fun j a => (f j a).bind g`. `FreeM.induction` at
the tautological fiber of the tree; the leaf branch reduces both sides to
`((f (v y) ⟨y, rfl⟩).bind g).1` and the node branch recurses through the
hypotheses. -/
theorem bindW_bindW (f : ∀ j, { a : Y // v a = j } → FreeM v' F j)
    (g : ∀ j, { b : Y' // v' b = j } → FreeM v'' F j) (z : (translate v F).W) :
    bindW g (bindW f z) = bindW (fun j a => (f j a).bind g) z :=
  induction
    (motive := fun _ t => bindW g (bindW f t.1) = bindW (fun j a => (f j a).bind g) t.1)
    (fun _ _ => rfl)
    (fun _ _ ih => congrArg W.mk
      (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun b => ih b)))))
    (⟨z, rfl⟩ : FreeM v F _)

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

/-- The algebra of the `elim` fold at the sigma carrier `Σ i, C i` with index
map `Sigma.fst`: a leaf shape returns the leaf function's value at its own
index; a node shape applies the node algebra to the children's values, each
transported along its pinned index (the compatibility of the folded child).
N. Gambino and J. Kock, "Polynomial functors and polynomial monads",
Mathematical Proceedings of the Cambridge Philosophical Society 154 (2013)
153-192, DOI `10.1017/S0305004112000394` (the free monad's fold). -/
def elimAlg (C : I → Type uC) (leaf : ∀ i, { y : Y // v y = i } → C i)
    (node : ∀ a : F.A, (∀ b : F.B a, C (F.rCurried a b)) → C (F.q a)) :
    (translate v F).toSliceDomPFunctor.Obj (Sigma.fst (β := C)) → Σ i, C i :=
  fun z => match z with
    | ⟨⟨Sum.inl y, _⟩, _⟩ => ⟨v y, leaf (v y) ⟨y, rfl⟩⟩
    | ⟨⟨Sum.inr a, c⟩, hc⟩ =>
        ⟨F.q a, node a (fun b => cast (congrArg C
          (((translate v F).toSliceDomPFunctor.compatible_iff
            (Sigma.fst (β := C)) (Sum.inr a) c).mp hc b)) (c b).2)⟩

/-- The `elimAlg` algebra lies over `I`: its sigma index is the translate
functor's output index, by a non-recursive shape split. -/
theorem elimAlg_over (C : I → Type uC) (leaf : ∀ i, { y : Y // v y = i } → C i)
    (node : ∀ a : F.A, (∀ b : F.B a, C (F.rCurried a b)) → C (F.q a)) :
    Sigma.fst ∘ elimAlg C leaf node = (translate v F).obj (Sigma.fst (β := C)) :=
  funext fun z => match z with
    | ⟨⟨Sum.inl _, _⟩, _⟩ => rfl
    | ⟨⟨Sum.inr _, _⟩, _⟩ => rfl

/-- The fold of the free monad into a sort-indexed family `C`: a leaf function
and a node algebra, realized by a single `W.elim` at the sigma carrier
`Σ i, C i` with index map `Sigma.fst`; the final value is the sigma's second
component transported along the fiber proof `t.2`. N. Gambino and J. Kock,
"Polynomial functors and polynomial monads", Mathematical Proceedings of the
Cambridge Philosophical Society 154 (2013) 153-192, DOI
`10.1017/S0305004112000394` (the free monad's fold). -/
def elim (C : I → Type uC) (leaf : ∀ i, { y : Y // v y = i } → C i)
    (node : ∀ a : F.A, (∀ b : F.B a, C (F.rCurried a b)) → C (F.q a))
    {i : I} (t : FreeM v F i) : C i :=
  cast (congrArg C ((congrFun (W.comp_elim (translate v F) (Σ j, C j)
      (Sigma.fst (β := C)) (elimAlg C leaf node) (elimAlg_over C leaf node)) t.1).trans t.2))
    (W.elim (translate v F) (Σ j, C j) (Sigma.fst (β := C))
      (elimAlg C leaf node) (elimAlg_over C leaf node) t.1).2

/-- Left unit: folding a leaf `pure a` applies the leaf function at `a`. -/
theorem elim_pure (C : I → Type uC) (leaf : ∀ i, { y : Y // v y = i } → C i)
    (node : ∀ a : F.A, (∀ b : F.B a, C (F.rCurried a b)) → C (F.q a))
    {i : I} (a : { y : Y // v y = i }) :
    elim C leaf node (FreeM.pure a) = leaf i a := by
  obtain ⟨y, hy⟩ := a
  subst hy
  rfl

/-- Folding commutes with `node`: it recurses into each child. -/
theorem elim_node (C : I → Type uC) (leaf : ∀ i, { y : Y // v y = i } → C i)
    (node : ∀ a : F.A, (∀ b : F.B a, C (F.rCurried a b)) → C (F.q a))
    (a : F.A) (c : (b : F.B a) → FreeM v F (F.rCurried a b)) :
    elim C leaf node (FreeM.node a c) = node a (fun b => elim C leaf node (c b)) :=
  rfl

/-- Transport commutes with `elim`: folding a transported tree equals
transporting the fold. -/
theorem elim_transport (C : I → Type uC) (leaf : ∀ i, { y : Y // v y = i } → C i)
    (node : ∀ a : F.A, (∀ b : F.B a, C (F.rCurried a b)) → C (F.q a))
    {i i' : I} (h : i = i') (t : FreeM v F i) :
    elim C leaf node (h ▸ t) = h ▸ (elim C leaf node t) := by
  subst h
  rfl

end FreeM

end SlicePFunctor

import GebLean.SliceW.FreeM
import GebLeanTests.SliceW.Iso
import GebLeanTests.SliceW.Translate

/-! Smoke test for `SlicePFunctor.FreeM`, `FreeM.pure`, and `FreeM.node`, on
the toy translate functor of `GebLeanTests.SliceW.Translate` (the toy slice
endofunctor `F` of `GebLeanTests.SliceW.Iso`, translated along the constant
leaf map `v : Bool → PUnit`). -/

namespace SliceWFreeMTest

open SlicePFunctor

/-- A `pure` leaf, from the leaf datum `true` (`v true = PUnit.unit` by
`rfl`). -/
def pureLeaf : FreeM SliceWTranslateTest.v SliceWIsoTest.F PUnit.unit :=
  FreeM.pure ⟨true, rfl⟩

/-- `pureLeaf`'s fiber proof: its underlying tree's index is `PUnit.unit`. -/
example :
    (translate SliceWTranslateTest.v SliceWIsoTest.F).wIndex pureLeaf.1 = PUnit.unit :=
  pureLeaf.2

/-- `pureLeaf`'s underlying tree, via `val_pure`. -/
example :
    pureLeaf.1 = W.mk (F := translate SliceWTranslateTest.v SliceWIsoTest.F)
      ⟨⟨Sum.inl true, fun e => e.elim⟩, funext fun e => e.elim⟩ := by
  rfl

/-- A `node` at the unary `true` shape of the toy functor `F`, with `pureLeaf`
as its single child. -/
def nodeWithLeaves : FreeM SliceWTranslateTest.v SliceWIsoTest.F (SliceWIsoTest.F.q true) :=
  FreeM.node true (fun _ => pureLeaf)

/-- `nodeWithLeaves`'s fiber proof: its underlying tree's index is
`F.q true`. -/
example :
    (translate SliceWTranslateTest.v SliceWIsoTest.F).wIndex nodeWithLeaves.1
      = SliceWIsoTest.F.q true :=
  nodeWithLeaves.2

/-- `nodeWithLeaves`'s underlying tree, via `val_node`. -/
example : nodeWithLeaves.1 =
    W.mk (F := translate SliceWTranslateTest.v SliceWIsoTest.F)
      ⟨⟨Sum.inr true, fun _ => pureLeaf.1⟩,
        ((translate SliceWTranslateTest.v SliceWIsoTest.F).toSliceDomPFunctor.compatible_iff
          _ _ _).mpr fun _ => pureLeaf.2⟩ := by
  rfl

/-- The identity substitution: every leaf maps to its own `pure`. -/
def pureSubst : ∀ j, { a : Bool // SliceWTranslateTest.v a = j } →
    FreeM SliceWTranslateTest.v SliceWIsoTest.F j :=
  fun _ a => FreeM.pure a

/-- Left unit: binding a `pure` leaf with `pureSubst` returns the leaf, by
`pure_bind`. -/
example : pureLeaf.bind pureSubst = pureLeaf :=
  FreeM.pure_bind ⟨true, rfl⟩ pureSubst

/-- Binding a one-node tree with `pureSubst` reduces, by `bind_node` then
`pure_bind` on the child, back to the tree. No kernel reduction of trees. -/
example : nodeWithLeaves.bind pureSubst = nodeWithLeaves := by
  have hleaf : pureLeaf.bind pureSubst = pureLeaf := FreeM.pure_bind ⟨true, rfl⟩ pureSubst
  rw [nodeWithLeaves, FreeM.bind_node]
  simp only [hleaf]

/-- Right unit: binding a one-node tree with the identity substitution
`pureSubst` returns the tree, by `bind_pure`. -/
example : nodeWithLeaves.bind pureSubst = nodeWithLeaves :=
  FreeM.bind_pure nodeWithLeaves

/-- Associativity: rebinding a one-node tree factors through the pointwise
composite, by `bind_assoc`. -/
example : (nodeWithLeaves.bind pureSubst).bind pureSubst =
    nodeWithLeaves.bind (fun j a => (pureSubst j a).bind pureSubst) :=
  FreeM.bind_assoc nodeWithLeaves pureSubst pureSubst

/-- A constant carrier family: `Nat` at every index. -/
abbrev natCarrier : PUnit → Type := fun _ => Nat

/-- The leaf case of a node-counting fold: every leaf counts as one. -/
abbrev countLeaf : ∀ i : PUnit, { y : Bool // SliceWTranslateTest.v y = i } → natCarrier i :=
  fun _ _ => 1

/-- The node case of a node-counting fold: one more than the child count at
the toy functor's unary shape, zero at its nullary shape. -/
abbrev countNode : ∀ a : SliceWIsoTest.F.A,
    (∀ b : SliceWIsoTest.F.B a, natCarrier (SliceWIsoTest.F.rCurried a b)) →
      natCarrier (SliceWIsoTest.F.q a) :=
  fun a ih => match a with
    | true => ih () + 1
    | false => 0

/-- Folding `pureLeaf` counts its single leaf, by `elim_pure`. -/
example : FreeM.elim natCarrier countLeaf countNode pureLeaf = 1 :=
  FreeM.elim_pure natCarrier countLeaf countNode ⟨true, rfl⟩

/-- Folding `nodeWithLeaves` counts its one node plus its one leaf, by
`elim_node` then `elim_pure` on the child. No kernel reduction of trees. -/
example : FreeM.elim natCarrier countLeaf countNode nodeWithLeaves = 2 := by
  have hleaf : FreeM.elim natCarrier countLeaf countNode pureLeaf = 1 :=
    FreeM.elim_pure natCarrier countLeaf countNode ⟨true, rfl⟩
  rw [nodeWithLeaves, FreeM.elim_node]
  simp only [hleaf]

end SliceWFreeMTest

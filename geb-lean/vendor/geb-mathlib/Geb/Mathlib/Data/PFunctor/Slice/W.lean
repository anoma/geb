/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.PFunctor.Slice.Basic

/-!
# W-types of slice polynomial functors (constructive core)

When `dom = cod = I`, a `SlicePFunctor I I` is a slice endofunctor
`Type/I → Type/I`. Its W-type (initial algebra) is obtained as a subtype of the
`PFunctor` W-type `P.W`: a tree is admitted when every node's children sit
over the direction-input indices prescribed by `r`, and it is indexed by the
`q`-assigned output index of its root shape.

The index (codomain-assignment) and the admissibility predicate
(domain-restriction) are not written by explicit recursion. The index of a
tree is the output index of its root, so it is not recursive at all; the
predicate is recursive, but is obtained from mathlib's non-dependent W-type
eliminator `WType.elim`, folding the index and the predicate together into
the structure `WIndex` via the algebra `windexStep`. Carrying the index
inside the fold is what lets the algebra state the direction-input-map
condition `OverInput` — the children's index family, as a function of
direction, equals `rCurried a`, the shape of `SliceDomPFunctor.Compatible`:
the plain `Prop`-valued fold discards the children, so the condition would
be inexpressible without either this
pairing or the dependent recursor.

The carrier `W` is the admissible trees, with structure map `windex`. Its
constructor `mk` and destructor `dest` are mutually inverse (`W` is a fixed
point of the slice endofunctor), and `elim` is the morphism into any slice
algebra over `I`. Only the existence half of the initial-algebra universal
property is established here — the carrier, its fixed-point structure
(`mk`/`dest`), and `elim` with its computation rule `elim_mk` and over-`I` law
`comp_elim`; uniqueness of `elim` is not formalized. The value of `elim` is
computed by a single non-dependent `WType.elim` (the fold `elimData`, with
algebra `elimStep`) into the carrier `ElimData` — each subtree's index, its
admissibility, and (given admissibility) its image value with the witness that
the value lies over the index, i.e. a slice morphism
`(valid, const index) → (Y, p)`; carrying the value in the fold keeps `elim`'s
computational layer independent of the dependent recursor: `elim` uses
`WType.rec` only in the proof `elimData_valid`, relating the fold's
admissibility component to `WValid`. A direct `WType.rec` definition of a
`Type`-valued datum (such as `elim`'s value) would be `noncomputable` — the
code generator does not compile recursor applications — which the project's
constructive discipline forbids; a `Prop`-valued recursor definition such as
`recProp` is exempt, its content being erased. All of this stays
`Classical.choice`-free.

The single index type is forced: the constraint compares a child's
codomain-index against the parent's domain-index, so it typechecks only when
`dom = cod`. That is the endofunctor condition an initial algebra requires.

## Main definitions

* `SlicePFunctor.windexRoot` — the index of a slice W-tree: the output index
  of its root shape. Not recursive.
* `SlicePFunctor.WIndex` / `SlicePFunctor.windexStep` / `SlicePFunctor.windexValid`
  — the index-and-admissibility carrier, the algebra computing it, and the fold.
  `SlicePFunctor.ForAll` / `SlicePFunctor.AllValid` / `SlicePFunctor.OverInput` /
  `SlicePFunctor.NodeValid` are the direction-quantifier, the
  all-children-admissible condition (`ForAll` of the children's `valid`), the
  direction-input-map condition, and the node-admissibility predicate
  combining the latter two.
* `SlicePFunctor.WValid` — the domain-restriction predicate: the admissibility
  component of `windexValid`.
* `SlicePFunctor.W` — the carrier of the slice W-type: the admissible trees.
* `SlicePFunctor.windex` — the slice W-type's structure map into `I`.
* `SlicePFunctor.W.mk` / `SlicePFunctor.W.dest` — the constructor and
  destructor of the slice W-type.
* `SlicePFunctor.W.ElimData` / `SlicePFunctor.W.elimStep` /
  `SlicePFunctor.W.elimData` — the `elim` carrier, algebra, and fold.
* `SlicePFunctor.W.elim` — the morphism from the slice W-type into any slice
  algebra over `I`.
* `SlicePFunctor.W.recProp` — the paramorphism from the slice W-type into
  `Prop`: a predicate whose step sees each node and its child subtrees together
  with the children's predicate values.

## Main statements

* `SlicePFunctor.windexValid_index_eq_windexRoot` — the index component of the
  fold agrees with the non-recursive root index; one non-recursive case split.
* `SlicePFunctor.wValid_mk` — admissibility unfolded one level.
* `SlicePFunctor.W.dest_mk` / `SlicePFunctor.W.mk_dest` — `mk` and `dest` are
  mutually inverse.
* `SlicePFunctor.W.windex_mk` / `SlicePFunctor.W.comp_elim` — `mk` and `elim`
  lie over `I`.
* `SlicePFunctor.W.elim_mk` — the computation rule for `elim`: it is a morphism
  of slice algebras.
* `SlicePFunctor.W.elimData_valid` — the fold's admissibility component agrees
  with `WValid`; a use of the dependent recursor `WType.rec`.
* `SlicePFunctor.W.ind` — structural induction for the slice W-type, the wrapped
  form of `WType.rec` on the admissibility subtype.
* `SlicePFunctor.W.recProp_mk` — the one-level computation rule for `recProp`.

## Implementation notes

`windexValid` folds into the structure `WIndex` (`index`, `valid`) via
`windexStep`; a node's `valid` is `NodeValid` — `AllValid` (every child
admissible) and `OverInput` (the children's index family equal to `rCurried a`,
the `Compatible` shape). Its index component is the depth-1 root output
index, so `windexValid_index_eq_windexRoot` needs only `cases`. `elim`'s
value is computed by `elimData`, a single non-dependent `WType.elim` with
algebra `elimStep` into
the structure `ElimData` (extending `WIndex` with a `value` function and an
`over` law, a slice morphism); within `elim`'s construction the dependent
recursor is used only in the proof `elimData_valid` (a `WType.rec` application
showing the fold's admissibility component agrees with `WValid`). A direct
`WType.rec` *definition* of a `Type`-valued datum (such as `elim`'s value) would
be rejected by the code generator as `noncomputable`; a `WType.rec` application
in a proof, or a `Prop`-valued `WType.rec` definition such as `recProp`, is
unproblematic. `windexRoot`, `ForAll`, `AllValid`, `OverInput`,
`NodeValid`, `windexStep`,
`windexValid`, `WValid`, `W`, `windex`, `W.mk`, `W.dest`, `W.elimStep`,
`W.elimData`, `W.elim`, and `W.recProp` are `@[expose]` so a wrapper module and
the tests can unfold them across the module boundary.

## References

* [GambinoHyland2004]
* [GambinoKock2013]

## Tags

W-type, initial algebra, polynomial functor, dependent polynomial functor,
slice category, container, PFunctor
-/

public section

universe uA uB uI uY

namespace SlicePFunctor

/-- The index of a slice W-tree: the `q`-assigned output index of its root
shape. Not recursive — it reads only the root node, via `PFunctor.W.head`. -/
@[expose] def windexRoot {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I) :
    F.toPFunctor.W → I :=
  F.q ∘ PFunctor.W.head

/-- The index and admissibility of a slice W-tree, the two components folded
together by `windexValid`. -/
@[ext]
structure WIndex (I : Type uI) where
  /-- The tree's index: the output index of its root shape. -/
  index : I
  /-- The tree's admissibility. -/
  valid : Prop

/-- Every direction satisfies the predicate `P`. Parallels `OverInput`, over
`F.B a`. -/
@[expose] def ForAll {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    (a : F.toPFunctor.A) (P : F.toPFunctor.B a → Prop) : Prop :=
  ∀ b, P b

/-- Every child of `c` is admissible: `ForAll` of the children's `valid`. -/
@[expose] def AllValid {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    (a : F.toPFunctor.A) (c : F.toPFunctor.B a → WIndex I) : Prop :=
  F.ForAll a (WIndex.valid ∘ c)

/-- The direction-input-map condition on a node's children: their index
family, as a function of direction, equals the direction-input map
`rCurried a`. Point-free — the shape of `SliceDomPFunctor.Compatible` for
the identity projection. -/
@[expose] def OverInput {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    (a : F.toPFunctor.A) (idx : F.toPFunctor.B a → I) : Prop :=
  idx = F.rCurried a

/-- A node with shape `a` and children `c` is admissible when every child is
admissible (`AllValid`) and the children's index family lies over the
direction-input map (`OverInput`). -/
@[expose] def NodeValid {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    (a : F.toPFunctor.A) (c : F.toPFunctor.B a → WIndex I) : Prop :=
  F.AllValid a c ∧ F.OverInput a (WIndex.index ∘ c)

/-- The algebra computing a node's index and admissibility from its children's:
the index is the `q`-assigned output index of the shape, and the node is
`NodeValid`. -/
@[expose] def windexStep {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I) :
    F.toPFunctor.Obj (WIndex I) → WIndex I :=
  fun ⟨a, c⟩ ↦ { index := F.q a, valid := F.NodeValid a c }

/-- The index paired with admissibility: the `F.toPFunctor`-algebra morphism
into `(WIndex I, windexStep)` given by `WType.elim`. -/
@[expose] def windexValid {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I) :
    F.toPFunctor.W → WIndex I :=
  WType.elim (WIndex I) F.windexStep

/-- The domain-restriction predicate on slice W-trees: a tree is admitted when
every node's children sit over the direction-input indices prescribed by
`r`. The admissibility component of `windexValid`. -/
@[expose] def WValid {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I) :
    F.toPFunctor.W → Prop :=
  WIndex.valid ∘ F.windexValid

/-- The index component of `windexValid` agrees with the non-recursive root
index. A depth-1 fact: proved by a single non-recursive case split. -/
@[simp]
theorem windexValid_index_eq_windexRoot {I : Type uI}
    (F : SlicePFunctor.{uA, uB, uI, uI} I I) (w : F.toPFunctor.W) :
    (F.windexValid w).index = F.windexRoot w := by
  cases w with
  | mk a f => rfl

/-- Admissibility unfolded one level: `WType.mk a f` is admitted exactly when
every child `f b` is admitted and the children's index family lies over the
direction-input map. -/
theorem wValid_mk {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    (a : F.toPFunctor.A) (f : F.toPFunctor.B a → F.toPFunctor.W) :
    F.WValid (WType.mk a f) ↔
      F.ForAll a (F.WValid ∘ f) ∧ F.OverInput a (F.windexRoot ∘ f) := by
  have h : WIndex.index ∘ F.windexValid ∘ f = F.windexRoot ∘ f :=
    funext fun b ↦ F.windexValid_index_eq_windexRoot (f b)
  change (F.ForAll a (F.WValid ∘ f) ∧ F.OverInput a (WIndex.index ∘ F.windexValid ∘ f)) ↔ _
  rw [h]

/-- The carrier of the slice W-type: the admissible `PFunctor` W-trees. -/
@[expose] def W {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I) : Type (max uA uB) :=
  { w : F.toPFunctor.W // F.WValid w }

/-- The slice W-type's structure map as an object of `Type/I`: the index of the
underlying tree. -/
@[expose] def windex {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I) : F.W → I :=
  F.windexRoot ∘ Subtype.val

namespace W

/-- The constructor of the slice W-type: the slice endofunctor's value at
`(W, windex)` maps into `W`. The algebra structure map. -/
@[expose] def mk {I : Type uI} {F : SlicePFunctor.{uA, uB, uI, uI} I I}
    (x : F.toSliceDomPFunctor.Obj F.windex) : F.W :=
  ⟨WType.mk x.1.1 (Subtype.val ∘ x.1.2),
    (F.wValid_mk _ _).mpr ⟨fun b ↦ (x.1.2 b).property,
      funext ((F.toSliceDomPFunctor.compatible_iff F.windex x.1.1 x.1.2).mp x.2)⟩⟩

/-- The destructor of the slice W-type: every admissible tree decomposes as a
shape together with a compatible family of admissible subtrees. Inverse to
`mk`. -/
@[expose] def dest {I : Type uI} {F : SlicePFunctor.{uA, uB, uI, uI} I I}
    (z : F.W) : F.toSliceDomPFunctor.Obj F.windex :=
  match z with
  | ⟨WType.mk a f, hw⟩ =>
      ⟨⟨a, fun b ↦ ⟨f b, ((F.wValid_mk a f).mp hw).1 b⟩⟩,
        (F.toSliceDomPFunctor.compatible_iff F.windex a _).mpr
          fun b ↦ congrFun ((F.wValid_mk a f).mp hw).2 b⟩

/-- `dest` is a left inverse of `mk`. -/
@[simp]
theorem dest_mk {I : Type uI} {F : SlicePFunctor.{uA, uB, uI, uI} I I}
    (x : F.toSliceDomPFunctor.Obj F.windex) : dest (mk x) = x := by
  obtain ⟨⟨a, v⟩, hv⟩ := x
  apply Subtype.ext
  exact Sigma.ext rfl (heq_of_eq (funext fun b ↦ Subtype.ext rfl))

/-- `mk` is a left inverse of `dest`; with `dest_mk`, `mk` and `dest` are
mutually inverse, so `W` is a fixed point of the slice endofunctor. -/
@[simp]
theorem mk_dest {I : Type uI} {F : SlicePFunctor.{uA, uB, uI, uI} I I}
    (z : F.W) : mk (dest z) = z := by
  obtain ⟨w, hw⟩ := z
  cases w with
  | mk a f => rfl

/-- `mk` lies over `I`: its index is the output index assigned by `F.obj`. -/
@[simp]
theorem windex_mk {I : Type uI} {F : SlicePFunctor.{uA, uB, uI, uI} I I}
    (x : F.toSliceDomPFunctor.Obj F.windex) : F.windex (mk x) = F.obj F.windex x :=
  rfl

/-- The `elim` fold carrier: extends `WIndex` to a slice morphism
`(valid, const index) → (Y, p)` — a value function defined once the subtree is
admissible, together with the proof that it lies over the index. -/
@[ext]
structure ElimData {I : Type uI} (Y : Type uY) (p : Y → I) extends WIndex I where
  /-- The image value, available once the subtree is admissible. -/
  value : valid → Y
  /-- The value lies over the index: `p ∘ value` is constant at `index`. -/
  over : p ∘ value = Function.const valid index

/-- The slice-algebra step of the `elim` fold: index and admissibility
(`NodeValid`) as for `windexStep`, and a value function that, given a node's
admissibility, applies the target algebra `g` to the compatible family of its
children's values, with `over` recording that the result lies over the index. -/
@[expose] def elimStep {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    (Y : Type uY) (p : Y → I) (g : F.toSliceDomPFunctor.Obj p → Y) (hg : p ∘ g = F.obj p) :
    F.toPFunctor.Obj (ElimData Y p) → ElimData Y p :=
  fun ⟨a, c⟩ ↦
    { index := F.q a
      valid := F.NodeValid a (ElimData.toWIndex ∘ c)
      value := fun hv ↦ g ⟨⟨a, fun b ↦ (c b).value (hv.1 b)⟩,
        (F.toSliceDomPFunctor.compatible_iff p a _).mpr fun b ↦
          (congrFun (c b).over (hv.1 b)).trans (congrFun hv.2 b)⟩
      over := funext fun _ ↦ congrFun hg _ }

/-- The `elim` fold: the `F.toPFunctor`-algebra morphism into
`(ElimData Y p, elimStep)` given by `WType.elim`, a single non-dependent fold
with no explicit recursion. -/
@[expose] def elimData {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    (Y : Type uY) (p : Y → I) (g : F.toSliceDomPFunctor.Obj p → Y) (hg : p ∘ g = F.obj p) :
    F.toPFunctor.W → ElimData Y p :=
  WType.elim (ElimData Y p) (elimStep F Y p g hg)

/-- The index component of `elimData` is the root index. -/
@[simp]
theorem elimData_index {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    (Y : Type uY) (p : Y → I) (g : F.toSliceDomPFunctor.Obj p → Y) (hg : p ∘ g = F.obj p)
    (w : F.toPFunctor.W) : (elimData F Y p g hg w).index = F.windexRoot w := by
  cases w with
  | mk a f => rfl

/-- The admissibility component of `elimData`, unfolded one level. -/
theorem elimData_valid_mk {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    (Y : Type uY) (p : Y → I) (g : F.toSliceDomPFunctor.Obj p → Y) (hg : p ∘ g = F.obj p)
    (a : F.toPFunctor.A) (f : F.toPFunctor.B a → F.toPFunctor.W) :
    (elimData F Y p g hg (WType.mk a f)).valid =
      (F.ForAll a (fun b ↦ (elimData F Y p g hg (f b)).valid) ∧
        F.OverInput a (fun b ↦ (elimData F Y p g hg (f b)).index)) :=
  rfl

/-- The admissibility component of `elimData` agrees with `WValid`. An
inductive step: it applies the dependent recursor `WType.rec` (the initial
algebra's induction principle, consulting the hypothesis `ih`), unlike the
non-recursive `cases`/`casesOn` splits elsewhere. It is in a proof, where
non-computability is immaterial. -/
theorem elimData_valid {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    (Y : Type uY) (p : Y → I) (g : F.toSliceDomPFunctor.Obj p → Y) (hg : p ∘ g = F.obj p)
    (w : F.toPFunctor.W) : (elimData F Y p g hg w).valid ↔ F.WValid w :=
  WType.rec (motive := fun w ↦ (elimData F Y p g hg w).valid ↔ F.WValid w)
    (fun a f ih ↦ by
      beta_reduce
      rw [F.wValid_mk, elimData_valid_mk]
      exact and_congr (forall_congr' ih) (by simp only [OverInput, elimData_index]; rfl))
    w

/-- The eliminator of the slice W-type: the morphism into any slice algebra
`(Y, p, g)` over `I`. The existence half of initiality. The value is computed by
the non-dependent fold `elimData`; the tree's admissibility supplies the
argument to the fold's `value` function. -/
@[expose] def elim {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    (Y : Type uY) (p : Y → I) (g : F.toSliceDomPFunctor.Obj p → Y) (hg : p ∘ g = F.obj p) :
    F.W → Y :=
  fun z ↦
    (elimData F Y p g hg z.val).value
      ((elimData_valid F Y p g hg z.val).mpr z.property)

/-- `elim` lies over `I`: composing with the target structure map recovers
`windex`. -/
theorem comp_elim {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    (Y : Type uY) (p : Y → I) (g : F.toSliceDomPFunctor.Obj p → Y) (hg : p ∘ g = F.obj p) :
    p ∘ elim F Y p g hg = F.windex :=
  funext fun z ↦
    (congrFun (elimData F Y p g hg z.val).over
      ((elimData_valid F Y p g hg z.val).mpr z.property)).trans
      (elimData_index F Y p g hg z.val)

/-- The computation rule for `elim`: it commutes with the constructors, i.e. it
is a morphism of slice algebras. -/
theorem elim_mk {I : Type uI} (F : SlicePFunctor.{uA, uB, uI, uI} I I)
    (Y : Type uY) (p : Y → I) (g : F.toSliceDomPFunctor.Obj p → Y) (hg : p ∘ g = F.obj p)
    (x : F.toSliceDomPFunctor.Obj F.windex) :
    elim F Y p g hg (mk x) =
      g (F.toSliceDomPFunctor.map (elim F Y p g hg) (comp_elim F Y p g hg) x) :=
  rfl

/-- Structural induction for the slice W-type: a predicate holds of every
admissible tree once it holds of `mk x` whenever it holds of each child
`x.1.2 b`. The wrapped form of the dependent recursor `WType.rec` on the
admissibility subtype. -/
theorem ind {I : Type uI} {F : SlicePFunctor.{uA, uB, uI, uI} I I}
    {motive : F.W → Prop}
    (mk : ∀ (x : F.toSliceDomPFunctor.Obj F.windex),
        (∀ b, motive (x.1.2 b)) → motive (W.mk x)) :
    ∀ z, motive z :=
  fun z ↦
    WType.rec (motive := fun w ↦ ∀ (hw : F.WValid w), motive ⟨w, hw⟩)
      (fun a f ih hw' ↦ by
        rw [← mk_dest ⟨WType.mk a f, hw'⟩]
        exact mk _ fun b ↦ ih b (((F.wValid_mk a f).mp hw').1 b))
      z.1 z.2

/-- Paramorphism from the slice W-type into `Prop`: `step` sees the node `x`,
hence its child subtrees `x.1.2 b`, together with the children's predicate
values. The value is computed by `WType.rec` with a `Prop` motive, so no
`noncomputable` flag arises. `@[expose]` so the presheaf layer can unfold it. -/
@[expose] def recProp {I : Type uI} {F : SlicePFunctor.{uA, uB, uI, uI} I I}
    (step : (x : F.toSliceDomPFunctor.Obj F.windex) →
      (F.toPFunctor.B x.1.1 → Prop) → Prop) :
    F.W → Prop :=
  fun z ↦
    WType.rec (motive := fun w ↦ F.WValid w → Prop)
      (fun a f ih hv ↦
        step (dest ⟨WType.mk a f, hv⟩)
          (fun b ↦ ih b (((F.wValid_mk a f).mp hv).1 b)))
      z.1 z.2

/-- The one-level computation rule for `recProp`: on `mk x` it applies `step`
to the node `x` and the family of child values. Definitional; stated for
downstream unfolding. -/
theorem recProp_mk {I : Type uI} {F : SlicePFunctor.{uA, uB, uI, uI} I I}
    (step : (x : F.toSliceDomPFunctor.Obj F.windex) →
      (F.toPFunctor.B x.1.1 → Prop) → Prop)
    (x : F.toSliceDomPFunctor.Obj F.windex) :
    W.recProp step (W.mk x) = step x (fun b ↦ W.recProp step (x.1.2 b)) := by
  obtain ⟨⟨a, v⟩, hc⟩ := x
  rfl

end W

end SlicePFunctor

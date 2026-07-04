import GebLean.Binding.Laws

/-!
# The relative-monad universal property of substitution

The universal-property layer of an indexed binder-substitution kit
(decision 8): `RelativeMonad` bundles the minimal relative-monad structure
of Altenkirch, Chapman, and Uustalu, and `Tm.relativeMonad` instantiates it
at the substitution kit, exhibiting `(Tm S, Tm.var, sub)` as the free
relative monad over the variables family `Var`, relative to the `Set^Ty`
hom-family `∀ s, X s → Y s`. Its three laws are exactly `sub_var`, `sub_id`,
and `sub_sub` (Task 7), bridged to the hom-level statement by `funext`. This
is a relative-monad framing, not a `[Ctx, Set]` presheaf monoid: the
`hom`-family is a family map that `sub` consumes directly (an
`Env (Tm S)`), deliberately distinct from a presheaf natural transformation.
`(Tm S, Tm.var, sub)` is thereby the initial Sigma-monoid / free relative
monad over the variables presheaf, whose discrete degeneration (dropping the
sort-indexing, `J0 = Fin`) is the ordinary free monad of `S.polyEndo`. A
`Mon_` instantiation over the substitution-monoidal `[Ctx, Set]` category
(once its coend tensor is built) is deferred future work, per the design
spec's section 8.

## Main definitions

* `RelativeMonad` — a relative monad on `J : J0 → C`, relative to an
  ambient hom-family `hom` with identities `homId` and composition
  `homComp`: an object map `T`, a unit, and a Kleisli extension operator,
  subject to the two unit laws and associativity.
* `pointwiseId`, `pointwiseComp` — the identities and composition of the
  ambient `Set^Ty` hom-family `∀ s, X s → Y s`, pointwise at each sort.
* `Tm.relativeMonad` — the substitution relative monad: unit `Tm.var`,
  Kleisli extension `sub`.

## References

The relative-monad structure and its three laws follow T. Altenkirch,
J. Chapman, and T. Uustalu, "Monads need not be endofunctors", FoSSaCS 2010,
LNCS 6014, pp. 297-311, DOI `10.1007/978-3-642-12032-9_21` (Definition 1);
extended version, Logical Methods in Computer Science 11 (1:3), 2015, DOI
`10.2168/LMCS-11(1:3)2015`. The well-scoped-lambda-terms-as-relative-monad
reading follows the same source's Examples 2-3; background is detailed in
the research note,
`docs/superpowers/notes/2026-07-04-binder-substitution-research.md`,
section 2.2.
-/

namespace GebLean.Binding

universe u v w

/-- A minimal relative monad on `J : J0 → C` (Altenkirch, Chapman, and
Uustalu, Definition 1): an object map `T`, a unit embedding each `J`-object
into the corresponding `T`-object, and a Kleisli extension operator turning a
map out of a `J`-object into a `T`-object into a map out of the corresponding
`T`-object. The three laws are stated against the ambient hom-family `hom`,
whose identities and composition are supplied by `homId` and `homComp`
(`C` need not be a genuine category for this structure; only these two
operations on `hom` are used). Ordinary monads are the case `J = id`. -/
structure RelativeMonad {J0 : Type u} {C : Type v} (J : J0 → C)
    (hom : C → C → Type w) (homId : ∀ X, hom X X)
    (homComp : ∀ {X Y Z}, hom X Y → hom Y Z → hom X Z) (T : J0 → C) where
  /-- The unit: embeds a `J`-object into the corresponding `T`-object. -/
  unit : ∀ X, hom (J X) (T X)
  /-- Kleisli extension: extends a map out of a `J`-object into a `T`-object
  to a map out of the corresponding `T`-object. -/
  ext : ∀ {X Y}, hom (J X) (T Y) → hom (T X) (T Y)
  /-- Left unit law: extending a Kleisli arrow and composing it after the
  unit recovers the arrow. -/
  ext_unit : ∀ {X Y} (k : hom (J X) (T Y)), homComp (unit X) (ext k) = k
  /-- Right unit law: extending the unit is the ambient identity. -/
  unit_ext : ∀ {X}, ext (unit X) = homId (T X)
  /-- Associativity law: extending twice in sequence equals extending the
  hom-composite once. -/
  ext_ext : ∀ {X Y Z} (k : hom (J X) (T Y)) (l : hom (J Y) (T Z)),
      homComp (ext k) (ext l) = ext (homComp k (ext l))

variable {Ty : Type}

/-- The identity of the ambient `Set^Ty` hom-family `∀ s, X s → Y s`: the
pointwise identity function at every sort. -/
def pointwiseId (X : Ty → Type) : ∀ s, X s → X s :=
  fun _ => id

/-- Composition in the ambient `Set^Ty` hom-family `∀ s, X s → Y s`: pointwise
function composition at every sort. -/
def pointwiseComp {X Y Z : Ty → Type} (f : ∀ s, X s → Y s) (g : ∀ s, Y s → Z s) :
    ∀ s, X s → Z s :=
  fun s => g s ∘ f s

/-- The substitution relative monad: `Tm S` is the relative monad on the
variables family `Var`, relative to the `Set^Ty` hom-family
`∀ s, X s → Y s`, with unit `Tm.var` and Kleisli extension `sub`. The three
laws are exactly `sub_var`, `sub_id`, and `sub_sub`, each bridged from its
pointwise Task-7 statement to the hom-level equation by `funext`. -/
def Tm.relativeMonad (S : BinderSig Ty) :
    RelativeMonad (J0 := Ctx Ty) (C := Ty → Type) (fun Γ s => Var Γ s)
      (fun X Y => ∀ s, X s → Y s) pointwiseId pointwiseComp (fun Γ => Tm S Γ) where
  unit _ := fun _ x => Tm.var x
  ext k := fun _ t => sub k t
  ext_unit k := by funext s x; exact sub_var k x
  unit_ext := fun {_} => by funext s t; exact sub_id t
  ext_ext k l := by funext s t; exact sub_sub k l t

end GebLean.Binding

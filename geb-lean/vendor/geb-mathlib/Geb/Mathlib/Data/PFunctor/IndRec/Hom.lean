/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.Basic

/-!
# The homset of IR codes

`IR.Hom γ γ'` is the homset between two `IR` codes (Definition 8 of
[HancockMcBrideGhaniMalatestaAltenkirch2013]), by `IR.elimAlg` on the
codomain in the `ι`-case (`IR.InnerHom`) nested inside `IR.elimAlg` on the
domain (`IR.Hom`); the recursive `δ`-clause is stated at the
precomposed subcode `γ'^i`. The identity morphism `IR.id` — a
construction, since the paper gives no explicit one — is built through
a list-generalized pre-unit `IR.preUnitStack`, using injection helpers
(`IR.sigmaPush`, `IR.deltaEmptyPush`, `IR.msigmaPush`) and a
navigation construction (`IR.deltaNavBase`, `IR.deltaNav`) up an
iterated-precomposition tower recorded by `IR.mprecomp`.

## Main definitions

* `IR.InnerHom` — the homset from a fixed `ι`-code, by `IR.elimAlg` on
  the codomain.
* `IR.Hom` — the homset of IR codes, by `IR.elimAlg` on the domain with
  `IR.InnerHom` in the `ι`-case (Definition 8 of
  [HancockMcBrideGhaniMalatestaAltenkirch2013]).
* `IR.sigmaPush` — postcomposition with a `σ`-injection.
* `IR.deltaEmptyPush` — postcomposition with a `δ`-injection at an
  empty direction witness.
* `IR.SupObj` — a superscript object: an object
  `FreeCoprodCompDisc.{uB, uI} I` of the free coproduct completion.
* `IR.mprecomp` — iterated precomposition along a list of superscript
  objects (`IR.SupObj`).
* `IR.msigmaPush` — `IR.sigmaPush` under an iterated precomposition.
* `IR.deltaNavBase`, `IR.deltaNav` — navigation of a `Hom` up an
  iterated-precomposition tower into a `δ`-code, at a base case and
  along the tower respectively.
* `IR.preUnitStack` — the list-generalized pre-unit `Hom γ (γ ^^ L)`.
* `IR.id` — the identity morphism of an IR code, as `IR.preUnitStack`
  at the empty stack.
* `IR.SigmaPushMotive`, `IR.sigmaPushStep`,
  `IR.DeltaEmptyPushMotive`, `IR.deltaEmptyPushStep`,
  `IR.PreUnitStackMotive`, `IR.preUnitStackStep` — the named
  motives and recursor steps of the three `IR.rec`-built
  operations, at which `IR.rec_mk` applies.
* `IR.preUnitDeltaData` — the `δ`-domain pre-unit's summand datum.

## Main statements

* `IR.mprecomp_snoc` — `IR.mprecomp` at a right-appended superscript is
  one outer `IR.precomp`.
* `IR.mprecomp_iota`, `IR.mprecomp_iota_mk` — `IR.mprecomp` fixes the
  constant (`iota`) code, including any `IR.mk`-form of one.
* `IR.sigmaPush_mk_iota`, `IR.sigmaPush_mk_sigma`,
  `IR.sigmaPush_mk_delta`, `IR.deltaEmptyPush_mk_iota`,
  `IR.deltaEmptyPush_mk_sigma`, `IR.deltaEmptyPush_mk_delta`,
  `IR.preUnitStack_mk_iota`, `IR.preUnitStack_mk_sigma`,
  `IR.preUnitStack_mk_delta` — the computation equations of the
  three operations at an `IR.mk`-built domain code.

## Implementation notes

Every declaration here is at the uniform stabilized instantiation
`IR.{max uA uB, uB, uI, uO} I O`, at which `IR.precomp Q i` (for
`Q : Type uB`) is an endofunction on codes, so `IR.Hom`'s `δ`-clause
recursion stays at this instantiation and iterates.

`IR.SupObj` is definitionally the free-coproduct-completion object type
`FreeCoprodCompDisc.{uB, uI} I`; `IR.mprecomp L γ` — written `γ ^^ L` in
these notes — folds `IR.precomp` over a list of these (`List.foldl`), and its
computation lemmas are proved by `List.rec` (`IR.mprecomp_snoc` reuses
`List.foldl_concat`), keeping every recursion confined to a recursor's
internals.

`IR.preUnitStack` generalizes the identity's `Hom γ γ` goal to
`Hom γ (γ ^^ L)` for an arbitrary stack `L` of superscript objects, by
`IR.rec` on `γ`: the `δ`-case appends the mapped direction to `L`, so
the subcode induction hypothesis lands at the precomposition depth
Definition 8's clause 3 demands, and `IR.deltaNav`'s factorization
parameter `g : Bin → Bout` tracks how a peeled classifier subtype
resolves against the outer superscript as the tower is climbed.
`IR.id` specializes `IR.preUnitStack` to the empty stack.

## References

* [HancockMcBrideGhaniMalatestaAltenkirch2013] — Definition 8 for
  `IR.Hom`. The identity morphism is not given explicitly by the
  paper; `IR.id` and the injection/navigation helpers it is built
  from are this project's construction.

## Tags

inductive-recursive, morphism, homset, category
-/

@[expose] public section

universe uA uB uI uO

namespace IndRec

variable (I : Type uI) (O : Type uO)

namespace IR

/-- The homset from an `ι`-code (Definition 8, clauses 1A–1C of
[HancockMcBrideGhaniMalatestaAltenkirch2013]), by `IR.elimAlg` on the
codomain: propositional equality of indices, a dependent sum over the
`σ`-arity, and an empty-witness sum over the `δ`-arity. -/
def InnerHom (o : O) : IR.{max uA uB, uB, uI, uO} I O → Type (max uA uB uI) :=
  elimAlg I O (Type (max uA uB uI))
    ⟨fun o' => ULift.{max uA uB uI} (PLift (o = o')), fun _ dir => Σ a, dir a,
     fun B dir => Σ e : B → PEmpty.{1}, dir (fun b => (e b).elim)⟩

/-- The homset of IR codes (Definition 8 of
[HancockMcBrideGhaniMalatestaAltenkirch2013]), by `IR.elimAlg` on the
domain code with `IR.InnerHom` in the `ι` case: a product over the
`σ`-arity, and over `δ`-directions a product landing at the precomposed
codomain (clause 3's `γ'^i`). -/
def Hom : IR.{max uA uB, uB, uI, uO} I O → IR.{max uA uB, uB, uI, uO} I O
    → Type (max uA uB uI) :=
  elimAlg I O (IR.{max uA uB, uB, uI, uO} I O → Type (max uA uB uI))
    ⟨fun o => InnerHom I O o, fun _ dir => fun g' => ∀ a, dir a g',
     fun B dir => fun g' => ∀ i : B → I, dir i (precomp I O B i g')⟩

/-- The motive of `IR.sigmaPush` (named so `IR.rec_mk` applies). -/
def SigmaPushMotive (γ : IR.{max uA uB, uB, uI, uO} I O) :
    Type (max (max uA uB + 1) uI uO) :=
  ∀ (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O)
    (a' : A'), Hom I O γ (K' a') → Hom I O γ (sigma I O A' K')

/-- The step of `IR.sigmaPush` (named so `IR.rec_mk` applies). -/
def sigmaPushStep :
    RecStep.{max uA uB, uB, uI, uO, max (max uA uB + 1) uI uO} I O
      (SigmaPushMotive I O) :=
  fun s _c m => match s with
  | Sum.inl _ => fun _ _ a' f => ⟨a', f⟩
  | Sum.inr (Sum.inl _) => fun A' K' a' f b => m (ULift.up b) A' K' a' (f b)
  | Sum.inr (Sum.inr B) => fun A' K' a' f i =>
      m (ULift.up i) (ULift.{uB} A')
        (fun x => precomp I O B i (K' x.down)) (ULift.up a') (f i)

/-- Postcomposition with the `σ`-injection into the `a'`-th summand:
identity at a `σ`-code is a product of these injections. By `IR.rec` on
the domain with the target `(A', K', a')` generalized; the `δ`-domain
case reuses the injection at the superscripted `σ`-code (`precomp_sigma`
keeps `(σ A' K')^i` a `σ`-code). -/
def sigmaPush : (γ : IR.{max uA uB, uB, uI, uO} I O) →
      ∀ (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A'),
        Hom I O γ (K' a') → Hom I O γ (sigma I O A' K') :=
  rec I O (sigmaPushStep I O)

/-- The characterizing equation of `IR.sigmaPush` at an `ι`-shaped
`IR.mk`: the target data pairs with the argument. -/
theorem sigmaPush_mk_iota (o : O)
    (d : Direction I O (Sum.inl o : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O)
    (a' : A') (f : Hom.{uA, uB, uI, uO} I O (mk I O (Sum.inl o) d) (K' a')) :
    sigmaPush I O (mk I O (Sum.inl o) d) A' K' a' f = ⟨a', f⟩ :=
  congrFun (congrFun (congrFun (congrFun
    (rec_mk I O (sigmaPushStep I O) (Sum.inl o) d) A') K') a') f

/-- The characterizing equation of `IR.sigmaPush` at a `σ`-shaped
`IR.mk`: componentwise recursion. -/
theorem sigmaPush_mk_sigma (A : Type (max uA uB))
    (d : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O)
    (a' : A')
    (f : Hom.{uA, uB, uI, uO} I O (mk I O (Sum.inr (Sum.inl A)) d) (K' a')) :
    sigmaPush I O (mk I O (Sum.inr (Sum.inl A)) d) A' K' a' f =
      fun b => sigmaPush I O (d (ULift.up b)) A' K' a' (f b) :=
  congrFun (congrFun (congrFun (congrFun
    (rec_mk I O (sigmaPushStep I O) (Sum.inr (Sum.inl A)) d) A') K') a') f

/-- The characterizing equation of `IR.sigmaPush` at a `δ`-shaped
`IR.mk`: recursion at the precomposed target. -/
theorem sigmaPush_mk_delta (B : Type uB)
    (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O)
    (a' : A')
    (f : Hom.{uA, uB, uI, uO} I O (mk I O (Sum.inr (Sum.inr B)) d) (K' a')) :
    sigmaPush I O (mk I O (Sum.inr (Sum.inr B)) d) A' K' a' f =
      fun i => sigmaPush I O (d (ULift.up i)) (ULift.{uB} A')
        (fun x => precomp I O B i (K' x.down)) (ULift.up a') (f i) :=
  congrFun (congrFun (congrFun (congrFun
    (rec_mk I O (sigmaPushStep I O) (Sum.inr (Sum.inr B)) d) A') K') a') f

/-- The motive of `IR.deltaEmptyPush` (named so `IR.rec_mk` applies). -/
def DeltaEmptyPushMotive (γ : IR.{max uA uB, uB, uI, uO} I O) :
    Type (max (max uA uB + 1) uI uO) :=
  ∀ (E : Type uB) (e : E → PEmpty.{1})
    (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O),
    Hom I O γ (M (fun x => (e x).elim)) → Hom I O γ (delta I O E M)

/-- The step of `IR.deltaEmptyPush` (named so `IR.rec_mk` applies). -/
def deltaEmptyPushStep :
    RecStep.{max uA uB, uB, uI, uO, max (max uA uB + 1) uI uO} I O
      (DeltaEmptyPushMotive I O) :=
  fun s c m => match s with
  | Sum.inl _ => fun _ e _ f => ⟨e, f⟩
  | Sum.inr (Sum.inl _) => fun E e M f b => m (ULift.up b) E e M (f b)
  | Sum.inr (Sum.inr B) => fun E e M f i =>
      sigmaPush I O (c (ULift.up i)) (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
        (fun cl => delta I O {z : E // cl.down z = Sum.inr PUnit.unit}
          (fun j => precomp I O B i (M (precompMerge I B i cl.down j))))
        (ULift.up (fun x => (e x).elim))
        (m (ULift.up i) {z : E // (fun x => (e x).elim) z = Sum.inr PUnit.unit}
          (fun z => (e z.1).elim)
          (fun j => precomp I O B i (M (precompMerge I B i (fun x => (e x).elim) j)))
          (cast (congrArg
            (fun a => Hom I O (c (ULift.up i)) (precomp I O B i (M a)))
            (funext (fun x => (e x).elim) :
              (fun x => (e x).elim) = precompMerge I B i (fun x => (e x).elim)
                    (fun z : {z : E // (fun x => (e x).elim) z = Sum.inr PUnit.unit}
                      => ((e z.1).elim : PEmpty.{1}).elim)))
            (f i)))

/-- Postcomposition with the `δ`-injection at an empty direction witness
(`e : E → PEmpty`): by `IR.rec` on the domain with `(E, e, M)`
generalized; the `δ`-domain case injects, via `sigmaPush`, into the
all-resolved classifier summand of the precomposed `δ`-code. -/
def deltaEmptyPush : (γ : IR.{max uA uB, uB, uI, uO} I O) →
      ∀ (E : Type uB) (e : E → PEmpty.{1}) (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O),
        Hom I O γ (M (fun x => (e x).elim)) → Hom I O γ (delta I O E M) :=
  rec I O (deltaEmptyPushStep I O)

/-- The characterizing equation of `IR.deltaEmptyPush` at an `ι`-shaped
`IR.mk`: the empty witness pairs with the argument. -/
theorem deltaEmptyPush_mk_iota (o : O)
    (d : Direction I O (Sum.inl o : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (E : Type uB) (e : E → PEmpty.{1})
    (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
    (f : Hom.{uA, uB, uI, uO} I O (mk I O (Sum.inl o) d)
      (M (fun x => (e x).elim))) :
    deltaEmptyPush I O (mk I O (Sum.inl o) d) E e M f = ⟨e, f⟩ :=
  congrFun (congrFun (congrFun (congrFun
    (rec_mk I O (deltaEmptyPushStep I O) (Sum.inl o) d) E) e) M) f

/-- The characterizing equation of `IR.deltaEmptyPush` at a `σ`-shaped
`IR.mk`: componentwise recursion. -/
theorem deltaEmptyPush_mk_sigma (A : Type (max uA uB))
    (d : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (E : Type uB) (e : E → PEmpty.{1})
    (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
    (f : Hom.{uA, uB, uI, uO} I O (mk I O (Sum.inr (Sum.inl A)) d)
      (M (fun x => (e x).elim))) :
    deltaEmptyPush I O (mk I O (Sum.inr (Sum.inl A)) d) E e M f =
      fun b => deltaEmptyPush I O (d (ULift.up b)) E e M (f b) :=
  congrFun (congrFun (congrFun (congrFun
    (rec_mk I O (deltaEmptyPushStep I O) (Sum.inr (Sum.inl A)) d) E) e) M) f

/-- The characterizing equation of `IR.deltaEmptyPush` at a `δ`-shaped
`IR.mk`: injection through the all-resolved classifier summand of the
precomposed `δ`-code, recursing at the unresolved subtype. -/
theorem deltaEmptyPush_mk_delta (B : Type uB)
    (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (E : Type uB) (e : E → PEmpty.{1})
    (M : (E → I) → IR.{max uA uB, uB, uI, uO} I O)
    (f : Hom.{uA, uB, uI, uO} I O (mk I O (Sum.inr (Sum.inr B)) d)
      (M (fun x => (e x).elim))) :
    deltaEmptyPush I O (mk I O (Sum.inr (Sum.inr B)) d) E e M f =
      fun i => sigmaPush I O (d (ULift.up i))
        (ULift.{max uA uB} (E → B ⊕ PUnit.{uB + 1}))
        (fun cl => delta I O {z : E // cl.down z = Sum.inr PUnit.unit}
          (fun j => precomp I O B i (M (precompMerge I B i cl.down j))))
        (ULift.up (fun x => (e x).elim))
        (deltaEmptyPush I O (d (ULift.up i))
          {z : E // (fun x => (e x).elim) z = Sum.inr PUnit.unit}
          (fun z => (e z.1).elim)
          (fun j => precomp I O B i (M (precompMerge I B i (fun x => (e x).elim) j)))
          (cast (congrArg
            (fun a => Hom I O (d (ULift.up i)) (precomp I O B i (M a)))
            (funext (fun x => (e x).elim) :
              (fun x => (e x).elim) = precompMerge I B i (fun x => (e x).elim)
                    (fun z : {z : E // (fun x => (e x).elim) z = Sum.inr PUnit.unit}
                      => ((e z.1).elim : PEmpty.{1}).elim)))
            (f i))) :=
  congrFun (congrFun (congrFun (congrFun
    (rec_mk I O (deltaEmptyPushStep I O) (Sum.inr (Sum.inr B)) d) E) e) M) f

/-- Superscript objects: index types with an `I`-valued assignment
(definitionally `FreeCoprodCompDisc.{uB, uI} I`, the free-coproduct-
completion object), the index objects along which codes are
precomposed. Kept as the `Σ` form (reducibly), so `List` append in
`deltaNav`/`preUnitStack` unifies without per-site type annotations. -/
abbrev SupObj (I : Type uI) := Σ Q : Type uB, Q → I

/-- Iterated precomposition: fold `IR.precomp` over a list of superscript
objects (`γ ^^ L`). -/
def mprecomp (L : List (SupObj.{uB, uI} I)) (γ : IR.{max uA uB, uB, uI, uO} I O) :
    IR.{max uA uB, uB, uI, uO} I O :=
  L.foldl (fun g a => precomp I O a.1 a.2 g) γ

/-- `mprecomp` at a right-appended superscript is one outer `precomp`. -/
theorem mprecomp_snoc (L : List (SupObj.{uB, uI} I)) (b : SupObj.{uB, uI} I)
    (γ : IR.{max uA uB, uB, uI, uO} I O) :
    mprecomp I O (L ++ [b]) γ = precomp I O b.1 b.2 (mprecomp I O L γ) :=
  (List.foldl_concat (fun g a => precomp I O a.1 a.2 g) γ b L) ▸ rfl

/-- `mprecomp` fixes the constant (`iota`) code. -/
theorem mprecomp_iota (L : List (SupObj.{uB, uI} I)) (o : O) :
    mprecomp I O L (iota I O o) = iota I O o :=
  L.rec (motive := fun L => ∀ o, mprecomp I O L (iota I O o) = iota I O o)
    (fun _ => rfl) (fun _a _L ih o => ih o) o

/-- `mprecomp` fixes any `mk`-form of an `iota` code. -/
theorem mprecomp_iota_mk (L : List (SupObj.{uB, uI} I)) (o : O)
    (c : Direction I O (Sum.inl o) → IR.{max uA uB, uB, uI, uO} I O) :
    mprecomp I O L (mk I O (Sum.inl o) c) = iota I O o :=
  (mk_congr I O (Sum.inl o) (funext (fun x => nomatch x)) :
      mk I O (Sum.inl o) c = iota I O o) ▸ mprecomp_iota I O L o

/-- Stack `σ`-push: `sigmaPush` under an iterated precomposition. By
`List.rec` on the stack; the `cons` step peels one `precomp` layer,
reindexing the target family through `ULift`. -/
def msigmaPush (D : IR.{max uA uB, uB, uI, uO} I O) (A' : Type (max uA uB))
    (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A') (L : List (SupObj.{uB, uI} I))
    (f : Hom I O D (mprecomp I O L (K' a'))) : Hom I O D (mprecomp I O L (sigma I O A' K')) :=
  L.rec (motive := fun L => ∀ (A' : Type (max uA uB))
      (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A'),
      Hom I O D (mprecomp I O L (K' a')) → Hom I O D (mprecomp I O L (sigma I O A' K')))
    (fun A' K' a' f => sigmaPush I O D A' K' a' f)
    (fun c _L ih A' K' a' f =>
      ih (ULift.{uB} A') (fun x => precomp I O c.1 c.2 (K' x.down)) (ULift.up a') f)
    A' K' a' f

/-- The base navigation: inject a `Hom` into `precomp Bout iout (K …)`
up to `precomp Bout iout (delta Bin K)`, via the all-resolved classifier
(`Sum.inl ∘ g`) whose unresolved subtype is empty. -/
def deltaNavBase (D : IR.{max uA uB, uB, uI, uO} I O) (Bout : Type uB) (iout : Bout → I)
    (Bin : Type uB) (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout)
    (f : Hom I O D (precomp I O Bout iout (K (iout ∘ g)))) :
    Hom I O D (precomp I O Bout iout (delta I O Bin K)) :=
  sigmaPush I O D (ULift.{max uA uB} (Bin → Bout ⊕ PUnit.{uB + 1}))
    (fun cl => delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
      (fun j => precomp I O Bout iout (K (precompMerge I Bout iout cl.down j))))
    (ULift.up (fun b => Sum.inl (g b)))
    (deltaEmptyPush I O D {z : Bin // (fun b => Sum.inl (g b)) z = Sum.inr PUnit.unit}
      (fun z => nomatch z.2)
      (fun j => precomp I O Bout iout
        (K (precompMerge I Bout iout (fun b => Sum.inl (g b)) j)))
      (cast (congrArg (fun a => Hom I O D (precomp I O Bout iout (K a)))
        (funext (fun _b => rfl) :
          (iout ∘ g) = precompMerge I Bout iout (fun b => Sum.inl (g b))
                (fun z : {z : Bin // (fun b => Sum.inl (g b)) z = Sum.inr PUnit.unit}
                  => (nomatch z.2 : I)))) f))

/-- The navigation up an iterated-precomposition tower: at each stack
layer, inject through the all-unresolved classifier (`msigmaPush`),
bottoming out at `deltaNavBase`. By `List.rec` on the stack. -/
def deltaNav (D : IR.{max uA uB, uB, uI, uO} I O) (Bout : Type uB) (iout : Bout → I)
    (Bin : Type uB) (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout)
    (L : List (SupObj.{uB, uI} I))
    (f : Hom I O D
      (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (K (iout ∘ g)))) :
    Hom I O D (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I O Bin K)) :=
  L.rec (motive := fun L => ∀ (Bin : Type uB)
      (K : (Bin → I) → IR.{max uA uB, uB, uI, uO} I O) (g : Bin → Bout),
      Hom I O D (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (K (iout ∘ g))) →
      Hom I O D (mprecomp I O (L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)]) (delta I O Bin K)))
    (fun Bin K g f =>
      (mprecomp_snoc I O [] (⟨Bout, iout⟩ : SupObj.{uB, uI} I) (delta I O Bin K)).symm ▸
        deltaNavBase I O D Bout iout Bin K g
          (mprecomp_snoc I O [] (⟨Bout, iout⟩ : SupObj.{uB, uI} I) (K (iout ∘ g)) ▸ f))
    (fun a _L ih Bin K g f =>
      msigmaPush I O D (ULift.{max uA uB, uB} (Bin → a.1 ⊕ PUnit.{uB + 1}))
        (fun cl => delta I O {z : Bin // cl.down z = Sum.inr PUnit.unit}
          (fun m => precomp.{max uA uB, uB, uI, uO, uB} I O a.1 a.2
            (K (precompMerge I a.1 a.2 cl.down m))))
        (ULift.up (fun _ => Sum.inr PUnit.unit))
        (_L ++ [(⟨Bout, iout⟩ : SupObj.{uB, uI} I)])
        (ih {z : Bin // (fun _ : Bin => (Sum.inr PUnit.unit : a.1 ⊕ PUnit.{uB + 1})) z
              = Sum.inr PUnit.unit}
          (fun m => precomp.{max uA uB, uB, uI, uO, uB} I O a.1 a.2
            (K (precompMerge I a.1 a.2 (fun _ => Sum.inr PUnit.unit) m)))
          (fun z => g z.1) f))
    Bin K g f

/-- The motive of `IR.preUnitStack` (named so `IR.rec_mk` applies). -/
def PreUnitStackMotive (γ : IR.{max uA uB, uB, uI, uO} I O) :
    Type (max uA (uB + 1) uI) :=
  ∀ L : List (SupObj.{uB, uI} I), Hom.{uA, uB, uI, uO} I O γ (mprecomp I O L γ)

/-- The step of `IR.preUnitStack` (named so `IR.rec_mk` applies). -/
def preUnitStackStep :
    RecStep.{max uA uB, uB, uI, uO, max uA (uB + 1) uI} I O
      (PreUnitStackMotive I O) :=
  fun s c m => match s with
  | Sum.inl o => fun L =>
      cast (congrArg (InnerHom.{uA, uB, uI, uO} I O o)
          (mprecomp_iota_mk I O L o c).symm)
        (ULift.up (PLift.up rfl) : InnerHom.{uA, uB, uI, uO} I O o (iota I O o))
  | Sum.inr (Sum.inl A) => fun L a =>
      msigmaPush I O (c (ULift.up a)) A (fun a' => c (ULift.up a')) a L
        (m (ULift.up a) L)
  | Sum.inr (Sum.inr B) => fun L i =>
      cast (congrArg (Hom I O (c (ULift.up i)))
             (mprecomp_snoc I O L ⟨B, i⟩ (mk I O (Sum.inr (Sum.inr B)) c)))
        (deltaNav I O (c (ULift.up i)) B i B (fun i' => c (ULift.up i')) _root_.id L
          (m (ULift.up i) (L ++ [⟨B, i⟩])))

/-- The list-generalized pre-unit `Hom γ (γ ^^ L)`: by `IR.rec` on `γ`
with the stack `L` generalized. The `δ`-case appends the mapped direction
to `L`, so the subcode induction hypothesis lands at the precomposition
depth clause 3 demands, and `deltaNav` navigates the superscripted
`δ`-tower. -/
def preUnitStack : (γ : IR.{max uA uB, uB, uI, uO} I O) →
      ∀ (L : List (SupObj.{uB, uI} I)), Hom I O γ (mprecomp I O L γ) :=
  rec I O (preUnitStackStep I O)

/-- The characterizing equation of `IR.preUnitStack` at an `ι`-shaped
`IR.mk`: the transported reflexivity witness. -/
theorem preUnitStack_mk_iota (o : O)
    (d : Direction I O (Sum.inl o : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (L : List (SupObj.{uB, uI} I)) :
    preUnitStack I O (mk I O (Sum.inl o) d) L =
      cast (congrArg (InnerHom.{uA, uB, uI, uO} I O o)
          (mprecomp_iota_mk I O L o d).symm)
        (ULift.up (PLift.up rfl) : InnerHom.{uA, uB, uI, uO} I O o (iota I O o)) :=
  congrFun (rec_mk I O (preUnitStackStep I O) (Sum.inl o) d) L

/-- The characterizing equation of `IR.preUnitStack` at a `σ`-shaped
`IR.mk`: the subcode's pre-unit pushed along the stack `σ`-injection. -/
theorem preUnitStack_mk_sigma (A : Type (max uA uB))
    (d : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (L : List (SupObj.{uB, uI} I)) (a : A) :
    preUnitStack I O (mk I O (Sum.inr (Sum.inl A)) d) L a =
      msigmaPush I O (d (ULift.up a)) A (fun a' => d (ULift.up a')) a L
        (preUnitStack I O (d (ULift.up a)) L) :=
  congrFun (congrFun
    (rec_mk I O (preUnitStackStep I O) (Sum.inr (Sum.inl A)) d) L) a

/-- The `δ`-domain pre-unit's summand datum: the subcode's pre-unit at
the extended stack, navigated up the tower and transported by
`IR.mprecomp_snoc`. -/
def preUnitDeltaData (B : Type uB)
    (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (L : List (SupObj.{uB, uI} I)) (i : B → I) :
    Hom.{uA, uB, uI, uO} I O (d (ULift.up i))
      (precomp I O B i (mprecomp I O L (mk I O (Sum.inr (Sum.inr B)) d))) :=
  cast (congrArg (Hom I O (d (ULift.up i)))
      (mprecomp_snoc I O L ⟨B, i⟩ (mk I O (Sum.inr (Sum.inr B)) d)))
    (deltaNav I O (d (ULift.up i)) B i B (fun i' => d (ULift.up i')) _root_.id L
      (preUnitStack I O (d (ULift.up i)) (L ++ [⟨B, i⟩])))

/-- The characterizing equation of `IR.preUnitStack` at a `δ`-shaped
`IR.mk`: the summand datum `IR.preUnitDeltaData` at every assignment. -/
theorem preUnitStack_mk_delta (B : Type uB)
    (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (L : List (SupObj.{uB, uI} I)) (i : B → I) :
    preUnitStack I O (mk I O (Sum.inr (Sum.inr B)) d) L i =
      preUnitDeltaData I O B d L i :=
  congrFun (congrFun
    (rec_mk I O (preUnitStackStep I O) (Sum.inr (Sum.inr B)) d) L) i

/-- The identity morphism of an IR code (the paper gives no explicit
identity; this is a construction), as the pre-unit at the empty stack. -/
def id (γ : IR.{max uA uB, uB, uI, uO} I O) : Hom I O γ γ := preUnitStack I O γ []

end IR

end IndRec

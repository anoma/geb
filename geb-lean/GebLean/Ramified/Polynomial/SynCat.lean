import GebLean.Ramified.Polynomial.Interp
import GebLean.Ramified.SynCat
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# The primed syntactic category

A second realization of the generic syntactic category
(`GebLean/Ramified/SynCat.lean`) on the primed term layer `Tm'`
(`GebLean/Ramified/Polynomial/Term.lean`) and its evaluation `Tm'.eval`
(`GebLean/Ramified/Polynomial/Interp.lean`), quotiented by a `QuotRel'`. Its
objects are contexts; a morphism `Γ ⟶ Δ` is a codomain-indexed tuple of
domain terms, `∀ i, Tm' P.sig Γ (Δ.get i)`, modulo the pointwise closure of a
`QuotRel'`; identity is the variable tuple and composition is substitution.
The in-scope instantiation of the quotient relation is `interpQuotRel' P`.
The category has chosen finite products by context concatenation, so it is a
`CartesianMonoidalCategory`. This module mirrors the legacy
`GebLean.Ramified.SynCat` in full, over the primed term layer; the
sort-generic index machinery of the product layer (`finAppL`, `finAppR`,
`get_finAppL`, `get_finAppR`, `get_append_lt`, `get_append_ge`,
`finApp_cases`) is reused unchanged from the legacy module rather than
redeclared.

## Main definitions

* `HomTuple'` — raw morphism data: a codomain-indexed tuple of domain terms.
* `homSetoid'` — the pointwise closure of a `QuotRel'` on morphism tuples.
* `Hom'` — morphisms of the primed syntactic category: morphism tuples modulo
  `homSetoid'`.
* `SynCat'` — the primed syntactic category's carrier (a type synonym for
  `Ctx`).
* `SynCat'.instCategory` — the `Category` instance: `Hom'` is the tuple
  quotient, identity the variable tuple, composition substitution.
* `SynCat'.instCartesianMonoidalCategory` — chosen finite products by context
  concatenation.
* `HomTuple'.eval` — componentwise `Tm'.eval` of a morphism tuple at an
  environment.
* `Hom'.eval` — evaluation of a hom class at the standard model, the lift of
  `HomTuple'.eval` along `interpQuotRel'`.

## Main statements

* `Hom'.eval_mk` — evaluation of a class is componentwise evaluation of its
  representative.
* `Hom'.eval_comp` — evaluation respects composition (the semantic clone law
  `Tm'.eval_subst` componentwise).
* `Hom'.eval_id` — evaluation of the identity morphism is the environment.

## Implementation notes

Morphism tuples are indexed by `Fin Δ.length` and typed by `Δ.get`; the
product of contexts is their concatenation `Γ ++ Δ`, whose positions split by
`List.length_append` into the left- and right-injected positions `finAppL`,
`finAppR` (legacy `GebLean/Ramified/SynCat.lean`, sort-generic). The
projections and the pairing map reindex terms along the `List.get`-of-append
equalities `get_finAppL`, `get_finAppR` (the operation `Tm'.reind`); the
product laws follow from `Tm'.var_subst`, the commutation of substitution with
reindexing (`Tm'.subst_reind`), and reindex cancellation (`Tm'.reind_symm`).
The category and product instances live on the `Quotient` of `homSetoid'`: the
four category laws and the two projection identities hold at the level of raw
tuples (propositional equality of tuples) and reduce by the clone laws, while
pairing well-definedness and uniqueness use the `QuotRel'`'s substitution
congruence through `Quotient.sound`.

## References

The free multi-sorted Lawvere theory / term-clone conventions realized here
follow D. Leivant, "Ramified recurrence and computational complexity III:
Higher type recurrence and elementary complexity", Annals of Pure and Applied
Logic 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`, section 2.1,
transcribed by the legacy `GebLean/Ramified/SynCat.lean`. The quotient-category
assembly follows the repository precedent `GebLean.LawvereERCat`
(`GebLean/LawvereERQuot.lean`).

## Tags

ramified recurrence, syntactic category, Lawvere theory, term clone, quotient
category, cartesian monoidal category, product, context concatenation
-/

namespace GebLean.Ramified.Polynomial

open CategoryTheory CategoryTheory.Limits GebLean.Ramified

variable {S : Type}

/-- Reindexing at a propositionally equal codomain position. Mirrors the
legacy `Tm.reind_index`. -/
theorem Tm'.reind_index {sig : SortedSig S} {Γ Δ : Ctx S}
    (g : ∀ j : Fin Δ.length, Tm' sig Γ (Δ.get j)) {j j' : Fin Δ.length}
    (hj : j' = j) {b : S} (h : Δ.get j' = b) :
    Tm'.reind h (g j') = Tm'.reind (hj ▸ h) (g j) := by
  subst hj; rfl

/-- Raw morphism data of the primed syntactic category from `Γ` to `Δ`: a
tuple assigning to each position of the codomain context a primed term over
the domain context, of that position's sort. Mirrors the legacy `HomTuple`. -/
def HomTuple' (P : Presentation) (Γ Δ : Ctx P.S) : Type :=
  ∀ i : Fin Δ.length, Tm' P.sig Γ (Δ.get i)

/-- The identity tuple: the variable at each codomain position. Mirrors the
legacy `HomTuple.id`. -/
def HomTuple'.id (P : Presentation) (Γ : Ctx P.S) : HomTuple' P Γ Γ :=
  fun i => Tm'.var i

/-- The composite tuple: substitute the second tuple's terms by the first (the
slice free monad's bind). Mirrors the legacy `HomTuple.comp`. -/
def HomTuple'.comp {P : Presentation} {Γ Δ E : Ctx P.S}
    (f : HomTuple' P Γ Δ) (g : HomTuple' P Δ E) : HomTuple' P Γ E :=
  fun i => (g i).subst f

/-- The pointwise closure of a `QuotRel'` on morphism tuples: two tuples are
related when they are related position by position. The dependent-function
setoid `piSetoid` of the per-position setoids `r.rel Γ (Δ.get i)`. Mirrors
the legacy `homSetoid`. -/
def homSetoid' (P : Presentation) (r : QuotRel' P.sig) (Γ Δ : Ctx P.S) :
    Setoid (HomTuple' P Γ Δ) :=
  @piSetoid _ _ (fun i => r.rel Γ (Δ.get i))

/-- Morphisms of the primed syntactic category: morphism tuples modulo
`homSetoid'`. Mirrors the legacy `Hom`. -/
def Hom' (P : Presentation) (r : QuotRel' P.sig) (Γ Δ : Ctx P.S) : Type :=
  Quotient (homSetoid' P r Γ Δ)

/-- The identity morphism: the class of the variable tuple. Mirrors the
legacy `Hom.id`. -/
def Hom'.id (P : Presentation) (r : QuotRel' P.sig) (Γ : Ctx P.S) :
    Hom' P r Γ Γ :=
  Quotient.mk _ (HomTuple'.id P Γ)

/-- Composition of morphisms, lifted from `HomTuple'.comp`; well-defined by
the `QuotRel'`'s substitution congruence. Mirrors the legacy `Hom.comp`. -/
def Hom'.comp {P : Presentation} {r : QuotRel' P.sig} {Γ Δ E : Ctx P.S}
    (f : Hom' P r Γ Δ) (g : Hom' P r Δ E) : Hom' P r Γ E :=
  Quotient.liftOn₂ f g (fun f' g' => Quotient.mk _ (HomTuple'.comp f' g'))
    (fun f₁ g₁ f₂ g₂ hf hg => Quotient.sound
      (fun i => r.subst_congr (g₁ i) (g₂ i) f₁ f₂ (hg i) hf))

/-- Left identity law. -/
theorem Hom'.id_comp {P : Presentation} {r : QuotRel' P.sig} {Γ Δ : Ctx P.S}
    (f : Hom' P r Γ Δ) : (Hom'.id P r Γ).comp f = f := by
  induction f using Quotient.ind with
  | _ f' => exact congrArg (Quotient.mk _) (funext fun i => Tm'.subst_id (f' i))

/-- Right identity law. -/
theorem Hom'.comp_id {P : Presentation} {r : QuotRel' P.sig} {Γ Δ : Ctx P.S}
    (f : Hom' P r Γ Δ) : f.comp (Hom'.id P r Δ) = f := by
  induction f using Quotient.ind with
  | _ f' => exact congrArg (Quotient.mk _) (funext fun i => Tm'.var_subst i f')

/-- Associativity law. -/
theorem Hom'.assoc {P : Presentation} {r : QuotRel' P.sig} {Γ Δ E W : Ctx P.S}
    (f : Hom' P r Γ Δ) (g : Hom' P r Δ E) (h : Hom' P r E W) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  induction f using Quotient.ind with
  | _ f' =>
  induction g using Quotient.ind with
  | _ g' =>
  induction h using Quotient.ind with
  | _ h' =>
    exact congrArg (Quotient.mk _)
      (funext fun i => (Tm'.subst_subst (h' i) g' f').symm)

/-- Evaluate a hom-tuple at an environment of the model `M`: componentwise
`Tm'.eval`, giving a value at each codomain position. Mirrors the legacy
`HomTuple.eval`. -/
def HomTuple'.eval {P : Presentation} {Γ Δ : Ctx P.S} (f : HomTuple' P Γ Δ)
    (M : SortedModel P.sig) (ρ : M.Env Γ) : M.Env Δ :=
  fun i => (f i).eval M ρ

/-- Evaluate a hom (a `homSetoid'`-class over `interpQuotRel' P`) at the
standard model over an environment: componentwise `Tm'.eval` of any
representative. The lift is well-defined because `interpQuotRel' P` relates
two tuples exactly when their `Tm'.eval` at the standard model agree on every
environment. Mirrors the legacy `Hom.eval`. -/
def Hom'.eval {P : Presentation} {Γ Δ : Ctx P.S}
    (f : Hom' P (interpQuotRel' P) Γ Δ) (ρ : (standardModel P).Env Γ) :
    (standardModel P).Env Δ :=
  Quotient.liftOn f (fun f' => HomTuple'.eval f' (standardModel P) ρ)
    (fun _ _ h => funext (fun i => h i ρ))

/-- Evaluation of a hom class is componentwise evaluation of its representative
tuple. -/
@[simp] theorem Hom'.eval_mk {P : Presentation} {Γ Δ : Ctx P.S}
    (f : HomTuple' P Γ Δ) (ρ : (standardModel P).Env Γ) :
    Hom'.eval (Quotient.mk _ f) ρ = HomTuple'.eval f (standardModel P) ρ :=
  rfl

/-- Evaluation respects composition (`≫`, i.e. `Hom'.comp`): evaluating a
composite at an environment evaluates the second hom at the value of the
first. The semantic clone law `Tm'.eval_subst` componentwise. -/
theorem Hom'.eval_comp {P : Presentation} {Γ Δ E : Ctx P.S}
    (f : Hom' P (interpQuotRel' P) Γ Δ) (g : Hom' P (interpQuotRel' P) Δ E)
    (ρ : (standardModel P).Env Γ) :
    (f.comp g).eval ρ = g.eval (f.eval ρ) := by
  induction f using Quotient.ind with
  | _ f' =>
  induction g using Quotient.ind with
  | _ g' => exact funext (fun i => Tm'.eval_subst (standardModel P) (g' i) f' ρ)

/-- Evaluation of the identity morphism is the environment (the fold's
left-unit computation rule componentwise). Mirrors the legacy `Hom.eval_id`
(`GebLean/Ramified/Soundness/Collapse.lean`). -/
theorem Hom'.eval_id {P : Presentation} {Γ : Ctx P.S}
    (ρ : (standardModel P).Env Γ) :
    (Hom'.id P (interpQuotRel' P) Γ).eval ρ = ρ := by
  funext i
  simp only [Hom'.id, Hom'.eval_mk, HomTuple'.eval, HomTuple'.id, Tm'.eval_var]

/-- The carrier of the primed syntactic category of a presentation `P` under a
quotient relation `r`: a type synonym for `Ctx P.S` carrying the category
instance. The relation `r` is a phantom parameter: it does not occur in the
carrier but distinguishes the instances, so that the `Category` structures
for different relations do not collide. Mirrors the legacy `SynCat`. -/
@[nolint unusedArguments]
def SynCat' (P : Presentation) (_r : QuotRel' P.sig) : Type := Ctx P.S

/-- The primed syntactic category: objects are contexts, a morphism `Γ ⟶ Δ`
is a tuple of primed terms modulo `r`, identity is the variable tuple, and
composition is substitution. Mirrors the legacy `SynCat.instCategory`. -/
instance SynCat'.instCategory (P : Presentation) (r : QuotRel' P.sig) :
    Category (SynCat' P r) where
  Hom Γ Δ := Hom' P r Γ Δ
  id Γ := Hom'.id P r Γ
  comp f g := Hom'.comp f g
  id_comp f := Hom'.id_comp f
  comp_id f := Hom'.comp_id f
  assoc f g h := Hom'.assoc f g h

/-- The pairing tuple into a concatenated context: a term into `Γ` at each
left position and a term into `Δ` at each right position. Mirrors the legacy
`joinTuple`. -/
def joinTuple' {P : Presentation} {T Γ Δ : Ctx P.S}
    (f : HomTuple' P T Γ) (g : HomTuple' P T Δ) : HomTuple' P T (Γ ++ Δ) :=
  fun k =>
    if h : k.val < Γ.length then
      Tm'.reind (get_append_lt Γ Δ k h).symm (f ⟨k.val, h⟩)
    else
      Tm'.reind (get_append_ge Γ Δ k h).symm
        (g ⟨k.val - Γ.length, by
          have hk : k.val < Γ.length + Δ.length := Nat.lt_of_lt_of_eq k.isLt List.length_append
          omega⟩)

/-- The first-projection tuple: the left-injected variable at each position.
Mirrors the legacy `fstTuple`. -/
def fstTuple' (P : Presentation) (Γ Δ : Ctx P.S) : HomTuple' P (Γ ++ Δ) Γ :=
  fun i => Tm'.reind (get_finAppL Γ Δ i) (Tm'.var (finAppL Γ Δ i))

/-- The second-projection tuple: the right-injected variable at each position.
Mirrors the legacy `sndTuple`. -/
def sndTuple' (P : Presentation) (Γ Δ : Ctx P.S) : HomTuple' P (Γ ++ Δ) Δ :=
  fun j => Tm'.reind (get_finAppR Γ Δ j) (Tm'.var (finAppR Γ Δ j))

/-- The pairing tuple selects the left tuple at a left-injected position.
Mirrors the legacy `joinTuple_finAppL`. -/
theorem joinTuple'_finAppL {P : Presentation} {T Γ Δ : Ctx P.S}
    (f : HomTuple' P T Γ) (g : HomTuple' P T Δ) (i : Fin Γ.length) :
    joinTuple' f g (finAppL Γ Δ i) = Tm'.reind (get_finAppL Γ Δ i).symm (f i) := by
  have hlt : (finAppL Γ Δ i).val < Γ.length := i.isLt
  simp only [joinTuple', dif_pos hlt]
  rfl

/-- The pairing tuple selects the right tuple at a right-injected position.
Mirrors the legacy `joinTuple_finAppR`. -/
theorem joinTuple'_finAppR {P : Presentation} {T Γ Δ : Ctx P.S}
    (f : HomTuple' P T Γ) (g : HomTuple' P T Δ) (j : Fin Δ.length) :
    joinTuple' f g (finAppR Γ Δ j) = Tm'.reind (get_finAppR Γ Δ j).symm (g j) := by
  have hge : ¬ (finAppR Γ Δ j).val < Γ.length := by simp only [finAppR]; omega
  simp only [joinTuple', dif_neg hge]
  exact Tm'.reind_index g (by apply Fin.ext; simp only [finAppR]; omega) _

/-- Substituting a projection tuple by a pairing tuple recovers the paired
tuple. Mirrors the legacy `fst_join`. -/
theorem fst_join' {P : Presentation} {T Γ Δ : Ctx P.S}
    (f : HomTuple' P T Γ) (g : HomTuple' P T Δ) :
    HomTuple'.comp (joinTuple' f g) (fstTuple' P Γ Δ) = f := by
  funext i
  simp only [HomTuple'.comp, fstTuple', Tm'.subst_reind, Tm'.var_subst,
    joinTuple'_finAppL, Tm'.reind_symm']

/-- Substituting the second projection by a pairing tuple recovers the second
tuple. Mirrors the legacy `snd_join`. -/
theorem snd_join' {P : Presentation} {T Γ Δ : Ctx P.S}
    (f : HomTuple' P T Γ) (g : HomTuple' P T Δ) :
    HomTuple'.comp (joinTuple' f g) (sndTuple' P Γ Δ) = g := by
  funext j
  simp only [HomTuple'.comp, sndTuple', Tm'.subst_reind, Tm'.var_subst,
    joinTuple'_finAppR, Tm'.reind_symm']

/-- The pairing tuple respects the pointwise relation position by position.
Mirrors the legacy `joinTuple_rel`. -/
theorem joinTuple'_rel {P : Presentation} {r : QuotRel' P.sig} {T Γ Δ : Ctx P.S}
    {f f' : HomTuple' P T Γ} {g g' : HomTuple' P T Δ}
    (hf : ∀ i, (r.rel T (Γ.get i)) (f i) (f' i))
    (hg : ∀ j, (r.rel T (Δ.get j)) (g j) (g' j)) :
    ∀ k, (r.rel T ((Γ ++ Δ).get k)) (joinTuple' f g k) (joinTuple' f' g' k) := by
  refine finApp_cases (fun i => ?_) (fun j => ?_)
  · rw [joinTuple'_finAppL, joinTuple'_finAppL]
    exact r.rel_reind _ (hf i)
  · rw [joinTuple'_finAppR, joinTuple'_finAppR]
    exact r.rel_reind _ (hg j)

/-- The first projection morphism of the concatenation product. Mirrors the
legacy `SynProd.fst`. -/
def SynProd'.fst (P : Presentation) (r : QuotRel' P.sig) (Γ Δ : Ctx P.S) :
    Hom' P r (Γ ++ Δ) Γ :=
  Quotient.mk _ (fstTuple' P Γ Δ)

/-- The second projection morphism of the concatenation product. Mirrors the
legacy `SynProd.snd`. -/
def SynProd'.snd (P : Presentation) (r : QuotRel' P.sig) (Γ Δ : Ctx P.S) :
    Hom' P r (Γ ++ Δ) Δ :=
  Quotient.mk _ (sndTuple' P Γ Δ)

/-- The pairing morphism into the concatenation product; well-defined by
`joinTuple'_rel`. Mirrors the legacy `SynProd.lift`. -/
def SynProd'.lift {P : Presentation} {r : QuotRel' P.sig} {T Γ Δ : Ctx P.S}
    (f : Hom' P r T Γ) (g : Hom' P r T Δ) : Hom' P r T (Γ ++ Δ) :=
  Quotient.liftOn₂ f g (fun f' g' => Quotient.mk _ (joinTuple' f' g'))
    (fun _ _ _ _ hf hg => Quotient.sound (joinTuple'_rel hf hg))

/-- Pairing followed by the first projection recovers the first component.
Mirrors the legacy `SynProd.lift_fst`. -/
theorem SynProd'.lift_fst {P : Presentation} {r : QuotRel' P.sig} {T Γ Δ : Ctx P.S}
    (f : Hom' P r T Γ) (g : Hom' P r T Δ) :
    Hom'.comp (SynProd'.lift f g) (SynProd'.fst P r Γ Δ) = f := by
  induction f using Quotient.ind with
  | _ f' =>
  induction g using Quotient.ind with
  | _ g' => exact congrArg (Quotient.mk _) (fst_join' f' g')

/-- Pairing followed by the second projection recovers the second component.
Mirrors the legacy `SynProd.lift_snd`. -/
theorem SynProd'.lift_snd {P : Presentation} {r : QuotRel' P.sig} {T Γ Δ : Ctx P.S}
    (f : Hom' P r T Γ) (g : Hom' P r T Δ) :
    Hom'.comp (SynProd'.lift f g) (SynProd'.snd P r Γ Δ) = g := by
  induction f using Quotient.ind with
  | _ f' =>
  induction g using Quotient.ind with
  | _ g' => exact congrArg (Quotient.mk _) (snd_join' f' g')

/-- Uniqueness of the pairing morphism. Mirrors the legacy `SynProd.lift_uniq`. -/
theorem SynProd'.lift_uniq {P : Presentation} {r : QuotRel' P.sig} {T Γ Δ : Ctx P.S}
    (f : Hom' P r T Γ) (g : Hom' P r T Δ) (m : Hom' P r T (Γ ++ Δ))
    (hf : Hom'.comp m (SynProd'.fst P r Γ Δ) = f)
    (hg : Hom'.comp m (SynProd'.snd P r Γ Δ) = g) :
    m = SynProd'.lift f g := by
  induction m using Quotient.ind with
  | _ m' =>
  induction f using Quotient.ind with
  | _ f' =>
  induction g using Quotient.ind with
  | _ g' =>
    apply Quotient.sound
    have hfr := Quotient.exact hf
    have hgr := Quotient.exact hg
    refine finApp_cases (fun i => ?_) (fun j => ?_)
    · have hthis := hfr i
      simp only [HomTuple'.comp, fstTuple', Tm'.subst_reind, Tm'.var_subst] at hthis
      rw [joinTuple'_finAppL]
      have key := r.rel_reind (get_finAppL Γ Δ i).symm hthis
      rw [Tm'.reind_symm (get_finAppL Γ Δ i)] at key
      exact key
    · have hthis := hgr j
      simp only [HomTuple'.comp, sndTuple', Tm'.subst_reind, Tm'.var_subst] at hthis
      rw [joinTuple'_finAppR]
      have key := r.rel_reind (get_finAppR Γ Δ j).symm hthis
      rw [Tm'.reind_symm (get_finAppR Γ Δ j)] at key
      exact key

/-- The terminal tuple: the empty tuple into the empty context. Mirrors the
legacy `terminalTuple`. -/
def terminalTuple' (P : Presentation) (Γ : Ctx P.S) : HomTuple' P Γ [] :=
  fun i => i.elim0

/-- The terminal morphism to the empty context. Mirrors the legacy
`Hom.terminal`. -/
def Hom'.terminal (P : Presentation) (r : QuotRel' P.sig) (Γ : Ctx P.S) :
    Hom' P r Γ [] :=
  Quotient.mk _ (terminalTuple' P Γ)

/-- Every morphism to the empty context is the terminal morphism. Mirrors the
legacy `Hom.terminal_uniq`. -/
theorem Hom'.terminal_uniq {P : Presentation} {r : QuotRel' P.sig} {Γ : Ctx P.S}
    (f : Hom' P r Γ []) : f = Hom'.terminal P r Γ := by
  induction f using Quotient.ind with
  | _ f' => exact congrArg (Quotient.mk _) (funext fun i => i.elim0)

/-- The chosen terminal cone of the primed syntactic category: the empty
context. Mirrors the legacy `synTerminalCone`. -/
def synTerminalCone' (P : Presentation) (r : QuotRel' P.sig) :
    LimitCone (Functor.empty.{0} (SynCat' P r)) :=
  ⟨asEmptyCone (([] : Ctx P.S) : SynCat' P r),
   IsTerminal.ofUniqueHom (fun X => Hom'.terminal P r X)
     (fun _ f => Hom'.terminal_uniq f)⟩

/-- The chosen binary product cone of the primed syntactic category: context
concatenation. Mirrors the legacy `synProdCone`. -/
def synProdCone' (P : Presentation) (r : QuotRel' P.sig) (Γ Δ : SynCat' P r) :
    LimitCone (pair Γ Δ) :=
  ⟨BinaryFan.mk (SynProd'.fst P r Γ Δ) (SynProd'.snd P r Γ Δ),
   BinaryFan.IsLimit.mk _
     (fun f g => SynProd'.lift f g)
     (fun f g => SynProd'.lift_fst f g)
     (fun f g => SynProd'.lift_snd f g)
     (fun f g m hf hg => SynProd'.lift_uniq f g m hf hg)⟩

/-- The primed syntactic category has chosen finite products by context
concatenation, hence a cartesian monoidal structure. Mirrors the legacy
`SynCat.instCartesianMonoidalCategory`. -/
instance SynCat'.instCartesianMonoidalCategory (P : Presentation)
    (r : QuotRel' P.sig) : CartesianMonoidalCategory (SynCat' P r) :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    (synTerminalCone' P r) (synProdCone' P r)

end GebLean.Ramified.Polynomial

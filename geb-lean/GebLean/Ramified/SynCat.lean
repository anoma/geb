import GebLean.Ramified.Interp
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# The generic syntactic category

The syntactic category of a presentation, quotiented by a relation on terms.
Its objects are contexts; a morphism `Γ ⟶ Δ` is a codomain-indexed tuple of
domain terms, `∀ i, Tm P.sig Γ (Δ.get i)`, modulo the pointwise closure of a
`QuotRel`; identity is the variable tuple and composition is substitution. The
category has chosen finite products by context concatenation, so it is a
`CartesianMonoidalCategory`. The quotient relation is a parameter: the in-scope
instantiation is `interpQuotRel P` (interpretative equality at the standard
model, `GebLean/Ramified/Interp.lean`); the deferred equational workstream
re-instantiates the same construction with a derivability relation.

These definitions are novel packaging: they present the free multi-sorted
Lawvere theory of a signature — the clone of its terms, quotiented by a
congruence — through this development's polynomial-endofunctor term layer
(decision 8). The category is the term clone: composition is the free monad's
bind (`Tm.subst`), the category laws are the clone laws `Tm.subst_id`,
`Tm.subst_subst`, and the left-unit law `Tm.var_subst`
(`GebLean/Ramified/Term.lean`), and well-definedness on the quotient is the
`QuotRel`'s substitution congruence. The construction
generalizes the hand-rolled quotient categories `GebLean.LawvereERCat`
(`GebLean/LawvereERQuot.lean`) and `GebLean.LawvereKSimCat`
(`GebLean/LawvereKSimQuot.lean`) from a fixed interpretation to an arbitrary
`QuotRel`, and from natural-number arities to sorted contexts.

## Main definitions

* `HomTuple` — raw morphism data: a codomain-indexed tuple of domain terms.
* `homSetoid` — the pointwise closure of a `QuotRel` on morphism tuples.
* `Hom` — morphisms of the syntactic category: morphism tuples modulo
  `homSetoid`.
* `SynCat` — the syntactic category's carrier (a type synonym for `Ctx`).
* `SynCat.instCategory` — the `Category` instance: `Hom` is the tuple quotient,
  identity the variable tuple, composition substitution.
* `SynCat.instCartesianMonoidalCategory` — chosen finite products by context
  concatenation.

## Implementation notes

Morphism tuples are indexed by `Fin Δ.length` and typed by `Δ.get`; the product
of contexts is their concatenation `Γ ++ Δ`, whose positions split by
`List.length_append` into the left- and right-injected positions `finAppL`,
`finAppR`. The projections and the pairing map reindex terms along the
`List.get`-of-append equalities `get_finAppL`, `get_finAppR` (the operation
`Tm.reind`); the product laws follow from `Tm.var_subst`, the commutation of
substitution with reindexing (`Tm.subst_reind`), and reindex cancellation
(`Tm.reind_symm`). The category and product instances live on the `Quotient` of
`homSetoid`: the four category laws and the two projection identities hold at
the level of raw tuples (propositional equality of tuples) and reduce by the
clone laws, while pairing well-definedness and uniqueness use the `QuotRel`'s
substitution congruence through `Quotient.sound`.

## References

The free multi-sorted Lawvere theory / term-clone conventions realized here
follow D. Leivant, "Ramified recurrence and computational complexity III:
Higher type recurrence and elementary complexity", Annals of Pure and Applied
Logic 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`, section 2.1. The
quotient-category assembly follows the repository precedent
`GebLean.LawvereERCat` (`GebLean/LawvereERQuot.lean`).

Categorical/doctrinal treatment of tiered (ramified) recurrence via
height-graded multi-sorted equational theories, with complexity classes as
images of initial doctrine-categories: J. R. Otto, "Complexity Doctrines", PhD
thesis, McGill University, 1995, DOI `10.82308/7828` (§1.1 sketch theories;
Chapter 4 the Kalmar-elementary doctrines `R`/`C`/`C'` with the enough-maps /
not-too-many-maps pair). The present development differs in: (i) it formalizes
Leivant's higher-type system `RMRec-omega` (Leivant III, APAL 96 (1999)
209-229, DOI `10.1016/S0168-0072(98)00040-2`), which postdates Otto and which
Otto does not treat, his positive characterizations being first-order and his
higher-type LCC-comprehension attempt a negative result; (ii) it uses a
multi-sorted Lawvere theory with a syntactic category under interpretative
equality and a soundness functor into `LawvereERCat`, rather than set-valued
sketch models and images in `set^2`/`set^V`/`set^3`; (iii) it realizes syntax
as W-types of polynomial endofunctors, a device with no counterpart in Otto.

## Tags

ramified recurrence, syntactic category, Lawvere theory, term clone, quotient
category, cartesian monoidal category, product, context concatenation
-/

namespace GebLean.Ramified

open CategoryTheory CategoryTheory.Limits

variable {S : Type}

/-- Reindexing at a propositionally equal codomain position. -/
theorem Tm.reind_index {sig : SortedSig S} {Γ Δ : Ctx S}
    (g : ∀ j : Fin Δ.length, Tm sig Γ (Δ.get j)) {j j' : Fin Δ.length}
    (hj : j' = j) {b : S} (h : Δ.get j' = b) :
    Tm.reind h (g j') = Tm.reind (hj ▸ h) (g j) := by
  subst hj; rfl

/-- Raw morphism data of the syntactic category from `Γ` to `Δ`: a tuple
assigning to each position of the codomain context a term over the domain
context, of that position's sort. Novel packaging. -/
def HomTuple (P : Presentation) (Γ Δ : Ctx P.S) : Type :=
  ∀ i : Fin Δ.length, Tm P.sig Γ (Δ.get i)

/-- The identity tuple: the variable at each codomain position. Novel
packaging. -/
def HomTuple.id (P : Presentation) (Γ : Ctx P.S) : HomTuple P Γ Γ :=
  fun i => Tm.var i

/-- The composite tuple: substitute the second tuple's terms by the first (the
free monad's bind). Novel packaging. -/
def HomTuple.comp {P : Presentation} {Γ Δ E : Ctx P.S}
    (f : HomTuple P Γ Δ) (g : HomTuple P Δ E) : HomTuple P Γ E :=
  fun i => (g i).subst f

/-- The pointwise closure of a `QuotRel` on morphism tuples: two tuples are
related when they are related position by position. The dependent-function
setoid `piSetoid` of the per-position setoids `r.rel Γ (Δ.get i)`. Novel
packaging. -/
def homSetoid (P : Presentation) (r : QuotRel P.sig) (Γ Δ : Ctx P.S) :
    Setoid (HomTuple P Γ Δ) :=
  @piSetoid _ _ (fun i => r.rel Γ (Δ.get i))

/-- Morphisms of the syntactic category: morphism tuples modulo `homSetoid`.
Novel packaging. -/
def Hom (P : Presentation) (r : QuotRel P.sig) (Γ Δ : Ctx P.S) : Type :=
  Quotient (homSetoid P r Γ Δ)

/-- The identity morphism: the class of the variable tuple. Novel packaging. -/
def Hom.id (P : Presentation) (r : QuotRel P.sig) (Γ : Ctx P.S) :
    Hom P r Γ Γ :=
  Quotient.mk _ (HomTuple.id P Γ)

/-- Composition of morphisms, lifted from `HomTuple.comp`; well-defined by the
`QuotRel`'s substitution congruence. Novel packaging. -/
def Hom.comp {P : Presentation} {r : QuotRel P.sig} {Γ Δ E : Ctx P.S}
    (f : Hom P r Γ Δ) (g : Hom P r Δ E) : Hom P r Γ E :=
  Quotient.liftOn₂ f g (fun f' g' => Quotient.mk _ (HomTuple.comp f' g'))
    (fun f₁ g₁ f₂ g₂ hf hg => Quotient.sound
      (fun i => r.subst_congr (g₁ i) (g₂ i) f₁ f₂ (hg i) hf))

/-- Left identity law. -/
theorem Hom.id_comp {P : Presentation} {r : QuotRel P.sig} {Γ Δ : Ctx P.S}
    (f : Hom P r Γ Δ) : (Hom.id P r Γ).comp f = f := by
  induction f using Quotient.ind with
  | _ f' => exact congrArg (Quotient.mk _) (funext fun i => Tm.subst_id (f' i))

/-- Right identity law. -/
theorem Hom.comp_id {P : Presentation} {r : QuotRel P.sig} {Γ Δ : Ctx P.S}
    (f : Hom P r Γ Δ) : f.comp (Hom.id P r Δ) = f := by
  induction f using Quotient.ind with
  | _ f' => exact congrArg (Quotient.mk _) (funext fun i => Tm.var_subst i f')

/-- Associativity law. -/
theorem Hom.assoc {P : Presentation} {r : QuotRel P.sig} {Γ Δ E W : Ctx P.S}
    (f : Hom P r Γ Δ) (g : Hom P r Δ E) (h : Hom P r E W) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  induction f using Quotient.ind with
  | _ f' =>
  induction g using Quotient.ind with
  | _ g' =>
  induction h using Quotient.ind with
  | _ h' =>
    exact congrArg (Quotient.mk _)
      (funext fun i => (Tm.subst_subst (h' i) g' f').symm)

/-- The carrier of the syntactic category of a presentation `P` under a quotient
relation `r`: a type synonym for `Ctx P.S` carrying the category and product
instances. The relation `r` is a phantom parameter: it does not occur in the
carrier but distinguishes the instances, so that the `Category` and
`CartesianMonoidalCategory` structures for different relations do not collide.
Novel packaging. -/
@[nolint unusedArguments]
def SynCat (P : Presentation) (_r : QuotRel P.sig) : Type := Ctx P.S

/-- The syntactic category: objects are contexts, a morphism `Γ ⟶ Δ` is a tuple
of terms modulo `r`, identity is the variable tuple, and composition is
substitution. Novel packaging. -/
instance SynCat.instCategory (P : Presentation) (r : QuotRel P.sig) :
    Category (SynCat P r) where
  Hom Γ Δ := Hom P r Γ Δ
  id Γ := Hom.id P r Γ
  comp f g := Hom.comp f g
  id_comp f := Hom.id_comp f
  comp_id f := Hom.comp_id f
  assoc f g h := Hom.assoc f g h

/-- Left index injection into a concatenated context: the position `i` of `Γ`,
viewed as a position of `Γ ++ Δ`. The counterpart of `Fin.castAdd` for the
length of a list append; defined directly, on the underlying value with a
`List.length_append` bound, rather than through `Fin.castAdd` composed with the
`List.length_append` length cast, to avoid the intervening cast-transport
layers. Novel packaging. -/
def finAppL (Γ Δ : Ctx S) (i : Fin Γ.length) : Fin (Γ ++ Δ).length :=
  ⟨i.val, by rw [List.length_append]; omega⟩

/-- Right index injection into a concatenated context: the position `j` of `Δ`,
viewed as the position `Γ.length + j` of `Γ ++ Δ`. The counterpart of
`Fin.natAdd` for the length of a list append; defined directly, on the
underlying value with a `List.length_append` bound, rather than through
`Fin.natAdd` composed with the `List.length_append` length cast, to avoid the
intervening cast-transport layers. Novel packaging. -/
def finAppR (Γ Δ : Ctx S) (j : Fin Δ.length) : Fin (Γ ++ Δ).length :=
  ⟨Γ.length + j.val, by rw [List.length_append]; omega⟩

/-- The sort at a left-injected position is the source sort. -/
theorem get_finAppL (Γ Δ : Ctx S) (i : Fin Γ.length) :
    (Γ ++ Δ).get (finAppL Γ Δ i) = Γ.get i := by
  simp only [finAppL, List.get_eq_getElem, List.getElem_append_left i.isLt]

/-- The sort at a right-injected position is the source sort. -/
theorem get_finAppR (Γ Δ : Ctx S) (j : Fin Δ.length) :
    (Γ ++ Δ).get (finAppR Γ Δ j) = Δ.get j := by
  simp only [finAppR, List.get_eq_getElem,
    List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- The sort at a below-`Γ.length` position of `Γ ++ Δ` is a source sort. -/
theorem get_append_lt (Γ Δ : Ctx S) (k : Fin (Γ ++ Δ).length)
    (h : k.val < Γ.length) : (Γ ++ Δ).get k = Γ.get ⟨k.val, h⟩ := by
  simp only [List.get_eq_getElem, List.getElem_append_left h]

/-- The sort at an at-or-above-`Γ.length` position of `Γ ++ Δ` is a source
sort of `Δ`. -/
theorem get_append_ge (Γ Δ : Ctx S) (k : Fin (Γ ++ Δ).length)
    (h : ¬ k.val < Γ.length) :
    (Γ ++ Δ).get k
      = Δ.get ⟨k.val - Γ.length, by
        have hk : k.val < Γ.length + Δ.length := Nat.lt_of_lt_of_eq k.isLt List.length_append
        omega⟩ := by
  simp only [List.get_eq_getElem, List.getElem_append_right (Nat.le_of_not_lt h)]

/-- The pairing tuple into a concatenated context: a term into `Γ` at each
left position and a term into `Δ` at each right position. Novel packaging. -/
def joinTuple {P : Presentation} {T Γ Δ : Ctx P.S}
    (f : HomTuple P T Γ) (g : HomTuple P T Δ) : HomTuple P T (Γ ++ Δ) :=
  fun k =>
    if h : k.val < Γ.length then
      Tm.reind (get_append_lt Γ Δ k h).symm (f ⟨k.val, h⟩)
    else
      Tm.reind (get_append_ge Γ Δ k h).symm
        (g ⟨k.val - Γ.length, by
          have hk : k.val < Γ.length + Δ.length := Nat.lt_of_lt_of_eq k.isLt List.length_append
          omega⟩)

/-- The first-projection tuple: the left-injected variable at each position. -/
def fstTuple (P : Presentation) (Γ Δ : Ctx P.S) : HomTuple P (Γ ++ Δ) Γ :=
  fun i => Tm.reind (get_finAppL Γ Δ i) (Tm.var (finAppL Γ Δ i))

/-- The second-projection tuple: the right-injected variable at each position. -/
def sndTuple (P : Presentation) (Γ Δ : Ctx P.S) : HomTuple P (Γ ++ Δ) Δ :=
  fun j => Tm.reind (get_finAppR Γ Δ j) (Tm.var (finAppR Γ Δ j))

/-- The pairing tuple selects the left tuple at a left-injected position. -/
theorem joinTuple_finAppL {P : Presentation} {T Γ Δ : Ctx P.S}
    (f : HomTuple P T Γ) (g : HomTuple P T Δ) (i : Fin Γ.length) :
    joinTuple f g (finAppL Γ Δ i) = Tm.reind (get_finAppL Γ Δ i).symm (f i) := by
  have hlt : (finAppL Γ Δ i).val < Γ.length := i.isLt
  simp only [joinTuple, dif_pos hlt]
  rfl

/-- The pairing tuple selects the right tuple at a right-injected position. -/
theorem joinTuple_finAppR {P : Presentation} {T Γ Δ : Ctx P.S}
    (f : HomTuple P T Γ) (g : HomTuple P T Δ) (j : Fin Δ.length) :
    joinTuple f g (finAppR Γ Δ j) = Tm.reind (get_finAppR Γ Δ j).symm (g j) := by
  have hge : ¬ (finAppR Γ Δ j).val < Γ.length := by simp only [finAppR]; omega
  simp only [joinTuple, dif_neg hge]
  exact Tm.reind_index g (by apply Fin.ext; simp only [finAppR]; omega) _

/-- Substituting a projection tuple by a pairing tuple recovers the paired
tuple. -/
theorem fst_join {P : Presentation} {T Γ Δ : Ctx P.S}
    (f : HomTuple P T Γ) (g : HomTuple P T Δ) :
    HomTuple.comp (joinTuple f g) (fstTuple P Γ Δ) = f := by
  funext i
  simp only [HomTuple.comp, fstTuple, Tm.subst_reind, Tm.var_subst,
    joinTuple_finAppL, Tm.reind_symm']

/-- Substituting the second projection by a pairing tuple recovers the second
tuple. -/
theorem snd_join {P : Presentation} {T Γ Δ : Ctx P.S}
    (f : HomTuple P T Γ) (g : HomTuple P T Δ) :
    HomTuple.comp (joinTuple f g) (sndTuple P Γ Δ) = g := by
  funext j
  simp only [HomTuple.comp, sndTuple, Tm.subst_reind, Tm.var_subst,
    joinTuple_finAppR, Tm.reind_symm']

/-- Every position of a concatenated context is a left- or right-injected
position. The counterpart of `Fin.addCases` for the length of a list append;
proved directly against `finAppL`/`finAppR`, rather than through `Fin.addCases`
composed with the `List.length_append` length cast, to avoid the intervening
cast-transport layers. -/
theorem finApp_cases {Γ Δ : Ctx S} {motive : Fin (Γ ++ Δ).length → Prop}
    (hl : ∀ i, motive (finAppL Γ Δ i)) (hr : ∀ j, motive (finAppR Γ Δ j))
    (k : Fin (Γ ++ Δ).length) : motive k := by
  by_cases h : k.val < Γ.length
  · have hk : k = finAppL Γ Δ ⟨k.val, h⟩ := Fin.ext rfl
    rw [hk]; exact hl _
  · have hb : k.val - Γ.length < Δ.length := by
      have hk : k.val < Γ.length + Δ.length :=
        Nat.lt_of_lt_of_eq k.isLt List.length_append
      omega
    have hk : k = finAppR Γ Δ ⟨k.val - Γ.length, hb⟩ := by
      apply Fin.ext; simp only [finAppR]; omega
    rw [hk]; exact hr _

/-- The pairing tuple respects the pointwise relation position by position. -/
theorem joinTuple_rel {P : Presentation} {r : QuotRel P.sig} {T Γ Δ : Ctx P.S}
    {f f' : HomTuple P T Γ} {g g' : HomTuple P T Δ}
    (hf : ∀ i, (r.rel T (Γ.get i)) (f i) (f' i))
    (hg : ∀ j, (r.rel T (Δ.get j)) (g j) (g' j)) :
    ∀ k, (r.rel T ((Γ ++ Δ).get k)) (joinTuple f g k) (joinTuple f' g' k) := by
  refine finApp_cases (fun i => ?_) (fun j => ?_)
  · rw [joinTuple_finAppL, joinTuple_finAppL]
    exact r.rel_reind _ (hf i)
  · rw [joinTuple_finAppR, joinTuple_finAppR]
    exact r.rel_reind _ (hg j)

/-- The first projection morphism of the concatenation product. -/
def SynProd.fst (P : Presentation) (r : QuotRel P.sig) (Γ Δ : Ctx P.S) :
    Hom P r (Γ ++ Δ) Γ :=
  Quotient.mk _ (fstTuple P Γ Δ)

/-- The second projection morphism of the concatenation product. -/
def SynProd.snd (P : Presentation) (r : QuotRel P.sig) (Γ Δ : Ctx P.S) :
    Hom P r (Γ ++ Δ) Δ :=
  Quotient.mk _ (sndTuple P Γ Δ)

/-- The pairing morphism into the concatenation product; well-defined by
`joinTuple_rel`. -/
def SynProd.lift {P : Presentation} {r : QuotRel P.sig} {T Γ Δ : Ctx P.S}
    (f : Hom P r T Γ) (g : Hom P r T Δ) : Hom P r T (Γ ++ Δ) :=
  Quotient.liftOn₂ f g (fun f' g' => Quotient.mk _ (joinTuple f' g'))
    (fun _ _ _ _ hf hg => Quotient.sound (joinTuple_rel hf hg))

/-- Pairing followed by the first projection recovers the first component. -/
theorem SynProd.lift_fst {P : Presentation} {r : QuotRel P.sig} {T Γ Δ : Ctx P.S}
    (f : Hom P r T Γ) (g : Hom P r T Δ) :
    Hom.comp (SynProd.lift f g) (SynProd.fst P r Γ Δ) = f := by
  induction f using Quotient.ind with
  | _ f' =>
  induction g using Quotient.ind with
  | _ g' => exact congrArg (Quotient.mk _) (fst_join f' g')

/-- Pairing followed by the second projection recovers the second component. -/
theorem SynProd.lift_snd {P : Presentation} {r : QuotRel P.sig} {T Γ Δ : Ctx P.S}
    (f : Hom P r T Γ) (g : Hom P r T Δ) :
    Hom.comp (SynProd.lift f g) (SynProd.snd P r Γ Δ) = g := by
  induction f using Quotient.ind with
  | _ f' =>
  induction g using Quotient.ind with
  | _ g' => exact congrArg (Quotient.mk _) (snd_join f' g')

/-- Uniqueness of the pairing morphism. -/
theorem SynProd.lift_uniq {P : Presentation} {r : QuotRel P.sig} {T Γ Δ : Ctx P.S}
    (f : Hom P r T Γ) (g : Hom P r T Δ) (m : Hom P r T (Γ ++ Δ))
    (hf : Hom.comp m (SynProd.fst P r Γ Δ) = f)
    (hg : Hom.comp m (SynProd.snd P r Γ Δ) = g) :
    m = SynProd.lift f g := by
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
      simp only [HomTuple.comp, fstTuple, Tm.subst_reind, Tm.var_subst] at hthis
      rw [joinTuple_finAppL]
      have key := r.rel_reind (get_finAppL Γ Δ i).symm hthis
      rw [Tm.reind_symm (get_finAppL Γ Δ i)] at key
      exact key
    · have hthis := hgr j
      simp only [HomTuple.comp, sndTuple, Tm.subst_reind, Tm.var_subst] at hthis
      rw [joinTuple_finAppR]
      have key := r.rel_reind (get_finAppR Γ Δ j).symm hthis
      rw [Tm.reind_symm (get_finAppR Γ Δ j)] at key
      exact key

/-- The terminal tuple: the empty tuple into the empty context. -/
def terminalTuple (P : Presentation) (Γ : Ctx P.S) : HomTuple P Γ [] :=
  fun i => i.elim0

/-- The terminal morphism to the empty context. -/
def Hom.terminal (P : Presentation) (r : QuotRel P.sig) (Γ : Ctx P.S) :
    Hom P r Γ [] :=
  Quotient.mk _ (terminalTuple P Γ)

/-- Every morphism to the empty context is the terminal morphism. -/
theorem Hom.terminal_uniq {P : Presentation} {r : QuotRel P.sig} {Γ : Ctx P.S}
    (f : Hom P r Γ []) : f = Hom.terminal P r Γ := by
  induction f using Quotient.ind with
  | _ f' => exact congrArg (Quotient.mk _) (funext fun i => i.elim0)

/-- The chosen terminal cone of the syntactic category: the empty context. -/
def synTerminalCone (P : Presentation) (r : QuotRel P.sig) :
    LimitCone (Functor.empty.{0} (SynCat P r)) :=
  ⟨asEmptyCone (([] : Ctx P.S) : SynCat P r),
   IsTerminal.ofUniqueHom (fun X => Hom.terminal P r X)
     (fun _ f => Hom.terminal_uniq f)⟩

/-- The chosen binary product cone of the syntactic category: context
concatenation. -/
def synProdCone (P : Presentation) (r : QuotRel P.sig) (Γ Δ : SynCat P r) :
    LimitCone (pair Γ Δ) :=
  ⟨BinaryFan.mk (SynProd.fst P r Γ Δ) (SynProd.snd P r Γ Δ),
   BinaryFan.IsLimit.mk _
     (fun f g => SynProd.lift f g)
     (fun f g => SynProd.lift_fst f g)
     (fun f g => SynProd.lift_snd f g)
     (fun f g m hf hg => SynProd.lift_uniq f g m hf hg)⟩

/-- The syntactic category has chosen finite products by context concatenation,
hence a cartesian monoidal structure. Novel packaging. -/
instance SynCat.instCartesianMonoidalCategory (P : Presentation)
    (r : QuotRel P.sig) : CartesianMonoidalCategory (SynCat P r) :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    (synTerminalCone P r) (synProdCone P r)

end GebLean.Ramified

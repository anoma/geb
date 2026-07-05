import GebLean.Ramified.Soundness.BarRep

/-!
# The representation relation

The logical relation `Represents` tying a closed source term of the
object-sorted applicative calculus `RλMR_o^ω` (`GebLean/Ramified/Soundness/
Applicative.lean`) to a closed term of the simply-typed calculus `1λ(A)`
(`GebLean/Ramified/Soundness/OneLambda.lean`) that computes its value, following
Leivant III section 4.2 (p. 223). Defined by structural recursion on the r-type
`τ` (via `PolyFix.ind`, decision 8): at the object sorts `o` and `Ω τ'` a closed
term `Fhat` represents `F` when `Fhat` reduces to the Berarducci-Böhm value term of
`F`'s denotation, and at an arrow `σ → τ'` representation is the logical-relation
implication carrying represented arguments to represented applications.

## Main definitions

* `sourceApp` — closed-term application of the object-sorted applicative
  calculus, the empty-context specialization of `Ramified.app'`.
* `Represents` — the representation relation of Leivant III section 4.2.

## Main statements

* `lemma8` — target-reduction closure of `Represents` (Leivant III section 4.2,
  Lemma 8): a `1λ(A)` reduction may be prepended to a representative.
* `lemma9_o`, `lemma9_omega` — self-representation of a closed source term at
  the object sorts (Leivant III section 4.2, Lemma 9, weakened): a closed term
  is represented by the canonical bar-term of its own denotation.

## Implementation notes

`Represents` is a decision-2 denotational reformulation of Leivant III section
4.2's operational `Represents`: the object and `Ω` clauses anchor the source
value denotationally through `appEval` rather than by measuring a source-side
reduction, since the source side is never measured downstream and `appEval` is
total and ties to `RIdent.interp` via `prop7Translate_interp`. This is novel
packaging (an approved internal-lemma deviation), not a verbatim transcription.

The relation is `Prop`-valued, so decision 8's requirement that recursive data be
a `PolyFix` W-type does not constrain it; the `PolyFix.ind` recursion carries a
dependent motive `fun {_} (t : RType) => Tm [] t → Tm [] (barTy t) → Prop`, and
the arrow clause recurses into both children through the eliminator's induction
hypothesis. The source-side application transports `F` across the node
reconstruction `arrow_node_eq`, since a term-valued position cannot avoid the
transport the way `RType.interp` (a `Type`-valued recursion) does. The
object-clause denotations `appEval F finZeroElim` supply the empty semantic
environment at the empty context through `finZeroElim`, the dependent empty
eliminator, rather than the non-dependent `Fin.elim0`, which does not match the
dependent environment Pi.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`, section 4.2 (p. 223): the
representation of a closed term of the ramified calculus by a closed term of the
simply-typed calculus `1λ(A)`.

## Tags

ramified recurrence, logical relation, representation, simply-typed lambda
calculus, Berarducci-Böhm representation, reduction
-/

namespace GebLean.Ramified

open GebLean.Binding

/-- Closed-term application of the object-sorted applicative calculus
`RλMR_o^ω(natAlgSig)`: the empty-context specialization of `Ramified.app'`,
applying a closed function term `F : arrow σ τ'` to a closed argument term
`G : σ` to yield a closed term of sort `τ'`. Named so that the representation
relation and its downstream consumers reference the closed-term application by a
stable name. -/
def sourceApp {σ τ' : RType}
    (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow σ τ'))
    (G : Binding.Tm (rlmrOSig natAlgSig) [] σ) :
    Binding.Tm (rlmrOSig natAlgSig) [] τ' :=
  app' F G

/-- The representation relation of the bar-translation (Leivant III section 4.2,
p. 223), a decision-2 denotational reformulation: a closed source term `F` of the
object-sorted applicative calculus at r-type `τ` is represented by a closed term
`Fhat` of the simply-typed calculus `1λ(A)` at the barred type `barTy τ` when

* at the base sort `o`, `Fhat` reduces (`OneLambdaStep`, reflexive-transitively) to
  the concrete `o`-term `conc` of `F`'s denotation `appEval F finZeroElim`;
* at an object sort `Ω τ'`, `Fhat` reduces to the Berarducci-Böhm representation
  `bbRep` of `F`'s denotation at the barred sort `barTy τ'`;
* at an arrow `σ → τ'`, `Fhat` represents `F` exactly when it carries every
  represented argument to a represented application — the logical-relation
  clause, recursing into both arrow children.

Realized by the dependent eliminator `PolyFix.ind` (decision 8) with the motive
`fun {_} (t : RType) => Tm [] t → Tm [] (barTy t) → Prop`. The denotational
anchoring of the object clauses is novel packaging; see the module docstring. -/
def Represents (τ : RType) (F : Binding.Tm (rlmrOSig natAlgSig) [] τ)
    (Fhat : Binding.Tm (oneLambdaSig natAlgSig) [] (barTy τ)) : Prop :=
  PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} (t : RType) =>
      Binding.Tm (rlmrOSig natAlgSig) [] t →
        Binding.Tm (oneLambdaSig natAlgSig) [] (barTy t) → Prop)
    (fun {x} i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ =>
        fun F Fhat => Relation.ReflTransGen OneLambdaStep Fhat (conc (appEval F finZeroElim))
      | RTypeShape.arrow, childx, ih =>
        fun F Fhat =>
          ∀ (G : Binding.Tm (rlmrOSig natAlgSig) []
                (childx (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))))
            (Ghat : Binding.Tm (oneLambdaSig natAlgSig) []
                (barTy (childx (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))))),
            ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)) G Ghat →
              ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))
                (sourceApp (arrow_node_eq x childx ▸ F) G) (OneLambda.app' Fhat Ghat)
      | RTypeShape.omega, childx, _ =>
        fun F Fhat =>
          Relation.ReflTransGen OneLambdaStep Fhat
            (bbRep (appEval F finZeroElim)
              (barTy (childx (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega)))))) τ F Fhat

/-- Target-reduction closure of `Represents` (Leivant III section 4.2, Lemma 8),
a decision-2 denotational reformulation: a `1λ(A)` reduction may be prepended to a
representative. If `Fhat` represents `F` at r-type `τ` and `Fhat'` reduces to
`Fhat` (`OneLambdaStep`, reflexive-transitively), then `Fhat'` also represents `F`.

Because the source side is read only through `appEval` (decision 2), no source
metatheory is required: at the object sorts `o` and `Ω τ'` closure is target
transitivity of the reduction to the anchoring value, and at an arrow the reduction
is carried under the application spine by `OneLambda.reduces_app'_left` before the
recursion. Proved by the dependent eliminator `PolyFix.ind` (decision 8) on `τ`
with a motive quantifying over the terms, the representation, and the reduction. -/
theorem lemma8 {τ : RType} {F : Binding.Tm (rlmrOSig natAlgSig) [] τ}
    {Fhat' Fhat : Binding.Tm (oneLambdaSig natAlgSig) [] (barTy τ)}
    (h : Represents τ F Fhat)
    (hred : Relation.ReflTransGen OneLambdaStep Fhat' Fhat) :
    Represents τ F Fhat' :=
  PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} (t : RType) =>
      ∀ (F : Binding.Tm (rlmrOSig natAlgSig) [] t)
        (Fhat' Fhat : Binding.Tm (oneLambdaSig natAlgSig) [] (barTy t)),
        Represents t F Fhat →
          Relation.ReflTransGen OneLambdaStep Fhat' Fhat → Represents t F Fhat')
    (fun {x} i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => fun _ _ _ h hred => hred.trans h
      | RTypeShape.arrow, childx, ih =>
        fun F Fhat' Fhat h hred G Ghat hGG =>
          have hApp : Represents (childx (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)))
              (sourceApp (arrow_node_eq x childx ▸ F) G) (OneLambda.app' Fhat Ghat) :=
            h G Ghat hGG
          ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)) _
            (OneLambda.app' Fhat' Ghat) (OneLambda.app' Fhat Ghat) hApp
            (OneLambda.reduces_app'_left Ghat hred)
      | RTypeShape.omega, _, _ => fun _ _ _ h hred => hred.trans h) τ F Fhat' Fhat h hred

/-- Self-representation at the base object sort `o` (Leivant III section 4.2,
Lemma 9, weakened): a closed source term `F : o` is represented by the concrete
`o`-term of its own denotation, `conc (appEval F finZeroElim)`. Leivant's Lemma
9 additionally asserts that this representative is the *unique* normal `1λ(A)`
term representing `F`; under decision 2's denotational reformulation that
uniqueness content is dropped as unneeded (`Prop11` case 7 reads `F̂`'s normal
form from the `Represents` hypothesis directly, not from this lemma). What
remains is existence, and at `o` the object clause of `Represents` *is* the
statement that its target reduces to this term, so the anchor represents
itself reflexively. -/
theorem lemma9_o (F : Binding.Tm (rlmrOSig natAlgSig) [] RType.o) :
    Represents RType.o F (conc (appEval F finZeroElim)) :=
  Relation.ReflTransGen.refl

/-- Self-representation at an object sort `Ω τ'` (Leivant III section 4.2,
Lemma 9, weakened): a closed source term `F : Ω τ'` is represented by the
Berarducci-Böhm representation of its own denotation, `bbRep (appEval F
finZeroElim) (barTy τ')`. See `lemma9_o` for the dropped uniqueness content. -/
theorem lemma9_omega (τ' : RType) (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.omega τ')) :
    Represents (RType.omega τ') F (bbRep (appEval F finZeroElim) (barTy τ')) :=
  Relation.ReflTransGen.refl

/-- Two closing environments related pointwise through the representation
relation (Leivant III section 4.2, the hypothesis of Lemma 10): a source-side
environment `Eσ` substituting a closed source term for every variable of `Γ`,
and a target-side environment `Eσhat` substituting a closed `1λ(A)` term for
every barred variable of `Γ.map barTy`, such that at each variable the
substituted terms are `Represents`-related. The logical-relation environment
condition that `lemma10` carries through a substitution. -/
def RepresentsEnv {Γ : Binding.Ctx RType}
    (Eσ : Binding.Env (Binding.Tm (rlmrOSig natAlgSig)) Γ [])
    (Eσhat : Binding.Env (Binding.Tm (oneLambdaSig natAlgSig)) (Γ.map barTy) []) : Prop :=
  ∀ {s : RType} (x : Binding.Var Γ s),
    Represents s (Eσ s x) (Eσhat (barTy s) (barVar x))

/-- The variable-application fragment of the λ-free terms of the applicative
calculus `RλMR_o^ω` (Leivant III section 4.2, the terms Lemma 10 quantifies
over, as consumed by Proposition 11's recurrence case): a term built from
variables by application alone, with no λ-abstraction (`lam`), no recurrence
combinator (`recur`), and no object constant (`con`, `dstr`, `case`).

This is precisely the fragment Proposition 11's recurrence case substitutes
into. There, the Berarducci-Böhm representation `bbRep a τ̄` of a recurrence
argument's value, applied to represented step terms, reduces to the value's
constructor template `a{g⃗}` — an application spine over the bound constructor
variables, hence a variable-application term. Proposition 11's other cases
(`con^o`, `case`/`dstr`, `con^{Ωτ}`) discharge the object constants directly,
not through Lemma 10, and `recur`'s compatibility is the separate recurrence
bridge; so the object constants are absent from the terms Lemma 10 serves and
are excluded from this predicate. -/
inductive LamFree {Γ : Binding.Ctx RType} :
    {τ : RType} → Binding.Tm (rlmrOSig natAlgSig) Γ τ → Prop where
  /-- A variable is λ-free. -/
  | var {s : RType} (x : Binding.Var Γ s) : LamFree (Binding.Tm.var x)
  /-- An application of λ-free terms is λ-free. -/
  | app {σ τ : RType} {f : Binding.Tm (rlmrOSig natAlgSig) Γ (RType.arrow σ τ)}
      {x : Binding.Tm (rlmrOSig natAlgSig) Γ σ} (hf : LamFree f) (hx : LamFree x) :
      LamFree (app' f x)

end GebLean.Ramified

import GebLean.Ramified.Soundness.OneLambda

/-!
# The Berarducci-Böhm representation

The concrete `o`-term `a{c̄}` and the Berarducci-Böhm abstract representation
`a^σ` of a free-algebra value `a`, as closed terms of the simply-typed calculus
`1λ(A)` (`GebLean/Ramified/Soundness/OneLambda.lean`), following Leivant III
section 4.2 (p. 223) and the impredicative representation of algebra elements of
[6] (Berarducci-Böhm).

For a value `a` of the free algebra `FreeAlg A`, the concrete term `conc a`
folds `a`'s constructor nodes into `con`-headed application spines over
`oneLambdaSig A`, giving a closed term at the base object sort `o`. The abstract
representation `bbRep a σ` — Leivant's `a^σ` — abstracts the `k` constructor
constants of `A` into bound variables and reruns the same fold at an arbitrary
sort `σ` in place of `o`, giving a closed term at the type `Ā[σ]` (`bbType A σ`).
Over the standard word signature `natAlgSig` (`k = 2`, arities `0` and `1`),
`bbType σ` is the Church type of `σ`; a value `a` interpreted as a numeral `n`
gives the Church numeral `a^σ = λc̄. cₛ (cₛ (⋯ (c_z)))`.

## Main definitions

* `OneLambda.lamSpine` — iterated λ-abstraction of a context suffix into curried
  arrows over `oneLambdaSig`, the abstraction dual of `OneLambda.appSpine`.
* `conc` — the concrete `o`-term `a{c̄}` of a free-algebra value.
* `bbType` — the type `Ā[σ]` of the abstract representation: the constructor
  step types folded to `σ`, `RType.curried (stepTypes A σ σ) σ`.
* `ctorVar` — the bound constructor variable of `natAlgSig` at result sort `σ`,
  the variable of the abstraction context `stepTypes natAlgSig σ σ` selected by a
  constructor label.
* `bbRep` — the Berarducci-Böhm representation `a^σ = λc̄. a{c̄}`.
* `barTy` — the type bar-map `overline(·)`: `ō = o`, `overline(σ→ρ) = σ̄→ρ̄`,
  `overline(Ω τ) = bbType natAlgSig τ̄`.
* `barConOmega` — the constructor bar-map `c̄_i^{Ωτ}`, the bar image of the
  shifted constructor constant `c_i^{Ωτ}`.
* `barRecur` — the recurrence bar-map `R̄^τ = λ g⃗ a. a g⃗`, the bar image of the
  recurrence combinator `R^τ`.
* `barCase` — the case bar-map `casē^θ`, the bar image of the case combinator
  `case^θ`, splitting on `θ.IsObj` into the base `case` and its push-under-λ.

## Main statements

* `barTy_isSimple` — the type bar-map lands in the simple (omega-free) types,
  the faithfulness invariant of the bar-translation.
* `bbType_isSimple` — the Berarducci-Böhm type `bbType A σ` is simple when `σ` is.
* `RType.curried_isSimple` — a curried arrow over a context of simple types with
  a simple result sort is itself simple.

## Implementation notes

The constructor order of the abstract representation is the enumeration order
`ctorList A` reused from the recurrence machinery (`stepTypes`), not the order in
which Leivant's example prints the constructors. Over `natAlgSig` the enumeration
is zero-first (`ctorAt 0 = false`, `ctorAt 1 = true`), so `bbType σ` unfolds to
`σ → (σ→σ) → σ`, the constructor reordering of Leivant's presented Church type
`(σ→σ)→σ→σ` (p. 223). The concrete order is immaterial to correctness provided
every consumer — `conc`, `bbRep`, and the bar-maps that consume them — reuses the
same `ctorList` (the consistency contract of `ctorList`), and matching the
recurrence step order `stepTypes` is what lets the recurrence-constant bridge
apply the abstract representation to the recurrence step functions in place.

`conc` and `bbRep` run the free-algebra recurrence `FreeAlg.recurse`
(`GebLean/Ramified/AlgSig.lean`) with no parameters (`P = Unit`); the step
function ignores the subterms and threads only the recursive results, so both are
plain folds rather than paramorphisms.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`, section 4.2 (p. 223): the
concrete term `a{c̄}`, the type `Ā[σ]`, the abstract representation `a^σ`, and the
`N̄ = (o→o)→o→o` example. The abstract representation transcribes the
impredicative encoding of [6], C. Böhm and A. Berarducci, "Automatic synthesis of
typed Λ-programs on term algebras", Theoretical Computer Science 39 (1985)
135-154, DOI `10.1016/0304-3975(85)90135-5`.

## Tags

ramified recurrence, Berarducci-Böhm representation, Church encoding, free
algebra, simply-typed lambda calculus, binding signature
-/

namespace GebLean.Ramified

open GebLean.Binding

namespace OneLambda

/-- Iterated λ-abstraction of a context suffix into curried arrows over
`oneLambdaSig`: from a body in the append-at-end extension `Γ ++ Δ` at sort `τ`,
the term in `Γ` at the curried sort `RType.curried Δ τ` binding the suffix `Δ`
from the outside in. The abstraction dual of `OneLambda.appSpine`, parallel to
`Ramified.lamSpine` at `oneLambdaSig`; recursion on `Δ` peels the head sort via
`lam'`, reassociating `Γ ++ (σ :: Δ') = (Γ ++ [σ]) ++ Δ'` so the tail abstraction
sees the freshly bound variable at the end of its context. -/
def lamSpine {A : AlgSig} [Fintype A.B] {Γ : Binding.Ctx RType} :
    (Δ : List RType) → {τ : RType} →
    Binding.Tm (oneLambdaSig A) (Γ ++ Δ) τ →
    Binding.Tm (oneLambdaSig A) Γ (RType.curried Δ τ)
  | [], _τ, body =>
    cast (congrArg (fun c => Binding.Tm (oneLambdaSig A) c _) (List.append_nil Γ)) body
  | σ :: Δ', _τ, body =>
    lam' (lamSpine Δ'
      (cast (congrArg (fun c => Binding.Tm (oneLambdaSig A) c _)
        (List.append_assoc Γ [σ] Δ').symm) body))

end OneLambda

/-- The concrete `o`-term `a{c̄}` of a free-algebra value `a` (Leivant III
section 4.2, p. 223): the fold of `a`'s constructor nodes into `con`-headed
application spines over `oneLambdaSig A`, a closed term at the base object sort
`o`. Realized by the free-algebra recurrence `FreeAlg.recurse` with no
parameters, replacing each node `c_b(t₁,…,t_{r_b})` by the constructor constant
`con b` saturated with the recursive results. -/
def conc {A : AlgSig} [Fintype A.B] (a : FreeAlg A) :
    Binding.Tm (oneLambdaSig A) [] RType.o :=
  FreeAlg.recurse (A := A) (P := Unit)
    (fun b _ _sub rec =>
      OneLambda.replicateSpine (A.ar b) RType.o
        (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con b) (fun k => k.elim0)) rec)
    () a

/-- The type `Ā[σ]` of the Berarducci-Böhm representation at sort `σ` (Leivant
III section 4.2, p. 223): the constructor step types `ξ_i = σ^{r_i} → σ` folded
into the curried arrow `ξ_1, …, ξ_k → σ`, reusing the recurrence-combinator step
types `stepTypes A σ σ`. At `σ = o` these are the concrete constructor types
`o^{r_i} → o`; over `natAlgSig` the result is the Church type of `σ` (in the
enumeration order `ctorList natAlgSig`, `σ → (σ→σ) → σ`). -/
def bbType (A : AlgSig) [Fintype A.B] [LinearOrder A.B] (σ : RType) : RType :=
  RType.curried (stepTypes A σ σ) σ

/-- The bound constructor variable of `natAlgSig` at result sort `σ`: the
variable of the abstraction context `stepTypes natAlgSig σ σ` at the enumeration
position `ctorIdx b` of the constructor label `b`, whose sort is the step type
`σ^{r_b} → σ`. The abstraction-side counterpart of the recurrence step lookup
`stepAtLabel`, selecting from the bound constructor variables of `bbRep` the one
standing for `b`. -/
def ctorVar {σ : RType} (b : natAlgSig.B) :
    Binding.Var (stepTypes natAlgSig σ σ)
      (RType.curried (List.replicate (natAlgSig.ar b) σ) σ) :=
  ⟨⟨(ctorIdx b).val, by
      have hlen : (stepTypes natAlgSig σ σ).length = (ctorList natAlgSig).length := by
        rw [stepTypes, List.length_map]
      rw [hlen]; exact (ctorIdx b).isLt⟩,
    by
      simp only [stepTypes, List.get_eq_getElem, List.getElem_map]
      exact congrArg (fun c => RType.curried (List.replicate (natAlgSig.ar c) σ) σ)
        (ctorList_get_ctorIdx b)⟩

/-- The Berarducci-Böhm representation `a^σ = λc̄. a{c̄}` of a value `a` of the
standard word algebra `FreeAlg natAlgSig` (Leivant III section 4.2, p. 223; the
impredicative encoding of [6]): the concrete fold of `conc` run at sort `σ` in
place of `o`, with the constructor constants replaced by bound variables `c̄` and
those `k = A.numCtors` variables abstracted by `OneLambda.lamSpine`. A closed
term at the type `bbType natAlgSig σ`. Over `natAlgSig`, `bbRep (natToFreeAlg n)
σ` is the Church numeral `n` at `σ`. -/
def bbRep (a : FreeAlg natAlgSig) (σ : RType) :
    Binding.Tm (oneLambdaSig natAlgSig) [] (bbType natAlgSig σ) :=
  OneLambda.lamSpine (stepTypes natAlgSig σ σ)
    (FreeAlg.recurse (A := natAlgSig) (P := Unit)
      (C := Binding.Tm (oneLambdaSig natAlgSig) (stepTypes natAlgSig σ σ) σ)
      (fun b _ _sub rec =>
        OneLambda.replicateSpine (natAlgSig.ar b) σ
          (Binding.Tm.var (ctorVar b)) rec) () a)

/-- The type bar-map `overline(·)` of the bar-translation (Leivant III section
4.2, p. 223): `ō = o`, `overline(σ → ρ) = σ̄ → ρ̄`, and `overline(Ω τ) = Ω̄ τ̄ =
bbType natAlgSig τ̄`, translating each ramified type to a simple (omega-free)
type by replacing every `Ω` node with the Berarducci-Böhm type `bbType natAlgSig`
at its bar. Realized by the dependent eliminator `PolyFix.ind` (decision 8),
following `RType.interp`'s pattern. -/
def barTy (τ : RType) : RType :=
  PolyFix.ind (P := rTypeSig.polyEndo) (motive := fun {_} _ => RType)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => RType.o
      | RTypeShape.arrow, _, ih =>
        RType.arrow (ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)))
          (ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)))
      | RTypeShape.omega, _, ih =>
        bbType natAlgSig (ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega)))) τ

@[simp] theorem barTy_o : barTy RType.o = RType.o := rfl

@[simp] theorem barTy_arrow (a b : RType) :
    barTy (RType.arrow a b) = RType.arrow (barTy a) (barTy b) := rfl

@[simp] theorem barTy_omega (a : RType) :
    barTy (RType.omega a) = bbType natAlgSig (barTy a) := rfl

/-- The curried arrow sort over simple contexts is simple: if every context
sort and the result sort are omega-free, so is the folded arrow
`RType.curried Γ τ`. Internal packaging for `bbType_isSimple`, not a statement
Leivant makes directly. -/
theorem RType.curried_isSimple {Γ : List RType} {τ : RType}
    (hΓ : ∀ x ∈ Γ, x.IsSimple) (hτ : τ.IsSimple) :
    (RType.curried Γ τ).IsSimple := by
  induction Γ with
  | nil => simpa using hτ
  | cons σ Γ' ih =>
    rw [RType.curried_cons, RType.arrow_isSimple_iff]
    exact ⟨hΓ σ List.mem_cons_self,
      ih (fun x hx => hΓ x (List.mem_cons_of_mem _ hx))⟩

/-- The Berarducci-Böhm type is omega-free whenever its sort is (Leivant III
section 4.2): `bbType A σ` folds the constructor step types `σ^{r_i} → σ`, each
simple when `σ` is, so the whole curried arrow is simple. The currying step is
internal packaging (`RType.curried_isSimple`); the substance is Leivant's. -/
theorem bbType_isSimple {A : AlgSig} [Fintype A.B] [LinearOrder A.B] {σ : RType}
    (h : σ.IsSimple) : (bbType A σ).IsSimple := by
  rw [bbType]
  refine RType.curried_isSimple (fun x hx => ?_) h
  rw [stepTypes, List.mem_map] at hx
  obtain ⟨b, _, rfl⟩ := hx
  exact RType.curried_isSimple
    (fun y hy => by rw [List.eq_of_mem_replicate hy]; exact h) h

/-- The type bar-map lands in the simple (omega-free) types (Leivant III section
4.2): every `barTy τ` is simple, the faithfulness invariant of the
bar-translation into the simply-typed calculus `1λ(A)`. Each `Ω` node is
replaced by the omega-free `bbType natAlgSig` (`bbType_isSimple`), while `o` and
`arrow` preserve simplicity. -/
theorem barTy_isSimple (τ : RType) : (barTy τ).IsSimple :=
  PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} t => (barTy t).IsSimple)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => RType.o_isSimple
      | RTypeShape.arrow, _, ih =>
        RType.arrow_isSimple_iff.mpr
          ⟨ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)),
            ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))⟩
      | RTypeShape.omega, _, ih =>
        bbType_isSimple (ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega)))) τ

/-- The constructor bar-map `c̄_i^{Ωτ}` of the bar-translation (Leivant III
section 4.2, p. 223–224), the bar image of the shifted constructor constant
`c_i^{Ωτ}`: the closed `1λ(A)` term
`λ x_1…x_{r_i}. λ c_1…c_k. c_i (x_1 c⃗) … (x_{r_i} c⃗)` at the type
`(Ω̄τ)^{r_i} → Ω̄τ`, where `Ω̄τ = bbType natAlgSig τ̄` (`τ̄ = barTy τ`), each `x_j`
is a Berarducci-Böhm value of type `Ω̄τ`, the `c⃗` are the bound constructor
variables of `bbType natAlgSig τ̄` (the step types `stepTypes natAlgSig τ̄ τ̄`),
and `c_i` (via `ctorVar`) is the bound constructor for label `b`. Mirrors
`bbRep`'s constructor fold at one node, with the recursive results supplied by
the outer arguments `x⃗` applied along the `c`-spine (`appSpine`). -/
def barConOmega {Γ : Binding.Ctx RType} (b : natAlgSig.B) (τ : RType) :
    Binding.Tm (oneLambdaSig natAlgSig) Γ
      (RType.curried (List.replicate (natAlgSig.ar b) (bbType natAlgSig (barTy τ)))
        (bbType natAlgSig (barTy τ))) :=
  OneLambda.lamSpine (List.replicate (natAlgSig.ar b) (bbType natAlgSig (barTy τ)))
    (OneLambda.lamSpine (stepTypes natAlgSig (barTy τ) (barTy τ))
      (OneLambda.replicateSpine (natAlgSig.ar b) (barTy τ)
        (Binding.Tm.var (Binding.Var.appendRight
          (Γ ++ List.replicate (natAlgSig.ar b) (bbType natAlgSig (barTy τ))) (ctorVar b)))
        (fun j =>
          OneLambda.appSpine (stepTypes natAlgSig (barTy τ) (barTy τ))
            (Binding.Tm.var (Binding.Thinning.weakAppend.app
              (Binding.Var.appendRight Γ
                (⟨⟨j.val, by rw [List.length_replicate]; exact j.isLt⟩,
                  by rw [List.get_eq_getElem, List.getElem_replicate]⟩ :
                    Binding.Var (List.replicate (natAlgSig.ar b) (bbType natAlgSig (barTy τ)))
                      (bbType natAlgSig (barTy τ))))))
            (fun idx =>
              Binding.Tm.var (Binding.Var.appendRight
                (Γ ++ List.replicate (natAlgSig.ar b) (bbType natAlgSig (barTy τ)))
                ⟨idx, rfl⟩)))))

/-- The recurrence bar-map `R̄^τ` of the bar-translation (Leivant III section
4.2, p. 223–224), the bar image of the recurrence combinator `R^τ`: the closed
`1λ(A)` term `λ g_1…g_k a. a g_1…g_k` at the type `ξ̄_1, …, ξ̄_k, Ω̄τ → τ̄`, where
the `g_i` have the step types `stepTypes natAlgSig τ̄ τ̄` (`τ̄ = barTy τ`), `a` is
a Berarducci-Böhm value of type `Ω̄τ = bbType natAlgSig τ̄`, and `a g_1…g_k`
applies the Church-encoded `a` to its step arguments along the `g`-spine
(`appSpine`), yielding `τ̄`. The Berarducci-Böhm iterator: a Church value is its
own recursor. -/
def barRecur {Γ : Binding.Ctx RType} (τ : RType) :
    Binding.Tm (oneLambdaSig natAlgSig) Γ
      (RType.curried (stepTypes natAlgSig (barTy τ) (barTy τ))
        (RType.arrow (bbType natAlgSig (barTy τ)) (barTy τ))) :=
  OneLambda.lamSpine (stepTypes natAlgSig (barTy τ) (barTy τ))
    (OneLambda.lamSpine [bbType natAlgSig (barTy τ)]
      (OneLambda.appSpine (stepTypes natAlgSig (barTy τ) (barTy τ))
        (Binding.Tm.var (Binding.Var.appendRight
          (Γ ++ stepTypes natAlgSig (barTy τ) (barTy τ))
          (⟨⟨0, by simp⟩, rfl⟩ :
            Binding.Var [bbType natAlgSig (barTy τ)] (bbType natAlgSig (barTy τ)))))
        (fun idx =>
          Binding.Tm.var (Binding.Thinning.weakAppend.app
            (Binding.Var.appendRight Γ
              (⟨idx, rfl⟩ :
                Binding.Var (stepTypes natAlgSig (barTy τ) (barTy τ))
                  ((stepTypes natAlgSig (barTy τ) (barTy τ)).get idx)))))))

/-- An r-type whose top shape is `o` is the base sort `o`. Reconstruction of the
`o`-headed node, the shape-level counterpart of `RType.objTarget_of_isObj` used
to reduce the `case^o` clause of the bar-map to the base case combinator. -/
theorem RType.eq_o_of_shape_o {t : RType} (h : t.shape = RTypeShape.o) : t = RType.o := by
  rcases t with ⟨_, i, childx⟩
  simp only [RType.shape, PolyFix.index] at h
  subst h
  exact RType.mk_o_eq childx

/-- The object target of a simple (omega-free) r-type is the base sort `o`
(Leivant III section 4.2, with section 2.4): a simple type is a chain of arrows
terminating in `o`, so its rightmost object target is `o`. Proved by structural
induction via `PolyFix.ind`, the simple-type counterpart of
`RType.objTarget_of_isObj`. -/
theorem RType.objTarget_of_isSimple (t : RType) (h : RType.IsSimple t) :
    RType.objTarget t = RType.o :=
  PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} t => RType.IsSimple t → RType.objTarget t = RType.o)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => fun _ => rfl
      | RTypeShape.arrow, _, ih =>
        fun hs => ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)) hs.2
      | RTypeShape.omega, _, _ => fun hs => hs.elim) t h

/-- The case bar-map `casē^θ` of the bar-translation (Leivant III section 4.2,
p. 223–224), the bar image of the case combinator `case^θ`, split on `θ.IsObj`:

* at `θ = o` it is the base case combinator `case` of `1λ(A)`;
* at `θ = Ω τ` it is the push-under-λ term
  `λ a^o x_1…x_k^{θ̄} y⃗:σ⃗. case(a, x_1 y⃗, …, x_k y⃗)`, where `θ̄ = barTy θ = σ⃗ → o`
  (with `σ⃗ = θ̄.domains`, `o = θ̄.objTarget` by `RType.objTarget_of_isSimple`),
  each branch `x_j : θ̄` is applied along the `y`-spine (`appSpine`) to reach the
  base sort before the base `case` selects among the `k = numCtors` results.

At the higher object type the branches are functions, so the case must descend
under their argument abstractions; at `o` no descent is needed. -/
def barCase {Γ : Binding.Ctx RType} (θ : RType) (hθ : θ.IsObj) :
    Binding.Tm (oneLambdaSig natAlgSig) Γ
      (RType.arrow RType.o
        (RType.curried (List.replicate natAlgSig.numCtors (barTy θ)) (barTy θ))) := by
  cases hs : θ.shape with
  | o =>
    have hθo : θ = RType.o := RType.eq_o_of_shape_o hs
    subst hθo
    exact Binding.Tm.op (S := oneLambdaSig natAlgSig) OneLambdaOp.case (fun k => k.elim0)
  | arrow => exact absurd hθ (by unfold RType.IsObj; rw [hs]; decide)
  | omega =>
    have hobj : (barTy θ).objTarget = RType.o :=
      RType.objTarget_of_isSimple (barTy θ) (barTy_isSimple θ)
    have h_ctd : RType.curried (barTy θ).domains RType.o = barTy θ :=
      (congrArg (RType.curried (barTy θ).domains) hobj.symm).trans
        (RType.curried_domains (barTy θ)).symm
    refine OneLambda.lamSpine [RType.o]
      (OneLambda.lamSpine (List.replicate natAlgSig.numCtors (barTy θ))
        (cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig)
            ((Γ ++ [RType.o]) ++ List.replicate natAlgSig.numCtors (barTy θ))) h_ctd)
          (OneLambda.lamSpine (barTy θ).domains ?_)))
    refine OneLambda.replicateSpine natAlgSig.numCtors RType.o
      (OneLambda.app'
        (Binding.Tm.op (S := oneLambdaSig natAlgSig) OneLambdaOp.case (fun k => k.elim0))
        (Binding.Tm.var (Binding.Thinning.weakAppend.app (Binding.Thinning.weakAppend.app
          (Binding.Var.appendRight Γ
            (⟨⟨0, Nat.zero_lt_one⟩, rfl⟩ : Binding.Var [RType.o] RType.o))))))
      (fun j =>
        OneLambda.appSpine (barTy θ).domains
          (cast (congrArg (Binding.Tm (oneLambdaSig natAlgSig)
              (((Γ ++ [RType.o]) ++ List.replicate natAlgSig.numCtors (barTy θ))
                ++ (barTy θ).domains)) h_ctd.symm)
            (Binding.Tm.var (Binding.Thinning.weakAppend.app
              (Binding.Var.appendRight (Γ ++ [RType.o])
                (⟨⟨j.val, by rw [List.length_replicate]; exact j.isLt⟩,
                  by rw [List.get_eq_getElem, List.getElem_replicate]⟩ :
                    Binding.Var (List.replicate natAlgSig.numCtors (barTy θ)) (barTy θ))))))
          (fun idx =>
            Binding.Tm.var (Binding.Var.appendRight
              ((Γ ++ [RType.o]) ++ List.replicate natAlgSig.numCtors (barTy θ))
              (⟨idx, rfl⟩ :
                Binding.Var (barTy θ).domains ((barTy θ).domains.get idx)))))

end GebLean.Ramified

import GebLean.Binding.Renaming

/-!
# Capture-avoiding substitution

The substitution layer of an indexed binder-substitution kit (decision 8):
substitution is the instance of the generic binder-aware traversal
(`traverse`) at the substitution kit `subKit`, whose values are terms
themselves, embedded by the identity and weakened by renaming `ren`. The
environment helpers `idEnv`, `splitVar`, `extendEnv`, `instantiate`, and
`instantiate₁` supply the maps that Phase-6 reduction rules substitute along:
`instantiate` replaces every bound variable of an append-at-end suffix by a
term, and `instantiate₁` is its single-variable specialization (the
substitution a beta or destructor reduction performs).

## Main definitions

* `subKit` — the substitution kit: values are terms, embedded by `id` and
  weakened by `ren`.
* `sub` — substitution of a term along an environment, `traverse` at `subKit`.
* `idEnv` — the identity environment: every variable maps to itself as a term.
* `splitVar` — split a variable of `Γ ++ Ξ` into a variable of the prefix `Γ`
  or of the suffix `Ξ`.
* `extendEnv` — extend an environment on `Γ` by a meta-map on the suffix `Ξ`,
  routing each variable of `Γ ++ Ξ` through `splitVar`.
* `instantiate` — substitute the append-at-end suffix `Ξ` by a meta-map,
  leaving the prefix `Γ` fixed.
* `instantiate₁` — the single-variable specialization of `instantiate`,
  substituting the sole bound variable of `[a]` by a term `u`.

## References

The kit presentation of substitution follows G. Allais, R. Atkey, J. Chapman,
C. McBride, and J. McKinna, "A type and scope safe universe of syntaxes with
binding: their semantics and proofs", Proceedings of the ACM on Programming
Languages 2 (ICFP), 2018, DOI `10.1145/3236785`.
-/

namespace GebLean.Binding

variable {Ty : Type}

/-- The substitution kit: values are terms, read from a variable by `Tm.var`,
embedded as terms by the identity, and weakened along a thinning by renaming
`ren`. -/
def subKit (S : BinderSig Ty) : Kit S (Tm S) where
  var := Tm.var
  toTm := id
  wk := ren

/-- Substitution of a term `t` along an environment `σ`: the generic traversal
at the substitution kit `subKit`. -/
def sub {S : BinderSig Ty} {Γ Δ : Ctx Ty} {s : Ty} (σ : Env (Tm S) Γ Δ)
    (t : Tm S Γ s) : Tm S Δ s :=
  traverse (subKit S) σ t

/-- The identity environment: every variable maps to itself as a variable
term. -/
def idEnv {S : BinderSig Ty} {Γ : Ctx Ty} : Env (Tm S) Γ Γ :=
  fun _ x => Tm.var x

/-- Split a variable of the append-at-end context `Γ ++ Ξ`: a variable of the
prefix `Γ` lands in the left summand, a variable of the suffix `Ξ` in the
right, via the append-variable eliminator `Var.appendCases`. -/
def splitVar {Γ Ξ : Ctx Ty} {s : Ty} (x : Var (Γ ++ Ξ) s) : Var Γ s ⊕ Var Ξ s :=
  Var.appendCases Sum.inr Γ Sum.inl x

/-- Extend an environment `σ` on `Γ` by a meta-map `m` on the suffix `Ξ`: route
each variable of `Γ ++ Ξ` through `splitVar`, sending a `Γ`-variable through
`σ` and a `Ξ`-variable through `m`. -/
def extendEnv {S : BinderSig Ty} {Γ Δ Ξ : Ctx Ty} (σ : Env (Tm S) Γ Δ)
    (m : ∀ t, Var Ξ t → Tm S Δ t) : Env (Tm S) (Γ ++ Ξ) Δ :=
  fun s x =>
    match splitVar x with
    | Sum.inl v => σ s v
    | Sum.inr w => m s w

/-- Substitute the append-at-end suffix `Ξ` of a term by the meta-map `m`,
leaving the prefix `Γ` fixed: substitute along the environment extending the
identity on `Γ` by `m`. -/
def instantiate {S : BinderSig Ty} {Γ Ξ : Ctx Ty} {s : Ty}
    (m : ∀ t, Var Ξ t → Tm S Γ t) (t : Tm S (Γ ++ Ξ) s) : Tm S Γ s :=
  sub (extendEnv idEnv m) t

/-- The single-variable specialization of `instantiate`: substitute the sole
bound variable of the singleton suffix `[a]` by the term `u`. The meta-map
recovers the sort equality `a = b` from a variable `v : Var [a] b` — its
position is the unique element of `Fin 1`, so `[a].get v.1` reduces to `a` —
and transports `u` along it. -/
def instantiate₁ {S : BinderSig Ty} {Γ : Ctx Ty} {a s : Ty}
    (u : Tm S Γ a) (t : Tm S (Γ ++ [a]) s) : Tm S Γ s :=
  instantiate (fun b v => by
    obtain ⟨i, hi⟩ := v
    cases i using Fin.cases with
    | zero => exact hi ▸ u
    | succ j => exact j.elim0) t

/-- Assemble the meta-map of `instantiate` from an argument tuple: an indexed
tuple `args`, supplying a term of `Γ` at each position of the suffix `Ξ`, becomes
the substitution meta-map sending a suffix variable `⟨i, hi⟩ : Var Ξ t` to
`args i` transported along the position's sort equality `hi : Ξ.get i = t`. The
argument-tuple interface of `instantiate`, feeding a positionally-indexed spine
of arguments (as produced by an application spine) into the suffix
substitution. -/
def metaTuple {S : BinderSig Ty} {Γ Ξ : Ctx Ty}
    (args : ∀ i : Fin Ξ.length, Tm S Γ (Ξ.get i)) :
    ∀ t, Var Ξ t → Tm S Γ t :=
  fun _ v => v.2 ▸ args v.1

end GebLean.Binding

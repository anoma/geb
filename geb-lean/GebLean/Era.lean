/-
  Elementary Recursive Arithmetic as a logic-free equation calculus.

  Variable-ful ("Tm") presentation, per the Skolem–Curry–Goodstein tradition
  (Goodstein, "Logic-free formalisations of recursive arithmetic",
   Math. Scand. 2 (1954) 247–261; "Recursive Number Theory", 1957).

  Design decisions (from discussion):
  * Formulas are EXACTLY equations between terms (`Eqn`).  No connectives,
    no quantifiers, no propositional layer.
  * `zero`/`succ` are structural constructors of the format (the NNO data),
    NOT members of the basis `B`: they have no defining equations, and their
    meaning is given by the elimination rule `uniq` instead.
  * No `proj` constructor: variables ARE projections in this presentation.
  * One merged substitution/congruence rule (`subst`) replaces Goodstein's
    Sb1 (term-for-variable) and Sb2 (equals-for-equals); both are instances.
  * Induction is the uniqueness rule `uniq` — the uniqueness half of the
    parametrized-NNO universal property.  It consumes functions, never
    produces them; existence lives in `defs`.
  * The clone laws (left/right unit, associativity of substitution) are
    META-theorems about `Tm.subst`, proved below — they are not part of the
    object calculus.  (In the point-free `Fn` presentation they would be
    object-level axiom schemas.)

  Basis: the minimal three-element substitution basis for the Kalmár elementary
  functions E³:  { x+y, x mod y, 2ˣ }
  (M. Prunescu, L. Sauras-Altuzarra, J. M. Shunia, "A Minimal Substitution Basis
   for the Kalmár Elementary Functions", J. Logic & Computation (2026),
   arXiv:2505.23787).  Mazzanti's five operations { x+y, x∸y, x·y, ⌊x/y⌋, xʸ }
  (S. Mazzanti, "Plain Bases for Classes of Primitive Recursive Functions",
   MLQ 48:1 (2002) 93–104) are derived as terms over this basis, following the
  derivation chain x², δ, x∸y, 2xy, ⌊x/y⌋, x·y, xʸ.
  Conventions match Lean's `Nat`:  x mod 0 = x,  x ∸ y = x - y,  x / 0 = 0,
  0 ^ 0 = 1.

  Dependency-free: compiles with core Lean 4 (no Mathlib).
-/

namespace Era

universe u

/-- Cons for finite tuples (core-only stand-in for `Fin.cons`). -/
def fcons {α : Sort u} {n : Nat} (a : α) (f : Fin n → α) : Fin (n + 1) → α
  | ⟨0, _⟩     => a
  | ⟨k + 1, h⟩ => f ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- First-order terms over a basis `B` with arities `ar`, in `n` free
(de Bruijn) variables.  Note: no binders anywhere, so substitution is plain
structural recursion with no capture issues. -/
inductive Tm (B : Type) (ar : B → Nat) : Nat → Type
  | var  {n : Nat} : Fin n → Tm B ar n
  | zero {n : Nat} : Tm B ar n
  | succ {n : Nat} : Tm B ar n → Tm B ar n
  | app  {n : Nat} (b : B) : (Fin (ar b) → Tm B ar n) → Tm B ar n

/-- Simultaneous substitution.  Generalized composition `F ∘ ⟨g₀,…⟩` is the
special case; under terms-as-morphisms this IS composition in the
classifying category. -/
def Tm.subst {B : Type} {ar : B → Nat} {n m : Nat}
    (t : Tm B ar n) (σ : Fin n → Tm B ar m) : Tm B ar m :=
  match t with
  | .var i    => σ i
  | .zero     => .zero
  | .succ t   => .succ (t.subst σ)
  | .app b ts => .app b (fun i => (ts i).subst σ)

/-! ### The clone laws, as meta-theorems
Left unit `(var i).subst σ = σ i` holds definitionally.  The other two are
proved by induction on terms.  These never appear in `Derivable`. -/

theorem Tm.subst_id {B : Type} {ar : B → Nat} {n : Nat} (t : Tm B ar n) :
    t.subst .var = t := by
  induction t with
  | var i      => rfl
  | zero       => rfl
  | succ t ih  => exact congrArg Tm.succ ih
  | app b ts ih => exact congrArg (Tm.app b) (funext fun i => ih i)

theorem Tm.subst_subst {B : Type} {ar : B → Nat} {n m k : Nat}
    (t : Tm B ar n) (σ : Fin n → Tm B ar m) (τ : Fin m → Tm B ar k) :
    (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ) := by
  induction t with
  | var i      => rfl
  | zero       => rfl
  | succ t ih  => exact congrArg Tm.succ ih
  | app b ts ih => exact congrArg (Tm.app b) (funext fun i => ih i)

/-- A formula is exactly an equation between terms in a common scope. -/
structure Eqn (B : Type) (ar : B → Nat) (n : Nat) : Type where
  /-- The left-hand side. -/
  lhs : Tm B ar n
  /-- The right-hand side. -/
  rhs : Tm B ar n

/-- An axiom set: each defining equation stored at its natural scope.
For ERA this will be a *finite literal list* — the point of the finite
basis. -/
abbrev Defs (B : Type) (ar : B → Nat) := List ((n : Nat) × Eqn B ar n)

/-! ### Substitution tuples used by the uniqueness rule
Convention: in `F G : Tm B ar (n+1)`, variable 0 is the recursion variable,
variables 1..n are parameters.  In `H : Tm B ar (n+2)`, variable 0 is the
recursion variable, variable 1 the previous-value slot, variables 2..n+1 the
parameters. -/

/-- `x ↦ t`, parameters shift down: instantiates the recursion variable. -/
def sub0 {B : Type} {ar : B → Nat} {n : Nat} (t : Tm B ar n) :
    Fin (n + 1) → Tm B ar n :=
  fcons t Tm.var

/-- `x ↦ S x`, parameters fixed: the step instance. -/
def bump {B : Type} {ar : B → Nat} {n : Nat} : Fin (n + 1) → Tm B ar (n + 1) :=
  fcons (.succ (.var 0)) (fun i => .var i.succ)

/-- Arguments for `H`: `x ↦ x`, previous-value ↦ `F`, parameters fixed. -/
def recArgs {B : Type} {ar : B → Nat} {n : Nat} (F : Tm B ar (n + 1)) :
    Fin (n + 2) → Tm B ar (n + 1) :=
  fcons (.var 0) (fcons F (fun i => .var i.succ))

/-- The logic-free equation calculus.  Derivability = deductive closure:
`Derivable defs` is `Cn(defs)`, implemented as the least predicate containing
the axioms and closed under the rules. -/
inductive Derivable {B : Type} {ar : B → Nat} (defs : Defs B ar) :
    {n : Nat} → Eqn B ar n → Prop
  /-- Defining equations (for ERA: a finite list). -/
  | ax {n : Nat} {e : Eqn B ar n} : ⟨n, e⟩ ∈ defs → Derivable defs e
  /-- Reflexivity.  (Symmetry and transitivity follow from `refl`+`euclid`.) -/
  | refl {n : Nat} (t : Tm B ar n) : Derivable defs ⟨t, t⟩
  /-- Goodstein's Euclidean equality rule: things equal to the same thing
  are equal to one another. -/
  | euclid {n : Nat} {a b c : Tm B ar n} :
      Derivable defs ⟨a, b⟩ → Derivable defs ⟨a, c⟩ → Derivable defs ⟨b, c⟩
  /-- Merged substitution/congruence rule.  Goodstein's Sb1 is the instance
  `σ = σ'` (tuple part by `refl`); Sb2 is the instance `F = G` (head by
  `refl`); weakening is the instance where `σ` is a renaming. -/
  | subst {n m : Nat} {F G : Tm B ar n} {σ σ' : Fin n → Tm B ar m} :
      Derivable defs ⟨F, G⟩ → (∀ i, Derivable defs ⟨σ i, σ' i⟩) →
      Derivable defs ⟨F.subst σ, G.subst σ'⟩
  /-- Goodstein's uniqueness rule (parametrized form) — induction.
  Premises: `F` and `G` are both solutions of the recursion scheme given by
  base value `F[0]` and step `H`.  Conclusion: solutions are unique.
  This is the uniqueness half of the parametrized-NNO universal property;
  the existence half lives in `defs`. -/
  | uniq {n : Nat} {F G : Tm B ar (n + 1)} {H : Tm B ar (n + 2)} :
      Derivable defs ⟨F.subst (sub0 .zero), G.subst (sub0 .zero)⟩ →
      Derivable defs ⟨F.subst bump, H.subst (recArgs F)⟩ →
      Derivable defs ⟨G.subst bump, H.subst (recArgs G)⟩ →
      Derivable defs ⟨F, G⟩

/-! ### Derived equational rules
Symmetry and transitivity follow from `refl` and `euclid`; instantiation (Goodstein's
Sb1) and the congruences are instances of the merged `subst` rule. -/

/-- Symmetry. -/
theorem Derivable.symm {B : Type} {ar : B → Nat} {defs : Defs B ar} {n : Nat}
    {a b : Tm B ar n} (h : Derivable defs ⟨a, b⟩) : Derivable defs ⟨b, a⟩ :=
  .euclid h (.refl a)

/-- Transitivity. -/
theorem Derivable.trans {B : Type} {ar : B → Nat} {defs : Defs B ar} {n : Nat}
    {a b c : Tm B ar n} (h₁ : Derivable defs ⟨a, b⟩) (h₂ : Derivable defs ⟨b, c⟩) :
    Derivable defs ⟨a, c⟩ :=
  .euclid h₁.symm h₂

/-- Instantiation along a substitution tuple (Goodstein's Sb1). -/
theorem Derivable.inst {B : Type} {ar : B → Nat} {defs : Defs B ar} {m n : Nat}
    {F G : Tm B ar m} (σ : Fin m → Tm B ar n) (h : Derivable defs ⟨F, G⟩) :
    Derivable defs ⟨F.subst σ, G.subst σ⟩ :=
  .subst h fun _ => .refl _

/-- Congruence for the successor. -/
theorem Derivable.succ_congr {B : Type} {ar : B → Nat} {defs : Defs B ar} {n : Nat}
    {t t' : Tm B ar n} (h : Derivable defs ⟨t, t'⟩) :
    Derivable defs ⟨.succ t, .succ t'⟩ :=
  Derivable.subst (F := (.succ (.var 0) : Tm B ar 1)) (G := .succ (.var 0))
    (σ := fun _ => t) (σ' := fun _ => t') (.refl _) fun _ => h

/-- Zero/successor extensionality (Goodstein 1954 E₃): two solutions agreeing at
`0` and at every successor are equal.  Derived from `uniq` with the step
functional `(F.subst bump)` re-indexed by the renaming that skips the
previous-value slot, so that the step instance collapses to `F.subst bump` for
both `F` and `G` (the slot the two `recArgs` tuples differ in is never read). -/
theorem Derivable.ext_succ {B : Type} {ar : B → Nat} {defs : Defs B ar} {n : Nat}
    {F G : Tm B ar (n + 1)}
    (h0 : Derivable defs ⟨F.subst (sub0 .zero), G.subst (sub0 .zero)⟩)
    (hS : Derivable defs ⟨F.subst bump, G.subst bump⟩) :
    Derivable defs ⟨F, G⟩ := by
  have key : ∀ X : Tm B ar (n + 1),
      ((F.subst bump).subst
          (fcons (.var 0) (fun i => .var i.succ.succ))).subst (recArgs X) =
        F.subst bump := by
    intro X
    rw [Tm.subst_subst]
    have hvar : (fun j => ((fcons (.var 0) (fun i => .var i.succ.succ) : Fin (n + 1) →
          Tm B ar (n + 2)) j).subst (recArgs X)) = (Tm.var : Fin (n + 1) → Tm B ar (n + 1)) := by
      funext j
      match j with
      | ⟨0, _⟩ => rfl
      | ⟨_ + 1, _⟩ => rfl
    rw [hvar, Tm.subst_id]
  refine Derivable.uniq
    (H := (F.subst bump).subst (fcons (.var 0) (fun i => .var i.succ.succ))) h0 ?stepF ?stepG
  case stepF =>
    rw [key F]
    exact Derivable.refl _
  case stepG =>
    rw [key G]
    exact hS.symm

/-! ## The ERA instance: the minimal basis -/

/-- The minimal substitution basis for the Kalmár elementary functions E³:
`{ x+y, x mod y, 2ˣ }` (Prunescu–Sauras-Altuzarra–Shunia, arXiv:2505.23787). -/
inductive EraB : Type
  | add | mod | exp2
  deriving DecidableEq

/-- Arities: addition and remainder are binary; base-two exponentiation is unary. -/
def eraAr : EraB → Nat
  | .add => 2
  | .mod => 2
  | .exp2 => 1

/-- Terms over the minimal basis. -/
abbrev ETm (n : Nat) := Tm EraB eraAr n

/-- Equations over the minimal basis. -/
abbrev EEqn (n : Nat) := Eqn EraB eraAr n

/-- Apply the addition symbol to two terms. -/
def eadd {n : Nat} (s t : ETm n) : ETm n :=
  .app .add (fcons s (fcons t Fin.elim0))

/-- Apply the remainder symbol to two terms. -/
def emod {n : Nat} (s t : ETm n) : ETm n :=
  .app .mod (fcons s (fcons t Fin.elim0))

/-- Apply the base-two-exponentiation symbol to a term. -/
def eexp2 {n : Nat} (t : ETm n) : ETm n :=
  .app .exp2 (fcons t Fin.elim0)

/-- Addition. -/
infixl:65 " +ᵉ " => eadd

/-- Remainder (`x mod 0 = x`). -/
infixl:70 " %ᵉ " => emod

/-- The numeral 1. -/
def one {n : Nat} : ETm n := .succ .zero

/-- Substitution commutes with addition application (the argument tuple is a function,
so this needs `funext` + case analysis on the index). -/
theorem eadd_subst {n m : Nat} (s t : ETm n) (σ : Fin n → ETm m) :
    (s +ᵉ t).subst σ = s.subst σ +ᵉ t.subst σ :=
  congrArg (Tm.app EraB.add) (funext fun i =>
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨_ + 2, h⟩ =>
        absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h)) (Nat.not_lt_zero _))

/-- Substitution commutes with remainder application. -/
theorem emod_subst {n m : Nat} (s t : ETm n) (σ : Fin n → ETm m) :
    (s %ᵉ t).subst σ = s.subst σ %ᵉ t.subst σ :=
  congrArg (Tm.app EraB.mod) (funext fun i =>
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨_ + 2, h⟩ =>
        absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h)) (Nat.not_lt_zero _))

/-- Substitution commutes with base-two-exponentiation application. -/
theorem eexp2_subst {n m : Nat} (t : ETm n) (σ : Fin n → ETm m) :
    (eexp2 t).subst σ = eexp2 (t.subst σ) :=
  congrArg (Tm.app EraB.exp2) (funext fun i =>
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨_ + 1, h⟩ => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _))

/-! ### The seven defining equations, named
Recursion equations for addition and base-two exponentiation; for the remainder, the
divisor-zero equation, the small-dividend equation, and the divisor-subtraction
equation.  All seven are literally true of Lean's `Nat` operations (see `eraSound`
below). -/

-- addition (recursion on the 2nd argument)

/-- `x + 0 = x`. -/
def axAdd0 : (n : Nat) × EEqn n := ⟨1, ⟨(.var 0) +ᵉ .zero, .var 0⟩⟩

/-- `x + S y = S (x + y)`. -/
def axAddS : (n : Nat) × EEqn n :=
  ⟨2, ⟨(.var 0) +ᵉ .succ (.var 1), .succ ((.var 0) +ᵉ (.var 1))⟩⟩

-- remainder (x mod 0 = x)

/-- `x mod 0 = x`. -/
def axMod0 : (n : Nat) × EEqn n := ⟨1, ⟨(.var 0) %ᵉ .zero, .var 0⟩⟩

/-- `x mod (x + S y) = x`: a dividend below the divisor is its own remainder. -/
def axModLt : (n : Nat) × EEqn n :=
  ⟨2, ⟨(.var 0) %ᵉ ((.var 0) +ᵉ .succ (.var 1)), .var 0⟩⟩

/-- `(x + y) mod y = x mod y`: removing one divisor leaves the remainder. -/
def axModAdd : (n : Nat) × EEqn n :=
  ⟨2, ⟨((.var 0) +ᵉ (.var 1)) %ᵉ (.var 1), (.var 0) %ᵉ (.var 1)⟩⟩

-- base-two exponentiation

/-- `2 ^ 0 = 1`. -/
def axExp0 : (n : Nat) × EEqn n := ⟨0, ⟨eexp2 (.zero : ETm 0), one⟩⟩

/-- `2 ^ S x = 2 ^ x + 2 ^ x`. -/
def axExpS : (n : Nat) × EEqn n :=
  ⟨1, ⟨eexp2 (.succ (.var 0)), eexp2 (.var 0) +ᵉ eexp2 (.var 0)⟩⟩

/-- The axiom set of ERA: the seven defining equations, as a finite literal list. -/
def eraDefs : Defs EraB eraAr :=
  [axAdd0, axAddS, axMod0, axModLt, axModAdd, axExp0, axExpS]

/-! ## Standard semantics and soundness -/

/-- Evaluation of terms in ℕ, given an interpretation of the basis. -/
def Tm.eval {B : Type} {ar : B → Nat} (I : (b : B) → (Fin (ar b) → Nat) → Nat)
    {n : Nat} (t : Tm B ar n) (ρ : Fin n → Nat) : Nat :=
  match t with
  | .var i    => ρ i
  | .zero     => 0
  | .succ t   => (t.eval I ρ) + 1
  | .app b ts => I b (fun i => (ts i).eval I ρ)

/-- The standard interpretation of the minimal basis (Lean's `Nat` operations have
exactly the right conventions). -/
def eraInterp : (b : EraB) → (Fin (eraAr b) → Nat) → Nat
  | .add,  v => v ⟨0, by decide⟩ + v ⟨1, by decide⟩
  | .mod,  v => v ⟨0, by decide⟩ % v ⟨1, by decide⟩
  | .exp2, v => 2 ^ v ⟨0, by decide⟩

/-- Substitution-evaluation lemma (terms-as-morphisms functoriality). -/
theorem Tm.eval_subst {B : Type} {ar : B → Nat}
    (I : (b : B) → (Fin (ar b) → Nat) → Nat) {n m : Nat}
    (t : Tm B ar n) (σ : Fin n → Tm B ar m) (ρ : Fin m → Nat) :
    (t.subst σ).eval I ρ = t.eval I (fun i => (σ i).eval I ρ) := by
  induction t with
  | var i      => rfl
  | zero       => rfl
  | succ t ih  => exact congrArg (· + 1) ih
  | app b ts ih => exact congrArg (I b) (funext fun i => ih i)

/-- Eta rule for `fcons`: a tuple is its head consed onto its tail.  Stated with an
explicit `Fin.mk` head so that both match arms close by `rfl`. -/
theorem fcons_eta {α : Sort u} {n : Nat} (ρ : Fin (n + 1) → α) :
    fcons (ρ ⟨0, Nat.succ_pos n⟩) (fun i => ρ i.succ) = ρ :=
  funext fun i =>
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨_ + 1, _⟩ => rfl

/-- Evaluating the substitution tuple `sub0 t`: the recursion variable receives the value
of `t`; the parameters read the environment unchanged. -/
theorem sub0_eval {B : Type} {ar : B → Nat} (I : (b : B) → (Fin (ar b) → Nat) → Nat)
    {n : Nat} (t : Tm B ar n) (ρ : Fin n → Nat) :
    (fun i => ((sub0 t) i).eval I ρ) = fcons (t.eval I ρ) ρ :=
  funext fun i =>
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨_ + 1, _⟩ => rfl

/-- Evaluating the substitution tuple `bump` over an environment with head `k`: the
recursion variable receives `k + 1`; the parameters are unchanged. -/
theorem bump_eval {B : Type} {ar : B → Nat} (I : (b : B) → (Fin (ar b) → Nat) → Nat)
    {n : Nat} (k : Nat) (τ : Fin n → Nat) :
    (fun i => (bump (B := B) (ar := ar) i).eval I (fcons k τ)) = fcons (k + 1) τ :=
  funext fun i =>
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨_ + 1, _⟩ => rfl

/-- Evaluating the substitution tuple `recArgs F` over an environment with head `k`: the
recursion variable receives `k`, the previous-value slot receives the value of `F`, and
the parameters are unchanged. -/
theorem recArgs_eval {B : Type} {ar : B → Nat} (I : (b : B) → (Fin (ar b) → Nat) → Nat)
    {n : Nat} (F : Tm B ar (n + 1)) (k : Nat) (τ : Fin n → Nat) :
    (fun i => ((recArgs F) i).eval I (fcons k τ)) =
      fcons k (fcons (F.eval I (fcons k τ)) τ) :=
  funext fun i =>
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨_ + 2, _⟩ => rfl

/-- Soundness of the equation calculus over any interpretation of the basis that
satisfies the defining equations: every derivable equation holds under every valuation.
The `uniq` case is an inner induction on the value of the recursion variable — the
uniqueness half of `Nat.rec`'s universal property. -/
theorem Derivable.sound {B : Type} {ar : B → Nat} {defs : Defs B ar}
    (I : (b : B) → (Fin (ar b) → Nat) → Nat)
    (hdefs : ∀ d ∈ defs, ∀ ρ : Fin d.1 → Nat, d.2.lhs.eval I ρ = d.2.rhs.eval I ρ)
    {n : Nat} {e : Eqn B ar n} (h : Derivable defs e) :
    ∀ ρ : Fin n → Nat, e.lhs.eval I ρ = e.rhs.eval I ρ := by
  induction h with
  | ax hm => exact hdefs _ hm
  | refl _ => exact fun ρ => rfl
  | euclid _ _ ih1 ih2 => exact fun ρ => (ih1 ρ).symm.trans (ih2 ρ)
  | @subst ns nt F G σ σ' _ _ ihFG ihσ =>
      intro ρ
      exact (Tm.eval_subst I F σ ρ).trans ((ihFG _).trans
        ((congrArg (Tm.eval I G) (funext fun i => ihσ i ρ)).trans
          (Tm.eval_subst I G σ' ρ).symm))
  | @uniq m F G H _ _ _ ih0 ihF ihG =>
      intro ρ
      -- the two solutions agree at recursion-variable value `0`
      have base : ∀ τ : Fin m → Nat, F.eval I (fcons 0 τ) = G.eval I (fcons 0 τ) :=
        fun τ =>
          ((congrArg (Tm.eval I F) (sub0_eval I .zero τ)).symm.trans
              (Tm.eval_subst I F (sub0 .zero) τ).symm).trans
            ((ih0 τ).trans ((Tm.eval_subst I G (sub0 .zero) τ).trans
              (congrArg (Tm.eval I G) (sub0_eval I .zero τ))))
      -- a solution's value at `k + 1` is the step functional applied at `k`
      have stepEq : ∀ J : Tm B ar (m + 1),
          (∀ ρ', (J.subst bump).eval I ρ' = (H.subst (recArgs J)).eval I ρ') →
          ∀ (k : Nat) (τ : Fin m → Nat),
            J.eval I (fcons (k + 1) τ) =
              H.eval I (fcons k (fcons (J.eval I (fcons k τ)) τ)) := fun J hJ k τ =>
        ((congrArg (Tm.eval I J) (bump_eval I k τ)).symm.trans
            (Tm.eval_subst I J bump (fcons k τ)).symm).trans
          ((hJ (fcons k τ)).trans ((Tm.eval_subst I H (recArgs J) (fcons k τ)).trans
            (congrArg (Tm.eval I H) (recArgs_eval I J k τ))))
      -- inner induction on the value of the recursion variable
      have key : ∀ (k : Nat) (τ : Fin m → Nat),
          F.eval I (fcons k τ) = G.eval I (fcons k τ) := by
        intro k
        induction k with
        | zero => exact base
        | succ k ih =>
            intro τ
            exact (stepEq F ihF k τ).trans
              ((congrArg (fun v => H.eval I (fcons k (fcons v τ))) (ih τ)).trans
                (stepEq G ihG k τ).symm)
      have hkey := key (ρ ⟨0, Nat.succ_pos m⟩) (fun i => ρ i.succ)
      rwa [fcons_eta ρ] at hkey

/-- The seven defining equations hold of Lean's `Nat` operations. -/
theorem eraDefs_sound : ∀ d ∈ eraDefs, ∀ ρ : Fin d.1 → Nat,
    d.2.lhs.eval eraInterp ρ = d.2.rhs.eval eraInterp ρ := by
  simp only [eraDefs, axAdd0, axAddS, axMod0, axModLt, axModAdd, axExp0, axExpS,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  -- The addition equations are linear (`omega`); the remainder and exponentiation
  -- equations are core `Nat` facts.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      intro ρ <;> simp only [Tm.eval, eadd, emod, eexp2, one, fcons, eraInterp] <;>
    first
    | omega
    | exact Nat.mod_zero _
    | exact Nat.mod_eq_of_lt (by omega)
    | exact Nat.add_mod_right _ _
    | exact Nat.pow_zero 2
    | (rw [Nat.pow_succ]; omega)

/-- Soundness in the standard model: every derivable equation holds of Lean's `Nat`
operations under every valuation.  Instance of the generic `Derivable.sound` at the
thirteen verified identities `eraDefs_sound`. -/
theorem eraSound {n : Nat} {e : EEqn n} (h : Derivable eraDefs e)
    (ρ : Fin n → Nat) : e.lhs.eval eraInterp ρ = e.rhs.eval eraInterp ρ :=
  Derivable.sound eraInterp eraDefs_sound h ρ

/-! ## The additive flip `0 + u = u` via `uniq`.
The defining equation gives only `u + 0 = u`; the flipped identity needs
induction.  Take F := 0 + x, G := x, step functional H := S(previous), then
instantiate the recursion variable with an arbitrary term. -/

/-- `0 + u = u` (Goodstein 1954 (6)); the additive flip of `derivable_add_zero`,
by `uniq` over the recursion variable then instantiation.  The defining equation
gives only `u + 0 = u`. -/
theorem derivable_zero_add {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨(.zero : ETm n) +ᵉ u, u⟩ := by
  have base : Derivable eraDefs ⟨(.zero : ETm 1) +ᵉ .var 0, .var 0⟩ := by
    have hA0 : (⟨1, ⟨(.var 0 : ETm 1) +ᵉ .zero, .var 0⟩⟩ : (n : Nat) × EEqn n) ∈ eraDefs :=
      .head _
    have hAS : (⟨2, ⟨(.var 0 : ETm 2) +ᵉ .succ (.var 1),
                     .succ ((.var 0) +ᵉ (.var 1))⟩⟩ : (n : Nat) × EEqn n) ∈ eraDefs :=
      .tail _ (.head _)
    refine Derivable.uniq (H := .succ (.var 1)) ?base ?stepF ?stepG
    case base =>
      -- 0 + 0 = 0 — instance of axiom `x + 0 = x` under x ↦ 0
      have h := Derivable.subst (σ := fun _ => (.zero : ETm 0)) (σ' := fun _ => .zero)
        (Derivable.ax hA0) (fun _ => Derivable.refl _)
      simp only [Tm.subst, eadd_subst] at h ⊢
      exact h
    case stepF =>
      -- 0 + S x = S (0 + x) — instance of `x + S y = S (x + y)` under x ↦ 0, y ↦ x
      have h := Derivable.subst
        (σ  := fcons (.zero : ETm 1) (fcons (.var 0) Fin.elim0))
        (σ' := fcons (.zero : ETm 1) (fcons (.var 0) Fin.elim0))
        (Derivable.ax hAS) (fun _ => Derivable.refl _)
      simp only [Tm.subst, eadd_subst] at h ⊢
      exact h
    case stepG =>
      -- S x = S x
      exact Derivable.refl _
  have h := base.inst (fun _ => u)
  simp only [Tm.subst, eadd_subst] at h
  exact h

/-! ## Consistency and closed-equation completeness

Soundness yields consistency directly.  In the converse direction the calculus is
complete for closed equations: every closed term is derivably equal to the numeral of
its value, so a closed equation that holds in the standard model is derivable.  This is
the exact boundary of completeness with respect to the standard model: derivability is
recursively enumerable, while truth of equations in even one free variable is
`Π⁰₁`-complete (the terms denote all Kalmár elementary functions, which suffice to encode
bounded Turing-machine simulation), so true-but-underivable open equations exist; by
Gödel's second incompleteness theorem, an arithmetization of `eraConsistent` itself is
one. -/

/-- Consistency: the closed equation `1 = 0` is not derivable. -/
theorem eraConsistent : ¬Derivable eraDefs ⟨(one : ETm 0), .zero⟩ :=
  fun h => Nat.one_ne_zero (eraSound h Fin.elim0)

/-- The numeral `S^k 0`.  Generic in the basis: numerals use only the structural
constructors. -/
def Tm.numeral {B : Type} {ar : B → Nat} {n : Nat} : Nat → Tm B ar n
  | 0 => .zero
  | k + 1 => .succ (Tm.numeral k)

/-- An `add`-application is an `eadd` of its two components. -/
theorem app_add_eq {n : Nat} (ts : Fin (eraAr .add) → ETm n) :
    Tm.app EraB.add ts = ts ⟨0, Nat.succ_pos 1⟩ +ᵉ ts ⟨1, Nat.lt_succ_self 1⟩ :=
  congrArg (Tm.app EraB.add) (funext fun i =>
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨_ + 2, h⟩ => absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h))
        (Nat.not_lt_zero _))

/-- A `mod`-application is an `emod` of its two components. -/
theorem app_mod_eq {n : Nat} (ts : Fin (eraAr .mod) → ETm n) :
    Tm.app EraB.mod ts = ts ⟨0, Nat.succ_pos 1⟩ %ᵉ ts ⟨1, Nat.lt_succ_self 1⟩ :=
  congrArg (Tm.app EraB.mod) (funext fun i =>
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨_ + 2, h⟩ => absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h))
        (Nat.not_lt_zero _))

/-- An `exp2`-application is an `eexp2` of its component. -/
theorem app_exp2_eq {n : Nat} (ts : Fin (eraAr .exp2) → ETm n) :
    Tm.app EraB.exp2 ts = eexp2 (ts ⟨0, Nat.succ_pos 0⟩) :=
  congrArg (Tm.app EraB.exp2) (funext fun i =>
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨_ + 1, h⟩ => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _))

/-- Congruence for addition. -/
theorem eadd_congr {defs : Defs EraB eraAr} {n : Nat} {s s' t t' : ETm n}
    (hs : Derivable defs ⟨s, s'⟩) (ht : Derivable defs ⟨t, t'⟩) :
    Derivable defs ⟨s +ᵉ t, s' +ᵉ t'⟩ := by
  have h := Derivable.subst (F := ((.var 0) +ᵉ (.var 1) : ETm 2))
    (G := (.var 0) +ᵉ (.var 1))
    (σ := fcons s fun _ => t) (σ' := fcons s' fun _ => t') (.refl _) fun i =>
      match i with
      | ⟨0, _⟩ => hs
      | ⟨_ + 1, _⟩ => ht
  simp only [Tm.subst, eadd_subst] at h
  exact h

/-- Congruence for the remainder. -/
theorem emod_congr {defs : Defs EraB eraAr} {n : Nat} {s s' t t' : ETm n}
    (hs : Derivable defs ⟨s, s'⟩) (ht : Derivable defs ⟨t, t'⟩) :
    Derivable defs ⟨s %ᵉ t, s' %ᵉ t'⟩ := by
  have h := Derivable.subst (F := ((.var 0) %ᵉ (.var 1) : ETm 2))
    (G := (.var 0) %ᵉ (.var 1))
    (σ := fcons s fun _ => t) (σ' := fcons s' fun _ => t') (.refl _) fun i =>
      match i with
      | ⟨0, _⟩ => hs
      | ⟨_ + 1, _⟩ => ht
  simp only [Tm.subst, emod_subst] at h
  exact h

/-- Congruence for base-two exponentiation. -/
theorem eexp2_congr {defs : Defs EraB eraAr} {n : Nat} {t t' : ETm n}
    (h : Derivable defs ⟨t, t'⟩) : Derivable defs ⟨eexp2 t, eexp2 t'⟩ := by
  have h2 := Derivable.subst (F := (eexp2 (.var 0) : ETm 1)) (G := eexp2 (.var 0))
    (σ := fun _ => t) (σ' := fun _ => t') (.refl _) fun _ => h
  simp only [Tm.subst, eexp2_subst] at h2
  exact h2

/-- A listed defining equation, instantiated along a substitution tuple. -/
theorem derivable_def {m n : Nat} {e : EEqn m} (hax : ⟨m, e⟩ ∈ eraDefs)
    (σ : Fin m → ETm n) : Derivable eraDefs ⟨e.lhs.subst σ, e.rhs.subst σ⟩ :=
  (Derivable.ax hax).inst σ

/-- `u + 0 = u`. -/
theorem derivable_add_zero {n : Nat} (u : ETm n) : Derivable eraDefs ⟨u +ᵉ .zero, u⟩ := by
  have h := derivable_def (m := 1) (e := ⟨(.var 0) +ᵉ .zero, .var 0⟩)
    (by simp [eraDefs, axAdd0]) (fun _ => u)
  simp only [Tm.subst, eadd_subst] at h
  exact h

/-- `u + S v = S (u + v)`. -/
theorem derivable_add_succ {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨u +ᵉ .succ v, .succ (u +ᵉ v)⟩ := by
  have h := derivable_def (m := 2)
    (e := ⟨(.var 0) +ᵉ .succ (.var 1), .succ ((.var 0) +ᵉ (.var 1))⟩)
    (by simp [eraDefs, axAddS]) (fcons u fun _ => v)
  simp only [Tm.subst, eadd_subst] at h
  exact h

/-- `u mod 0 = u`. -/
theorem derivable_mod_zero {n : Nat} (u : ETm n) : Derivable eraDefs ⟨u %ᵉ .zero, u⟩ := by
  have h := derivable_def (m := 1) (e := ⟨(.var 0) %ᵉ .zero, .var 0⟩)
    (by simp [eraDefs, axMod0]) (fun _ => u)
  simp only [Tm.subst, emod_subst] at h
  exact h

/-- `u mod (u + S v) = u`. -/
theorem derivable_mod_lt {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨u %ᵉ (u +ᵉ .succ v), u⟩ := by
  have h := derivable_def (m := 2)
    (e := ⟨(.var 0) %ᵉ ((.var 0) +ᵉ .succ (.var 1)), .var 0⟩)
    (by simp [eraDefs, axModLt]) (fcons u fun _ => v)
  simp only [Tm.subst, emod_subst, eadd_subst] at h
  exact h

/-- `(u + v) mod v = u mod v`. -/
theorem derivable_mod_add {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨(u +ᵉ v) %ᵉ v, u %ᵉ v⟩ := by
  have h := derivable_def (m := 2)
    (e := ⟨((.var 0) +ᵉ (.var 1)) %ᵉ (.var 1), (.var 0) %ᵉ (.var 1)⟩)
    (by simp [eraDefs, axModAdd]) (fcons u fun _ => v)
  simp only [Tm.subst, emod_subst, eadd_subst] at h
  exact h

/-- `2 ^ 0 = 1`. -/
theorem derivable_exp2_zero {n : Nat} :
    Derivable eraDefs ⟨eexp2 (.zero : ETm n), one⟩ := by
  have h := derivable_def (m := 0) (e := ⟨eexp2 (.zero : ETm 0), one⟩)
    (by simp [eraDefs, axExp0]) (Fin.elim0 : Fin 0 → ETm n)
  simp only [Tm.subst, eexp2_subst] at h
  exact h

/-- `2 ^ S u = 2 ^ u + 2 ^ u`. -/
theorem derivable_exp2_succ {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨eexp2 (.succ u), eexp2 u +ᵉ eexp2 u⟩ := by
  have h := derivable_def (m := 1)
    (e := ⟨eexp2 (.succ (.var 0)), eexp2 (.var 0) +ᵉ eexp2 (.var 0)⟩)
    (by simp [eraDefs, axExpS]) (fun _ => u)
  simp only [Tm.subst, eexp2_subst, eadd_subst] at h
  exact h

/-! ### Numeral computation
The defining equations compute every basis operation on numerals. -/

/-- Numerals compute addition. -/
theorem numeral_add {n : Nat} (a b : Nat) :
    Derivable eraDefs ⟨(.numeral a : ETm n) +ᵉ .numeral b, .numeral (a + b)⟩ := by
  induction b with
  | zero => exact derivable_add_zero _
  | succ b ih => exact (derivable_add_succ _ _).trans (Derivable.succ_congr ih)

/-- Numerals compute base-two exponentiation. -/
theorem numeral_exp2 {n : Nat} (a : Nat) :
    Derivable eraDefs ⟨eexp2 (.numeral a : ETm n), .numeral (2 ^ a)⟩ := by
  induction a with
  | zero => exact derivable_exp2_zero
  | succ a ih =>
      rw [show (2 : Nat) ^ (a + 1) = 2 ^ a + 2 ^ a by rw [Nat.pow_succ]; omega]
      exact (derivable_exp2_succ _).trans ((eadd_congr ih ih).trans (numeral_add _ _))

/-- Numerals compute the remainder.  Recursion on the dividend: the
divisor-subtraction axiom peels one divisor from the dividend until it is small. -/
theorem numeral_mod {n : Nat} (a b : Nat) :
    Derivable eraDefs ⟨(.numeral a : ETm n) %ᵉ .numeral b, .numeral (a % b)⟩ := by
  cases b with
  | zero =>
      rw [Nat.mod_zero]
      exact derivable_mod_zero _
  | succ k =>
      cases Nat.lt_or_ge a (k + 1) with
      | inl hlt =>
          -- small dividend: `k + 1 = a + S (k - a)`, then the small-dividend axiom
          rw [Nat.mod_eq_of_lt hlt]
          have hadd := numeral_add (n := n) a (k - a + 1)
          rw [show a + (k - a + 1) = k + 1 by omega] at hadd
          exact (emod_congr (.refl _) hadd.symm).trans (derivable_mod_lt _ _)
      | inr hge =>
          -- large dividend: peel one divisor and recurse on `a - (k + 1)`
          have hadd := numeral_add (n := n) (a - (k + 1)) (k + 1)
          rw [show a - (k + 1) + (k + 1) = a by omega] at hadd
          have hrec := numeral_mod (n := n) (a - (k + 1)) (k + 1)
          have hmod := Nat.add_mod_right (a - (k + 1)) (k + 1)
          rw [show a - (k + 1) + (k + 1) = a by omega] at hmod
          rw [hmod]
          exact (emod_congr hadd.symm (.refl _)).trans
            ((derivable_mod_add _ _).trans hrec)
  termination_by a
  decreasing_by omega

/-- Numeral normalization: every closed term is derivably equal to the numeral of its
value. -/
theorem closed_term_numeral (t : ETm 0) :
    Derivable eraDefs ⟨t, .numeral (t.eval eraInterp Fin.elim0)⟩ := by
  induction t with
  | var i => exact i.elim0
  | zero => exact .refl _
  | succ t ih => exact Derivable.succ_congr ih
  | app b ts ih =>
      cases b with
      | add =>
          rw [app_add_eq ts]
          exact (eadd_congr (ih _) (ih _)).trans (numeral_add _ _)
      | mod =>
          rw [app_mod_eq ts]
          exact (emod_congr (ih _) (ih _)).trans (numeral_mod _ _)
      | exp2 =>
          rw [app_exp2_eq ts]
          exact (eexp2_congr (ih _)).trans (numeral_exp2 _)

/-- Completeness for closed equations: a closed equation that holds in the standard
model is derivable.  With `eraSound`, derivability of a closed equation coincides with
its truth in the standard model. -/
theorem eraClosedComplete {s t : ETm 0}
    (h : ∀ ρ : Fin 0 → Nat, s.eval eraInterp ρ = t.eval eraInterp ρ) :
    Derivable eraDefs ⟨s, t⟩ := by
  have hs := closed_term_numeral s
  rw [h Fin.elim0] at hs
  exact hs.trans (closed_term_numeral t).symm

/-! ## The Mazzanti operations, derived

The five Mazzanti operations are terms over the minimal basis, following the
derivation chain of Prunescu–Sauras-Altuzarra–Shunia (arXiv:2505.23787; see also the
`Elementary recursive function` article of Wikipedia): squaring, the Kronecker delta,
truncated subtraction, the double product, division, multiplication, exponentiation.
Each operation carries a congruence rule and a numeral-computation rule; the latter
rests on the corresponding `Nat`-level identity, proved here from core lemmas. -/

/-- Auxiliary bound: `2n ≤ 2 ^ n`. -/
theorem two_mul_le_two_pow (n : Nat) : 2 * n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      cases k with
      | zero => decide
      | succ m =>
          have h2 : 2 ^ 1 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          rw [Nat.pow_one] at h2
          rw [Nat.pow_succ]
          omega

/-- Auxiliary bound: `n² < 2 ^ n + n`. -/
theorem mul_self_lt_two_pow_add (n : Nat) : n * n < 2 ^ n + n := by
  induction n with
  | zero => decide
  | succ k ih =>
      have h := two_mul_le_two_pow k
      have hexp : (k + 1) * (k + 1) = k * k + k + (k + 1) := by
        rw [Nat.succ_mul, Nat.mul_succ]
      rw [Nat.pow_succ]
      omega

/-- The squaring identity: `2 ^ 2n mod (2 ^ n + n) = n²`, since `2 ^ n ≡ -n` modulo
`2 ^ n + n` and `n²` is below the modulus. -/
theorem sq_identity (n : Nat) : 2 ^ (n + n) % (2 ^ n + n) = n * n := by
  have hA : n ≤ 2 ^ n := Nat.le_of_lt Nat.lt_two_pow_self
  have hsq : n * n < 2 ^ n + n := mul_self_lt_two_pow_add n
  have hRP : n * n ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul hA hA
  have hsub : (2 ^ n - n) * (2 ^ n + n) = 2 ^ n * (2 ^ n + n) - n * (2 ^ n + n) :=
    Nat.sub_mul _ _ _
  have h1 : 2 ^ n * (2 ^ n + n) = 2 ^ n * 2 ^ n + 2 ^ n * n := Nat.mul_add _ _ _
  have h2 : n * (2 ^ n + n) = n * 2 ^ n + n * n := Nat.mul_add _ _ _
  have hcomm : n * 2 ^ n = 2 ^ n * n := Nat.mul_comm _ _
  have key : 2 ^ (n + n) = (2 ^ n + n) * (2 ^ n - n) + n * n := by
    rw [Nat.pow_add, Nat.mul_comm (2 ^ n + n) (2 ^ n - n), hsub, h1, h2, hcomm]
    omega
  rw [key, Nat.mul_add_mod, Nat.mod_eq_of_lt hsq]

/-- Squaring: `x² = 2 ^ (x + x) mod (2 ^ x + x)`. -/
def esq {n : Nat} (t : ETm n) : ETm n := eexp2 (t +ᵉ t) %ᵉ (eexp2 t +ᵉ t)

/-- Congruence for squaring. -/
theorem esq_congr {defs : Defs EraB eraAr} {n : Nat} {t t' : ETm n}
    (h : Derivable defs ⟨t, t'⟩) : Derivable defs ⟨esq t, esq t'⟩ :=
  emod_congr (eexp2_congr (eadd_congr h h)) (eadd_congr (eexp2_congr h) h)

/-- Numerals compute squaring. -/
theorem numeral_sq {n : Nat} (a : Nat) :
    Derivable eraDefs ⟨esq (.numeral a : ETm n), .numeral (a * a)⟩ := by
  rw [← sq_identity a]
  exact (emod_congr ((eexp2_congr (numeral_add a a)).trans (numeral_exp2 _))
      ((eadd_congr (numeral_exp2 a) (.refl _)).trans (numeral_add _ _))).trans
    (numeral_mod _ _)

/-- The Kronecker-delta identity, off-diagonal case: for `i < j` the inner sum is
strictly between `0` and the modulus, so the outer exponent is positive and the power
is even. -/
theorem delta_identity_of_lt {i j : Nat} (h : i < j) :
    2 ^ ((2 ^ i % (2 ^ j + 1) + 2 ^ j % (2 ^ i + 1)) % (2 ^ i + 2 ^ j)) % 2 = 0 := by
  have hij : 2 ^ i ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
  have hA : 2 ^ i % (2 ^ j + 1) = 2 ^ i := Nat.mod_eq_of_lt (by omega)
  have hB : 2 ^ j % (2 ^ i + 1) < 2 ^ i + 1 := Nat.mod_lt _ (by omega)
  have h2i : 2 ^ i + 2 ^ i = 2 ^ (i + 1) := by rw [Nat.pow_succ]; omega
  have hi1j : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
  have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
  have hsum : 2 ^ i % (2 ^ j + 1) + 2 ^ j % (2 ^ i + 1) < 2 ^ i + 2 ^ j := by
    rw [hA]; omega
  rw [Nat.mod_eq_of_lt hsum, hA]
  rw [show 2 ^ i + 2 ^ j % (2 ^ i + 1) = (2 ^ i + 2 ^ j % (2 ^ i + 1) - 1) + 1 by omega,
    Nat.pow_succ, Nat.mul_mod_left]

/-- The Kronecker-delta identity: on the diagonal the inner sum is the modulus itself,
so the outer exponent is `0` and the power is the odd number `1`. -/
theorem delta_identity (i j : Nat) :
    2 ^ ((2 ^ i % (2 ^ j + 1) + 2 ^ j % (2 ^ i + 1)) % (2 ^ i + 2 ^ j)) % 2 =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hA : 2 ^ i % (2 ^ i + 1) = 2 ^ i := Nat.mod_eq_of_lt (by omega)
    rw [hA, Nat.mod_self]
  · rw [if_neg hij]
    cases Nat.lt_or_gt_of_ne hij with
    | inl h => exact delta_identity_of_lt h
    | inr h =>
        have hsymm := delta_identity_of_lt h
        rw [Nat.add_comm (2 ^ i % (2 ^ j + 1)) (2 ^ j % (2 ^ i + 1)),
          Nat.add_comm (2 ^ i) (2 ^ j)]
        exact hsymm

/-- The Kronecker delta:
`δ(x, y) = 2 ^ ((2ˣ mod (2ʸ + 1) + 2ʸ mod (2ˣ + 1)) mod (2ˣ + 2ʸ)) mod 2`. -/
def edelta {n : Nat} (s t : ETm n) : ETm n :=
  eexp2 ((eexp2 s %ᵉ (eexp2 t +ᵉ one) +ᵉ eexp2 t %ᵉ (eexp2 s +ᵉ one)) %ᵉ
    (eexp2 s +ᵉ eexp2 t)) %ᵉ .numeral 2

/-- Congruence for the Kronecker delta. -/
theorem edelta_congr {defs : Defs EraB eraAr} {n : Nat} {s s' t t' : ETm n}
    (hs : Derivable defs ⟨s, s'⟩) (ht : Derivable defs ⟨t, t'⟩) :
    Derivable defs ⟨edelta s t, edelta s' t'⟩ :=
  emod_congr (eexp2_congr (emod_congr
    (eadd_congr (emod_congr (eexp2_congr hs) (eadd_congr (eexp2_congr ht) (.refl one)))
      (emod_congr (eexp2_congr ht) (eadd_congr (eexp2_congr hs) (.refl one))))
    (eadd_congr (eexp2_congr hs) (eexp2_congr ht)))) (.refl _)

/-- Numerals compute the Kronecker delta. -/
theorem numeral_delta {n : Nat} (a b : Nat) :
    Derivable eraDefs
      ⟨edelta (.numeral a : ETm n) (.numeral b), .numeral (if a = b then 1 else 0)⟩ := by
  rw [← delta_identity a b]
  have hA := (emod_congr (numeral_exp2 (n := n) a)
      ((eadd_congr (numeral_exp2 b) (.refl one)).trans (numeral_add _ 1))).trans
    (numeral_mod _ _)
  have hB := (emod_congr (numeral_exp2 (n := n) b)
      ((eadd_congr (numeral_exp2 a) (.refl one)).trans (numeral_add _ 1))).trans
    (numeral_mod _ _)
  have hsum := (eadd_congr hA hB).trans (numeral_add _ _)
  have hden := (eadd_congr (numeral_exp2 (n := n) a) (numeral_exp2 b)).trans
    (numeral_add _ _)
  have hexp := (eexp2_congr ((emod_congr hsum hden).trans (numeral_mod _ _))).trans
    (numeral_exp2 _)
  exact (emod_congr hexp (.refl _)).trans (numeral_mod _ 2)

/-- The truncated-subtraction identity (Lemma 2 of arXiv:2505.23787):
`((2^(x+y) + x) mod (2^(x+y) + y)) mod (2^(x+y) + x) = x ∸ y`.  For `x ≥ y` the inner
remainder is `x - y`, fixed by the outer one; for `x < y` the inner remainder is the
outer modulus itself. -/
theorem tsub_identity (x y : Nat) :
    ((2 ^ (x + y) + x) % (2 ^ (x + y) + y)) % (2 ^ (x + y) + x) = x - y := by
  have hx : x < 2 ^ (x + y) :=
    Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by omega) (by omega))
  have hy : y < 2 ^ (x + y) :=
    Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by omega) (by omega))
  cases Nat.lt_or_ge x y with
  | inl hlt =>
      have h1 : (2 ^ (x + y) + x) % (2 ^ (x + y) + y) = 2 ^ (x + y) + x :=
        Nat.mod_eq_of_lt (by omega)
      rw [h1, Nat.mod_self]
      omega
  | inr hge =>
      have h1 : 2 ^ (x + y) + x = (x - y) + (2 ^ (x + y) + y) := by omega
      have h2 : (x - y) % (2 ^ (x + y) + y) = x - y := Nat.mod_eq_of_lt (by omega)
      have h3 : (x - y) % (2 ^ (x + y) + x) = x - y := Nat.mod_eq_of_lt (by omega)
      rw [h1, Nat.add_mod_right, h2, ← h1, h3]

/-- Truncated subtraction:
`x ∸ y = ((2^(x+y) + x) mod (2^(x+y) + y)) mod (2^(x+y) + x)`. -/
def esub {n : Nat} (s t : ETm n) : ETm n :=
  ((eexp2 (s +ᵉ t) +ᵉ s) %ᵉ (eexp2 (s +ᵉ t) +ᵉ t)) %ᵉ (eexp2 (s +ᵉ t) +ᵉ s)

/-- Truncated subtraction (derived). -/
infixl:65 " ∸ᵉ " => esub

/-- Congruence for truncated subtraction. -/
theorem esub_congr {defs : Defs EraB eraAr} {n : Nat} {s s' t t' : ETm n}
    (hs : Derivable defs ⟨s, s'⟩) (ht : Derivable defs ⟨t, t'⟩) :
    Derivable defs ⟨s ∸ᵉ t, s' ∸ᵉ t'⟩ :=
  emod_congr
    (emod_congr (eadd_congr (eexp2_congr (eadd_congr hs ht)) hs)
      (eadd_congr (eexp2_congr (eadd_congr hs ht)) ht))
    (eadd_congr (eexp2_congr (eadd_congr hs ht)) hs)

/-- Numerals compute truncated subtraction. -/
theorem numeral_sub {n : Nat} (a b : Nat) :
    Derivable eraDefs ⟨(.numeral a : ETm n) ∸ᵉ .numeral b, .numeral (a - b)⟩ := by
  rw [← tsub_identity a b]
  have hP := (eexp2_congr (numeral_add (n := n) a b)).trans (numeral_exp2 _)
  have hL := (eadd_congr hP (.refl _)).trans (numeral_add _ a)
  have hR := (eadd_congr hP (.refl _)).trans (numeral_add _ b)
  exact (emod_congr ((emod_congr hL hR).trans (numeral_mod _ _)) hL).trans
    (numeral_mod _ _)

/-- The double-product identity: `(x + y)² ∸ (x² + y²) = 2xy`. -/
theorem dmul_identity (x y : Nat) :
    (x + y) * (x + y) - (x * x + y * y) = 2 * (x * y) := by
  have h : (x + y) * (x + y) = x * x + x * y + (x * y + y * y) := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm y x]
  omega

/-- The double product: `2xy = (x + y)² ∸ (x² + y²)`. -/
def edmul {n : Nat} (s t : ETm n) : ETm n := esq (s +ᵉ t) ∸ᵉ (esq s +ᵉ esq t)

/-- Congruence for the double product. -/
theorem edmul_congr {defs : Defs EraB eraAr} {n : Nat} {s s' t t' : ETm n}
    (hs : Derivable defs ⟨s, s'⟩) (ht : Derivable defs ⟨t, t'⟩) :
    Derivable defs ⟨edmul s t, edmul s' t'⟩ :=
  esub_congr (esq_congr (eadd_congr hs ht)) (eadd_congr (esq_congr hs) (esq_congr ht))

/-- Numerals compute the double product. -/
theorem numeral_dmul {n : Nat} (a b : Nat) :
    Derivable eraDefs ⟨edmul (.numeral a : ETm n) (.numeral b), .numeral (2 * (a * b))⟩ := by
  rw [← dmul_identity a b]
  exact (esub_congr ((esq_congr (numeral_add a b)).trans (numeral_sq _))
      ((eadd_congr (numeral_sq a) (numeral_sq b)).trans (numeral_add _ _))).trans
    (numeral_sub _ _)

/-- The division identity (Lemma 3 of arXiv:2505.23787):
`⌊x/y⌋ = (2(x+1)(x ∸ (x mod y))) mod (2(x+1)y ∸ 1)`.  For `y > 0` the dividend is
`q·M + q` for `M` the modulus and `q` the quotient, which is below the modulus. -/
theorem div_identity (x y : Nat) :
    (2 * ((x + 1) * (x - x % y))) % (2 * ((x + 1) * y) - 1) = x / y := by
  cases y with
  | zero =>
      rw [Nat.mod_zero, Nat.sub_self, Nat.mul_zero, Nat.mul_zero, Nat.div_zero]
  | succ k =>
      have hdm := Nat.div_add_mod x (k + 1)
      have hq : x / (k + 1) ≤ x := Nat.div_le_self x (k + 1)
      have hsub : x - x % (k + 1) = (k + 1) * (x / (k + 1)) := by omega
      rw [hsub]
      have hZ : 2 * ((x + 1) * ((k + 1) * (x / (k + 1)))) =
          2 * ((x + 1) * (k + 1)) * (x / (k + 1)) := by
        simp [Nat.mul_assoc]
      rw [hZ]
      have h1 : x + 1 ≤ (x + 1) * (k + 1) := Nat.le_mul_of_pos_right (x + 1) (by omega)
      have hqM : x / (k + 1) < 2 * ((x + 1) * (k + 1)) - 1 := by omega
      have hle : x / (k + 1) ≤ 2 * ((x + 1) * (k + 1)) * (x / (k + 1)) :=
        Nat.le_mul_of_pos_left _ (by omega)
      have hkey : 2 * ((x + 1) * (k + 1)) * (x / (k + 1)) =
          (2 * ((x + 1) * (k + 1)) - 1) * (x / (k + 1)) + x / (k + 1) := by
        rw [Nat.sub_mul]
        omega
      rw [hkey, Nat.mul_add_mod, Nat.mod_eq_of_lt hqM]

/-- Division: `⌊x/y⌋ = (2(x+1)(x ∸ (x mod y))) mod (2(x+1)y ∸ 1)`. -/
def ediv {n : Nat} (s t : ETm n) : ETm n :=
  edmul (.succ s) (s ∸ᵉ (s %ᵉ t)) %ᵉ (edmul (.succ s) t ∸ᵉ one)

/-- Division (derived; `x / 0 = 0`). -/
infixl:70 " /ᵉ " => ediv

/-- Congruence for division. -/
theorem ediv_congr {defs : Defs EraB eraAr} {n : Nat} {s s' t t' : ETm n}
    (hs : Derivable defs ⟨s, s'⟩) (ht : Derivable defs ⟨t, t'⟩) :
    Derivable defs ⟨s /ᵉ t, s' /ᵉ t'⟩ :=
  emod_congr (edmul_congr (Derivable.succ_congr hs) (esub_congr hs (emod_congr hs ht)))
    (esub_congr (edmul_congr (Derivable.succ_congr hs) ht) (.refl one))

/-- Numerals compute division. -/
theorem numeral_div {n : Nat} (a b : Nat) :
    Derivable eraDefs ⟨(.numeral a : ETm n) /ᵉ .numeral b, .numeral (a / b)⟩ := by
  rw [← div_identity a b]
  have hsub := (esub_congr (.refl _) (numeral_mod (n := n) a b)).trans
    (numeral_sub a (a % b))
  have hN := (edmul_congr (.refl (.succ (.numeral a))) hsub).trans
    (numeral_dmul (a + 1) (a - a % b))
  have hM := (esub_congr (numeral_dmul (n := n) (a + 1) b) (.refl one)).trans
    (numeral_sub _ 1)
  exact (emod_congr hN hM).trans (numeral_mod _ _)

/-- Multiplication: `xy = ⌊2xy / 2⌋`. -/
def emul {n : Nat} (s t : ETm n) : ETm n := edmul s t /ᵉ .numeral 2

/-- Multiplication (derived). -/
infixl:70 " *ᵉ " => emul

/-- Congruence for multiplication. -/
theorem emul_congr {defs : Defs EraB eraAr} {n : Nat} {s s' t t' : ETm n}
    (hs : Derivable defs ⟨s, s'⟩) (ht : Derivable defs ⟨t, t'⟩) :
    Derivable defs ⟨s *ᵉ t, s' *ᵉ t'⟩ :=
  ediv_congr (edmul_congr hs ht) (.refl _)

/-- Numerals compute multiplication. -/
theorem numeral_mul {n : Nat} (a b : Nat) :
    Derivable eraDefs ⟨(.numeral a : ETm n) *ᵉ .numeral b, .numeral (a * b)⟩ := by
  rw [show a * b = 2 * (a * b) / 2 from (Nat.mul_div_cancel_left _ (by omega)).symm]
  exact (ediv_congr (numeral_dmul a b) (.refl _)).trans (numeral_div _ 2)

/-- Modular representation of powers of `2 ^ c`: since `2 ^ c ≡ x` modulo `2 ^ c - x`,
every `2 ^ (c·y)` is `x ^ y` plus a multiple of the modulus. -/
theorem pow_mod_rep (x c : Nat) (hx : x ≤ 2 ^ c) (y : Nat) :
    ∃ q, 2 ^ (c * y) = q * (2 ^ c - x) + x ^ y := by
  induction y with
  | zero => exact ⟨0, by simp⟩
  | succ y ih =>
      cases ih with
      | intro q hq =>
          refine ⟨q * 2 ^ c + x ^ y, ?_⟩
          have hsplit : 2 ^ c = (2 ^ c - x) + x := by omega
          have h1 : 2 ^ (c * (y + 1)) = 2 ^ (c * y) * 2 ^ c := by
            rw [Nat.mul_succ, Nat.pow_add]
          have h2 : x ^ y * 2 ^ c = x ^ y * (2 ^ c - x) + x ^ (y + 1) := by
            rw [Nat.pow_succ, ← Nat.mul_add, ← hsplit]
          have h3 : q * (2 ^ c - x) * 2 ^ c = q * 2 ^ c * (2 ^ c - x) :=
            Nat.mul_right_comm _ _ _
          rw [h1, hq, Nat.add_mul, h2, Nat.add_mul]
          omega

/-- The exponentiation identity: `x ^ y = 2 ^ ((xy+x+1)y) mod (2 ^ (xy+x+1) ∸ x)`,
by `pow_mod_rep` at `c := xy + x + 1`, which is large enough that `x ^ y` is below the
modulus. -/
theorem pow_identity (x y : Nat) :
    2 ^ ((x * y + x + 1) * y) % (2 ^ (x * y + x + 1) - x) = x ^ y := by
  have hxlt : x < 2 ^ (x * y + x) :=
    Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by omega) (by omega))
  have hk : 2 ^ (x * y + x + 1) = 2 ^ (x * y + x) * 2 := Nat.pow_succ 2 (x * y + x)
  have hb1 : x ^ y ≤ 2 ^ (x * y) := by
    have h1 : x ^ y ≤ (2 ^ x) ^ y :=
      Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) y
    have h2 : (2 ^ x) ^ y = 2 ^ (x * y) := (Nat.pow_mul 2 x y).symm
    omega
  have hyle : 2 ^ (x * y) ≤ 2 ^ (x * y + x) := Nat.pow_le_pow_right (by omega) (by omega)
  have hxc : x ≤ 2 ^ (x * y + x + 1) := by omega
  have hbound : x ^ y < 2 ^ (x * y + x + 1) - x := by omega
  cases pow_mod_rep x (x * y + x + 1) hxc y with
  | intro q hq =>
      rw [hq, Nat.mul_comm q, Nat.mul_add_mod, Nat.mod_eq_of_lt hbound]

/-- Exponentiation: `x ^ y = 2 ^ ((xy+x+1)y) mod (2 ^ (xy+x+1) ∸ x)`. -/
def epow {n : Nat} (s t : ETm n) : ETm n :=
  eexp2 ((s *ᵉ t +ᵉ s +ᵉ one) *ᵉ t) %ᵉ (eexp2 (s *ᵉ t +ᵉ s +ᵉ one) ∸ᵉ s)

/-- Exponentiation (derived; `0 ^ 0 = 1`). -/
infixr:75 " ^ᵉ " => epow

/-- Congruence for exponentiation. -/
theorem epow_congr {defs : Defs EraB eraAr} {n : Nat} {s s' t t' : ETm n}
    (hs : Derivable defs ⟨s, s'⟩) (ht : Derivable defs ⟨t, t'⟩) :
    Derivable defs ⟨s ^ᵉ t, s' ^ᵉ t'⟩ :=
  emod_congr
    (eexp2_congr (emul_congr
      (eadd_congr (eadd_congr (emul_congr hs ht) hs) (.refl one)) ht))
    (esub_congr (eexp2_congr
      (eadd_congr (eadd_congr (emul_congr hs ht) hs) (.refl one))) hs)

/-- Numerals compute exponentiation. -/
theorem numeral_pow {n : Nat} (a b : Nat) :
    Derivable eraDefs ⟨(.numeral a : ETm n) ^ᵉ .numeral b, .numeral (a ^ b)⟩ := by
  rw [← pow_identity a b]
  have hk := (eadd_congr ((eadd_congr (numeral_mul (n := n) a b) (.refl _)).trans
      (numeral_add _ a)) (.refl one)).trans (numeral_add _ 1)
  have hN := (eexp2_congr ((emul_congr hk (.refl _)).trans (numeral_mul _ b))).trans
    (numeral_exp2 _)
  have hM := (esub_congr ((eexp2_congr hk).trans (numeral_exp2 _)) (.refl _)).trans
    (numeral_sub _ a)
  exact (emod_congr hN hM).trans (numeral_mod _ _)

/-! ## Open-term recursion laws for the derived operations

The recursion laws that were defining axioms before the basis reduction, now
derived as theorems over the seven-equation basis.  Additive algebra
(Goodstein 1954 (6)–(10)) comes first; the subtraction, multiplication,
division, and exponentiation laws follow.  See
`docs/superpowers/specs/2026-06-12-era-open-laws-design.md`. -/

/-- `S u + v = S (u + v)` (`succ_add`); from Goodstein 1954's interchange (7)
`u + S v = S u + v` and the defining `u + S v = S (u + v)`.  By `uniq` on the
recursion variable then instantiation. -/
theorem derivable_succ_add {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨.succ u +ᵉ v, .succ (u +ᵉ v)⟩ := by
  have base : Derivable eraDefs
      ⟨(.succ (.var 1) : ETm 2) +ᵉ .var 0, .succ ((.var 1) +ᵉ (.var 0))⟩ := by
    refine Derivable.uniq (H := .succ (.var 1)) ?base ?stepF ?stepG
    case base =>
      have h := (derivable_add_zero (.succ (.var 0) : ETm 1)).trans
        (Derivable.succ_congr (derivable_add_zero (.var 0 : ETm 1))).symm
      simp only [Tm.subst, eadd_subst] at h ⊢
      exact h
    case stepF =>
      have h := derivable_add_succ (.succ (.var 1) : ETm 2) (.var 0)
      simp only [Tm.subst, eadd_subst] at h ⊢
      exact h
    case stepG =>
      have h := Derivable.succ_congr (derivable_add_succ (.var 1 : ETm 2) (.var 0))
      simp only [Tm.subst, eadd_subst] at h ⊢
      exact h
  have h := base.inst (fcons v (fcons u Fin.elim0))
  simp only [Tm.subst, eadd_subst, fcons] at h
  exact h

/-- `u + v = v + u` (Goodstein 1954 (8)).  By `uniq` on the recursion variable;
the step uses `derivable_succ_add`. -/
theorem derivable_add_comm {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨u +ᵉ v, v +ᵉ u⟩ := by
  have base : Derivable eraDefs
      ⟨(.var 1 : ETm 2) +ᵉ .var 0, (.var 0) +ᵉ (.var 1)⟩ := by
    refine Derivable.uniq (H := .succ (.var 1)) ?base ?stepF ?stepG
    case base =>
      have h := (derivable_add_zero (.var 0 : ETm 1)).trans
        (derivable_zero_add (.var 0 : ETm 1)).symm
      simp only [Tm.subst, eadd_subst] at h ⊢
      exact h
    case stepF =>
      have h := derivable_add_succ (.var 1 : ETm 2) (.var 0)
      simp only [Tm.subst, eadd_subst] at h ⊢
      exact h
    case stepG =>
      have h := derivable_succ_add (.var 0 : ETm 2) (.var 1)
      simp only [Tm.subst, eadd_subst] at h ⊢
      exact h
  have h := base.inst (fcons v (fcons u Fin.elim0))
  simp only [Tm.subst, eadd_subst, fcons] at h
  exact h

/-- `(u + v) + w = u + (v + w)` (Goodstein 1954 (10)).  By `uniq` on the
recursion variable `w`. -/
theorem derivable_add_assoc {n : Nat} (u v w : ETm n) :
    Derivable eraDefs ⟨(u +ᵉ v) +ᵉ w, u +ᵉ (v +ᵉ w)⟩ := by
  have base : Derivable eraDefs
      ⟨((.var 2 : ETm 3) +ᵉ .var 1) +ᵉ .var 0, (.var 2) +ᵉ ((.var 1) +ᵉ (.var 0))⟩ := by
    refine Derivable.uniq (H := .succ (.var 1)) ?base ?stepF ?stepG
    case base =>
      have h := (derivable_add_zero ((.var 1 : ETm 2) +ᵉ .var 0)).trans
        (eadd_congr (.refl (.var 1)) (derivable_add_zero (.var 0 : ETm 2))).symm
      simp only [Tm.subst, eadd_subst] at h ⊢
      exact h
    case stepF =>
      have h := derivable_add_succ ((.var 2 : ETm 3) +ᵉ .var 1) (.var 0)
      simp only [Tm.subst, eadd_subst] at h ⊢
      exact h
    case stepG =>
      have h := (eadd_congr (.refl (.var 2))
          (derivable_add_succ (.var 1 : ETm 3) (.var 0))).trans
        (derivable_add_succ (.var 2 : ETm 3) ((.var 1) +ᵉ (.var 0)))
      simp only [Tm.subst, eadd_subst] at h ⊢
      exact h
  have h := base.inst (fcons w (fcons v (fcons u Fin.elim0)))
  simp only [Tm.subst, eadd_subst, fcons] at h
  exact h

/-- `0 mod v = 0`.  By `uniq` on `v` with the constant-zero step functional. -/
theorem derivable_zero_mod {n : Nat} (v : ETm n) :
    Derivable eraDefs ⟨(.zero : ETm n) %ᵉ v, .zero⟩ := by
  have base : Derivable eraDefs ⟨(.zero : ETm 1) %ᵉ .var 0, .zero⟩ := by
    refine Derivable.uniq (H := .zero) ?base ?stepF ?stepG
    case base =>
      have h := derivable_mod_zero (.zero : ETm 0)
      simp only [Tm.subst, emod_subst] at h ⊢
      exact h
    case stepF =>
      have h := (emod_congr (.refl (.zero : ETm 1))
          (derivable_zero_add (.succ (.var 0))).symm).trans
        (derivable_mod_lt (.zero : ETm 1) (.var 0))
      simp only [Tm.subst, emod_subst] at h ⊢
      exact h
    case stepG =>
      exact Derivable.refl _
  have h := base.inst (fun _ => v)
  simp only [Tm.subst, emod_subst] at h
  exact h

/-- `v mod v = 0`.  From the divisor-subtraction axiom at dividend `0`, with no
induction. -/
theorem derivable_mod_self {n : Nat} (v : ETm n) :
    Derivable eraDefs ⟨v %ᵉ v, .zero⟩ :=
  (emod_congr (derivable_zero_add v) (.refl v)).symm.trans
    ((derivable_mod_add .zero v).trans (derivable_zero_mod v))

/-- `t ∸ t = 0`.  Both remainders of the `esub` unfolding collapse: the inner is
`mod_self`, the outer is `zero_mod`; the divisor and dividend shapes coincide. -/
theorem derivable_sub_self {n : Nat} (t : ETm n) :
    Derivable eraDefs ⟨t ∸ᵉ t, .zero⟩ :=
  (emod_congr (derivable_mod_self (eexp2 (t +ᵉ t) +ᵉ t)) (.refl _)).trans
    (derivable_zero_mod (eexp2 (t +ᵉ t) +ᵉ t))

/-- `0 ∸ w = 0`.  By `uniq` on `w` with the constant-zero step functional (an
instance of extensionality, `Derivable.ext_succ`, since the right side is
constant).  The zero case is `sub_self`; the successor case uses `axModLt` on the
inner remainder, which matches only a successor-shaped divisor. -/
theorem derivable_zero_sub {n : Nat} (w : ETm n) :
    Derivable eraDefs ⟨(.zero : ETm n) ∸ᵉ w, .zero⟩ := by
  have base : Derivable eraDefs ⟨(.zero : ETm 1) ∸ᵉ .var 0, .zero⟩ := by
    refine Derivable.uniq (H := .zero) ?base ?stepF ?stepG
    case base =>
      have h := derivable_sub_self (.zero : ETm 0)
      simp only [esub, Tm.subst, eadd_subst, emod_subst, eexp2_subst] at h ⊢
      exact h
    case stepF =>
      -- the exponent `eexp2 (0 + S x)` is written inline so it unifies with the goal
      have hinner : Derivable eraDefs
          ⟨(eexp2 ((.zero : ETm 1) +ᵉ .succ (.var 0)) +ᵉ .zero) %ᵉ
              (eexp2 ((.zero : ETm 1) +ᵉ .succ (.var 0)) +ᵉ .succ (.var 0)),
            eexp2 ((.zero : ETm 1) +ᵉ .succ (.var 0)) +ᵉ .zero⟩ :=
        (emod_congr (.refl _)
            (eadd_congr (derivable_add_zero
                (eexp2 ((.zero : ETm 1) +ᵉ .succ (.var 0)))).symm
              (.refl (.succ (.var 0))))).trans
          (derivable_mod_lt (eexp2 ((.zero : ETm 1) +ᵉ .succ (.var 0)) +ᵉ .zero) (.var 0))
      have h : Derivable eraDefs
          ⟨((eexp2 ((.zero : ETm 1) +ᵉ .succ (.var 0)) +ᵉ .zero) %ᵉ
                (eexp2 ((.zero : ETm 1) +ᵉ .succ (.var 0)) +ᵉ .succ (.var 0))) %ᵉ
              (eexp2 ((.zero : ETm 1) +ᵉ .succ (.var 0)) +ᵉ .zero), .zero⟩ :=
        (emod_congr hinner (.refl _)).trans
          (derivable_mod_self (eexp2 ((.zero : ETm 1) +ᵉ .succ (.var 0)) +ᵉ .zero))
      simp only [esub, Tm.subst, eadd_subst, emod_subst, eexp2_subst, bump, fcons] at h ⊢
      exact h
    case stepG =>
      exact Derivable.refl _
  have h := base.inst (fun _ => w)
  simp only [esub, Tm.subst, eadd_subst, emod_subst, eexp2_subst] at h
  exact h

/-- `0 ∸ 1 = 0` (predecessor of zero); the instance of `zero_sub` at `1`. -/
theorem derivable_pred_zero {n : Nat} :
    Derivable eraDefs ⟨(.zero : ETm n) ∸ᵉ one, .zero⟩ :=
  derivable_zero_sub one

/-- `edmul t 0 = 0` (the double product `2·t·0`).  The squared first factor
reduces by `add_zero`; the second `esq 0` is the numeral `0`; the remaining
`esq t ∸ esq t` is `sub_self`. -/
theorem derivable_edmul_zero {n : Nat} (t : ETm n) :
    Derivable eraDefs ⟨edmul t .zero, .zero⟩ :=
  have hsq0 : Derivable eraDefs ⟨esq (.zero : ETm n), .zero⟩ := numeral_sq (n := n) 0
  esub_congr (esq_congr (derivable_add_zero t))
      ((eadd_congr (.refl (esq t)) hsq0).trans (derivable_add_zero (esq t)))
    |>.trans (derivable_sub_self (esq t))

/-- `u * 0 = 0`.  The double product `edmul u 0` is `0` (`edmul_zero`); the
remaining `0 / 2` is the numeral `0`. -/
theorem derivable_mul_zero {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨u *ᵉ .zero, .zero⟩ :=
  (ediv_congr (derivable_edmul_zero u) (.refl (.numeral 2))).trans
    (numeral_div (n := n) 0 2)

/-- `u / 0 = 0`.  The dividend's `edmul (S u) (u ∸ (u mod 0))` collapses to `0`
(`mod_zero`, `sub_self`, `edmul_zero`); the divisor's `edmul (S u) 0 ∸ 1`
collapses to `0` (`edmul_zero`, `pred_zero`); the result is `0 mod 0 = 0`. -/
theorem derivable_div_zero {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨u /ᵉ .zero, .zero⟩ :=
  have harg : Derivable eraDefs ⟨u ∸ᵉ (u %ᵉ .zero), .zero⟩ :=
    (esub_congr (.refl u) (derivable_mod_zero u)).trans (derivable_sub_self u)
  have hdividend : Derivable eraDefs
      ⟨edmul (.succ u) (u ∸ᵉ (u %ᵉ .zero)), .zero⟩ :=
    (edmul_congr (.refl (.succ u)) harg).trans (derivable_edmul_zero (.succ u))
  have hdivisor : Derivable eraDefs ⟨edmul (.succ u) .zero ∸ᵉ one, .zero⟩ :=
    (esub_congr (derivable_edmul_zero (.succ u)) (.refl one)).trans (derivable_zero_sub one)
  (emod_congr hdividend hdivisor).trans (derivable_mod_zero .zero)

/-- `0 / S u = 0`.  The dividend's inner remainder `0 mod S u` is `0`
(`zero_mod`), so its subtraction is `0 ∸ 0 = 0` (`sub_self`) and the double
product is `0` (`edmul_zero`); the modulus stays open in `u` and the result is
`0 mod (modulus) = 0` (`zero_mod`). -/
theorem derivable_zero_div {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨(.zero : ETm n) /ᵉ .succ u, .zero⟩ :=
  have harg : Derivable eraDefs
      ⟨(.zero : ETm n) ∸ᵉ ((.zero : ETm n) %ᵉ .succ u), .zero⟩ :=
    (esub_congr (.refl .zero) (derivable_zero_mod (.succ u))).trans
      (derivable_sub_self .zero)
  have hdividend : Derivable eraDefs
      ⟨edmul (.succ .zero) ((.zero : ETm n) ∸ᵉ ((.zero : ETm n) %ᵉ .succ u)), .zero⟩ :=
    (edmul_congr (.refl (.succ .zero)) harg).trans (derivable_edmul_zero (.succ .zero))
  (emod_congr hdividend (.refl _)).trans (derivable_zero_mod _)

/-! ### The exponent-parametric subtraction template

`esubAt e s t` exposes the exponent of the `esub` unfolding as a separate
argument, so that `s ∸ t = esubAt (s + t) s t` definitionally.  Two laws decide
the value purely by term shape, given domination of the dividend by `2^e`. -/

/-- The `esub` unfolding with its exponent `e` exposed as a separate argument. -/
def esubAt {n : Nat} (e s t : ETm n) : ETm n :=
  ((eexp2 e +ᵉ s) %ᵉ (eexp2 e +ᵉ t)) %ᵉ (eexp2 e +ᵉ s)

/-- `esub` is `esubAt` at the canonical exponent `s + t`. -/
theorem esub_eq_esubAt {n : Nat} (s t : ETm n) : s ∸ᵉ t = esubAt (s +ᵉ t) s t := rfl

/-- `esubAt e u v = 0` when `v` exceeds `u` by a successor (`v = u + S d`).  The
inner divisor is the dividend plus `S d`, closed by `axModLt`; the outer
remainder is `mod_self`.  No domination hypothesis is consumed. -/
theorem derivable_esubAt_of_lt {n : Nat} {e u v d : ETm n}
    (hlt : Derivable eraDefs ⟨v, u +ᵉ .succ d⟩) :
    Derivable eraDefs ⟨esubAt e u v, .zero⟩ :=
  have hdiv : Derivable eraDefs ⟨eexp2 e +ᵉ v, (eexp2 e +ᵉ u) +ᵉ .succ d⟩ :=
    (eadd_congr (.refl (eexp2 e)) hlt).trans (derivable_add_assoc (eexp2 e) u (.succ d)).symm
  have hinner : Derivable eraDefs
      ⟨(eexp2 e +ᵉ u) %ᵉ (eexp2 e +ᵉ v), eexp2 e +ᵉ u⟩ :=
    (emod_congr (.refl (eexp2 e +ᵉ u)) hdiv).trans (derivable_mod_lt (eexp2 e +ᵉ u) d)
  (emod_congr hinner (.refl (eexp2 e +ᵉ u))).trans (derivable_mod_self (eexp2 e +ᵉ u))

/-- `esubAt e u v = w` when `u = w + v` and `2^e` exceeds `u` by a successor
(`2^e = u + S p`).  The inner remainder rewrites `2^e + u` as `w + (2^e + v)` and
peels one `2^e + v` by `axModAdd`, leaving `w` (below `2^e + v`); the outer
remainder leaves `w` (below `2^e + u`).  Both domination sites are discharged by
`hED`, which exhibits `2^e + Y = w + S (v + (p + Y))`. -/
theorem derivable_esubAt_of_add {n : Nat} {e u v w p : ETm n}
    (hsum : Derivable eraDefs ⟨u, w +ᵉ v⟩)
    (hdom : Derivable eraDefs ⟨eexp2 e, u +ᵉ .succ p⟩) :
    Derivable eraDefs ⟨esubAt e u v, w⟩ := by
  have hED : ∀ Y : ETm n, Derivable eraDefs
      ⟨eexp2 e +ᵉ Y, w +ᵉ .succ (v +ᵉ (p +ᵉ Y))⟩ := fun Y =>
    (eadd_congr hdom (.refl Y)).trans
      ((derivable_add_assoc u (.succ p) Y).trans
        ((eadd_congr (.refl u) (derivable_succ_add p Y)).trans
          ((derivable_add_succ u (p +ᵉ Y)).trans
            ((Derivable.succ_congr (eadd_congr hsum (.refl (p +ᵉ Y)))).trans
              ((Derivable.succ_congr (derivable_add_assoc w v (p +ᵉ Y))).trans
                (derivable_add_succ w (v +ᵉ (p +ᵉ Y))).symm)))))
  have hwv : Derivable eraDefs ⟨w %ᵉ (eexp2 e +ᵉ v), w⟩ :=
    (emod_congr (.refl w) (hED v)).trans (derivable_mod_lt w (v +ᵉ (p +ᵉ v)))
  have hwu : Derivable eraDefs ⟨w %ᵉ (eexp2 e +ᵉ u), w⟩ :=
    (emod_congr (.refl w) (hED u)).trans (derivable_mod_lt w (v +ᵉ (p +ᵉ u)))
  have hrearrange : Derivable eraDefs ⟨eexp2 e +ᵉ u, w +ᵉ (eexp2 e +ᵉ v)⟩ :=
    (eadd_congr (.refl (eexp2 e)) hsum).trans
      ((derivable_add_assoc (eexp2 e) w v).symm.trans
        ((eadd_congr (derivable_add_comm (eexp2 e) w) (.refl v)).trans
          (derivable_add_assoc w (eexp2 e) v)))
  have hinner : Derivable eraDefs ⟨(eexp2 e +ᵉ u) %ᵉ (eexp2 e +ᵉ v), w⟩ :=
    ((emod_congr hrearrange (.refl (eexp2 e +ᵉ v))).trans
      (derivable_mod_add w (eexp2 e +ᵉ v))).trans hwv
  exact (emod_congr hinner (.refl (eexp2 e +ᵉ u))).trans hwu

end Era

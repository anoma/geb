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

  Basis: Mazzanti's five-element composition basis for E³
  (S. Mazzanti, "Plain Bases for Classes of Primitive Recursive Functions",
   MLQ 48:1 (2002) 93–104):  { x+y, x∸y, x·y, ⌊x/y⌋, xʸ }.
  Conventions match Lean's `Nat`:  x ∸ y = x - y,  x / 0 = 0,  0 ^ 0 = 1.

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

/-! ## The ERA instance: Mazzanti's basis -/

/-- Mazzanti's composition basis for the Kalmár elementary functions E³:
`{ x+y, x∸y, x·y, ⌊x/y⌋, xʸ }`.  All five are binary. -/
inductive EraB : Type
  | add | tsub | mul | div | pow
  deriving DecidableEq

/-- All five basis symbols are binary.  (Point-free so that `eraAr b` is manifestly
independent of `b`.) -/
def eraAr : EraB → Nat := Function.const _ 2

/-- Terms over the Mazzanti basis. -/
abbrev ETm (n : Nat) := Tm EraB eraAr n

/-- Equations over the Mazzanti basis. -/
abbrev EEqn (n : Nat) := Eqn EraB eraAr n

/-- Apply a (binary) basis symbol to two terms. -/
def bin (b : EraB) {n : Nat} (s t : ETm n) : ETm n :=
  .app b (fcons s (fcons t Fin.elim0))

/-- Addition. -/
infixl:65 " +ᵉ " => bin EraB.add

/-- Truncated subtraction (`x ∸ y = max (x - y) 0`). -/
infixl:65 " ∸ᵉ " => bin EraB.tsub

/-- Multiplication. -/
infixl:70 " *ᵉ " => bin EraB.mul

/-- Division (`x / 0 = 0`). -/
infixl:70 " /ᵉ " => bin EraB.div

/-- Exponentiation (`0 ^ 0 = 1`). -/
infixr:75 " ^ᵉ " => bin EraB.pow

/-- The numeral 1. -/
def one {n : Nat} : ETm n := .succ .zero

/-- Substitution commutes with basis application (the tuple of arguments is a
function, so this congruence needs `funext` + case analysis on `Fin 2`; it is
the `E³` instance of the general `subst`/`app` commutation). -/
theorem bin_subst (b : EraB) {n m : Nat} (s t : ETm n) (σ : Fin n → ETm m) :
    (bin b s t).subst σ = bin b (s.subst σ) (t.subst σ) :=
  congrArg (Tm.app b) (funext fun i =>
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨_ + 2, h⟩ =>
        absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h)) (Nat.not_lt_zero _))

/-! ### The thirteen defining equations, named
Conventions: recursion equations throughout; `∸` via its own predecessor term `z ∸ 1`;
division by the remainder-increment recurrence, with the remainder spelled out as the
term `x ∸ S y · (x / S y)`.  All thirteen are literally true of Lean's `Nat` operations
(see `eraSound` below). -/

-- addition (recursion on the 2nd argument)

/-- `x + 0 = x`. -/
def axAdd0 : (n : Nat) × EEqn n := ⟨1, ⟨(.var 0) +ᵉ .zero, .var 0⟩⟩

/-- `x + S y = S (x + y)`. -/
def axAddS : (n : Nat) × EEqn n :=
  ⟨2, ⟨(.var 0) +ᵉ .succ (.var 1), .succ ((.var 0) +ᵉ (.var 1))⟩⟩

-- truncated subtraction

/-- `x ∸ 0 = x`. -/
def axSub0 : (n : Nat) × EEqn n := ⟨1, ⟨(.var 0) ∸ᵉ .zero, .var 0⟩⟩

/-- `x ∸ S y = (x ∸ y) ∸ 1`. -/
def axSubS : (n : Nat) × EEqn n :=
  ⟨2, ⟨(.var 0) ∸ᵉ .succ (.var 1), ((.var 0) ∸ᵉ (.var 1)) ∸ᵉ one⟩⟩

/-- `0 ∸ 1 = 0`. -/
def axPred0 : (n : Nat) × EEqn n := ⟨0, ⟨(.zero : ETm 0) ∸ᵉ one, .zero⟩⟩

/-- `S x ∸ 1 = x`. -/
def axPredS : (n : Nat) × EEqn n := ⟨1, ⟨.succ (.var 0) ∸ᵉ one, .var 0⟩⟩

-- multiplication

/-- `x · 0 = 0`. -/
def axMul0 : (n : Nat) × EEqn n := ⟨1, ⟨(.var 0) *ᵉ .zero, .zero⟩⟩

/-- `x · S y = x·y + x`. -/
def axMulS : (n : Nat) × EEqn n :=
  ⟨2, ⟨(.var 0) *ᵉ .succ (.var 1), ((.var 0) *ᵉ (.var 1)) +ᵉ (.var 0)⟩⟩

-- exponentiation (0^0 = 1)

/-- `x ^ 0 = 1`. -/
def axPow0 : (n : Nat) × EEqn n := ⟨1, ⟨(.var 0) ^ᵉ .zero, one⟩⟩

/-- `x ^ S y = x^y · x`. -/
def axPowS : (n : Nat) × EEqn n :=
  ⟨2, ⟨(.var 0) ^ᵉ .succ (.var 1), ((.var 0) ^ᵉ (.var 1)) *ᵉ (.var 0)⟩⟩

-- division (x / 0 = 0)

/-- `x / 0 = 0`. -/
def axDivZ : (n : Nat) × EEqn n := ⟨1, ⟨(.var 0) /ᵉ .zero, .zero⟩⟩

/-- `0 / S y = 0`. -/
def axDiv0 : (n : Nat) × EEqn n := ⟨1, ⟨(.zero : ETm 1) /ᵉ .succ (.var 0), .zero⟩⟩

/-- `S x / S y = x / S y + (1 ∸ (y ∸ r))` with `r := x ∸ S y · (x / S y)`: the quotient
increments exactly when the remainder has reached `y`. -/
def axDivS : (n : Nat) × EEqn n :=
  ⟨2, ⟨.succ (.var 0) /ᵉ .succ (.var 1),
       ((.var 0) /ᵉ .succ (.var 1)) +ᵉ
         (one ∸ᵉ ((.var 1) ∸ᵉ ((.var 0) ∸ᵉ .succ (.var 1) *ᵉ ((.var 0) /ᵉ .succ (.var 1)))))⟩⟩

/-- The axiom set of ERA: the thirteen defining equations, as a finite literal list. -/
def eraDefs : Defs EraB eraAr :=
  [axAdd0, axAddS, axSub0, axSubS, axPred0, axPredS,
   axMul0, axMulS, axPow0, axPowS, axDivZ, axDiv0, axDivS]

/-! ## Standard semantics and soundness -/

/-- Evaluation of terms in ℕ, given an interpretation of the basis. -/
def Tm.eval {B : Type} {ar : B → Nat} (I : (b : B) → (Fin (ar b) → Nat) → Nat)
    {n : Nat} (t : Tm B ar n) (ρ : Fin n → Nat) : Nat :=
  match t with
  | .var i    => ρ i
  | .zero     => 0
  | .succ t   => (t.eval I ρ) + 1
  | .app b ts => I b (fun i => (ts i).eval I ρ)

/-- The standard interpretation of the Mazzanti basis (Lean's `Nat`
operations have exactly the right conventions). -/
def eraInterp : (b : EraB) → (Fin (eraAr b) → Nat) → Nat
  | .add,  v => v ⟨0, by decide⟩ + v ⟨1, by decide⟩
  | .tsub, v => v ⟨0, by decide⟩ - v ⟨1, by decide⟩
  | .mul,  v => v ⟨0, by decide⟩ * v ⟨1, by decide⟩
  | .div,  v => v ⟨0, by decide⟩ / v ⟨1, by decide⟩
  | .pow,  v => v ⟨0, by decide⟩ ^ v ⟨1, by decide⟩

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

/-- The recurrence for the successor case of division, as a `Nat` identity: the quotient
increments exactly when the remainder has reached the predecessor of the divisor. -/
theorem succ_div_succ (x y : Nat) :
    (x + 1) / (y + 1) = x / (y + 1) + (1 - (y - (x - (y + 1) * (x / (y + 1))))) := by
  have hdm : (y + 1) * (x / (y + 1)) + x % (y + 1) = x := Nat.div_add_mod x (y + 1)
  have hlt : x % (y + 1) < y + 1 := Nat.mod_lt x (Nat.succ_pos y)
  cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hlt) with
  | inl heq =>
      -- the remainder has reached `y`: the divisor divides `x + 1`, the quotient steps
      have hx : x + 1 = (y + 1) * (x / (y + 1) + 1) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      rw [hx, Nat.mul_div_cancel_left _ (Nat.succ_pos y)]
      omega
  | inr hlt' =>
      -- the remainder is below `y`: the quotient is unchanged
      have hx : x + 1 = (y + 1) * (x / (y + 1)) + (x % (y + 1) + 1) := by omega
      have h0 : (x % (y + 1) + 1) / (y + 1) = 0 := Nat.div_eq_of_lt (by omega)
      rw [hx, Nat.mul_add_div (Nat.succ_pos y), h0]
      omega

/-- The thirteen defining equations hold of Lean's `Nat` operations. -/
theorem eraDefs_sound : ∀ d ∈ eraDefs, ∀ ρ : Fin d.1 → Nat,
    d.2.lhs.eval eraInterp ρ = d.2.rhs.eval eraInterp ρ := by
  simp only [eraDefs, axAdd0, axAddS, axSub0, axSubS, axPred0, axPredS, axMul0, axMulS,
    axPow0, axPowS, axDivZ, axDiv0, axDivS, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true]
  -- The additive and truncated-subtractive equations are linear (`omega`); the
  -- multiplicative, exponential, and divisor-zero equations are core recurrences; the
  -- division step equation is `succ_div_succ`.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      intro ρ <;> simp only [Tm.eval, bin, one, fcons, eraInterp] <;>
    first
    | omega
    | exact Nat.mul_succ _ _
    | exact Nat.pow_zero _
    | exact Nat.pow_succ _ _
    | exact Nat.div_zero _
    | exact Nat.zero_div _
    | exact succ_div_succ _ _

/-- Soundness in the standard model: every derivable equation holds of Lean's `Nat`
operations under every valuation.  Instance of the generic `Derivable.sound` at the
thirteen verified identities `eraDefs_sound`. -/
theorem eraSound {n : Nat} {e : EEqn n} (h : Derivable eraDefs e)
    (ρ : Fin n → Nat) : e.lhs.eval eraInterp ρ = e.rhs.eval eraInterp ρ :=
  Derivable.sound eraInterp eraDefs_sound h ρ

/-! ## A machine-checked example derivation: `0 + x = x` via `uniq`.
(The defining equation gives only `x + 0 = x`; the flipped identity needs
induction.)  Take F := 0 + x, G := x, step functional H := S(previous). -/

example : Derivable eraDefs ⟨(.zero : ETm 1) +ᵉ .var 0, .var 0⟩ := by
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
    simp only [Tm.subst, bin_subst] at h ⊢
    exact h
  case stepF =>
    -- 0 + S x = S (0 + x) — instance of `x + S y = S (x + y)` under x ↦ 0, y ↦ x
    have h := Derivable.subst
      (σ  := fcons (.zero : ETm 1) (fcons (.var 0) Fin.elim0))
      (σ' := fcons (.zero : ETm 1) (fcons (.var 0) Fin.elim0))
      (Derivable.ax hAS) (fun _ => Derivable.refl _)
    simp only [Tm.subst, bin_subst] at h ⊢
    exact h
  case stepG =>
    -- S x = S x
    exact Derivable.refl _

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

/-- Every basis application over the (uniformly binary) Mazzanti basis is a `bin`. -/
theorem app_eq_bin {n : Nat} (b : EraB) (ts : Fin (eraAr b) → ETm n) :
    Tm.app b ts = bin b (ts ⟨0, Nat.succ_pos 1⟩) (ts ⟨1, Nat.lt_succ_self 1⟩) :=
  congrArg (Tm.app b) (funext fun i =>
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨_ + 2, h⟩ => absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h))
        (Nat.not_lt_zero _))

/-- Congruence for a binary basis application. -/
theorem bin_congr {defs : Defs EraB eraAr} (b : EraB) {n : Nat} {s s' t t' : ETm n}
    (hs : Derivable defs ⟨s, s'⟩) (ht : Derivable defs ⟨t, t'⟩) :
    Derivable defs ⟨bin b s t, bin b s' t'⟩ := by
  have h := Derivable.subst (F := (bin b (.var 0) (.var 1) : ETm 2)) (G := bin b (.var 0) (.var 1))
    (σ := fcons s fun _ => t) (σ' := fcons s' fun _ => t') (.refl _) fun i =>
      match i with
      | ⟨0, _⟩ => hs
      | ⟨_ + 1, _⟩ => ht
  simp only [Tm.subst, bin_subst] at h
  exact h

/-- A listed defining equation, instantiated along a substitution tuple. -/
theorem derivable_def {m n : Nat} {e : EEqn m} (hax : ⟨m, e⟩ ∈ eraDefs)
    (σ : Fin m → ETm n) : Derivable eraDefs ⟨e.lhs.subst σ, e.rhs.subst σ⟩ :=
  (Derivable.ax hax).inst σ

/-- `u + 0 = u`. -/
theorem derivable_add_zero {n : Nat} (u : ETm n) : Derivable eraDefs ⟨u +ᵉ .zero, u⟩ := by
  have h := derivable_def (m := 1) (e := ⟨(.var 0) +ᵉ .zero, .var 0⟩)
    (by simp [eraDefs, axAdd0]) (fun _ => u)
  simp only [Tm.subst, bin_subst] at h
  exact h

/-- `u + S v = S (u + v)`. -/
theorem derivable_add_succ {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨u +ᵉ .succ v, .succ (u +ᵉ v)⟩ := by
  have h := derivable_def (m := 2)
    (e := ⟨(.var 0) +ᵉ .succ (.var 1), .succ ((.var 0) +ᵉ (.var 1))⟩)
    (by simp [eraDefs, axAddS]) (fcons u fun _ => v)
  simp only [Tm.subst, bin_subst] at h
  exact h

/-- `u ∸ 0 = u`. -/
theorem derivable_sub_zero {n : Nat} (u : ETm n) : Derivable eraDefs ⟨u ∸ᵉ .zero, u⟩ := by
  have h := derivable_def (m := 1) (e := ⟨(.var 0) ∸ᵉ .zero, .var 0⟩)
    (by simp [eraDefs, axSub0]) (fun _ => u)
  simp only [Tm.subst, bin_subst] at h
  exact h

/-- `u ∸ S v = (u ∸ v) ∸ 1`. -/
theorem derivable_sub_succ {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨u ∸ᵉ .succ v, (u ∸ᵉ v) ∸ᵉ one⟩ := by
  have h := derivable_def (m := 2)
    (e := ⟨(.var 0) ∸ᵉ .succ (.var 1), ((.var 0) ∸ᵉ (.var 1)) ∸ᵉ one⟩)
    (by simp [eraDefs, axSubS]) (fcons u fun _ => v)
  simp only [Tm.subst, bin_subst] at h
  exact h

/-- `0 ∸ 1 = 0`. -/
theorem derivable_pred_zero {n : Nat} : Derivable eraDefs ⟨(.zero : ETm n) ∸ᵉ one, .zero⟩ := by
  have h := derivable_def (m := 0) (e := ⟨(.zero : ETm 0) ∸ᵉ one, .zero⟩)
    (by simp [eraDefs, axPred0]) (Fin.elim0 : Fin 0 → ETm n)
  simp only [Tm.subst, bin_subst] at h
  exact h

/-- `S u ∸ 1 = u`. -/
theorem derivable_pred_succ {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨.succ u ∸ᵉ one, u⟩ := by
  have h := derivable_def (m := 1) (e := ⟨.succ (.var 0) ∸ᵉ one, .var 0⟩)
    (by simp [eraDefs, axPredS]) (fun _ => u)
  simp only [Tm.subst, bin_subst] at h
  exact h

/-- `u · 0 = 0`. -/
theorem derivable_mul_zero {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨u *ᵉ .zero, .zero⟩ := by
  have h := derivable_def (m := 1) (e := ⟨(.var 0) *ᵉ .zero, .zero⟩)
    (by simp [eraDefs, axMul0]) (fun _ => u)
  simp only [Tm.subst, bin_subst] at h
  exact h

/-- `u · S v = u·v + u`. -/
theorem derivable_mul_succ {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨u *ᵉ .succ v, (u *ᵉ v) +ᵉ u⟩ := by
  have h := derivable_def (m := 2)
    (e := ⟨(.var 0) *ᵉ .succ (.var 1), ((.var 0) *ᵉ (.var 1)) +ᵉ (.var 0)⟩)
    (by simp [eraDefs, axMulS]) (fcons u fun _ => v)
  simp only [Tm.subst, bin_subst] at h
  exact h

/-- `u ^ 0 = 1`. -/
theorem derivable_pow_zero {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨u ^ᵉ .zero, one⟩ := by
  have h := derivable_def (m := 1) (e := ⟨(.var 0) ^ᵉ .zero, one⟩)
    (by simp [eraDefs, axPow0]) (fun _ => u)
  simp only [Tm.subst, bin_subst] at h
  exact h

/-- `u ^ S v = u^v · u`. -/
theorem derivable_pow_succ {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨u ^ᵉ .succ v, (u ^ᵉ v) *ᵉ u⟩ := by
  have h := derivable_def (m := 2)
    (e := ⟨(.var 0) ^ᵉ .succ (.var 1), ((.var 0) ^ᵉ (.var 1)) *ᵉ (.var 0)⟩)
    (by simp [eraDefs, axPowS]) (fcons u fun _ => v)
  simp only [Tm.subst, bin_subst] at h
  exact h

/-- `u / 0 = 0`. -/
theorem derivable_div_zero {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨u /ᵉ .zero, .zero⟩ := by
  have h := derivable_def (m := 1) (e := ⟨(.var 0) /ᵉ .zero, .zero⟩)
    (by simp [eraDefs, axDivZ]) (fun _ => u)
  simp only [Tm.subst, bin_subst] at h
  exact h

/-- `0 / S u = 0`. -/
theorem derivable_zero_div {n : Nat} (u : ETm n) :
    Derivable eraDefs ⟨(.zero : ETm n) /ᵉ .succ u, .zero⟩ := by
  have h := derivable_def (m := 1) (e := ⟨(.zero : ETm 1) /ᵉ .succ (.var 0), .zero⟩)
    (by simp [eraDefs, axDiv0]) (fun _ => u)
  simp only [Tm.subst, bin_subst] at h
  exact h

/-- `S u / S v = u / S v + (1 ∸ (v ∸ (u ∸ S v · (u / S v))))`. -/
theorem derivable_div_succ {n : Nat} (u v : ETm n) :
    Derivable eraDefs ⟨.succ u /ᵉ .succ v,
      (u /ᵉ .succ v) +ᵉ (one ∸ᵉ (v ∸ᵉ (u ∸ᵉ .succ v *ᵉ (u /ᵉ .succ v))))⟩ := by
  have h := derivable_def (m := 2)
    (e := ⟨.succ (.var 0) /ᵉ .succ (.var 1),
      ((.var 0) /ᵉ .succ (.var 1)) +ᵉ
        (one ∸ᵉ ((.var 1) ∸ᵉ ((.var 0) ∸ᵉ .succ (.var 1) *ᵉ ((.var 0) /ᵉ .succ (.var 1)))))⟩)
    (by simp [eraDefs, axDivS]) (fcons u fun _ => v)
  simp only [Tm.subst, bin_subst] at h
  exact h

/-! ### Numeral computation
The defining equations compute every basis operation on numerals. -/

/-- Numerals compute addition. -/
theorem numeral_add {n : Nat} (a b : Nat) :
    Derivable eraDefs ⟨(.numeral a : ETm n) +ᵉ .numeral b, .numeral (a + b)⟩ := by
  induction b with
  | zero => exact derivable_add_zero _
  | succ b ih => exact (derivable_add_succ _ _).trans (Derivable.succ_congr ih)

/-- Numerals compute the predecessor term `z ∸ 1`. -/
theorem numeral_pred {n : Nat} (a : Nat) :
    Derivable eraDefs ⟨(.numeral a : ETm n) ∸ᵉ one, .numeral (a - 1)⟩ := by
  cases a with
  | zero => exact derivable_pred_zero
  | succ a => exact derivable_pred_succ _

/-- Numerals compute truncated subtraction. -/
theorem numeral_sub {n : Nat} (a b : Nat) :
    Derivable eraDefs ⟨(.numeral a : ETm n) ∸ᵉ .numeral b, .numeral (a - b)⟩ := by
  induction b with
  | zero => exact derivable_sub_zero _
  | succ b ih =>
      exact (derivable_sub_succ _ _).trans
        ((bin_congr .tsub ih (.refl one)).trans (numeral_pred _))

/-- Numerals compute multiplication. -/
theorem numeral_mul {n : Nat} (a b : Nat) :
    Derivable eraDefs ⟨(.numeral a : ETm n) *ᵉ .numeral b, .numeral (a * b)⟩ := by
  induction b with
  | zero => exact derivable_mul_zero _
  | succ b ih =>
      exact (derivable_mul_succ _ _).trans
        ((bin_congr .add ih (.refl _)).trans (numeral_add _ _))

/-- Numerals compute exponentiation. -/
theorem numeral_pow {n : Nat} (a b : Nat) :
    Derivable eraDefs ⟨(.numeral a : ETm n) ^ᵉ .numeral b, .numeral (a ^ b)⟩ := by
  induction b with
  | zero => exact derivable_pow_zero _
  | succ b ih =>
      exact (derivable_pow_succ _ _).trans
        ((bin_congr .mul ih (.refl _)).trans (numeral_mul _ _))

/-- Numerals compute division, through the remainder-increment recurrence and
`succ_div_succ`. -/
theorem numeral_div {n : Nat} (a b : Nat) :
    Derivable eraDefs ⟨(.numeral a : ETm n) /ᵉ .numeral b, .numeral (a / b)⟩ := by
  cases b with
  | zero =>
      rw [Nat.div_zero]
      exact derivable_div_zero _
  | succ y =>
      induction a with
      | zero =>
          rw [Nat.zero_div]
          exact derivable_zero_div _
      | succ x ih =>
          rw [succ_div_succ]
          -- evaluate the remainder-increment term numeral-by-numeral, innermost first
          have hprod := (bin_congr .mul (.refl (.succ (.numeral y))) ih).trans
            (numeral_mul (y + 1) (x / (y + 1)))
          have hrem := (bin_congr .tsub (.refl (.numeral x)) hprod).trans
            (numeral_sub x ((y + 1) * (x / (y + 1))))
          have hgap := (bin_congr .tsub (.refl (.numeral y)) hrem).trans
            (numeral_sub y (x - (y + 1) * (x / (y + 1))))
          have hincr := (bin_congr .tsub (.refl one) hgap).trans
            (numeral_sub 1 (y - (x - (y + 1) * (x / (y + 1)))))
          exact (derivable_div_succ (.numeral x) (.numeral y)).trans
            ((bin_congr .add ih hincr).trans
              (numeral_add (x / (y + 1)) (1 - (y - (x - (y + 1) * (x / (y + 1)))))))

/-- Numeral normalization: every closed term is derivably equal to the numeral of its
value. -/
theorem closed_term_numeral (t : ETm 0) :
    Derivable eraDefs ⟨t, .numeral (t.eval eraInterp Fin.elim0)⟩ := by
  induction t with
  | var i => exact i.elim0
  | zero => exact .refl _
  | succ t ih => exact Derivable.succ_congr ih
  | app b ts ih =>
      rw [app_eq_bin b ts]
      cases b with
      | add => exact (bin_congr .add (ih _) (ih _)).trans (numeral_add _ _)
      | tsub => exact (bin_congr .tsub (ih _) (ih _)).trans (numeral_sub _ _)
      | mul => exact (bin_congr .mul (ih _) (ih _)).trans (numeral_mul _ _)
      | div => exact (bin_congr .div (ih _) (ih _)).trans (numeral_div _ _)
      | pow => exact (bin_congr .pow (ih _) (ih _)).trans (numeral_pow _ _)

/-- Completeness for closed equations: a closed equation that holds in the standard
model is derivable.  With `eraSound`, derivability of a closed equation coincides with
its truth in the standard model. -/
theorem eraClosedComplete {s t : ETm 0}
    (h : ∀ ρ : Fin 0 → Nat, s.eval eraInterp ρ = t.eval eraInterp ρ) :
    Derivable eraDefs ⟨s, t⟩ := by
  have hs := closed_term_numeral s
  rw [h Fin.elim0] at hs
  exact hs.trans (closed_term_numeral t).symm

end Era

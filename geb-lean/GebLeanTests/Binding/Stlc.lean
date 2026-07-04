import GebLean.Binding.Examples.Stlc
import GebLean.Binding.Laws

/-!
# Tests for the simply-typed lambda calculus acceptance test

The end-to-end acceptance test of the indexed binder-substitution kit
(decision 8): worked `example`s over `GebLean.Binding.stlcId` and
`GebLean.Binding.stlcBody` exercising `Tm.var`, `ren`, `sub`,
`instantiate₁`, and each law of the substitution-lemma suite (`sub_var`,
`sub_id`, `ren_sub`, `sub_ren`, `sub_sub`).
-/

namespace GebLean.Binding.Test

open GebLean.Binding

-- `Tm.var` — `stlcBody` is the variable term at the sole position of the
-- singleton context `[a]`.
example (a : StlcTy) : stlcBody a = Tm.var (⟨0, rfl⟩ : Var [a] a) := rfl

-- `ren` — renaming `stlcBody` along the weakening thinning shifts its
-- variable, as in the general renaming tests (`GebLeanTests.Binding.Renaming`).
example (a : StlcTy) :
    ren (S := stlcSig) (Thinning.weak (s := a)) (stlcBody a)
      = Tm.var ((Thinning.weak (s := a)).app (⟨0, rfl⟩ : Var [a] a)) := by
  simp [stlcBody, ren, renEnv, traverse_var, varKit]

-- `sub` — substituting `stlcBody` by the identity environment is the identity.
example (a : StlcTy) : sub (S := stlcSig) idEnv (stlcBody a) = stlcBody a := by
  simp [stlcBody, sub, idEnv, subKit, traverse_var]

-- `instantiate₁` — beta-instantiating the identity's body at a closed
-- argument returns the argument. `stlcBody a : Tm stlcSig [a] a :=
-- Tm.var ⟨0, rfl⟩`; here `Γ = []`, so `Γ ++ [a] = [a]`, and `instantiate₁`
-- returns the closed argument `u`.
example (a : StlcTy) (u : Tm stlcSig [] a) :
    instantiate₁ (Γ := []) (a := a) u (stlcBody a) = u := by
  simp only [stlcBody, instantiate₁, instantiate, sub, subKit]
  -- the sole bound variable is a `Fin` numeral literal that `Var.appendCases`
  -- resolves only by definitional reduction, not by a structural `simp` lemma
  rfl

-- The left-unit law `sub_var`, on the identity's bound variable.
example (a : StlcTy) {Δ : Ctx StlcTy} (σ : Env (Tm stlcSig) [a] Δ) :
    sub σ (stlcBody a) = σ a ⟨0, rfl⟩ :=
  sub_var σ ⟨0, rfl⟩

-- The right-unit law `sub_id`, on the closed identity term.
example (a : StlcTy) : sub idEnv (stlcId a) = stlcId a :=
  sub_id (stlcId a)

-- The ren-sub fusion law `ren_sub`, on the closed identity term.
example {Δ Θ : Ctx StlcTy} (ρ : Thinning ([] : Ctx StlcTy) Δ)
    (σ : Env (Tm stlcSig) Δ Θ) (a : StlcTy) :
    sub σ (ren ρ (stlcId a)) = sub (fun s x => σ s (ρ.app x)) (stlcId a) :=
  ren_sub ρ σ (stlcId a)

-- The sub-ren fusion law `sub_ren`, on the closed identity term.
example {Δ Θ : Ctx StlcTy} (σ : Env (Tm stlcSig) ([] : Ctx StlcTy) Δ)
    (ρ : Thinning Δ Θ) (a : StlcTy) :
    ren ρ (sub σ (stlcId a)) = sub (fun s x => ren ρ (σ s x)) (stlcId a) :=
  sub_ren σ ρ (stlcId a)

-- The associativity law `sub_sub`, on the closed identity term.
example {Δ Θ : Ctx StlcTy} (σ : Env (Tm stlcSig) ([] : Ctx StlcTy) Δ)
    (τ : Env (Tm stlcSig) Δ Θ) (a : StlcTy) :
    sub τ (sub σ (stlcId a)) = sub (fun s x => sub τ (σ s x)) (stlcId a) :=
  sub_sub σ τ (stlcId a)

end GebLean.Binding.Test

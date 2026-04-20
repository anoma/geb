import GebLean.LawvereERQuot
import GebLean.LawvereGodelTQuot
import GebLean.LawvereGodelTInterp
import GebLean.Utilities.ERArith
import Mathlib.CategoryTheory.Equivalence

/-!
# Categorical equivalence `LawvereGodelTCat ≃ LawvereERCat`

Back-translation `GodelTMor1.toER` is a direct structural
recursion with one named-ER case per constructor.  Forward
translation `ERMor1.toGodelT` similarly maps each ER
constructor to a `GodelTMor1` term, with `sub` built from
`disc` / `pred`.  Interp preservation holds
constructor-by-constructor; round-trip identities follow from
the two interp-preservation theorems.
-/

namespace GebLean

open CategoryTheory

/-- Back-translation from a `GodelTMor1 n` term to an
`ERMor1 n` term.  Each constructor maps to its named ER
backing: `ERMor1.zero` / `succ` / `pred` / `proj` / `discN` /
`bsum` / `bprod` / `comp`. -/
def GodelTMor1.toER : {n : ℕ} → GodelTMor1 n → ERMor1 n
  | _, .zero       => ERMor1.zero
  | _, .succ       => ERMor1.succ
  | _, .pred       => ERMor1.pred
  | _, .proj i     => ERMor1.proj i
  | _, .disc       => ERMor1.discN
  | _, .bsum f     => ERMor1.bsum f.toER
  | _, .bprod f    => ERMor1.bprod f.toER
  | _, .comp f g   =>
      ERMor1.comp f.toER (fun i => (g i).toER)

/-- Interp preservation of `toER`: structural induction whose
cases are either `rfl` or reduce to a matching ER simp lemma. -/
theorem GodelTMor1.toER_interp : {n : ℕ} → (t : GodelTMor1 n) →
    (ctx : Fin n → ℕ) → t.toER.interp ctx = t.interp ctx
  | _, .zero, _ => rfl
  | _, .succ, _ => rfl
  | _, .pred, _ => rfl
  | _, .proj _, _ => rfl
  | _, .disc, ctx => by
      change ERMor1.discN.interp ctx = _
      rw [ERMor1.interp_discN]
      change (if ctx 0 = 0 then ctx 1 else ctx 2) =
        (match ctx 0 with | 0 => ctx 1 | _ + 1 => ctx 2)
      by_cases h : ctx 0 = 0
      · simp [h]
      · rcases Nat.exists_eq_succ_of_ne_zero h with ⟨k, hk⟩
        simp [hk]
  | _, .bsum f, ctx => by
      change (ERMor1.bsum f.toER).interp ctx = _
      rw [ERMor1.interp_bsum]
      change natBSum _ _ = natBSum _ _
      congr 1
      funext i
      exact GodelTMor1.toER_interp f _
  | _, .bprod f, ctx => by
      change (ERMor1.bprod f.toER).interp ctx = _
      rw [ERMor1.interp_bprod]
      change natBProd _ _ = natBProd _ _
      congr 1
      funext i
      exact GodelTMor1.toER_interp f _
  | _, .comp f g, ctx => by
      change (ERMor1.comp f.toER (fun i => (g i).toER)).interp
          ctx = _
      rw [ERMor1.interp_comp, GodelTMor1.toER_interp f]
      congr 1
      funext i
      exact GodelTMor1.toER_interp (g i) ctx

end GebLean

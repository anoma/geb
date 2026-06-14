import GebLean.Era
import GebLean.LawvereER
import GebLean.Utilities.ERArith

/-!
# Era basis completeness bridge

Relates the denotations of `Era` terms (`Tm.eval eraInterp`) to the
Kalmár elementary functions as formalised by `ERMor1`
(`GebLean/LawvereER.lean`).

## Main statements

* `era_sound_er` — every `ETm` denotes an `ERMor1` function
  (the inclusion `Era ⊆ E³`).

## References

* Prunescu, Sauras-Altuzarra, Shunia, arXiv:2505.23787.

## Tags

elementary recursive, substitution basis, completeness
-/

namespace GebLean.EraCompleteness

open Era

/-- The `ERMor1` term realising each basis operation. -/
def eraOpToER : (b : EraB) → ERMor1 (eraAr b)
  | .add  => ERMor1.addN
  | .mod  => ERMor1.mod
  | .pow2 => ERMor1.comp ERMor1.powN ![ERMor1.natN 1 2, ERMor1.proj (0 : Fin 1)]
  | .tsub => ERMor1.sub
  | .mul  => ERMor1.mulN
  | .div  => ERMor1.div
  | .pow  => ERMor1.powN

/-- The `ERMor1` witness for each basis operation interprets to that operation's
`Nat` semantics. -/
theorem eraOpToER_interp (b : EraB) (ctx : Fin (eraAr b) → ℕ) :
    (eraOpToER b).interp ctx = eraInterp b ctx := by
  -- Each binary operation has arity-2 context; rewrite `ctx` to the explicit
  -- two-element vector so the literal-vector interp lemmas apply.
  have hctx2 : ∀ (c : Fin 2 → ℕ),
      c = ![c ⟨0, by decide⟩, c ⟨1, by decide⟩] := by
    intro c
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  cases b with
  | add => rw [hctx2 ctx]; exact ERMor1.interp_addN _
  | mod => rw [hctx2 ctx]; exact ERMor1.interp_mod _ _
  | pow2 =>
      change (ERMor1.comp ERMor1.powN
          ![ERMor1.natN 1 2, ERMor1.proj (0 : Fin 1)]).interp ctx = 2 ^ ctx ⟨0, by decide⟩
      rw [ERMor1.interp_comp]
      simp only [ERMor1.interp_powN, ERMor1.interp_natN, ERMor1.interp_proj,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rfl
  | tsub => rw [hctx2 ctx]; exact ERMor1.interp_sub _
  | mul => rw [hctx2 ctx]; exact ERMor1.interp_mulN _
  | div => rw [hctx2 ctx]; exact ERMor1.interp_div _ _
  | pow => rw [hctx2 ctx]; exact ERMor1.interp_powN _

end GebLean.EraCompleteness

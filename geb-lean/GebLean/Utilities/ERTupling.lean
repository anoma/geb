import GebLean.Utilities.Tupling
import GebLean.Utilities.ERArith

/-!
# ER-side fixed-length k-tuple Szudzik pairing

ER-level named composites mirroring `Nat.tuplePack` and
`Nat.tupleAt` in `Utilities/Tupling.lean`.  Bottom-up
construction from existing atomic ER generators (`proj`,
`natPair`, `natUnpairFst`, `natUnpairSnd`, `comp`) per
CLAUDE.md "bottom-up named-composite discipline".

See master design §3.1 (Lean entities, ER layer) and
the spec at
`docs/superpowers/specs/2026-05-02-step-1-er-tupling-design.md`.
-/

namespace GebLean
namespace ERMor1

/-- ER named composite for fixed-length `(k + 1)`-tuple
Szudzik pack.  Built bottom-up from `proj`, `natPair`,
`comp` per CLAUDE.md "bottom-up named-composite
discipline".  Mirrors `Nat.tuplePack`'s left-fold
recurrence (master design §3.1; Tourlakis 2018 §0.1.0.34,
p. 14). -/
def tuplePack : (k : ℕ) → ERMor1 (k + 1)
  | 0     => ERMor1.proj 0
  | k + 1 =>
      ERMor1.comp ERMor1.natPair
        ![ ERMor1.comp (tuplePack k)
             (fun i : Fin (k + 1) =>
               ERMor1.proj i.castSucc)
         , ERMor1.proj (Fin.last (k + 1)) ]

/-- ER named composite extracting component `i` from a
packed `(k + 1)`-tuple.  Built bottom-up from `proj`,
`natUnpairFst`, `natUnpairSnd`, `comp`.  Mirrors
`Nat.tupleAt`'s left-fold recurrence (master design §3.1;
Tourlakis 2018 §0.1.0.34, p. 14, with index orientation
matched to the inverse of the left-fold recurrence). -/
def tupleAt : (k : ℕ) → Fin (k + 1) → ERMor1 1
  | 0,     _ => ERMor1.proj 0
  | k + 1, i =>
      Fin.lastCases
        (motive := fun _ : Fin (k + 2) => ERMor1 1)
        ERMor1.natUnpairSnd
        (fun j : Fin (k + 1) =>
          ERMor1.comp (tupleAt k j) ![ERMor1.natUnpairFst])
        i

/-- Interpretation alignment for `tuplePack`: the ER named
composite computes Tourlakis 2018 §0.1.0.34, p. 14's
`[[z_1,…,z_{k+1}]]^{(k+1)}` Szudzik pack of its argument.
Master design §3.1. -/
@[simp] theorem interp_tuplePack :
    ∀ (k : ℕ) (v : Fin (k + 1) → ℕ),
      (tuplePack k).interp v = Nat.tuplePack k v
  | 0, v => by
      simp only [tuplePack, ERMor1.interp_proj, Nat.tuplePack]
  | k + 1, v => by
      simp only [tuplePack, ERMor1.interp_comp]
      have ih := interp_tuplePack k
        (fun i : Fin (k + 1) => v i.castSucc)
      have hshift :
          (fun i : Fin (k + 1) => v i.castSucc)
            = Fin.init v := by
        funext i
        rfl
      rw [hshift] at ih
      have hctx :
          (fun i : Fin 2 =>
              (![(tuplePack k).comp
                  (fun i : Fin (k + 1) =>
                    ERMor1.proj i.castSucc),
                 ERMor1.proj (Fin.last (k + 1))] i).interp v)
            = ![Nat.tuplePack k (Fin.init v),
                 v (Fin.last (k + 1))] := by
        funext x
        match x with
        | ⟨0, _⟩ =>
            change ((tuplePack k).comp
                (fun i : Fin (k + 1) =>
                  ERMor1.proj i.castSucc)).interp v
              = Nat.tuplePack k (Fin.init v)
            simp only [ERMor1.interp_comp,
              ERMor1.interp_proj]
            exact ih
        | ⟨1, _⟩ =>
            change (ERMor1.proj (Fin.last (k + 1))).interp v
              = v (Fin.last (k + 1))
            simp only [ERMor1.interp_proj]
      rw [hctx, ERMor1.interp_natPair, Nat.tuplePack]

/-- Interpretation alignment for `tupleAt`: the ER named
composite computes Tourlakis 2018 §0.1.0.34, p. 14's
`Π^{k+1}_i` projection of its argument.  Master design
§3.1. -/
@[simp] theorem interp_tupleAt :
    ∀ (k : ℕ) (i : Fin (k + 1)) (n : ℕ),
      (tupleAt k i).interp ![n] = Nat.tupleAt k n i
  | 0, _, n => by
      simp only [tupleAt, ERMor1.interp_proj, Nat.tupleAt,
        Matrix.cons_val_zero]
  | k + 1, i, n => by
      refine Fin.lastCases ?_ ?_ i
      · simp only [tupleAt, Fin.lastCases_last,
          ERMor1.interp_natUnpairSnd, Nat.tupleAt_succ_last]
      · intro j
        simp only [tupleAt, Fin.lastCases_castSucc,
          ERMor1.interp_comp, Nat.tupleAt_succ_castSucc]
        have ih := interp_tupleAt k j (Nat.unpair n).1
        have hctx :
            (fun i : Fin 1 =>
              (![ERMor1.natUnpairFst] i).interp
                (![n] : Fin 1 → ℕ))
              = ![(Nat.unpair n).1] := by
          funext x
          match x with
          | ⟨0, _⟩ =>
              change ERMor1.natUnpairFst.interp ![n]
                = (Nat.unpair n).1
              exact ERMor1.interp_natUnpairFst n
        rw [hctx]
        exact ih

end ERMor1
end GebLean

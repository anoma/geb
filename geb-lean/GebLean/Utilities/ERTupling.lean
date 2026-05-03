import GebLean.LawvereERPolynomialBound
import GebLean.Utilities.ERArith
import GebLean.Utilities.Tupling

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
    ∀ (k : ℕ) (i : Fin (k + 1)) (ctx : Fin 1 → ℕ),
      (tupleAt k i).interp ctx = Nat.tupleAt k (ctx 0) i
  | 0, _, ctx => by
      simp only [tupleAt, ERMor1.interp_proj, Nat.tupleAt]
  | k + 1, i, ctx => by
      have hctx_eq : ctx = ![ctx 0] := by
        funext x
        match x with
        | ⟨0, _⟩ => rfl
      refine Fin.lastCases ?_ ?_ i
      · rw [hctx_eq]
        simp only [tupleAt, Fin.lastCases_last,
          ERMor1.interp_natUnpairSnd, Nat.tupleAt_succ_last,
          Matrix.cons_val_zero]
      · intro j
        simp only [tupleAt, Fin.lastCases_castSucc,
          ERMor1.interp_comp, Nat.tupleAt_succ_castSucc]
        have ih := interp_tupleAt k j ![(Nat.unpair (ctx 0)).1]
        have hctx :
            (fun i : Fin 1 =>
              (![ERMor1.natUnpairFst] i).interp ctx)
              = ![(Nat.unpair (ctx 0)).1] := by
          funext x
          match x with
          | ⟨0, _⟩ =>
              change ERMor1.natUnpairFst.interp ctx
                = (Nat.unpair (ctx 0)).1
              rw [hctx_eq]
              exact ERMor1.interp_natUnpairFst (ctx 0)
        rw [hctx]
        simpa using ih

namespace PolyBound

/-- PolyBound builder for `tuplePack k`.  Cites master
design §3.1: `tuplePack k v ≤ tuplePackCoef k * (M+1)^(2^k)`. -/
def ofTuplePack (k : ℕ) :
    PolyBound (tuplePack k) where
  degree := 2 ^ k
  coefficient := Nat.tuplePackCoef k
  constant := 0
  bounds := fun ctx => by
    rw [interp_tuplePack]
    simpa using Nat.tuplePack_le k ctx

/-- PolyBound builder for `tupleAt k i`.  Linear bound
from `Nat.tupleAt_le` (single-arity context); master
design §3.1. -/
def ofTupleAt (k : ℕ) (i : Fin (k + 1)) :
    PolyBound (tupleAt k i) where
  degree := 1
  coefficient := 1
  constant := 0
  bounds := fun ctx => by
    rw [interp_tupleAt]
    have h := Nat.tupleAt_le k (ctx 0) i
    have hsup :
        ctx 0 ≤ (Finset.univ : Finset (Fin 1)).sup ctx :=
      Finset.le_sup (f := ctx) (Finset.mem_univ 0)
    simp only [pow_one, one_mul, Nat.add_zero]
    omega

end PolyBound

end ERMor1

namespace ERMorN

/-- One-element vector view of a single-output ER term.
`ERMorN.lift f i = f` for the unique `i : Fin 1`.
Auxiliary helper supporting the `ERMorN`-quotient
round-trip lemmas named in master design §3.1; bridges
single-output `ERMor1.tuplePack` to the multi-output
`ERMorN` interface on which the round-trip equation is
stated. -/
def lift {n : ℕ} (f : ERMor1 n) : ERMorN n 1 :=
  fun _ => f

/-- Named identity coercion from a vector of single-output
ER terms to the multi-output `ERMorN`.  Definitionally `g`,
since `ERMorN n m := Fin m → ERMor1 n`.  Auxiliary helper
supporting the round-trip lemmas named in master design
§3.1; gives the `Fin (k + 1) → ERMor1 1` family of
`tupleAt` projections a stable `ERMorN 1 (k + 1)` interface
for the quotient-level lemma signatures. -/
def ofVec {n m : ℕ} (g : Fin m → ERMor1 n) :
    ERMorN n m := g

@[simp] theorem lift_apply {n : ℕ} (f : ERMor1 n)
    (i : Fin 1) :
    ERMorN.lift f i = f := rfl

@[simp] theorem ofVec_apply {n m : ℕ}
    (g : Fin m → ERMor1 n) (i : Fin m) :
    ERMorN.ofVec g i = g i := rfl

end ERMorN

end GebLean

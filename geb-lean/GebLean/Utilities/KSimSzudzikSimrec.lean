import GebLean.LawvereER
import GebLean.LawvereERBoundComputable
import GebLean.Utilities.ERArith
import GebLean.Utilities.SzudzikSeq

/-!
# Szudzik-based simrec helpers for `kToER`

ER-side combinators packing a `(k+1)`-tuple of ER values
into a single ℕ via iterated right-associated Szudzik
pairing, the inverse component-extraction term, and the
packed base/step builders for translating a K^sim
`simrec` term to an `ERMor1` term using
`ERMor1.boundedRec`.

The pack/unpack ER terms compose `ERMor1.natPair`,
`ERMor1.natUnpairFst`, and `ERMor1.natUnpairSnd` per the
sequence-encoding rules of `Nat.seqPack` and
`Nat.seqAt` from `Utilities/SzudzikSeq.lean`.

See `docs/plans/2026-04-29-lawvere-k-sim-ktoer-design.md`,
component C5.
-/

namespace GebLean

/-- Pack a `(k + 1)`-tuple of ER terms into a single ER
term whose interp is the iterated right-associated
Szudzik pairing of the tuple's interps, terminated with
`0` (mirroring `Nat.seqPack`). -/
def kSimSzudzikPackList :
    {a k : ℕ} → (Fin (k + 1) → ERMor1 a) → ERMor1 a
  | a, 0,     t =>
      ERMor1.comp ERMor1.succ
        (fun (_ : Fin 1) =>
          ERMor1.comp ERMor1.natPair
            (fun i => match i with
              | ⟨0, _⟩ => t 0
              | ⟨1, _⟩ => ERMor1.zeroN a))
  | a, k + 1, t =>
      ERMor1.comp ERMor1.succ
        (fun (_ : Fin 1) =>
          ERMor1.comp ERMor1.natPair
            (fun i => match i with
              | ⟨0, _⟩ => t 0
              | ⟨1, _⟩ =>
                  kSimSzudzikPackList (a := a) (k := k)
                    (fun j => t j.succ)))

@[simp] theorem kSimSzudzikPackList_zero_interp {a : ℕ}
    (t : Fin 1 → ERMor1 a) (ctx : Fin a → ℕ) :
    (kSimSzudzikPackList (k := 0) t).interp ctx =
      Nat.pair ((t 0).interp ctx) 0 + 1 := by
  unfold kSimSzudzikPackList
  rw [ERMor1.interp_comp, ERMor1.interp_succ]
  change (ERMor1.natPair.interp _) + 1 = _
  rw [show (fun (i : Fin 2) =>
        (match i with
          | ⟨0, _⟩ => t 0
          | ⟨1, _⟩ => ERMor1.zeroN a : ERMor1 a).interp ctx) =
      ![(t 0).interp ctx, 0] from by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ =>
        change (ERMor1.zeroN a).interp ctx = _
        simp]
  rw [ERMor1.interp_natPair]

@[simp] theorem kSimSzudzikPackList_succ_interp
    {a k : ℕ} (t : Fin (k + 2) → ERMor1 a)
    (ctx : Fin a → ℕ) :
    (kSimSzudzikPackList (k := k + 1) t).interp ctx =
      Nat.pair ((t 0).interp ctx)
        ((kSimSzudzikPackList (k := k)
          (fun j => t j.succ)).interp ctx) + 1 := by
  conv_lhs => unfold kSimSzudzikPackList
  rw [ERMor1.interp_comp, ERMor1.interp_succ]
  change (ERMor1.natPair.interp _) + 1 = _
  rw [show (fun (i : Fin 2) =>
        (match i with
          | ⟨0, _⟩ => t 0
          | ⟨1, _⟩ =>
              kSimSzudzikPackList (a := a) (k := k)
                (fun j => t j.succ) : ERMor1 a).interp ctx) =
      ![(t 0).interp ctx,
        (kSimSzudzikPackList (a := a) (k := k)
          (fun j => t j.succ)).interp ctx] from by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl]
  rw [ERMor1.interp_natPair]

/-- Interpretation of `kSimSzudzikPackList` equals
`Nat.seqPack` applied to the list of component interps. -/
theorem kSimSzudzikPackList_interp :
    {a k : ℕ} → (t : Fin (k + 1) → ERMor1 a) →
      (ctx : Fin a → ℕ) →
      (kSimSzudzikPackList t).interp ctx =
        Nat.seqPack
          ((List.finRange (k + 1)).map
            (fun j => (t j).interp ctx))
  | _, 0,     t, ctx => by
      rw [kSimSzudzikPackList_zero_interp]
      simp [List.finRange, Nat.seqPack]
  | _, k + 1, t, ctx => by
      rw [kSimSzudzikPackList_succ_interp]
      rw [kSimSzudzikPackList_interp (k := k)
        (fun j => t j.succ) ctx]
      simp [List.finRange_succ, List.map_cons,
        Nat.seqPack]
      rfl

end GebLean

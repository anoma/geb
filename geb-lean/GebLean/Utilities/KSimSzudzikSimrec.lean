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

/-- Component selector: `unpackAt a i` is an ER term of
arity `a + 1` whose interp at `Fin.cons packed ctx`
returns `Nat.seqAt packed i`.  The recursion descends
through `i` peeling off Szudzik pairs via
`natUnpairSnd`, then takes a `natUnpairFst` at the
target depth.  The leading `pred` strips the `+ 1`
introduced by `Nat.seqPack`. -/
def kSimSzudzikUnpackAt : (a : ℕ) → (i : ℕ) →
    ERMor1 (a + 1)
  | a, 0     =>
      ERMor1.comp ERMor1.natUnpairFst
        (fun (_ : Fin 1) =>
          ERMor1.comp ERMor1.pred
            (fun (_ : Fin 1) =>
              ERMor1.proj (k := a + 1) ⟨0, by omega⟩))
  | a, i + 1 =>
      ERMor1.comp (kSimSzudzikUnpackAt a i)
        (fun j =>
          if h : j.val = 0 then
            ERMor1.comp ERMor1.natUnpairSnd
              (fun (_ : Fin 1) =>
                ERMor1.comp ERMor1.pred
                  (fun (_ : Fin 1) =>
                    ERMor1.proj (k := a + 1)
                      ⟨0, by omega⟩))
          else
            ERMor1.proj (k := a + 1)
              ⟨j.val, by
                have := j.isLt; omega⟩)

/-- Auxiliary: interpretation of the leaf
`natUnpairFst ∘ pred ∘ proj 0` against
`Fin.cons packed ctx`. -/
theorem kSimSzudzikUnpackAt_leafFst_interp
    {a : ℕ} (packed : ℕ) (ctx : Fin a → ℕ) :
    (ERMor1.comp ERMor1.natUnpairFst
      (fun (_ : Fin 1) =>
        ERMor1.comp ERMor1.pred
          (fun (_ : Fin 1) =>
            ERMor1.proj (k := a + 1)
              ⟨0, by omega⟩))).interp
        (Fin.cons packed ctx) =
      (Nat.unpair packed.pred).1 := by
  rw [ERMor1.interp_comp]
  have hinner :
      (fun (_ : Fin 1) =>
        (ERMor1.comp ERMor1.pred
          (fun (_ : Fin 1) =>
            ERMor1.proj (k := a + 1)
              ⟨0, by omega⟩)).interp
            (Fin.cons packed ctx)) =
        ![packed.pred] := by
    funext j
    match j with
    | ⟨0, _⟩ =>
        rw [ERMor1.interp_comp]
        have hproj :
            (fun (_ : Fin 1) =>
              (ERMor1.proj (k := a + 1)
                ⟨0, by omega⟩).interp
                (Fin.cons packed ctx)) =
              ![packed] := by
          funext j2
          match j2 with
          | ⟨0, _⟩ => rfl
        rw [hproj, ERMor1.interp_pred]
        rfl
  rw [hinner, ERMor1.interp_natUnpairFst]

/-- Auxiliary: interpretation of the descent leaf
`natUnpairSnd ∘ pred ∘ proj 0` against
`Fin.cons packed ctx`. -/
theorem kSimSzudzikUnpackAt_leafSnd_interp
    {a : ℕ} (packed : ℕ) (ctx : Fin a → ℕ) :
    (ERMor1.comp ERMor1.natUnpairSnd
      (fun (_ : Fin 1) =>
        ERMor1.comp ERMor1.pred
          (fun (_ : Fin 1) =>
            ERMor1.proj (k := a + 1)
              ⟨0, by omega⟩))).interp
        (Fin.cons packed ctx) =
      (Nat.unpair packed.pred).2 := by
  rw [ERMor1.interp_comp]
  have hinner :
      (fun (_ : Fin 1) =>
        (ERMor1.comp ERMor1.pred
          (fun (_ : Fin 1) =>
            ERMor1.proj (k := a + 1)
              ⟨0, by omega⟩)).interp
            (Fin.cons packed ctx)) =
        ![packed.pred] := by
    funext j
    match j with
    | ⟨0, _⟩ =>
        rw [ERMor1.interp_comp]
        have hproj :
            (fun (_ : Fin 1) =>
              (ERMor1.proj (k := a + 1)
                ⟨0, by omega⟩).interp
                (Fin.cons packed ctx)) =
              ![packed] := by
          funext j2
          match j2 with
          | ⟨0, _⟩ => rfl
        rw [hproj, ERMor1.interp_pred]
        rfl
  rw [hinner, ERMor1.interp_natUnpairSnd]

/-- Interpretation of `kSimSzudzikUnpackAt`: extracting
the `i`-th component from a packed value. -/
theorem kSimSzudzikUnpackAt_interp_eq_seqAt :
    {a : ℕ} → (i : ℕ) → (packed : ℕ) →
      (ctx : Fin a → ℕ) →
      (kSimSzudzikUnpackAt a i).interp
          (Fin.cons packed ctx) =
        Nat.seqAt packed i
  | _, 0,     0,     _   => by
      unfold kSimSzudzikUnpackAt
      rw [kSimSzudzikUnpackAt_leafFst_interp]
      rfl
  | _, 0,     n + 1, _   => by
      unfold kSimSzudzikUnpackAt
      rw [kSimSzudzikUnpackAt_leafFst_interp]
      rfl
  | _, i + 1, 0,     ctx => by
      unfold kSimSzudzikUnpackAt
      rw [ERMor1.interp_comp]
      have hzero :
          (fun j : Fin (_ + 1) =>
            (if h : j.val = 0 then
                ERMor1.comp ERMor1.natUnpairSnd
                  (fun (_ : Fin 1) =>
                    ERMor1.comp ERMor1.pred
                      (fun (_ : Fin 1) =>
                        ERMor1.proj (k := _ + 1)
                          ⟨0, by omega⟩))
              else
                ERMor1.proj (k := _ + 1)
                  ⟨j.val, by
                    have := j.isLt; omega⟩).interp
                (Fin.cons 0 ctx)) =
            Fin.cons 0 ctx := by
        funext j
        by_cases h : j.val = 0
        · simp only [h, dif_pos]
          rw [kSimSzudzikUnpackAt_leafSnd_interp]
          have h0 : j = ⟨0, by omega⟩ := Fin.ext h
          rw [h0]
          rfl
        · rcases j with ⟨jv, hjv⟩
          cases jv with
          | zero => exact absurd rfl h
          | succ jv' =>
              simp only [h, dif_neg, not_false_eq_true]
              rw [ERMor1.interp_proj]
      rw [hzero]
      rw [kSimSzudzikUnpackAt_interp_eq_seqAt
        (a := _) (i := i) (packed := 0) (ctx := ctx)]
      simp
  | a, i + 1, n + 1, ctx => by
      unfold kSimSzudzikUnpackAt
      rw [ERMor1.interp_comp]
      have hstep :
          (fun j : Fin (a + 1) =>
            (if h : j.val = 0 then
                ERMor1.comp ERMor1.natUnpairSnd
                  (fun (_ : Fin 1) =>
                    ERMor1.comp ERMor1.pred
                      (fun (_ : Fin 1) =>
                        ERMor1.proj (k := a + 1)
                          ⟨0, by omega⟩))
              else
                ERMor1.proj (k := a + 1)
                  ⟨j.val, by
                    have := j.isLt; omega⟩).interp
                (Fin.cons (n + 1) ctx)) =
            Fin.cons (Nat.unpair n).2 ctx := by
        funext j
        by_cases h : j.val = 0
        · simp only [h, dif_pos]
          rw [kSimSzudzikUnpackAt_leafSnd_interp]
          have h0 : j = ⟨0, by omega⟩ := Fin.ext h
          rw [h0]
          rfl
        · rcases j with ⟨jv, hjv⟩
          cases jv with
          | zero => exact absurd rfl h
          | succ jv' =>
              simp only [h, dif_neg, not_false_eq_true]
              rw [ERMor1.interp_proj]
              have hjv' : jv' < a := by omega
              change (Fin.cons (n + 1) ctx :
                  Fin (a + 1) → ℕ)
                  (Fin.succ ⟨jv', hjv'⟩) =
                (Fin.cons (Nat.unpair n).2 ctx :
                  Fin (a + 1) → ℕ)
                  (Fin.succ ⟨jv', hjv'⟩)
              rw [Fin.cons_succ, Fin.cons_succ]
      rw [hstep,
        kSimSzudzikUnpackAt_interp_eq_seqAt
          (a := a) (i := i)
          (packed := (Nat.unpair n).2) (ctx := ctx)]
      rfl

end GebLean

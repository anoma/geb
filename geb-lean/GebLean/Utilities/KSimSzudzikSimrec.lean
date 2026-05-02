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

/-- Round-trip: extracting the `i`-th component of a
Szudzik-packed family recovers the `i`-th component's
interpretation. -/
theorem kSimSzudzikUnpackAt_packList {a k : ℕ}
    (t : Fin (k + 1) → ERMor1 a) (i : Fin (k + 1))
    (ctx : Fin a → ℕ) :
    (kSimSzudzikUnpackAt a i.val).interp
        (Fin.cons
          ((kSimSzudzikPackList t).interp ctx) ctx) =
      (t i).interp ctx := by
  rw [kSimSzudzikUnpackAt_interp_eq_seqAt,
    kSimSzudzikPackList_interp]
  have hlen :
      ((List.finRange (k + 1)).map
        (fun j => (t j).interp ctx)).length = k + 1 := by
    simp
  rw [Nat.seqAt_seqPack
    (xs := (List.finRange (k + 1)).map
      (fun j => (t j).interp ctx))
    (i := i.val) (h := by rw [hlen]; exact i.isLt)]
  simp

/-- Base-family packer for `simrec` translation: packs
the family `h : Fin (k + 1) → ERMor1 a` into a single
`ERMor1 a` whose interp at `ctx` Szudzik-packs the
component interps. -/
def kSimPackedBase {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a) : ERMor1 a :=
  kSimSzudzikPackList h

@[simp] theorem kSimPackedBase_interp {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a) (ctx : Fin a → ℕ) :
    (kSimPackedBase h).interp ctx =
      Nat.seqPack
        ((List.finRange (k + 1)).map
          (fun j => (h j).interp ctx)) :=
  kSimSzudzikPackList_interp h ctx

/-- Context substitution family for the simrec packed
step.  Translates each slot `idx : Fin (a + 1 + (k + 1))`
of the K^sim step's input context into an ER expression
of arity `a + 2`.  Slot 0 is the iteration index;
slots 1..a are parameters drawn from ER slots 2..a+1;
slots a+1..a+k+1 unpack components 0..k of the packed
previous value (ER slot 1) via `kSimSzudzikUnpackAt`. -/
def kSimStepContext {a k : ℕ} :
    Fin (a + 1 + (k + 1)) → ERMor1 (a + 2) :=
  fun idx =>
    if h₀ : idx.val = 0 then
      ERMor1.proj (k := a + 2) ⟨0, by omega⟩
    else if h₁ : idx.val < a + 1 then
      ERMor1.proj (k := a + 2)
        ⟨idx.val + 1, by
          have := idx.isLt; omega⟩
    else
      ERMor1.comp
        (kSimSzudzikUnpackAt a (idx.val - (a + 1)))
        (fun j =>
          if h : j.val = 0 then
            ERMor1.proj (k := a + 2) ⟨1, by omega⟩
          else
            ERMor1.proj (k := a + 2)
              ⟨j.val + 1, by
                have := j.isLt; omega⟩)

/-- Step-family packer for `simrec` translation: at
ambient context `(j, prev, ȳ)`, applies each `g_j_ER`
to the K^sim step context built by `kSimStepContext`
and Szudzik-packs the resulting `(k + 1)`-vector. -/
def kSimPackedStep {a k : ℕ}
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    ERMor1 (a + 2) :=
  kSimSzudzikPackList
    (fun j =>
      ERMor1.comp (g j) kSimStepContext)

@[simp] theorem kSimPackedStep_interp {a k : ℕ}
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (ctx : Fin (a + 2) → ℕ) :
    (kSimPackedStep g).interp ctx =
      Nat.seqPack
        ((List.finRange (k + 1)).map
          (fun j =>
            (g j).interp
              (fun idx =>
                kSimStepContext idx |>.interp ctx))) := by
  unfold kSimPackedStep
  rw [kSimSzudzikPackList_interp]
  simp only [ERMor1.interp_comp]

/-- Bound term for the simrec packed recursion's
`boundedRec`.  Uses `iterAutoBoundExpr` parameterised by
the tower height of the packed step term and the tower
height of the packed base term.  The dominance argument
is supplied at the call site (in the simrec case of
`kToER_interp`).

Realizes Claim 4 Fix B part 2 (research doc): the explicit
ER bound term shape `tower h_e (linear)` matching
Recursion Class Ch. 4 Prop. 4.7's iterated bound for the
n = 1 (linear step ⇒ polynomial output) and n = 2
(polynomial step ⇒ tower output) cases.  The height
parameters are the structural towerHeights of the step
and base, supplying the analytical bound height required
by Prop. 4.6 / Prop. 4.7 chaining. -/
def kSimTowerBound {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    ERMor1 (a + 1) :=
  ERMor1.iterAutoBoundExpr a
    (kSimPackedStep g).towerHeight
    (kSimPackedBase h).towerHeight

@[simp] theorem kSimTowerBound_interp {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (ctx : Fin (a + 1) → ℕ) :
    (kSimTowerBound h g).interp ctx =
      tower ((kSimPackedStep g).towerHeight + 1)
        ((kSimPackedStep g).towerHeight + 1 +
          2 * (kSimPackedBase h).towerHeight +
          2 * ((ERMor1.sumCtxER (a + 1)).interp ctx) +
          2) := by
  unfold kSimTowerBound
  exact ERMor1.interp_iterAutoBoundExpr _ _ _

/-- The bound is non-decreasing as the iteration counter
(slot 0) grows.  Used at the call site to discharge
`boundedRec_eq_natRec_of_bounded`'s monotonicity
hypothesis. -/
theorem kSimTowerBound_mono_counter {a k : ℕ}
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (j j' : ℕ) (params : Fin a → ℕ)
    (hj : j ≤ j') :
    (kSimTowerBound h g).interp (Fin.cons j params) ≤
      (kSimTowerBound h g).interp
        (Fin.cons j' params) := by
  rw [kSimTowerBound_interp, kSimTowerBound_interp]
  apply tower_mono_right
  rw [ERMor1.interp_sumCtxER, ERMor1.interp_sumCtxER]
  rw [Fin.sum_univ_succ (f := Fin.cons j params),
    Fin.sum_univ_succ (f := Fin.cons j' params)]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have hsum :
      2 * (j + (Finset.univ : Finset (Fin a)).sum params) =
        2 * j + 2 *
          (Finset.univ : Finset (Fin a)).sum params := by ring
  have hsum' :
      2 * (j' + (Finset.univ : Finset (Fin a)).sum params) =
        2 * j' + 2 *
          (Finset.univ : Finset (Fin a)).sum params := by ring
  omega

end GebLean

import GebLean.Utilities.ERArith
import GebLean.Utilities.SzudzikSeq
import GebLean.LawvereNatBT

/-!
# ER-Derived BTL Operations

`ERMor1`-level versions of `BTL.encode` (leaf and node cases)
and `BTL.fold`-on-Gödel-code.  The encode primitives are direct
closed-form arithmetic; the fold-on-code combinator builds on
`ERMor1.boundedRec` plus a Gödel β-encoded fold table.

Used by Stage β Task 14's back-translation.
-/

namespace GebLean

/-- The constant `2` as an `n`-ary ER term: applies `succ`
twice to `zeroN n`. -/
def ERMor1.twoN (n : ℕ) : ERMor1 n :=
  ERMor1.comp ERMor1.succ
    (fun (_ : Fin 1) => ERMor1.oneN n)

/-- Interpretation of `twoN`: always returns `2`. -/
@[simp] theorem ERMor1.interp_twoN
    {n : ℕ} (ctx : Fin n → ℕ) :
    (ERMor1.twoN n).interp ctx = 2 :=
  rfl

/-- ER-derived `BTL.encode` of a leaf: `btlEncodeLeaf ![lbl]`
returns `2 * lbl`, matching `BTL.encode (BTL.leaf lbl)`. -/
def ERMor1.btlEncodeLeaf : ERMor1 1 :=
  ERMor1.comp ERMor1.mulN
    (fun i => match i with
      | ⟨0, _⟩ => ERMor1.twoN 1
      | ⟨1, _⟩ => ERMor1.proj 0)

/-- Interpretation of `btlEncodeLeaf`: matches
`BTL.encode (BTL.leaf lbl)`. -/
@[simp] theorem ERMor1.interp_btlEncodeLeaf (lbl : ℕ) :
    ERMor1.btlEncodeLeaf.interp ![lbl] =
      BTL.encode (BTL.leaf lbl) := by
  unfold ERMor1.btlEncodeLeaf
  simp only [ERMor1.interp_comp, ERMor1.interp_mulN,
    ERMor1.interp_twoN, ERMor1.interp_proj,
    BTL.encode, Matrix.cons_val_zero]

/-- ER-derived `BTL.encode` for a node, with pre-encoded child
codes.  `btlEncodeNode ![l, r]` returns
`2 * Nat.pair l r + 1`, matching
`BTL.encode (BTL.node t_l t_r)` when `l = BTL.encode t_l` and
`r = BTL.encode t_r`. -/
def ERMor1.btlEncodeNode : ERMor1 2 :=
  ERMor1.comp ERMor1.succ
    (fun (_ : Fin 1) =>
      ERMor1.comp ERMor1.mulN
        (fun i => match i with
          | ⟨0, _⟩ => ERMor1.twoN 2
          | ⟨1, _⟩ =>
              ERMor1.comp ERMor1.natPair
                (fun j => match j with
                  | ⟨0, _⟩ => ERMor1.proj 0
                  | ⟨1, _⟩ => ERMor1.proj 1)))

/-- Interpretation of `btlEncodeNode`: given pre-encoded child
codes, produces the parent node's code. -/
@[simp] theorem ERMor1.interp_btlEncodeNode (l r : ℕ) :
    ERMor1.btlEncodeNode.interp ![l, r] =
      2 * Nat.pair l r + 1 := by
  have hpair : ERMor1.natPair.interp ![l, r] =
      Nat.pair l r := ERMor1.interp_natPair l r
  unfold ERMor1.btlEncodeNode
  simp only [ERMor1.interp_comp, ERMor1.interp_succ,
    ERMor1.interp_mulN, ERMor1.interp_twoN]
  change 2 * ERMor1.natPair.interp ![l, r] + 1 =
      2 * Nat.pair l r + 1
  rw [hpair]

/-! ### ER-derived fold on a BTL Gödel code

The `foldBTLOnCode` combinator runs `Nat.foldBTLOnCode` as a
single bounded search for a Gödel β-witness whose values at
positions `0 ≤ j ≤ code` match the fold trace.  At even
positions the recurrence applies `baseLeaf` to the label
`j / 2`; at odd positions it applies `stepNode` to the β-values
at `(j / 2).unpair.1` and `(j / 2).unpair.2`.  Correctness holds
under the same adequacy hypotheses as
`ERMor1.boundedRec`: a user-supplied ER bound `bound` must
pointwise dominate the trace and be monotone in the counter. -/

/-- β-extraction at a body position `j` at arity `k + 3` with
`cand` in slot `1`.  The inner argument `iTerm` supplies the
third β argument. -/
def ERMor1.betaOnCandFold {k : ℕ}
    (iTerm : ERMor1 (k + 3)) : ERMor1 (k + 3) :=
  ERMor1.comp ERMor1.beta (fun j => match j with
    | ⟨0, _⟩ =>
        ERMor1.comp ERMor1.natUnpairFst
          (fun (_ : Fin 1) => ERMor1.proj 1)
    | ⟨1, _⟩ =>
        ERMor1.comp ERMor1.natUnpairSnd
          (fun (_ : Fin 1) => ERMor1.proj 1)
    | ⟨2, _⟩ => iTerm)

/-- Interpretation of `betaOnCandFold iTerm` at
`Fin.cons j (Fin.cons cand (Fin.cons code ctx))`. -/
theorem ERMor1.interp_betaOnCandFold {k : ℕ}
    (iTerm : ERMor1 (k + 3)) (j cand code : ℕ)
    (ctx : Fin k → ℕ) :
    (ERMor1.betaOnCandFold iTerm).interp
        (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) =
      cand.unpair.1 %
        (1 + (iTerm.interp
          (Fin.cons j
            (Fin.cons cand (Fin.cons code ctx))) + 1) *
            cand.unpair.2) := by
  have hconv : (fun (_ : Fin 1) => cand) = ![cand] := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
  set iVal :=
    iTerm.interp
      (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) with _
  have hrew :
      (ERMor1.betaOnCandFold iTerm).interp
          (Fin.cons j
            (Fin.cons cand (Fin.cons code ctx))) =
        ERMor1.beta.interp
          ![cand.unpair.1, cand.unpair.2, iVal] := by
    unfold ERMor1.betaOnCandFold
    change ERMor1.beta.interp _ = ERMor1.beta.interp _
    congr 1
    funext p
    match p with
    | ⟨0, _⟩ =>
      change ERMor1.natUnpairFst.interp
          (fun (_ : Fin 1) =>
            (Fin.cons j (Fin.cons cand
              (Fin.cons code ctx)) :
                Fin (k + 3) → ℕ) 1) = _
      have hcand :
          (Fin.cons j (Fin.cons cand (Fin.cons code ctx)) :
            Fin (k + 3) → ℕ) 1 = cand := rfl
      rw [hcand, hconv, ERMor1.interp_natUnpairFst]
      rfl
    | ⟨1, _⟩ =>
      change ERMor1.natUnpairSnd.interp
          (fun (_ : Fin 1) =>
            (Fin.cons j (Fin.cons cand
              (Fin.cons code ctx)) :
                Fin (k + 3) → ℕ) 1) = _
      have hcand :
          (Fin.cons j (Fin.cons cand (Fin.cons code ctx)) :
            Fin (k + 3) → ℕ) 1 = cand := rfl
      rw [hcand, hconv, ERMor1.interp_natUnpairSnd]
      rfl
    | ⟨2, _⟩ => rfl
  rw [hrew, ERMor1.interp_beta]

/-- `j / 2` as an arity-`k + 3` term with `j` in slot `0`. -/
def ERMor1.halfJ {k : ℕ} : ERMor1 (k + 3) :=
  ERMor1.comp ERMor1.div (fun i => match i with
    | ⟨0, _⟩ => ERMor1.proj 0
    | ⟨1, _⟩ => ERMor1.twoN (k + 3))

/-- Interpretation of `halfJ`. -/
@[simp] theorem ERMor1.interp_halfJ {k : ℕ}
    (ctx : Fin (k + 3) → ℕ) :
    (ERMor1.halfJ (k := k)).interp ctx = ctx 0 / 2 := by
  unfold ERMor1.halfJ
  rw [ERMor1.interp_comp]
  have harg :
      (fun (i : Fin 2) =>
        ((match i with
          | ⟨0, _⟩ => ERMor1.proj 0
          | ⟨1, _⟩ =>
              ERMor1.twoN (k + 3) : ERMor1 (k + 3))).interp
          ctx) =
      ![ctx 0, 2] := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  rw [harg, ERMor1.interp_div]

/-- Apply `baseLeaf` within the `k + 3`-ary fold body context
`(j, cand, code, ctx)`: slot `0` of `baseLeaf` is `j / 2`, slots
`1..k` are the parameter context. -/
def ERMor1.baseLeafOnFold {k : ℕ} (baseLeaf : ERMor1 (k + 1)) :
    ERMor1 (k + 3) :=
  ERMor1.comp baseLeaf (fun i => match i with
    | ⟨0, _⟩ => ERMor1.halfJ
    | ⟨p + 1, h⟩ =>
        ERMor1.proj ⟨p + 3, by omega⟩)

/-- Interpretation of `baseLeafOnFold` at
`Fin.cons j (Fin.cons cand (Fin.cons code ctx))` reduces to
`baseLeaf.interp (Fin.cons (j / 2) ctx)`. -/
theorem ERMor1.interp_baseLeafOnFold {k : ℕ}
    (baseLeaf : ERMor1 (k + 1)) (j cand code : ℕ)
    (ctx : Fin k → ℕ) :
    (ERMor1.baseLeafOnFold baseLeaf).interp
        (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) =
      baseLeaf.interp (Fin.cons (j / 2) ctx) := by
  unfold ERMor1.baseLeafOnFold
  rw [ERMor1.interp_comp]
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ =>
    change (ERMor1.halfJ (k := k)).interp
        (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) = _
    rw [ERMor1.interp_halfJ]
    rfl
  | ⟨p + 1, h⟩ =>
    change (Fin.cons j (Fin.cons cand (Fin.cons code ctx)) :
        Fin (k + 3) → ℕ) ⟨p + 3, by omega⟩ = _
    rfl

/-- `(j / 2).unpair.1` as an arity-`k + 3` term with `j` in
slot `0`. -/
def ERMor1.halfJFst {k : ℕ} : ERMor1 (k + 3) :=
  ERMor1.comp ERMor1.natUnpairFst
    (fun (_ : Fin 1) => ERMor1.halfJ (k := k))

/-- `(j / 2).unpair.2` as an arity-`k + 3` term with `j` in
slot `0`. -/
def ERMor1.halfJSnd {k : ℕ} : ERMor1 (k + 3) :=
  ERMor1.comp ERMor1.natUnpairSnd
    (fun (_ : Fin 1) => ERMor1.halfJ (k := k))

/-- Interpretation of `halfJFst`. -/
@[simp] theorem ERMor1.interp_halfJFst {k : ℕ}
    (ctx : Fin (k + 3) → ℕ) :
    (ERMor1.halfJFst (k := k)).interp ctx =
      (ctx 0 / 2).unpair.1 := by
  unfold ERMor1.halfJFst
  rw [ERMor1.interp_comp]
  have hconv :
      (fun (_ : Fin 1) =>
        (ERMor1.halfJ (k := k)).interp ctx) =
      ![ctx 0 / 2] := by
    funext i
    match i with
    | ⟨0, _⟩ =>
      rw [ERMor1.interp_halfJ]
      rfl
  rw [hconv, ERMor1.interp_natUnpairFst]

/-- Interpretation of `halfJSnd`. -/
@[simp] theorem ERMor1.interp_halfJSnd {k : ℕ}
    (ctx : Fin (k + 3) → ℕ) :
    (ERMor1.halfJSnd (k := k)).interp ctx =
      (ctx 0 / 2).unpair.2 := by
  unfold ERMor1.halfJSnd
  rw [ERMor1.interp_comp]
  have hconv :
      (fun (_ : Fin 1) =>
        (ERMor1.halfJ (k := k)).interp ctx) =
      ![ctx 0 / 2] := by
    funext i
    match i with
    | ⟨0, _⟩ =>
      rw [ERMor1.interp_halfJ]
      rfl
  rw [hconv, ERMor1.interp_natUnpairSnd]

/-- Apply `stepNode` within the `k + 3`-ary fold body context
`(j, cand, code, ctx)`: slot `0` of `stepNode` is
`β(a, b, (j / 2).unpair.1)`, slot `1` is
`β(a, b, (j / 2).unpair.2)`, slots `2..k + 1` are the parameter
context. -/
def ERMor1.stepNodeOnFold {k : ℕ}
    (stepNode : ERMor1 (k + 2)) : ERMor1 (k + 3) :=
  ERMor1.comp stepNode (fun i => match i with
    | ⟨0, _⟩ =>
        ERMor1.betaOnCandFold (ERMor1.halfJFst (k := k))
    | ⟨1, _⟩ =>
        ERMor1.betaOnCandFold (ERMor1.halfJSnd (k := k))
    | ⟨p + 2, h⟩ =>
        ERMor1.proj ⟨p + 3, by omega⟩)

/-- Interpretation of `stepNodeOnFold` at
`Fin.cons j (Fin.cons cand (Fin.cons code ctx))`. -/
theorem ERMor1.interp_stepNodeOnFold {k : ℕ}
    (stepNode : ERMor1 (k + 2)) (j cand code : ℕ)
    (ctx : Fin k → ℕ) :
    (ERMor1.stepNodeOnFold stepNode).interp
        (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) =
      stepNode.interp
        (Fin.cons
          (cand.unpair.1 %
            (1 + ((j / 2).unpair.1 + 1) * cand.unpair.2))
          (Fin.cons
            (cand.unpair.1 %
              (1 + ((j / 2).unpair.2 + 1) * cand.unpair.2))
            ctx)) := by
  unfold ERMor1.stepNodeOnFold
  rw [ERMor1.interp_comp]
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ =>
    change (ERMor1.betaOnCandFold
        (ERMor1.halfJFst (k := k))).interp
        (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) = _
    rw [ERMor1.interp_betaOnCandFold]
    rw [ERMor1.interp_halfJFst]
    rfl
  | ⟨1, _⟩ =>
    change (ERMor1.betaOnCandFold
        (ERMor1.halfJSnd (k := k))).interp
        (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) = _
    rw [ERMor1.interp_betaOnCandFold]
    rw [ERMor1.interp_halfJSnd]
    rfl
  | ⟨p + 2, h⟩ =>
    change (Fin.cons j (Fin.cons cand (Fin.cons code ctx)) :
        Fin (k + 3) → ℕ) ⟨p + 3, by omega⟩ = _
    rfl

/-- `j % 2` as an arity-`k + 3` term with `j` in slot `0`. -/
def ERMor1.jMod2 {k : ℕ} : ERMor1 (k + 3) :=
  ERMor1.comp ERMor1.mod (fun i => match i with
    | ⟨0, _⟩ => ERMor1.proj 0
    | ⟨1, _⟩ => ERMor1.twoN (k + 3))

/-- Interpretation of `jMod2`. -/
@[simp] theorem ERMor1.interp_jMod2 {k : ℕ}
    (ctx : Fin (k + 3) → ℕ) :
    (ERMor1.jMod2 (k := k)).interp ctx = ctx 0 % 2 := by
  unfold ERMor1.jMod2
  rw [ERMor1.interp_comp]
  have harg :
      (fun (i : Fin 2) =>
        ((match i with
          | ⟨0, _⟩ => ERMor1.proj 0
          | ⟨1, _⟩ =>
              ERMor1.twoN (k + 3) : ERMor1 (k + 3))).interp
          ctx) =
      ![ctx 0, 2] := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  rw [harg, ERMor1.interp_mod]

/-- Expected fold value at position `j` as an arity-`k + 3`
term: if `j % 2 = 1` returns
`stepNode(β(a, b, (j / 2).unpair.1), β(a, b, (j / 2).unpair.2),
ctx)`; if `j % 2 = 0` returns `baseLeaf(j / 2, ctx)`.  Evaluated
at `(j, cand, code, ctx)`. -/
def ERMor1.foldBTLExpected {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2)) : ERMor1 (k + 3) :=
  ERMor1.comp ERMor1.condN (fun i => match i with
    | ⟨0, _⟩ => ERMor1.jMod2 (k := k)
    | ⟨1, _⟩ => ERMor1.stepNodeOnFold stepNode
    | ⟨2, _⟩ => ERMor1.baseLeafOnFold baseLeaf)

/-- Interpretation of `foldBTLExpected` at
`(j, cand, code, ctx)`. -/
theorem ERMor1.interp_foldBTLExpected {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2))
    (j cand code : ℕ) (ctx : Fin k → ℕ) :
    (ERMor1.foldBTLExpected baseLeaf stepNode).interp
        (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) =
      if j % 2 = 1 then
        stepNode.interp
          (Fin.cons
            (cand.unpair.1 %
              (1 + ((j / 2).unpair.1 + 1) * cand.unpair.2))
            (Fin.cons
              (cand.unpair.1 %
                (1 + ((j / 2).unpair.2 + 1) * cand.unpair.2))
              ctx))
      else
        baseLeaf.interp (Fin.cons (j / 2) ctx) := by
  unfold ERMor1.foldBTLExpected
  rw [ERMor1.interp_comp]
  set cctx :=
    (Fin.cons j (Fin.cons cand (Fin.cons code ctx)) :
      Fin (k + 3) → ℕ) with _
  have hmod :
      (ERMor1.jMod2 (k := k)).interp cctx = j % 2 := by
    rw [ERMor1.interp_jMod2]
    rfl
  have hstep :
      (ERMor1.stepNodeOnFold stepNode).interp cctx =
        stepNode.interp
          (Fin.cons
            (cand.unpair.1 %
              (1 + ((j / 2).unpair.1 + 1) * cand.unpair.2))
            (Fin.cons
              (cand.unpair.1 %
                (1 + ((j / 2).unpair.2 + 1) * cand.unpair.2))
              ctx)) :=
    ERMor1.interp_stepNodeOnFold stepNode j cand code ctx
  have hbase :
      (ERMor1.baseLeafOnFold baseLeaf).interp cctx =
        baseLeaf.interp (Fin.cons (j / 2) ctx) :=
    ERMor1.interp_baseLeafOnFold baseLeaf j cand code ctx
  have hmod_le : j % 2 ≤ 1 := by
    have : j % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  have hargfn :
      (fun (i : Fin 3) =>
        ((match i with
          | ⟨0, _⟩ => ERMor1.jMod2 (k := k)
          | ⟨1, _⟩ => ERMor1.stepNodeOnFold stepNode
          | ⟨2, _⟩ =>
              ERMor1.baseLeafOnFold baseLeaf :
            ERMor1 (k + 3))).interp cctx) =
      ![j % 2,
        stepNode.interp
          (Fin.cons
            (cand.unpair.1 %
              (1 + ((j / 2).unpair.1 + 1) * cand.unpair.2))
            (Fin.cons
              (cand.unpair.1 %
                (1 + ((j / 2).unpair.2 + 1) * cand.unpair.2))
              ctx)),
        baseLeaf.interp (Fin.cons (j / 2) ctx)] := by
    funext i
    match i with
    | ⟨0, _⟩ => exact hmod
    | ⟨1, _⟩ => exact hstep
    | ⟨2, _⟩ => exact hbase
  rw [hargfn]
  have hcond :
      ERMor1.condN.interp
        ![j % 2,
          stepNode.interp
            (Fin.cons
              (cand.unpair.1 %
                (1 + ((j / 2).unpair.1 + 1) * cand.unpair.2))
              (Fin.cons
                (cand.unpair.1 %
                  (1 + ((j / 2).unpair.2 + 1) * cand.unpair.2))
                ctx)),
          baseLeaf.interp (Fin.cons (j / 2) ctx)] =
        if j % 2 = 1 then
          stepNode.interp
            (Fin.cons
              (cand.unpair.1 %
                (1 + ((j / 2).unpair.1 + 1) * cand.unpair.2))
              (Fin.cons
                (cand.unpair.1 %
                  (1 + ((j / 2).unpair.2 + 1) * cand.unpair.2))
                ctx))
        else baseLeaf.interp (Fin.cons (j / 2) ctx) :=
    ERMor1.condN_boolean _ hmod_le
  exact hcond

/-- Per-position body of the fold predicate: an arity-`k + 3`
term at context `(j, cand, code, ctx)` evaluating to `1` iff
`β(a, b, j) = foldBTLExpected(j, cand, code, ctx)`. -/
def ERMor1.foldBTLBody {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2)) : ERMor1 (k + 3) :=
  ERMor1.boolEqAt
    (ERMor1.betaOnCandFold (ERMor1.proj 0))
    (ERMor1.foldBTLExpected baseLeaf stepNode)

/-- The fold body evaluates in `{0, 1}`. -/
theorem ERMor1.foldBTLBody_le_one {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2))
    (ctx : Fin (k + 3) → ℕ) :
    (ERMor1.foldBTLBody baseLeaf stepNode).interp ctx ≤ 1 :=
  ERMor1.boolEqAt_le_one _ _ _

/-- Fold body evaluates to `1` iff the β-value at position `j`
matches the expected fold value. -/
theorem ERMor1.foldBTLBody_eq_one_iff {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2))
    (j cand code : ℕ) (ctx : Fin k → ℕ) :
    (ERMor1.foldBTLBody baseLeaf stepNode).interp
        (Fin.cons j (Fin.cons cand (Fin.cons code ctx))) = 1 ↔
      cand.unpair.1 % (1 + (j + 1) * cand.unpair.2) =
        (if j % 2 = 1 then
          stepNode.interp
            (Fin.cons
              (cand.unpair.1 %
                (1 + ((j / 2).unpair.1 + 1) * cand.unpair.2))
              (Fin.cons
                (cand.unpair.1 %
                  (1 + ((j / 2).unpair.2 + 1) * cand.unpair.2))
                ctx))
        else baseLeaf.interp (Fin.cons (j / 2) ctx)) := by
  unfold ERMor1.foldBTLBody
  rw [ERMor1.boolEqAt_eq_one_iff,
    ERMor1.interp_betaOnCandFold,
    ERMor1.interp_foldBTLExpected]
  have hproj :
      (ERMor1.proj (0 : Fin (k + 3))).interp
        (Fin.cons j
          (Fin.cons cand (Fin.cons code ctx))) = j := rfl
  rw [hproj]

/-- Full predicate for the fold β-witness search.  At context
`Fin.cons cand (Fin.cons code ctx)`, evaluates to `1` iff every
position `j < code + 1` satisfies the fold body check. -/
def ERMor1.foldBTLPred {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2)) : ERMor1 (k + 2) :=
  ERMor1.comp (ERMor1.bprod
      (ERMor1.foldBTLBody baseLeaf stepNode))
    (fun (i : Fin (k + 3)) => match i with
      | ⟨0, _⟩ =>
          ERMor1.comp ERMor1.succ
            (fun (_ : Fin 1) => ERMor1.proj 1)
      | ⟨1, _⟩ => ERMor1.proj 0
      | ⟨2, _⟩ => ERMor1.proj 1
      | ⟨p + 3, h⟩ =>
          ERMor1.proj ⟨p + 2, by omega⟩)

/-- The fold predicate evaluates in `{0, 1}`. -/
theorem ERMor1.foldBTLPred_le_one {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2))
    (ctx : Fin (k + 2) → ℕ) :
    (ERMor1.foldBTLPred baseLeaf stepNode).interp ctx ≤ 1 := by
  unfold ERMor1.foldBTLPred
  rw [ERMor1.interp_comp, ERMor1.interp_bprod]
  exact natBProd_le_one_of_body_le_one _ _ (fun _ =>
    ERMor1.foldBTLBody_le_one baseLeaf stepNode _)

/-- The fold predicate as a bounded product of fold-body
values over positions `j ∈ [0, code + 1)`. -/
theorem ERMor1.interp_foldBTLPred_as_bprod {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2))
    (cand code : ℕ) (ctx : Fin k → ℕ) :
    (ERMor1.foldBTLPred baseLeaf stepNode).interp
        (Fin.cons cand (Fin.cons code ctx)) =
      natBProd (code + 1) (fun j =>
        (ERMor1.foldBTLBody baseLeaf stepNode).interp
          (Fin.cons j
            (Fin.cons cand (Fin.cons code ctx)))) := by
  unfold ERMor1.foldBTLPred
  rw [ERMor1.interp_comp]
  set argFn : Fin (k + 3) → ℕ := fun i =>
    ((fun i : Fin (k + 3) => match i with
      | ⟨0, _⟩ =>
          ERMor1.comp ERMor1.succ
            (fun (_ : Fin 1) => ERMor1.proj (k := k + 2) 1)
      | ⟨1, _⟩ => ERMor1.proj 0
      | ⟨2, _⟩ => ERMor1.proj 1
      | ⟨p + 3, h⟩ =>
          ERMor1.proj
            (⟨p + 2, by omega⟩ : Fin (k + 2))) i).interp
      (Fin.cons cand (Fin.cons code ctx))
  rw [ERMor1.interp_bprod]
  have h0 : argFn 0 = code + 1 := by
    change ((ERMor1.comp ERMor1.succ
          (fun (_ : Fin 1) =>
            ERMor1.proj (k := k + 2) 1)).interp
          (Fin.cons cand (Fin.cons code ctx))) = _
    rw [ERMor1.interp_comp, ERMor1.interp_succ]
    rfl
  have htail :
      Fin.tail argFn =
        Fin.cons cand (Fin.cons code ctx) := by
    funext ⟨p, hp⟩
    change argFn ⟨p + 1, by omega⟩ = _
    match p with
    | 0 => rfl
    | 1 => rfl
    | q + 2 => rfl
  rw [h0, htail]

/-- Fold predicate equals `1` iff the β-values match the
expected fold trace at every position `j ≤ code`. -/
theorem ERMor1.foldBTLPred_eq_one_iff_trace {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2))
    (cand code : ℕ) (ctx : Fin k → ℕ) :
    (ERMor1.foldBTLPred baseLeaf stepNode).interp
        (Fin.cons cand (Fin.cons code ctx)) = 1 ↔
      ∀ j, j < code + 1 →
        cand.unpair.1 % (1 + (j + 1) * cand.unpair.2) =
          (if j % 2 = 1 then
            stepNode.interp
              (Fin.cons
                (cand.unpair.1 %
                  (1 + ((j / 2).unpair.1 + 1)
                    * cand.unpair.2))
                (Fin.cons
                  (cand.unpair.1 %
                    (1 + ((j / 2).unpair.2 + 1)
                      * cand.unpair.2))
                  ctx))
          else baseLeaf.interp (Fin.cons (j / 2) ctx)) := by
  rw [ERMor1.interp_foldBTLPred_as_bprod,
    natBProd_eq_one_iff_all_one]
  constructor
  · intro h j hj
    exact (ERMor1.foldBTLBody_eq_one_iff baseLeaf stepNode
      j cand code ctx).mp (h j hj)
  · intro h j hj
    exact (ERMor1.foldBTLBody_eq_one_iff baseLeaf stepNode
      j cand code ctx).mpr (h j hj)

/-- ER-derived course-of-values fold on a `BTL` Gödel code.
At outer arity `k + 1` with slot `0` the code and slots `1..k`
the parameter context, returns `min (β(a, b, code)) bound`,
where `(a, b) = Nat.unpair` of the least `cand` satisfying
`foldBTLPred = 1` below `boundedRecRange bound`.  The outer
`minN` makes the output unconditionally bounded by `bound`.
Correctness against `Nat.foldBTLOnCode` holds when `bound`
pointwise dominates the fold trace. -/
def ERMor1.foldBTLOnCode {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) : ERMor1 (k + 1) :=
  let search : ERMor1 (k + 1) :=
    ERMor1.boundedSearch (ERMor1.boundedRecRange bound)
      (ERMor1.foldBTLPred baseLeaf stepNode)
  let betaAtCode : ERMor1 (k + 1) :=
    ERMor1.comp ERMor1.beta (fun i => match i with
      | ⟨0, _⟩ =>
          ERMor1.comp ERMor1.natUnpairFst
            (fun (_ : Fin 1) => search)
      | ⟨1, _⟩ =>
          ERMor1.comp ERMor1.natUnpairSnd
            (fun (_ : Fin 1) => search)
      | ⟨2, _⟩ => ERMor1.proj 0)
  ERMor1.comp ERMor1.minN (fun i => match i with
    | ⟨0, _⟩ => betaAtCode
    | ⟨1, _⟩ => bound)

/-- Unconditional upper bound for `foldBTLOnCode`: its
interpretation is dominated by `bound.interp (Fin.cons code
ctx)` for every code and parameter context. -/
theorem ERMor1.interp_foldBTLOnCode_le_bound {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) (ctx : Fin (k + 1) → ℕ) :
    (ERMor1.foldBTLOnCode baseLeaf stepNode bound).interp
        ctx ≤ bound.interp ctx := by
  unfold ERMor1.foldBTLOnCode
  rw [ERMor1.interp_comp, ERMor1.interp_minN]
  exact Nat.min_le_right _ _

/-- Helper for the conditional correctness of
`foldBTLOnCode`: if a candidate satisfies the per-position
clauses of `foldBTLPred` for every `j < code + 1`, then its
β-extraction at each index `j ≤ code` equals the
`Nat.foldBTLOnCode` trace at `j`. -/
theorem ERMor1.foldBTLPred_trace_match {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2))
    (cand : ℕ) (ctx : Fin k → ℕ) (code : ℕ)
    (htrace : ∀ j, j < code + 1 →
      cand.unpair.1 % (1 + (j + 1) * cand.unpair.2) =
        (if j % 2 = 1 then
          stepNode.interp
            (Fin.cons
              (cand.unpair.1 %
                (1 + ((j / 2).unpair.1 + 1)
                  * cand.unpair.2))
              (Fin.cons
                (cand.unpair.1 %
                  (1 + ((j / 2).unpair.2 + 1)
                    * cand.unpair.2))
                ctx))
        else baseLeaf.interp (Fin.cons (j / 2) ctx))) :
    ∀ j, j ≤ code →
      cand.unpair.1 % (1 + (j + 1) * cand.unpair.2) =
        Nat.foldBTLOnCode
          (fun lbl => baseLeaf.interp (Fin.cons lbl ctx))
          (fun l r => stepNode.interp
            (Fin.cons l (Fin.cons r ctx)))
          j := by
  intro j hj
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have hj_lt : j < code + 1 := Nat.lt_succ_of_le hj
    have hbody := htrace j hj_lt
    by_cases hjzero : j = 0
    · subst hjzero
      have hmod0 : (0 : ℕ) / 2 = 0 := rfl
      rw [hbody]
      have hne : ((0 : ℕ) % 2) ≠ 1 := by decide
      rw [if_neg hne, hmod0, Nat.foldBTLOnCode_zero]
    · by_cases hev : j % 2 = 0
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hjzero
        rw [hbody]
        have hne1 : j % 2 ≠ 1 := by
          rw [hev]; decide
        simp only [hne1, if_false]
        rw [Nat.foldBTLOnCode_even
          (fun lbl => baseLeaf.interp (Fin.cons lbl ctx))
          (fun l r => stepNode.interp
            (Fin.cons l (Fin.cons r ctx)))
          j hjpos hev]
      · have hodd : j % 2 = 1 := by
          have : j % 2 < 2 := Nat.mod_lt _ (by decide)
          omega
        have hjpos : 0 < j := by
          rcases Nat.eq_zero_or_pos j with hz | hp
          · exact absurd hz hjzero
          · exact hp
        have hhalf_lt : j / 2 < j :=
          Nat.div_lt_self hjpos (by decide)
        have hfst_le : (j / 2).unpair.1 ≤ j / 2 :=
          Nat.unpair_left_le _
        have hsnd_le : (j / 2).unpair.2 ≤ j / 2 :=
          Nat.unpair_right_le _
        have hfst_lt_j : (j / 2).unpair.1 < j :=
          lt_of_le_of_lt hfst_le hhalf_lt
        have hsnd_lt_j : (j / 2).unpair.2 < j :=
          lt_of_le_of_lt hsnd_le hhalf_lt
        have hfst_le_code : (j / 2).unpair.1 ≤ code := by
          have := Nat.le_of_lt_succ hj_lt
          exact le_trans (le_of_lt hfst_lt_j) this
        have hsnd_le_code : (j / 2).unpair.2 ≤ code := by
          have := Nat.le_of_lt_succ hj_lt
          exact le_trans (le_of_lt hsnd_lt_j) this
        have ihfst := ih _ hfst_lt_j hfst_le_code
        have ihsnd := ih _ hsnd_lt_j hsnd_le_code
        rw [hbody]
        simp only [hodd, if_true]
        rw [ihfst, ihsnd]
        rw [Nat.foldBTLOnCode_odd
          (fun lbl => baseLeaf.interp (Fin.cons lbl ctx))
          (fun l r => stepNode.interp
            (Fin.cons l (Fin.cons r ctx)))
          j (by rw [hodd]; decide)]

set_option maxHeartbeats 800000 in
-- bprod-based β-witness search for the course-of-values fold
-- exceeds the default heartbeat limit.
/-- Conditional equality with `Nat.foldBTLOnCode`: when the
client's bound is monotone in the counter slot and pointwise
dominates the fold trace, the combinator agrees with
`Nat.foldBTLOnCode`. -/
theorem ERMor1.interp_foldBTLOnCode_of_bounded {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1))
    (code : ℕ) (ctx : Fin k → ℕ)
    (h : ∀ j, j ≤ code →
      Nat.foldBTLOnCode
        (fun lbl => baseLeaf.interp (Fin.cons lbl ctx))
        (fun l r => stepNode.interp
          (Fin.cons l (Fin.cons r ctx)))
        j ≤
        bound.interp (Fin.cons j ctx))
    (h_mono : ∀ j, j ≤ code →
      bound.interp (Fin.cons j ctx) ≤
        bound.interp (Fin.cons code ctx)) :
    (ERMor1.foldBTLOnCode baseLeaf stepNode bound).interp
        (Fin.cons code ctx) =
      Nat.foldBTLOnCode
        (fun lbl => baseLeaf.interp (Fin.cons lbl ctx))
        (fun l r => stepNode.interp
          (Fin.cons l (Fin.cons r ctx)))
        code := by
  set B : ℕ := bound.interp (Fin.cons code ctx) with _
  let trace : ℕ → ℕ := fun j =>
    Nat.foldBTLOnCode
      (fun lbl => baseLeaf.interp (Fin.cons lbl ctx))
      (fun l r => stepNode.interp
        (Fin.cons l (Fin.cons r ctx)))
      j
  let s : Fin (code + 1) → ℕ := fun j => trace j.val
  have hs_le_B : ∀ j : Fin (code + 1), s j ≤ B := by
    intro j
    have hj_le : j.val ≤ code := Nat.le_of_lt_succ j.isLt
    have h1 : s j ≤ bound.interp (Fin.cons j.val ctx) :=
      h j.val hj_le
    have h2 :
        bound.interp (Fin.cons j.val ctx) ≤ B :=
      h_mono j.val hj_le
    exact le_trans h1 h2
  obtain ⟨a, b, hb_eq, ha_lt, hbeta⟩ :=
    Nat.bounded_beta_exists s B hs_le_B
  set cand : ℕ := Nat.pair a b with hcand_def
  have hcand_unpair_fst : cand.unpair.1 = a := by
    rw [hcand_def, Nat.unpair_pair]
  have hcand_unpair_snd : cand.unpair.2 = b := by
    rw [hcand_def, Nat.unpair_pair]
  have hrange :
      (ERMor1.boundedRecRange bound).interp
        (Fin.cons code ctx) =
      ((code + B + 3).factorial) ^
        ((code + B + 3).factorial) + 1 := by
    rw [ERMor1.interp_boundedRecRange]
    have hc0 :
        (Fin.cons code ctx : Fin (k + 1) → ℕ) 0 = code := by
      rfl
    rw [hc0]
  have hcand_lt_range :
      cand <
        (ERMor1.boundedRecRange bound).interp
          (Fin.cons code ctx) := by
    rw [hrange]
    exact Nat.pair_lt_boundedRecRange code B a b hb_eq ha_lt
  have hpred_hold :
      (ERMor1.foldBTLPred baseLeaf stepNode).interp
          (Fin.cons cand (Fin.cons code ctx)) = 1 := by
    rw [ERMor1.foldBTLPred_eq_one_iff_trace]
    intro j hj
    rw [hcand_unpair_fst, hcand_unpair_snd]
    have hbeta_j := hbeta ⟨j, hj⟩
    change a % (1 + (j + 1) * b) = trace j at hbeta_j
    by_cases hodd : j % 2 = 1
    · have hhalf_lt : j / 2 < j :=
        Nat.div_lt_self (by
          rcases Nat.eq_zero_or_pos j with hz | hp
          · subst hz; simp at hodd
          · exact hp) (by decide)
      have hj_le : j ≤ code := Nat.le_of_lt_succ hj
      have hfst_le : (j / 2).unpair.1 ≤ j / 2 :=
        Nat.unpair_left_le _
      have hsnd_le : (j / 2).unpair.2 ≤ j / 2 :=
        Nat.unpair_right_le _
      have hfst_lt_cs : (j / 2).unpair.1 < code + 1 := by
        have : (j / 2).unpair.1 < j :=
          lt_of_le_of_lt hfst_le hhalf_lt
        omega
      have hsnd_lt_cs : (j / 2).unpair.2 < code + 1 := by
        have : (j / 2).unpair.2 < j :=
          lt_of_le_of_lt hsnd_le hhalf_lt
        omega
      have hbeta_fst := hbeta ⟨(j / 2).unpair.1, hfst_lt_cs⟩
      have hbeta_snd := hbeta ⟨(j / 2).unpair.2, hsnd_lt_cs⟩
      change a % (1 + ((j / 2).unpair.1 + 1) * b) =
        trace (j / 2).unpair.1 at hbeta_fst
      change a % (1 + ((j / 2).unpair.2 + 1) * b) =
        trace (j / 2).unpair.2 at hbeta_snd
      have htrace_odd :
          trace j = stepNode.interp
            (Fin.cons (trace (j / 2).unpair.1)
              (Fin.cons (trace (j / 2).unpair.2) ctx)) := by
        change Nat.foldBTLOnCode _ _ j = _
        exact Nat.foldBTLOnCode_odd _ _ j (by
          rw [hodd]; decide)
      rw [if_pos hodd]
      rw [hbeta_j, htrace_odd, hbeta_fst, hbeta_snd]
    · rw [if_neg hodd]
      by_cases hjzero : j = 0
      · subst hjzero
        have hdiv0 : (0 : ℕ) / 2 = 0 := rfl
        rw [hdiv0, hbeta_j]
        change Nat.foldBTLOnCode _ _ 0 = _
        rw [Nat.foldBTLOnCode_zero]
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hjzero
        have hev : j % 2 = 0 := by
          have hmod_lt : j % 2 < 2 := Nat.mod_lt _ (by decide)
          omega
        rw [hbeta_j]
        change Nat.foldBTLOnCode _ _ j = _
        rw [Nat.foldBTLOnCode_even
          (fun lbl => baseLeaf.interp (Fin.cons lbl ctx))
          (fun l r => stepNode.interp
            (Fin.cons l (Fin.cons r ctx)))
          j hjpos hev]
  have hpred_bound :
      ∀ j, (ERMor1.foldBTLPred baseLeaf stepNode).interp
        (Fin.cons j (Fin.cons code ctx)) ≤ 1 := by
    intro j
    exact ERMor1.foldBTLPred_le_one baseLeaf stepNode _
  set search : ERMor1 (k + 1) :=
    ERMor1.boundedSearch (ERMor1.boundedRecRange bound)
      (ERMor1.foldBTLPred baseLeaf stepNode) with hsearch_def
  have hex : ∃ j, j <
      (ERMor1.boundedRecRange bound).interp
        (Fin.cons code ctx) ∧
      (ERMor1.foldBTLPred baseLeaf stepNode).interp
        (Fin.cons j (Fin.cons code ctx)) = 1 :=
    ⟨cand, hcand_lt_range, hpred_hold⟩
  have hsearch_eval :
      search.interp (Fin.cons code ctx) = Nat.find hex := by
    rw [hsearch_def,
      ERMor1.interp_boundedSearch _ _ _ hpred_bound,
      dif_pos hex]
  set found : ℕ := Nat.find hex with hfound_def
  have hfound_pred :
      (ERMor1.foldBTLPred baseLeaf stepNode).interp
        (Fin.cons found (Fin.cons code ctx)) = 1 :=
    (Nat.find_spec hex).2
  have hfound_htrace :=
    (ERMor1.foldBTLPred_eq_one_iff_trace baseLeaf stepNode
      found code ctx).mp hfound_pred
  have hfound_trace :
      ∀ j, j ≤ code →
        found.unpair.1 % (1 + (j + 1) * found.unpair.2) =
          trace j :=
    ERMor1.foldBTLPred_trace_match baseLeaf stepNode
      found ctx code hfound_htrace
  unfold ERMor1.foldBTLOnCode
  rw [ERMor1.interp_comp, ERMor1.interp_minN]
  change min
      ((ERMor1.comp ERMor1.beta _).interp (Fin.cons code ctx))
      (bound.interp (Fin.cons code ctx)) = trace code
  have hbetaCode_eval :
      (ERMor1.comp ERMor1.beta
        (fun (i : Fin 3) => match i with
          | ⟨0, _⟩ =>
              ERMor1.comp ERMor1.natUnpairFst
                (fun (_ : Fin 1) => search)
          | ⟨1, _⟩ =>
              ERMor1.comp ERMor1.natUnpairSnd
                (fun (_ : Fin 1) => search)
          | ⟨2, _⟩ =>
              ERMor1.proj 0)).interp
        (Fin.cons code ctx) =
      found.unpair.1 %
        (1 + (code + 1) * found.unpair.2) := by
    rw [ERMor1.interp_comp]
    have harg :
        (fun (i : Fin 3) =>
          ((match i with
            | ⟨0, _⟩ =>
                ERMor1.comp ERMor1.natUnpairFst
                  (fun (_ : Fin 1) => search)
            | ⟨1, _⟩ =>
                ERMor1.comp ERMor1.natUnpairSnd
                  (fun (_ : Fin 1) => search)
            | ⟨2, _⟩ =>
                ERMor1.proj 0 : ERMor1 (k + 1))).interp
            (Fin.cons code ctx)) =
        ![found.unpair.1, found.unpair.2, code] := by
      funext i
      match i with
      | ⟨0, _⟩ =>
        change ERMor1.natUnpairFst.interp
            (fun (_ : Fin 1) =>
              search.interp (Fin.cons code ctx)) = _
        rw [hsearch_eval]
        have hfun :
            (fun (_ : Fin 1) => (found : ℕ)) = ![found] := by
          funext j
          match j with
          | ⟨0, _⟩ => rfl
        rw [hfun, ERMor1.interp_natUnpairFst]
        rfl
      | ⟨1, _⟩ =>
        change ERMor1.natUnpairSnd.interp
            (fun (_ : Fin 1) =>
              search.interp (Fin.cons code ctx)) = _
        rw [hsearch_eval]
        have hfun :
            (fun (_ : Fin 1) => (found : ℕ)) = ![found] := by
          funext j
          match j with
          | ⟨0, _⟩ => rfl
        rw [hfun, ERMor1.interp_natUnpairSnd]
        rfl
      | ⟨2, _⟩ =>
        change (Fin.cons code ctx :
            Fin (k + 1) → ℕ) 0 = _
        rfl
    rw [harg, ERMor1.interp_beta]
  rw [hbetaCode_eval]
  have htrace_code := hfound_trace code (le_refl code)
  rw [htrace_code]
  have htrace_le : trace code ≤ B := by
    have := h code (le_refl code)
    have hmono := h_mono code (le_refl code)
    exact le_trans this hmono
  exact min_eq_left htrace_le

/-- Convenience alias for `interp_foldBTLOnCode_of_bounded`.
When the client supplies pointwise bound-adequacy and
counter-monotonicity hypotheses, `foldBTLOnCode` computes the
exact `Nat.foldBTLOnCode` trace value at the given code. -/
theorem ERMor1.foldBTLOnCode_eq_foldBTLOnCode_of_bounded
    {k : ℕ}
    (baseLeaf : ERMor1 (k + 1))
    (stepNode : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1))
    (code : ℕ) (ctx : Fin k → ℕ)
    (h : ∀ j, j ≤ code →
      Nat.foldBTLOnCode
        (fun lbl => baseLeaf.interp (Fin.cons lbl ctx))
        (fun l r => stepNode.interp
          (Fin.cons l (Fin.cons r ctx)))
        j ≤
        bound.interp (Fin.cons j ctx))
    (h_mono : ∀ j, j ≤ code →
      bound.interp (Fin.cons j ctx) ≤
        bound.interp (Fin.cons code ctx)) :
    (ERMor1.foldBTLOnCode baseLeaf stepNode bound).interp
        (Fin.cons code ctx) =
      Nat.foldBTLOnCode
        (fun lbl => baseLeaf.interp (Fin.cons lbl ctx))
        (fun l r => stepNode.interp
          (Fin.cons l (Fin.cons r ctx)))
        code :=
  ERMor1.interp_foldBTLOnCode_of_bounded baseLeaf stepNode
    bound code ctx h h_mono

end GebLean

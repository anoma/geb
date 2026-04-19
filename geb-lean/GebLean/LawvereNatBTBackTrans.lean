import GebLean.LawvereNatBT
import GebLean.LawvereER
import GebLean.Utilities.ERArith
import GebLean.Utilities.ERTreeArith

/-!
# Back-Translation from `NatBTMor1` (fold-free) to `ERMor1`

Translation of the fold-free fragment of `NatBTMor1` at ambient
BT-arity 0 back to the ℕ-only theory `ERMor1`.  A structural
predicate `isFoldFree` isolates the sub-language without
`foldBTNat` or `foldBTBT`, propagating a BT-arity-0 invariant
through composition constructors.  Correctness theorems
`toER_interp` and `toER_bt_interp` are proved by mutual
induction.  BT outputs are compared under `BTL.encode`.

**Version note**: this file back-translates the *bounded* variant
of the two-sort theory. The fold-free fragment excludes the bounded
`foldBTNat` and `foldBTBT` operations (those with explicit bound
parameters). The two-stage equivalence `LawvereERCat ≃
LawvereNatBT_bounded ≃ LawvereNatBT_ramified` is documented in
`docs/superpowers/specs/2026-04-18-lawvere-natbt-two-stage-design.md`.
-/

namespace GebLean

/-- Structural predicate: `True` iff the term contains neither
`foldBTNat` nor `foldBTBT` anywhere, and every composition
sub-term has BT-arity 0.  The latter propagates the ambient
BT-arity-0 invariant through `compNat`/`compBT`. -/
def NatBTMor1.isFoldFree : {nm : ℕ × ℕ} → {σ : NatBTSort} →
    NatBTMor1 nm σ → Prop
  | _, _, NatBTMor1.zero => True
  | _, _, NatBTMor1.succ x => x.isFoldFree
  | _, _, NatBTMor1.natProj _ => True
  | _, _, NatBTMor1.sub a b => a.isFoldFree ∧ b.isFoldFree
  | _, _, NatBTMor1.compNat (nm' := nm') f gNat _ =>
      nm'.2 = 0 ∧ f.isFoldFree ∧ ∀ i, (gNat i).isFoldFree
  | _, _, NatBTMor1.bsum f => f.isFoldFree
  | _, _, NatBTMor1.bprod f => f.isFoldFree
  | _, _, NatBTMor1.leafBT label => label.isFoldFree
  | _, _, NatBTMor1.nodeBT l r => l.isFoldFree ∧ r.isFoldFree
  | _, _, NatBTMor1.btProj _ => True
  | _, _, NatBTMor1.compBT (nm' := nm') f gNat _ =>
      nm'.2 = 0 ∧ f.isFoldFree ∧ ∀ i, (gNat i).isFoldFree
  | _, _, NatBTMor1.foldBTNat _ _ _ _ => False
  | _, _, NatBTMor1.foldBTBT _ _ _ => False
  | _, _, NatBTMor1.encodeBT t => t.isFoldFree
  | _, _, NatBTMor1.decodeBT k => k.isFoldFree

/-- Back-translation to `ERMor1`, uniform across the two
output sorts.  On `.nat` outputs, produces the corresponding
`ERMor1` term.  On `.bt` outputs, produces an `ERMor1` term
whose value is the Gödel code `BTL.encode` of the interpreted
tree.  Fold constructors, `btProj`, and composition sub-terms
with BT-arity > 0 are mapped to the placeholder
`ERMor1.zeroN _`; these cases are never reached under
`isFoldFree` combined with ambient BT-arity 0. -/
def NatBTMor1.toERUniform : {nm : ℕ × ℕ} → {σ : NatBTSort} →
    NatBTMor1 nm σ → ERMor1 nm.1
  | _, _, NatBTMor1.zero => ERMor1.zeroN _
  | _, _, NatBTMor1.succ x =>
      ERMor1.comp ERMor1.succ
        (fun _ : Fin 1 => x.toERUniform)
  | _, _, NatBTMor1.natProj i => ERMor1.proj i
  | _, _, NatBTMor1.sub a b =>
      ERMor1.comp ERMor1.sub (fun i => match i with
        | ⟨0, _⟩ => a.toERUniform
        | ⟨1, _⟩ => b.toERUniform)
  | _, _, NatBTMor1.compNat (nm' := nm') f gNat _ =>
      if _ : nm'.2 = 0 then
        ERMor1.comp f.toERUniform
          (fun i => (gNat i).toERUniform)
      else
        ERMor1.zeroN _
  | _, _, NatBTMor1.bsum f => ERMor1.bsum f.toERUniform
  | _, _, NatBTMor1.bprod f => ERMor1.bprod f.toERUniform
  | _, _, NatBTMor1.foldBTNat _ _ _ _ => ERMor1.zeroN _
  | _, _, NatBTMor1.encodeBT t => t.toERUniform
  | _, _, NatBTMor1.leafBT label =>
      ERMor1.comp ERMor1.btlEncodeLeaf
        (fun _ : Fin 1 => label.toERUniform)
  | _, _, NatBTMor1.nodeBT l r =>
      ERMor1.comp ERMor1.btlEncodeNode
        (fun i => match i with
          | ⟨0, _⟩ => l.toERUniform
          | ⟨1, _⟩ => r.toERUniform)
  | _, _, NatBTMor1.btProj _ => ERMor1.zeroN _
  | _, _, NatBTMor1.compBT (nm' := nm') f gNat _ =>
      if _ : nm'.2 = 0 then
        ERMor1.comp f.toERUniform
          (fun i => (gNat i).toERUniform)
      else
        ERMor1.zeroN _
  | _, _, NatBTMor1.foldBTBT _ _ _ => ERMor1.zeroN _
  | _, _, NatBTMor1.decodeBT k => k.toERUniform

/-- Back-translation specialized to `.nat` outputs. -/
def NatBTMor1.toER {nm : ℕ × ℕ} (t : NatBTMor1 nm .nat) :
    ERMor1 nm.1 := t.toERUniform

/-- Back-translation specialized to `.bt` outputs: the value is
`BTL.encode` of the interpreted tree. -/
def NatBTMor1.toER_bt {nm : ℕ × ℕ} (t : NatBTMor1 nm .bt) :
    ERMor1 nm.1 := t.toERUniform

/-- Encode a value of either carrier sort to ℕ: identity on
`.nat`, `BTL.encode` on `.bt`. -/
def NatBTSort.encodeValue : (σ : NatBTSort) → σ.carrier → ℕ
  | .nat, v => v
  | .bt, v => v.encode

/-- Unified correctness of the back-translation.  For any
`isFoldFree` term at ambient BT-arity 0, the ER interpretation
of `toERUniform` equals the sort-encoded original
interpretation. -/
theorem NatBTMor1.toERUniform_interp_aux :
    {nm : ℕ × ℕ} → {σ : NatBTSort} →
    (t : NatBTMor1 nm σ) → t.isFoldFree → (h2 : nm.2 = 0) →
    (ctxN : Fin nm.1 → ℕ) →
    t.toERUniform.interp ctxN =
      σ.encodeValue
        (t.interp ctxN (h2 ▸ (Fin.elim0 : Fin 0 → BTL))) := by
  intro nm σ t
  induction t with
  | zero =>
      intro _ _ _
      simp [NatBTMor1.toERUniform, NatBTMor1.interp,
        NatBTSort.encodeValue]
  | succ x ih =>
      intro h h2 ctxN
      simp only [NatBTMor1.toERUniform,
        ERMor1.interp_comp, ERMor1.interp_succ,
        NatBTMor1.interp, NatBTSort.encodeValue]
      have := ih h h2 ctxN
      simp only [NatBTSort.encodeValue] at this
      rw [this]
  | natProj i =>
      intro _ _ _
      simp [NatBTMor1.toERUniform, NatBTMor1.interp,
        NatBTSort.encodeValue]
  | sub a b iha ihb =>
      intro h h2 ctxN
      obtain ⟨ha, hb⟩ := h
      have ea := iha ha h2 ctxN
      have eb := ihb hb h2 ctxN
      simp only [NatBTSort.encodeValue] at ea eb
      simp only [NatBTMor1.toERUniform,
        ERMor1.interp_comp, ERMor1.interp_sub,
        NatBTMor1.interp, NatBTSort.encodeValue]
      change (a.toERUniform.interp ctxN) -
        (b.toERUniform.interp ctxN) = _
      rw [ea, eb]
      rfl
  | @compNat nm nm' f gNat gBT ih_f ih_gNat _ =>
      intro h h2 ctxN
      obtain ⟨hm', hff, hgs⟩ := h
      have ih_f' :
          f.toERUniform.interp
              (fun i => (gNat i).toERUniform.interp ctxN) =
            (NatBTSort.nat).encodeValue
              (f.interp
                (fun i => (gNat i).toERUniform.interp ctxN)
                (hm' ▸ (Fin.elim0 : Fin 0 → BTL))) :=
        ih_f hff hm'
            (fun i => (gNat i).toERUniform.interp ctxN)
      simp only [NatBTSort.encodeValue] at ih_f'
      have hgeq : (fun i => (gNat i).toERUniform.interp ctxN)
          = (fun i => (gNat i).interp ctxN
              (h2 ▸ (Fin.elim0 : Fin 0 → BTL))) := by
        funext i
        have := ih_gNat i (hgs i) h2 ctxN
        simp only [NatBTSort.encodeValue] at this
        exact this
      have hBTeq :
          (fun i : Fin nm'.2 => (gBT i).interp ctxN
              (h2 ▸ (Fin.elim0 : Fin 0 → BTL))) =
            (hm' ▸ (Fin.elim0 : Fin 0 → BTL)) := by
        funext i
        have : i.val < 0 := hm' ▸ i.isLt
        exact absurd this (Nat.not_lt_zero _)
      simp only [NatBTMor1.toERUniform, hm', dif_pos,
        ERMor1.interp_comp, NatBTMor1.interp,
        NatBTSort.encodeValue]
      rw [ih_f', hgeq, hBTeq]
  | bsum f ih =>
      rename_i nm
      intro h h2 ctxN
      simp only [NatBTMor1.toERUniform,
        ERMor1.interp_bsum, NatBTMor1.interp,
        NatBTSort.encodeValue]
      apply congrArg
      funext i
      have := ih h h2 (Fin.cons i (Fin.tail ctxN))
      simp only [NatBTSort.encodeValue] at this
      exact this
  | bprod f ih =>
      rename_i nm
      intro h h2 ctxN
      simp only [NatBTMor1.toERUniform,
        ERMor1.interp_bprod, NatBTMor1.interp,
        NatBTSort.encodeValue]
      apply congrArg
      funext i
      have := ih h h2 (Fin.cons i (Fin.tail ctxN))
      simp only [NatBTSort.encodeValue] at this
      exact this
  | leafBT label ih =>
      intro h h2 ctxN
      have e := ih h h2 ctxN
      simp only [NatBTSort.encodeValue] at e
      simp only [NatBTMor1.toERUniform, NatBTMor1.interp,
        NatBTSort.encodeValue, ERMor1.interp_comp]
      have hleaf :
          ERMor1.btlEncodeLeaf.interp
              ![label.toERUniform.interp ctxN] =
            BTL.encode
              (BTL.leaf (label.toERUniform.interp ctxN)) :=
        ERMor1.interp_btlEncodeLeaf _
      change ERMor1.btlEncodeLeaf.interp
          (fun _ : Fin 1 => label.toERUniform.interp ctxN) = _
      have hfunext :
          (fun _ : Fin 1 =>
              label.toERUniform.interp ctxN) =
            ![label.toERUniform.interp ctxN] := by
        funext i
        match i with
        | ⟨0, _⟩ => rfl
      rw [hfunext, hleaf, e]
  | nodeBT l r ihl ihr =>
      intro h h2 ctxN
      obtain ⟨hl, hr⟩ := h
      have el := ihl hl h2 ctxN
      have er := ihr hr h2 ctxN
      simp only [NatBTSort.encodeValue] at el er
      simp only [NatBTMor1.toERUniform, NatBTMor1.interp,
        NatBTSort.encodeValue, ERMor1.interp_comp]
      have hfunext :
          (fun i : Fin 2 =>
              (match i with
                | ⟨0, _⟩ => l.toERUniform
                | ⟨1, _⟩ => r.toERUniform).interp ctxN) =
            ![l.toERUniform.interp ctxN,
              r.toERUniform.interp ctxN] := by
        funext i
        match i with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ => rfl
      rw [hfunext]
      rw [ERMor1.interp_btlEncodeNode]
      rw [el, er]
      rfl
  | btProj i =>
      intro _ h2 _
      exact (h2 ▸ i).elim0
  | @compBT nm nm' f gNat gBT ih_f ih_gNat _ =>
      intro h h2 ctxN
      obtain ⟨hm', hff, hgs⟩ := h
      have ih_f' :
          f.toERUniform.interp
              (fun i => (gNat i).toERUniform.interp ctxN) =
            (NatBTSort.bt).encodeValue
              (f.interp
                (fun i => (gNat i).toERUniform.interp ctxN)
                (hm' ▸ (Fin.elim0 : Fin 0 → BTL))) :=
        ih_f hff hm'
            (fun i => (gNat i).toERUniform.interp ctxN)
      simp only [NatBTSort.encodeValue] at ih_f'
      have hgeq : (fun i => (gNat i).toERUniform.interp ctxN)
          = (fun i => (gNat i).interp ctxN
              (h2 ▸ (Fin.elim0 : Fin 0 → BTL))) := by
        funext i
        have := ih_gNat i (hgs i) h2 ctxN
        simp only [NatBTSort.encodeValue] at this
        exact this
      have hBTeq :
          (fun i : Fin nm'.2 => (gBT i).interp ctxN
              (h2 ▸ (Fin.elim0 : Fin 0 → BTL))) =
            (hm' ▸ (Fin.elim0 : Fin 0 → BTL)) := by
        funext i
        have : i.val < 0 := hm' ▸ i.isLt
        exact absurd this (Nat.not_lt_zero _)
      simp only [NatBTMor1.toERUniform, hm', dif_pos,
        ERMor1.interp_comp, NatBTMor1.interp,
        NatBTSort.encodeValue]
      rw [ih_f', hgeq, hBTeq]
  | foldBTNat _ _ _ _ _ _ =>
      intro h _ _
      exact absurd h (by
        simp [NatBTMor1.isFoldFree])
  | foldBTBT _ _ _ _ _ _ =>
      intro h _ _
      exact absurd h (by
        simp [NatBTMor1.isFoldFree])
  | encodeBT t ih =>
      intro h h2 ctxN
      have e := ih h h2 ctxN
      simp only [NatBTSort.encodeValue] at e
      simp only [NatBTMor1.toERUniform, NatBTMor1.interp,
        NatBTSort.encodeValue]
      exact e
  | decodeBT k ih =>
      intro h h2 ctxN
      have e := ih h h2 ctxN
      simp only [NatBTSort.encodeValue] at e
      simp only [NatBTMor1.toERUniform, NatBTMor1.interp,
        NatBTSort.encodeValue]
      rw [e]
      exact (BTL.encode_decode _).symm

/-- Correctness of `toER` on `.nat` outputs with BT-arity 0. -/
theorem NatBTMor1.toER_interp {n : ℕ}
    (t : NatBTMor1 (n, 0) .nat) (h : t.isFoldFree)
    (ctxN : Fin n → ℕ) :
    t.toER.interp ctxN = t.interp ctxN Fin.elim0 := by
  have := NatBTMor1.toERUniform_interp_aux t h rfl ctxN
  simpa [NatBTMor1.toER, NatBTSort.encodeValue] using this

/-- Correctness of `toER_bt` on `.bt` outputs with BT-arity 0:
value equals `BTL.encode` of the interpreted tree. -/
theorem NatBTMor1.toER_bt_interp {n : ℕ}
    (t : NatBTMor1 (n, 0) .bt) (h : t.isFoldFree)
    (ctxN : Fin n → ℕ) :
    t.toER_bt.interp ctxN =
      BTL.encode (t.interp ctxN Fin.elim0) := by
  have := NatBTMor1.toERUniform_interp_aux t h rfl ctxN
  simpa [NatBTMor1.toER_bt, NatBTSort.encodeValue] using this

/-- Tuple-level back-translation at BT-arity 0.  Transports
each `.nat` component through `toER`; the output BT arity is
0 so there are no BT components to emit. -/
def NatBTMorN.toER {n m : ℕ}
    (f : NatBTMorN (n, 0) (m, 0)) : ERMorN n m :=
  fun i => (f.natComps i).toER

/-- Correctness of the tuple-level back-translation. -/
theorem NatBTMorN.toER_interp {n m : ℕ}
    (f : NatBTMorN (n, 0) (m, 0))
    (h : ∀ i, (f.natComps i).isFoldFree)
    (ctxN : Fin n → ℕ) :
    f.toER.interp ctxN = (f.interp ctxN Fin.elim0).1 := by
  funext i
  exact (f.natComps i).toER_interp (h i) ctxN

end GebLean

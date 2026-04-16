import GebLean.LawvereTreeERInterp
import GebLean.Utilities.SzudzikSeq

/-!
# Tree-ER Syntactic Arithmetic

Tree-ER term encodings of the Layer-1 arithmetic from
`GebLean/Utilities/SzudzikSeq.lean`.  Each primitive is a
concrete `TreeERMor1` term; for each, an `@[simp]` agreement
theorem links its interpretation to the Layer-1 function via
`encodeBT` / `decodeBT`.
-/

namespace GebLean

/-- Tree-ER term realizing course-of-values recursion on a
BT input.  Parameters `base` and `step` are depth-0 terms for
the leaf value and the branching combinator; the resulting
term has depth 1 (exactly one fold layer over depth-0
ingredients), leaving two levels of depth budget for
downstream compositions that fold this term itself. -/
def TreeERMor1.treeFoldOnCode
    (base : TreeERMor1_0 0) (step : TreeERMor1_0 2) :
    TreeERMor1_1 1 :=
  TreeERMor1_1.fold1
    (TreeERMor1_0.comp base Fin.elim0)
    step
    (TreeERMor1_0.proj 0)

private theorem treeFoldOnCode_fold_agreement_gen
    {x : PUnit.{1}}
    (baseB : BT.{0}) (stepB : BT.{0} → BT.{0} → BT.{0})
    (t : PolyFreeM
      (overTerminal PUnit.{1})
      polyProdType x) :
    BT.fold baseB stepB t =
      decodeBT (BT.fold
        (encodeBT baseB)
        (fun l r => encodeBT
          (stepB (decodeBT l) (decodeBT r)))
        t) := by
  induction t with
  | mk y idx children ih =>
    match idx with
    | Sum.inl leafIdx =>
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
      have hli :
          leafIdx = ⟨PUnit.unit, rfl⟩ :=
        Subtype.ext (PUnit.eq_punit _)
      subst hli
      have hleaf :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{1})
                polyProdType) PUnit.unit from
              Sum.inl ⟨PUnit.unit, rfl⟩)
            children =
          BT.leaf := by
        unfold BT.leaf polyFreeMPure
        congr 1
        funext e; exact PEmpty.elim e
      rw [hleaf, BT.fold_leaf, BT.fold_leaf,
          decodeBT_encodeBT]
    | Sum.inr nodeIdx =>
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{1})
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BT.node
            (children (Sum.inl PUnit.unit))
            (children (Sum.inr PUnit.unit)) := by
        unfold BT.node polyProdFreeMNode
          polyFreeMStrFamily
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hmk, BT.fold_node, BT.fold_node,
          decodeBT_encodeBT,
          ih (Sum.inl PUnit.unit),
          ih (Sum.inr PUnit.unit)]

/-- Auxiliary fold identity: `BT.fold` over a BT carrier
produces the same result as decoding the `Nat`-coded fold.
The step function wraps BT values as codes before the user's
step and decodes the result, so the encoding round-trips on
each node. -/
private theorem treeFoldOnCode_fold_agreement
    (baseB : BT.{0}) (stepB : BT.{0} → BT.{0} → BT.{0})
    (t : BT.{0}) :
    BT.fold baseB stepB t =
      decodeBT (Nat.treeFoldOnCode
        (encodeBT baseB)
        (fun l r => encodeBT
          (stepB (decodeBT l) (decodeBT r)))
        (encodeBT t)) := by
  rw [GebLean.treeFoldOnCode_encodeBT]
  exact treeFoldOnCode_fold_agreement_gen baseB stepB t

private theorem fold_fin1_eq_scalar_fold_gen
    {x : PUnit.{1}}
    (baseB : BT.{0})
    (stepB : BT.{0} → BT.{0} → BT.{0})
    (t : PolyFreeM
      (overTerminal PUnit.{1})
      polyProdType x) :
    BT.fold baseB stepB t =
      BT.fold
        (α := Fin 1 → BT.{0})
        (fun _ => baseB)
        (fun leftAll rightAll _ =>
          stepB (leftAll 0) (rightAll 0))
        t 0 := by
  induction t with
  | mk y idx children ih =>
    match idx with
    | Sum.inl leafIdx =>
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
      have hli :
          leafIdx = ⟨PUnit.unit, rfl⟩ :=
        Subtype.ext (PUnit.eq_punit _)
      subst hli
      have hleaf :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{1})
                polyProdType) PUnit.unit from
              Sum.inl ⟨PUnit.unit, rfl⟩)
            children =
          BT.leaf := by
        unfold BT.leaf polyFreeMPure
        congr 1
        funext e; exact PEmpty.elim e
      rw [hleaf, BT.fold_leaf, BT.fold_leaf]
    | Sum.inr nodeIdx =>
      have hy : y = PUnit.unit :=
        PUnit.eq_punit y
      subst hy
      have hni : nodeIdx = PUnit.unit :=
        PUnit.eq_punit nodeIdx
      subst hni
      have hmk :
          PolyFix.mk PUnit.unit
            (show polyBetweenIndex PUnit PUnit
              (polyTranslate
                (overTerminal PUnit.{1})
                polyProdType) PUnit.unit from
              Sum.inr PUnit.unit)
            children =
          BT.node
            (children (Sum.inl PUnit.unit))
            (children (Sum.inr PUnit.unit)) := by
        unfold BT.node polyProdFreeMNode
          polyFreeMStrFamily
        congr 1
        funext e
        match e with
        | Sum.inl _ => rfl
        | Sum.inr _ => rfl
      rw [hmk, BT.fold_node, BT.fold_node,
          ih (Sum.inl PUnit.unit),
          ih (Sum.inr PUnit.unit)]

/-- A single-slot BT-valued fold equals the `Fin 1 →
BT`-valued fold of its constantly-extended parameters,
evaluated at slot 0.  Used to bridge the `fold1` form (which
operates at carrier `Fin 1 → BT`) to a plain BT-to-BT
fold. -/
private theorem fold_fin1_eq_scalar_fold
    (baseB : BT.{0})
    (stepB : BT.{0} → BT.{0} → BT.{0})
    (t : BT.{0}) :
    BT.fold baseB stepB t =
      BT.fold
        (α := Fin 1 → BT.{0})
        (fun _ => baseB)
        (fun leftAll rightAll _ =>
          stepB (leftAll 0) (rightAll 0))
        t 0 :=
  fold_fin1_eq_scalar_fold_gen baseB stepB t

@[simp] theorem TreeERMor1.treeFoldOnCode_interp
    (base : TreeERMor1_0 0) (step : TreeERMor1_0 2)
    (ctx : Fin 1 → BT.{0}) :
    (TreeERMor1.treeFoldOnCode base step).interp ctx =
      decodeBT (Nat.treeFoldOnCode
        (encodeBT (base.interp Fin.elim0))
        (fun l r => encodeBT
          (step.interp
            (fun i => Fin.cases (decodeBT l)
              (fun _ => decodeBT r) i)))
        (encodeBT (ctx 0))) := by
  unfold TreeERMor1.treeFoldOnCode
  simp only [TreeERMor1_1.interp, TreeERMor1_1.fold1,
    TreeERMor1_1.fold, TreeMor1.interp_fold,
    TreeERMor1_0.interp, TreeERMor1_0.proj,
    TreeMor1.interp_proj, TreeERMor1_0.comp,
    TreeMor1.interp_comp]
  set baseB : BT.{0} := base.val.interp Fin.elim0
    with hbaseB
  set stepB : BT.{0} → BT.{0} → BT.{0} :=
    fun L R =>
      step.val.interp
        (fun i => Fin.cases L (fun _ => R) i)
    with hstepB
  rw [← treeFoldOnCode_fold_agreement baseB stepB (ctx 0),
      fold_fin1_eq_scalar_fold baseB stepB (ctx 0)]
  have hbase_eq :
      (fun (_ : Fin 1) =>
        base.val.interp
          (fun (i : Fin 0) =>
            ((Fin.elim0 i : TreeERMor1_0 1).val).interp
              ctx)) =
        (fun (_ : Fin 1) => baseB) := by
    funext _
    simp only [hbaseB]
    congr 1
    funext j
    exact j.elim0
  have hstep_eq :
      (fun (leftAll rightAll : Fin 1 → BT.{0})
          (_ : Fin 1) =>
        step.val.interp (finAppend leftAll rightAll)) =
        (fun (leftAll rightAll : Fin 1 → BT.{0})
            (_ : Fin 1) =>
          stepB (leftAll 0) (rightAll 0)) := by
    funext leftAll rightAll _
    simp only [hstepB]
    congr 1
    funext i
    refine Fin.cases ?_ ?_ i
    · change finAppend leftAll rightAll 0 = leftAll 0
      simp only [finAppend, Fin.val_zero,
        Nat.zero_lt_succ, dite_true]
      congr
    · intro k
      have hk : k = 0 := Fin.eq_zero k
      subst hk
      change finAppend leftAll rightAll 1 = rightAll 0
      simp only [finAppend]
      rfl
  rw [hbase_eq, hstep_eq]

end GebLean

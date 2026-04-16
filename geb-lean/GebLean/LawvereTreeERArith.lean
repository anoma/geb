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
  refine BT.ind (motive := fun t =>
    BT.fold baseB stepB t =
      decodeBT (BT.fold
        (encodeBT baseB)
        (fun l r => encodeBT
          (stepB (decodeBT l) (decodeBT r)))
        t)) ?_ ?_ t
  · change BT.fold baseB stepB BT.leaf = _
    rw [BT.fold_leaf, BT.fold_leaf, decodeBT_encodeBT]
  · intro l r hl hr
    change BT.fold baseB stepB (BT.node l r) = _
    rw [BT.fold_node, BT.fold_node, decodeBT_encodeBT,
        hl, hr]

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
        (fun l r _ => stepB (l 0) (r 0))
        t 0 := by
  refine BT.ind (motive := fun t =>
    BT.fold baseB stepB t =
      BT.fold
        (α := Fin 1 → BT.{0})
        (fun _ => baseB)
        (fun l r _ => stepB (l 0) (r 0))
        t 0) ?_ ?_ t
  · change BT.fold baseB stepB BT.leaf = _
    rw [BT.fold_leaf, BT.fold_leaf]
  · intro l r hl hr
    change BT.fold baseB stepB (BT.node l r) = _
    rw [BT.fold_node, BT.fold_node, hl, hr]

@[simp] theorem TreeERMor1.treeFoldOnCode_interp
    (base : TreeERMor1_0 0) (step : TreeERMor1_0 2)
    (ctx : Fin 1 → BT.{0}) :
    (TreeERMor1.treeFoldOnCode base step).interp ctx =
      decodeBT (Nat.treeFoldOnCode
        (encodeBT (base.interp Fin.elim0))
        (fun l r => encodeBT
          (step.interp
            (Fin.cases (decodeBT l)
              (fun _ => decodeBT r))))
        (encodeBT (ctx 0))) := by
  unfold TreeERMor1.treeFoldOnCode
  simp only [TreeERMor1_1.interp, TreeERMor1_1.fold1,
    TreeERMor1_1.fold, TreeMor1.interp_fold,
    TreeERMor1_0.interp, TreeERMor1_0.proj,
    TreeMor1.interp_proj, TreeERMor1_0.comp,
    TreeMor1.interp_comp]
  let baseB : BT.{0} := base.val.interp Fin.elim0
  let stepB : BT.{0} → BT.{0} → BT.{0} :=
    fun L R =>
      step.val.interp (Fin.cases L (fun _ => R))
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
    congr 1
    funext j
    exact j.elim0
  have hstep_eq :
      (fun (l r : Fin 1 → BT.{0}) (_ : Fin 1) =>
        step.val.interp (finAppend l r)) =
        (fun (l r : Fin 1 → BT.{0}) (_ : Fin 1) =>
          stepB (l 0) (r 0)) := by
    funext l r _
    congr 1
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro k
      have hk : k = 0 := Fin.eq_zero k
      subst hk
      rw [Fin.cases_succ]
      simp
  rw [hbase_eq, hstep_eq]

end GebLean

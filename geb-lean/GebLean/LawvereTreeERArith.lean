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

/-- Multi-slot course-of-values recursion as a tree-ER
term.  At the `Nat` level, runs
`Nat.mutuTreeFoldOnCode` on the Gödel code of the
input; at the tree level, this is an `m`-slot
`BT.fold` over the input.  `base` and `step` are
depth-0 ingredients — `base` has arity 1 (outer-ctx
access at leaves), `step` has arity `m + m` (the `m`
slot values from each recursive branch).  The
resulting term has depth 1, leaving headroom for
depth-2 compositions. -/
def TreeERMor1.mutuFoldOnCode {m : ℕ}
    (base : Fin m → TreeERMor1_0 1)
    (step : Fin m → TreeERMor1_0 (m + m))
    (j : Fin m) :
    TreeERMor1_1 1 :=
  TreeERMor1_1.fold base step (TreeERMor1_0.proj 0) j

/-- Multi-slot generalization of
`treeFoldOnCode_fold_agreement`: a multi-slot `BT.fold`
at carrier `Fin m → BT` agrees with the
`decodeBT`-wrapped `Nat.mutuTreeFoldOnCode` whose step
encodes BT values as codes and decodes them back on
each recursive call.  Stated on the whole
`Fin m → BT` tuple (not per-slot) so the `BT.node`
inductive step can rewrite the child tuples directly
via the inductive hypotheses. -/
private theorem mutuFoldOnCode_fold_agreement {m : ℕ}
    (baseB : Fin m → BT.{0})
    (stepB : (Fin m → BT.{0}) → (Fin m → BT.{0}) →
      Fin m → BT.{0})
    (t : BT.{0}) :
    BT.fold (α := Fin m → BT.{0}) baseB stepB t =
      (fun j => decodeBT (Nat.mutuTreeFoldOnCode
        (fun i => encodeBT (baseB i))
        (fun lAll rAll i => encodeBT
          (stepB (fun k => decodeBT (lAll k))
                 (fun k => decodeBT (rAll k)) i))
        (encodeBT t) j)) := by
  have hrw :
      (fun j : Fin m => decodeBT
        (Nat.mutuTreeFoldOnCode
          (fun i => encodeBT (baseB i))
          (fun lAll rAll i => encodeBT
            (stepB (fun k => decodeBT (lAll k))
                   (fun k => decodeBT (rAll k)) i))
          (encodeBT t) j)) =
      (fun j : Fin m => decodeBT
        (BT.fold (α := Fin m → ℕ)
          (fun i => encodeBT (baseB i))
          (fun lAll rAll i => encodeBT
            (stepB (fun k => decodeBT (lAll k))
                   (fun k => decodeBT (rAll k)) i))
          t j)) := by
    funext j
    rw [GebLean.mutuTreeFoldOnCode_encodeBT]
  rw [hrw]
  refine BT.ind (motive := fun t =>
    BT.fold (α := Fin m → BT.{0}) baseB stepB t =
      (fun j : Fin m => decodeBT
        (BT.fold (α := Fin m → ℕ)
          (fun i => encodeBT (baseB i))
          (fun lAll rAll i => encodeBT
            (stepB (fun k => decodeBT (lAll k))
                   (fun k => decodeBT (rAll k)) i))
          t j))) ?_ ?_ t
  · change BT.fold (α := Fin m → BT.{0}) baseB stepB
      BT.leaf = _
    rw [BT.fold_leaf]
    funext j
    rw [BT.fold_leaf, decodeBT_encodeBT]
  · intro l r hl hr
    change BT.fold (α := Fin m → BT.{0}) baseB stepB
      (BT.node l r) = _
    rw [BT.fold_node]
    funext j
    rw [BT.fold_node, decodeBT_encodeBT]
    have hleft : (fun k : Fin m => decodeBT
        (BT.fold (α := Fin m → ℕ)
          (fun i => encodeBT (baseB i))
          (fun lAll rAll i => encodeBT
            (stepB (fun k => decodeBT (lAll k))
                   (fun k => decodeBT (rAll k)) i))
          l k)) =
        BT.fold (α := Fin m → BT.{0}) baseB stepB l :=
      hl.symm
    have hright : (fun k : Fin m => decodeBT
        (BT.fold (α := Fin m → ℕ)
          (fun i => encodeBT (baseB i))
          (fun lAll rAll i => encodeBT
            (stepB (fun k => decodeBT (lAll k))
                   (fun k => decodeBT (rAll k)) i))
          r k)) =
        BT.fold (α := Fin m → BT.{0}) baseB stepB r :=
      hr.symm
    rw [hleft, hright]

@[simp] theorem TreeERMor1.mutuFoldOnCode_interp
    {m : ℕ}
    (base : Fin m → TreeERMor1_0 1)
    (step : Fin m → TreeERMor1_0 (m + m))
    (j : Fin m) (ctx : Fin 1 → BT.{0}) :
    (TreeERMor1.mutuFoldOnCode base step j).interp ctx =
      decodeBT (Nat.mutuTreeFoldOnCode
        (fun i => encodeBT ((base i).interp ctx))
        (fun leftAll rightAll i =>
          encodeBT ((step i).interp
            (finAppend
              (fun k => decodeBT (leftAll k))
              (fun k => decodeBT (rightAll k)))))
        (encodeBT (ctx 0)) j) := by
  unfold TreeERMor1.mutuFoldOnCode
  simp only [TreeERMor1_1.interp, TreeERMor1_1.fold,
    TreeMor1.interp_fold, TreeERMor1_0.interp,
    TreeERMor1_0.proj, TreeMor1.interp_proj]
  let baseB : Fin m → BT.{0} :=
    fun i => (base i).val.interp ctx
  let stepB : (Fin m → BT.{0}) → (Fin m → BT.{0}) →
      Fin m → BT.{0} :=
    fun lAll rAll i =>
      (step i).val.interp (finAppend lAll rAll)
  have hagree :=
    mutuFoldOnCode_fold_agreement baseB stepB (ctx 0)
  have heq : (fun i : Fin m =>
      (base i).val.interp ctx) = baseB := rfl
  have hstepeq :
      (fun (lAll rAll : Fin m → BT.{0}) (j' : Fin m) =>
        (step j').val.interp (finAppend lAll rAll)) =
        stepB := rfl
  rw [heq, hstepeq]
  rw [hagree]

end GebLean

import GebLean.LawvereTreeERInterp
import GebLean.Utilities.SzudzikSeq
import GebLean.Utilities.RegisterMachine

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

/-!
## Register-machine simulation blueprint

The following combinator packages abstract register-machine iteration
into a depth-≤-2 tree-ER term.  Inputs are:

* an abstract `RegisterMachine` (Layer 1) specifying states,
  registers, and transition;
* a tree-ER realization of one transition step, expressed as a
  depth-0 term operating on a single BT-encoded configuration;
* a tree-ER realization of the initial configuration, expressed
  as a depth-0 term;
* a depth-0 readout mapping the final configuration to the output
  register's value.

The iteration count equals the number of `BT.node` visits in the
structural fold over the input tree — i.e. `BT.fold` on the input
interpreted as the time budget.  Downstream arithmetic primitives
(Tasks 10–13) supply configuration encodings realizing their
specific transitions.
-/

/-- Tree-ER realization of a register-machine step, as a
depth-0 tree function on a single BT-encoded configuration.
Callers supply both the tree-level realization (`realize`) and
a proof that it agrees with the abstract `step` on codes via a
chosen `encodeConfig` / `decodeConfig` pair.  The realization
takes one BT argument (the current config) and returns one BT
(the next config). -/
structure RegisterMachineRealization
    (M : GebLean.RegisterMachine.RegisterMachine) where
  /-- Encode a configuration as a single `BT`. -/
  encodeConfig :
    GebLean.RegisterMachine.Config M → BT.{0}
  /-- Decode a `BT` back to a configuration.  Only required to be
  a left inverse of `encodeConfig` (`decode_encode`). -/
  decodeConfig :
    BT.{0} → GebLean.RegisterMachine.Config M
  /-- Round-trip: decoding an encoded config returns the original
  config.  No section-side (`encode_decode`) property is imposed,
  which lets implementors use non-injective BT encodings. -/
  decode_encode :
    ∀ c : GebLean.RegisterMachine.Config M,
      decodeConfig (encodeConfig c) = c
  /-- Depth-0 tree-ER term realizing one transition step on
  the encoded configuration.  Arity 1: takes the current
  encoded config and produces the next. -/
  stepRealize : TreeERMor1_0 1
  /-- Correctness of the step realization: interpreting
  `stepRealize` on an encoded configuration equals encoding the
  result of `RegisterMachine.step`. -/
  stepRealize_interp :
    ∀ c : GebLean.RegisterMachine.Config M,
      stepRealize.interp
        (fun _ => encodeConfig c) =
        encodeConfig (GebLean.RegisterMachine.step M c)

/-- Run the abstract register machine for `k` steps,
with `k` derived from iterating `step` along the
right-spine of a given BT.  The return value is the final
configuration. -/
private def runRightSpine
    {M : GebLean.RegisterMachine.RegisterMachine}
    (c₀ : GebLean.RegisterMachine.Config M)
    (t : BT.{0}) : GebLean.RegisterMachine.Config M :=
  BT.fold c₀
    (fun _ r => GebLean.RegisterMachine.step M r) t

@[simp] private theorem runRightSpine_leaf
    {M : GebLean.RegisterMachine.RegisterMachine}
    (c₀ : GebLean.RegisterMachine.Config M) :
    runRightSpine (M := M) c₀ BT.leaf = c₀ := by
  unfold runRightSpine; rw [BT.fold_leaf]

@[simp] private theorem runRightSpine_node
    {M : GebLean.RegisterMachine.RegisterMachine}
    (c₀ : GebLean.RegisterMachine.Config M)
    (l r : BT.{0}) :
    runRightSpine (M := M) c₀ (BT.node l r) =
      GebLean.RegisterMachine.step M
        (runRightSpine (M := M) c₀ r) := by
  unfold runRightSpine; rw [BT.fold_node]

/-- Step ingredient for `simulateRegisterMachine`: lift a
depth-0 1-ary step function to a depth-0 2-ary fold step that
applies the 1-ary step to the right-child accumulator.  The
left-child accumulator is ignored.  The resulting fold iterates
the step function once per right-descent in the input tree. -/
private def stepRightAccum
    (stepTerm : TreeERMor1_0 1) : TreeERMor1_0 (1 + 1) :=
  TreeERMor1_0.comp stepTerm
    (fun _ => TreeERMor1_0.proj (1 : Fin 2))

/-- Tree-ER term simulating a register machine.  The
`initialConfig` is a depth-0 term producing the encoded starting
configuration.  The `stepTerm` is a depth-0 1-ary term realizing
one transition step on the encoded configuration.  The
`timeBound` is a depth-1 term producing a BT whose right-spine
length determines the iteration count: one `stepTerm`
application per right-descent in `timeBound.interp ctx`.
Implemented as a depth-2 fold whose `tree` argument is the
depth-1 `timeBound`, with depth-0 base and step lifted to
depth-1 via `toDepth1`. -/
def TreeERMor1.simulateRM {n : ℕ}
    (initialConfig : TreeERMor1_0 n)
    (stepTerm : TreeERMor1_0 1)
    (timeBound : TreeERMor1_1 n) :
    TreeERMor1 n :=
  TreeERMor1.fold1
    (base := initialConfig.toDepth1)
    (step := (stepRightAccum stepTerm).toDepth1)
    (tree := timeBound)

/-- Agreement lemma for `simulateRM`: interpreting the
simulation term equals iterating the step function once per
right-descent in the `timeBound` tree, starting from the
initial value.  Stated purely at the tree level; higher-level
callers compose with `RegisterMachineRealization.stepRealize_interp`
and `runRightSpine` to obtain the register-machine semantics. -/
@[simp] theorem TreeERMor1.simulateRM_interp
    {n : ℕ}
    (initialConfig : TreeERMor1_0 n)
    (stepTerm : TreeERMor1_0 1)
    (timeBound : TreeERMor1_1 n)
    (ctx : Fin n → BT.{0}) :
    (TreeERMor1.simulateRM initialConfig stepTerm
        timeBound).interp ctx =
      BT.fold (initialConfig.interp ctx)
        (fun _ r => stepTerm.interp (fun _ => r))
        (timeBound.interp ctx) := by
  unfold TreeERMor1.simulateRM TreeERMor1.fold1
    TreeERMor1.fold
  simp only [TreeERMor1.interp, TreeMor1.interp_fold,
    TreeERMor1_0.toDepth1]
  change
    BT.fold (α := Fin 1 → BT.{0})
      (fun _ => initialConfig.val.interp ctx)
      (fun l r _ =>
        (stepRightAccum stepTerm).val.interp
          (finAppend l r))
      (timeBound.val.interp ctx) 0 =
    BT.fold (initialConfig.interp ctx)
      (fun _ r => stepTerm.interp (fun _ => r))
      (timeBound.interp ctx)
  have hstep_eq :
      (fun (l r : Fin 1 → BT.{0}) (_ : Fin 1) =>
        (stepRightAccum stepTerm).val.interp
          (finAppend l r)) =
      (fun (l r : Fin 1 → BT.{0}) (_ : Fin 1) =>
        stepTerm.interp (fun _ => r 0)) := by
    funext l r _
    unfold stepRightAccum
    simp only [TreeERMor1_0.comp, TreeERMor1_0.proj,
      TreeMor1.interp_comp, TreeMor1.interp_proj]
    congr 1
  rw [hstep_eq]
  refine BT.ind (motive := fun t =>
    BT.fold (α := Fin 1 → BT.{0})
      (fun _ => initialConfig.val.interp ctx)
      (fun _ r _ => stepTerm.interp (fun _ => r 0)) t 0 =
    BT.fold (initialConfig.interp ctx)
      (fun _ r => stepTerm.interp (fun _ => r))
      t) ?_ ?_ (timeBound.val.interp ctx)
  · change
      BT.fold (α := Fin 1 → BT.{0}) _ _ BT.leaf 0 = _
    rw [BT.fold_leaf]
    rfl
  · intro l r _ hr
    change
      BT.fold (α := Fin 1 → BT.{0}) _ _
        (BT.node l r) 0 = _
    rw [BT.fold_node, BT.fold_node]
    congr 1
    funext _
    have hr' :
        BT.fold (α := Fin 1 → BT.{0})
          (fun _ => initialConfig.val.interp ctx)
          (fun _ r _ =>
            stepTerm.interp (fun _ => r 0)) r 0 =
        BT.fold (initialConfig.interp ctx)
          (fun _ r => stepTerm.interp (fun _ => r)) r := hr
    exact hr'

/-- Register-machine agreement specialization of
`simulateRM_interp`: when the `stepTerm` is a realization of a
register-machine step (per `RegisterMachineRealization`), the
simulation result equals `encodeConfig` applied to
`runRightSpine`, i.e. the abstract machine run for
`rightSpineLength(timeBound.interp ctx)` steps. -/
theorem TreeERMor1.simulateRM_interp_rm
    {n : ℕ}
    (M : GebLean.RegisterMachine.RegisterMachine)
    (realization : RegisterMachineRealization M)
    (initialConfig : TreeERMor1_0 n)
    (timeBound : TreeERMor1_1 n)
    (ctx : Fin n → BT.{0})
    (initConfig : GebLean.RegisterMachine.Config M)
    (hInit :
      initialConfig.interp ctx =
        realization.encodeConfig initConfig) :
    (TreeERMor1.simulateRM initialConfig
        realization.stepRealize timeBound).interp ctx =
      realization.encodeConfig
        (runRightSpine (M := M) initConfig
          (timeBound.interp ctx)) := by
  rw [TreeERMor1.simulateRM_interp, hInit]
  refine BT.ind (motive := fun t =>
    BT.fold (realization.encodeConfig initConfig)
      (fun _ r =>
        realization.stepRealize.interp (fun _ => r)) t =
    realization.encodeConfig
      (runRightSpine (M := M) initConfig t))
    ?_ ?_ (timeBound.interp ctx)
  · change BT.fold _ _ BT.leaf = _
    rw [BT.fold_leaf, runRightSpine_leaf]
  · intro l r _ hr
    change BT.fold _ _ (BT.node l r) = _
    rw [BT.fold_node, runRightSpine_node, hr]
    exact realization.stepRealize_interp
      (runRightSpine (M := M) initConfig r)

end GebLean

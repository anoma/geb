import GebLean.LawvereTreeER

/-!
# Tests for LawvereTreeER

Sanity tests for TreeMor1, smart constructors,
interpretation, depth tiers, and the mutumorphism
primitive.
-/

open GebLean

-- TreeMor1.foldDepth reduces by rfl on each
-- constructor.
#guard TreeMor1.foldDepth
  (TreeMor1.leaf (n := 0)) = 0
#guard TreeMor1.foldDepth
  (TreeMor1.proj (n := 2) 0) = 0
#guard TreeMor1.foldDepth (TreeMor1.branch
  (TreeMor1.leaf (n := 0))
  (TreeMor1.leaf (n := 0))) = 0
#guard TreeMor1.foldDepth
  (TreeMor1.comp (n := 0) (k := 0)
    TreeMor1.leaf
    (fun i : Fin 0 => i.elim0)) = 0

-- Depth-0 smart constructors type-check.
example : TreeERMor1_0 3 := TreeERMor1_0.leaf
example : TreeERMor1_0 3 := TreeERMor1_0.proj 1

-- Depth-0 branch type-checks.
example : TreeERMor1_0 3 :=
  TreeERMor1_0.branch
    TreeERMor1_0.leaf
    (TreeERMor1_0.proj 0)

-- Depth-0 comp type-checks.
example : TreeERMor1_0 2 :=
  TreeERMor1_0.comp (k := 1)
    TreeERMor1_0.leaf
    (fun _ => TreeERMor1_0.proj 0)

-- Depth-1 fold type-checks.
example : TreeERMor1_1 1 :=
  TreeERMor1_1.fold1
    (TreeERMor1_0.leaf (n := 1))
    (TreeERMor1_0.proj (n := 1 + 1) 0)
    (TreeERMor1_0.leaf (n := 1))

-- Depth-2 nested fold type-checks.
example : TreeERMor1 1 :=
  TreeERMor1.fold1
    (TreeERMor1_1.fold1
      (TreeERMor1_0.leaf (n := 1))
      (TreeERMor1_0.proj (n := 1 + 1) 0)
      (TreeERMor1_0.leaf (n := 1)))
    (TreeERMor1_1.proj (n := 1 + 1) 0)
    (TreeERMor1_1.leaf (n := 1))

-- Widening lifts type-check.
example : TreeERMor1 3 :=
  TreeERMor1_0.leaf.toDepth2
example : TreeERMor1_1 3 :=
  TreeERMor1_0.leaf.toDepth1

-- Interpretation of leaf is BT.leaf.
example : (TreeERMor1_0.leaf (n := 0)).interp
    (fun i : Fin 0 => i.elim0) = BT.leaf :=
  rfl

-- Interpretation of proj returns the context
-- element.
example : (TreeERMor1_0.proj (n := 1) 0).interp
    (fun _ => BT.leaf) = BT.leaf :=
  rfl

-- Interpretation of branch produces node.
example :
    (TreeERMor1_0.branch
      (TreeERMor1_0.leaf (n := 0))
      (TreeERMor1_0.leaf (n := 0))).interp
    (fun i : Fin 0 => i.elim0) =
    BT.node BT.leaf BT.leaf :=
  rfl

-- Composition: comp (branch leaf (proj 0)) [leaf]
-- maps proj 0 to leaf, yielding branch leaf leaf.
example :
    (TreeERMor1_0.comp (k := 1)
      (TreeERMor1_0.branch
        (TreeERMor1_0.leaf (n := 1))
        (TreeERMor1_0.proj (n := 1) 0))
      (fun _ =>
        TreeERMor1_0.leaf (n := 0))).interp
    (fun i : Fin 0 => i.elim0) =
    BT.node BT.leaf BT.leaf :=
  rfl

-- foldDepth of comp is max of parts.
#guard (TreeERMor1_0.comp (k := 1)
  (TreeERMor1_0.branch
    (TreeERMor1_0.leaf (n := 1))
    (TreeERMor1_0.proj (n := 1) 0))
  (fun _ =>
    TreeERMor1_0.leaf (n := 2))).val.foldDepth = 0

-- foldDepth of fold is 1 + max of parts.
#guard (TreeERMor1_1.fold1
  (TreeERMor1_0.leaf (n := 1))
  (TreeERMor1_0.proj (n := 1 + 1) 0)
  (TreeERMor1_0.leaf (n := 1))).val.foldDepth = 1

-- MutuFold type-checks at depth 1.
example : TreeERMorN_1 2 1 :=
  TreeERMor1_1.mutuFold
    (fun _ => TreeERMor1_0.leaf (n := 2))
    (fun _ =>
      TreeERMor1_0.proj (n := 1 + 1) 0)
    (TreeERMor1_0.proj (n := 2) 0)

-- MutuFold type-checks at depth 2.
example : TreeERMorN 2 1 :=
  TreeERMor1.mutuFold
    (fun _ => TreeERMor1_1.leaf (n := 2))
    (fun _ =>
      TreeERMor1_1.proj (n := 1 + 1) 0)
    (TreeERMor1_1.proj (n := 2) 0)

-- TreeERMorN identity interprets as identity.
example : (TreeERMorN.id 2).interp
    (fun i : Fin 2 =>
      if i.val = 0 then BT.leaf
      else BT.node BT.leaf BT.leaf) =
    (fun i : Fin 2 =>
      if i.val = 0 then BT.leaf
      else BT.node BT.leaf BT.leaf) :=
  rfl

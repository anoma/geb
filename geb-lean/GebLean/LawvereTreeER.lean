import GebLean.LawvereBT

/-!
# Tree-Native Elementary Recursive Morphisms

Depth-2-bounded fragment of `BTMor1`, presenting elementary recursive
functions in their tree-native form (Leivant 1999; Beckmann-Weiermann
2000).  Subtype over `BTMor1` so that every BT computation lemma
applies after `.val` unwrapping; tier aliases
`TreeERMor1_0`, `TreeERMor1_1`, `TreeERMor1` give static depth-
tracking at the smart-constructor level.
-/

namespace GebLean

/-- Step function for `BTMor1.foldDepth`.  One arm per
component of `btMorPoly`.  Factored out so that
`BTMor1.ind` computation rules can reduce each
constructor case by `simp only [foldDepthStep]`. -/
def foldDepthStep :
    ∀ (i : Fin 4) {n : ℕ}
      (p : polyBetweenIndex ℕ ℕ
        (btMorComponents i) n)
      (_ :
        ∀ e : (polyBetweenFamily ℕ ℕ
          (btMorComponents i) n p).left,
          BTMor1
            ((polyBetweenFamily ℕ ℕ
              (btMorComponents i) n
                p).hom e))
      (_ :
        ∀ _ : (polyBetweenFamily ℕ ℕ
          (btMorComponents i) n p).left, ℕ),
      ℕ :=
  fun i => match i with
    | ⟨0, _⟩ => fun _ _ _ => 0
    | ⟨1, _⟩ => fun _ _ _ => 0
    | ⟨2, _⟩ => fun _ _ ih =>
        max (ih (Sum.inl PUnit.unit))
            (ih (Sum.inr PUnit.unit))
    | ⟨3, _⟩ => fun pos _ ih =>
        let pm := pos.1
        have hlb (i : Fin pm) :
            i.val < pm + pm + 1 :=
          Nat.lt_of_lt_of_le i.isLt
            (Nat.le_add_right pm (pm + 1))
        have hls (i : Fin pm) :
            pm + i.val < pm + pm + 1 := by
          have := i.isLt; omega
        have hlt : pm + pm < pm + pm + 1 :=
          Nat.lt_succ_self _
        1 + max (max
          ((Finset.univ : Finset (Fin pm)).sup
            (fun i => ih ⟨i.val, hlb i⟩))
          ((Finset.univ : Finset (Fin pm)).sup
            (fun i => ih ⟨pm + i.val, hls i⟩)))
          (ih ⟨pm + pm, hlt⟩)

/-- Maximum nesting depth of `fold` constructors in a `BTMor1` term.
Used to carve out depth-bounded subtypes for the tree-native
elementary-recursive Lawvere theory. -/
def BTMor1.foldDepth {n : ℕ} (t : BTMor1 n) : ℕ :=
  BTMor1.ind
    (motive := fun {_} _ => ℕ)
    (step := foldDepthStep)
    t

@[simp] theorem BTMor1.foldDepth_proj {n : ℕ} (i : Fin n) :
    (BTMor1.proj i).foldDepth = 0 := rfl

@[simp] theorem BTMor1.foldDepth_leaf {n : ℕ} :
    (@BTMor1.leaf n).foldDepth = 0 := rfl

@[simp] theorem BTMor1.foldDepth_branch {n : ℕ}
    (l r : BTMor1 n) :
    (BTMor1.branch l r).foldDepth =
      max l.foldDepth r.foldDepth := rfl

/-- `foldDepth` on a transported term equals
`foldDepth` on the original term. -/
private theorem BTMor1.foldDepth_cast {a b : ℕ}
    (h : a = b) (t : BTMor1 a) :
    (h ▸ t).foldDepth = t.foldDepth := by
  subst h; rfl

private theorem BTMor1.foldDepth_snd_resolve
    {s : Σ k, BTMor1 k}
    {a : ℕ} {t : BTMor1 a}
    (hsig : s = ⟨a, t⟩)
    (hfst : s.1 = a) :
    s.snd.foldDepth = t.foldDepth := by
  subst hsig; rfl

private theorem BTMor1.foldDepth_ind_eq {n : ℕ}
    (t : BTMor1 n) :
    BTMor1.ind
      (motive := fun {_} _ => ℕ)
      (step := foldDepthStep) t = t.foldDepth := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem BTMor1.foldDepth_fold {n m : ℕ}
    (f : Fin m → BTMor1 n)
    (g : Fin m → BTMor1 (m + m))
    (tree : BTMor1 n) (j : Fin m) :
    (BTMor1.fold m f g tree j).foldDepth =
      1 + max (max
        ((Finset.univ : Finset (Fin m)).sup
          (fun i => (f i).foldDepth))
        ((Finset.univ : Finset (Fin m)).sup
          (fun i => (g i).foldDepth)))
        tree.foldDepth := by
  unfold BTMor1.foldDepth BTMor1.fold
  rw [ind_btMorInject]
  simp only [foldDepthStep, BTMor1.foldDepth_ind_eq]
  congr 2
  · congr 1
    · apply Finset.sup_congr rfl
      intro i _
      rw [polyFixCoprodStr_inj_child]
      have hsig := foldChildSigma_base m f g tree j i
      have hfst :
          ((pbefMor (foldEval m f g tree j)).left
            ⟨i.val,
              Nat.lt_of_lt_of_le i.isLt
                (Nat.le_add_right m (m + 1))⟩).1
            = n := by
        rw [hsig]
      rw [BTMor1.foldDepth_cast]
      exact BTMor1.foldDepth_snd_resolve hsig hfst
    · apply Finset.sup_congr rfl
      intro i _
      rw [polyFixCoprodStr_inj_child]
      have hi : i.val < m := i.isLt
      have hls : m + i.val < m + m + 1 := by omega
      have hsig :=
        foldChildSigma_step m f g tree j i hls
      have hfst :
          ((pbefMor (foldEval m f g tree j)).left
            ⟨m + i.val, hls⟩).1 = m + m := by
        rw [hsig]
      rw [BTMor1.foldDepth_cast]
      exact BTMor1.foldDepth_snd_resolve hsig hfst
  · rw [polyFixCoprodStr_inj_child]
    have hsig := foldChildSigma_tree m f g tree j
    have hlt : m + m < m + m + 1 := Nat.lt_succ_self _
    have hfst :
        ((pbefMor (foldEval m f g tree j)).left
          ⟨m + m, hlt⟩).1 = n := by
      rw [hsig]
    rw [BTMor1.foldDepth_cast]
    exact BTMor1.foldDepth_snd_resolve hsig hfst

/-- Tree morphism with explicit composition: a
5-constructor inductive paralleling `BTMor1` but with
a `comp` constructor whose fold-nesting depth is the
max (not additive) of its arguments.  The depth-bounded
subtype `TreeERMor1` characterizes the elementary
recursive fragment (Leivant 1999). -/
inductive TreeMor1 : ℕ → Type
  | leaf {n : ℕ} : TreeMor1 n
  | branch {n : ℕ}
      (l r : TreeMor1 n) : TreeMor1 n
  | proj {n : ℕ} (i : Fin n) : TreeMor1 n
  | comp {n k : ℕ} (f : TreeMor1 k)
      (g : Fin k → TreeMor1 n) : TreeMor1 n
  | fold {n : ℕ} (m : ℕ)
      (f : Fin m → TreeMor1 n)
      (g : Fin m → TreeMor1 (m + m))
      (tree : TreeMor1 n)
      (j : Fin m) : TreeMor1 n

/-- Maximum nesting depth of `fold` constructors
in a `TreeMor1` term. -/
def TreeMor1.foldDepth :
    {n : ℕ} → TreeMor1 n → ℕ
  | _, .leaf => 0
  | _, .branch l r =>
      max l.foldDepth r.foldDepth
  | _, .proj _ => 0
  | _, .comp f g =>
      max f.foldDepth
        ((Finset.univ : Finset (Fin _)).sup
          (fun i => (g i).foldDepth))
  | _, .fold _ f g tree _ =>
      1 + max (max
        ((Finset.univ : Finset (Fin _)).sup
          (fun i => (f i).foldDepth))
        ((Finset.univ : Finset (Fin _)).sup
          (fun i => (g i).foldDepth)))
        tree.foldDepth

@[simp] theorem TreeMor1.foldDepth_leaf
    {n : ℕ} :
    (@TreeMor1.leaf n).foldDepth = 0 := rfl

@[simp] theorem TreeMor1.foldDepth_branch
    {n : ℕ} (l r : TreeMor1 n) :
    (TreeMor1.branch l r).foldDepth =
      max l.foldDepth r.foldDepth := rfl

@[simp] theorem TreeMor1.foldDepth_proj
    {n : ℕ} (i : Fin n) :
    (TreeMor1.proj i).foldDepth = 0 := rfl

@[simp] theorem TreeMor1.foldDepth_comp
    {n k : ℕ} (f : TreeMor1 k)
    (g : Fin k → TreeMor1 n) :
    (TreeMor1.comp f g).foldDepth =
      max f.foldDepth
        ((Finset.univ : Finset (Fin k)).sup
          (fun i => (g i).foldDepth)) := rfl

@[simp] theorem TreeMor1.foldDepth_fold
    {n : ℕ} (m : ℕ)
    (f : Fin m → TreeMor1 n)
    (g : Fin m → TreeMor1 (m + m))
    (tree : TreeMor1 n) (j : Fin m) :
    (TreeMor1.fold m f g tree j).foldDepth =
      1 + max (max
        ((Finset.univ : Finset (Fin m)).sup
          (fun i => (f i).foldDepth))
        ((Finset.univ : Finset (Fin m)).sup
          (fun i => (g i).foldDepth)))
        tree.foldDepth := rfl

/-- Map a `TreeMor1` to the corresponding `BTMor1`,
translating `comp` to `BTMor1.subst`. -/
def TreeMor1.toBTMor1 :
    {n : ℕ} → TreeMor1 n → BTMor1 n
  | _, .leaf => BTMor1.leaf
  | _, .branch l r =>
      BTMor1.branch l.toBTMor1 r.toBTMor1
  | _, .proj i => BTMor1.proj i
  | _, .comp f g =>
      f.toBTMor1.subst (fun i => (g i).toBTMor1)
  | _, .fold m f g tree j =>
      BTMor1.fold m
        (fun i => (f i).toBTMor1)
        (fun i => (g i).toBTMor1)
        tree.toBTMor1 j

/-- Interpret a `TreeMor1` in `BT` via its
translation to `BTMor1`. -/
def TreeMor1.interp.{u} {n : ℕ}
    (t : TreeMor1 n)
    (ctx : Fin n → BT.{u}) : BT.{u} :=
  t.toBTMor1.interpU ctx

@[simp] theorem TreeMor1.interp_leaf.{u}
    {n : ℕ} (ctx : Fin n → BT.{u}) :
    TreeMor1.leaf.interp ctx = BT.leaf := by
  simp only [TreeMor1.interp,
    TreeMor1.toBTMor1, BTMor1.interpU_leaf]

@[simp] theorem TreeMor1.interp_branch.{u}
    {n : ℕ} (l r : TreeMor1 n)
    (ctx : Fin n → BT.{u}) :
    (TreeMor1.branch l r).interp ctx =
      BT.node (l.interp ctx)
        (r.interp ctx) := by
  simp only [TreeMor1.interp,
    TreeMor1.toBTMor1, BTMor1.interpU_branch]

@[simp] theorem TreeMor1.interp_proj.{u}
    {n : ℕ} (i : Fin n)
    (ctx : Fin n → BT.{u}) :
    (TreeMor1.proj i).interp ctx = ctx i := by
  simp only [TreeMor1.interp,
    TreeMor1.toBTMor1, BTMor1.interpU_proj]

@[simp] theorem TreeMor1.interp_comp.{u}
    {n k : ℕ} (f : TreeMor1 k)
    (g : Fin k → TreeMor1 n)
    (ctx : Fin n → BT.{u}) :
    (TreeMor1.comp f g).interp ctx =
      f.interp
        (fun i => (g i).interp ctx) := by
  simp only [TreeMor1.interp, TreeMor1.toBTMor1,
    BTMor1.interpU_subst]

@[simp] theorem TreeMor1.interp_fold.{u}
    {n : ℕ} (m : ℕ)
    (f : Fin m → TreeMor1 n)
    (g : Fin m → TreeMor1 (m + m))
    (tree : TreeMor1 n) (j : Fin m)
    (ctx : Fin n → BT.{u}) :
    (TreeMor1.fold m f g tree j).interp ctx =
      BT.fold
        (fun i => (f i).interp ctx)
        (fun leftAll rightAll j' =>
          (g j').interp
            (finAppend leftAll rightAll))
        (tree.interp ctx)
        j := by
  simp only [TreeMor1.interp, TreeMor1.toBTMor1,
    BTMor1.interpU_fold]

/-- Depth-0 fragment: no fold constructors. -/
def TreeERMor1_0 (n : ℕ) : Type :=
  { t : TreeMor1 n // t.foldDepth = 0 }

/-- Depth-at-most-1 fragment: at most one fold layer. -/
def TreeERMor1_1 (n : ℕ) : Type :=
  { t : TreeMor1 n // t.foldDepth ≤ 1 }

/-- Depth-at-most-2 fragment: at most two fold layers.
Corresponds to the elementary recursive fragment of
tree morphisms (Leivant 1999). -/
def TreeERMor1 (n : ℕ) : Type :=
  { t : TreeMor1 n // t.foldDepth ≤ 2 }

def TreeERMor1_0.toDepth1 {n : ℕ}
    (t : TreeERMor1_0 n) : TreeERMor1_1 n :=
  ⟨t.val, by have := t.property; omega⟩

def TreeERMor1_1.toDepth2 {n : ℕ}
    (t : TreeERMor1_1 n) : TreeERMor1 n :=
  ⟨t.val, by have := t.property; omega⟩

def TreeERMor1_0.toDepth2 {n : ℕ}
    (t : TreeERMor1_0 n) : TreeERMor1 n :=
  t.toDepth1.toDepth2

def TreeERMor1_0.leaf {n : ℕ} : TreeERMor1_0 n :=
  ⟨.leaf, rfl⟩

def TreeERMor1_0.proj {n : ℕ} (i : Fin n) :
    TreeERMor1_0 n :=
  ⟨.proj i, rfl⟩

def TreeERMor1_0.branch {n : ℕ}
    (l r : TreeERMor1_0 n) : TreeERMor1_0 n :=
  ⟨.branch l.val r.val, by
    simp only [TreeMor1.foldDepth_branch,
      Nat.max_eq_zero_iff]
    exact ⟨l.property, r.property⟩⟩

def TreeERMor1_0.comp {n k : ℕ}
    (f : TreeERMor1_0 k)
    (g : Fin k → TreeERMor1_0 n) :
    TreeERMor1_0 n :=
  ⟨.comp f.val (fun i => (g i).val), by
    simp only [TreeMor1.foldDepth_comp,
      Nat.max_eq_zero_iff]
    exact ⟨f.property, le_antisymm
      (Finset.sup_le
        (fun i _ => le_of_eq (g i).property))
      (Nat.zero_le _)⟩⟩

def TreeERMor1_1.leaf {n : ℕ} : TreeERMor1_1 n :=
  TreeERMor1_0.leaf.toDepth1

def TreeERMor1_1.proj {n : ℕ} (i : Fin n) :
    TreeERMor1_1 n :=
  (TreeERMor1_0.proj i).toDepth1

def TreeERMor1_1.branch {n : ℕ}
    (l r : TreeERMor1_1 n) : TreeERMor1_1 n :=
  ⟨.branch l.val r.val, by
    simp only [TreeMor1.foldDepth_branch]
    exact Nat.max_le.mpr ⟨l.property, r.property⟩⟩

def TreeERMor1_1.comp {n k : ℕ}
    (f : TreeERMor1_1 k)
    (g : Fin k → TreeERMor1_1 n) :
    TreeERMor1_1 n :=
  ⟨.comp f.val (fun i => (g i).val), by
    simp only [TreeMor1.foldDepth_comp]
    exact Nat.max_le.mpr ⟨f.property,
      Finset.sup_le
        (fun i _ => (g i).property)⟩⟩

def TreeERMor1_1.fold {n m : ℕ}
    (f : Fin m → TreeERMor1_0 n)
    (g : Fin m → TreeERMor1_0 (m + m))
    (tree : TreeERMor1_0 n) (j : Fin m) :
    TreeERMor1_1 n :=
  ⟨.fold m (fun i => (f i).val)
    (fun i => (g i).val) tree.val j, by
    simp only [TreeMor1.foldDepth_fold]
    have hf : (Finset.univ.sup
        (fun i => (f i).val.foldDepth)) = 0 :=
      le_antisymm (Finset.sup_le
        (fun i _ => le_of_eq (f i).property))
        (Nat.zero_le _)
    have hg : (Finset.univ.sup
        (fun i => (g i).val.foldDepth)) = 0 :=
      le_antisymm (Finset.sup_le
        (fun i _ => le_of_eq (g i).property))
        (Nat.zero_le _)
    rw [hf, hg, tree.property]; decide⟩

def TreeERMor1.leaf {n : ℕ} : TreeERMor1 n :=
  TreeERMor1_0.leaf.toDepth2

def TreeERMor1.proj {n : ℕ} (i : Fin n) :
    TreeERMor1 n :=
  (TreeERMor1_0.proj i).toDepth2

def TreeERMor1.branch {n : ℕ}
    (l r : TreeERMor1 n) : TreeERMor1 n :=
  ⟨.branch l.val r.val, by
    simp only [TreeMor1.foldDepth_branch]
    exact Nat.max_le.mpr
      ⟨l.property, r.property⟩⟩

def TreeERMor1.comp {n k : ℕ}
    (f : TreeERMor1 k)
    (g : Fin k → TreeERMor1 n) :
    TreeERMor1 n :=
  ⟨.comp f.val (fun i => (g i).val), by
    simp only [TreeMor1.foldDepth_comp]
    exact Nat.max_le.mpr ⟨f.property,
      Finset.sup_le
        (fun i _ => (g i).property)⟩⟩

def TreeERMor1.fold {n m : ℕ}
    (f : Fin m → TreeERMor1_1 n)
    (g : Fin m → TreeERMor1_1 (m + m))
    (tree : TreeERMor1_1 n) (j : Fin m) :
    TreeERMor1 n :=
  ⟨.fold m (fun i => (f i).val)
    (fun i => (g i).val) tree.val j, by
    simp only [TreeMor1.foldDepth_fold]
    have hf : (Finset.univ.sup
        (fun i => (f i).val.foldDepth)) ≤ 1 :=
      Finset.sup_le
        (fun i _ => (f i).property)
    have hg : (Finset.univ.sup
        (fun i => (g i).val.foldDepth)) ≤ 1 :=
      Finset.sup_le
        (fun i _ => (g i).property)
    have ht := tree.property
    omega⟩

def TreeERMorN_1 (n m : ℕ) : Type :=
  Fin m → TreeERMor1_1 n

def TreeERMorN (n m : ℕ) : Type :=
  Fin m → TreeERMor1 n

def TreeERMor1_1.fold1 {n : ℕ}
    (base : TreeERMor1_0 n)
    (step : TreeERMor1_0 (1 + 1))
    (tree : TreeERMor1_0 n) : TreeERMor1_1 n :=
  TreeERMor1_1.fold
    (fun _ => base) (fun _ => step) tree 0

def TreeERMor1.fold1 {n : ℕ}
    (base : TreeERMor1_1 n)
    (step : TreeERMor1_1 (1 + 1))
    (tree : TreeERMor1_1 n) : TreeERMor1 n :=
  TreeERMor1.fold
    (fun _ => base) (fun _ => step) tree 0

def TreeERMor1_1.mutuFold {n m : ℕ}
    (f : Fin m → TreeERMor1_0 n)
    (g : Fin m → TreeERMor1_0 (m + m))
    (tree : TreeERMor1_0 n) :
    TreeERMorN_1 n m :=
  fun j => TreeERMor1_1.fold f g tree j

def TreeERMor1.mutuFold {n m : ℕ}
    (f : Fin m → TreeERMor1_1 n)
    (g : Fin m → TreeERMor1_1 (m + m))
    (tree : TreeERMor1_1 n) : TreeERMorN n m :=
  fun j => TreeERMor1.fold f g tree j

def TreeERMor1_0.interp.{u} {n : ℕ}
    (t : TreeERMor1_0 n)
    (ctx : Fin n → BT.{u}) : BT.{u} :=
  t.val.interp ctx

def TreeERMor1_1.interp.{u} {n : ℕ}
    (t : TreeERMor1_1 n)
    (ctx : Fin n → BT.{u}) : BT.{u} :=
  t.val.interp ctx

def TreeERMor1.interp.{u} {n : ℕ}
    (t : TreeERMor1 n)
    (ctx : Fin n → BT.{u}) : BT.{u} :=
  t.val.interp ctx

def TreeERMorN.interp.{u} {n m : ℕ}
    (f : TreeERMorN n m)
    (ctx : Fin n → BT.{u}) : Fin m → BT.{u} :=
  fun i => (f i).interp ctx

def TreeERMorN.id (n : ℕ) : TreeERMorN n n :=
  fun i => TreeERMor1.proj i

def TreeERMorN.comp {n m k : ℕ}
    (f : TreeERMorN n m) (g : TreeERMorN m k) :
    TreeERMorN n k :=
  fun i => TreeERMor1.comp (g i) f

@[simp] theorem TreeERMorN.interp_id
    {n : ℕ} (ctx : Fin n → BT.{0}) :
    (TreeERMorN.id n).interp ctx = ctx := by
  funext i
  simp only [TreeERMorN.interp, TreeERMorN.id,
    TreeERMor1.interp, TreeERMor1.proj,
    TreeERMor1_0.proj, TreeERMor1_0.toDepth2,
    TreeERMor1_0.toDepth1, TreeERMor1_1.toDepth2,
    TreeMor1.interp_proj]

@[simp] theorem TreeERMorN.interp_comp
    {n m k : ℕ} (f : TreeERMorN n m)
    (g : TreeERMorN m k)
    (ctx : Fin n → BT.{0}) :
    (f.comp g).interp ctx =
      g.interp (f.interp ctx) := by
  funext i
  simp only [TreeERMorN.interp, TreeERMorN.comp,
    TreeERMor1.interp, TreeERMor1.comp,
    TreeMor1.interp_comp]
  rfl

end GebLean

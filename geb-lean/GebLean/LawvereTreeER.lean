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

end GebLean

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

/-- Maximum nesting depth of `fold` constructors in a `BTMor1` term.
Used to carve out depth-bounded subtypes for the tree-native
elementary-recursive Lawvere theory. -/
def BTMor1.foldDepth : ∀ {n : ℕ}, BTMor1 n → ℕ := fun {_} t =>
  BTMor1.ind
    (motive := fun {_} _ => ℕ)
    (step := fun i => match i with
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
            (ih ⟨pm + pm, hlt⟩))
    t

@[simp] theorem BTMor1.foldDepth_proj {n : ℕ} (i : Fin n) :
    (BTMor1.proj i).foldDepth = 0 := rfl

@[simp] theorem BTMor1.foldDepth_leaf {n : ℕ} :
    (@BTMor1.leaf n).foldDepth = 0 := rfl

@[simp] theorem BTMor1.foldDepth_branch {n : ℕ}
    (l r : BTMor1 n) :
    (BTMor1.branch l r).foldDepth =
      max l.foldDepth r.foldDepth := rfl

end GebLean

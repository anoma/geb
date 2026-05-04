import GebLean.LawvereKSimMajorization

namespace GebLean

/-- Level-1 simrec witness used in tests.
addK = simrec_0 base=proj 0 step=succ(prev). -/
private def addK : KMor1 2 :=
  KMor1.simrec (a := 1) (k := 0) ⟨0, by decide⟩
    (fun _ => KMor1.proj 0)
    (fun _ => KMor1.comp KMor1.succ
                fun _ : Fin 1 =>
                  KMor1.proj ⟨2, by decide⟩)

example : addK.level ≤ 1 := by decide
example : addK.level = 1 := by decide

-- Atomic majorize_one witnesses: offset = 0.
#guard (KMor1.majorize_one (KMor1.zero (n := 1))
          (by decide)).2 = 0
#guard (KMor1.majorize_one (KMor1.proj (0 : Fin 2))
          (by decide)).2 = 0
#guard (KMor1.majorize_one KMor1.succ (by decide)).2 = 0

-- addK exercises level-1 simrec: r positive.
#guard (KMor1.majorize_one addK (by decide)).1 ≥ 1
#guard (KMor1.majorize_one addK (by decide)).2 = 0

-- Atomic majorize witnesses: r = 2 uniform.
#guard (KMor1.majorize (KMor1.zero (n := 1))
          (by decide)).1 = 2
#guard (KMor1.majorize KMor1.succ (by decide)).1 = 2
#guard (KMor1.majorize (KMor1.proj (0 : Fin 2))
          (by decide)).1 = 2

-- addK exercises level-1 path through KMor1.majorize's
-- raise / structural branches; r still 2.
#guard (KMor1.majorize addK (by decide)).1 = 2

-- Concrete-input dominance via the proven theorem.
-- These bypass kernel reduction of A_two_iter's expER
-- tree (intractable per CLAUDE.md memory) by invoking
-- the universal theorem at concrete inputs.

example : addK.interp ![1, 1] ≤
    (ERMor1.A_two_iter
      (KMor1.majorize addK (by decide)).1).interp
        ![(Finset.univ : Finset (Fin 2)).sup
            (![1, 1] : Fin 2 → ℕ)
          + (KMor1.majorize addK (by decide)).2] :=
  KMor1.majorize_by_A_two_iter addK (by decide) ![1, 1]

example : KMor1.succ.interp ![3] ≤
    (ERMor1.A_two_iter
      (KMor1.majorize KMor1.succ (by decide)).1).interp
        ![(Finset.univ : Finset (Fin 1)).sup
            (![3] : Fin 1 → ℕ)
          + (KMor1.majorize KMor1.succ (by decide)).2] :=
  KMor1.majorize_by_A_two_iter KMor1.succ (by decide) ![3]

end GebLean

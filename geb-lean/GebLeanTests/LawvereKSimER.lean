import GebLean

namespace GebLeanTests.LawvereKSimER

open GebLean

-- Tier 1 — atomic kToER definitional rfl checks.

example : kToER (a := 3) KMor1.zero
              (by simp [KMor1.level])
            = ERMor1.zeroN 3 := rfl

example : kToER KMor1.succ (by simp [KMor1.level])
            = ERMor1.succ := rfl

example : kToER (a := 3)
              (KMor1.proj (Fin.mk 1 (by omega)))
              (by simp [KMor1.level])
            = ERMor1.proj (Fin.mk 1 (by omega)) := rfl

example {f : KMor1 2}
        (h : (KMor1.raise f).level ≤ 2)
        (h' : f.level ≤ 2) :
    kToER (KMor1.raise f) h = kToER f h' := rfl

-- Tier 2 — universal-theorem example proofs.
--
-- Inline addK : KMor1 2 simrec witness (level 1).
-- λ(x, y). x + y, defined via simrec over successor.
-- The Phase-1 addK at GebLeanTests/LawvereKSimInterp.lean
-- is private; reconstruct here for step 5's tests.
private def addK : KMor1 2 :=
  KMor1.simrec (k := 0)
    ⟨0, by omega⟩
    (fun _ => KMor1.proj 0)
    (fun _ =>
      KMor1.comp KMor1.succ
        ![KMor1.proj 2])

example : (kToER addK
              (by unfold addK; decide)).interp ![3, 5]
            = addK.interp ![3, 5] :=
  kToER_interp addK (by unfold addK; decide) ![3, 5]

example : (kToER addK
              (by unfold addK; decide)).interp ![0, 7]
            = addK.interp ![0, 7] :=
  kToER_interp addK (by unfold addK; decide) ![0, 7]

-- Tier 3 — kToERFunctor sanity.

example : kToERFunctor.obj 5 = 5 := rfl

example {n : ℕ} :
    kToERFunctor.map (CategoryTheory.CategoryStruct.id
        (obj := LawvereKSimDCat 2) n)
      = CategoryTheory.CategoryStruct.id
          (obj := LawvereERCat) (kToERFunctor.obj n) :=
  kToERFunctor.map_id n

end GebLeanTests.LawvereKSimER

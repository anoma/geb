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

end GebLeanTests.LawvereKSimER

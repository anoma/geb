import GebLean.LawvereGodelTTerm

namespace GebLean

private def Snat : Set GodelTBase := {GodelTBase.nat}

theorem hNS : GodelTBase.nat ∈ Snat := by
  simp [Snat]

private def numeral (n : Nat) :
    GodelTTerm Snat 0 (.base .nat hNS) :=
  match n with
  | 0 => .zero hNS
  | k + 1 => .app (.succ hNS) (numeral k)

#guard (numeral 5).interp Fin.elim0 = 5

#guard (GodelTTerm.app (.app (.K (.base .nat hNS)
            (.base .nat hNS)) (numeral 7))
          (numeral 3)).interp Fin.elim0 = 7

end GebLean

import GebLean.LawvereGodelTReduces
import GebLean.Utilities.Tower

/-!
# Lemma 16: structural tower bound for `GodelTTerm`

Following Beckmann-Weiermann 2000 Definitions 7-10 and the
proof of Lemma 16 on pp. 480-484.  All measures are defined
parametrically over `S : Set GodelTBase` and apply uniformly
to the nucleus (`S = {.nat}`) and the binary-tree extension
(`S = {.nat, .tree}`).

`tower` from `Utilities/Tower.lean` matches Beckmann-Weiermann's
`2_m`: `tower 0 x = x`, `tower (k+1) x = 2 ^ tower k x`.
-/

namespace GebLean

end GebLean

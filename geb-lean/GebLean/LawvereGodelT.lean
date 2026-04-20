import Mathlib.Data.Fin.Basic

/-!
# `LawvereGodelT`: Restricted Gödel-T Fragment T*

A typed combinatory logic encoding Beckmann-Weiermann's T*
fragment of Gödel's T (B-W 2000, "Characterizing the
elementary recursive functions by a fragment of Gödel's T").
T*'s discipline restricts the iterator `𝒥_ρ` to type-0
applications, which fixes its expressivity to exactly the
elementary recursive functions.

Each GodelT term has a named ER backing in
`GebLean/Utilities/`; the categorical equivalence with
`LawvereERCat` is preserved by construction (see
`GebLean/LawvereGodelTERCatEquiv.lean`).
-/

namespace GebLean

end GebLean

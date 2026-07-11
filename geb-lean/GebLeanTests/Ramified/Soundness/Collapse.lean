import GebLean.Ramified.Soundness.Collapse

/-!
# Tests for the collapse packaging

Acceptance example for the collapse denotation (task 6.5a): the collapse
denotation of an identity morphism of `SynCatFO` is the identity function,
through `collapseDenotation_id`.
-/

namespace GebLean.Ramified

open CategoryTheory
open GebLean.Ramified.Definability

/-- The collapse denotation of the identity morphism is the identity function. -/
example (Γ : SynCatFO) : collapseDenotation (𝟙 Γ) = id :=
  collapseDenotation_id Γ

end GebLean.Ramified

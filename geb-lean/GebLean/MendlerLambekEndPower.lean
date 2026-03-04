import GebLean.RestrictedCoendAsColimit
import GebLean.Utilities.EndsAndCoends

/-!
# Mendler-Lambek Equivalence via Ends and Powers

This module re-expresses the `GExtFunctor` (Vene's `G^e`) using
ends and powers instead of restricted coends.

Starting from
`G^e(pt) = restricted coend of G by HomToProf(pt)`,
the derivation proceeds in three steps:

1. Transfer the restricted coend to a copower-profunctor coend
   (done in `RestrictedCoendAsColimit.lean`).
2. Apply coend-end duality:
   `Hom(coend, Y) ≃ typeEnd (P ⇓ Y)`.
3. Replace copowers with powers inside the end via
   `copowerPowerEquiv`.

The final characterization is:
`Hom(G^e(pt), Y) ≃ ∫_A Hom(G(A,A), Y^(A→pt))`.
-/

namespace GebLean

open CategoryTheory
open CategoryTheory.Limits

universe v w

/-!
## Coend-End Duality for Initial Cowedges

Given a coend cowedge `c` (initial in `Cowedge P`) for a
`D`-valued profunctor, the hom-set `c.pt ⟶ Y` is
isomorphic to the explicit end `typeEnd (P ⇓ Y)`.
-/

section CoendEndDuality

variable
  {C : Type v} [Category.{v} C]
  {D : Type w} [Category.{v} D]

/-- Coend-end duality for initial cowedges:
given a coend cowedge `c` (initial in `Cowedge P`),
`(c.pt ⟶ Y) ≃ typeEnd (P ⇓ Y)`.

Combines `ordinaryHomIsoEndApex` (relating the
coend apex hom to any terminal wedge apex) with
`typeEndWedge_isTerminal` (making `typeEnd` the apex
of a terminal wedge). -/
def cowedgeHomEndEquiv
    (P : Cᵒᵖ ⥤ C ⥤ D)
    {c : Cowedge (J := C) (C := D) P}
    (hc : IsInitial c) (Y : D) :
    (c.pt ⟶ Y) ≃ typeEnd (P ⇓ Y) :=
  let iso := ordinaryHomIsoEndApex P hc Y
    (typeEndWedge_isTerminal (P ⇓ Y))
  ⟨iso.hom, iso.inv,
   fun x => congr_fun iso.hom_inv_id x,
   fun x => congr_fun iso.inv_hom_id x⟩

end CoendEndDuality

end GebLean

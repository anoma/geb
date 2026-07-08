import Geb.Mathlib.Data.PFunctor.Slice.Basic

/-! Smoke test: the vendored geb-mathlib `Slice` core is importable and
its declarations are usable under `v4.29.0-rc6`. Replace with a genuine
ported import once `geb-lean` consumes curated content directly. -/

example (dom : Type) (F : SliceDomPFunctor dom) {X : Type} (p : X → dom)
    (a : F.A) (v : F.B a → X) :
    F.Compatible p a v ↔ ∀ b, p (v b) = F.r ⟨a, b⟩ :=
  F.compatible_iff p a v

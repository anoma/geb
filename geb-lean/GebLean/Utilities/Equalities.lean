import Mathlib.Data.Sigma.Basic

namespace GebLean

/--
Helper lemma: Sigma types with equal first components and heterogeneously equal
second components are equal.
-/
lemma sigma_ext_rfl_heq {α : Type*} {β : α → Type*} {a : α} {b₁ b₂ : β a}
    (h : b₁ = b₂) : (⟨a, b₁⟩ : Sigma β) = ⟨a, b₂⟩ :=
  Sigma.ext rfl (heq_of_eq h)

/--
Helper lemma: Subtypes with the same value but different proofs are
heterogeneously equal.
-/
lemma subtype_mk_heq {α : Type*} {p : α → Prop} {a : α} (h₁ h₂ : p a) :
    (Subtype.mk a h₁ : Subtype p) ≍ Subtype.mk a h₂ :=
  heq_of_eq (Subtype.ext rfl)

/--
Transport by a reflexivity proof is the identity.
For any proof `h : a = a`, transporting along `h` does nothing.
-/
lemma transport_by_refl {α : Type*} {a : α} (h : a = a) {β : α → Type*}
    (x : β a) : h ▸ x = x := by
  cases h
  rfl

/--
Transport along an equality reduces to heterogeneous equality.
If `h : a = b` and `x : β a`, `y : β b` are heterogeneously equal,
then transporting `x` along `h` gives `y`.
-/
lemma transport_heq {α : Type*} {a b : α} (h : a = b) {β : α → Type*}
    {x : β a} {y : β b} (heq : x ≍ y) : h ▸ x = y := by
  cases h
  exact eq_of_heq heq

/--
Coercion of transported subtype equals target if coercions are heterogeneously
equal. When we transport a subtype value and then take its coercion, if the
original coercion is heterogeneously equal to the target, then the coercion of
the transported value equals the target.
-/
lemma subtype_transport_val_heq {α : Type*} {a b : α} (h : a = b)
    {β : α → Type*} {P : ∀ x, β x → Prop} {x : Subtype (P a)} {z : β b}
    (heq : x.val ≍ z) : (h ▸ x : Subtype (P b)).val = z := by
  cases h
  exact eq_of_heq heq

/--
Coercion of transported pair equals the first component.
For a subtype constructed from a pair `⟨v, proof⟩`, transporting it
and taking the coercion just gives back the value `v` (up to heterogeneous
equality). This handles the general case where both the type and predicate may
vary. The motive must have the form `fun x h => {y : β x // P x y}` where `P`
may depend on the index `x` but not on the equality proof `h`.
-/
lemma coe_transport_pair {α : Type*} {a b : α} (h : a = b)
    {β : α → Type*} {P : (x : α) → β x → Prop}
    {v : β a} {prf : _} {z : β b}
    (heq : v ≍ z) :
    (@Eq.rec α a (fun x (_ : a = x) => {y : β x // P x y})
      ⟨v, prf⟩ b h).val = z := by
  cases h
  simp only [eq_of_heq heq]

/--
When transporting a value along a sigma equality where the first component
is definitionally equal, the transport is the identity.
-/
lemma sigma_transport_fst_rfl {α : Type*} {β : α → Type*}
    {a b : Σ x, β x} (h : a = b) (hab : a.fst = b.fst)
    (v : β a.fst) :
    (h ▸ v : β b.fst) = (hab ▸ v : β b.fst) := by
  cases h
  rfl

/--
When transporting a subtype along a sigma equality where the first components
are definitionally equal, the coercion is preserved.
-/
lemma coe_subtype_sigma_transport_fst_rfl {α : Type*} {β : α → Type*}
    {a b : Σ x, β x}
    (P : (s : Σ x, β x) → β s.fst → Prop)
    (h : a = b) (hab : a.fst = b.fst)
    {v : β a.fst} (pf : P a v) :
    (h ▸ (⟨v, pf⟩ : {y : β a.fst // P a y})).val =
      (hab ▸ v : β b.fst) := by
  rw [← sigma_transport_fst_rfl h hab v]
  cases h
  rfl

/--
Special case when the first component equality is definitionally `rfl`.
-/
lemma coe_subtype_sigma_transport_fst_refl {α : Type*} {β : α → Type*}
    {x : α} {a b : β x}
    (P : (s : Σ y, β y) → β s.fst → Prop)
    (h : (⟨x, a⟩ : Σ y, β y) = ⟨x, b⟩)
    (v : β x) (pf : P ⟨x, a⟩ v) :
    (@Eq.rec (Σ y, β y) ⟨x, a⟩ (fun s _ => {y : β s.fst // P s y})
      ⟨v, pf⟩ ⟨x, b⟩ h).val = v := by
  obtain ⟨h₁, h₂⟩ := Sigma.mk.inj_iff.mp h
  cases h₁
  cases (eq_of_heq h₂)
  rfl

/--
When we take a subtype `w`, extract its coercion, build a new subtype from that
coercion, transport it along a sigma equality where the first component is
`rfl`, and take the coercion again, we get back the original coercion.
-/
lemma coe_subtype_sigma_transport_coe {α : Type*} {β : α → Type*}
    {x : α} {a b : β x}
    (P : (s : Σ y, β y) → β s.fst → Prop)
    {Q : β x → Prop}
    (h : (⟨x, a⟩ : Σ y, β y) = ⟨x, b⟩)
    (w : Subtype Q) (pf : P ⟨x, a⟩ w.val) :
    (@Eq.rec (Σ y, β y) ⟨x, a⟩ (fun s _ => {y : β s.fst // P s y})
      ⟨w.val, pf⟩ ⟨x, b⟩ h).val = w.val := by
  exact coe_subtype_sigma_transport_fst_refl P h w.val pf

end GebLean

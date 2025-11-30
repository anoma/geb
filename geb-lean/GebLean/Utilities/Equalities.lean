import Mathlib.Data.Sigma.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic

namespace GebLean

open CategoryTheory

def typeEq_eq.{u} {α β : Sort u} (h : α = β) (a : α) (b : β) : Prop :=
  match h with | rfl => a = b

def typeEq_of_heq.{u} {α β : Sort u} (h : α = β) {a : α} {b : β} (heq : a ≍ b) :
  typeEq_eq h a b :=
    by cases h ; exact eq_of_heq heq

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

/--
Sigma equality when first components are equal and second components are related
via the equality.
-/
lemma sigma_ext_fst {α : Type*} {β : α → Type*} {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂}
    (ha : a₁ = a₂) (hb : ha ▸ b₁ = b₂) : (⟨a₁, b₁⟩ : Sigma β) = ⟨a₂, b₂⟩ := by
  cases ha
  simp at hb
  rw [hb]

/--
Sigma transport `.snd` extraction: transporting a sigma along an equality in
an outer parameter and then extracting `.snd` gives a heterogeneously equal
value.
-/
lemma sigma_transport_snd_heq {α : Type*} {I : Type*} {β : α → I → Type*}
    {a₁ a₂ : α} (h : a₁ = a₂) {i : I} {b : β a₁ i} :
    (h ▸ (⟨i, b⟩ : (i : I) × β a₁ i) : (i : I) × β a₂ i).snd ≍ b := by
  cases h
  rfl

/--
Sigma transport when the first component is independent of the transported
parameter: the first component is preserved.
-/
lemma sigma_transport_fst_indep {α : Type*} {I : Type*} {β : α → I → Type*}
    {a₁ a₂ : α} (h : a₁ = a₂) {i : I} {b : β a₁ i} :
    (h ▸ (⟨i, b⟩ : (i : I) × β a₁ i) : (i : I) × β a₂ i).fst = i := by
  cases h
  rfl

/--
HEq of sigmas when indexed types depend on an outer parameter that changes.
Given `h : a₁ = a₂`, sigmas `⟨i₁, b₁⟩ : (i : I) × β a₁ i` and
`⟨i₂, b₂⟩ : (i : I) × β a₂ i` are heterogeneously equal if their first
components are equal (`i₁ = i₂`) and second components are HEq.
-/
lemma sigma_heq_of_fst_eq_snd_heq {α : Type*} {I : Type*} {β : α → I → Type*}
    {a₁ a₂ : α} (h : a₁ = a₂)
    {i₁ i₂ : I} (hi : i₁ = i₂)
    {b₁ : β a₁ i₁} {b₂ : β a₂ i₂} (hb : b₁ ≍ b₂) :
    (⟨i₁, b₁⟩ : (i : I) × β a₁ i) ≍ (⟨i₂, b₂⟩ : (i : I) × β a₂ i) := by
  cases h
  cases hi
  cases hb
  rfl

lemma over_cast_left {X : Type*} {S1 S2 T : Over X}
    (hsrc : S1 = S2) (f : S1 ⟶ T) (p : S2.left) :
    (cast (congrArg (fun s => s ⟶ T) hsrc) f).left p =
      f.left (cast (congrArg (fun s : Over X => s.left) hsrc.symm) p) := by
  cases hsrc
  rfl

/--
If two sigma values (over possibly different families on the same base type)
are heterogeneously equal, and the families are propositionally equal,
the first components are equal.
-/
lemma sigma_fst_heq_eq.{u, w} {α : Type u} {β₁ β₂ : α → Type w}
    {s₁ : Sigma β₁} {s₂ : Sigma β₂}
    (hβ : β₁ = β₂)
    (h : s₁ ≍ s₂) : s₁.fst = s₂.fst := by
  cases hβ
  exact congrArg Sigma.fst (eq_of_heq h)

/--
If two sigma values over the same family are equal, their first components
are equal.
-/
lemma sigma_fst_of_eq {α : Type*} {β : α → Type*}
    {s₁ s₂ : Sigma β}
    (h : s₁ = s₂) : s₁.fst = s₂.fst := by
  cases h
  rfl

/--
If two sigma values over the same family are equal, their second components
are heterogeneously equal.
-/
lemma sigma_snd_heq_of_eq {α : Type*} {β : α → Type*}
    {s₁ s₂ : Sigma β}
    (h : s₁ = s₂) : s₁.snd ≍ s₂.snd := by
  cases h
  rfl

/--
Two sigma values are heterogeneously equal if their first components are equal
and their second components are heterogeneously equal.
-/
lemma sigma_mk_heq {A : Type*} {f : A → Type*}
    {a1 a2 : A} (ha : a1 = a2)
    {b1 : f a1} {b2 : f a2} (hb : b1 ≍ b2) :
    (⟨a1, b1⟩ : Sigma f) ≍ (⟨a2, b2⟩ : Sigma f) := by
  cases ha
  cases hb
  rfl

/--
Two subtype values with the same underlying value are heterogeneously equal
when the predicates are propositionally equal.
-/
lemma subtype_heq_of_val_eq {A : Type*} {P1 P2 : A → Prop}
    {x1 : Subtype P1} {x2 : Subtype P2}
    (hP : P1 = P2) (hval : x1.val = x2.val) : x1 ≍ x2 := by
  cases hP
  exact heq_of_eq (Subtype.ext hval)

/--
For subtypes indexed by a family, if the indices are equal and the underlying
values are equal, the subtypes are heterogeneously equal.
-/
lemma subtype_heq_of_index_eq {A : Type*} {I : Type*} {P : I → A → Prop}
    {i1 i2 : I} (hi : i1 = i2)
    {x1 : {a // P i1 a}} {x2 : {a // P i2 a}}
    (hval : x1.val = x2.val) : x1 ≍ x2 := by
  cases hi
  exact heq_of_eq (Subtype.ext hval)

/--
Two sigma values indexed by a parameter are HEq if the parameter indices are
equal, the first components are HEq, and the second components are HEq.
This handles the case where the sigma type itself depends on an outer parameter.
-/
lemma sigma_heq_of_param_eq {I : Type*} {A : I → Type*} {B : (i : I) → A i → Type*}
    {i1 i2 : I} (hi : i1 = i2)
    {a1 : A i1} {a2 : A i2} (ha : a1 ≍ a2)
    {b1 : B i1 a1} {b2 : B i2 a2} (hb : b1 ≍ b2) :
    (⟨a1, b1⟩ : Sigma (B i1)) ≍ (⟨a2, b2⟩ : Sigma (B i2)) := by
  cases hi
  cases ha
  cases hb
  rfl

end GebLean

/--
Tactic to split an equality goal `A = C` into two subgoals `A = B` and `B = C`
where `B` is explicitly provided. Uses `Eq.trans` to combine the results.
-/
macro "intermediate_eq" b:term : tactic =>
  `(tactic| refine Eq.trans (b := $b) ?_ ?_)

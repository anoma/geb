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
Matching on a transported sigma and applying a function: the result is the
function applied at the original first component and the transported second.
This handles the pattern `match h ▸ ⟨i, b⟩ with | ⟨j, c⟩ => f j c`.
-/
lemma sigma_transport_match_eq {α : Type*} {I : Type*} {β : α → I → Type*}
    {T : Type*} {a₁ a₂ : α} (h : a₁ = a₂) {i : I} {b : β a₁ i}
    (f : (j : I) → β a₂ j → T) :
    (match (h ▸ ⟨i, b⟩ : (j : I) × β a₂ j) with | ⟨j, c⟩ => f j c) =
    f i (((congrArg (fun a => β a i) h) ▸ b : β a₂ i)) := by
  cases h
  rfl

universe u_fg in
/--
When transporting a sigma `⟨i, b⟩ : (j : I) × F j` along an equality `h : F = G`
between the fiber types, the first component (index) is preserved.
-/
lemma sigma_transport_fun_fst_eq {I : Type*} {F G : I → Type u_fg} (h : F = G)
    (i : I) (b : F i) :
    (h ▸ ⟨i, b⟩ : (j : I) × G j).fst = i := by
  cases h
  rfl

universe u_fg2 in
/--
When transporting a sigma `⟨i, b⟩ : (j : I) × F j` along an equality `h : F = G`,
the second component is heq to the transported `b`.
-/
lemma sigma_transport_fun_snd_heq {I : Type*} {F G : I → Type u_fg2} (h : F = G)
    (i : I) (b : F i) :
    HEq (h ▸ ⟨i, b⟩ : (j : I) × G j).snd ((congrFun h i) ▸ b : G i) := by
  cases h
  rfl

universe u_fg3 in
/--
When transporting a sigma along an equality between function types,
the match can be simplified to use the original index and transported fiber.
This is a more directly applicable form of sigma_transport_match_eq.
-/
lemma sigma_transport_match_simple {I : Type*} {F G : I → Type u_fg3}
    {T : Type*} (h : F = G) (i : I) (b : F i)
    (g : (j : I) → G j → T) :
    (match (h ▸ ⟨i, b⟩ : (j : I) × G j) with | ⟨j, c⟩ => g j c) =
    g i ((congrFun h i) ▸ b) := by
  cases h
  rfl

universe u_fg35 in
/--
Two transports along different proofs of the same type equality are equal.
This follows from proof irrelevance: all proofs of `A = B` are equal.
-/
@[simp]
lemma transport_proof_irrel {A : Sort u_fg35} {B : Sort u_fg35}
    (h1 h2 : A = B) (x : A) : h1 ▸ x = h2 ▸ x := by
  have : h1 = h2 := Subsingleton.elim h1 h2
  subst this
  rfl

universe u_fg36 in
/--
Matching on a transported sigma equals applying the function at the original
index with any transport of the fiber element. This combines
`sigma_transport_match_simple` with proof irrelevance: if the LHS has a
different transport proof than the RHS, they still give the same result.
-/
lemma sigma_transport_match_eq_transport {I : Type*} {F G : I → Type u_fg36}
    {T : Type*} (i : I) (b : F i) (hSigma : F = G) (hElem : F i = G i)
    (g : (j : I) → G j → T) :
    (match (hSigma ▸ ⟨i, b⟩ : (j : I) × G j) with | ⟨j, c⟩ => g j c) =
    g i (hElem ▸ b) := by
  cases hSigma
  cases hElem
  rfl

universe u_fg4 in
/--
HEq variant: matching on a transported sigma gives HEq to applying the
function at the original index with the transported fiber element.
-/
lemma sigma_transport_match_heq {I : Type*} {F G : I → Type u_fg4}
    (h : F = G) (i : I) (b : F i) (g : (j : I) → G j → Type*) :
    HEq (match (h ▸ ⟨i, b⟩ : (j : I) × G j) with | ⟨j, c⟩ => g j c)
        (g i ((congrFun h i) ▸ b)) := by
  cases h
  rfl

universe u_fg45 in
/--
When applying a function to a transported element equals matching on a
transported sigma, as long as both transports are along proofs of the same
equality type. This combines sigma transport match with proof irrelevance.
-/
@[simp]
lemma sigma_transport_match_eq_direct {I : Type*} {F G : I → Type u_fg45}
    {R : Type*} (g : (i : I) → G i → R)
    (i : I) (b : F i) (hElem : F i = G i) (hFun : F = G) :
    g i (hElem ▸ b) =
    (match (hFun ▸ ⟨i, b⟩ : (j : I) × G j) with | ⟨j, c⟩ => g j c) := by
  have hProofIrrel : hElem = congrFun hFun i := Subsingleton.elim _ _
  rw [hProofIrrel, sigma_transport_match_simple]

/--
When transporting a product `(subtype, other)` along an equality, the first
component's coercion is preserved. This handles the pattern where the subtype
has a predicate depending on the transported parameter.
-/
lemma prod_fst_val_transport {α : Type*} {T : Type*} {P : T → α → Prop}
    {Q : T → Type*} {t1 t2 : T} (h : t1 = t2) (a : α) (ha : P t1 a) (b : Q t1) :
    ↑(h ▸ (⟨a, ha⟩, b) : { v // P t2 v } × Q t2).1 = a := by
  cases h
  rfl

/--
Variant with predicate applied in reverse order: `P : α → T → Prop`.
-/
lemma prod_fst_val_transport' {α : Type*} {T : Type*} {P : α → T → Prop}
    {Q : T → Type*} {t1 t2 : T} (h : t1 = t2) (a : α) (ha : P a t1) (b : Q t1) :
    ↑(h ▸ (⟨a, ha⟩, b) : { v // P v t2 } × Q t2).1 = a := by
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
When transporting a subtype along a predicate equality, the coercion is
preserved: `↑(hP ▸ ⟨v, pf⟩) = v`.
-/
@[simp]
lemma subtype_transport_pred_coe {A : Type*} {P Q : A → Prop}
    (hPQ : P = Q) (v : A) (pf : P v) :
    (hPQ ▸ (⟨v, pf⟩ : Subtype P) : Subtype Q).val = v := by
  cases hPQ
  rfl

/--
When transporting any subtype along a predicate equality, the underlying value
is preserved: `(hP ▸ x).val = x.val`.
-/
@[simp]
lemma subtype_transport_pred_val {A : Type*} {P Q : A → Prop}
    (hPQ : P = Q) (x : Subtype P) :
    (hPQ ▸ x : Subtype Q).val = x.val := by
  cases hPQ
  rfl

/--
HEq version: transporting any subtype along a predicate equality gives a
value whose `.val` is heterogeneously equal to the original.
-/
lemma subtype_transport_pred_val_heq {A : Type*} {P Q : A → Prop}
    (hPQ : P = Q) (x : Subtype P) :
    (hPQ ▸ x : Subtype Q).val ≍ x.val := by
  cases hPQ
  rfl

/--
Cast version: casting a subtype along a type equality derived from predicate
equality preserves the underlying value. This is the `cast` form of
`subtype_transport_pred_val`. The proof uses induction on the predicate
equality component.
-/
@[simp]
lemma subtype_cast_val {A : Type*} {P Q : A → Prop}
    (hPQ : P = Q) (x : {a // P a}) :
    (cast (congrArg Subtype hPQ) x).val = x.val := by
  cases hPQ
  rfl

/--
Cast version for sigma-valued subtypes: casting preserves `.val.fst`.
-/
@[simp]
lemma subtype_cast_val_fst {A : Type*} {B : A → Type*}
    {P Q : (Σ a, B a) → Prop}
    (hPQ : P = Q) (x : {s // P s}) :
    (cast (congrArg Subtype hPQ) x).val.fst = x.val.fst := by
  cases hPQ
  rfl

/--
Coercion version for sigma-valued subtypes after cast: casting preserves
the first component when extracted via coercion.
-/
@[simp]
lemma subtype_cast_coe_fst {A : Type*} {B : A → Type*}
    {P Q : (Σ a, B a) → Prop}
    (hPQ : P = Q) (x : {s // P s}) :
    (↑(cast (congrArg Subtype hPQ) x) : Σ a, B a).fst = (↑x : Σ a, B a).fst := by
  cases hPQ
  rfl

/--
When transporting a subtype whose underlying value is a sigma type along a
predicate equality, then taking `.val.fst`, we get the original `.fst`.
-/
@[simp]
lemma subtype_transport_pred_val_fst {A : Type*} {B : A → Type*}
    {P Q : (Σ a, B a) → Prop}
    (hPQ : P = Q) (x : Subtype P) :
    (hPQ ▸ x : Subtype Q).val.fst = x.val.fst := by
  cases hPQ
  rfl

/--
Same as `subtype_transport_pred_val_fst` but with explicit constructor.
-/
@[simp]
lemma subtype_transport_pred_mk_fst {A : Type*} {B : A → Type*}
    {P Q : (Σ a, B a) → Prop}
    (hPQ : P = Q) (v : Σ a, B a) (p : P v) :
    (hPQ ▸ ⟨v, p⟩ : Subtype Q).val.fst = v.fst := by
  cases hPQ
  rfl

/--
Transport of a subtype with explicit constructor, taking `.val.fst`.
Same as `subtype_transport_pred_mk_fst` with the ⟨v, p⟩ pattern.
-/
@[simp]
lemma subtype_transport_pred_mk_val_fst' {A : Type*} {B : A → Type*}
    {P Q : (Σ a, B a) → Prop}
    (hPQ : P = Q) (v : Σ a, B a) (p : P v) :
    (hPQ ▸ ⟨v, p⟩ : Subtype Q).val.fst = v.fst := by
  cases hPQ
  rfl

/--
Coercion version: When transporting a subtype whose underlying value is a
sigma type along a predicate equality, then taking the coercion and `.fst`,
we get the original coercion's `.fst`.
-/
@[simp]
lemma subtype_transport_pred_coe_fst {A : Type*} {B : A → Type*}
    {P Q : (Σ a, B a) → Prop}
    (hPQ : P = Q) (x : Subtype P) :
    (↑(hPQ ▸ x : Subtype Q) : Σ a, B a).fst = (↑x : Σ a, B a).fst := by
  cases hPQ
  rfl

/--
Coercion version with explicit constructor: When transporting an explicit
subtype constructor along a predicate equality, then taking the coercion and
`.fst`, we get the original sigma's `.fst`.
-/
@[simp]
lemma subtype_transport_pred_mk_coe_fst {A : Type*} {B : A → Type*}
    {P Q : (Σ a, B a) → Prop}
    (hPQ : P = Q) {v : Σ a, B a} (p : P v) :
    (↑(hPQ ▸ (⟨v, p⟩ : Subtype P) : Subtype Q) : Σ a, B a).fst = v.fst := by
  cases hPQ
  rfl

/--
When transporting an explicit subtype constructor along a predicate equality,
then taking `.val.fst`, we get the original sigma's `.fst`.
-/
@[simp]
lemma subtype_transport_pred_mk_val_fst {A : Type*} {B : A → Type*}
    {P Q : (Σ a, B a) → Prop}
    (hPQ : P = Q) {v : Σ a, B a} (p : P v) :
    (hPQ ▸ (⟨v, p⟩ : Subtype P) : Subtype Q).val.fst = v.fst := by
  cases hPQ
  rfl

/--
Transport version: When transporting an explicit subtype constructor along a
predicate equality, the transported value is still in Subtype Q (not Subtype P),
and taking `.val.fst` yields the original sigma's `.fst`.
This version uses `.val` notation (definitionally equal to `↑`) to avoid
needing explicit coercion target types.
-/
@[simp]
lemma subtype_transport_pred_mk_coe_fst_bare {A : Type*} {B : A → Type*}
    {P Q : (Σ a, B a) → Prop}
    (hPQ : P = Q) {v : Σ a, B a} (p : P v) :
    (hPQ ▸ (⟨v, p⟩ : Subtype P)).val.fst = v.fst := by
  cases hPQ
  rfl

/--
When transporting any subtype value along a predicate equality, then taking
`.val.fst`, we get the original value's `.fst`. This version takes any
Subtype value rather than requiring an explicit constructor.
-/
@[simp]
lemma subtype_transport_pred_coe_fst' {A : Type*} {B : A → Type*}
    {P Q : (Σ a, B a) → Prop}
    (hPQ : P = Q) (x : Subtype P) :
    (hPQ ▸ x).val.fst = x.val.fst := by
  cases hPQ
  rfl

/--
Version that uses `Subtype.val` coercion followed by `.fst`.
When transporting a subtype along a predicate equality then taking the value's
`.fst`, we get the original value's `.fst`.
-/
@[simp]
lemma subtype_transport_pred_sigma_coe_fst {A : Type*} {B : A → Type*}
    {P Q : (Σ a, B a) → Prop}
    (hPQ : P = Q) (x : Subtype P) :
    ((hPQ ▸ x : Subtype Q).val : Σ a, B a).fst = (x.val : Σ a, B a).fst := by
  cases hPQ
  rfl

/--
Version using coercion notation. When transporting a subtype along a
predicate equality then taking the coerced value's `.fst`, we get the
original coerced value's `.fst`.
-/
@[simp]
lemma subtype_transport_pred_coe_sigma_fst {A : Type*} {B : A → Type*}
    {P Q : (Σ a, B a) → Prop}
    (hPQ : P = Q) (x : Subtype P) :
    (↑(hPQ ▸ x : Subtype Q) : Σ a, B a).fst = (↑x : Σ a, B a).fst := by
  cases hPQ
  rfl

/--
Version for explicit constructor. When transporting an explicit subtype
constructor along a predicate equality then taking coerced `.fst`, we get
the original sigma's `.fst`.
-/
@[simp]
lemma subtype_transport_pred_coe_mk_sigma_fst {A : Type*} {B : A → Type*}
    {P Q : (Σ a, B a) → Prop}
    (hPQ : P = Q) {v : Σ a, B a} (p : P v) :
    (↑(hPQ ▸ (⟨v, p⟩ : Subtype P) : Subtype Q) : Σ a, B a).fst = v.fst := by
  cases hPQ
  rfl

/--
When transporting an explicit subtype constructor along a predicate equality,
then taking `.val.snd`, we get HEq to the original sigma's `.snd`.
-/
lemma subtype_transport_pred_mk_val_snd_heq {A : Type*} {B : A → Type*}
    {P Q : (Σ a, B a) → Prop}
    (hPQ : P = Q) {v : Σ a, B a} (p : P v) :
    (hPQ ▸ (⟨v, p⟩ : Subtype P) : Subtype Q).val.snd ≍ v.snd := by
  cases hPQ
  rfl

/--
When transporting a subtype whose underlying value is a sigma type along a
predicate equality, then taking `.val.snd`, we get HEq to the original `.snd`.
-/
lemma subtype_transport_pred_val_snd_heq {A : Type*} {B : A → Type*}
    {P Q : (Σ a, B a) → Prop}
    (hPQ : P = Q) (x : Subtype P) :
    (hPQ ▸ x : Subtype Q).val.snd ≍ x.val.snd := by
  cases hPQ
  rfl

/--
When transporting a subtype whose underlying value is a nested sigma type along
a predicate equality, then taking `.val.snd.fst`, we get the original value.
For non-dependent B, this is an equality.
-/
@[simp]
lemma subtype_transport_pred_val_snd_fst {A : Type*} {B : Type*}
    {C : A → B → Type*}
    {P Q : (Σ (a : A), (Σ (b : B), C a b)) → Prop}
    (hPQ : P = Q) (x : Subtype P) :
    (hPQ ▸ x : Subtype Q).val.snd.fst = x.val.snd.fst := by
  cases hPQ
  rfl

/--
When transporting an explicit subtype constructor with nested sigma along a
predicate equality, then taking `.val.snd.fst`, we get the original value.
-/
@[simp]
lemma subtype_transport_pred_mk_val_snd_fst {A : Type*} {B : Type*}
    {C : A → B → Type*}
    {P Q : (Σ (a : A), (Σ (b : B), C a b)) → Prop}
    (hPQ : P = Q) {v : Σ (a : A), (Σ (b : B), C a b)} (p : P v) :
    (hPQ ▸ (⟨v, p⟩ : Subtype P) : Subtype Q).val.snd.fst = v.snd.fst := by
  cases hPQ
  rfl

/--
When transporting an explicit subtype constructor with nested sigma along a
predicate equality, then taking `.val.snd.snd`, we get HEq to the original.
-/
lemma subtype_transport_pred_mk_val_snd_snd_heq {A : Type*} {B : Type*}
    {C : A → B → Type*}
    {P Q : (Σ (a : A), (Σ (b : B), C a b)) → Prop}
    (hPQ : P = Q) {v : Σ (a : A), (Σ (b : B), C a b)} (p : P v) :
    (hPQ ▸ (⟨v, p⟩ : Subtype P) : Subtype Q).val.snd.snd ≍ v.snd.snd := by
  cases hPQ
  rfl

/--
When transporting a subtype whose underlying value is a nested sigma type along
a predicate equality, then taking `.val.snd.snd`, we get HEq to the original.
-/
lemma subtype_transport_pred_val_snd_snd_heq {A : Type*} {B : Type*}
    {C : A → B → Type*}
    {P Q : (Σ (a : A), (Σ (b : B), C a b)) → Prop}
    (hPQ : P = Q) (x : Subtype P) :
    (hPQ ▸ x : Subtype Q).val.snd.snd ≍ x.val.snd.snd := by
  cases hPQ
  rfl

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
When two subtypes have the same underlying value but different predicates
indexed by equal indices, they are heterogeneously equal.
-/
lemma subtype_heq_of_pred_index_eq {A : Type*} {I : Type*} {f : I → A → Prop}
    {i j : I} (hij : i = j)
    {v : A} (hi : f i v) (hj : f j v) :
    HEq (⟨v, hi⟩ : { x // f i x }) (⟨v, hj⟩ : { x // f j x }) := by
  subst hij
  rfl

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

/--
Extract first component equality from HEq of sigmas over families that depend on
a shape parameter known to be equal. When shapes are equal, sigma types over
the families are equal, so HEq implies Eq.
-/
lemma sigma_fst_eq_of_heq_via_shape_eq {Shape : Type*} {α : Type*}
    {F : Shape → α → Type*}
    {s₁ s₂ : Shape} (hs : s₁ = s₂)
    {p₁ : Sigma (F s₁)} {p₂ : Sigma (F s₂)}
    (hp : p₁ ≍ p₂) : p₁.fst = p₂.fst := by
  subst hs
  exact congrArg Sigma.fst (eq_of_heq hp)

/--
Extract second component HEq from HEq of sigmas over families that depend on
a shape parameter known to be equal.
-/
lemma sigma_snd_heq_of_heq_via_shape_eq {Shape : Type*} {α : Type*}
    {F : Shape → α → Type*}
    {s₁ s₂ : Shape} (hs : s₁ = s₂)
    {p₁ : Sigma (F s₁)} {p₂ : Sigma (F s₂)}
    (hp : p₁ ≍ p₂) : p₁.snd ≍ p₂.snd := by
  subst hs
  exact sigma_snd_heq_of_eq (eq_of_heq hp)

/--
Fully-implicit version of transport lemma for sigma fst.
Takes all arguments implicitly so that Lean can infer them from the goal.
-/
@[simp]
lemma subtype_transport_pred_coe_sigma_fst' {A : Type*} {B : A → Type*}
    {P Q : (Σ a, B a) → Prop}
    {v : Σ a, B a} {p : P v}
    {hPQ : P = Q} :
    (↑(hPQ ▸ (⟨v, p⟩ : Subtype P) : Subtype Q) : Σ a, B a).fst = v.fst := by
  cases hPQ
  rfl

/--
Fully-implicit version: transport then `.val.snd.fst` equals original.
-/
@[simp]
lemma subtype_transport_pred_val_snd_fst' {A : Type*} {B : Type*}
    {C : A → B → Type*}
    {P Q : (Σ (a : A), (Σ (b : B), C a b)) → Prop}
    {v : Σ (a : A), (Σ (b : B), C a b)} {p : P v}
    {hPQ : P = Q} :
    (hPQ ▸ (⟨v, p⟩ : Subtype P) : Subtype Q).val.snd.fst = v.snd.fst := by
  cases hPQ
  rfl

/--
Fully-implicit version: transport then `.val.snd.snd` is HEq to original.
-/
lemma subtype_transport_pred_val_snd_snd_heq' {A : Type*} {B : Type*}
    {C : A → B → Type*}
    {P Q : (Σ (a : A), (Σ (b : B), C a b)) → Prop}
    {v : Σ (a : A), (Σ (b : B), C a b)} {p : P v}
    {hPQ : P = Q} :
    (hPQ ▸ (⟨v, p⟩ : Subtype P) : Subtype Q).val.snd.snd ≍ v.snd.snd := by
  cases hPQ
  rfl

/--
Fully-implicit version: transport then `.val.snd.snd` equals original.
Uses equality instead of HEq when the type is non-dependent on fst.
-/
@[simp]
lemma subtype_transport_pred_val_snd_snd' {A : Type*} {B : Type*}
    {C : Type*}
    {P Q : (Σ (_a : A), (Σ (_b : B), C)) → Prop}
    {v : Σ (_a : A), (Σ (_b : B), C)} {p : P v}
    {hPQ : P = Q} :
    (hPQ ▸ (⟨v, p⟩ : Subtype P) : Subtype Q).val.snd.snd = v.snd.snd := by
  cases hPQ
  rfl

/--
Combined extraction of both components from HEq of sigmas when shapes are known
equal. First component is equal, second component is HEq.
-/
lemma sigma_components_of_heq_via_shape_eq {Shape : Type*} {α : Type*}
    {F : Shape → α → Type*}
    {s₁ s₂ : Shape} (hs : s₁ = s₂)
    {p₁ : Sigma (F s₁)} {p₂ : Sigma (F s₂)}
    (hp : p₁ ≍ p₂) : p₁.fst = p₂.fst ∧ p₁.snd ≍ p₂.snd := by
  subst hs
  exact ⟨congrArg Sigma.fst (eq_of_heq hp), sigma_snd_heq_of_eq (eq_of_heq hp)⟩

/--
When fibers and shapes are both known equal, sigma positions can be compared.
This variant handles the case where shapes live in dependent types indexed by
fibers.
-/
lemma sigma_fst_eq_of_heq_via_fiber_shape_eq {X : Type*} {Shape : X → Type*}
    {α : Type*} {F : (x : X) → Shape x → α → Type*}
    {x₁ x₂ : X} (hx : x₁ = x₂)
    {s₁ : Shape x₁} {s₂ : Shape x₂} (hs : s₁ ≍ s₂)
    {p₁ : Sigma (F x₁ s₁)} {p₂ : Sigma (F x₂ s₂)}
    (hp : p₁ ≍ p₂) : p₁.fst = p₂.fst := by
  subst hx
  have hs_eq : s₁ = s₂ := eq_of_heq hs
  subst hs_eq
  exact congrArg Sigma.fst (eq_of_heq hp)

/--
Extract second component HEq when fibers and shapes are both known equal.
-/
lemma sigma_snd_heq_of_heq_via_fiber_shape_eq {X : Type*} {Shape : X → Type*}
    {α : Type*} {F : (x : X) → Shape x → α → Type*}
    {x₁ x₂ : X} (hx : x₁ = x₂)
    {s₁ : Shape x₁} {s₂ : Shape x₂} (hs : s₁ ≍ s₂)
    {p₁ : Sigma (F x₁ s₁)} {p₂ : Sigma (F x₂ s₂)}
    (hp : p₁ ≍ p₂) : p₁.snd ≍ p₂.snd := by
  subst hx
  have hs_eq : s₁ = s₂ := eq_of_heq hs
  subst hs_eq
  exact sigma_snd_heq_of_eq (eq_of_heq hp)

/--
For sigma types `Σ x : α, β₁ x` and `Σ x : α, β₂ x` with the same index type `α`,
if two values are HEq, their first components are equal.
Requires that β₁ = β₂.
-/
lemma sigma_fst_eq_of_heq_same_index.{u, v} {α : Type u}
    {β₁ β₂ : α → Type v}
    {p₁ : Sigma β₁} {p₂ : Sigma β₂}
    (hβ : β₁ = β₂)
    (hp : p₁ ≍ p₂) : p₁.fst = p₂.fst := by
  subst hβ
  exact congrArg Sigma.fst (eq_of_heq hp)

/--
For sigma types with the same index type and equal families,
extract snd HEq from sigma HEq.
-/
lemma sigma_snd_heq_of_heq_same_index.{u, v} {α : Type u}
    {β₁ β₂ : α → Type v}
    {p₁ : Sigma β₁} {p₂ : Sigma β₂}
    (hβ : β₁ = β₂)
    (hp : p₁ ≍ p₂) : p₁.snd ≍ p₂.snd := by
  subst hβ
  exact sigma_snd_heq_of_eq (eq_of_heq hp)

/--
Sigma equality for subtypes of function types where the domain depends on the
first component. Given equality of indices and pointwise equality of function
values (with appropriate casting), we get equality of the full sigma-subtype
structure.
-/
lemma sigma_subtype_fun_eq {I : Type*} {A : Type*}
    {F : I → Type*}
    {P : (i : I) → (F i → A) → Prop}
    {i1 i2 : I} (hi : i1 = i2)
    {f1 : F i1 → A} {f2 : F i2 → A}
    (hP1 : P i1 f1) (hP2 : P i2 f2)
    (hf : ∀ p : F i1, f1 p = f2 (cast (congrArg F hi) p)) :
    (⟨i1, ⟨f1, hP1⟩⟩ : Σ i, { f : F i → A // P i f }) =
    ⟨i2, ⟨f2, hP2⟩⟩ := by
  cases hi
  simp only [cast_eq] at hf
  congr 1
  exact Subtype.ext (funext hf)

/--
HEq of subtypes of function types where the domain depends on an index.
Given equality of indices and pointwise equality of function values
(with appropriate casting), we get HEq of the subtypes.
-/
lemma subtype_fun_heq {I : Type*} {A : Type*}
    {F : I → Type*}
    {P : (i : I) → (F i → A) → Prop}
    {i1 i2 : I} (hi : i1 = i2)
    {f1 : F i1 → A} {f2 : F i2 → A}
    (hP1 : P i1 f1) (hP2 : P i2 f2)
    (hf : ∀ p : F i1, f1 p = f2 (cast (congrArg F hi) p)) :
    (⟨f1, hP1⟩ : { f : F i1 → A // P i1 f }) ≍
    (⟨f2, hP2⟩ : { f : F i2 → A // P i2 f }) := by
  cases hi
  simp only [cast_eq] at hf
  exact heq_of_eq (Subtype.ext (funext hf))

/--
Variant of `subtype_fun_heq` that takes subtypes as explicit arguments.
-/
lemma subtype_fun_heq' {I : Type*} {A : Type*}
    {F : I → Type*}
    {P : (i : I) → (F i → A) → Prop}
    {i1 i2 : I} (hi : i1 = i2)
    (s1 : { f : F i1 → A // P i1 f })
    (s2 : { f : F i2 → A // P i2 f })
    (hf : ∀ p : F i1, s1.val p = s2.val (cast (congrArg F hi) p)) :
    s1 ≍ s2 := by
  cases hi
  simp only [cast_eq] at hf
  exact heq_of_eq (Subtype.ext (funext hf))

/--
For sigma types indexed by the same type I, when we have an equality of the
fiber families (F = G), casting a sigma value preserves the first component.
-/
lemma sigma_cast_fst.{u, v} {I : Type u} {F : I → Type v}
    {G : I → Type v}
    (hFG : F = G)
    (s : Σ i, F i) :
    (cast (congrArg Sigma hFG) s).fst = s.fst := by
  cases hFG
  rfl

/--
For sigma types over the same index type, when we have pointwise equality of
families (F i = G i for all i), a sigma value ⟨i, x⟩ casts to ⟨i, cast ... x⟩.
-/
lemma sigma_cast_eq_mk.{u, v} {I : Type u} {F : I → Type v}
    {G : I → Type v}
    (hFG : ∀ i, F i = G i)
    {i : I} {x : F i} :
    cast (congrArg Sigma (funext hFG)) ⟨i, x⟩ = ⟨i, cast (hFG i) x⟩ := by
  cases (funext hFG : F = G)
  simp only [cast_eq]

/--
When the sigma type depends on an outer index, casting along an equality of
indices preserves the first component of the sigma.
-/
lemma sigma_cast_fst_of_outer {I : Type*} {S : I → Type*}
    {F : (i : I) → S i → Type*}
    {i1 i2 : I} (hi : i1 = i2)
    {s : S i1} {x : F i1 s} :
    (cast (congrArg (fun i => Σ s : S i, F i s) hi) ⟨s, x⟩).fst ≍ s := by
  cases hi
  rfl

/--
Heterogeneous equality version of sigma cast equality: when casting a sigma
along an equality of indices, the components are HEq to the originals.
-/
lemma sigma_cast_snd_heq {I : Type*} {S : I → Type*}
    {F : (i : I) → S i → Type*}
    {i1 i2 : I} (hi : i1 = i2)
    {s : S i1} {x : F i1 s} :
    (cast (congrArg (fun i => Σ s : S i, F i s) hi) ⟨s, x⟩).snd ≍ x := by
  cases hi
  rfl

/--
For an arbitrary sigma value (not just constructor form), casting along an
equality of indices gives a sigma whose fst is HEq to the original fst.
-/
lemma sigma_cast_fst_heq {I : Type*} {S : I → Type*}
    {F : (i : I) → S i → Type*}
    {i1 i2 : I} (hi : i1 = i2)
    (p : Σ s : S i1, F i1 s) :
    (cast (congrArg (fun i => Σ s : S i, F i s) hi) p).fst ≍ p.fst := by
  cases hi
  rfl

/--
For an arbitrary sigma value (not just constructor form), casting along an
equality of indices gives a sigma whose snd is HEq to the original snd.
-/
lemma sigma_cast_snd_heq' {I : Type*} {S : I → Type*}
    {F : (i : I) → S i → Type*}
    {i1 i2 : I} (hi : i1 = i2)
    (p : Σ s : S i1, F i1 s) :
    (cast (congrArg (fun i => Σ s : S i, F i s) hi) p).snd ≍ p.snd := by
  cases hi
  rfl

/--
When two sigma types are equal and we have HEq between sigma values,
we can extract HEq of components using type coercion.
This version uses explicit proof that the sigma types are equal.
-/
lemma sigma_fst_heq_of_sigma_type_eq.{u, v} {A : Type u}
    {F₁ F₂ : A → Type v}
    (hF : F₁ = F₂)
    {p1 : Σ a : A, F₁ a} {p2 : Σ a : A, F₂ a}
    (hp : p1 ≍ p2) : p1.fst = p2.fst := by
  cases hF
  exact congrArg Sigma.fst (eq_of_heq hp)

lemma sigma_snd_heq_of_sigma_type_eq.{u, v} {A : Type u}
    {F₁ F₂ : A → Type v}
    (hF : F₁ = F₂)
    {p1 : Σ a : A, F₁ a} {p2 : Σ a : A, F₂ a}
    (hp : p1 ≍ p2) : p1.snd ≍ p2.snd := by
  cases hF
  exact sigma_snd_heq_of_eq (eq_of_heq hp)

/--
For sigmas with different index types, HEq of sigmas implies HEq of first components.
This uses the index equality and the structured cast lemmas.
-/
lemma sigma_fst_heq_of_heq_diff_base {I : Type*} {S : I → Type*}
    {F : (i : I) → S i → Type*}
    {i1 i2 : I} (hi : i1 = i2)
    {p1 : Σ s : S i1, F i1 s} {p2 : Σ s : S i2, F i2 s}
    (hp : p1 ≍ p2) : p1.fst ≍ p2.fst := by
  have hTypeEq : (Σ s : S i1, F i1 s) = (Σ s : S i2, F i2 s) :=
    congrArg (fun i => Σ s : S i, F i s) hi
  have hEq : cast hTypeEq p1 = p2 := eq_of_heq ((cast_heq hTypeEq p1).trans hp)
  exact (sigma_cast_fst_heq hi p1).symm.trans (heq_of_eq (congrArg (·.fst) hEq))

/--
For sigmas with different index types, HEq of sigmas implies HEq of second components.
-/
lemma sigma_snd_heq_of_heq_diff_base {I : Type*} {S : I → Type*}
    {F : (i : I) → S i → Type*}
    {i1 i2 : I} (hi : i1 = i2)
    {p1 : Σ s : S i1, F i1 s} {p2 : Σ s : S i2, F i2 s}
    (hp : p1 ≍ p2) : p1.snd ≍ p2.snd := by
  have hTypeEq : (Σ s : S i1, F i1 s) = (Σ s : S i2, F i2 s) :=
    congrArg (fun i => Σ s : S i, F i s) hi
  have hEq : cast hTypeEq p1 = p2 := eq_of_heq ((cast_heq hTypeEq p1).trans hp)
  exact (sigma_cast_snd_heq' hi p1).symm.trans (sigma_snd_heq_of_eq hEq)

/--
Given equality of sigmas where snd is a subtype of a function type, extract
equality of function values at corresponding points. The function domain depends
on the first component.
-/
lemma sigma_subtype_fun_app_eq {I : Type*} {A : Type*}
    {F : I → Type*}
    {P : (i : I) → (F i → A) → Prop}
    {i1 i2 : I}
    {f1 : F i1 → A} {hP1 : P i1 f1}
    {f2 : F i2 → A} {hP2 : P i2 f2}
    (heq : (⟨i1, ⟨f1, hP1⟩⟩ : Σ i, { f : F i → A // P i f }) =
           ⟨i2, ⟨f2, hP2⟩⟩)
    (x : F i1) :
    f1 x = f2 (cast (congrArg F (congrArg Sigma.fst heq)) x) := by
  have hfst : i1 = i2 := congrArg Sigma.fst heq
  cases hfst
  simp only [cast_eq]
  simp only [Sigma.mk.injEq] at heq
  have hsnd := eq_of_heq heq.2
  exact congrFun (congrArg Subtype.val hsnd) x

/--
Variant of sigma_subtype_fun_app_eq that takes sigma values directly.
-/
lemma sigma_subtype_fun_app_eq' {I : Type*} {A : Type*}
    {F : I → Type*}
    {P : (i : I) → (F i → A) → Prop}
    (s1 s2 : Σ i, { f : F i → A // P i f })
    (heq : s1 = s2)
    (x : F s1.fst) :
    s1.snd.val x = s2.snd.val (cast (congrArg F (congrArg Sigma.fst heq)) x) := by
  cases heq
  rfl

/--
For dependent sigma types, matching on a cast sigma gives the same result as
applying the function to the cast components.

When we have `⟨a, b⟩ : Σ x : A1, P1 x` and cast it to `Σ x : A2, P2 x`,
matching and applying a function `f` gives the same result as applying `f`
to the cast components directly.
-/
lemma sigma_cast_match_eq.{u, v, w} {A1 A2 : Type u} {P1 : A1 → Type v}
    {P2 : A2 → Type v} {R : Type w}
    (hA : A1 = A2) (hP : ∀ a1 : A1, P1 a1 = P2 (cast hA a1))
    (a : A1) (b : P1 a)
    (f : (x : A2) → P2 x → R)
    (hsig : (Σ x : A1, P1 x) = (Σ x : A2, P2 x)) :
    (match (cast hsig ⟨a, b⟩ : Σ x : A2, P2 x) with
      | ⟨x, y⟩ => f x y) =
    f (cast hA a) (cast (hP a) b) := by
  cases hA
  simp only [cast_eq] at hP
  have hP' : P1 = P2 := funext hP
  cases hP'
  simp only [cast_eq]

/--
Transport over a product distributes to the second component.
When both components of a product depend on a parameter `x`, transporting
along `h : x₁ = x₂` gives: `(h ▸ (a, b)).2 = h ▸ b`.
-/
lemma prod_transport_snd {I : Type*} {A B : I → Type*}
    {i₁ i₂ : I} (h : i₁ = i₂) {a : A i₁} {b : B i₁} :
    (h ▸ (a, b) : A i₂ × B i₂).2 = h ▸ b := by
  cases h
  rfl

/--
Transport over a product distributes to the first component.
When both components of a product depend on a parameter `x`, transporting
along `h : x₁ = x₂` gives: `(h ▸ (a, b)).1 = h ▸ a`.
-/
lemma prod_transport_fst {I : Type*} {A B : I → Type*}
    {i₁ i₂ : I} (h : i₁ = i₂) {a : A i₁} {b : B i₁} :
    (h ▸ (a, b) : A i₂ × B i₂).1 = h ▸ a := by
  cases h
  rfl

/--
Over morphisms with targets propositionally equal are heterogeneously equal
if their left functions are HEq.
-/
lemma overHomHEqOfTargetEq {X : Type*} {S T1 T2 : Over X}
    (hT : T1 = T2)
    {f : S ⟶ T1} {g : S ⟶ T2}
    (hfg : f.left ≍ g.left) :
    f ≍ g := by
  cases hT
  have : f.left = g.left := eq_of_heq hfg
  exact heq_of_eq (Over.OverMorphism.ext this)

/--
Extract `.left` HEq from HEq of Over morphisms with same source and target.
-/
lemma overMorphismLeftHEqOfHEq {X : Type*} {S T : Over X}
    {m1 m2 : S ⟶ T}
    (h : m1 ≍ m2) :
    m1.left ≍ m2.left := by
  have := eq_of_heq h
  exact heq_of_eq (congrArg CommaMorphism.left this)

/--
Extract `.left` HEq from HEq of Over morphisms with propositionally equal
sources and targets.
-/
lemma overMorphismLeftHEqOfHEq' {X : Type*} {S1 S2 T1 T2 : Over X}
    (hS : S1 = S2) (hT : T1 = T2)
    {m1 : S1 ⟶ T1} {m2 : S2 ⟶ T2}
    (h : m1 ≍ m2) :
    m1.left ≍ m2.left := by
  cases hS
  cases hT
  exact overMorphismLeftHEqOfHEq h

universe u' v' in
/--
Given HEq of functions with propositionally equal domains, extract pointwise
equality after transport.
-/
lemma funHEqApply {A B : Type u'} {C : Type v'} (hAB : A = B) {f : A → C}
    {g : B → C} (h : f ≍ g) (a : A) : f a = g (hAB ▸ a) := by
  cases hAB
  exact congrFun (eq_of_heq h) a

/--
For dependent sigma types where the first component is equal and second
components are HEq, the overall sigmas are equal. This is a direct
formulation useful when we have explicit shape equality.
-/
lemma sigma_eq_of_fst_eq_snd_heq {α : Type*} {β : α → Type*}
    {a₁ a₂ : α} (ha : a₁ = a₂)
    {b₁ : β a₁} {b₂ : β a₂} (hb : b₁ ≍ b₂) :
    (⟨a₁, b₁⟩ : Sigma β) = ⟨a₂, b₂⟩ := by
  cases ha
  cases hb
  rfl

/--
Over.homMk is HEq to Over.homMk composed with a morphism when the sources
are propositionally equal and the left functions satisfy the corresponding
pointwise relationship.
-/
lemma overHomMkHEqHomMkComp {X : Type*} {S1 S2 A B : Over X}
    (hS : S1 = S2)
    {g1 : S1.left → B.left} {h1 : g1 ≫ B.hom = S1.hom}
    {g2 : S2.left → A.left} {h2 : g2 ≫ A.hom = S2.hom}
    (f : A ⟶ B)
    (hg : g1 ≍ (fun x => f.left (g2 (hS ▸ x)))) :
    (Over.homMk g1 h1 : S1 ⟶ B) ≍ (Over.homMk g2 h2 : S2 ⟶ A) ≫ f := by
  cases hS
  have hleft : g1 = fun x => f.left (g2 x) := eq_of_heq hg
  have : (Over.homMk g1 h1).left = (Over.homMk g2 h2 ≫ f).left := by
    simp only [Over.homMk_left, Over.comp_left]
    exact hleft
  exact heq_of_eq (Over.OverMorphism.ext this)

universe u_vts in
/--
Transport of values through sigma matches equals direct transport with proof
irrelevance. Given any two proofs of element and function equalities (which
may be different proof terms), applying `g` to a transported element equals
matching on a transported sigma. This generalizes `sigma_transport_match_eq_direct`
by allowing the proofs to come from arbitrary sources.
-/
@[simp]
lemma val_transport_sigma_match_irrel {I : Type*} {F G : I → Type u_vts}
    {R : Type*} (g : (i : I) → G i → R)
    (i : I) (b : F i) (hElem : F i = G i) (hFun : F = G) :
    g i (hElem ▸ b) =
    (match (hFun ▸ ⟨i, b⟩ : (j : I) × G j) with | ⟨j, c⟩ => g j c) := by
  have hProofIrrel : hElem = congrFun hFun i := Subsingleton.elim _ _
  rw [hProofIrrel, sigma_transport_match_simple]

/--
Transport of a sigma type where the first component type doesn't depend on
the transported parameter. In this case, the first component is preserved
and only the second component is transported.

Given `β : α → I → Type*` where the first component `i : I` doesn't depend
on the transported parameter `a`, transporting `⟨i, b⟩` by `h : a₁ = a₂`
gives `⟨i, h ▸ b⟩`.
-/
@[simp]
theorem sigma_subst_fst_stable {α : Type*} {I : Type*} {β : α → I → Type*}
    {a₁ a₂ : α} (h : a₁ = a₂) (i : I) (b : β a₁ i) :
    (h ▸ (⟨i, b⟩ : (j : I) × β a₁ j) : (j : I) × β a₂ j) = ⟨i, h ▸ b⟩ := by
  subst h
  rfl

/--
Equality of triple-nested sigma types when all three indices are equal
and the innermost values (in a product) are HEq. The structure is:
  ⟨a₁, ⟨b₁, ⟨c₁, (d₁, e₁)⟩⟩⟩ = ⟨a₂, ⟨b₂, ⟨c₂, (d₂, e₂)⟩⟩⟩
given ha : a₁ = a₂, hb : b₁ = b₂, hc : c₁ = c₂, and HEq of the pairs.
-/
lemma sigma_eq_triple_of_indices_eq
    {A : Type*} {B : A → Type*} {C : (a : A) → B a → Type*}
    {D E : (a : A) → (b : B a) → C a b → Type*}
    {a₁ a₂ : A} (ha : a₁ = a₂)
    {b₁ : B a₁} {b₂ : B a₂} (hb : b₁ ≍ b₂)
    {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} (hc : c₁ ≍ c₂)
    {d₁ : D a₁ b₁ c₁} {d₂ : D a₂ b₂ c₂} (hd : d₁ ≍ d₂)
    {e₁ : E a₁ b₁ c₁} {e₂ : E a₂ b₂ c₂} (he : e₁ ≍ e₂) :
    (⟨a₁, ⟨b₁, ⟨c₁, (d₁, e₁)⟩⟩⟩ : Sigma (fun a => Sigma (fun b => Sigma (fun c =>
      D a b c × E a b c)))) =
    ⟨a₂, ⟨b₂, ⟨c₂, (d₂, e₂)⟩⟩⟩ := by
  cases ha
  cases hb
  cases hc
  cases hd
  cases he
  rfl

/--
Equality of triple-nested sigma types with non-uniform dependencies.
This is for the case where:
- D depends only on a and b (not c)
- E depends only on b and c (not a)
Structure: ⟨a₁, ⟨b₁, ⟨c₁, (d₁, e₁)⟩⟩⟩ = ⟨a₂, ⟨b₂, ⟨c₂, (d₂, e₂)⟩⟩⟩
-/
lemma sigma_eq_triple_of_indices_eq_nonuniform
    {Obj : Type*}
    {D : Obj → Obj → Type*}
    {E : Obj → Obj → Type*}
    {a₁ a₂ b₁ b₂ c₁ c₂ : Obj}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂)
    {d₁ : D a₁ b₁} {d₂ : D a₂ b₂} (hd : d₁ ≍ d₂)
    {e₁ : E b₁ c₁} {e₂ : E b₂ c₂} (he : e₁ ≍ e₂) :
    (⟨a₁, ⟨b₁, ⟨c₁, (d₁, e₁)⟩⟩⟩ : Sigma (fun a => Sigma (fun b => Sigma (fun c =>
      D a b × E b c)))) =
    ⟨a₂, ⟨b₂, ⟨c₂, (d₂, e₂)⟩⟩⟩ := by
  cases ha
  cases hb
  cases hc
  cases hd
  cases he
  rfl

end GebLean

/--
Tactic to split an equality goal `A = C` into two subgoals `A = B` and `B = C`
where `B` is explicitly provided. Uses `Eq.trans` to combine the results.
-/
macro "intermediate_eq" b:term : tactic =>
  `(tactic| refine Eq.trans (b := $b) ?_ ?_)

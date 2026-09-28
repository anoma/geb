/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation
public import Geb.Prototypes.FreeTopos.Internal.Square
public import Geb.Prototypes.FreeTopos.Classifier

set_option doc.verso true in
/-!
# The soundness of the internal language's rewritings

The semantics of the internal language's judgments, and the soundness of its rewritings. A
formula's arrow holds over an object when it is truth after the arrow to the terminal object
({lit}`Holds`). The judgments are external, with the hypotheses read as a restriction of the
environments: a rewriting in a context under hypotheses is sound when, in every environment of
arrows of the context's types in which the hypotheses hold, a term that compiles rewrites to a
term of its type whose arrow has its arrow's value ({lit}`RwSound`), and a formula is sound when,
in every such environment, it holds where it compiles ({lit}`FmSound`). A theorem is valid when,
at every assignment of objects to its object variables, its conclusion is sound under its
hypotheses ({lit}`Thm.Valid`). Soundness is stated in every such environment, not in the
context's environment of projections alone, since congruence under an abstraction, the
instances of theorems and induction reach environments of other forms. A term's type depends on
its environment's types alone ({name}`Geb.FreeTopos.Internal.compile_retype`), and its arrow in
an environment is its arrow in the context's environment of projections after the tuple of the
environment's arrows ({lit}`compile_of_stdEnv`).

Each equation of the language is sound by the equations of the combinators it compiles to: β by
substitution as composition and the evaluation of a currying, the components of a pair and the η
of pairs and of the terminal type by the product's equations, the unfolding of a definition by
its axiom, and the computation of the folds by the recursions' equations. An equation holds
exactly when its sides have one value, since equality is the characteristic map of the diagonal
({lit}`holds_eq_iff`), so rewriting by an equation among the hypotheses is sound
({lit}`rwHyp_sound`). An instance of a valid theorem holds where the instances of its hypotheses
hold ({lit}`Thm.Valid.inst`): the theorem holds on the subobject of its context's object on which
its hypotheses are true ({name}`Geb.FreeTopos.subObj`), whose substitution the instance's
environment factors through.

## Main definitions

* {lit}`Holds`, {lit}`HypsHold` — the truth of a formula's arrow, and of hypotheses in an
  environment.
* {lit}`RwSound`, {lit}`FmSound` — the soundness of a rewriting and of a formula in a context
  under hypotheses.
* {lit}`Thm.Valid` — the validity of a theorem in a model.
* {lit}`DefnsOk` — the definitions' bodies compile to the arrows their operations denote.

## Main statements

* {lit}`holds_eq_iff` — an equation holds exactly when its sides have one value.
* {lit}`Thm.Valid.inst` — an instance of a valid theorem holds.
* {lit}`rootStep_sound`, {lit}`cong_sound` — the rewritings are sound.

## Tags

internal language, soundness, proof checker, subobject classifier
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree op eval Model IsModel)
open Sorts
open scoped FinEnum

universe v

section Environments

variable {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}

/-- A result is related to itself. -/
theorem ResEq.refl (r : Tree × Tree) : ResEq M ρ r r := ⟨rfl, rfl⟩

/-- Related results are related in the other order. -/
theorem ResEq.symm {r₁ r₂ : Tree × Tree} (h : ResEq M ρ r₁ r₂) : ResEq M ρ r₂ r₁ :=
  ⟨h.1.symm, h.2.symm⟩

/-- Results related to related results are related. -/
theorem ResEq.trans {r₁ r₂ r₃ : Tree × Tree} (h₁ : ResEq M ρ r₁ r₂) (h₂ : ResEq M ρ r₂ r₃) :
    ResEq M ρ r₁ r₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

/-- An environment has its own values. -/
theorem envEq_refl (e : List (Tree × Tree)) : EnvEq M ρ e e :=
  fun _ p hp ↦ ⟨p, hp, ResEq.refl p⟩

/-- The types of a context's environment of projections are the context's. -/
theorem map_snd_stdEnv : ∀ Γ : List Tree, (stdEnv Γ).map Prod.snd = Γ :=
  List.rec rfl fun a Γ ih ↦ by
    rcases Γ with _ | ⟨b, Γ⟩
    · rfl
    · change (extEnv (ctxObj (b :: Γ)) a (stdEnv (b :: Γ))).map Prod.snd = a :: b :: Γ
      simpa [extEnv, Function.comp_def] using ih


/-- Products of equal types have equal factors. -/
theorem prod_inj {a b a' b' : Tree} (h : prod a b = prod a' b') : a = a' ∧ b = b' := by
  have h₁ := prodParts_eq_some.mpr h
  rw [prodParts_eq_some.mpr rfl] at h₁
  simpa using h₁

/-- Exponentials of equal types have equal exponents and bases. -/
theorem exp_inj {a b a' b' : Tree} (h : exp a b = exp a' b') : a = a' ∧ b = b' := by
  have h₁ := expParts_eq_some.mpr h
  rw [expParts_eq_some.mpr rfl] at h₁
  simpa using h₁

/-- List types of equal types have equal element types. -/
theorem list_inj {a a' : Tree} (h : list a = list a') : a = a' := by
  have h₁ := listPart_eq_some.mpr h
  rw [listPart_eq_some.mpr rfl] at h₁
  simpa using h₁

/-- Coproducts of equal types have equal summands. -/
theorem coprod_inj {a b a' b' : Tree} (h : coprod a b = coprod a' b') : a = a' ∧ b = b' := by
  have h₁ := coprodParts_eq_some.mpr h
  rw [coprodParts_eq_some.mpr rfl] at h₁
  simpa using h₁

/-- The element at an index of a list's results under a partial function is the result at the
list's element at the index. -/
theorem getElem?_of_mapM_eq {α β : Type} {f : α → Option β} {l : List α} {rs : List β}
    (h : l.mapM f = some rs) {i : ℕ} {r : β} (hr : rs[i]? = some r) :
    ∃ a, l[i]? = some a ∧ f a = some r := by
  rw [PartialHorn.mapM_eq_some_iff] at h
  have hi := congrArg (·[i]?) h
  simp only [List.getElem?_map, hr, Option.map_some] at hi
  exact Option.map_eq_some_iff.mp hi

/-- Results of two partial functions at related elements of related lists, related whenever the
first has one, lift to the lists of results. -/
theorem mapM_forall₂ {α α' β β' : Type} {R₁ : α → α' → Prop} {R : β → β' → Prop}
    {f : α → Option β} {g : α' → Option β'}
    (hfg : ∀ a a' r, R₁ a a' → f a = some r → ∃ r', g a' = some r' ∧ R r r')
    {l : List α} {l' : List α'} (h : List.Forall₂ R₁ l l') :
    ∀ {rs : List β}, l.mapM f = some rs →
      ∃ rs', l'.mapM g = some rs' ∧ List.Forall₂ R rs rs' :=
  h.rec (motive := fun l l' _ ↦ ∀ {rs : List β}, l.mapM f = some rs →
      ∃ rs', l'.mapM g = some rs' ∧ List.Forall₂ R rs rs')
    (fun h ↦ by
      obtain rfl : [] = _ := by simpa using h
      exact ⟨[], rfl, .nil⟩)
    (fun {a a' _ _} hR _ ih rs h ↦ by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨r, hr, rs₀, hrs₀, rfl⟩ := h
      obtain ⟨r', hr', hRr⟩ := hfg a a' r hR hr
      obtain ⟨rs', hrs', hR'⟩ := ih hrs₀
      exact ⟨r' :: rs', by simp [List.mapM_cons, hr', hrs'], .cons hRr hR'⟩)

/-- Terms of types in a context compile, in every environment of the context's types, to those
types. -/
theorem mapM_compile_of_typeIn {G : Globals} {n : ℕ} {Γ : List Tree} {X : Tree}
    {e : List (Tree × Tree)} (hΓ : e.map Prod.snd = Γ) :
    ∀ (σ : List Term) (Δ : List Tree), σ.length = Δ.length →
      (σ.zip Δ).all (fun x ↦ decide (typeIn G n Γ x.1 = some x.2)) = true →
      ∃ rs, σ.mapM (fun u ↦ compile G n u X e) = some rs ∧ rs.map Prod.snd = Δ := fun σ ↦
  σ.rec (fun Δ hl _ ↦ by
      obtain rfl : Δ = [] := List.length_eq_zero_iff.mp hl.symm
      exact ⟨[], rfl, rfl⟩)
    fun u σ ih Δ hl hall ↦ by
      rcases Δ with _ | ⟨A, Δ⟩
      · simp at hl
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall
      obtain ⟨⟨f₀, A₀⟩, hstd, hA⟩ := Option.map_eq_some_iff.mp hall.1
      obtain rfl : A₀ = A := hA
      obtain ⟨f, hf⟩ := compile_retype u _ _ _ hstd X e (hΓ.trans (map_snd_stdEnv Γ).symm)
      obtain ⟨rs, hrs, hsnd⟩ := ih Δ (by simpa using hl) hall.2
      exact ⟨(f, A₀) :: rs, by simp [List.mapM_cons, hf, hrs], by simp [hsnd]⟩

/-- The empty list's arrow at an object. -/
theorem subst_nil_x (a : Tree) : PartialHorn.subst [a] (nil (x 0)) = nil a := by
  simp [nil, subst_op, subst_x]

/-- Construction's arrow at an object. -/
theorem subst_cons_x (a : Tree) : PartialHorn.subst [a] (cons (x 0)) = cons a := by
  simp [cons, subst_op, subst_x]

/-- The list type at an object. -/
theorem subst_list_x (a : Tree) : PartialHorn.subst [a] (list (x 0)) = list a := by
  simp [subst_list, subst_x]

/-- The product of an object with its list type at an object. -/
theorem subst_prod_list_x (a : Tree) :
    PartialHorn.subst [a] (prod (x 0) (list (x 0))) = prod a (list a) := by
  simp [subst_prod, subst_list, subst_x]


/-- A list's results under a partial function are related to it elementwise. -/
theorem forall₂_of_mapM {α β : Type} {f : α → Option β} (l : List α) :
    ∀ {rs : List β}, l.mapM f = some rs → List.Forall₂ (fun a r ↦ f a = some r) l rs :=
  l.rec (motive := fun l ↦ ∀ {rs : List β}, l.mapM f = some rs →
      List.Forall₂ (fun a r ↦ f a = some r) l rs) (fun h ↦ by
      obtain rfl : [] = _ := by simpa using h
      exact .nil)
    fun a l ih rs h ↦ by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨r, hr, rs₀, hrs₀, rfl⟩ := h
      exact .cons hr (ih hrs₀)

/-- A relation on a list's elements paired with one context is a relation in that context. -/
theorem forall₂_zip_const {α : Type} {R : α → Term → Term → Prop} {Γ : α} (ts : List Term) :
    ∀ {ts' : List Term}, List.Forall₂ (fun (p : α × Term) u ↦ R p.1 p.2 u)
      ((ts.map fun _ ↦ Γ).zip ts) ts' → List.Forall₂ (R Γ) ts ts' :=
  ts.rec (motive := fun ts ↦ ∀ {ts' : List Term},
      List.Forall₂ (fun (p : α × Term) u ↦ R p.1 p.2 u) ((ts.map fun _ ↦ Γ).zip ts) ts' →
        List.Forall₂ (R Γ) ts ts') (fun h ↦ by
      obtain rfl := List.forall₂_nil_left_iff.mp h
      exact .nil)
    fun t ts ih ts' h ↦ by
      rcases h with _ | ⟨h₁, h₂⟩
      exact .cons h₁ (ih h₂)


/-- Zero compiles to its arrow after the arrow to the terminal object. -/
theorem compile_zeroT {G : Globals} {n kz : ℕ} (hk : G.prims[kz]? = some zeroPrim) (X : Tree)
    (e : List (Tree × Tree)) :
    compile G n (Term.arr kz [] Term.star) X e = some (comp zeroN (bang X), nat) :=
  compile_arr_iff.mpr ⟨Term.star, rfl, zeroPrim, hk, bang X,
    compile_star_iff.mpr ⟨rfl, by simp [zeroPrim, subst_one]⟩, rfl, rfl,
    by simp [zeroPrim, zeroN, subst_const, subst_nat]⟩

/-- The successor of a number compiles to the successor after its arrow. -/
theorem compile_succT {G : Globals} {n ks : ℕ} (hk : G.prims[ks]? = some succPrim) {c : Term}
    {X g : Tree} {e : List (Tree × Tree)} (hc : compile G n c X e = some (g, nat)) :
    compile G n (Term.arr ks [] c) X e = some (comp succ g, nat) :=
  compile_arr_iff.mpr ⟨c, rfl, succPrim, hk, g, by simpa [succPrim, subst_nat] using hc, rfl, rfl,
    by simp [succPrim, succ, subst_const, subst_nat]⟩

/-- The empty list compiles to its arrow after the arrow to the terminal object. -/
theorem compile_nilT {G : Globals} {n kn : ℕ} (hk : G.prims[kn]? = some nilPrim) {a : Tree}
    (ha : IsTy G n a = true) (X : Tree) (e : List (Tree × Tree)) :
    compile G n (Term.arr kn [a] Term.star) X e = some (comp (nil a) (bang X), list a) :=
  compile_arr_iff.mpr ⟨Term.star, rfl, nilPrim, hk, bang X,
    compile_star_iff.mpr ⟨rfl, by simp [nilPrim, subst_one]⟩, rfl, by simp [ha],
    by rw [show nilPrim.arrow = nil (x 0) from rfl, subst_nil_x,
      show nilPrim.cod = list (x 0) from rfl, subst_list_x]⟩

/-- A construction compiles to construction after its argument's arrow. -/
theorem compile_consT {G : Globals} {n kc : ℕ} (hk : G.prims[kc]? = some consPrim) {a : Tree}
    (ha : IsTy G n a = true) {c : Term} {X g : Tree} {e : List (Tree × Tree)}
    (hc : compile G n c X e = some (g, prod a (list a))) :
    compile G n (Term.arr kc [a] c) X e = some (comp (cons a) g, list a) :=
  compile_arr_iff.mpr ⟨c, rfl, consPrim, hk, g,
    by rw [show consPrim.dom = prod (x 0) (list (x 0)) from rfl, subst_prod_list_x]; exact hc,
    rfl, by simp [ha], by rw [show consPrim.arrow = cons (x 0) from rfl, subst_cons_x,
      show consPrim.cod = list (x 0) from rfl, subst_list_x]⟩


/-- A relation on a zip, implying one on its second list at elements of the first with a
property, gives the second on the second list. -/
theorem forall₂_zip_imp {α β γ : Type} {P : α → Prop} {R : α × β → γ → Prop}
    {S : β → γ → Prop} (hRS : ∀ a b c, P a → R (a, b) c → S b c) :
    ∀ (l₁ : List α) (l₂ : List β) (l₃ : List γ), l₂.length ≤ l₁.length → (∀ a ∈ l₁, P a) →
      List.Forall₂ R (l₁.zip l₂) l₃ → List.Forall₂ S l₂ l₃ := fun l₁ ↦
  l₁.rec (fun l₂ l₃ hl _ h ↦ by
      obtain rfl : l₂ = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
      obtain rfl := List.forall₂_nil_left_iff.mp h
      exact .nil)
    fun a l₁ ih l₂ l₃ hl hP h ↦ by
      rcases l₂ with _ | ⟨b, l₂⟩
      · obtain rfl := List.forall₂_nil_left_iff.mp h
        exact .nil
      rcases h with _ | ⟨h₁, h₂⟩
      exact .cons (hRS a b _ (hP a List.mem_cons_self) h₁)
        (ih l₂ _ (by simpa using hl) (fun a' ha' ↦ hP a' (List.mem_cons_of_mem _ ha')) h₂)


section Arrows

variable (hM : IsModel (ext defs) M)
include hM

/-- Evaluation after the pairing of a currying with an argument is the curried arrow after the
pairing of the identity with the argument. -/
theorem ev_pair_curry {T g X A B : Tree} (hX : IsObj M ρ X) (hA : IsObj M ρ A)
    (hT : Hom M ρ T (prod X A) B) (hg : Hom M ρ g X A) :
    eval M ρ (comp (ev A B) (pair (curry X A T) g)) = eval M ρ (comp T (pair (idt X) g)) := by
  have hc := curry_hom hM hX hA hT
  have hi := idt_hom hM hX
  have hh := pair_hom hM hi hg
  have hfX := fst_hom hM hX hA
  have hsX := snd_hom hM hX hA
  have hP := pair_hom hM (comp_hom hM hfX hc) hsX
  have e₁ : eval M ρ (pair (curry X A T) g) = eval M ρ
      (comp (pair (comp (curry X A T) (fst X A)) (snd X A)) (pair (idt X) g)) :=
    ((pair_comp hM (comp_hom hM hfX hc) hsX hh).trans (eval_op₂_congr 9
      ((comp_assoc hM hh hfX hc).symm.trans ((eval_op₂_congr 3 rfl (fst_pair hM hi hg)).trans
        (comp_idt hM hc))) (snd_pair hM hi hg))).symm
  exact (eval_op₂_congr 3 rfl e₁).trans ((comp_assoc hM hh hP (ev_hom hM hA hT.isObj_cod)).trans
    (eval_op₂_congr 3 (ev_curry hM hX hA hT) rfl))

/-- An environment after the identity has its own values. -/
theorem envEq_precomp_idt {X : Tree} {e : List (Tree × Tree)}
    (he : ∀ p ∈ e, Hom M ρ p.1 X p.2) : EnvEq M ρ (precomp (idt X) e) e := by
  intro i p hp
  simp only [precomp, List.getElem?_map, Option.map_eq_some_iff] at hp
  obtain ⟨p₀, hp₀, rfl⟩ := hp
  exact ⟨p₀, hp₀, rfl, (comp_idt hM (he p₀ (List.mem_of_getElem? hp₀))).symm⟩

/-- An environment after a composite has the values of the environment after the first arrow
and then the second. -/
theorem envEq_precomp_comp {X Y Z g h : Tree} {e : List (Tree × Tree)}
    (he : ∀ p ∈ e, Hom M ρ p.1 X p.2) (hg : Hom M ρ g Y X) (hh : Hom M ρ h Z Y) :
    EnvEq M ρ (precomp (comp g h) e) (precomp h (precomp g e)) := by
  intro i p hp
  simp only [precomp, List.getElem?_map, Option.map_eq_some_iff] at hp
  obtain ⟨p₀, hp₀, rfl⟩ := hp
  exact ⟨(comp (comp p₀.1 g) h, p₀.2), by simp [precomp, hp₀], rfl,
    (comp_assoc hM hh hg (he p₀ (List.mem_of_getElem? hp₀))).symm⟩

/-- An extended environment after an arrow into the product has the values of the new variable
at its second component and of the environment after its first. -/
theorem envEq_precomp_extEnv {X a Z h k v : Tree} {e e' : List (Tree × Tree)}
    (hX : IsObj M ρ X) (ha : IsObj M ρ a) (he : ∀ p ∈ e, Hom M ρ p.1 X p.2)
    (hh : Hom M ρ h Z (prod X a)) (hk : eval M ρ (comp (fst X a) h) = eval M ρ k)
    (hv : eval M ρ (comp (snd X a) h) = eval M ρ v) (he' : EnvEq M ρ (precomp k e) e') :
    EnvEq M ρ (precomp h (extEnv X a e)) ((v, a) :: e') := by
  intro i p hp
  rcases i with _ | j
  · obtain rfl : (comp (snd X a) h, a) = p := by simpa [precomp, extEnv] using hp
    exact ⟨(v, a), rfl, rfl, hv.symm⟩
  · simp only [precomp, extEnv, List.map_cons, List.getElem?_cons_succ, List.map_map,
      List.getElem?_map, Option.map_eq_some_iff, Function.comp_apply] at hp
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    obtain ⟨q, hq, h₂, h₁⟩ := he' j (comp p₀.1 k, p₀.2) (by simp [precomp, hp₀])
    refine ⟨q, by simpa using hq, h₂, h₁.trans ?_⟩
    exact (eval_op₂_congr 3 rfl hk.symm).trans
      (comp_assoc hM hh (fst_hom hM hX ha) (he p₀ (List.mem_of_getElem? hp₀)))

end Arrows

end Environments

section Rewriting

variable {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}

variable (M ρ) in
/-- An arrow of a formula holds over an object: the formula's type is the subobject classifier's,
and its arrow is truth after the arrow to the terminal object. -/
def Holds (X : Tree) (r : Tree × Tree) : Prop :=
  r.2 = omega ∧ eval M ρ r.1 = eval M ρ (comp tru (bang X))

variable (M ρ) in
/-- Hypotheses hold in an environment: each compiles there to an arrow that holds. -/
def HypsHold (G : Globals) (n : ℕ) (Φ : List Term) (X : Tree) (e : List (Tree × Tree)) : Prop :=
  ∀ ψ ∈ Φ, ∃ r, compile G n ψ X e = some r ∧ Holds M ρ X r

variable (M ρ) in
/-- A rewriting in a context under hypotheses is sound: in every environment of arrows of the
context's types in which the hypotheses hold, a term that compiles rewrites to a term of its
type whose arrow has its arrow's value. -/
def RwSound (G : Globals) (n : ℕ) (Γ : List Tree) (Φ : List Term) (t t' : Term) : Prop :=
  ∀ (X : Tree) (e : List (Tree × Tree)), EnvHom M ρ G n X e → e.map Prod.snd = Γ →
    HypsHold M ρ G n Φ X e →
    ∀ r, compile G n t X e = some r → ∃ r', compile G n t' X e = some r' ∧ ResEq M ρ r r'

variable (M ρ) in
/-- A formula in a context under hypotheses is sound: in every environment of arrows of the
context's types in which the hypotheses hold, the formula, where it compiles, holds. -/
def FmSound (G : Globals) (n : ℕ) (Γ : List Tree) (Φ : List Term) (φ : Term) : Prop :=
  ∀ (X : Tree) (e : List (Tree × Tree)), EnvHom M ρ G n X e → e.map Prod.snd = Γ →
    HypsHold M ρ G n Φ X e → ∀ r, compile G n φ X e = some r → Holds M ρ X r

variable (M) in
/-- Each definition's body compiles in its parameters' environment to its value's type and an
arrow whose instance at types has the value of the definition's operation at them. -/
def DefnsOk (G : Globals) : Prop :=
  ∀ (k : ℕ) (d : Defn), G.defs[k]? = some (.language d) →
    ∃ F, compile G d.arity d.body (ctxObj d.params) (stdEnv d.params) = some (F, d.type) ∧
      ∀ (m : ℕ) (ρ : List M.Val) (θ : List Tree), ρ.map Sigma.fst = List.replicate m obj →
        θ.length = d.arity → θ.all (IsTy G m) = true →
        eval M ρ (op (G.base + k) θ) = eval M ρ (PartialHorn.subst θ F)

variable (M) in
/-- A theorem is valid: its context is of types, its hypotheses and conclusion are formulas
there, and at every assignment of objects to its object variables the constants' arrows are
arrows and the conclusion holds in every environment of arrows of the context's types in which
the hypotheses hold. -/
def Thm.Valid (G : Globals) (a : Thm) : Prop :=
  a.ctx.all (IsTy G a.arity) = true ∧ (∀ h ∈ a.hyps, typeIn G a.arity a.ctx h = some omega) ∧
    typeIn G a.arity a.ctx a.concl = some omega ∧
    ∀ ρ : List M.Val, ρ.map Sigma.fst = List.replicate a.arity obj →
      PrimsHom M ρ G a.arity ∧ DefsHom M ρ G a.arity ∧
        FmSound M ρ G a.arity a.ctx a.hyps a.concl

variable (M) in
/-- An entry of a development's environment is valid: a theorem of the language valid, or a
sequent of the combinators valid in the model. -/
def Entry.Valid (G : Globals) : Entry → Prop
  | .language a => a.Valid M G
  | .combinators s => s.Valid M

/-- The theorem of the language an entry of valid entries is, is valid. -/
theorem Entry.valid_language {G : Globals} {E : Array Entry}
    (hE : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G) {j : ℕ} {a : Thm}
    (h : (E[j]?).bind Entry.language? = some a) : a.Valid M G := by
  obtain ⟨e, he, hea⟩ := Option.bind_eq_some_iff.mp h
  cases e with
  | language a' =>
    obtain rfl := Option.some_inj.mp hea
    exact hE j _ he
  | combinators s => cases hea

/-- The identity rewriting is sound. -/
theorem RwSound.refl {G : Globals} {n : ℕ} (Γ : List Tree) (Φ : List Term) (t : Term) :
    RwSound M ρ G n Γ Φ t t :=
  fun _ _ _ _ _ r h ↦ ⟨r, h, ResEq.refl r⟩

/-- One sound rewriting after another is sound. -/
theorem RwSound.trans {G : Globals} {n : ℕ} {Γ : List Tree} {Φ : List Term} {t t' t'' : Term}
    (h₁ : RwSound M ρ G n Γ Φ t t') (h₂ : RwSound M ρ G n Γ Φ t' t'') :
    RwSound M ρ G n Γ Φ t t'' :=
  fun X e he hΓ hΦ r h ↦ by
    obtain ⟨r', h', hr'⟩ := h₁ X e he hΓ hΦ r h
    obtain ⟨r'', h'', hr''⟩ := h₂ X e he hΓ hΦ r' h'
    exact ⟨r'', h'', hr'.trans hr''⟩

/-- A formula whose sides are two terms is their equation. -/
theorem eqParts_eq_some {φ t u : Term} (h : eqParts φ = some (t, u)) : φ = Term.eq t u := by
  unfold eqParts at h
  split at h
  · rename_i t' u' hl hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp h)
    rw [← RoseTree.node_label_children φ, hl, hc]
    rfl
  · cases h

/-- A result of a partial function at each element of a list is a result of its list's. -/
theorem exists_mem_of_mapM {α β : Type} {f : α → Option β} {l : List α} {ys : List β}
    (h : l.mapM f = some ys) {x : α} (hx : x ∈ l) : ∃ y ∈ ys, f x = some y := by
  have hF := forall₂_of_mapM l h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hy := hF.length_eq ▸ hi
  exact ⟨ys[i], List.getElem_mem hy, List.forall₂_iff_get.mp hF |>.2 i hi hy⟩

/-- A partial function with a result at each element of a list has a list of results. -/
theorem exists_mapM_of_forall {α β : Type} {f : α → Option β} {P : β → Prop} :
    ∀ l : List α, (∀ x ∈ l, ∃ y, f x = some y ∧ P y) →
      ∃ ys, l.mapM f = some ys ∧ ∀ y ∈ ys, P y :=
  List.rec (fun _ ↦ ⟨[], rfl, fun _ h ↦ by simp at h⟩) fun x l ih h ↦ by
    obtain ⟨y, hy, hPy⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys, hP⟩ := ih fun x' hx' ↦ h x' (List.mem_cons_of_mem _ hx')
    refine ⟨y :: ys, by simp [List.mapM_cons, hy, hys], fun y' hy' ↦ ?_⟩
    rcases List.mem_cons.mp hy' with rfl | hy'
    · exact hPy
    · exact hP y' hy'

/-- Hypotheses a lowering takes to others are those others weakened. -/
theorem lowerHyps_spec {G : Globals} {n : ℕ} {Γ : List Tree} {Φ Φ' : List Term}
    (h : lowerHyps G n Γ Φ = some Φ') :
    Φ = Φ'.map weaken1 ∧ ∀ ψ ∈ Φ', typeIn G n Γ ψ = some omega := by
  have hF := forall₂_of_mapM Φ h
  refine ⟨?_, fun ψ hψ ↦ ?_⟩
  · exact hF.rec (motive := fun Φ Φ' _ ↦ Φ = Φ'.map weaken1) rfl fun {a b _ _} hab _ ih ↦ by
      split_ifs at hab with hc
      obtain rfl := Option.some_inj.mp hab
      rw [List.map_cons, ← ih, hc.1]
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hψ
    have hi' := hF.length_eq.symm ▸ hi
    have hab := List.forall₂_iff_get.mp hF |>.2 i hi' hi
    split_ifs at hab with hc
    have hb := Option.some_inj.mp hab
    simp only [List.get_eq_getElem] at hb
    rw [← hb]
    exact hc.2

variable (M ρ) in
/-- Hypotheses with one more hold exactly when the first do and the last holds. -/
theorem hypsHold_append {G : Globals} {n : ℕ} {Φ : List Term} {ψ : Term} {X : Tree}
    {e : List (Tree × Tree)} :
    HypsHold M ρ G n (Φ ++ [ψ]) X e ↔
      HypsHold M ρ G n Φ X e ∧ ∃ r, compile G n ψ X e = some r ∧ Holds M ρ X r := by
  refine ⟨fun h ↦ ⟨fun ψ' hψ' ↦ h ψ' (List.mem_append_left _ hψ'),
    h ψ (List.mem_append_right _ List.mem_cons_self)⟩, fun ⟨h₁, h₂⟩ ψ' hψ' ↦ ?_⟩
  rcases List.mem_append.mp hψ' with hψ' | hψ'
  · exact h₁ ψ' hψ'
  · obtain rfl := List.mem_singleton.mp hψ'
    exact h₂


/-- The rewriting by an equational theorem at a term's root, inverted. -/
theorem rootStep_thm {G : Globals} {E : Array Entry} {n : ℕ} {Γ : List Tree} {Φ : List Term}
    {j : ℕ} {θ : List Tree} {σ : List Term} {flip : Bool} {t t' : Term}
    (h : rootStep G E n Γ Φ (.thm j θ σ flip) t = some t') :
    ∃ a lr, (E[j]?).bind Entry.language? = some a ∧ a.hyps = [] ∧ eqParts a.concl = some lr ∧
      instOk G n Γ a θ σ = true ∧ t = instTerm θ σ (if flip then lr.2 else lr.1) ∧
      t' = instTerm θ σ (if flip then lr.1 else lr.2) := by
  simp only [rootStep] at h
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
  by_cases hnil : a.hyps = []
  · rw [if_pos hnil] at h
    obtain ⟨lr, hlr, h⟩ := Option.bind_eq_some_iff.mp h
    by_cases hc : instOk G n Γ a θ σ = true ∧ t = instTerm θ σ (if flip then lr.2 else lr.1)
    · rw [if_pos hc] at h
      exact ⟨a, lr, ha, hnil, hlr, hc.1, hc.2, (Option.some_inj.mp h).symm⟩
    · rw [if_neg hc] at h
      cases h
  · rw [if_neg hnil] at h
    simp at h

/-- The rewriting by an equation among the hypotheses at a term's root, inverted. -/
theorem rootStep_rwHyp {G : Globals} {E : Array Entry} {n : ℕ} {Γ : List Tree} {Φ : List Term}
    {i : ℕ} {flip : Bool} {t t' : Term} (h : rootStep G E n Γ Φ (.rwHyp i flip) t = some t') :
    ∃ ψ lr, Φ[i]? = some ψ ∧ eqParts ψ = some lr ∧ t = (if flip then lr.2 else lr.1) ∧
      t' = (if flip then lr.1 else lr.2) := by
  simp only [rootStep] at h
  obtain ⟨lr, hlr, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ψ, hψ, hψlr⟩ := Option.bind_eq_some_iff.mp hlr
  by_cases hc : t = (if flip then lr.2 else lr.1)
  · rw [if_pos hc] at h
    exact ⟨ψ, lr, hψ, hψlr, hc, (Option.some_inj.mp h).symm⟩
  · rw [if_neg hc] at h
    cases h

/-- The checker at a node is its step at the node's children and their results. -/
theorem check_node (G : Globals) (E : Array Entry) (n : ℕ) (l : Rule) (cs : List Deriv) :
    check G E n (RoseTree.node l cs) = checkStep G E n l (cs.map fun c ↦ (c, check G E n c)) :=
  RoseTree.para_node _ l cs

/-- A derivation of the identity rule rewrites a term only to itself. -/
theorem check_isRefl {G : Globals} {E : Array Entry} {n : ℕ} {c : Deriv}
    (hc : c.label.isRefl = true) {Γ : List Tree} {Φ : List Term} {t t' : Term}
    (h : (check G E n c).1 Γ Φ t = some t') : t' = t := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, c = RoseTree.node l cs :=
    ⟨_, _, (RoseTree.node_label_children c).symm⟩
  cases l <;> simp only [RoseTree.label_node, Rule.isRefl, reduceCtorEq] at hc
  rw [check_node] at h
  rcases cs with _ | ⟨c', cs⟩
  · exact (Option.some_inj.mp h).symm
  · simp [checkStep] at h

/-- Where a node compiles in an environment of a context's types, the contexts of its children
are defined. -/
theorem childCtxs_isSome {G : Globals} {n : ℕ} {l : Label} {ts : List Term} {Γ : List Tree}
    (Φ : List Term) {X : Tree} {e : List (Tree × Tree)} {r : Tree × Tree}
    (hΓ : e.map Prod.snd = Γ) (h : compile G n (RoseTree.node l ts) X e = some r) :
    ∃ Γs, childCtxs G n l ts Γ Φ = some Γs := by
  cases l with
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
    have hc : typeIn G n [] z = some c := by
      change (compile G n z one []).map Prod.snd = some c
      rw [hz]
      rfl
    refine ⟨[([], []), ([c], []), (Γ, Φ)], ?_⟩
    change (typeIn G n [] z).bind (fun c ↦ some [([], []), ([c], []), (Γ, Φ)]) = _
    rw [hc, Option.bind_some]
  | listRec =>
    obtain ⟨z, s, m, rfl, m', A, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
    have hc : typeIn G n [] z = some c := by
      change (compile G n z one []).map Prod.snd = some c
      rw [hz]
      rfl
    obtain ⟨f₀, hf₀⟩ := compile_retype m X e _ hm (ctxObj Γ) (stdEnv Γ)
      (by rw [map_snd_stdEnv, hΓ])
    have hmt : typeIn G n Γ m = some (list A) := by
      change (compile G n m (ctxObj Γ) (stdEnv Γ)).map Prod.snd = some (list A)
      rw [hf₀]
      rfl
    refine ⟨[([], []), ([c, A], []), (Γ, Φ)], ?_⟩
    change (typeIn G n [] z).bind (fun c ↦ ((typeIn G n Γ m).bind listPart).bind
      fun a ↦ some [([], []), ([c, a], []), (Γ, Φ)]) = _
    rw [hc, Option.bind_some, hmt, Option.bind_some, listPart_eq_some.mpr rfl, Option.bind_some]
  | roseRec c =>
    obtain ⟨s, m, m', t, a, F, s', rfl, hct, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp h
    obtain ⟨f₀, hf₀⟩ := compile_retype m X e _ hm (ctxObj Γ) (stdEnv Γ)
      (by rw [map_snd_stdEnv, hΓ])
    have hmt : typeIn G n Γ m = some t := by
      change (compile G n m (ctxObj Γ) (stdEnv Γ)).map Prod.snd = some t
      rw [hf₀]
      rfl
    refine ⟨[([prod a (list c)], []), (Γ, Φ)], ?_⟩
    change ((typeIn G n Γ m).bind roseParts).bind
      (fun p ↦ some [([prod p.1 (list c)], []), (Γ, Φ)]) = _
    rw [hmt, Option.bind_some, ht, Option.bind_some]
  | lam a => rcases ts with _ | ⟨b, _ | ⟨b', ts⟩⟩ <;> exact ⟨_, rfl⟩
  | _ => exact ⟨_, rfl⟩

/-- The contexts of a node's children number its children. -/
theorem childCtxs_length {G : Globals} {n : ℕ} {l : Label} {ts : List Term} {Γ : List Tree}
    {Φ : List Term} {Γs : List (List Tree × List Term)} (hΓs : childCtxs G n l ts Γ Φ = some Γs) :
    Γs.length = ts.length := by
  unfold childCtxs at hΓs
  split at hΓs
  · cases hΓs
    rfl
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hΓs
    obtain ⟨_, -, rfl⟩ := hΓs
    rfl
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hΓs
    obtain ⟨_, -, _, -, rfl⟩ := hΓs
    rfl
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hΓs
    obtain ⟨_, -, rfl⟩ := hΓs
    rfl
  · cases hΓs
    exact List.length_map _

/-- The contexts {lit}`childCtxs` gives the children in the node's context are the node's. -/
theorem childCtxs_sameCtx {G : Globals} {n : ℕ} {l : Label} {ts : List Term} {Γ : List Tree}
    {Φ : List Term} {Γs : List (List Tree × List Term)} (hΓs : childCtxs G n l ts Γ Φ = some Γs)
    {i : ℕ} {p : List Tree × List Term} (hp : Γs[i]? = some p) (hi : sameCtx l i = true) :
    p = (Γ, Φ) := by
  unfold childCtxs at hΓs
  split at hΓs
  · simp [sameCtx] at hi
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hΓs
    obtain ⟨_, -, rfl⟩ := hΓs
    obtain rfl : i = 2 := by simpa [sameCtx] using hi
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp
    exact hp.symm
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hΓs
    obtain ⟨_, -, _, -, rfl⟩ := hΓs
    obtain rfl : i = 2 := by simpa [sameCtx] using hi
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp
    exact hp.symm
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hΓs
    obtain ⟨_, -, rfl⟩ := hΓs
    obtain rfl : i = 1 := by simpa [sameCtx] using hi
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hp
    exact hp.symm
  · cases hΓs
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hp
    obtain ⟨_, -, rfl⟩ := hp
    rfl

variable (hM : IsModel (ext defs) M) {G : Globals} (hG : G.WF) {n : ℕ}
  (hρ : ρ.map Sigma.fst = List.replicate n obj) (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n)
include hM hG hρ hps hds

/-- A term that compiles in an environment of arrows compiles in every environment of the values
of the first's after an arrow, to its arrow after the arrow. -/
theorem compile_precomp {s : Term} {Y X h : Tree} {e e' : List (Tree × Tree)} {r : Tree × Tree}
    (hs : compile G n s Y e = some r) (he : EnvHom M ρ G n Y e) (hh : Hom M ρ h X Y)
    (he' : EnvEq M ρ (precomp h e) e') :
    ∃ r', compile G n s X e' = some r' ∧ ResEq M ρ (comp r.1 h, r.2) r' := by
  obtain ⟨r₁, h₁, hr₁⟩ := compile_comp hM hG hρ hps hds s Y e r hs he X h hh
  obtain ⟨r₂, h₂, hr₂⟩ := compile_envEq s X _ r₁ h₁ e' he'
  exact ⟨r₂, h₂, hr₁.trans hr₂⟩

/-- A term that compiles in a context's environment of projections compiles in every environment
of arrows of the context's types, to its arrow after their tuple. -/
theorem compile_of_stdEnv {Γ : List Tree} {s : Term} {r : Tree × Tree}
    (h : compile G n s (ctxObj Γ) (stdEnv Γ) = some r) {X : Tree} {e : List (Tree × Tree)}
    (he : EnvHom M ρ G n X e) (hΓ : e.map Prod.snd = Γ) :
    ∃ r', compile G n s X e = some r' ∧
      ResEq M ρ (comp r.1 (tuple X (e.map Prod.fst)), r.2) r' := by
  subst hΓ
  have hΓ : (e.map Prod.snd).all (IsTy G n) = true := by
    rw [List.all_map, List.all_eq_true]
    exact fun p hp ↦ (he.2 p hp).2
  exact compile_precomp hM hG hρ hps hds h (stdEnv_hom hM hds.2 hρ _ hΓ)
    (tuple_hom hM he.1 e fun p hp ↦ (he.2 p hp).1) (proj_tuple hM hds.2 hρ he.1 e he.2)

/-- A term in the environment extended by a variable of a type, at an element of the type, is its
arrow there after the pairing of the identity with the element. -/
theorem compile_at {X x W B C : Tree} {e : List (Tree × Tree)} {w : Term}
    (he : EnvHom M ρ G n X e) (hB : IsTy G n B = true)
    (hw : compile G n w (prod X B) (extEnv X B e) = some (W, C)) (hx : Hom M ρ x X B) :
    ∃ q, compile G n w X ((x, B) :: e) = some q ∧ ResEq M ρ (comp W (pair (idt X) x), C) q := by
  have hBo := isObj_of_isTy hM hds.2 hρ B hB
  have hi := idt_hom hM he.1
  exact compile_precomp hM hG hρ hps hds hw (he.ext hM hBo hB) (pair_hom hM hi hx)
    (envEq_precomp_extEnv hM he.1 hBo (fun p hp ↦ (he.2 p hp).1) (pair_hom hM hi hx)
      (fst_pair hM hi hx) (snd_pair hM hi hx) (envEq_precomp_idt hM fun p hp ↦ (he.2 p hp).1))

/-- A term that compiles in the empty environment compiles in every environment of arrows, to its
arrow after the arrow to the terminal object. -/
theorem compile_closed {s : Term} {r : Tree × Tree} (h : compile G n s one [] = some r)
    {X : Tree} {e : List (Tree × Tree)} (he : EnvHom M ρ G n X e) :
    ∃ r', compile G n s X e = some r' ∧ ResEq M ρ (comp r.1 (bang X), r.2) r' :=
  compile_precomp hM hG hρ hps hds h ⟨isObj_one hM, by simp⟩ (bang_hom hM he.1)
    fun i p hp ↦ by simp [precomp] at hp

/-- β is sound: the application of an abstraction is its body with the argument substituted. -/
theorem beta_sound {Φ : List Term} (Γ : List Tree) (a : Tree) (b u : Term) :
    RwSound M ρ G n Γ Φ (Term.app (Term.lam a b) u) (Term.subst b (instVar u)) := by
  intro X e he _ _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨f, u', hfu, F, A, B, hf, g, hu, rfl⟩ := compile_app_iff.mp h
  simp only [List.cons.injEq, and_true] at hfu
  obtain ⟨rfl, rfl⟩ := hfu
  obtain ⟨b', T, B', hb', hat, hb, hFT⟩ := compile_lam_iff.mp hf
  simp only [List.cons.injEq, and_true] at hb'
  subst hb'
  simp only [Prod.mk.injEq] at hFT
  obtain ⟨rfl, hAB⟩ := hFT
  obtain ⟨rfl, rfl⟩ := exp_inj hAB
  have hA := isObj_of_isTy hM hds.2 hρ a hat
  have hT := (hty b _ _ _ hb (he.ext hM hA hat)).1
  have hg := (hty u X e _ hu he).1
  have hi := idt_hom hM he.1
  obtain ⟨r₁, h₁, hr₁⟩ := compile_precomp hM hG hρ hps hds hb (he.ext hM hA hat)
    (pair_hom hM hi hg) (envEq_precomp_extEnv hM he.1 hA (fun p hp ↦ (he.2 p hp).1)
      (pair_hom hM hi hg) (fst_pair hM hi hg) (snd_pair hM hi hg)
      (envEq_precomp_idt hM fun p hp ↦ (he.2 p hp).1))
  obtain ⟨r₂, h₂, hr₂⟩ := compile_subst hM hG hρ hps hds b X ((g, a) :: e) r₁ h₁ e (instVar u) he
    fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (g, a) = p := by simpa using hp
        exact ⟨(g, a), hu, ResEq.refl _⟩
      · exact ⟨p, compile_var_iff.mpr ⟨rfl, by simpa using hp⟩, ResEq.refl p⟩
  exact ⟨r₂, h₂, (show ResEq M ρ (comp (ev a B') (pair (curry X a T) g), B')
      (comp T (pair (idt X) g), B') from
    ⟨rfl, (ev_pair_curry hM he.1 hA hT hg).symm⟩).trans (hr₁.trans hr₂)⟩

/-- The first component of a pair is its first term. -/
theorem fstPair_sound {Φ : List Term} (Γ : List Tree) (a b : Term) :
    RwSound M ρ G n Γ Φ (Term.fst (Term.pair a b)) a := by
  intro X e he _ _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨p, f, A, B, hp, hc, rfl⟩ := compile_fst_iff.mp h
  simp only [List.cons.injEq, and_true] at hp
  subst hp
  obtain ⟨a', b', fa, A', fb, B', hab, ha, hb, hpair⟩ := compile_pair_iff.mp hc
  simp only [List.cons.injEq, and_true] at hab
  obtain ⟨rfl, rfl⟩ := hab
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨rfl, hAB⟩ := hpair
  obtain ⟨rfl, rfl⟩ := prod_inj hAB
  exact ⟨_, ha, rfl, (fst_pair hM (hty _ _ _ _ ha he).1 (hty _ _ _ _ hb he).1).symm⟩

/-- The second component of a pair is its second term. -/
theorem sndPair_sound {Φ : List Term} (Γ : List Tree) (a b : Term) :
    RwSound M ρ G n Γ Φ (Term.snd (Term.pair a b)) b := by
  intro X e he _ _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨p, f, A, B, hp, hc, rfl⟩ := compile_snd_iff.mp h
  simp only [List.cons.injEq, and_true] at hp
  subst hp
  obtain ⟨a', b', fa, A', fb, B', hab, ha, hb, hpair⟩ := compile_pair_iff.mp hc
  simp only [List.cons.injEq, and_true] at hab
  obtain ⟨rfl, rfl⟩ := hab
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨rfl, hAB⟩ := hpair
  obtain ⟨rfl, rfl⟩ := prod_inj hAB
  exact ⟨_, hb, rfl, (snd_pair hM (hty _ _ _ _ ha he).1 (hty _ _ _ _ hb he).1).symm⟩

/-- The pair of a term's components is the term. -/
theorem pairEta_sound {Φ : List Term} (Γ : List Tree) (p : Term) :
    RwSound M ρ G n Γ Φ (Term.pair (Term.fst p) (Term.snd p)) p := by
  intro X e he _ _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨x, y, f₁, A, f₂, B, hxy, hx, hy, rfl⟩ := compile_pair_iff.mp h
  simp only [List.cons.injEq, and_true] at hxy
  obtain ⟨rfl, rfl⟩ := hxy
  obtain ⟨p₁, f, A₁, B₁, hp₁, hf, hr₁⟩ := compile_fst_iff.mp hx
  obtain ⟨p₂, f', A₂, B₂, hp₂, hf', hr₂⟩ := compile_snd_iff.mp hy
  simp only [List.cons.injEq, and_true] at hp₁ hp₂
  subst hp₁ hp₂
  rw [hf] at hf'
  simp only [Option.some.injEq, Prod.mk.injEq] at hf' hr₁ hr₂
  obtain ⟨rfl, hAB⟩ := hf'
  obtain ⟨rfl, rfl⟩ := prod_inj hAB
  obtain ⟨rfl, rfl⟩ := hr₁
  obtain ⟨rfl, rfl⟩ := hr₂
  obtain ⟨hfh, hPt⟩ := hty _ _ _ _ hf he
  simp only [isTy_prod, Bool.and_eq_true] at hPt
  exact ⟨_, hf, rfl, (pair_eta hM (isObj_of_isTy hM hds.2 hρ _ hPt.1)
    (isObj_of_isTy hM hds.2 hρ _ hPt.2) hfh).symm⟩

/-- A term of the terminal type is its element. -/
theorem unitEta_sound {Φ : List Term} {Γ : List Tree} {t : Term} (h₁ : typeIn G n Γ t = some one) :
    RwSound M ρ G n Γ Φ t Term.star := by
  intro X e he hΓ _ r h
  obtain ⟨⟨f₀, A₀⟩, hstd, rfl⟩ := Option.map_eq_some_iff.mp h₁
  obtain ⟨f, hf⟩ := compile_retype t _ _ _ hstd X e (hΓ.trans (map_snd_stdEnv Γ).symm)
  obtain rfl := Option.some_inj.mp (h.symm.trans hf)
  exact ⟨_, compile_star_iff.mpr ⟨rfl, rfl⟩, rfl,
    (bang_unique hM (compile_hom hM hG hρ hps hds t X e _ hf he).1).symm⟩

/-- The unfolding of a definition is sound: its application is its body at the objects and the
arguments. -/
theorem delta_sound {Φ : List Term} (hδ : DefnsOk M G) {k : ℕ} {d : Defn}
    (hd : G.defs[k]? = some (.language d))
    (Γ θ : List Tree) (args : List Term) :
    RwSound M ρ G n Γ Φ (Term.defn k θ args)
      (Term.subst (Term.osubst θ d.body) (Term.substList args)) := by
  intro X e he _ _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨d', rs, hd', hrs, hl, hθ, hsnd, rfl⟩ := compile_defn_iff.mp h
  obtain rfl : d' = d := Definition.language.inj (Option.some_inj.mp (hd'.symm.trans hd))
  obtain ⟨F, hF, hop⟩ := hδ k d' hd
  have hF' := compile_osubst hG hl hθ d'.body _ _ _ hF
  rw [subst_ctxObj, map_substPair_stdEnv] at hF'
  have hrs' : EnvHom M ρ G n X rs := ⟨he.1, fun q hq ↦ by
    obtain ⟨c, -, hcq⟩ := exists_of_mapM hrs hq
    exact hty c X e q hcq he⟩
  obtain ⟨r₁, h₁, hr₁⟩ := compile_of_stdEnv hM hG hρ hps hds hF' hrs' hsnd
  obtain ⟨r₂, h₂, hr₂⟩ := compile_subst hM hG hρ hps hds _ X rs r₁ h₁ e (Term.substList args) he
    fun i p hp ↦ by
      obtain ⟨c, hc, hcp⟩ := getElem?_of_mapM_eq hrs hp
      exact ⟨p, by simpa [Term.substList, hc] using hcp, ResEq.refl p⟩
  exact ⟨r₂, h₂, (show ResEq M ρ
      (comp (op (G.base + k) θ) (tuple X (rs.map Prod.fst)), PartialHorn.subst θ d'.type)
      (comp (PartialHorn.subst θ F) (tuple X (rs.map Prod.fst)), PartialHorn.subst θ d'.type) from
    ⟨rfl, eval_op₂_congr 3 (hop n ρ θ hρ hl hθ).symm rfl⟩).trans (hr₁.trans hr₂)⟩

/-- The fold of zero is the start. -/
theorem natZero_sound {Φ : List Term} {kz : ℕ} (hk : G.prims[kz]? = some zeroPrim) (Γ : List Tree)
    (z s : Term) : RwSound M ρ G n Γ Φ (Term.natRec z s (Term.arr kz [] Term.star)) z := by
  intro X e he _ _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨z₁, s₁, m, hcs, z', C, hzc, s', hsc, m', hm, rfl⟩ := compile_natRec_iff.mp h
  simp only [List.cons.injEq, and_true] at hcs
  obtain ⟨rfl, rfl, rfl⟩ := hcs
  obtain ⟨t₀, ht₀, p, hp, g, hg, -, -, hm'⟩ := compile_arr_iff.mp hm
  simp only [List.cons.injEq, and_true] at ht₀
  subst ht₀
  obtain rfl : p = zeroPrim := Option.some_inj.mp (hp.symm.trans hk)
  obtain ⟨-, hgb⟩ := compile_star_iff.mp hg
  simp only [Prod.mk.injEq] at hgb hm'
  obtain ⟨rfl, -⟩ := hgb
  obtain ⟨rfl, -⟩ := hm'
  obtain ⟨hz', hCt⟩ := hty _ _ _ _ hzc ⟨isObj_one hM, by simp⟩
  have hC := isObj_of_isTy hM hds.2 hρ C hCt
  have hs' := (hty _ _ _ _ hsc ⟨hC, by simpa using ⟨idt_hom hM hC, hCt⟩⟩).1
  obtain ⟨r', h', hr'⟩ := compile_closed hM hG hρ hps hds hzc he
  refine ⟨r', h', (show ResEq M ρ
      (comp (natRec z' s') (comp (PartialHorn.subst [] zeroN) (bang X)), C)
      (comp z' (bang X), C) from ⟨rfl, ?_⟩).trans hr'⟩
  rw [show PartialHorn.subst [] zeroN = zeroN from subst_const [] 30]
  exact (eval_op₂_congr 3 (natRec_zero hM hz' hs') rfl).symm.trans
    (comp_assoc hM (bang_hom hM he.1) (zeroN_hom hM) (natRec_hom hM hz' hs')).symm

/-- The fold of a successor is the step at the fold. -/
theorem natSucc_sound {Φ : List Term} {ks : ℕ} (hk : G.prims[ks]? = some succPrim) (Γ : List Tree)
    (z s c : Term) :
    RwSound M ρ G n Γ Φ (Term.natRec z s (Term.arr ks [] c))
      (Term.subst s (instVar (Term.natRec z s c))) := by
  intro X e he _ _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨z₁, s₁, m, hcs, z', C, hzc, s', hsc, m', hm, rfl⟩ := compile_natRec_iff.mp h
  simp only [List.cons.injEq, and_true] at hcs
  obtain ⟨rfl, rfl, rfl⟩ := hcs
  obtain ⟨t₀, ht₀, p, hp, g, hg, -, -, hm'⟩ := compile_arr_iff.mp hm
  simp only [List.cons.injEq, and_true] at ht₀
  subst ht₀
  obtain rfl : p = succPrim := Option.some_inj.mp (hp.symm.trans hk)
  simp only [Prod.mk.injEq] at hm'
  obtain ⟨rfl, -⟩ := hm'
  rw [show PartialHorn.subst [] succPrim.dom = nat from subst_nat []] at hg
  obtain ⟨hz', hCt⟩ := hty _ _ _ _ hzc ⟨isObj_one hM, by simp⟩
  have hC := isObj_of_isTy hM hds.2 hρ C hCt
  have hCe : EnvHom M ρ G n C [(idt C, C)] := ⟨hC, by simpa using ⟨idt_hom hM hC, hCt⟩⟩
  have hs' := (hty _ _ _ _ hsc hCe).1
  have hg' := (hty _ _ _ _ hg he).1
  have hrec := natRec_hom hM hz' hs'
  have hq := comp_hom hM hg' hrec
  have hN : compile G n (Term.natRec z s c) X e = some (comp (natRec z' s') g, C) :=
    compile_natRec_iff.mpr ⟨z, s, c, rfl, z', C, hzc, s', hsc, g, hg, rfl⟩
  obtain ⟨r₁, h₁, hr₁⟩ := compile_precomp hM hG hρ hps hds hsc hCe hq
    (e' := [(comp (natRec z' s') g, C)]) fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (comp (idt C) (comp (natRec z' s') g), C) = p := by
          simpa [precomp] using hp
        exact ⟨_, rfl, rfl, (idt_comp hM hq).symm⟩
      · simp [precomp] at hp
  obtain ⟨r₂, h₂, hr₂⟩ := compile_subst hM hG hρ hps hds s X _ r₁ h₁ e
    (instVar (Term.natRec z s c)) he fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (comp (natRec z' s') g, C) = p := by simpa using hp
        exact ⟨_, hN, ResEq.refl _⟩
      · simp at hp
  refine ⟨r₂, h₂, (show ResEq M ρ
      (comp (natRec z' s') (comp (PartialHorn.subst [] succ) g), C)
      (comp s' (comp (natRec z' s') g), C) from ⟨rfl, ?_⟩).trans (hr₁.trans hr₂)⟩
  rw [show PartialHorn.subst [] succ = succ from subst_const [] 31]
  exact Eq.symm ((comp_assoc hM hg' (succ_hom hM) hrec).trans
    ((eval_op₂_congr 3 (natRec_succ hM hz' hs') rfl).trans (comp_assoc hM hg' hrec hs').symm))

/-- The fold of the empty list is the start. -/
theorem listNil_sound {Φ : List Term} {kn : ℕ} (hk : G.prims[kn]? = some nilPrim) (Γ : List Tree)
    (z s : Term) (a₀ : Tree) :
    RwSound M ρ G n Γ Φ (Term.listRec z s (Term.arr kn [a₀] Term.star)) z := by
  intro X e he _ _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨z₁, s₁, m, hcs, m', A, hm, z', C, hzc, s', hsc, rfl⟩ := compile_listRec_iff.mp h
  simp only [List.cons.injEq, and_true] at hcs
  obtain ⟨rfl, rfl, rfl⟩ := hcs
  obtain ⟨hmh, hLt⟩ := hty _ _ _ _ hm he
  rw [isTy_list] at hLt
  obtain ⟨t₀, ht₀, p, hp, g, hg, -, -, hm'⟩ := compile_arr_iff.mp hm
  simp only [List.cons.injEq, and_true] at ht₀
  subst ht₀
  obtain rfl : p = nilPrim := Option.some_inj.mp (hp.symm.trans hk)
  obtain ⟨-, hgb⟩ := compile_star_iff.mp hg
  simp only [Prod.mk.injEq] at hgb hm'
  obtain ⟨rfl, -⟩ := hgb
  obtain ⟨rfl, hA⟩ := hm'
  obtain rfl : a₀ = A := list_inj ((subst_list_x a₀).symm.trans hA)
  have hA := isObj_of_isTy hM hds.2 hρ a₀ hLt
  obtain ⟨hz', hCt⟩ := hty _ _ _ _ hzc ⟨isObj_one hM, by simp⟩
  have hC := isObj_of_isTy hM hds.2 hρ C hCt
  have hs' := (hty _ _ _ _ hsc ⟨isObj_prod hM hA hC, by
    simpa using ⟨⟨snd_hom hM hA hC, hCt⟩, fst_hom hM hA hC, hLt⟩⟩).1
  obtain ⟨r', h', hr'⟩ := compile_closed hM hG hρ hps hds hzc he
  refine ⟨r', h', (show ResEq M ρ
      (comp (listRec a₀ z' s') (comp (PartialHorn.subst [a₀] (nil (x 0))) (bang X)), C)
      (comp z' (bang X), C) from ⟨rfl, ?_⟩).trans hr'⟩
  rw [subst_nil_x]
  exact (eval_op₂_congr 3 (listRec_nil hM hA hz' hs') rfl).symm.trans
    (comp_assoc hM (bang_hom hM he.1) (nil_hom hM hA) (listRec_hom hM hA hz' hs')).symm

/-- The fold of a construction is the step at the element and the fold of the tail. -/
theorem listCons_sound {Φ : List Term} {kc : ℕ} (hk : G.prims[kc]? = some consPrim) (Γ : List Tree)
    (z s : Term) (a₀ : Tree) (hd tl : Term) :
    RwSound M ρ G n Γ Φ (Term.listRec z s (Term.arr kc [a₀] (Term.pair hd tl)))
      (Term.subst s (Term.substList [Term.listRec z s tl, hd])) := by
  intro X e he _ _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨z₁, s₁, m, hcs, m', A, hm, z', C, hzc, s', hsc, rfl⟩ := compile_listRec_iff.mp h
  simp only [List.cons.injEq, and_true] at hcs
  obtain ⟨rfl, rfl, rfl⟩ := hcs
  obtain ⟨-, hLt⟩ := hty _ _ _ _ hm he
  rw [isTy_list] at hLt
  obtain ⟨t₀, ht₀, p, hp, g, hg, -, -, hm'⟩ := compile_arr_iff.mp hm
  simp only [List.cons.injEq, and_true] at ht₀
  subst ht₀
  obtain rfl : p = consPrim := Option.some_inj.mp (hp.symm.trans hk)
  simp only [Prod.mk.injEq] at hm'
  obtain ⟨rfl, hA⟩ := hm'
  obtain rfl : a₀ = A := list_inj ((subst_list_x a₀).symm.trans hA)
  rw [show PartialHorn.subst [a₀] consPrim.dom = prod a₀ (list a₀) from subst_prod_list_x a₀]
    at hg
  obtain ⟨hd', tl', gh, A₁, gt, B₁, hht, hh, htl, hgp⟩ := compile_pair_iff.mp hg
  simp only [List.cons.injEq, and_true] at hht
  obtain ⟨rfl, rfl⟩ := hht
  simp only [Prod.mk.injEq] at hgp
  obtain ⟨rfl, hAB⟩ := hgp
  obtain ⟨rfl, rfl⟩ := prod_inj hAB
  have hA := isObj_of_isTy hM hds.2 hρ A₁ hLt
  obtain ⟨hz', hCt⟩ := hty _ _ _ _ hzc ⟨isObj_one hM, by simp⟩
  have hC := isObj_of_isTy hM hds.2 hρ C hCt
  have hse : EnvHom M ρ G n (prod A₁ C) [(snd A₁ C, C), (fst A₁ C, A₁)] :=
    ⟨isObj_prod hM hA hC, by simpa using ⟨⟨snd_hom hM hA hC, hCt⟩, fst_hom hM hA hC, hLt⟩⟩
  have hs' := (hty _ _ _ _ hsc hse).1
  have hgh := (hty _ _ _ _ hh he).1
  have hgt := (hty _ _ _ _ htl he).1
  have hlr := listRec_hom hM hA hz' hs'
  have hq := comp_hom hM hgt hlr
  have hk' := pair_hom hM hgh hq
  have hL : compile G n (Term.listRec z s tl) X e = some (comp (listRec A₁ z' s') gt, C) :=
    compile_listRec_iff.mpr ⟨z, s, tl, rfl, gt, A₁, htl, z', C, hzc, s', hsc, rfl⟩
  obtain ⟨r₁, h₁, hr₁⟩ := compile_precomp hM hG hρ hps hds hsc hse hk'
    (e' := [(comp (listRec A₁ z' s') gt, C), (gh, A₁)]) fun i p hp ↦ by
      rcases i with _ | _ | j
      · obtain rfl : (comp (snd A₁ C) (pair gh (comp (listRec A₁ z' s') gt)), C) = p := by
          simpa [precomp] using hp
        exact ⟨_, rfl, rfl, (snd_pair hM hgh hq).symm⟩
      · obtain rfl : (comp (fst A₁ C) (pair gh (comp (listRec A₁ z' s') gt)), A₁) = p := by
          simpa [precomp] using hp
        exact ⟨_, rfl, rfl, (fst_pair hM hgh hq).symm⟩
      · simp [precomp] at hp
  obtain ⟨r₂, h₂, hr₂⟩ := compile_subst hM hG hρ hps hds s X _ r₁ h₁ e
    (Term.substList [Term.listRec z s tl, hd]) he fun i p hp ↦ by
      rcases i with _ | _ | j
      · obtain rfl : (comp (listRec A₁ z' s') gt, C) = p := by simpa using hp
        exact ⟨_, by simpa [Term.substList] using hL, ResEq.refl _⟩
      · obtain rfl : (gh, A₁) = p := by simpa using hp
        exact ⟨_, by simpa [Term.substList] using hh, ResEq.refl _⟩
      · simp at hp
  refine ⟨r₂, h₂, (show ResEq M ρ
      (comp (listRec A₁ z' s') (comp (PartialHorn.subst [A₁] (cons (x 0))) (pair gh gt)), C)
      (comp s' (pair gh (comp (listRec A₁ z' s') gt)), C) from ⟨rfl, ?_⟩).trans
    (hr₁.trans hr₂)⟩
  rw [subst_cons_x]
  have hL' := isObj_list hM hA
  have hpg := pair_hom hM hgh hgt
  have hpm := pair_hom hM (fst_hom hM hA hL') (comp_hom hM (snd_hom hM hA hL') hlr)
  refine Eq.symm ((comp_assoc hM hpg (cons_hom hM hA) hlr).trans
    ((eval_op₂_congr 3 (listRec_cons hM hA hz' hs') rfl).trans
      ((comp_assoc hM hpg hpm hs').symm.trans (eval_op₂_congr 3 rfl ?_))))
  exact (pair_comp hM (fst_hom hM hA hL') (comp_hom hM (snd_hom hM hA hL') hlr) hpg).trans
    (eval_op₂_congr 9 (fst_pair hM hgh hgt) ((comp_assoc hM hpg (snd_hom hM hA hL') hlr).symm.trans
      (eval_op₂_congr 3 rfl (snd_pair hM hgh hgt))))

/-- The case analysis of a pair of functions at a left injection is the first function at the
injected term. -/
theorem caseInl_sound {Φ : List Term} {kc kl : ℕ} (hkc : G.prims[kc]? = some casePrim)
    (hkl : G.prims[kl]? = some inlPrim) (Γ θ θ' : List Tree) (f g v : Term) :
    RwSound M ρ G n Γ Φ (Term.app (Term.arr kc θ (Term.pair f g)) (Term.arr kl θ' v))
      (Term.app f v) := by
  intro X e he _ _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨t, u, hcs, F, D, C, ht, U, hu, rfl⟩ := compile_app_iff.mp h
  simp only [List.cons.injEq, and_true] at hcs
  obtain ⟨rfl, rfl⟩ := hcs
  obtain ⟨t₀, ht₀, p, hp, P, hP, hl, hθ, hF⟩ := compile_arr_iff.mp ht
  simp only [List.cons.injEq, and_true] at ht₀
  subst ht₀
  obtain rfl : p = casePrim := Option.some_inj.mp (hp.symm.trans hkc)
  obtain ⟨u₀, hu₀, q, hq, V, hV, hl', -, hU⟩ := compile_arr_iff.mp hu
  simp only [List.cons.injEq, and_true] at hu₀
  subst hu₀
  obtain rfl : q = inlPrim := Option.some_inj.mp (hq.symm.trans hkl)
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hl
  obtain ⟨a', b', rfl⟩ := List.length_eq_two.mp hl'
  simp only [Prod.mk.injEq] at hF hU
  obtain ⟨rfl, hFt⟩ := hF
  obtain ⟨rfl, hUt⟩ := hU
  obtain ⟨hD, hC⟩ := exp_inj (show exp (coprod a b) c = exp D C from hFt)
  subst hD hC
  obtain ⟨ha, hb⟩ := coprod_inj (show coprod a' b' = coprod a b from hUt)
  subst ha hb
  obtain ⟨f₁, g₁, Pf, A₁, Pg, B₁, hfg, hf, hg, hPe⟩ :=
    compile_pair_iff.mp (show compile G n (Term.pair f g) X e =
      some (P, prod (exp a' c) (exp b' c)) from hP)
  simp only [List.cons.injEq, and_true] at hfg
  obtain ⟨rfl, rfl⟩ := hfg
  simp only [Prod.mk.injEq] at hPe
  obtain ⟨rfl, hAB⟩ := hPe
  obtain ⟨rfl, rfl⟩ := prod_inj hAB
  have hV₁ : compile G n v X e = some (V, a') := hV
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hθ
  have hf' := (hty _ _ _ _ hf he).1
  have hV' := (hty _ _ _ _ hV₁ he).1
  have hPh := pair_hom hM hf' (hty _ _ _ _ hg he).1
  refine ⟨_, compile_app_iff.mpr ⟨f, v, rfl, Pf, a', c, hf, V, hV₁, rfl⟩, rfl, ?_⟩
  change eval M ρ (comp (ev a' c) (pair Pf V)) = eval M ρ (comp (ev (coprod a' b') c)
    (pair (comp (caseArr a' b' c) (pair Pf Pg)) (comp (inl a' b') V)))
  exact ((caseArr_inl hM (isObj_of_isTy hM hds.2 hρ b' hθ.2.1)
    (isObj_of_isTy hM hds.2 hρ c hθ.2.2) hPh hV').trans (eval_op₂_congr 3 rfl (eval_op₂_congr 9
      (fst_pair hM hf' (hty _ _ _ _ hg he).1) rfl))).symm

/-- The case analysis of a pair of functions at a right injection is the second function at the
injected term. -/
theorem caseInr_sound {Φ : List Term} {kc kr : ℕ} (hkc : G.prims[kc]? = some casePrim)
    (hkr : G.prims[kr]? = some inrPrim) (Γ θ θ' : List Tree) (f g v : Term) :
    RwSound M ρ G n Γ Φ (Term.app (Term.arr kc θ (Term.pair f g)) (Term.arr kr θ' v))
      (Term.app g v) := by
  intro X e he _ _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨t, u, hcs, F, D, C, ht, U, hu, rfl⟩ := compile_app_iff.mp h
  simp only [List.cons.injEq, and_true] at hcs
  obtain ⟨rfl, rfl⟩ := hcs
  obtain ⟨t₀, ht₀, p, hp, P, hP, hl, hθ, hF⟩ := compile_arr_iff.mp ht
  simp only [List.cons.injEq, and_true] at ht₀
  subst ht₀
  obtain rfl : p = casePrim := Option.some_inj.mp (hp.symm.trans hkc)
  obtain ⟨u₀, hu₀, q, hq, V, hV, hl', -, hU⟩ := compile_arr_iff.mp hu
  simp only [List.cons.injEq, and_true] at hu₀
  subst hu₀
  obtain rfl : q = inrPrim := Option.some_inj.mp (hq.symm.trans hkr)
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hl
  obtain ⟨a', b', rfl⟩ := List.length_eq_two.mp hl'
  simp only [Prod.mk.injEq] at hF hU
  obtain ⟨rfl, hFt⟩ := hF
  obtain ⟨rfl, hUt⟩ := hU
  obtain ⟨hD, hC⟩ := exp_inj (show exp (coprod a b) c = exp D C from hFt)
  subst hD hC
  obtain ⟨ha, hb⟩ := coprod_inj (show coprod a' b' = coprod a b from hUt)
  subst ha hb
  obtain ⟨f₁, g₁, Pf, A₁, Pg, B₁, hfg, hf, hg, hPe⟩ :=
    compile_pair_iff.mp (show compile G n (Term.pair f g) X e =
      some (P, prod (exp a' c) (exp b' c)) from hP)
  simp only [List.cons.injEq, and_true] at hfg
  obtain ⟨rfl, rfl⟩ := hfg
  simp only [Prod.mk.injEq] at hPe
  obtain ⟨rfl, hAB⟩ := hPe
  obtain ⟨rfl, rfl⟩ := prod_inj hAB
  have hV₁ : compile G n v X e = some (V, b') := hV
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hθ
  have hg' := (hty _ _ _ _ hg he).1
  have hV' := (hty _ _ _ _ hV₁ he).1
  have hPh := pair_hom hM (hty _ _ _ _ hf he).1 hg'
  refine ⟨_, compile_app_iff.mpr ⟨g, v, rfl, Pg, b', c, hg, V, hV₁, rfl⟩, rfl, ?_⟩
  change eval M ρ (comp (ev b' c) (pair Pg V)) = eval M ρ (comp (ev (coprod a' b') c)
    (pair (comp (caseArr a' b' c) (pair Pf Pg)) (comp (inr a' b') V)))
  exact ((caseArr_inr hM (isObj_of_isTy hM hds.2 hρ a' hθ.1)
    (isObj_of_isTy hM hds.2 hρ c hθ.2.2) hPh hV').trans (eval_op₂_congr 3 rfl (eval_op₂_congr 9
      (snd_pair hM (hty _ _ _ _ hf he).1 hg') rfl))).symm

omit hG hps in
/-- The primitive arrow of a rose tree's construction, at its objects, is an arrow from the
product of the object's type of labels and the list object of the rose-tree object it constructs,
after which the fold of that object is the step after the product of the labels with the fold's
action on the children. -/
theorem roseNode_prim {kn : ℕ} {p : Prim} (hp : G.prims[kn]? = some p)
    (hkn : G.prims[kn]? = some nodePrim ∨ G.prims[kn]? = some lnodePrim) {θ : List Tree}
    (hl : θ.length = p.arity) (hθ : θ.all (IsTy G n) = true) {a c : Tree} {F : Tree → Tree}
    (ht : roseParts (PartialHorn.subst θ p.cod) = some (a, F)) :
    PartialHorn.subst θ p.dom = prod a (list (PartialHorn.subst θ p.cod)) ∧
      Hom M ρ (PartialHorn.subst θ p.arrow) (prod a (list (PartialHorn.subst θ p.cod)))
        (PartialHorn.subst θ p.cod) ∧
      ∀ {S}, Hom M ρ S (prod a (list c)) c → eval M ρ (comp (F S) (PartialHorn.subst θ p.arrow)) =
        eval M ρ (comp S (prodMapRight a (listMap (F S)))) := by
  rcases hkn with hkn | hkn <;> obtain rfl := Option.some_inj.mp (hp.symm.trans hkn)
  · obtain rfl := List.length_eq_zero_iff.mp hl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp
      ((show roseParts rose = some (nat, roseRec) by simp [roseParts]).symm.trans ht))
    exact ⟨rfl, node_hom hM, fun hS ↦ roseRec_node hM hS⟩
  · obtain ⟨a', rfl⟩ := List.length_eq_one_iff.mp hl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp ((roseParts_lrose a').symm.trans ht))
    have hA : IsObj M ρ a' := isObj_of_isTy hM hds.2 hρ a' (by simpa using hθ)
    exact ⟨rfl, lnode_hom hM hA, fun hS ↦ lroseRec_node hM hA hS⟩

omit hM hG hρ hps hds in
/-- The list of the folds of the children of a rose tree, by the fold of a list whose step is
the construction of the fold at the element onto the list folded, compiles to the fold's action
on the children after the children's arrow. -/
theorem compile_roseMap {kl kc : ℕ} (hkl : G.prims[kl]? = some nilPrim)
    (hkc : G.prims[kc]? = some consPrim) {c t a S CS : Tree} {F : Tree → Tree}
    {X : Tree} {e : List (Tree × Tree)} {s cs : Term} (hct : IsTy G n c = true)
    (ht : roseParts t = some (a, F))
    (hs : compile G n s (prod a (list c)) [(idt (prod a (list c)), prod a (list c))] =
      some (S, c))
    (hcs : compile G n cs X e = some (CS, list t)) :
    compile G n (Term.listRec (Term.arr kl [c] Term.star)
      (Term.arr kc [c] (Term.pair (Term.roseRec c s (Term.var 1)) (Term.var 0))) cs) X e =
      some (comp (listRec t (comp (nil c) (bang one))
        (comp (cons c) (pair (comp (F S) (fst t (list c))) (snd t (list c))))) CS, list c) :=
  compile_listRec_iff.mpr ⟨_, _, _, rfl, CS, t, hcs, _, _, compile_nilT hkl hct one [], _,
    compile_consT hkc hct (compile_pair_iff.mpr ⟨_, _, _, _, _, _, rfl,
      compile_roseRec_iff.mpr ⟨s, Term.var 1, fst t (list c), t, a, F, S, rfl, hct,
        compile_var_iff.mpr ⟨rfl, rfl⟩, ht, hs, rfl⟩,
      compile_var_iff.mpr ⟨rfl, rfl⟩, rfl⟩), rfl⟩

/-- The fold of a rose tree's construction is the step at the pair of the label and the list of
the folds of the children. -/
theorem roseNode_sound {Φ : List Term} {kn kl kc : ℕ}
    (hkn : G.prims[kn]? = some nodePrim ∨ G.prims[kn]? = some lnodePrim)
    (hkl : G.prims[kl]? = some nilPrim) (hkc : G.prims[kc]? = some consPrim) (Γ : List Tree)
    (c : Tree) (θ : List Tree) (s l cs : Term) :
    RwSound M ρ G n Γ Φ (Term.roseRec c s (Term.arr kn θ (Term.pair l cs)))
      (Term.subst s (instVar (Term.pair l (Term.listRec (Term.arr kl [c] Term.star)
        (Term.arr kc [c] (Term.pair (Term.roseRec c s (Term.var 1)) (Term.var 0))) cs)))) := by
  intro X e he _ _ r h
  have hty := compile_hom hM hG hρ hps hds
  have hobj := isObj_of_isTy hM hds.2 hρ
  obtain ⟨s₁, m, m', t, a, F, S, hcs, hct, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp h
  simp only [List.cons.injEq, and_true] at hcs
  obtain ⟨rfl, rfl⟩ := hcs
  obtain ⟨u₀, hu₀, p, hp, P, hP, hl, hθ, hm'⟩ := compile_arr_iff.mp hm
  simp only [List.cons.injEq, and_true] at hu₀
  subst hu₀
  simp only [Prod.mk.injEq] at hm'
  obtain ⟨rfl, rfl⟩ := hm'
  obtain ⟨hdom, hndh, hcomp⟩ := roseNode_prim hM hρ hds (c := c) hp hkn hl hθ ht
  rw [hdom] at hP
  obtain ⟨l₁, cs₁, L, A₁, CS, T₁, hlcs, hl₁, hcs₁, hPe⟩ := compile_pair_iff.mp hP
  simp only [List.cons.injEq, and_true] at hlcs
  obtain ⟨rfl, rfl⟩ := hlcs
  simp only [Prod.mk.injEq] at hPe
  obtain ⟨rfl, hAT⟩ := hPe
  obtain ⟨hA₁, hT₁⟩ := prod_inj hAT
  subst A₁ T₁
  generalize PartialHorn.subst θ p.cod = T at *
  generalize PartialHorn.subst θ p.arrow = nd at *
  -- the typings
  have hLh : Hom M ρ L X a := (hty _ _ _ _ hl₁ he).1
  have hat : IsTy G n a = true := (hty _ _ _ _ hl₁ he).2
  have hCSh : Hom M ρ CS X (list T) := (hty _ _ _ _ hcs₁ he).1
  have hA := hobj a hat
  have hPt : IsTy G n (prod a (list c)) = true := by simp [isTy_prod, isTy_list, hat, hct]
  have hPo := hobj _ hPt
  have hSe : EnvHom M ρ G n (prod a (list c)) [(idt (prod a (list c)), prod a (list c))] :=
    ⟨hPo, by simpa using ⟨idt_hom hM hPo, hPt⟩⟩
  have hS : Hom M ρ S (prod a (list c)) c := (hty _ _ _ _ hs hSe).1
  have hFS := roseParts_hom hM ht hA hS
  have hmap := listMap_hom hM hFS
  have hMAP := compile_roseMap hkl hkc hct ht hs hcs₁
  generalize hq : comp (listRec T (comp (nil c) (bang one))
    (comp (cons c) (pair (comp (F S) (fst T (list c))) (snd T (list c))))) CS = MAPc at hMAP
  have hMAPh : Hom M ρ MAPc X (list c) := (hty _ _ _ _ hMAP he).1
  have hk := pair_hom hM hLh hMAPh
  obtain ⟨r₁, h₁, hr₁⟩ := compile_precomp hM hG hρ hps hds hs hSe hk
    (e' := [(pair L MAPc, prod a (list c))]) fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (comp (idt (prod a (list c))) (pair L MAPc), prod a (list c)) = p := by
          simpa [precomp] using hp
        exact ⟨_, rfl, rfl, (idt_comp hM hk).symm⟩
      · simp [precomp] at hp
  obtain ⟨r₂, h₂, hr₂⟩ := compile_subst hM hG hρ hps hds s X _ r₁ h₁ e
    (instVar (Term.pair l (Term.listRec (Term.arr kl [c] Term.star)
      (Term.arr kc [c] (Term.pair (Term.roseRec c s (Term.var 1)) (Term.var 0))) cs))) he
    fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (pair L MAPc, prod a (list c)) = p := by simpa using hp
        exact ⟨_, compile_pair_iff.mpr ⟨_, _, _, _, _, _, rfl, hl₁, hMAP, rfl⟩, ResEq.refl _⟩
      · simp at hp
  refine ⟨r₂, h₂, ResEq.trans (r₂ := (comp S (pair L MAPc), c)) ⟨rfl, ?_⟩ (hr₁.trans hr₂)⟩
  subst hq
  have hLCS := pair_hom hM hLh hCSh
  have hLT := isObj_list hM hFS.isObj_dom
  have hpm : Hom M ρ (prodMapRight a (listMap (F S))) (prod a (list T)) (prod a (list c)) :=
    (pair_hom hM (fst_hom hM hA hLT) (comp_hom hM (snd_hom hM hA hLT) hmap)).congr
      (eval_prodMapRight a hmap) rfl rfl
  exact Eq.symm ((comp_assoc hM hLCS hndh hFS).trans ((eval_op₂_congr 3 (hcomp hS) rfl).trans
    ((comp_assoc hM hLCS hpm hS).symm.trans (eval_op₂_congr 3 rfl
      ((prodMapRight_pair hM hLh hCSh hmap).trans
        (eval_op₂_congr 9 rfl (eval_op₂_congr 3 (eval_listMap hM hFS) rfl)))))))

/-- A side of a theorem, at objects and at terms of the instances of its context's types,
compiles to its arrow's instance after the terms' tuple. -/
theorem compile_thm_side {m : ℕ} {Δ : List Tree} {s : Term} {F A : Tree}
    (hs : compile G m s (ctxObj Δ) (stdEnv Δ) = some (F, A)) {θ : List Tree}
    (hl : θ.length = m) (hθ : θ.all (IsTy G n) = true) {σ : List Term} {X : Tree}
    {e rs : List (Tree × Tree)} (he : EnvHom M ρ G n X e)
    (hrs : σ.mapM (fun u ↦ compile G n u X e) = some rs)
    (hsnd : rs.map Prod.snd = Δ.map (PartialHorn.subst θ)) :
    ∃ r', compile G n (Term.subst (Term.osubst θ s) (Term.substList σ)) X e = some r' ∧
      ResEq M ρ (comp (PartialHorn.subst θ F) (tuple X (rs.map Prod.fst)),
        PartialHorn.subst θ A) r' := by
  have hty := compile_hom hM hG hρ hps hds
  have hs' := compile_osubst hG hl hθ s _ _ _ hs
  rw [subst_ctxObj, map_substPair_stdEnv] at hs'
  have hrs' : EnvHom M ρ G n X rs := ⟨he.1, fun q hq ↦ by
    obtain ⟨c, -, hcq⟩ := exists_of_mapM hrs hq
    exact hty c X e q hcq he⟩
  obtain ⟨r₁, h₁, hr₁⟩ := compile_of_stdEnv hM hG hρ hps hds hs' hrs' hsnd
  obtain ⟨r₂, h₂, hr₂⟩ := compile_subst hM hG hρ hps hds _ X rs r₁ h₁ e (Term.substList σ) he
    fun i p hp ↦ by
      obtain ⟨c, hc, hcp⟩ := getElem?_of_mapM_eq hrs hp
      exact ⟨p, by simpa [Term.substList, hc] using hcp, ResEq.refl p⟩
  exact ⟨r₂, h₂, hr₁.trans hr₂⟩

omit hG hρ hps hds in
/-- An environment of arrows after an arrow is an environment of arrows. -/
theorem envHom_precomp {X Y h : Tree} {e : List (Tree × Tree)} (he : EnvHom M ρ G n Y e)
    (hh : Hom M ρ h X Y) : EnvHom M ρ G n X (precomp h e) := by
  refine ⟨hh.isObj_dom, fun p hp ↦ ?_⟩
  simp only [precomp, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact ⟨comp_hom hM hh (he.2 q hq).1, (he.2 q hq).2⟩

/-- Hypotheses that hold in an environment hold in one of its values after an arrow. -/
theorem hypsHold_precomp {Φ : List Term} {X Y h : Tree} {e e' : List (Tree × Tree)}
    (hΦ : HypsHold M ρ G n Φ Y e) (he : EnvHom M ρ G n Y e) (hh : Hom M ρ h X Y)
    (he' : EnvEq M ρ (precomp h e) e') : HypsHold M ρ G n Φ X e' := fun ψ hψ ↦ by
  obtain ⟨r, hr, hr₂, hr₁⟩ := hΦ ψ hψ
  obtain ⟨r', hr', hr'₂, hr'₁⟩ := compile_precomp hM hG hρ hps hds hr he hh he'
  exact ⟨r', hr', hr'₂.trans hr₂, hr'₁.trans ((eval_op₂_congr 3 hr₁ rfl).trans (truth_comp hM hh))⟩

/-- Hypotheses that hold in an environment hold, renamed, in an environment whose variables at
the renamed indices are the first's values after an arrow. -/
theorem hypsHold_rename {Φ : List Term} {X Y h : Tree} {e e' E : List (Tree × Tree)}
    {f : ℕ → ℕ} (hΦ : HypsHold M ρ G n Φ Y e) (he : EnvHom M ρ G n Y e) (hh : Hom M ρ h X Y)
    (he' : EnvEq M ρ (precomp h e) e') (hf : ∀ i < e'.length, E[f i]? = e'[i]?) :
    HypsHold M ρ G n (Φ.map fun ψ ↦ Term.rename ψ f) X E := fun ψ hψ ↦ by
  obtain ⟨ψ₀, hψ₀, rfl⟩ := List.mem_map.mp hψ
  obtain ⟨r, hr, hH⟩ := hypsHold_precomp hM hG hρ hps hds hΦ he hh he' ψ₀ hψ₀
  exact ⟨r, compile_rename ψ₀ X E e' f r hr hf, hH⟩

/-- Hypotheses that hold in an environment hold, weakened, in its extension by a variable. -/
theorem hypsHold_weaken1 {Φ : List Term} {X a : Tree} {e : List (Tree × Tree)}
    (hΦ : HypsHold M ρ G n Φ X e) (he : EnvHom M ρ G n X e) (ha : IsObj M ρ a) :
    HypsHold M ρ G n (Φ.map weaken1) (prod X a) (extEnv X a e) :=
  hypsHold_rename hM hG hρ hps hds hΦ he (fst_hom hM he.1 ha) (envEq_refl _) fun i hi ↦ by
    simp [extEnv, precomp]

/-- An equation holds exactly when its sides have one value. -/
theorem holds_eq_iff {t u : Term} {X f g A : Tree} {e : List (Tree × Tree)}
    (he : EnvHom M ρ G n X e) (ht : compile G n t X e = some (f, A))
    (hu : compile G n u X e = some (g, A)) :
    Holds M ρ X (comp (chi (diag A)) (pair f g), omega) ↔ eval M ρ f = eval M ρ g := by
  have hf : Hom M ρ f X A := (compile_hom hM hG hρ hps hds t X e _ ht he).1
  have hg : Hom M ρ g X A := (compile_hom hM hG hρ hps hds u X e _ hu he).1
  refine ⟨fun h ↦ eq_of_chi_diag hM hf hg h.2, fun h ↦ ⟨rfl, ?_⟩⟩
  exact (eval_op₂_congr 3 rfl (eval_op₂_congr 9 rfl h.symm)).trans (chi_diag_pair_self hM hf)

/-- Rewriting by an equation among the hypotheses is sound, in either direction. -/
theorem rwHyp_sound {Γ : List Tree} {Φ : List Term} {i : ℕ} {ψ l r : Term}
    (hψ : Φ[i]? = some ψ) (hlr : eqParts ψ = some (l, r)) :
    RwSound M ρ G n Γ Φ l r ∧ RwSound M ρ G n Γ Φ r l := by
  obtain rfl := eqParts_eq_some hlr
  have key : ∀ X e, EnvHom M ρ G n X e → HypsHold M ρ G n Φ X e → ∃ f g A,
      compile G n l X e = some (f, A) ∧ compile G n r X e = some (g, A) ∧
        eval M ρ f = eval M ρ g := fun X e he hΦ ↦ by
    obtain ⟨q, hq, hH⟩ := hΦ _ (List.mem_of_getElem? hψ)
    obtain ⟨l', r', hlr', f, A, hl, g, hr, rfl⟩ := compile_eq_iff.mp hq
    simp only [List.cons.injEq, and_true] at hlr'
    obtain ⟨rfl, rfl⟩ := hlr'
    exact ⟨f, g, A, hl, hr, (holds_eq_iff hM hG hρ hps hds he hl hr).mp hH⟩
  refine ⟨fun X e he _ hΦ q hq ↦ ?_, fun X e he _ hΦ q hq ↦ ?_⟩
  · obtain ⟨f, g, A, hl, hr, hfg⟩ := key X e he hΦ
    obtain rfl := Option.some_inj.mp (hq.symm.trans hl)
    exact ⟨_, hr, rfl, hfg.symm⟩
  · obtain ⟨f, g, A, hl, hr, hfg⟩ := key X e he hΦ
    obtain rfl := Option.some_inj.mp (hq.symm.trans hr)
    exact ⟨_, hl, rfl, hfg⟩

omit hM hG hρ hps hds in
/-- An arrow between objects at the values of types is, with the types substituted for the
object variables, an arrow between the substituted objects. -/
theorem Hom.subst {θ : List Tree} {ws : List M.Val} (hθw : θ.map (eval M ρ) = ws.map Part.some)
    (hlen : ws.length = θ.length) {f X Y : Tree} (h : Hom M ws f X Y) :
    Hom M ρ (PartialHorn.subst θ f) (PartialHorn.subst θ X) (PartialHorn.subst θ Y) := by
  have hs : ∀ {t : Tree} {w : M.Val}, eval M ws t = Part.some w →
      eval M ρ (PartialHorn.subst θ t) = eval M ws t := fun {t w} ht ↦
    PartialHorn.eval_subst hθw t (hlen ▸ scoped_of_eval t ht)
  obtain ⟨w, hw, hws, ⟨x, hx, hxs⟩, ⟨y, hy, hys⟩, hd, hc⟩ := h
  refine ⟨w, (hs hw).trans hw, hws, ⟨x, (hs hx).trans hx, hxs⟩, ⟨y, (hs hy).trans hy, hys⟩,
    ?_, ?_⟩
  · rw [show dom (PartialHorn.subst θ f) = PartialHorn.subst θ (dom f) by simp [dom, subst_op],
      hs (hd.trans hx), hs hx, hd]
  · rw [show cod (PartialHorn.subst θ f) = PartialHorn.subst θ (cod f) by simp [cod, subst_op],
      hs (hc.trans hy), hs hy, hc]

/-- A valid theorem's instance holds: at objects and at terms of the instances of its context's
types, in an environment of arrows in which the instances of its hypotheses hold, the instance of
its conclusion holds. -/
theorem Thm.Valid.inst {a : Thm} (ha : a.Valid M G) {θ : List Tree} {σ : List Term}
    (hl : θ.length = a.arity) (hθ : θ.all (IsTy G n) = true) {X : Tree}
    {e rs : List (Tree × Tree)} (he : EnvHom M ρ G n X e)
    (hrs : σ.mapM (fun u ↦ compile G n u X e) = some rs)
    (hsnd : rs.map Prod.snd = a.ctx.map (PartialHorn.subst θ))
    (hH : HypsHold M ρ G n (a.hyps.map (instTerm θ σ)) X e) :
    ∀ r, compile G n (instTerm θ σ a.concl) X e = some r → Holds M ρ X r := by
  obtain ⟨hctx, hhyps, hcon, hv⟩ := ha
  obtain ⟨ws, hθw, hws⟩ := exists_vals_of_isTy hM hds.2 hρ θ hθ
  rw [hl] at hws
  have hlen : ws.length = θ.length := by simpa [hl] using congrArg List.length hws
  obtain ⟨hpsw, hdsw, hfw⟩ := hv ws hws
  have hstdw := stdEnv_hom hM hdsw.2 hws a.ctx hctx
  -- the conclusion and the hypotheses in the context's environment of projections
  obtain ⟨⟨C, C'⟩, hC, hC'⟩ := Option.map_eq_some_iff.mp hcon
  obtain rfl : C' = omega := hC'
  obtain ⟨Hs, hHs, hHs'⟩ := exists_mapM_of_forall
    (f := fun h ↦ compile G a.arity h (ctxObj a.ctx) (stdEnv a.ctx))
    (P := fun q ↦ q.2 = omega) a.hyps fun h hh ↦ by
      obtain ⟨q, hq, hq'⟩ := Option.map_eq_some_iff.mp (hhyps h hh)
      exact ⟨q, hq, hq'⟩
  have hCw : Hom M ws C (ctxObj a.ctx) omega :=
    (compile_hom hM hG hws hpsw hdsw _ _ _ _ hC hstdw).1
  have hHw : ∀ h ∈ Hs.map Prod.fst, Hom M ws h (ctxObj a.ctx) omega := fun h hh ↦ by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hh
    obtain ⟨ψ, -, hψ⟩ := exists_of_mapM hHs hq
    have := (compile_hom hM hG hws hpsw hdsw _ _ _ _ hψ hstdw).1
    rwa [hHs' q hq] at this
  -- at the objects' values, the conclusion holds on the subobject on which the hypotheses hold
  obtain ⟨hm, hmH⟩ := subObj_hom hM hstdw.1 _ hHw
  have hE₀ := envHom_precomp hM hstdw hm
  have hE₀Γ : (precomp (subObj (ctxObj a.ctx) (Hs.map Prod.fst)).2 (stdEnv a.ctx)).map
      Prod.snd = a.ctx := by
    simp [precomp, Function.comp_def, map_snd_stdEnv]
  have hH₀ : HypsHold M ws G a.arity a.hyps (subObj (ctxObj a.ctx) (Hs.map Prod.fst)).1
      (precomp (subObj (ctxObj a.ctx) (Hs.map Prod.fst)).2 (stdEnv a.ctx)) := fun ψ hψ ↦ by
    obtain ⟨q, hq, hψq⟩ := exists_mem_of_mapM hHs hψ
    obtain ⟨r, hr, hr₂, hr₁⟩ := compile_comp hM hG hws hpsw hdsw ψ _ _ q hψq hstdw _ _ hm
    exact ⟨r, hr, hr₂.trans (hHs' q hq), hr₁.trans (hmH q.1 (List.mem_map_of_mem hq))⟩
  obtain ⟨r₀, hr₀, -, hr₀₁⟩ := compile_comp hM hG hws hpsw hdsw _ _ _ _ hC hstdw _ _ hm
  have hCm := hr₀₁.symm.trans (hfw _ _ hE₀ hE₀Γ hH₀ r₀ hr₀).2
  -- at the given assignment, the instances' arrows after the terms' tuple
  have hT := tuple_hom hM he.1 rs fun q hq ↦ by
    obtain ⟨u, -, hu⟩ := exists_of_mapM hrs hq
    exact (compile_hom hM hG hρ hps hds u X e q hu he).1
  rw [hsnd, ← subst_ctxObj] at hT
  have hmρ := Hom.subst hθw hlen hm
  have hCρ := Hom.subst hθw hlen hCw
  rw [subst_omega] at hCρ
  have hHρ : ∀ h ∈ (Hs.map Prod.fst).map (PartialHorn.subst θ),
      Hom M ρ h (PartialHorn.subst θ (ctxObj a.ctx)) omega := fun h hh ↦ by
    obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hh
    have := Hom.subst hθw hlen (hHw h' hh')
    rwa [subst_omega] at this
  have htrue : ∀ h ∈ (Hs.map Prod.fst).map (PartialHorn.subst θ),
      eval M ρ (comp h (tuple X (rs.map Prod.fst))) = eval M ρ (comp tru (bang X)) :=
    fun h hh ↦ by
      obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hh
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hh'
      obtain ⟨ψ, hψ, hψq⟩ := exists_of_mapM hHs hq
      obtain ⟨r', hr', -, hr'₁⟩ := compile_thm_side hM hG hρ hps hds hψq hl hθ he hrs hsnd
      obtain ⟨r, hr, -, hr₁⟩ := hH _ (List.mem_map_of_mem hψ)
      obtain rfl := Option.some_inj.mp (hr.symm.trans hr')
      exact hr'₁.symm.trans hr₁
  obtain ⟨l, hl', hml⟩ := subObj_lift hM hmρ.isObj_cod hT _ hHρ htrue
  have hS := subst_subObj θ (ctxObj a.ctx) (Hs.map Prod.fst)
  rw [← hS] at hl' hml
  -- the conclusion's instance
  intro r hr
  obtain ⟨r', hr', hr'₂, hr'₁⟩ := compile_thm_side hM hG hρ hps hds hC hl hθ he hrs hsnd
  obtain rfl := Option.some_inj.mp (hr.symm.trans hr')
  refine ⟨hr'₂.trans (subst_omega θ), hr'₁.trans ?_⟩
  have hsw : ∀ {t : Tree} {w : M.Val}, eval M ws t = Part.some w →
      eval M ρ (PartialHorn.subst θ t) = eval M ws t := fun {t w} ht ↦
    PartialHorn.eval_subst hθw t (hlen ▸ scoped_of_eval t ht)
  obtain ⟨w₁, hw₁, -⟩ := (comp_hom hM hm hCw).exists_eval
  obtain ⟨w₂, hw₂, -⟩ := (truth_hom hM hm.isObj_dom).exists_eval
  have hsC : eval M ρ (comp (PartialHorn.subst θ C)
      (PartialHorn.subst θ (subObj (ctxObj a.ctx) (Hs.map Prod.fst)).2)) =
      eval M ρ (comp tru (bang (PartialHorn.subst θ
        (subObj (ctxObj a.ctx) (Hs.map Prod.fst)).1))) := by
    rw [← subst_comp, hsw hw₁, hCm, ← hsw hw₂, subst_comp, subst_bang,
      show PartialHorn.subst θ tru = tru from subst_const θ 26]
  exact (eval_op₂_congr 3 rfl hml.symm).trans ((comp_assoc hM hl' hmρ hCρ).trans
    ((eval_op₂_congr 3 hsC rfl).trans (truth_comp hM hl')))


/-- An instance of a valid equational theorem, from either side to the other, is sound: its
sides at objects and at terms of the instances of its context's types. -/
theorem thm_inst_sound {a : Thm} (ha : a.Valid M G) (hnil : a.hyps = []) {lr : Term × Term}
    (hlr : eqParts a.concl = some lr) {Γ θ : List Tree} {Φ : List Term} {σ : List Term}
    (hl : θ.length = a.arity) (hθ : θ.all (IsTy G n) = true) (hσl : σ.length = a.ctx.length)
    (hall : (σ.zip (a.ctx.map (PartialHorn.subst θ))).all
      (fun x ↦ decide (typeIn G n Γ x.1 = some x.2)) = true)
    {s s' : Term} (hs : s = lr.1 ∧ s' = lr.2 ∨ s = lr.2 ∧ s' = lr.1) :
    RwSound M ρ G n Γ Φ (instTerm θ σ s) (instTerm θ σ s') := by
  intro X e he hΓ _ q hq
  have hconcl := eqParts_eq_some hlr
  obtain ⟨-, -, hcon, -⟩ := id ha
  obtain ⟨⟨C, C'⟩, hC, -⟩ := Option.map_eq_some_iff.mp hcon
  rw [hconcl] at hC
  obtain ⟨l', r', hlr', f, A, hf, g, hg, -⟩ := compile_eq_iff.mp hC
  simp only [List.cons.injEq, and_true] at hlr'
  obtain ⟨rfl, rfl⟩ := hlr'
  obtain ⟨rs, hrs, hsnd⟩ := mapM_compile_of_typeIn hΓ σ _ (by simp [hσl]) hall
  obtain ⟨r₁, h₁, hr₁₂, hr₁₁⟩ := compile_thm_side hM hG hρ hps hds hf hl hθ he hrs hsnd
  obtain ⟨r₂, h₂, hr₂₂, hr₂₁⟩ := compile_thm_side hM hG hρ hps hds hg hl hθ he hrs hsnd
  -- the equation's instance holds, so its sides' arrows have one value
  obtain ⟨f₁, A₁⟩ := r₁
  obtain ⟨g₁, A₂⟩ := r₂
  simp only at hr₁₂ hr₂₂
  subst hr₁₂ hr₂₂
  have hinst : compile G n (instTerm θ σ a.concl) X e =
      some (comp (chi (diag (PartialHorn.subst θ A))) (pair f₁ g₁), omega) := by
    rw [hconcl]
    exact compile_eq_iff.mpr ⟨_, _, rfl, f₁, _, h₁, g₁, h₂, rfl⟩
  have hH := Thm.Valid.inst hM hG hρ hps hds ha hl hθ he hrs hsnd
    (by rw [hnil]; exact fun _ h ↦ by simp at h) _ hinst
  have hfg := (holds_eq_iff hM hG hρ hps hds he h₁ h₂).mp hH
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain rfl := Option.some_inj.mp (hq.symm.trans h₁)
    exact ⟨_, h₂, rfl, hfg.symm⟩
  · obtain rfl := Option.some_inj.mp (hq.symm.trans h₂)
    exact ⟨_, h₁, rfl, hfg⟩

/-- Each equation of the language applied at a term's root is sound, with sound unfoldings and
valid earlier theorems. -/
theorem rootStep_sound (hδ : DefnsOk M G) {E : Array Entry}
    (hE : ∀ (j : ℕ) (a : Thm), (E[j]?).bind Entry.language? = some a → a.Valid M G)
    {Γ : List Tree} {Φ : List Term}
    {l : Rule} {t t' : Term} (h : rootStep G E n Γ Φ l t = some t') :
    RwSound M ρ G n Γ Φ t t' := by
  obtain ⟨l₀, cs, rfl⟩ : ∃ l cs, t = RoseTree.node l cs :=
    ⟨_, _, (RoseTree.node_label_children t).symm⟩
  cases l with
  | beta =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨f, _ | ⟨u, _ | ⟨w, cs⟩⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, f = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children f).symm⟩
    cases l₁ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs₁ with _ | ⟨b, _ | ⟨w, cs⟩⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at h
    subst h
    exact beta_sound hM hG hρ hps hds Γ _ b u
  | fstPair =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨p, _ | ⟨w, cs⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, p = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children p).symm⟩
    cases l₁ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs₁ with _ | ⟨a, _ | ⟨b, _ | ⟨w, cs⟩⟩⟩ <;>
      simp only [reduceCtorEq, Option.some.injEq] at h
    subst h
    exact fstPair_sound hM hG hρ hps hds Γ _ b
  | sndPair =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨p, _ | ⟨w, cs⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, p = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children p).symm⟩
    cases l₁ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs₁ with _ | ⟨a, _ | ⟨b, _ | ⟨w, cs⟩⟩⟩ <;>
      simp only [reduceCtorEq, Option.some.injEq] at h
    subst h
    exact sndPair_sound hM hG hρ hps hds Γ a _
  | pairEta =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨x₁, _ | ⟨y₁, _ | ⟨w, cs⟩⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, x₁ = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children x₁).symm⟩
    obtain ⟨l₂, cs₂, rfl⟩ : ∃ l cs, y₁ = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children y₁).symm⟩
    cases l₁ <;> cases l₂ <;>
      simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs₁ with _ | ⟨p, _ | ⟨w, cs₁⟩⟩ <;> rcases cs₂ with _ | ⟨q, _ | ⟨w', cs₂⟩⟩ <;>
      simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact pairEta_sound hM hG hρ hps hds Γ p
  | unitEta =>
    simp only [rootStep] at h
    split_ifs at h with h₁
    obtain rfl := Option.some_inj.mp h
    exact unitEta_sound hM hG hρ hps hds h₁
  | delta =>
    cases l₀ <;> simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq,
      Option.map_eq_some_iff] at h
    obtain ⟨d, hd, rfl⟩ := h
    exact delta_sound hM hG hρ hps hds hδ (bind_language?_eq_some.mp hd) Γ _ cs
  | natZero kz =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨w, cs⟩⟩⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, m = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children m).symm⟩
    cases l₁ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rename_i k θ
    rcases θ with _ | ⟨a, θ⟩ <;> rcases cs₁ with _ | ⟨c, _ | ⟨w, cs₁⟩⟩ <;>
      simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨rfl, hk, rfl⟩, rfl⟩ := h
    exact natZero_sound hM hG hρ hps hds hk Γ z s
  | natSucc ks =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨w, cs⟩⟩⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, m = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children m).symm⟩
    cases l₁ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rename_i k θ
    rcases θ with _ | ⟨a, θ⟩ <;> rcases cs₁ with _ | ⟨c, _ | ⟨w, cs₁⟩⟩ <;>
      simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨rfl, hk⟩, rfl⟩ := h
    exact natSucc_sound hM hG hρ hps hds hk Γ z s c
  | listNil kn =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨w, cs⟩⟩⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, m = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children m).symm⟩
    cases l₁ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rename_i k θ
    rcases θ with _ | ⟨a, _ | ⟨b, θ⟩⟩ <;> rcases cs₁ with _ | ⟨c, _ | ⟨w, cs₁⟩⟩ <;>
      simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨rfl, hk, rfl⟩, rfl⟩ := h
    exact listNil_sound hM hG hρ hps hds hk Γ z s a
  | listCons kc =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨w, cs⟩⟩⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, m = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children m).symm⟩
    cases l₁ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rename_i k θ
    rcases θ with _ | ⟨a, _ | ⟨b, θ⟩⟩ <;> rcases cs₁ with _ | ⟨p, _ | ⟨w, cs₁⟩⟩ <;>
      simp only [reduceCtorEq] at h
    obtain ⟨l₂, cs₂, rfl⟩ : ∃ l cs, p = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children p).symm⟩
    cases l₂ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs₂ with _ | ⟨hd, _ | ⟨tl, _ | ⟨w, cs₂⟩⟩⟩ <;>
      simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨rfl, hk⟩, rfl⟩ := h
    exact listCons_sound hM hG hρ hps hds hk Γ z s a hd tl
  | thm j θ σ flip =>
    obtain ⟨a, lr, ha, hnil, hlr, hok, ht, rfl⟩ := rootStep_thm h
    rw [ht]
    simp only [instOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hl, hθ⟩, hσl⟩, hall⟩ := hok
    cases flip
    · exact thm_inst_sound hM hG hρ hps hds (hE j a ha) hnil hlr hl hθ hσl hall (.inl ⟨rfl, rfl⟩)
    · exact thm_inst_sound hM hG hρ hps hds (hE j a ha) hnil hlr hl hθ hσl hall (.inr ⟨rfl, rfl⟩)
  | rwHyp i flip =>
    obtain ⟨ψ, ⟨l, r⟩, hψ, hψlr, ht, rfl⟩ := rootStep_rwHyp h
    rw [ht]
    obtain ⟨h₁, h₂⟩ := rwHyp_sound hM hG hρ hps hds hψ hψlr
    cases flip
    · exact h₁
    · exact h₂
  | roseNode kn kl kc =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨s, _ | ⟨m, _ | ⟨w, cs⟩⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, m = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children m).symm⟩
    cases l₁ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs₁ with _ | ⟨p, _ | ⟨w, cs₁⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₂, cs₂, rfl⟩ : ∃ l cs, p = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children p).symm⟩
    cases l₂ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs₂ with _ | ⟨hd, _ | ⟨tl, _ | ⟨w, cs₂⟩⟩⟩ <;>
      simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨rfl, hkn, hkl, hkc⟩, rfl⟩ := h
    exact roseNode_sound hM hG hρ hps hds hkn hkl hkc Γ _ _ s hd tl
  | caseInl kc kl =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨f, _ | ⟨u, _ | ⟨w, cs⟩⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, f = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children f).symm⟩
    obtain ⟨l₂, cs₂, rfl⟩ : ∃ l cs, u = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children u).symm⟩
    cases l₁ <;> cases l₂ <;>
      simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs₁ with _ | ⟨p, _ | ⟨w, cs₁⟩⟩ <;> rcases cs₂ with _ | ⟨v, _ | ⟨w', cs₂⟩⟩ <;>
      simp only [reduceCtorEq] at h
    obtain ⟨l₃, cs₃, rfl⟩ : ∃ l cs, p = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children p).symm⟩
    cases l₃ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs₃ with _ | ⟨g, _ | ⟨g', _ | ⟨w, cs₃⟩⟩⟩ <;>
      simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl, hkc, hkl⟩, rfl⟩ := h
    exact caseInl_sound hM hG hρ hps hds hkc hkl Γ _ _ g g' v
  | caseInr kc kr =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨f, _ | ⟨u, _ | ⟨w, cs⟩⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, f = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children f).symm⟩
    obtain ⟨l₂, cs₂, rfl⟩ : ∃ l cs, u = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children u).symm⟩
    cases l₁ <;> cases l₂ <;>
      simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs₁ with _ | ⟨p, _ | ⟨w, cs₁⟩⟩ <;> rcases cs₂ with _ | ⟨v, _ | ⟨w', cs₂⟩⟩ <;>
      simp only [reduceCtorEq] at h
    obtain ⟨l₃, cs₃, rfl⟩ : ∃ l cs, p = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children p).symm⟩
    cases l₃ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs₃ with _ | ⟨g, _ | ⟨g', _ | ⟨w, cs₃⟩⟩⟩ <;>
      simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨rfl, rfl, hkc, hkr⟩, rfl⟩ := h
    exact caseInr_sound hM hG hρ hps hds hkc hkr Γ _ _ g g' v
  | refl | trans | cong | join | natInd | listInd | hyp | cut | conv | convFrom | propExt
    | funExt | apply | natIndHyp | listIndHyp | coprodInd | zeroInd | roseInd | roseIndHyp
    | cert | certSeq | quotInd =>
simp only [rootStep, reduceCtorEq] at h


/-- Congruence is sound: a node whose children rewrite soundly, each in its own context,
rewrites soundly to the node of their rewrites. -/
theorem cong_sound {l : Label} {ts ts' : List Term} {Γ : List Tree} {Φ : List Term}
    {Γs : List (List Tree × List Term)} (hΓs : childCtxs G n l ts Γ Φ = some Γs)
    (hR : List.Forall₂ (fun (p : (List Tree × List Term) × Term) u ↦
      RwSound M ρ G n p.1.1 p.1.2 p.2 u) (Γs.zip ts) ts') :
    RwSound M ρ G n Γ Φ (RoseTree.node l ts) (RoseTree.node l ts') := by
  intro X e he hΓ hΦ r h
  have hty := compile_hom hM hG hρ hps hds
  have hobj := isObj_of_isTy hM hds.2 hρ
  have he₁ : EnvHom M ρ G n one [] := ⟨isObj_one hM, by simp⟩
  have hnil : ∀ {Y : Tree} {e' : List (Tree × Tree)}, HypsHold M ρ G n [] Y e' :=
    fun _ h ↦ by simp at h
  cases l with
  | var i =>
    obtain ⟨rfl, -⟩ := compile_var_iff.mp h
    obtain rfl : ts' = [] := by simpa using hR
    exact ⟨r, h, ResEq.refl r⟩
  | star =>
    obtain ⟨rfl, -⟩ := compile_star_iff.mp h
    obtain rfl : ts' = [] := by simpa using hR
    exact ⟨r, h, ResEq.refl r⟩
  | pair =>
    obtain ⟨t, u, f, a, g, b, rfl, ht, hu, rfl⟩ := compile_pair_iff.mp h
    obtain rfl : Γs = [(Γ, Φ), (Γ, Φ)] := (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | ⟨h₂, _ | _⟩⟩
    obtain ⟨⟨f', a'⟩, ht', rfl, hf⟩ := h₁ X e he hΓ hΦ _ ht
    obtain ⟨⟨g', b'⟩, hu', rfl, hg⟩ := h₂ X e he hΓ hΦ _ hu
    exact ⟨_, compile_pair_iff.mpr ⟨_, _, f', a', g', b', rfl, ht', hu', rfl⟩, rfl,
      eval_op₂_congr 9 hf hg⟩
  | fst =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_fst_iff.mp h
    obtain rfl : Γs = [(Γ, Φ)] := (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | _⟩
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := h₁ X e he hΓ hΦ _ ht
    exact ⟨_, compile_fst_iff.mpr ⟨_, f', a, b, rfl, ht', rfl⟩, rfl, eval_op₂_congr 3 rfl hf⟩
  | snd =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_snd_iff.mp h
    obtain rfl : Γs = [(Γ, Φ)] := (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | _⟩
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := h₁ X e he hΓ hΦ _ ht
    exact ⟨_, compile_snd_iff.mpr ⟨_, f', a, b, rfl, ht', rfl⟩, rfl, eval_op₂_congr 3 rfl hf⟩
  | lam a =>
    obtain ⟨b, f, B, rfl, hat, hb, rfl⟩ := compile_lam_iff.mp h
    obtain rfl : Γs = [(a :: Γ, Φ.map weaken1)] := (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | _⟩
    obtain ⟨⟨f', B'⟩, hb', rfl, hf⟩ := h₁ _ _ (he.ext hM (hobj a hat) hat)
      (by simp [extEnv, hΓ, Function.comp_def])
      (hypsHold_weaken1 hM hG hρ hps hds hΦ he (hobj a hat)) _ hb
    exact ⟨_, compile_lam_iff.mpr ⟨_, f', B', rfl, hat, hb', rfl⟩, rfl,
      eval_op₃_congr 24 rfl rfl hf⟩
  | app =>
    obtain ⟨t, u, rfl, f, a, b, ht, g, hu, rfl⟩ := compile_app_iff.mp h
    obtain rfl : Γs = [(Γ, Φ), (Γ, Φ)] := (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | ⟨h₂, _ | _⟩⟩
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := h₁ X e he hΓ hΦ _ ht
    obtain ⟨⟨g', a'⟩, hu', rfl, hg⟩ := h₂ X e he hΓ hΦ _ hu
    exact ⟨_, compile_app_iff.mpr ⟨_, _, rfl, f', a', b, ht', g', hu', rfl⟩, rfl,
      eval_op₂_congr 3 rfl (eval_op₂_congr 9 hf hg)⟩
  | arr k θ =>
    obtain ⟨t, rfl, p, hp, g, ht, hl, hθ, rfl⟩ := compile_arr_iff.mp h
    obtain rfl : Γs = [(Γ, Φ)] := (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | _⟩
    obtain ⟨⟨g', d'⟩, ht', rfl, hg⟩ := h₁ X e he hΓ hΦ _ ht
    exact ⟨_, compile_arr_iff.mpr ⟨_, rfl, p, hp, g', ht', hl, hθ, rfl⟩, rfl,
      eval_op₂_congr 3 rfl hg⟩
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
    have hc : typeIn G n [] z = some c := by
      change (compile G n z one []).map Prod.snd = some c
      rw [hz]
      rfl
    obtain rfl : Γs = [([], []), ([c], []), (Γ, Φ)] := by
      change (typeIn G n [] z).bind (fun c ↦ some [([], []), ([c], []), (Γ, Φ)]) = some Γs at hΓs
      rw [hc, Option.bind_some] at hΓs
      exact (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | ⟨h₂, _ | ⟨h₃, _ | _⟩⟩⟩
    obtain ⟨hz'h, hct⟩ := hty _ _ _ _ hz he₁
    have hC := hobj c hct
    obtain ⟨⟨z'', c'⟩, hz', hzc, hzv⟩ := h₁ one [] he₁ rfl hnil _ hz
    obtain rfl : c = c' := hzc.symm
    obtain ⟨⟨s'', c''⟩, hs', hsc, hsv⟩ := h₂ c [(idt c, c)]
      ⟨hC, by simpa using ⟨idt_hom hM hC, hct⟩⟩ rfl hnil _ hs
    obtain rfl : c = c'' := hsc.symm
    obtain ⟨⟨m'', N⟩, hm', rfl, hmv⟩ := h₃ X e he hΓ hΦ _ hm
    exact ⟨_, compile_natRec_iff.mpr ⟨_, _, _, rfl, z'', c, hz', s'', hs', m'', hm', rfl⟩, rfl,
      eval_op₂_congr 3 (eval_op₂_congr 32 hzv hsv) hmv⟩
  | listRec =>
    obtain ⟨z, s, m, rfl, m', A, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
    have hc : typeIn G n [] z = some c := by
      change (compile G n z one []).map Prod.snd = some c
      rw [hz]
      rfl
    obtain ⟨f₀, hf₀⟩ := compile_retype m X e _ hm (ctxObj Γ) (stdEnv Γ)
      (by rw [map_snd_stdEnv, hΓ])
    have hmt : typeIn G n Γ m = some (list A) := by
      change (compile G n m (ctxObj Γ) (stdEnv Γ)).map Prod.snd = some (list A)
      rw [hf₀]
      rfl
    obtain rfl : Γs = [([], []), ([c, A], []), (Γ, Φ)] := by
      change (typeIn G n [] z).bind (fun c ↦ ((typeIn G n Γ m).bind listPart).bind
        fun a ↦ some [([], []), ([c, a], []), (Γ, Φ)]) = some Γs at hΓs
      rw [hc, Option.bind_some, hmt, Option.bind_some, listPart_eq_some.mpr rfl,
        Option.bind_some] at hΓs
      exact (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | ⟨h₂, _ | ⟨h₃, _ | _⟩⟩⟩
    obtain ⟨-, hLt⟩ := hty _ _ _ _ hm he
    rw [isTy_list] at hLt
    obtain ⟨-, hct⟩ := hty _ _ _ _ hz he₁
    have hA := hobj A hLt
    have hC := hobj c hct
    obtain ⟨⟨z'', c'⟩, hz', hzc, hzv⟩ := h₁ one [] he₁ rfl hnil _ hz
    obtain rfl : c = c' := hzc.symm
    obtain ⟨⟨s'', c''⟩, hs', hsc, hsv⟩ := h₂ (prod A c) [(snd A c, c), (fst A c, A)]
      ⟨isObj_prod hM hA hC, by simpa using ⟨⟨snd_hom hM hA hC, hct⟩, fst_hom hM hA hC, hLt⟩⟩
      rfl hnil _ hs
    obtain rfl : c = c'' := hsc.symm
    obtain ⟨⟨m'', N⟩, hm', hmN, hmv⟩ := h₃ X e he hΓ hΦ _ hm
    obtain rfl : list A = N := hmN.symm
    exact ⟨_, compile_listRec_iff.mpr ⟨_, _, _, rfl, m'', A, hm', z'', c, hz', s'', hs', rfl⟩,
      rfl, eval_op₂_congr 3 (eval_op₃_congr 36 rfl hzv hsv) hmv⟩
  | roseRec c =>
    obtain ⟨s, m, m', t, a, F, s', rfl, hct, hm, ht, hs, rfl⟩ := compile_roseRec_iff.mp h
    obtain ⟨f₀, hf₀⟩ := compile_retype m X e _ hm (ctxObj Γ) (stdEnv Γ)
      (by rw [map_snd_stdEnv, hΓ])
    have hmt : typeIn G n Γ m = some t := by
      change (compile G n m (ctxObj Γ) (stdEnv Γ)).map Prod.snd = some t
      rw [hf₀]
      rfl
    obtain rfl : Γs = [([prod a (list c)], []), (Γ, Φ)] := by
      change ((typeIn G n Γ m).bind roseParts).bind
        (fun p ↦ some [([prod p.1 (list c)], []), (Γ, Φ)]) = some Γs at hΓs
      rw [hmt, Option.bind_some, ht, Option.bind_some] at hΓs
      exact (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | ⟨h₂, _ | _⟩⟩
    have hat := isTy_of_roseParts ht (hty _ _ _ _ hm he).2
    have hPt : IsTy G n (prod a (list c)) = true := by simp [isTy_prod, isTy_list, hat, hct]
    have hP := hobj _ hPt
    obtain ⟨⟨s'', c'⟩, hs', rfl, hsv⟩ := h₁ _ [(idt (prod a (list c)), prod a (list c))]
      ⟨hP, by simpa using ⟨idt_hom hM hP, hPt⟩⟩ rfl hnil _ hs
    obtain ⟨⟨m'', N⟩, hm', hmN, hmv⟩ := h₂ X e he hΓ hΦ _ hm
    obtain rfl : t = N := hmN.symm
    exact ⟨_, compile_roseRec_iff.mpr ⟨_, _, m'', t, a, F, s'', rfl, hct, hm', ht, hs', rfl⟩,
      rfl, eval_op₂_congr 3 (eval_roseParts_congr ht hsv) hmv⟩
  | eq =>
    obtain ⟨t, u, rfl, f, a, ht, g, hu, rfl⟩ := compile_eq_iff.mp h
    obtain rfl : Γs = [(Γ, Φ), (Γ, Φ)] := (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | ⟨h₂, _ | _⟩⟩
    obtain ⟨⟨f', a'⟩, ht', rfl, hf⟩ := h₁ X e he hΓ hΦ _ ht
    obtain ⟨⟨g', b'⟩, hu', rfl, hg⟩ := h₂ X e he hΓ hΦ _ hu
    exact ⟨_, compile_eq_iff.mpr ⟨_, _, rfl, f', _, ht', g', hu', rfl⟩, rfl,
      eval_op₂_congr 3 rfl (eval_op₂_congr 9 hf hg)⟩
  | defn k θ =>
    obtain ⟨d, rs, hd, hrs, hl, hθ, hsnd, rfl⟩ := compile_defn_iff.mp h
    obtain rfl : Γs = ts.map fun _ ↦ (Γ, Φ) := (Option.some_inj.mp hΓs).symm
    obtain ⟨rs', hrs', hRR⟩ := mapM_forall₂ (R := ResEq M ρ)
      (fun _ _ r h₁ hr ↦ h₁ X e he hΓ hΦ r hr)
      (forall₂_zip_const (R := fun (p : List Tree × List Term) ↦ RwSound M ρ G n p.1 p.2) ts hR)
      hrs
    exact ⟨_, compile_defn_iff.mpr ⟨d, rs', hd, hrs', hl, hθ,
      (map_snd_of_forall₂ hRR).trans hsnd, rfl⟩, rfl,
      eval_op₂_congr 3 rfl (eval_tuple_of_forall₂ X hRR)⟩

/-- Congruence in the node's context is sound: a node whose children rewrite soundly in its
context, each child not in the node's context rewriting to itself, rewrites soundly to the node
of their rewrites. -/
theorem cong_sound_same {l : Label} {ts ts' : List Term} {Γ : List Tree} {Φ : List Term}
    (hR : List.Forall₂ (RwSound M ρ G n Γ Φ) ts ts')
    (hkeep : ∀ (i : ℕ) (h₁ : i < ts.length) (h₂ : i < ts'.length), sameCtx l i = false →
      ts'[i] = ts[i]) :
    RwSound M ρ G n Γ Φ (RoseTree.node l ts) (RoseTree.node l ts') := by
  intro X e he hΓ hΦ r h
  obtain ⟨Γs, hΓs⟩ := childCtxs_isSome Φ hΓ h
  have hlen := childCtxs_length hΓs
  obtain ⟨hl, hR⟩ := List.forall₂_iff_get.mp hR
  refine cong_sound hM hG hρ hps hds hΓs ?_ X e he hΓ hΦ r h
  refine List.forall₂_iff_get.mpr ⟨by simp [hlen, hl], fun i h₁ h₂ ↦ ?_⟩
  simp only [List.length_zip] at h₁
  simp only [List.get_eq_getElem, List.getElem_zip]
  cases hs : sameCtx l i
  · rw [hkeep i (by omega) h₂ hs]
    exact RwSound.refl _ _ _
  · rw [childCtxs_sameCtx hΓs (List.getElem?_eq_getElem _) hs]
    exact hR i (by omega) h₂

end Rewriting

end Geb.FreeTopos.Internal

end

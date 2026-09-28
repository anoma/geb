/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Coequalizers
public import Geb.Prototypes.FreeTopos.Internal.Soundness

set_option doc.verso true in
/-!
# The soundness of the internal language's proofs

The checker {name}`Geb.FreeTopos.Internal.check` is sound ({lit}`check_sound`): every rewriting a
derivation performs is sound, and every formula it proves is sound, in the sense of
{name}`Geb.FreeTopos.Internal.FmSound`.

The rules of proof are sound by the universal properties of the subobject classifier and of the
exponential. An equation whose sides rewrite to one term holds; a cut, and a formula rewritten
before or after its proof, are sound by the soundness of the rewriting and of the formula cut in.
Propositional extensionality is sound by the uniqueness of characteristic maps
({name}`Geb.FreeTopos.omega_ext`), each formula being true on the other's pullback of truth;
function extensionality by the η of the exponential, the applications compared in the
environment extended by a variable; and the application of an earlier theorem by its validity at
the instance. Induction in the form of the uniqueness of recursion is sound by the uniqueness of
the folds with a parameter ({name}`Geb.FreeTopos.natRec_param_unique`,
{name}`Geb.FreeTopos.listRec_param_unique`), and induction with the induction hypothesis by
induction on subobjects ({name}`Geb.FreeTopos.truth_of_natInd`,
{name}`Geb.FreeTopos.truth_of_listInd`), the step proved on the formula's pullback of truth. Each
induction is applied in the environment that extends the other variables' environment by the
induction variable, in which the hypotheses, which do not mention it, still hold, and is carried
to the given environment by the arrow of the variable. Case analysis on a coproduct is applied in
the same way, and is sound because an arrow from the product of an object and a coproduct is
determined by its composites with the products of the object and the injections
({name}`Geb.FreeTopos.prod_coprod_ext`); a formula in a context with a variable of the initial
type holds because an object with an arrow to the initial object is initial
({name}`Geb.FreeTopos.eq_of_hom_zero`). Induction on a quotient is applied in the same way, and is
sound because the product of an object with a coequalizer's projection is an epimorphism
({name}`Geb.FreeTopos.prod_coeq_ext`). The sequent a valid theorem compiles to is valid
({lit}`Thm.seq_valid`): its hypotheses are true in the environment of the context's projections
after the inclusion of the subobject on which they are true, where the theorem's conclusion is
then true. An equation cited from a certificate is sound by the certificates' checker's
soundness ({name}`Geb.PartialHorn.check_sound`), in a model whose definitions begin with the
compilations of the language's ({lit}`cert_sound`).

## Main statements

* {lit}`join_sound`, {lit}`cut_sound`, {lit}`conv_sound`, {lit}`convFrom_sound`,
  {lit}`propExt_sound`, {lit}`funExt_sound`, {lit}`apply_sound` — the logical rules are sound.
* {lit}`natInd_sound`, {lit}`listInd_sound`, {lit}`natIndHyp_sound`, {lit}`listIndHyp_sound` —
  induction is sound.
* {lit}`Thm.seq_valid`, {lit}`cert_sound` — the citations between the two checkers are
  sound.
* {lit}`quotInd_sound` — induction on a quotient is sound.
* {lit}`coprodInd_sound`, {lit}`zeroInd_sound` — case analysis on a coproduct, and a context
  with a variable of the initial type, are sound.
* {lit}`roseInd_sound` — induction on rose trees is sound.
* {lit}`check_sound` — the checker is sound.

## Tags

internal language, soundness, proof checker, induction, subobject classifier
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree op eval Model IsModel)
open Sorts
open scoped FinEnum

universe v

section Proofs

variable {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}
  (hM : IsModel (ext defs) M) {G : Globals} (hG : G.WF) {n : ℕ}
  (hρ : ρ.map Sigma.fst = List.replicate n obj) (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n)
include hM hG hρ hps hds

omit hM hG hρ hps hds in
/-- A term's result related to another has the other's type. -/
theorem compile_resEq {s : Term} {X : Tree} {e : List (Tree × Tree)} {q r : Tree × Tree}
    (hq : compile G n s X e = some q) (hr : ResEq M ρ r q) :
    compile G n s X e = some (q.1, r.2) :=
  hq.trans (congrArg some (Prod.ext rfl hr.1))

omit hM hG hρ hps hds in
/-- A formula of a context compiles, to the subobject classifier's type, in every environment of
the context's types. -/
theorem compile_of_typeIn {Γ : List Tree} {φ : Term} {A : Tree} (hφ : typeIn G n Γ φ = some A)
    {X : Tree} {e : List (Tree × Tree)} (hΓ : e.map Prod.snd = Γ) :
    ∃ f, compile G n φ X e = some (f, A) := by
  obtain ⟨⟨f₀, A₀⟩, hstd, rfl⟩ := Option.map_eq_some_iff.mp hφ
  exact compile_retype φ _ _ _ hstd X e (hΓ.trans (map_snd_stdEnv Γ).symm)

/-- An equation whose sides rewrite soundly to one term holds. -/
theorem join_sound {Γ : List Tree} {Φ : List Term} {t u v : Term}
    (h₁ : RwSound M ρ G n Γ Φ t v) (h₂ : RwSound M ρ G n Γ Φ u v) :
    FmSound M ρ G n Γ Φ (Term.eq t u) := by
  intro X e he hΓ hΦ r hr
  obtain ⟨t', u', htu, f, A, ht, g, hu, rfl⟩ := compile_eq_iff.mp hr
  simp only [List.cons.injEq, and_true] at htu
  obtain ⟨rfl, rfl⟩ := htu
  obtain ⟨q, hq, -, hq₁⟩ := h₁ X e he hΓ hΦ _ ht
  obtain ⟨q', hq', -, hq'₁⟩ := h₂ X e he hΓ hΦ _ hu
  obtain rfl : q = q' := Option.some_inj.mp (hq.symm.trans hq')
  exact (holds_eq_iff hM hG hρ hps hds he ht hu).mpr (hq₁.symm.trans hq'₁)

omit hM hG hρ hps hds in
/-- A hypothesis holds. -/
theorem hyp_sound {Γ : List Tree} {Φ : List Term} {i : ℕ} {φ : Term} (h : Φ[i]? = some φ) :
    FmSound M ρ G n Γ Φ φ := fun X e _ _ hΦ r hr ↦ by
  obtain ⟨q, hq, hH⟩ := hΦ φ (List.mem_of_getElem? h)
  obtain rfl := Option.some_inj.mp (hq.symm.trans hr)
  exact hH

omit hM hG hρ hps hds in
/-- A formula that holds under a formula proved first holds. -/
theorem cut_sound {Γ : List Tree} {Φ : List Term} {ψ φ : Term}
    (hψ : typeIn G n Γ ψ = some omega) (p : FmSound M ρ G n Γ Φ ψ)
    (q : FmSound M ρ G n Γ (Φ ++ [ψ]) φ) : FmSound M ρ G n Γ Φ φ := by
  intro X e he hΓ hΦ r hr
  obtain ⟨f, hf⟩ := compile_of_typeIn hψ (X := X) hΓ
  exact q X e he hΓ ((hypsHold_append M ρ).mpr ⟨hΦ, _, hf, p X e he hΓ hΦ _ hf⟩) r hr

omit hM hG hρ hps hds in
/-- A formula that a sound rewriting takes to one that holds holds. -/
theorem conv_sound {Γ : List Tree} {Φ : List Term} {φ φ' : Term}
    (d : RwSound M ρ G n Γ Φ φ φ') (p : FmSound M ρ G n Γ Φ φ') : FmSound M ρ G n Γ Φ φ := by
  intro X e he hΓ hΦ r hr
  obtain ⟨r', hr', hr'₂, hr'₁⟩ := d X e he hΓ hΦ r hr
  obtain ⟨h₂, h₁⟩ := p X e he hΓ hΦ r' hr'
  exact ⟨hr'₂.symm.trans h₂, hr'₁.symm.trans h₁⟩

omit hM hG hρ hps hds in
/-- A formula to which a formula that holds rewrites soundly holds. -/
theorem convFrom_sound {Γ : List Tree} {Φ : List Term} {φ φ' : Term}
    (hφ' : typeIn G n Γ φ' = some omega) (d : RwSound M ρ G n Γ Φ φ' φ)
    (p : FmSound M ρ G n Γ Φ φ') : FmSound M ρ G n Γ Φ φ := by
  intro X e he hΓ hΦ r hr
  obtain ⟨f, hf⟩ := compile_of_typeIn hφ' (X := X) hΓ
  obtain ⟨r', hr', hr'₂, hr'₁⟩ := d X e he hΓ hΦ _ hf
  obtain rfl := Option.some_inj.mp (hr.symm.trans hr')
  obtain ⟨h₂, h₁⟩ := p X e he hΓ hΦ _ hf
  exact ⟨hr'₂.trans h₂, hr'₁.trans h₁⟩

/-- Two formulas, each of which holds under the other, are equal. -/
theorem propExt_sound {Γ : List Tree} {Φ : List Term} {α β : Term}
    (hα : typeIn G n Γ α = some omega)
    (p : FmSound M ρ G n Γ (Φ ++ [α]) β) (q : FmSound M ρ G n Γ (Φ ++ [β]) α) :
    FmSound M ρ G n Γ Φ (Term.eq α β) := by
  intro X e he hΓ hΦ r hr
  obtain ⟨α', β', hαβ, F, A, hF, P, hP, rfl⟩ := compile_eq_iff.mp hr
  simp only [List.cons.injEq, and_true] at hαβ
  obtain ⟨rfl, rfl⟩ := hαβ
  obtain ⟨F', hF'⟩ := compile_of_typeIn hα (X := X) hΓ
  obtain rfl : A = omega := (Prod.mk.inj (Option.some_inj.mp (hF.symm.trans hF'))).2
  have hFh : Hom M ρ F X omega := (compile_hom hM hG hρ hps hds _ X e _ hF he).1
  have hPh : Hom M ρ P X omega := (compile_hom hM hG hρ hps hds _ X e _ hP he).1
  -- each holds on the other's pullback of truth
  have key : ∀ {γ δ : Term} {C D : Tree}, Hom M ρ C X omega → Hom M ρ D X omega →
      compile G n γ X e = some (C, omega) → compile G n δ X e = some (D, omega) →
      FmSound M ρ G n Γ (Φ ++ [γ]) δ →
      eval M ρ (comp D (truthIncl C)) = eval M ρ (comp tru (bang (truthEq C))) := by
    intro γ δ C D hC hD hγ hδ pγ
    obtain ⟨hi, hCi⟩ := truthIncl_hom hM hC
    have he₁ := envHom_precomp hM he hi
    obtain ⟨r₁, hr₁, hr₁₂, hr₁₁⟩ := compile_precomp hM hG hρ hps hds hγ he hi (envEq_refl _)
    obtain ⟨r₂, hr₂, hr₂₂, hr₂₁⟩ := compile_precomp hM hG hρ hps hds hδ he hi (envEq_refl _)
    have hH := pγ _ _ he₁ (by simp [precomp, Function.comp_def, hΓ])
      ((hypsHold_append M ρ).mpr ⟨hypsHold_precomp hM hG hρ hps hds hΦ he hi (envEq_refl _),
        r₁, hr₁, hr₁₂, hr₁₁.trans hCi⟩) r₂ hr₂
    exact hr₂₁.symm.trans hH.2
  have hFP := omega_ext hM hFh hPh (key hFh hPh hF hP p) (key hPh hFh hP hF q)
  exact (holds_eq_iff hM hG hρ hps hds he hF hP).mpr hFP

/-- Two functions whose applications to a new variable are equal are equal. -/
theorem funExt_sound {Γ : List Tree} {Φ : List Term} {f g : Term} {a b : Tree}
    (hf : (typeIn G n Γ f).bind expParts = some (a, b))
    (p : FmSound M ρ G n (a :: Γ) (Φ.map weaken1)
      (Term.eq (Term.app (weaken1 f) (Term.var 0)) (Term.app (weaken1 g) (Term.var 0)))) :
    FmSound M ρ G n Γ Φ (Term.eq f g) := by
  intro X e he hΓ hΦ r hr
  obtain ⟨f', g', hfg, F, A, hF, G', hG', rfl⟩ := compile_eq_iff.mp hr
  simp only [List.cons.injEq, and_true] at hfg
  obtain ⟨rfl, rfl⟩ := hfg
  obtain ⟨T, hT, hTab⟩ := Option.bind_eq_some_iff.mp hf
  obtain rfl := expParts_eq_some.mp hTab
  obtain ⟨F', hF'⟩ := compile_of_typeIn hT (X := X) hΓ
  obtain rfl : A = exp a b := (Prod.mk.inj (Option.some_inj.mp (hF.symm.trans hF'))).2
  obtain ⟨hFh, hABt⟩ := compile_hom hM hG hρ hps hds _ X e _ hF he
  have hGh : Hom M ρ G' X (exp a b) := (compile_hom hM hG hρ hps hds _ X e _ hG' he).1
  simp only [isTy_exp, Bool.and_eq_true] at hABt
  have hA := isObj_of_isTy hM hds.2 hρ a hABt.1
  have hB := isObj_of_isTy hM hds.2 hρ b hABt.2
  have hX := he.1
  -- the applications to the new variable, in the extended environment
  have app : ∀ {w : Term} {W : Tree}, compile G n w X e = some (W, exp a b) →
      ∃ W', compile G n (Term.app (weaken1 w) (Term.var 0)) (prod X a) (extEnv X a e) =
        some (comp (ev a b) (pair W' (snd X a)), b) ∧
        eval M ρ W' = eval M ρ (comp W (fst X a)) := fun {w W} hw ↦ by
    obtain ⟨⟨W', B'⟩, hr₁, hr₁₂, hr₁₁⟩ := compile_precomp hM hG hρ hps hds hw he
      (fst_hom hM hX hA) (envEq_refl _)
    obtain rfl : B' = exp a b := hr₁₂
    have hw' := compile_rename w (prod X a) (extEnv X a e) (precomp (fst X a) e) (· + 1) _ hr₁
      fun i hi ↦ by simp [extEnv, precomp]
    exact ⟨W', compile_app_iff.mpr ⟨_, _, rfl, W', a, b, hw', snd X a,
      compile_var_iff.mpr ⟨rfl, rfl⟩, rfl⟩, hr₁₁⟩
  obtain ⟨F₁, hF₁, hF₁v⟩ := app hF
  obtain ⟨G₁, hG₁, hG₁v⟩ := app hG'
  have hext := he.ext hM hA hABt.1
  have hH := p _ _ hext (by simp [extEnv, hΓ, Function.comp_def])
    (hypsHold_weaken1 hM hG hρ hps hds hΦ he hA) _
    (compile_eq_iff.mpr ⟨_, _, rfl, _, b, hF₁, _, hG₁, rfl⟩)
  have heq := (holds_eq_iff hM hG hρ hps hds hext hF₁ hG₁).mp hH
  -- each function is the currying of its evaluation at the new variable
  have hcur : ∀ {W W₁ : Tree}, Hom M ρ W X (exp a b) → eval M ρ W₁ = eval M ρ (comp W (fst X a)) →
      eval M ρ W = eval M ρ (curry X a (comp (ev a b) (pair W₁ (snd X a)))) :=
    fun hW hW₁ ↦ (curry_eta hM hA hB hW).symm.trans
      (eval_op₃_congr 24 rfl rfl (eval_op₂_congr 3 rfl (eval_op₂_congr 9 hW₁.symm rfl)))
  exact (holds_eq_iff hM hG hρ hps hds he hF hG').mpr ((hcur hFh hF₁v).trans
    ((eval_op₃_congr 24 rfl rfl heq).trans (hcur hGh hG₁v).symm))

/-- An instance of a valid theorem, the instances of whose hypotheses hold, holds. -/
theorem apply_sound {E : Array Entry}
    (hE : ∀ (j : ℕ) (a : Thm), (E[j]?).bind Entry.language? = some a → a.Valid M G)
    {Γ : List Tree} {Φ : List Term} {j : ℕ} {a : Thm} (ha : (E[j]?).bind Entry.language? = some a)
    {θ : List Tree}
    {σ : List Term} (hok : instOk G n Γ a θ σ = true)
    (hs : ∀ h ∈ a.hyps, FmSound M ρ G n Γ Φ (instTerm θ σ h)) :
    FmSound M ρ G n Γ Φ (instTerm θ σ a.concl) := by
  intro X e he hΓ hΦ r hr
  simp only [instOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hl, hθ⟩, hσl⟩, hall⟩ := hok
  obtain ⟨rs, hrs, hsnd⟩ := mapM_compile_of_typeIn hΓ σ _ (by simp [hσl]) hall
  have hv := hE j a ha
  refine Thm.Valid.inst hM hG hρ hps hds hv hl hθ he hrs hsnd (fun ψ hψ ↦ ?_) r hr
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hψ
  obtain ⟨⟨fh, Ah⟩, hstd, -⟩ := Option.map_eq_some_iff.mp (hv.2.1 h hh)
  obtain ⟨r', hr', -⟩ := compile_thm_side hM hG hρ hps hds hstd hl hθ he hrs hsnd
  exact ⟨r', hr', hs h hh X e he hΓ hΦ r' hr'⟩

omit hM hG hρ hps hds in
/-- Hypotheses that hold in an environment extended by a variable none of them mentions hold,
lowered, in the environment. -/
theorem hypsHold_lower {Γ' : List Tree} {Φ Φ' : List Term} (hlow : lowerHyps G n Γ' Φ = some Φ')
    {X x B : Tree} {e' : List (Tree × Tree)} (hΓ' : e'.map Prod.snd = Γ')
    (hΦ : HypsHold M ρ G n Φ X ((x, B) :: e')) : HypsHold M ρ G n Φ' X e' := by
  obtain ⟨hΦeq, hty⟩ := lowerHyps_spec hlow
  intro ψ hψ
  obtain ⟨f, hf⟩ := compile_of_typeIn (hty ψ hψ) (X := X) hΓ'
  obtain ⟨r, hr, hH⟩ := hΦ (weaken1 ψ) (by rw [hΦeq]; exact List.mem_map_of_mem hψ)
  have hw := compile_rename ψ X ((x, B) :: e') e' (· + 1) _ hf fun i _ ↦ by simp
  obtain rfl := Option.some_inj.mp (hr.symm.trans hw)
  exact ⟨_, hf, hH⟩

/-- A term in the environment extended by a natural number variable, at an element of the
natural numbers object, is its arrow there after the pairing of the identity with the
element. -/
theorem natAt {X x W B : Tree} {e' : List (Tree × Tree)} {w : Term} (he' : EnvHom M ρ G n X e')
    (hw : compile G n w (prod X nat) (extEnv X nat e') = some (W, B)) (hx : Hom M ρ x X nat) :
    ∃ q, compile G n w X ((x, nat) :: e') = some q ∧
      ResEq M ρ (comp W (pair (idt X) x), B) q :=
  compile_at hM hG hρ hps hds he' isTy_nat hw hx

/-- A term in the environment extended by a natural number variable, at zero, is its arrow there
after the pairing of the identity with zero. -/
theorem natZeroAt {kz : ℕ} (hkz : G.prims[kz]? = some zeroPrim) {X W B : Tree}
    {e' : List (Tree × Tree)} {w : Term} (he' : EnvHom M ρ G n X e')
    (hw : compile G n w (prod X nat) (extEnv X nat e') = some (W, B)) :
    ∃ q, compile G n (Term.subst w (instVar (Term.arr kz [] Term.star))) X e' = some q ∧
      ResEq M ρ (comp W (pair (idt X) (comp zeroN (bang X))), B) q := by
  obtain ⟨q₀, hq₀, hr₀⟩ := natAt hM hG hρ hps hds he' hw
    (comp_hom hM (bang_hom hM he'.1) (zeroN_hom hM))
  obtain ⟨q₁, hq₁, hr₁⟩ := compile_subst hM hG hρ hps hds w X _ q₀ hq₀ e'
    (instVar (Term.arr kz [] Term.star)) he' fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (comp zeroN (bang X), nat) = p := by simpa using hp
        exact ⟨_, compile_zeroT hkz X e', ResEq.refl _⟩
      · exact ⟨p, compile_var_iff.mpr ⟨rfl, by simpa using hp⟩, ResEq.refl p⟩
  exact ⟨q₁, hq₁, hr₀.trans hr₁⟩

/-- A term in the environment extended by a variable of type {lit}`D`, at a term that compiles in
the environment extended instead by a variable of type {lit}`A` to an arrow {lit}`i` from
{lit}`A` to {lit}`D` after the variable, is its arrow after the product of the environment's
object with {lit}`i`. -/
theorem atVar0_compile {X W B A D i : Tree} {e' : List (Tree × Tree)} {w u : Term}
    (he' : EnvHom M ρ G n X e') (hAt : IsTy G n A = true) (hDt : IsTy G n D = true)
    (hi : Hom M ρ i A D) (hw : compile G n w (prod X D) (extEnv X D e') = some (W, B))
    (hu : compile G n u (prod X A) (extEnv X A e') = some (comp i (snd X A), D)) :
    ∃ q, compile G n (Term.subst w (atVar0 u)) (prod X A) (extEnv X A e') = some q ∧
      ResEq M ρ (comp W (pair (fst X A) (comp i (snd X A))), B) q := by
  have hA := hi.isObj_dom
  have hD := hi.isObj_cod
  have hX := he'.1
  have hfst := fst_hom hM hX hA
  have hsc := comp_hom hM (snd_hom hM hX hA) hi
  have hk₁ := pair_hom hM hfst hsc
  obtain ⟨q₀, hq₀, hr₀⟩ := compile_precomp hM hG hρ hps hds hw (he'.ext hM hD hDt) hk₁
    (e' := (comp i (snd X A), D) :: precomp (fst X A) e')
    (envEq_precomp_extEnv hM hX hD (fun p hp ↦ (he'.2 p hp).1) hk₁ (fst_pair hM hfst hsc)
      (snd_pair hM hfst hsc) (envEq_refl _))
  obtain ⟨q₁, hq₁, hr₁⟩ := compile_subst hM hG hρ hps hds w _ _ q₀ hq₀ (extEnv X A e')
    (atVar0 u) (he'.ext hM hA hAt) fun j p hp ↦ by
      rcases j with _ | j
      · obtain rfl : (comp i (snd X A), D) = p := by simpa using hp
        exact ⟨_, hu, ResEq.refl _⟩
      · exact ⟨p, compile_var_iff.mpr ⟨rfl, by simpa [extEnv, precomp] using hp⟩,
          ResEq.refl p⟩
  exact ⟨q₁, hq₁, hr₀.trans hr₁⟩

/-- A term in the environment extended by a natural number variable, at the variable's
successor, is its arrow after the successor on the variable. -/
theorem natSuccAt_compile {ks : ℕ} (hks : G.prims[ks]? = some succPrim) {X W B : Tree}
    {e' : List (Tree × Tree)} {w : Term} (he' : EnvHom M ρ G n X e')
    (hw : compile G n w (prod X nat) (extEnv X nat e') = some (W, B)) :
    ∃ q, compile G n (natSuccAt ks w) (prod X nat) (extEnv X nat e') = some q ∧
      ResEq M ρ (comp W (pair (fst X nat) (comp succ (snd X nat))), B) q :=
  atVar0_compile hM hG hρ hps hds he' isTy_nat isTy_nat (succ_hom hM) hw
    (compile_succT hks (compile_var_iff.mpr ⟨rfl, rfl⟩))

/-- An induction's step at a term's value, in the environment extended by a natural number
variable, is the step's arrow after the parameters paired with the term's arrow. -/
theorem natStepAt {X W S C : Tree} {e' : List (Tree × Tree)} {w s : Term}
    (he' : EnvHom M ρ G n X e') (hCt : IsTy G n C = true)
    (hS : compile G n s (prod X C) (extEnv X C e') = some (S, C))
    (hw : compile G n w (prod X nat) (extEnv X nat e') = some (W, C)) :
    ∃ q, compile G n (Term.subst s (atVar0 w)) (prod X nat) (extEnv X nat e') = some q ∧
      ResEq M ρ (comp S (pair (fst X nat) W), C) q := by
  have hN := isObj_nat (ρ := ρ) hM
  have hX := he'.1
  have hC := isObj_of_isTy hM hds.2 hρ C hCt
  have hê := he'.ext hM hN isTy_nat
  have hfst := fst_hom hM hX hN
  have hWh : Hom M ρ W (prod X nat) C := (compile_hom hM hG hρ hps hds _ _ _ _ hw hê).1
  have hk₂ := pair_hom hM hfst hWh
  obtain ⟨q₂, hq₂, hr₂⟩ := compile_precomp hM hG hρ hps hds hS (he'.ext hM hC hCt) hk₂
    (e' := (W, C) :: precomp (fst X nat) e')
    (envEq_precomp_extEnv hM hX hC (fun p hp ↦ (he'.2 p hp).1) hk₂ (fst_pair hM hfst hWh)
      (snd_pair hM hfst hWh) (envEq_refl _))
  obtain ⟨q₃, hq₃, hr₃⟩ := compile_subst hM hG hρ hps hds s _ _ q₂ hq₂ (extEnv X nat e')
    (atVar0 w) hê fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (W, C) = p := by simpa using hp
        exact ⟨_, hw, ResEq.refl _⟩
      · exact ⟨p, compile_var_iff.mpr ⟨rfl, by simpa [extEnv, precomp] using hp⟩,
          ResEq.refl p⟩
  exact ⟨q₃, hq₃, hr₂.trans hr₃⟩

/-- Induction on the natural numbers, in the form of the uniqueness of recursion, is sound: an
equation, in a context of a natural number variable, whose sides agree at zero and are each, at
a successor, a step of their type applied to their value, holds, under hypotheses that do not
mention the variable. -/
theorem natInd_sound {kz ks : ℕ} (hkz : G.prims[kz]? = some zeroPrim)
    (hks : G.prims[ks]? = some succPrim) {Γ' : List Tree} {Φ Φ' : List Term}
    (hlow : lowerHyps G n Γ' Φ = some Φ') {t u s : Term} {C : Tree}
    (htC : typeIn G n (nat :: Γ') t = some C) (hsC : typeIn G n (C :: Γ') s = some C)
    (p₀ : FmSound M ρ G n Γ' Φ' (Term.eq (Term.subst t (instVar (Term.arr kz [] Term.star)))
      (Term.subst u (instVar (Term.arr kz [] Term.star)))))
    (p₁ : FmSound M ρ G n (nat :: Γ') Φ (Term.eq (natSuccAt ks t) (Term.subst s (atVar0 t))))
    (p₂ : FmSound M ρ G n (nat :: Γ') Φ (Term.eq (natSuccAt ks u) (Term.subst s (atVar0 u)))) :
    FmSound M ρ G n (nat :: Γ') Φ (Term.eq t u) := by
  intro X e he hΓ hΦ r hr
  obtain ⟨t', u', htu, f, A, ht, g, hu, rfl⟩ := compile_eq_iff.mp hr
  simp only [List.cons.injEq, and_true] at htu
  obtain ⟨rfl, rfl⟩ := htu
  have hty := compile_hom hM hG hρ hps hds
  rcases e with _ | ⟨⟨x₀, N⟩, e'⟩
  · simp at hΓ
  simp only [List.map_cons, List.cons.injEq] at hΓ
  obtain ⟨rfl, hΓ'⟩ := hΓ
  have he' : EnvHom M ρ G n X e' := ⟨he.1, fun p hp ↦ he.2 p (List.mem_cons_of_mem _ hp)⟩
  have hx₀ : Hom M ρ x₀ X nat := (he.2 _ List.mem_cons_self).1
  have hN := isObj_nat (ρ := ρ) hM
  have hX := he.1
  have hê : EnvHom M ρ G n (prod X nat) (extEnv X nat e') := he'.ext hM hN isTy_nat
  have hêΓ : (extEnv X nat e').map Prod.snd = nat :: Γ' := by
    simp [extEnv, hΓ', Function.comp_def]
  have hΦ' := hypsHold_lower hlow hΓ' hΦ
  have hΦê : HypsHold M ρ G n Φ (prod X nat) (extEnv X nat e') := by
    rw [(lowerHyps_spec hlow).1]
    exact hypsHold_weaken1 hM hG hρ hps hds hΦ' he' hN
  -- the sides' type, and their arrows in the generic environment
  obtain ⟨f₀, hf₀⟩ := compile_of_typeIn htC (X := X) (e := (x₀, nat) :: e') (by simp [hΓ'])
  obtain rfl : A = C := (Prod.mk.inj (Option.some_inj.mp (ht.symm.trans hf₀))).2
  obtain ⟨F, hF⟩ := compile_retype t X _ _ ht (prod X nat) (extEnv X nat e')
    (by simp [hêΓ, hΓ'])
  obtain ⟨G', hG'⟩ := compile_retype u X _ _ hu (prod X nat) (extEnv X nat e')
    (by simp [hêΓ, hΓ'])
  obtain ⟨hFh, hCt⟩ := hty _ _ _ _ hF hê
  have hGh := (hty _ _ _ _ hG' hê).1
  -- the sides are their generic arrows at the variable
  obtain ⟨q, hq, hrq⟩ := natAt hM hG hρ hps hds he' hF hx₀
  obtain rfl := Option.some_inj.mp (hq.symm.trans ht)
  obtain ⟨q', hq', hrq'⟩ := natAt hM hG hρ hps hds he' hG' hx₀
  obtain rfl := Option.some_inj.mp (hq'.symm.trans hu)
  -- at zero
  obtain ⟨z₁, hz₁, hrz₁⟩ := natZeroAt hM hG hρ hps hds hkz he' hF
  obtain ⟨z₂, hz₂, hrz₂⟩ := natZeroAt hM hG hρ hps hds hkz he' hG'
  have hz₁' := compile_resEq hz₁ hrz₁
  have hz₂' := compile_resEq hz₂ hrz₂
  have h₀ := (holds_eq_iff hM hG hρ hps hds he' hz₁' hz₂').mp
    (p₀ X e' he' hΓ' hΦ' _ (compile_eq_iff.mpr ⟨_, _, rfl, _, _, hz₁', _, hz₂', rfl⟩))
  -- at a successor
  obtain ⟨S, hS⟩ := compile_of_typeIn hsC (X := prod X A) (e := extEnv X A e')
    (by simp [extEnv, hΓ', Function.comp_def])
  have hSh : Hom M ρ S (prod X A) A :=
    (hty _ _ _ _ hS (he'.ext hM (isObj_of_isTy hM hds.2 hρ A hCt) hCt)).1
  have step : ∀ {w : Term} {W : Tree},
      compile G n w (prod X nat) (extEnv X nat e') = some (W, A) →
      FmSound M ρ G n (nat :: Γ') Φ (Term.eq (natSuccAt ks w) (Term.subst s (atVar0 w))) →
      eval M ρ (comp W (pair (fst X nat) (comp succ (snd X nat)))) =
        eval M ρ (comp S (pair (fst X nat) W)) := fun {w W} hw pw ↦ by
    obtain ⟨q₁, hq₁, hr₁⟩ := natSuccAt_compile hM hG hρ hps hds hks he' hw
    obtain ⟨q₃, hq₃, hr₃⟩ := natStepAt hM hG hρ hps hds he' hCt hS hw
    have hq₁' := compile_resEq hq₁ hr₁
    have hq₃' := compile_resEq hq₃ hr₃
    exact hr₁.2.symm.trans (((holds_eq_iff hM hG hρ hps hds hê hq₁' hq₃').mp
      (pw _ _ hê hêΓ hΦê _ (compile_eq_iff.mpr ⟨_, _, rfl, _, _, hq₁', _, hq₃', rfl⟩))).trans
      hr₃.2)
  have hFG := natRec_param_unique hM hX hFh hGh hSh (hrz₁.2.symm.trans (h₀.trans hrz₂.2))
    (step hF p₁) (step hG' p₂)
  exact (holds_eq_iff hM hG hρ hps hds he hq hq').mpr
    (hrq.2.trans ((eval_op₂_congr 3 hFG rfl).trans hrq'.2.symm))

/-- Induction on the natural numbers with an induction hypothesis is sound: a formula, in a
context of a natural number variable, that holds at zero and, where it holds, at the successor,
holds, under hypotheses that do not mention the variable. -/
theorem natIndHyp_sound {kz ks : ℕ} (hkz : G.prims[kz]? = some zeroPrim)
    (hks : G.prims[ks]? = some succPrim) {Γ' : List Tree} {Φ Φ' : List Term}
    (hlow : lowerHyps G n Γ' Φ = some Φ') {φ : Term}
    (hφ : typeIn G n (nat :: Γ') φ = some omega)
    (p₀ : FmSound M ρ G n Γ' Φ' (Term.subst φ (instVar (Term.arr kz [] Term.star))))
    (p₁ : FmSound M ρ G n (nat :: Γ') (Φ ++ [φ]) (natSuccAt ks φ)) :
    FmSound M ρ G n (nat :: Γ') Φ φ := by
  intro X e he hΓ hΦ r hr
  rcases e with _ | ⟨⟨x₀, N⟩, e'⟩
  · simp at hΓ
  simp only [List.map_cons, List.cons.injEq] at hΓ
  obtain ⟨rfl, hΓ'⟩ := hΓ
  have he' : EnvHom M ρ G n X e' := ⟨he.1, fun p hp ↦ he.2 p (List.mem_cons_of_mem _ hp)⟩
  have hx₀ : Hom M ρ x₀ X nat := (he.2 _ List.mem_cons_self).1
  have hN := isObj_nat (ρ := ρ) hM
  have hX := he.1
  have hê : EnvHom M ρ G n (prod X nat) (extEnv X nat e') := he'.ext hM hN isTy_nat
  have hêΓ : (extEnv X nat e').map Prod.snd = nat :: Γ' := by
    simp [extEnv, hΓ', Function.comp_def]
  have hΦ' := hypsHold_lower hlow hΓ' hΦ
  have hΦê : HypsHold M ρ G n Φ (prod X nat) (extEnv X nat e') := by
    rw [(lowerHyps_spec hlow).1]
    exact hypsHold_weaken1 hM hG hρ hps hds hΦ' he' hN
  obtain ⟨F, hF⟩ := compile_of_typeIn hφ (X := prod X nat) hêΓ
  have hFh : Hom M ρ F (prod X nat) omega := (compile_hom hM hG hρ hps hds _ _ _ _ hF hê).1
  -- at zero
  obtain ⟨z, hz, hrz⟩ := natZeroAt hM hG hρ hps hds hkz he' hF
  have h₀ := hrz.2.symm.trans (p₀ X e' he' hΓ' hΦ' _ hz).2
  -- at the successor, on the pullback of truth along the formula
  obtain ⟨hi, hFi⟩ := truthIncl_hom hM hFh
  have hE₁ := envHom_precomp hM hê hi
  have hE₁Γ : (precomp (truthIncl F) (extEnv X nat e')).map Prod.snd = nat :: Γ' := by
    simp [precomp, Function.comp_def, ← hêΓ]
  obtain ⟨r₁, hr₁, hr₁₂, hr₁₁⟩ := compile_precomp hM hG hρ hps hds hF hê hi (envEq_refl _)
  have hH₁ : HypsHold M ρ G n (Φ ++ [φ]) (truthEq F)
      (precomp (truthIncl F) (extEnv X nat e')) :=
    (hypsHold_append M ρ).mpr ⟨hypsHold_precomp hM hG hρ hps hds hΦê hê hi (envEq_refl _),
      r₁, hr₁, hr₁₂, hr₁₁.trans hFi⟩
  obtain ⟨q₁, hq₁, hrq₁⟩ := natSuccAt_compile hM hG hρ hps hds hks he' hF
  obtain ⟨q₂, hq₂, -, hq₂₁⟩ :=
    compile_precomp hM hG hρ hps hds (compile_resEq hq₁ hrq₁) hê hi (envEq_refl _)
  have h₁ := (eval_op₂_congr 3 hrq₁.2.symm rfl).trans
    (hq₂₁.symm.trans (p₁ _ _ hE₁ hE₁Γ hH₁ q₂ hq₂).2)
  have hFtrue := truth_of_natInd hM hX hFh h₀ h₁
  -- the formula at the variable
  obtain ⟨q, hq, hrq⟩ := natAt hM hG hρ hps hds he' hF hx₀
  obtain rfl := Option.some_inj.mp (hq.symm.trans hr)
  exact ⟨hrq.1, hrq.2.trans ((eval_op₂_congr 3 hFtrue rfl).trans
    (truth_comp hM (pair_hom hM (idt_hom hM hX) hx₀)))⟩

/-- A term in a context of a rose tree, at a construction from the next variable's label and the
innermost variable's children, compiles in their context's environment to its arrow after the
structure map, which, with the folds, is an initial algebra. -/
theorem roseNodeAt_compile {kn : ℕ} {r a : Tree} {F : Tree → Tree}
    (hr : roseParts r = some (a, F))
    (hkn : (G.prims[kn]? = some nodePrim ∧ r = rose) ∨
      (G.prims[kn]? = some lnodePrim ∧ r = lrose a))
    (hrt : IsTy G n r = true) {t : Term} {T C : Tree}
    (ht : compile G n t r [(idt r, r)] = some (T, C)) :
    ∃ nd q, Hom M ρ nd (prod a (list r)) r ∧
      (∀ {S c h}, Hom M ρ S (prod a (list c)) c → Hom M ρ h r c →
        eval M ρ (comp h nd) = eval M ρ (comp S (prodMapRight a (listMap h))) →
        eval M ρ h = eval M ρ (F S)) ∧
      (∀ {S c}, Hom M ρ S (prod a (list c)) c → Hom M ρ (F S) r c ∧
        eval M ρ (comp (F S) nd) = eval M ρ (comp S (prodMapRight a (listMap (F S))))) ∧
      compile G n (roseNodeAt kn r a t) (prod a (list r)) (stdEnv [list r, a]) = some q ∧
      ResEq M ρ (comp T nd, C) q := by
  have hat := isTy_of_roseParts hr hrt
  have hA := isObj_of_isTy hM hds.2 hρ a hat
  have hR := isObj_of_isTy hM hds.2 hρ r hrt
  have hLr := isObj_list hM hR
  have hpv : compile G n (Term.pair (Term.var 1) (Term.var 0)) (prod a (list r))
      (stdEnv [list r, a]) = some (pair (comp (idt a) (fst a (list r))) (snd a (list r)),
        prod a (list r)) :=
    compile_pair_iff.mpr ⟨_, _, _, _, _, _, rfl, compile_var_iff.mpr ⟨rfl, rfl⟩,
      compile_var_iff.mpr ⟨rfl, rfl⟩, rfl⟩
  -- the structure map, by the construction's primitive
  obtain ⟨nd, hnd, huniq, hfold, hnode⟩ : ∃ nd, Hom M ρ nd (prod a (list r)) r ∧
      (∀ {S c h}, Hom M ρ S (prod a (list c)) c → Hom M ρ h r c →
        eval M ρ (comp h nd) = eval M ρ (comp S (prodMapRight a (listMap h))) →
        eval M ρ h = eval M ρ (F S)) ∧
      (∀ {S c}, Hom M ρ S (prod a (list c)) c → Hom M ρ (F S) r c ∧
        eval M ρ (comp (F S) nd) = eval M ρ (comp S (prodMapRight a (listMap (F S))))) ∧
      compile G n (Term.arr kn (if r = rose then [] else [a])
        (Term.pair (Term.var 1) (Term.var 0))) (prod a (list r)) (stdEnv [list r, a]) =
        some (comp nd (pair (comp (idt a) (fst a (list r))) (snd a (list r))), r) := by
    rcases hkn with ⟨hkn, rfl⟩ | ⟨hkn, rfl⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp
        ((show roseParts rose = some (nat, roseRec) by simp [roseParts]).symm.trans hr))
      refine ⟨node, node_hom hM, fun hS hh h₁ ↦ roseRec_unique hM hS hh h₁,
        fun hS ↦ ⟨roseRec_hom hM hS, roseRec_node hM hS⟩, ?_⟩
      simp only [↓reduceIte]
      exact compile_arr_iff.mpr ⟨_, rfl, nodePrim, hkn, _, hpv, rfl, rfl, rfl⟩
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some_inj.mp ((roseParts_lrose a).symm.trans hr))
      refine ⟨lnode a, lnode_hom hM hA, fun hS hh h₁ ↦ lroseRec_unique hM hA hS hh h₁,
        fun hS ↦ ⟨lroseRec_hom hM hA hS, lroseRec_node hM hA hS⟩, ?_⟩
      simp only [lrose_ne_rose, ↓reduceIte]
      exact compile_arr_iff.mpr ⟨_, rfl, lnodePrim, hkn, _, hpv, rfl, by simp [hat], rfl⟩
  -- the term at the construction
  have hE : EnvHom M ρ G n (prod a (list r)) (stdEnv [list r, a]) :=
    (show EnvHom M ρ G n a [(idt a, a)] from ⟨hA, by simpa using ⟨idt_hom hM hA, hat⟩⟩).ext hM
      hLr (by simpa [isTy_list] using hrt)
  have hfA := fst_hom hM hA hLr
  have hpvh := pair_hom hM (comp_hom hM hfA (idt_hom hM hA)) (snd_hom hM hA hLr)
  have hk := comp_hom hM hpvh hnd
  have hEr : EnvHom M ρ G n r [(idt r, r)] := ⟨hR, by simpa using ⟨idt_hom hM hR, hrt⟩⟩
  obtain ⟨q₀, hq₀, hr₀⟩ := compile_precomp hM hG hρ hps hds ht hEr hk
    (e' := [(comp nd (pair (comp (idt a) (fst a (list r))) (snd a (list r))), r)])
    fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (comp (idt r) (comp nd (pair (comp (idt a) (fst a (list r)))
          (snd a (list r)))), r) = p := by simpa [precomp] using hp
        exact ⟨_, rfl, rfl, (idt_comp hM hk).symm⟩
      · simp [precomp] at hp
  obtain ⟨q₁, hq₁, hr₁⟩ := compile_subst hM hG hρ hps hds t _ _ q₀ hq₀ (stdEnv [list r, a])
    (instVar (Term.arr kn (if r = rose then [] else [a]) (Term.pair (Term.var 1) (Term.var 0))))
    hE fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (comp nd (pair (comp (idt a) (fst a (list r))) (snd a (list r))), r) = p := by
          simpa using hp
        exact ⟨_, hnode, ResEq.refl _⟩
      · simp at hp
  refine ⟨nd, q₁, hnd, huniq, hfold, hq₁, ResEq.trans (r₂ := (comp T (comp nd (pair (comp (idt a)
    (fst a (list r))) (snd a (list r)))), C)) ⟨rfl, ?_⟩ (hr₀.trans hr₁)⟩
  -- the pairing of the projections is the identity
  exact eval_op₂_congr 3 rfl ((eval_op₂_congr 3 rfl ((eval_op₂_congr 9 (idt_comp hM hfA) rfl).trans
    (pair_fst_snd hM hA hLr))).trans (comp_idt hM hnd))

/-- The list of the values at the children of a term in a context of a rose tree compiles, in
the context of a label and the children, to the term's arrow's action on the list after the
children's projection. -/
theorem roseMapAt_compile {kl kc : ℕ} (hkl : G.prims[kl]? = some nilPrim)
    (hkc : G.prims[kc]? = some consPrim) {r a : Tree} (hrt : IsTy G n r = true)
    {t : Term} {T C : Tree} (ht : compile G n t r [(idt r, r)] = some (T, C)) :
    ∃ q, compile G n (roseMapAt kl kc C t) (prod a (list r)) (stdEnv [list r, a]) = some q ∧
      ResEq M ρ (comp (listMap T) (snd a (list r)), list C) q := by
  have hR := isObj_of_isTy hM hds.2 hρ r hrt
  have hEr : EnvHom M ρ G n r [(idt r, r)] := ⟨hR, by simpa using ⟨idt_hom hM hR, hrt⟩⟩
  obtain ⟨hT, hCt⟩ := compile_hom hM hG hρ hps hds _ _ _ _ ht hEr
  have hLC := isObj_list hM (isObj_of_isTy hM hds.2 hρ C hCt)
  have hf := fst_hom hM hR hLC
  -- the term, weakened past the accumulated list, at the element
  obtain ⟨⟨Q, C'⟩, hq₀, hC', hQ⟩ := compile_precomp hM hG hρ hps hds ht hEr hf
    (e' := [(fst r (list C), r)]) fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (comp (idt r) (fst r (list C)), r) = p := by simpa [precomp] using hp
        exact ⟨_, rfl, rfl, (idt_comp hM hf).symm⟩
      · simp [precomp] at hp
  have hCC : C = C' := hC'.symm
  subst hCC
  have hw : compile G n (weaken1 t) (prod r (list C))
      [(snd r (list C), list C), (fst r (list C), r)] = some (Q, C) :=
    compile_rename t _ _ _ (· + 1) _ hq₀ fun i hi ↦ by
      rcases i with _ | j
      · rfl
      · simp at hi
  refine ⟨_, compile_listRec_iff.mpr ⟨_, _, _, rfl, snd a (list r), r,
    compile_var_iff.mpr ⟨rfl, rfl⟩, _, _, compile_nilT hkl hCt one [], _,
    compile_consT hkc hCt (compile_pair_iff.mpr ⟨_, _, _, _, _, _, rfl, hw,
      compile_var_iff.mpr ⟨rfl, rfl⟩, rfl⟩), rfl⟩, rfl, ?_⟩
  exact eval_op₂_congr 3 ((eval_op₃_congr 36 rfl rfl (eval_op₂_congr 3 rfl
    (eval_op₂_congr 9 hQ rfl))).trans (eval_listMap hM hT).symm) rfl

/-- Induction on rose trees, in the form of the uniqueness of the fold, is sound: two terms in a
context of a rose tree alone, each of which at a construction is the step at the label and the
list of its values at the children, are equal. -/
theorem roseInd_sound {kn kl kc : ℕ} {r a : Tree} {F : Tree → Tree}
    (hr : roseParts r = some (a, F))
    (hkn : (G.prims[kn]? = some nodePrim ∧ r = rose) ∨
      (G.prims[kn]? = some lnodePrim ∧ r = lrose a))
    (hkl : G.prims[kl]? = some nilPrim) (hkc : G.prims[kc]? = some consPrim)
    {Φ : List Term} {t u s : Term} {C : Tree} (htC : typeIn G n [r] t = some C)
    (huC : typeIn G n [r] u = some C) (hsC : typeIn G n [list C, a] s = some C)
    (p₁ : FmSound M ρ G n [list r, a] [] (Term.eq (roseNodeAt kn r a t)
      (Term.subst s (atVar0 (roseMapAt kl kc C t)))))
    (p₂ : FmSound M ρ G n [list r, a] [] (Term.eq (roseNodeAt kn r a u)
      (Term.subst s (atVar0 (roseMapAt kl kc C u))))) :
    FmSound M ρ G n [r] Φ (Term.eq t u) := by
  intro X e he hΓ _ q hq
  obtain ⟨t', u', htu, f, A, ht, g, hu, rfl⟩ := compile_eq_iff.mp hq
  simp only [List.cons.injEq, and_true] at htu
  obtain ⟨rfl, rfl⟩ := htu
  have hty := compile_hom hM hG hρ hps hds
  rcases e with _ | ⟨⟨x₀, R⟩, _ | ⟨p, e⟩⟩
  · simp at hΓ
  swap
  · simp at hΓ
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hΓ
  subst hΓ
  obtain ⟨hx₀, hrt⟩ := he.2 _ List.mem_cons_self
  have hat := isTy_of_roseParts hr hrt
  have hA := isObj_of_isTy hM hds.2 hρ a hat
  have hR := isObj_of_isTy hM hds.2 hρ R hrt
  have hLr := isObj_list hM hR
  have hEr : EnvHom M ρ G n R [(idt R, R)] := ⟨hR, by simpa using ⟨idt_hom hM hR, hrt⟩⟩
  -- the sides' arrows in the environment of the tree
  obtain ⟨T, hT⟩ := compile_of_typeIn htC (X := R) (e := [(idt R, R)]) rfl
  obtain ⟨U, hU⟩ := compile_of_typeIn huC (X := R) (e := [(idt R, R)]) rfl
  obtain ⟨hTh, hCt⟩ := hty _ _ _ _ hT hEr
  have hUh := (hty _ _ _ _ hU hEr).1
  have hLC := isObj_list hM (isObj_of_isTy hM hds.2 hρ C hCt)
  have hEa : EnvHom M ρ G n a [(idt a, a)] := ⟨hA, by simpa using ⟨idt_hom hM hA, hat⟩⟩
  have hEs : EnvHom M ρ G n (prod a (list C)) (stdEnv [list C, a]) :=
    hEa.ext hM hLC (by simpa [isTy_list] using hCt)
  have hE : EnvHom M ρ G n (prod a (list R)) (stdEnv [list R, a]) :=
    hEa.ext hM hLr (by simpa [isTy_list] using hrt)
  obtain ⟨S, hS⟩ := compile_of_typeIn hsC (X := prod a (list C)) (map_snd_stdEnv _)
  have hSh : Hom M ρ S (prod a (list C)) C := (hty _ _ _ _ hS hEs).1
  have hfA := comp_hom hM (fst_hom hM hA hLr) (idt_hom hM hA)
  -- each side is the fold of the step
  have side : ∀ {w : Term} {W : Tree}, compile G n w R [(idt R, R)] = some (W, C) →
      FmSound M ρ G n [list R, a] [] (Term.eq (roseNodeAt kn R a w)
        (Term.subst s (atVar0 (roseMapAt kl kc C w)))) → eval M ρ W = eval M ρ (F S) := by
    intro w W hw pw
    have hWh := (hty _ _ _ _ hw hEr).1
    have hmap := listMap_hom hM hWh
    obtain ⟨nd, q₁, -, huniq, -, hq₁, hrq₁⟩ := roseNodeAt_compile hM hG hρ hps hds hr hkn hrt hw
    obtain ⟨q₂, hq₂, hrq₂⟩ := roseMapAt_compile hM hG hρ hps hds hkl hkc (a := a) hrt hw
    have hm := comp_hom hM (snd_hom hM hA hLr) hmap
    have hk := pair_hom hM hfA hm
    obtain ⟨q₃, hq₃, hrq₃⟩ := compile_precomp hM hG hρ hps hds hS hEs hk
      (e' := [(comp (listMap W) (snd a (list R)), list C), (comp (idt a) (fst a (list R)), a)])
      (envEq_precomp_extEnv hM hA hLC (fun p hp ↦ by
        obtain rfl : p = (idt a, a) := by simpa using hp
        exact idt_hom hM hA) hk (fst_pair hM hfA hm) (snd_pair hM hfA hm) fun i p hp ↦ by
          rcases i with _ | j
          · obtain rfl : (comp (idt a) (comp (idt a) (fst a (list R))), a) = p := by
              simpa [precomp] using hp
            exact ⟨_, rfl, rfl, (idt_comp hM hfA).symm⟩
          · simp [precomp] at hp)
    obtain ⟨q₄, hq₄, hrq₄⟩ := compile_subst hM hG hρ hps hds s _ _ q₃ hq₃ (stdEnv [list R, a])
      (atVar0 (roseMapAt kl kc C w)) hE fun i p hp ↦ by
        rcases i with _ | _ | j
        · obtain rfl : (comp (listMap W) (snd a (list R)), list C) = p := by simpa using hp
          exact ⟨q₂, hq₂, hrq₂⟩
        · obtain rfl : (comp (idt a) (fst a (list R)), a) = p := by simpa using hp
          exact ⟨_, compile_var_iff.mpr ⟨rfl, rfl⟩, ResEq.refl _⟩
        · simp at hp
    have hq₁' := compile_resEq hq₁ hrq₁
    have hr₄ := hrq₃.trans hrq₄
    have hq₄' := compile_resEq hq₄ hr₄
    have hH := (holds_eq_iff hM hG hρ hps hds hE hq₁' hq₄').mp (pw _ _ hE (map_snd_stdEnv _)
      (fun _ h ↦ by simp at h) _ (compile_eq_iff.mpr ⟨_, _, rfl, _, _, hq₁', _, hq₄', rfl⟩))
    refine huniq hSh hWh (hrq₁.2.symm.trans (hH.trans (hr₄.2.trans (eval_op₂_congr 3 rfl ?_))))
    exact (eval_op₂_congr 9 (idt_comp hM (fst_hom hM hA hLr)) rfl).trans
      (eval_prodMapRight a hmap).symm
  have hTU := (side hT p₁).trans (side hU p₂).symm
  -- the sides at the tree
  have hEx : ∀ {W : Tree} {w : Term}, compile G n w R [(idt R, R)] = some (W, C) →
      ∃ q, compile G n w X [(x₀, R)] = some q ∧ ResEq M ρ (comp W x₀, C) q := fun hw ↦
    compile_precomp hM hG hρ hps hds hw hEr hx₀ fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (comp (idt R) x₀, R) = p := by simpa [precomp] using hp
        exact ⟨_, rfl, rfl, (idt_comp hM hx₀).symm⟩
      · simp [precomp] at hp
  obtain ⟨q₅, hq₅, hr₅⟩ := hEx hT
  obtain rfl := Option.some_inj.mp (hq₅.symm.trans ht)
  obtain ⟨q₆, hq₆, hr₆⟩ := hEx hU
  obtain rfl := Option.some_inj.mp (hq₆.symm.trans hu)
  exact (holds_eq_iff hM hG hρ hps hds he ht hu).mpr
    (hr₅.2.trans ((eval_op₂_congr 3 hTU rfl).trans hr₆.2.symm))

/-- Induction on rose trees with an induction hypothesis is sound: a formula in a context of a rose
tree alone that holds at a construction, under the hypothesis that it holds at each child,
holds. -/
theorem roseIndHyp_sound {kn kl kc : ℕ} {r a : Tree} {F : Tree → Tree}
    (hr : roseParts r = some (a, F))
    (hkn : (G.prims[kn]? = some nodePrim ∧ r = rose) ∨
      (G.prims[kn]? = some lnodePrim ∧ r = lrose a))
    (hkl : G.prims[kl]? = some nilPrim) (hkc : G.prims[kc]? = some consPrim)
    {Φ : List Term} {φ : Term} (hφ : typeIn G n [r] φ = some omega)
    (p₁ : FmSound M ρ G n [list r, a] [roseHyp kl kc φ] (roseNodeAt kn r a φ)) :
    FmSound M ρ G n [r] Φ φ := by
  intro X e he hΓ _ q hq
  have hty := compile_hom hM hG hρ hps hds
  rcases e with _ | ⟨⟨x₀, R⟩, _ | ⟨p, e⟩⟩
  · simp at hΓ
  swap
  · simp at hΓ
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hΓ
  subst hΓ
  obtain ⟨hx₀, hrt⟩ := he.2 _ List.mem_cons_self
  have hat := isTy_of_roseParts hr hrt
  have hA := isObj_of_isTy hM hds.2 hρ a hat
  have hR := isObj_of_isTy hM hds.2 hρ R hrt
  have hLr := isObj_list hM hR
  have hEr : EnvHom M ρ G n R [(idt R, R)] := ⟨hR, by simpa using ⟨idt_hom hM hR, hrt⟩⟩
  have hEa : EnvHom M ρ G n a [(idt a, a)] := ⟨hA, by simpa using ⟨idt_hom hM hA, hat⟩⟩
  have hE : EnvHom M ρ G n (prod a (list R)) (stdEnv [list R, a]) :=
    hEa.ext hM hLr (by simpa [isTy_list] using hrt)
  -- the formula's arrow, and truth's, in the environment of the tree
  obtain ⟨T, hT⟩ := compile_of_typeIn hφ (X := R) (e := [(idt R, R)]) rfl
  have hTh : Hom M ρ T R omega := (hty _ _ _ _ hT hEr).1
  have hs : compile G n Term.star R [(idt R, R)] = some (bang R, one) :=
    compile_star_iff.mpr ⟨rfl, rfl⟩
  have htt : compile G n (Term.eq Term.star Term.star) R [(idt R, R)] =
      some (comp (chi (diag one)) (pair (bang R) (bang R)), omega) :=
    compile_eq_iff.mpr ⟨_, _, rfl, _, _, hs, _, hs, rfl⟩
  have hU := (hty _ _ _ _ htt hEr).1
  have hUv := ((holds_eq_iff hM hG hρ hps hds hEr hs hs).mpr rfl).2
  -- the structure map with its folds, the formula at a construction and the values at the children
  obtain ⟨nd, q₁, hnd, huniq, hfold, hq₁, hrq₁⟩ :=
    roseNodeAt_compile hM hG hρ hps hds hr hkn hrt hT
  obtain ⟨q₂, hq₂, hrq₂⟩ := roseMapAt_compile hM hG hρ hps hds hkl hkc (a := a) hrt hT
  obtain ⟨q₃, hq₃, hrq₃⟩ := roseMapAt_compile hM hG hρ hps hds hkl hkc (a := a) hrt htt
  -- the environment of a label and a list of elements of the formula's pullback of truth
  obtain ⟨hi, hTi⟩ := truthIncl_hom hM hTh
  have hLi := listMap_hom hM hi
  have hk := prodMapRight_hom hM a hA hLi
  have hE₁ := envHom_precomp hM hE hk
  have hE₁Γ : (precomp (prodMapRight a (listMap (truthIncl T))) (stdEnv [list R, a])).map
      Prod.snd = [list R, a] := by
    simp only [precomp, List.map_map, Function.comp_def]
    exact map_snd_stdEnv _
  -- the children's values there are the elements' values, truth's for both lists
  have hS := hi.isObj_dom
  have hLS := isObj_list hM hS
  have hsS := snd_hom hM hA hLS
  have hsk : eval M ρ (comp (snd a (list R)) (prodMapRight a (listMap (truthIncl T)))) =
      eval M ρ (comp (listMap (truthIncl T)) (snd a (list (truthEq T)))) :=
    (eval_op₂_congr 3 rfl (eval_prodMapRight a hLi)).trans
      (snd_pair hM (fst_hom hM hA hLS) (comp_hom hM hsS hLi))
  have hvals : ∀ {V : Tree}, Hom M ρ V R omega →
      eval M ρ (comp V (truthIncl T)) = eval M ρ (comp tru (bang (truthEq T))) →
      eval M ρ (comp (comp (listMap V) (snd a (list R)))
        (prodMapRight a (listMap (truthIncl T)))) =
        eval M ρ (comp (listMap (comp tru (bang (truthEq T)))) (snd a (list (truthEq T)))) := by
    intro V hV hVi
    have hLV := listMap_hom hM hV
    refine (comp_assoc hM hk (snd_hom hM hA hLr) hLV).symm.trans
      ((eval_op₂_congr 3 rfl hsk).trans ((comp_assoc hM hsS hLi hLV).trans
        (eval_op₂_congr 3 ((listMap_comp hM hi hV).trans ?_) rfl)))
    exact listMap_congr hM (comp_hom hM hi hV) (truth_hom hM hS) hVi
  obtain ⟨r₂, hr₂, hr₂₂, hr₂₁⟩ :=
    compile_precomp hM hG hρ hps hds (compile_resEq hq₂ hrq₂) hE hk (envEq_refl _)
  obtain ⟨r₃, hr₃, hr₃₂, hr₃₁⟩ :=
    compile_precomp hM hG hρ hps hds (compile_resEq hq₃ hrq₃) hE hk (envEq_refl _)
  have hr₂' : compile G n (roseMapAt kl kc omega φ) _ _ = some (r₂.1, list omega) :=
    hr₂.trans (congrArg some (Prod.ext rfl hr₂₂))
  have hr₃' : compile G n (roseMapAt kl kc omega (Term.eq Term.star Term.star)) _ _ =
      some (r₃.1, list omega) :=
    hr₃.trans (congrArg some (Prod.ext rfl hr₃₂))
  have hH : HypsHold M ρ G n [roseHyp kl kc φ] (prod a (list (truthEq T)))
      (precomp (prodMapRight a (listMap (truthIncl T))) (stdEnv [list R, a])) := fun ψ hψ ↦ by
    obtain rfl : ψ = roseHyp kl kc φ := by simpa using hψ
    refine ⟨_, compile_eq_iff.mpr ⟨_, _, rfl, _, _, hr₂', _, hr₃', rfl⟩,
      (holds_eq_iff hM hG hρ hps hds hE₁ hr₂' hr₃').mpr ?_⟩
    refine hr₂₁.trans ((eval_op₂_congr 3 hrq₂.2 rfl).trans ((hvals hTh hTi).trans
      (Eq.trans ?_ ((eval_op₂_congr 3 hrq₃.2 rfl).symm.trans hr₃₁.symm))))
    exact (hvals hU ((eval_op₂_congr 3 hUv rfl).trans (truth_comp hM hi))).symm
  -- the formula at a construction from such a label and list
  obtain ⟨q₄, hq₄, hq₄₂, hq₄₁⟩ :=
    compile_precomp hM hG hρ hps hds (compile_resEq hq₁ hrq₁) hE hk (envEq_refl _)
  have h₁ := hq₄₁.symm.trans (p₁ _ _ hE₁ hE₁Γ hH q₄ hq₄).2
  have hTtrue := truth_of_roseInd hM hA hnd hfold huniq hTh
    ((eval_op₂_congr 3 hrq₁.2.symm rfl).trans h₁)
  -- the formula at the tree
  obtain ⟨q₅, hq₅, hr₅⟩ := compile_precomp hM hG hρ hps hds hT hEr hx₀
    (e' := [(x₀, R)]) fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (comp (idt R) x₀, R) = p := by simpa [precomp] using hp
        exact ⟨_, rfl, rfl, (idt_comp hM hx₀).symm⟩
      · simp [precomp] at hp
  obtain rfl := Option.some_inj.mp (hq₅.symm.trans hq)
  exact ⟨hr₅.1, hr₅.2.trans ((eval_op₂_congr 3 hTtrue rfl).trans (truth_comp hM hx₀))⟩

/-- Case analysis on a coproduct is sound: a formula, in a context of a variable of a coproduct
type, that holds at the left injection of a variable of the first summand and at the right
injection of a variable of the second holds, under hypotheses that do not mention the
variable. -/
theorem coprodInd_sound {kl kr : ℕ} (hkl : G.prims[kl]? = some inlPrim)
    (hkr : G.prims[kr]? = some inrPrim) {a b : Tree} {Γ' : List Tree} {Φ Φ' : List Term}
    (hlow : lowerHyps G n Γ' Φ = some Φ') {φ : Term}
    (hφ : typeIn G n (coprod a b :: Γ') φ = some omega)
    (p₀ : FmSound M ρ G n (a :: Γ') Φ (Term.subst φ (atVar0 (Term.arr kl [a, b] (Term.var 0)))))
    (p₁ : FmSound M ρ G n (b :: Γ') Φ (Term.subst φ (atVar0 (Term.arr kr [a, b] (Term.var 0))))) :
    FmSound M ρ G n (coprod a b :: Γ') Φ φ := by
  intro X e he hΓ hΦ r hr
  rcases e with _ | ⟨⟨x₀, D⟩, e'⟩
  · simp at hΓ
  simp only [List.map_cons, List.cons.injEq] at hΓ
  obtain ⟨rfl, hΓ'⟩ := hΓ
  have he' : EnvHom M ρ G n X e' := ⟨he.1, fun p hp ↦ he.2 p (List.mem_cons_of_mem _ hp)⟩
  obtain ⟨hx₀, hDt⟩ := he.2 _ List.mem_cons_self
  have hab := hDt
  rw [isTy_coprod, Bool.and_eq_true] at hab
  obtain ⟨hat, hbt⟩ := hab
  have hA := isObj_of_isTy hM hds.2 hρ a hat
  have hB := isObj_of_isTy hM hds.2 hρ b hbt
  have hX := he.1
  have hP := isObj_prod hM hX (isObj_coprod hM hA hB)
  have hΦ' := hypsHold_lower hlow hΓ' hΦ
  obtain ⟨F, hF⟩ := compile_of_typeIn hφ (X := prod X (coprod a b))
    (by simp [extEnv, hΓ', Function.comp_def] : (extEnv X (coprod a b) e').map Prod.snd = _)
  have hFh : Hom M ρ F (prod X (coprod a b)) omega :=
    (compile_hom hM hG hρ hps hds _ _ _ _ hF (he'.ext hM (isObj_coprod hM hA hB) hDt)).1
  -- the formula holds at each injection, where it is its arrow after the product of the
  -- environment's object with the injection
  have side : ∀ {k c i}, IsTy G n c = true → Hom M ρ i c (coprod a b) →
      compile G n (Term.arr k [a, b] (Term.var 0)) (prod X c) (extEnv X c e') =
        some (comp i (snd X c), coprod a b) →
      FmSound M ρ G n (c :: Γ') Φ (Term.subst φ (atVar0 (Term.arr k [a, b] (Term.var 0)))) →
      eval M ρ (comp F (pair (fst X c) (comp i (snd X c)))) =
        eval M ρ (comp (comp tru (bang (prod X (coprod a b))))
          (pair (fst X c) (comp i (snd X c)))) := by
    intro k c i hct hi hu p
    have hC := hi.isObj_dom
    obtain ⟨q, hq, hrq⟩ := atVar0_compile hM hG hρ hps hds he' hct hDt hi hF hu
    have hΦc : HypsHold M ρ G n Φ (prod X c) (extEnv X c e') := by
      rw [(lowerHyps_spec hlow).1]
      exact hypsHold_weaken1 hM hG hρ hps hds hΦ' he' hC
    have hH := p _ _ (he'.ext hM hC hct) (by simp [extEnv, hΓ', Function.comp_def]) hΦc q hq
    exact hrq.2.symm.trans (hH.2.trans (truth_comp hM (pair_hom hM (fst_hom hM hX hC)
      (comp_hom hM (snd_hom hM hX hC) hi))).symm)
  have hθ : [a, b].all (IsTy G n) = true := by simp [hat, hbt]
  have hFtrue := prod_coprod_ext hM hX hA hB hFh
    (comp_hom hM (bang_hom hM hP) (tru_hom hM))
    (side hat (inl_hom hM hA hB) (compile_arr_iff.mpr ⟨_, rfl, inlPrim, hkl, snd X a,
      compile_var_iff.mpr ⟨rfl, rfl⟩, rfl, hθ, rfl⟩) p₀)
    (side hbt (inr_hom hM hA hB) (compile_arr_iff.mpr ⟨_, rfl, inrPrim, hkr, snd X b,
      compile_var_iff.mpr ⟨rfl, rfl⟩, rfl, hθ, rfl⟩) p₁)
  -- the formula at the variable
  obtain ⟨q, hq, hrq⟩ := compile_at hM hG hρ hps hds he' hDt hF hx₀
  obtain rfl := Option.some_inj.mp (hq.symm.trans hr)
  exact ⟨hrq.1, hrq.2.trans ((eval_op₂_congr 3 hFtrue rfl).trans
    (truth_comp hM (pair_hom hM (idt_hom hM hX) hx₀)))⟩

/-- Induction on a quotient is sound: a formula in a context whose innermost variable is of the
codomain of a primitive arrow that is a coequalizer's projection holds when it holds at the
projection's image of a variable of its domain, under hypotheses that do not mention the
variable, since the product of the environment's object with the projection is an
epimorphism. -/
theorem quotInd_sound {kq : ℕ} {p : Prim} (hp : G.prims[kq]? = some p) {f g : Tree}
    (hfg : p.coeqParts = some (f, g)) {θ : List Tree} (hl : θ.length = p.arity)
    (hθ : θ.all (IsTy G n) = true) {Γ' : List Tree} {Φ Φ' : List Term}
    (hlow : lowerHyps G n Γ' Φ = some Φ') {φ : Term}
    (hφ : typeIn G n (PartialHorn.subst θ p.cod :: Γ') φ = some omega)
    (p₀ : FmSound M ρ G n (PartialHorn.subst θ p.dom :: Γ') Φ
      (Term.subst φ (atVar0 (Term.arr kq θ (Term.var 0))))) :
    FmSound M ρ G n (PartialHorn.subst θ p.cod :: Γ') Φ φ := by
  intro X e he hΓ hΦ r hr
  rcases e with _ | ⟨⟨x₀, D⟩, e'⟩
  · simp at hΓ
  simp only [List.map_cons, List.cons.injEq] at hΓ
  obtain ⟨rfl, hΓ'⟩ := hΓ
  have he' : EnvHom M ρ G n X e' := ⟨he.1, fun p hp ↦ he.2 p (List.mem_cons_of_mem _ hp)⟩
  obtain ⟨hx₀, hDt⟩ := he.2 _ List.mem_cons_self
  obtain ⟨har, hdt, -⟩ := hG.prims kq p hp
  have hBt := isTy_subst hl hθ _ hdt
  have hi := hps kq p hp θ hl hθ
  -- the projection coequalizes two parallel arrows, and the type is their coequalizer
  have hparts := hfg
  unfold Prim.coeqParts at hparts
  split at hparts
  rotate_left
  · simp at hparts
  rename_i f₀ g₀ hch
  split at hparts
  rotate_left
  · simp at hparts
  rename_i a b c d hf₀ hg₀
  split_ifs at hparts with hpa
  obtain ⟨rfl, rfl⟩ : f₀ = f ∧ g₀ = g := by simpa using hparts
  obtain ⟨hpa, rfl, rfl⟩ := hpa
  have hia : PartialHorn.subst θ p.arrow =
      coeqProj (comp (PartialHorn.subst θ a) (PartialHorn.subst θ b))
        (comp (PartialHorn.subst θ c) (PartialHorn.subst θ d)) := by
    rw [hpa]; rfl
  rw [hia] at hi
  obtain ⟨A, hfA, hgA, hDv⟩ := coeqProj_parallel hM ⟨_, _, rfl⟩ ⟨_, _, rfl⟩ hi
  have hX := he.1
  have hB := hi.isObj_dom
  have hQ := isObj_coeqz hM hfA hgA
  have hΦ' := hypsHold_lower hlow hΓ' hΦ
  obtain ⟨F, hF⟩ := compile_of_typeIn hφ (X := prod X (PartialHorn.subst θ p.cod))
    (by simp [extEnv, hΓ', Function.comp_def] :
      (extEnv X (PartialHorn.subst θ p.cod) e').map Prod.snd = _)
  have hDo := hi.isObj_cod
  have hFh : Hom M ρ F (prod X (PartialHorn.subst θ p.cod)) omega :=
    (compile_hom hM hG hρ hps hds _ _ _ _ hF (he'.ext hM hDo hDt)).1
  have hPv : eval M ρ (prod X (PartialHorn.subst θ p.cod)) =
      eval M ρ (prod X (coeqz (comp (PartialHorn.subst θ a) (PartialHorn.subst θ b))
        (comp (PartialHorn.subst θ c) (PartialHorn.subst θ d)))) :=
    eval_op₂_congr 6 rfl hDv
  have hFh' := hFh.congr rfl hPv.symm rfl
  have hP := isObj_prod hM hX hQ
  -- the formula holds at the projection's image, where it is its arrow after the product of the
  -- environment's object with the projection
  have hu : compile G n (Term.arr kq θ (Term.var 0)) (prod X (PartialHorn.subst θ p.dom))
      (extEnv X (PartialHorn.subst θ p.dom) e') =
        some (comp (coeqProj (comp (PartialHorn.subst θ a) (PartialHorn.subst θ b))
          (comp (PartialHorn.subst θ c) (PartialHorn.subst θ d)))
          (snd X (PartialHorn.subst θ p.dom)), PartialHorn.subst θ p.cod) := by
    rw [← hia]
    exact compile_arr_iff.mpr ⟨Term.var 0, rfl, p, hp, snd X (PartialHorn.subst θ p.dom),
      compile_var_iff.mpr ⟨rfl, rfl⟩, hl, hθ, rfl⟩
  obtain ⟨q, hq, hrq⟩ := atVar0_compile hM hG hρ hps hds he' hBt hDt hi hF hu
  have hΦc : HypsHold M ρ G n Φ (prod X (PartialHorn.subst θ p.dom))
      (extEnv X (PartialHorn.subst θ p.dom) e') := by
    rw [(lowerHyps_spec hlow).1]
    exact hypsHold_weaken1 hM hG hρ hps hds hΦ' he' hB
  have hH := p₀ _ _ (he'.ext hM hB hBt) (by simp [extEnv, hΓ', Function.comp_def]) hΦc q hq
  have hside := hrq.2.symm.trans (hH.2.trans (truth_comp hM (pair_hom hM (fst_hom hM hX hB)
    (comp_hom hM (snd_hom hM hX hB) hi))).symm)
  have hFtrue := prod_coeq_ext hM hfA hgA hX hFh' (comp_hom hM (bang_hom hM hP) (tru_hom hM))
    (hside.trans (eval_op₂_congr 3 (eval_op₂_congr 3 rfl (eval_op₁_congr 5 hPv)) rfl))
  -- the formula at the variable
  obtain ⟨q, hq, hrq⟩ := compile_at hM hG hρ hps hds he' hDt hF hx₀
  obtain rfl := Option.some_inj.mp (hq.symm.trans hr)
  exact ⟨hrq.1, hrq.2.trans ((eval_op₂_congr 3 (hFtrue.trans
    (eval_op₂_congr 3 rfl (eval_op₁_congr 5 hPv.symm))) rfl).trans
    (truth_comp hM (pair_hom hM (idt_hom hM hX) hx₀)))⟩

/-- A formula in a context with a variable of the initial type holds: the environment's object
has an arrow to the initial object, and is initial. -/
theorem zeroInd_sound {i : ℕ} {Γ : List Tree} {Φ : List Term} {φ : Term}
    (hi : Γ[i]? = some zero) (hφ : typeIn G n Γ φ = some omega) : FmSound M ρ G n Γ Φ φ := by
  intro X e he hΓ _ r hr
  obtain ⟨F, hF⟩ := compile_of_typeIn hφ (X := X) hΓ
  obtain rfl := Option.some_inj.mp (hF.symm.trans hr)
  rw [← hΓ, List.getElem?_map, Option.map_eq_some_iff] at hi
  obtain ⟨p, hp, hpz⟩ := hi
  exact ⟨rfl, eq_of_hom_zero hM (hpz ▸ (he.2 p (List.mem_of_getElem? hp)).1)
    (compile_hom hM hG hρ hps hds _ _ _ _ hF he).1 (comp_hom hM (bang_hom hM he.1) (tru_hom hM))⟩

/-- A term in the environment extended by a list variable, at an element of the list object, is
its arrow there after the pairing of the identity with the element. -/
theorem listAt {X x W B a : Tree} {e' : List (Tree × Tree)} {w : Term}
    (he' : EnvHom M ρ G n X e') (hat : IsTy G n a = true)
    (hw : compile G n w (prod X (list a)) (extEnv X (list a) e') = some (W, B))
    (hx : Hom M ρ x X (list a)) :
    ∃ q, compile G n w X ((x, list a) :: e') = some q ∧
      ResEq M ρ (comp W (pair (idt X) x), B) q :=
  compile_at hM hG hρ hps hds he' (by simpa [isTy_list] using hat) hw hx

/-- A term in the environment extended by a list variable, at the empty list, is its arrow there
after the pairing of the identity with the empty list. -/
theorem listNilAt {kn : ℕ} (hkn : G.prims[kn]? = some nilPrim) {X W B a : Tree}
    {e' : List (Tree × Tree)} {w : Term} (he' : EnvHom M ρ G n X e') (hat : IsTy G n a = true)
    (hw : compile G n w (prod X (list a)) (extEnv X (list a) e') = some (W, B)) :
    ∃ q, compile G n (Term.subst w (instVar (Term.arr kn [a] Term.star))) X e' = some q ∧
      ResEq M ρ (comp W (pair (idt X) (comp (nil a) (bang X))), B) q := by
  obtain ⟨q₀, hq₀, hr₀⟩ := listAt hM hG hρ hps hds he' hat hw
    (comp_hom hM (bang_hom hM he'.1) (nil_hom hM (isObj_of_isTy hM hds.2 hρ a hat)))
  obtain ⟨q₁, hq₁, hr₁⟩ := compile_subst hM hG hρ hps hds w X _ q₀ hq₀ e'
    (instVar (Term.arr kn [a] Term.star)) he' fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (comp (nil a) (bang X), list a) = p := by simpa using hp
        exact ⟨_, compile_nilT hkn hat X e', ResEq.refl _⟩
      · exact ⟨p, compile_var_iff.mpr ⟨rfl, by simpa using hp⟩, ResEq.refl p⟩
  exact ⟨q₁, hq₁, hr₀.trans hr₁⟩

/-- A term in the environment extended by a list variable, at a construction of a new element
onto the variable, is its arrow after construction. -/
theorem listConsAt_compile {kc : ℕ} (hkc : G.prims[kc]? = some consPrim) {X W B a : Tree}
    {e' : List (Tree × Tree)} {w : Term} (he' : EnvHom M ρ G n X e') (hat : IsTy G n a = true)
    (hw : compile G n w (prod X (list a)) (extEnv X (list a) e') = some (W, B)) :
    ∃ q, compile G n (listConsAt kc a w) (prod (prod X a) (list a))
        (extEnv (prod X a) (list a) (extEnv X a e')) = some q ∧
      ResEq M ρ (comp W (pair (comp (fst X a) (fst (prod X a) (list a)))
        (comp (cons a) (pair (comp (snd X a) (fst (prod X a) (list a)))
          (snd (prod X a) (list a))))), B) q := by
  have hX := he'.1
  have hA := isObj_of_isTy hM hds.2 hρ a hat
  have hL := isObj_list hM hA
  have hLt : IsTy G n (list a) = true := by simpa [isTy_list] using hat
  have hea := he'.ext hM hA hat
  have hXa := hea.1
  have hê₁ := hea.ext hM hL hLt
  have hfQ := fst_hom hM hXa hL
  have hsQ := snd_hom hM hXa hL
  have hfXa := fst_hom hM hX hA
  have hff := comp_hom hM hfQ hfXa
  have hsf := comp_hom hM hfQ (snd_hom hM hX hA)
  have hcel := comp_hom hM (pair_hom hM hsf hsQ) (cons_hom hM hA)
  have hk₁ := pair_hom hM hff hcel
  have he'h : ∀ p ∈ e', Hom M ρ p.1 X p.2 := fun p hp ↦ (he'.2 p hp).1
  obtain ⟨q₀, hq₀, hr₀⟩ := compile_precomp hM hG hρ hps hds hw (he'.ext hM hL hLt) hk₁
    (e' := (comp (cons a) (pair (comp (snd X a) (fst (prod X a) (list a)))
      (snd (prod X a) (list a))), list a) ::
      precomp (comp (fst X a) (fst (prod X a) (list a))) e')
    (envEq_precomp_extEnv hM hX hL he'h hk₁ (fst_pair hM hff hcel) (snd_pair hM hff hcel)
      (envEq_refl _))
  obtain ⟨q₁, hq₁, hr₁⟩ := compile_subst hM hG hρ hps hds w _ _ q₀ hq₀
    (extEnv (prod X a) (list a) (extEnv X a e'))
    (fun i ↦ match i with
      | 0 => Term.arr kc [a] (Term.pair (Term.var 1) (Term.var 0))
      | j + 1 => Term.var (j + 2)) hê₁ fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (comp (cons a) (pair (comp (snd X a) (fst (prod X a) (list a)))
            (snd (prod X a) (list a))), list a) = p := by simpa using hp
        exact ⟨_, compile_consT hkc hat (compile_pair_iff.mpr ⟨_, _, _, a, _, list a, rfl,
          compile_var_iff.mpr ⟨rfl, rfl⟩, compile_var_iff.mpr ⟨rfl, rfl⟩, rfl⟩),
          ResEq.refl _⟩
      · simp only [precomp, List.getElem?_cons_succ, List.getElem?_map,
          Option.map_eq_some_iff] at hp
        obtain ⟨p₀, hp₀, rfl⟩ := hp
        exact ⟨(comp (comp p₀.1 (fst X a)) (fst (prod X a) (list a)), p₀.2),
          compile_var_iff.mpr ⟨rfl, by simp [extEnv, hp₀]⟩, rfl,
          (comp_assoc hM hfQ hfXa (he'h p₀ (List.mem_of_getElem? hp₀))).symm⟩
  exact ⟨q₁, hq₁, hr₀.trans hr₁⟩

/-- A term in the environment extended by a list variable, weakened past a new element, is its
arrow after the pairing of the parameters with the tail. -/
theorem weakenElemAt {X W B a : Tree} {e' : List (Tree × Tree)} {w : Term}
    (he' : EnvHom M ρ G n X e') (hat : IsTy G n a = true)
    (hw : compile G n w (prod X (list a)) (extEnv X (list a) e') = some (W, B)) :
    ∃ q, compile G n (weakenElem w) (prod (prod X a) (list a))
        (extEnv (prod X a) (list a) (extEnv X a e')) = some q ∧
      ResEq M ρ (comp W (pair (comp (fst X a) (fst (prod X a) (list a)))
        (snd (prod X a) (list a))), B) q := by
  have hX := he'.1
  have hA := isObj_of_isTy hM hds.2 hρ a hat
  have hL := isObj_list hM hA
  have hLt : IsTy G n (list a) = true := by simpa [isTy_list] using hat
  have hXa := (he'.ext hM hA hat).1
  have hfQ := fst_hom hM hXa hL
  have hsQ := snd_hom hM hXa hL
  have hfXa := fst_hom hM hX hA
  have hff := comp_hom hM hfQ hfXa
  have hk₂ := pair_hom hM hff hsQ
  have he'h : ∀ p ∈ e', Hom M ρ p.1 X p.2 := fun p hp ↦ (he'.2 p hp).1
  obtain ⟨q₂, hq₂, hr₂⟩ := compile_precomp hM hG hρ hps hds hw (he'.ext hM hL hLt) hk₂
    (e' := (snd (prod X a) (list a), list a) ::
      precomp (fst (prod X a) (list a)) (precomp (fst X a) e'))
    (envEq_precomp_extEnv hM hX hL he'h hk₂ (fst_pair hM hff hsQ) (snd_pair hM hff hsQ)
      (envEq_precomp_comp hM he'h hfXa hfQ))
  exact ⟨q₂, compile_rename w _ (extEnv (prod X a) (list a) (extEnv X a e')) _
    (fun i ↦ match i with
      | 0 => 0
      | j + 1 => j + 2) q₂ hq₂ fun i _ ↦ by
      rcases i with _ | j
      · rfl
      · simp [extEnv, precomp], hr₂⟩

/-- An induction's step at the element and a term's value at the tail, in the environment
extended by a list variable and a new element, is the step's arrow after the parameters and
the element paired with the term's arrow at the tail. -/
theorem listStepAt {X W S C a : Tree} {e' : List (Tree × Tree)} {w s : Term}
    (he' : EnvHom M ρ G n X e') (hat : IsTy G n a = true) (hCt : IsTy G n C = true)
    (hS : compile G n s (prod (prod X a) C) (extEnv (prod X a) C (extEnv X a e')) = some (S, C))
    (hw : compile G n w (prod X (list a)) (extEnv X (list a) e') = some (W, C)) :
    ∃ q, compile G n (Term.subst s (atVar0 (weakenElem w))) (prod (prod X a) (list a))
        (extEnv (prod X a) (list a) (extEnv X a e')) = some q ∧
      ResEq M ρ (comp S (pair (fst (prod X a) (list a)) (comp W
        (pair (comp (fst X a) (fst (prod X a) (list a))) (snd (prod X a) (list a))))), C) q := by
  have hX := he'.1
  have hA := isObj_of_isTy hM hds.2 hρ a hat
  have hL := isObj_list hM hA
  have hC := isObj_of_isTy hM hds.2 hρ C hCt
  have hLt : IsTy G n (list a) = true := by simpa [isTy_list] using hat
  have hea := he'.ext hM hA hat
  have hXa := hea.1
  have hê₁ := hea.ext hM hL hLt
  have hfQ := fst_hom hM hXa hL
  have hsQ := snd_hom hM hXa hL
  have hk₂ := pair_hom hM (comp_hom hM hfQ (fst_hom hM hX hA)) hsQ
  have hWh : Hom M ρ W (prod X (list a)) C :=
    (compile_hom hM hG hρ hps hds _ _ _ _ hw (he'.ext hM hL hLt)).1
  obtain ⟨q₂, hq₂, hr₂⟩ := weakenElemAt hM hG hρ hps hds he' hat hw
  have hk₃ := pair_hom hM hfQ (comp_hom hM hk₂ hWh)
  obtain ⟨q₃, hq₃, hr₃⟩ := compile_precomp hM hG hρ hps hds hS (hea.ext hM hC hCt) hk₃
    (e' := (comp W (pair (comp (fst X a) (fst (prod X a) (list a))) (snd (prod X a) (list a))),
      C) :: precomp (fst (prod X a) (list a)) (extEnv X a e'))
    (envEq_precomp_extEnv hM hXa hC (fun p hp ↦ (hea.2 p hp).1) hk₃
      (fst_pair hM hfQ (comp_hom hM hk₂ hWh)) (snd_pair hM hfQ (comp_hom hM hk₂ hWh))
      (envEq_refl _))
  obtain ⟨q₄, hq₄, hr₄⟩ := compile_subst hM hG hρ hps hds s _ _ q₃ hq₃
    (extEnv (prod X a) (list a) (extEnv X a e')) (atVar0 (weakenElem w)) hê₁ fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (comp W (pair (comp (fst X a) (fst (prod X a) (list a)))
            (snd (prod X a) (list a))), C) = p := by simpa using hp
        exact ⟨_, hq₂, hr₂⟩
      · exact ⟨p, compile_var_iff.mpr ⟨rfl, by simpa [extEnv, precomp] using hp⟩,
          ResEq.refl p⟩
  exact ⟨q₄, hq₄, hr₃.trans hr₄⟩

/-- Hypotheses that hold in an environment hold, weakened past two variables, in its extension
by an element and a list. -/
theorem hypsHold_weaken2 {Φ : List Term} {X a : Tree} {e' : List (Tree × Tree)}
    (hΦ : HypsHold M ρ G n Φ X e') (he' : EnvHom M ρ G n X e') (hat : IsTy G n a = true) :
    HypsHold M ρ G n (Φ.map weaken2) (prod (prod X a) (list a))
      (extEnv (prod X a) (list a) (extEnv X a e')) := by
  have hA := isObj_of_isTy hM hds.2 hρ a hat
  have hL := isObj_list hM hA
  have hXa := (he'.ext hM hA hat).1
  have hfQ := fst_hom hM hXa hL
  have hfXa := fst_hom hM he'.1 hA
  exact hypsHold_rename hM hG hρ hps hds hΦ he' (comp_hom hM hfQ hfXa)
    (envEq_precomp_comp hM (fun p hp ↦ (he'.2 p hp).1) hfXa hfQ) fun i _ ↦ by
      simp [extEnv, precomp]

/-- Induction on a list type, in the form of the uniqueness of recursion, is sound: an equation,
in a context of a list variable, whose sides agree at the empty list and are each, at a
construction, a step of their type applied to the element and their value at the tail, holds,
under hypotheses that do not mention the variable. -/
theorem listInd_sound {kn kc : ℕ} (hkn : G.prims[kn]? = some nilPrim)
    (hkc : G.prims[kc]? = some consPrim) {Γ' : List Tree} {Φ Φ' : List Term}
    (hlow : lowerHyps G n Γ' Φ = some Φ') {a : Tree} {t u s : Term} {C : Tree}
    (htC : typeIn G n (list a :: Γ') t = some C) (hsC : typeIn G n (C :: a :: Γ') s = some C)
    (p₀ : FmSound M ρ G n Γ' Φ' (Term.eq (Term.subst t (instVar (Term.arr kn [a] Term.star)))
      (Term.subst u (instVar (Term.arr kn [a] Term.star)))))
    (p₁ : FmSound M ρ G n (list a :: a :: Γ') (Φ'.map weaken2)
      (Term.eq (listConsAt kc a t) (Term.subst s (atVar0 (weakenElem t)))))
    (p₂ : FmSound M ρ G n (list a :: a :: Γ') (Φ'.map weaken2)
      (Term.eq (listConsAt kc a u) (Term.subst s (atVar0 (weakenElem u))))) :
    FmSound M ρ G n (list a :: Γ') Φ (Term.eq t u) := by
  intro X e he hΓ hΦ r hr
  obtain ⟨t', u', htu, f, A, ht, g, hu, rfl⟩ := compile_eq_iff.mp hr
  simp only [List.cons.injEq, and_true] at htu
  obtain ⟨rfl, rfl⟩ := htu
  have hty := compile_hom hM hG hρ hps hds
  rcases e with _ | ⟨⟨x₀, N⟩, e'⟩
  · simp at hΓ
  simp only [List.map_cons, List.cons.injEq] at hΓ
  obtain ⟨rfl, hΓ'⟩ := hΓ
  have he' : EnvHom M ρ G n X e' := ⟨he.1, fun p hp ↦ he.2 p (List.mem_cons_of_mem _ hp)⟩
  obtain ⟨hx₀, hLt⟩ := he.2 _ List.mem_cons_self
  have hat : IsTy G n a = true := by simpa [isTy_list] using hLt
  have hA := isObj_of_isTy hM hds.2 hρ a hat
  have hL := isObj_list hM hA
  have hX := he.1
  have hê : EnvHom M ρ G n (prod X (list a)) (extEnv X (list a) e') := he'.ext hM hL hLt
  have hêΓ : (extEnv X (list a) e').map Prod.snd = list a :: Γ' := by
    simp [extEnv, hΓ', Function.comp_def]
  have hΦ' := hypsHold_lower hlow hΓ' hΦ
  have hê₁ := (he'.ext hM hA hat).ext hM hL hLt
  have hê₁Γ : (extEnv (prod X a) (list a) (extEnv X a e')).map Prod.snd = list a :: a :: Γ' := by
    simp [extEnv, hΓ', Function.comp_def]
  have hΦ₁ := hypsHold_weaken2 hM hG hρ hps hds hΦ' he' hat
  -- the sides' type, and their arrows in the generic environment
  obtain ⟨f₀, hf₀⟩ := compile_of_typeIn htC (X := X) (e := (x₀, list a) :: e') (by simp [hΓ'])
  obtain rfl : A = C := (Prod.mk.inj (Option.some_inj.mp (ht.symm.trans hf₀))).2
  obtain ⟨F, hF⟩ := compile_retype t X _ _ ht (prod X (list a)) (extEnv X (list a) e')
    (by simp [hêΓ, hΓ'])
  obtain ⟨G', hG'⟩ := compile_retype u X _ _ hu (prod X (list a)) (extEnv X (list a) e')
    (by simp [hêΓ, hΓ'])
  obtain ⟨hFh, hCt⟩ := hty _ _ _ _ hF hê
  have hGh := (hty _ _ _ _ hG' hê).1
  -- the sides are their generic arrows at the variable
  obtain ⟨q, hq, hrq⟩ := listAt hM hG hρ hps hds he' hat hF hx₀
  obtain rfl := Option.some_inj.mp (hq.symm.trans ht)
  obtain ⟨q', hq', hrq'⟩ := listAt hM hG hρ hps hds he' hat hG' hx₀
  obtain rfl := Option.some_inj.mp (hq'.symm.trans hu)
  -- at the empty list
  obtain ⟨z₁, hz₁, hrz₁⟩ := listNilAt hM hG hρ hps hds hkn he' hat hF
  obtain ⟨z₂, hz₂, hrz₂⟩ := listNilAt hM hG hρ hps hds hkn he' hat hG'
  have hz₁' := compile_resEq hz₁ hrz₁
  have hz₂' := compile_resEq hz₂ hrz₂
  have h₀ := (holds_eq_iff hM hG hρ hps hds he' hz₁' hz₂').mp
    (p₀ X e' he' hΓ' hΦ' _ (compile_eq_iff.mpr ⟨_, _, rfl, _, _, hz₁', _, hz₂', rfl⟩))
  -- at a construction
  obtain ⟨S, hS⟩ := compile_of_typeIn hsC (X := prod (prod X a) A)
    (e := extEnv (prod X a) A (extEnv X a e')) (by simp [extEnv, hΓ', Function.comp_def])
  have hSh : Hom M ρ S (prod (prod X a) A) A :=
    (hty _ _ _ _ hS ((he'.ext hM hA hat).ext hM (isObj_of_isTy hM hds.2 hρ A hCt) hCt)).1
  have step : ∀ {w : Term} {W : Tree},
      compile G n w (prod X (list a)) (extEnv X (list a) e') = some (W, A) →
      FmSound M ρ G n (list a :: a :: Γ') (Φ'.map weaken2)
        (Term.eq (listConsAt kc a w) (Term.subst s (atVar0 (weakenElem w)))) →
      eval M ρ (comp W (pair (comp (fst X a) (fst (prod X a) (list a)))
          (comp (cons a) (pair (comp (snd X a) (fst (prod X a) (list a)))
            (snd (prod X a) (list a)))))) =
        eval M ρ (comp S (pair (fst (prod X a) (list a))
          (comp W (pair (comp (fst X a) (fst (prod X a) (list a)))
            (snd (prod X a) (list a)))))) := fun {w W} hw pw ↦ by
    obtain ⟨q₁, hq₁, hr₁⟩ := listConsAt_compile hM hG hρ hps hds hkc he' hat hw
    obtain ⟨q₃, hq₃, hr₃⟩ := listStepAt hM hG hρ hps hds he' hat hCt hS hw
    have hq₁' := compile_resEq hq₁ hr₁
    have hq₃' := compile_resEq hq₃ hr₃
    exact hr₁.2.symm.trans (((holds_eq_iff hM hG hρ hps hds hê₁ hq₁' hq₃').mp
      (pw _ _ hê₁ hê₁Γ hΦ₁ _ (compile_eq_iff.mpr ⟨_, _, rfl, _, _, hq₁', _, hq₃', rfl⟩))).trans
      hr₃.2)
  have hFG := listRec_param_unique hM hX hA hFh hGh hSh (hrz₁.2.symm.trans (h₀.trans hrz₂.2))
    (step hF p₁) (step hG' p₂)
  exact (holds_eq_iff hM hG hρ hps hds he hq hq').mpr
    (hrq.2.trans ((eval_op₂_congr 3 hFG rfl).trans hrq'.2.symm))

/-- Induction on a list type with an induction hypothesis is sound: a formula, in a context of a
list variable, that holds at the empty list and, at a construction, where it holds at the tail,
holds, under hypotheses that do not mention the variable. -/
theorem listIndHyp_sound {kn kc : ℕ} (hkn : G.prims[kn]? = some nilPrim)
    (hkc : G.prims[kc]? = some consPrim) {Γ' : List Tree} {Φ Φ' : List Term}
    (hlow : lowerHyps G n Γ' Φ = some Φ') {a : Tree} {φ : Term}
    (hφ : typeIn G n (list a :: Γ') φ = some omega)
    (p₀ : FmSound M ρ G n Γ' Φ' (Term.subst φ (instVar (Term.arr kn [a] Term.star))))
    (p₁ : FmSound M ρ G n (list a :: a :: Γ') (Φ'.map weaken2 ++ [weakenElem φ])
      (listConsAt kc a φ)) :
    FmSound M ρ G n (list a :: Γ') Φ φ := by
  intro X e he hΓ hΦ r hr
  rcases e with _ | ⟨⟨x₀, N⟩, e'⟩
  · simp at hΓ
  simp only [List.map_cons, List.cons.injEq] at hΓ
  obtain ⟨rfl, hΓ'⟩ := hΓ
  have he' : EnvHom M ρ G n X e' := ⟨he.1, fun p hp ↦ he.2 p (List.mem_cons_of_mem _ hp)⟩
  obtain ⟨hx₀, hLt⟩ := he.2 _ List.mem_cons_self
  have hat : IsTy G n a = true := by simpa [isTy_list] using hLt
  have hA := isObj_of_isTy hM hds.2 hρ a hat
  have hL := isObj_list hM hA
  have hX := he.1
  have hê : EnvHom M ρ G n (prod X (list a)) (extEnv X (list a) e') := he'.ext hM hL hLt
  have hêΓ : (extEnv X (list a) e').map Prod.snd = list a :: Γ' := by
    simp [extEnv, hΓ', Function.comp_def]
  have hΦ' := hypsHold_lower hlow hΓ' hΦ
  have hea := he'.ext hM hA hat
  have hê₁ := hea.ext hM hL hLt
  have hê₁Γ : (extEnv (prod X a) (list a) (extEnv X a e')).map Prod.snd = list a :: a :: Γ' := by
    simp [extEnv, hΓ', Function.comp_def]
  have hΦ₁ := hypsHold_weaken2 hM hG hρ hps hds hΦ' he' hat
  obtain ⟨F, hF⟩ := compile_of_typeIn hφ (X := prod X (list a)) hêΓ
  have hFh : Hom M ρ F (prod X (list a)) omega :=
    (compile_hom hM hG hρ hps hds _ _ _ _ hF hê).1
  -- at the empty list
  obtain ⟨z, hz, hrz⟩ := listNilAt hM hG hρ hps hds hkn he' hat hF
  have h₀ := hrz.2.symm.trans (p₀ X e' he' hΓ' hΦ' _ hz).2
  -- at a construction, on the pullback of truth along the formula at the tail
  have hXa := hea.1
  have hfQ := fst_hom hM hXa hL
  have hsQ := snd_hom hM hXa hL
  have hk₂ := pair_hom hM (comp_hom hM hfQ (fst_hom hM hX hA)) hsQ
  have hFk₂ := comp_hom hM hk₂ hFh
  obtain ⟨hi, hFk₂i⟩ := truthIncl_hom hM hFk₂
  have hE₁ := envHom_precomp hM hê₁ hi
  have hE₁Γ : (precomp (truthIncl (comp F (pair (comp (fst X a) (fst (prod X a) (list a)))
      (snd (prod X a) (list a))))) (extEnv (prod X a) (list a) (extEnv X a e'))).map
        Prod.snd = list a :: a :: Γ' := by
    simp [precomp, Function.comp_def, ← hê₁Γ]
  obtain ⟨qw, hqw, hrqw⟩ := weakenElemAt hM hG hρ hps hds he' hat hF
  obtain ⟨r₁, hr₁, hr₁₂, hr₁₁⟩ :=
    compile_precomp hM hG hρ hps hds (compile_resEq hqw hrqw) hê₁ hi (envEq_refl _)
  have hH₁ := (hypsHold_append M ρ).mpr ⟨hypsHold_precomp hM hG hρ hps hds hΦ₁ hê₁ hi
    (envEq_refl _), r₁, hr₁, hr₁₂, hr₁₁.trans ((eval_op₂_congr 3 hrqw.2 rfl).trans hFk₂i)⟩
  obtain ⟨qc, hqc, hrqc⟩ := listConsAt_compile hM hG hρ hps hds hkc he' hat hF
  obtain ⟨q₂, hq₂, -, hq₂₁⟩ :=
    compile_precomp hM hG hρ hps hds (compile_resEq hqc hrqc) hê₁ hi (envEq_refl _)
  have h₁ := (eval_op₂_congr 3 hrqc.2.symm rfl).trans
    (hq₂₁.symm.trans (p₁ _ _ hE₁ hE₁Γ hH₁ q₂ hq₂).2)
  have hFtrue := truth_of_listInd hM hX hA hFh h₀ h₁
  -- the formula at the variable
  obtain ⟨q, hq, hrq⟩ := listAt hM hG hρ hps hds he' hat hF hx₀
  obtain rfl := Option.some_inj.mp (hq.symm.trans hr)
  exact ⟨hrq.1, hrq.2.trans ((eval_op₂_congr 3 hFtrue rfl).trans
    (truth_comp hM (pair_hom hM (idt_hom hM hX) hx₀)))⟩

omit hM hG hρ hps hds in
/-- A property of each pair of a zip of lists of one length is a property of the second list's
elements with some element of the first. -/
theorem exists_of_all_zip {α β : Type} {p : α × β → Bool} :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length → (l₁.zip l₂).all p = true →
      ∀ y ∈ l₂, ∃ x ∈ l₁, p (x, y) = true := fun l₁ l₂ hl h y hy ↦ by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  have hi' : i < l₁.length := hl ▸ hi
  refine ⟨l₁[i], List.getElem_mem hi', List.all_eq_true.mp h _ ?_⟩
  rw [List.mem_iff_getElem]
  exact ⟨i, by simp [hi, hi'], by simp⟩

omit hG hρ hps hds in
/-- The inclusion of the subobject on which arrows into the subobject classifier are truth, folded
from an arrow into their domain, is an arrow into it that factors through the arrow it starts
from, and after it each arrow is truth. -/
theorem truthSub_foldl {X : Tree} :
    ∀ (Hs : List Tree) (S m : Tree), Hom M ρ m S X → (∀ H ∈ Hs, Hom M ρ H X omega) →
      Hom M ρ (Hs.foldl truthStep (S, m)).2 (Hs.foldl truthStep (S, m)).1 X ∧
        (∃ k, Hom M ρ k (Hs.foldl truthStep (S, m)).1 S ∧
          eval M ρ (Hs.foldl truthStep (S, m)).2 = eval M ρ (comp m k)) ∧
        ∀ H ∈ Hs, eval M ρ (comp H (Hs.foldl truthStep (S, m)).2) =
          eval M ρ (comp tru (bang (Hs.foldl truthStep (S, m)).1)) :=
  List.rec (fun S m hm _ ↦ ⟨hm, ⟨idt S, idt_hom hM hm.isObj_dom, (comp_idt hM hm).symm⟩,
      fun _ h ↦ by simp at h⟩)
    fun H Hs ih S m hm hHs ↦ by
      have hH := hHs H List.mem_cons_self
      obtain ⟨hi, hti⟩ := truthIncl_hom hM (comp_hom hM hm hH)
      have hmi := comp_hom hM hi hm
      obtain ⟨hr, ⟨k, hk, hmk⟩, hall⟩ := ih (truthEq (comp H m))
        (comp m (truthIncl (comp H m))) hmi fun H' h' ↦ hHs H' (List.mem_cons_of_mem _ h')
      refine ⟨hr, ⟨comp (truthIncl (comp H m)) k, comp_hom hM hk hi,
        hmk.trans (comp_assoc hM hk hi hm).symm⟩, fun H' h' ↦ ?_⟩
      rcases List.mem_cons.mp h' with rfl | h'
      · exact (eval_op₂_congr 3 rfl hmk).trans ((comp_assoc hM hk hmi hH).trans
          ((eval_op₂_congr 3 ((comp_assoc hM hi hm hH).trans hti) rfl).trans (truth_comp hM hk)))
      · exact hall H' h'

omit hG hρ hps hds in
/-- An arrow after which each of a list of arrows into the subobject classifier is truth, and
which factors through an arrow into their domain, factors through the inclusion of the subobject
on which they are truth, folded from that arrow. -/
theorem truthSub_lift {X Y x : Tree} :
    ∀ (Hs : List Tree) (S m k : Tree), Hom M ρ m S X → Hom M ρ k Y S →
      eval M ρ (comp m k) = eval M ρ x →
      (∀ H ∈ Hs, Hom M ρ H X omega ∧ eval M ρ (comp H x) = eval M ρ (comp tru (bang Y))) →
      ∃ k', Hom M ρ k' Y (Hs.foldl truthStep (S, m)).1 ∧
        eval M ρ (comp (Hs.foldl truthStep (S, m)).2 k') = eval M ρ x :=
  List.rec (fun _ _ k _ hk hmk _ ↦ ⟨k, hk, hmk⟩) fun H Hs ih S m k hm hk hmk hHs ↦ by
    obtain ⟨hH, hHx⟩ := hHs H List.mem_cons_self
    have hHm := comp_hom hM hm hH
    have hHmk : eval M ρ (comp (comp H m) k) = eval M ρ (comp tru (bang Y)) :=
      (comp_assoc hM hk hm hH).symm.trans ((eval_op₂_congr 3 rfl hmk).trans hHx)
    obtain ⟨hl, hil⟩ := truthLift_hom hM hHm hk hHmk
    obtain ⟨hi, -⟩ := truthIncl_hom hM hHm
    exact ih _ _ _ (comp_hom hM hi hm) hl
      ((comp_assoc hM hl hi hm).symm.trans ((eval_op₂_congr 3 rfl hil).trans hmk))
      fun H' h' ↦ hHs H' (List.mem_cons_of_mem _ h')

omit hρ hps hds in
/-- The sequent of the combinators a valid theorem compiles to is valid. -/
theorem Thm.seq_valid {a : Thm} (ha : a.Valid M G) : (a.seq G).Valid M := by
  obtain ⟨hctx, hhyps, hconcl, hall⟩ := ha
  intro ρ' hρ' _
  obtain ⟨hps', hds', hfm⟩ := hall ρ' hρ'
  have hty := compile_hom hM hG hρ' hps' hds'
  have hstd := stdEnv_hom hM hds'.2 hρ' _ hctx
  have harrow : ∀ {φ : Term} {F A : Tree},
      compile G a.arity φ (ctxObj a.ctx) (stdEnv a.ctx) = some (F, A) → a.arrow G φ = F :=
    fun h ↦ by simp [Thm.arrow, h]
  have hform : ∀ {φ : Term}, typeIn G a.arity a.ctx φ = some omega →
      compile G a.arity φ (ctxObj a.ctx) (stdEnv a.ctx) = some (a.arrow G φ, omega) := fun h ↦ by
    obtain ⟨⟨F, A⟩, hF, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [hF, harrow hF]
  -- the subobject on which the hypotheses hold
  have hHs : ∀ H ∈ a.hyps.map (a.arrow G), Hom M ρ' H (ctxObj a.ctx) omega := fun H hH ↦ by
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hH
    exact (hty _ _ _ _ (hform (hhyps h hh)) hstd).1
  obtain ⟨hm, -, htrue⟩ := truthSub_foldl hM (ρ := ρ') _ _ _ (idt_hom hM hstd.1) hHs
  have hS := hm.isObj_dom
  have he' := envHom_precomp hM hstd hm
  have hΓ' : (precomp (truthSub (ctxObj a.ctx) (a.hyps.map (a.arrow G))).2
      (stdEnv a.ctx)).map Prod.snd = a.ctx := by
    simp [precomp, Function.comp_def, map_snd_stdEnv]
  have hat : ∀ {φ : Term} {F A : Tree},
      compile G a.arity φ (ctxObj a.ctx) (stdEnv a.ctx) = some (F, A) →
      ∃ q, compile G a.arity φ (truthSub (ctxObj a.ctx) (a.hyps.map (a.arrow G))).1
        (precomp (truthSub (ctxObj a.ctx) (a.hyps.map (a.arrow G))).2 (stdEnv a.ctx)) = some q ∧
        ResEq M ρ' (comp F (truthSub (ctxObj a.ctx) (a.hyps.map (a.arrow G))).2, A) q :=
    fun h ↦ compile_precomp hM hG hρ' hps' hds' h hstd hm (envEq_refl _)
  have hΦ : HypsHold M ρ' G a.arity a.hyps _
      (precomp (truthSub (ctxObj a.ctx) (a.hyps.map (a.arrow G))).2 (stdEnv a.ctx)) :=
    fun ψ hψ ↦ by
      obtain ⟨q, hq, hq₂, hq₁⟩ := hat (hform (hhyps ψ hψ))
      exact ⟨q, hq, hq₂, hq₁.trans (htrue _ (List.mem_map_of_mem hψ))⟩
  -- a side of the sequent is its arrow after the inclusion
  have hside : ∀ {f Y : Tree}, Hom M ρ' f (ctxObj a.ctx) Y → eval M ρ' (a.side G f) =
      eval M ρ' (comp f (truthSub (ctxObj a.ctx) (a.hyps.map (a.arrow G))).2) := fun hf ↦ by
    by_cases hnil : a.hyps = []
    · simp only [Thm.side, hnil, List.map_nil, ↓reduceIte]
      exact (comp_idt hM hf).symm
    · simp only [Thm.side, hnil, ↓reduceIte]
  simp only [Thm.seq]
  split
  · rename_i t u htu
    rw [eqParts_eq_some htu] at hconcl
    obtain ⟨C, hC⟩ := Option.map_eq_some_iff.mp hconcl |>.imp fun _ h ↦ h.1
    obtain ⟨t', u', htu', f, A, hf, g, hg, -⟩ := compile_eq_iff.mp hC
    simp only [List.cons.injEq, and_true] at htu'
    obtain ⟨rfl, rfl⟩ := htu'
    obtain ⟨qt, hqt, hrt⟩ := hat hf
    obtain ⟨qu, hqu, hru⟩ := hat hg
    have hqt' := compile_resEq hqt hrt
    have hqu' := compile_resEq hqu hru
    have hH := (holds_eq_iff hM hG hρ' hps' hds' he' hqt' hqu').mp (hfm _ _ he' hΓ' hΦ _
      (by rw [eqParts_eq_some htu]; exact compile_eq_iff.mpr ⟨_, _, rfl, _, _, hqt', _, hqu', rfl⟩))
    have hfh := (hty _ _ _ _ hf hstd).1
    have hgh := (hty _ _ _ _ hg hstd).1
    obtain ⟨w, hw, -⟩ := (comp_hom hM hm hgh).exists_eval
    rw [harrow hf, harrow hg]
    exact holds_of_eval_eq ((hside hfh).trans (hrt.2.symm.trans (hH.trans (hru.2.trans
      (hside hgh).symm)))) ((hside hgh).trans hw)
  · rename_i hnone
    obtain ⟨q, hq, hrq⟩ := hat (hform hconcl)
    have hH := hfm _ _ he' hΓ' hΦ _ hq
    have hFh := (hty _ _ _ _ (hform hconcl) hstd).1
    have htX := truth_hom hM hstd.1
    obtain ⟨w, hw, -⟩ := (truth_hom hM hS).exists_eval
    exact holds_of_eval_eq ((hside hFh).trans (hrq.2.symm.trans (hH.2.trans
      ((truth_comp hM hm).symm.trans (hside htX).symm))))
      ((hside htX).trans ((truth_comp hM hm).trans hw))

omit hρ hps hds in
/-- A sequent a certificate proves, with the valid entries' sequents as its theorems, is valid,
when the definitions the definitions of {lit}`G` compile to begin the model's. -/
theorem certifies_valid {E : Array Entry}
    (hE : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G)
    (hcert : ∀ cds, compileDefs G = some cds → G.base = sig.length → cds <+: defs) {c : Tree}
    {q : PartialHorn.Seq} (h : certifies G E c q = true) : q.Valid M := by
  cases hcd : compileDefs G with
  | none => simp [certifies, hcd] at h
  | some cds =>
    simp only [certifies, hcd, Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hb, hc⟩ := h
    obtain ⟨hsig, hax⟩ := ext_prefix (hcert cds hcd hb)
    refine PartialHorn.check_sound hsig (fun a ha ↦ hM a (hax a ha)) (fun s hs ↦ ?_) c _ _ _ hc
    obtain ⟨e, he, rfl⟩ := Array.mem_map.mp hs
    obtain ⟨j, hj⟩ := Array.getElem?_of_mem he
    cases e with
    | language a => exact Thm.seq_valid hM hG (hE j _ hj)
    | combinators s => exact hE j _ hj

omit hM hG hρ hps hds in
/-- The sequent an equation compiles to, inverted. -/
theorem compileEq_eq_some {Γ : List Tree} {t u : Term} {q : PartialHorn.Seq}
    (h : compileEq G n Γ t u = some q) :
    ∃ f g A, compile G n t (ctxObj Γ) (stdEnv Γ) = some (f, A) ∧
      compile G n u (ctxObj Γ) (stdEnv Γ) = some (g, A) ∧
      q = ⟨List.replicate n obj, [], ⟨f, g⟩⟩ := by
  unfold compileEq at h
  cases ht : compile G n t (ctxObj Γ) (stdEnv Γ) with
  | none => simp [ht] at h
  | some p =>
    cases hu : compile G n u (ctxObj Γ) (stdEnv Γ) with
    | none => simp [ht, hu] at h
    | some p' =>
      obtain ⟨f, A⟩ := p
      obtain ⟨g, B⟩ := p'
      simp only [ht, hu, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
      split_ifs at h with hc
      obtain rfl := hc.2
      exact ⟨f, g, A, rfl, rfl, (Option.some_inj.mp h).symm⟩

/-- An equation proved by a certificate of the combinators of the sequent it compiles to, with
the valid entries' sequents as its theorems, holds, when the model's definitions are the
compilations of the definitions of {lit}`G`. -/
theorem cert_sound {E : Array Entry} (hE : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G)
    (hcert : ∀ cds, compileDefs G = some cds → G.base = sig.length → cds <+: defs)
    {Γ : List Tree} {Φ : List Term} {t u : Term} {q : PartialHorn.Seq}
    (hq : compileEq G n Γ t u = some q)
    {c : Tree} (hc : certifies G E c q = true) : FmSound M ρ G n Γ Φ (Term.eq t u) := by
  obtain ⟨f, g, A, hf, hg, rfl⟩ := compileEq_eq_some hq
  have hfg := eval_eq_of_holds (certifies_valid hM hG hE hcert hc ρ hρ fun _ h ↦ by simp at h)
  intro X e he hΓ _ r hr
  obtain ⟨t', u', htu, f', A', ht, g', hu, rfl⟩ := compile_eq_iff.mp hr
  simp only [List.cons.injEq, and_true] at htu
  obtain ⟨rfl, rfl⟩ := htu
  obtain ⟨r₁, hr₁, hres₁⟩ := compile_of_stdEnv hM hG hρ hps hds hf he hΓ
  obtain rfl := Option.some_inj.mp (hr₁.symm.trans ht)
  obtain ⟨r₂, hr₂, hres₂⟩ := compile_of_stdEnv hM hG hρ hps hds hg he hΓ
  obtain rfl := Option.some_inj.mp (hr₂.symm.trans hu)
  exact (holds_eq_iff hM hG hρ hps hds he ht hu).mpr
    (hres₁.2.trans ((eval_op₂_congr 3 hfg rfl).trans hres₂.2.symm))

/-- A formula proved under hypotheses by a certificate of the sequent its theorem compiles to,
with the valid entries' sequents as its theorems, holds, when the model's definitions are the
compilations of the definitions of {lit}`G`: the arrow of an environment in
which the hypotheses hold factors through the subobject on which their arrows are truth, after
whose inclusion the conclusion's arrows are equal. -/
theorem certSeq_sound {E : Array Entry}
    (hE : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G)
    (hcert : ∀ cds, compileDefs G = some cds → G.base = sig.length → cds <+: defs)
    {Γ : List Tree} {Φ : List Term} {φ : Term} (hΦ : ∀ ψ ∈ Φ, typeIn G n Γ ψ = some omega)
    (hφ : typeIn G n Γ φ = some omega) {c : Tree}
    (hc : certifies G E c (Thm.seq G ⟨n, Γ, Φ, φ⟩) = true) : FmSound M ρ G n Γ Φ φ := by
  have hv := certifies_valid hM hG hE hcert hc ρ hρ fun _ h ↦ by simp [Thm.seq] at h
  intro X e he hΓ hH r hr
  subst hΓ
  have hctx : (e.map Prod.snd).all (IsTy G n) = true := by
    rw [List.all_map, List.all_eq_true]
    exact fun p hp ↦ (he.2 p hp).2
  have hstd := stdEnv_hom hM hds.2 hρ _ hctx
  have hx := tuple_hom hM he.1 e fun p hp ↦ (he.2 p hp).1
  set a : Thm := ⟨n, e.map Prod.snd, Φ, φ⟩
  set x := tuple X (e.map Prod.fst)
  have hform : ∀ {ψ : Term}, typeIn G n (e.map Prod.snd) ψ = some omega →
      compile G n ψ (ctxObj (e.map Prod.snd)) (stdEnv (e.map Prod.snd)) =
        some (a.arrow G ψ, omega) := fun h ↦ by
    obtain ⟨⟨F, A⟩, hF, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [a, Thm.arrow, hF]
  -- the environment's arrow factors through the subobject on which the hypotheses hold
  have hHs : ∀ H ∈ Φ.map (a.arrow G), Hom M ρ H (ctxObj (e.map Prod.snd)) omega ∧
      eval M ρ (comp H x) = eval M ρ (comp tru (bang X)) := fun H hH' ↦ by
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hH'
    have hc := hform (hΦ ψ hψ)
    obtain ⟨r₁, hr₁, hres⟩ := compile_of_stdEnv hM hG hρ hps hds hc he rfl
    obtain ⟨r₂, hr₂, hh⟩ := hH ψ hψ
    obtain rfl := Option.some_inj.mp (hr₁.symm.trans hr₂)
    exact ⟨(compile_hom hM hG hρ hps hds _ _ _ _ hc hstd).1, hres.2.symm.trans hh.2⟩
  obtain ⟨k, hk, hik⟩ := truthSub_lift hM _ _ _ _ (idt_hom hM hstd.1) hx (idt_comp hM hx) hHs
  have hm := (truthSub_foldl hM (Φ.map (a.arrow G)) _ _ (idt_hom hM hstd.1)
    fun H h ↦ (hHs H h).1).1
  have hside : ∀ {f Y : Tree}, Hom M ρ f (ctxObj (e.map Prod.snd)) Y →
      eval M ρ (comp f x) = eval M ρ (comp (a.side G f) k) := fun hf ↦ by
    refine (eval_op₂_congr 3 rfl hik.symm).trans ((comp_assoc hM hk hm hf).trans ?_)
    by_cases hnil : Φ = []
    · simp only [Thm.side, a, hnil, ↓reduceIte]
      exact eval_op₂_congr 3 (comp_idt hM hf) rfl
    · simp only [Thm.side, a, hnil, ↓reduceIte]
      rfl
  cases hq : eqParts φ with
  | some tu =>
    obtain ⟨t, u⟩ := tu
    obtain rfl := eqParts_eq_some hq
    simp only [Thm.seq, a, hq] at hv
    obtain ⟨C, hC⟩ := Option.map_eq_some_iff.mp hφ |>.imp fun _ h ↦ h.1
    obtain ⟨t', u', htu', f, A, hf, g, hg, -⟩ := compile_eq_iff.mp hC
    simp only [List.cons.injEq, and_true] at htu'
    obtain ⟨rfl, rfl⟩ := htu'
    obtain ⟨t', u', htu, f', A', ht, g', hu, rfl⟩ := compile_eq_iff.mp hr
    simp only [List.cons.injEq, and_true] at htu
    obtain ⟨rfl, rfl⟩ := htu
    obtain ⟨r₁, hr₁, hres₁⟩ := compile_of_stdEnv hM hG hρ hps hds hf he rfl
    obtain rfl := Option.some_inj.mp (hr₁.symm.trans ht)
    obtain ⟨r₂, hr₂, hres₂⟩ := compile_of_stdEnv hM hG hρ hps hds hg he rfl
    obtain rfl := Option.some_inj.mp (hr₂.symm.trans hu)
    have hfh := (compile_hom hM hG hρ hps hds _ _ _ _ hf hstd).1
    have hgh := (compile_hom hM hG hρ hps hds _ _ _ _ hg hstd).1
    have harrow : ∀ {s : Term} {F B : Tree}, compile G n s (ctxObj (e.map Prod.snd))
        (stdEnv (e.map Prod.snd)) = some (F, B) → a.arrow G s = F := fun h ↦ by
      simp [a, Thm.arrow, h]
    rw [harrow hf, harrow hg] at hv
    refine (holds_eq_iff hM hG hρ hps hds he ht hu).mpr (hres₁.2.trans ?_)
    exact (hside hfh).trans ((eval_op₂_congr 3 (eval_eq_of_holds hv) rfl).trans
      ((hside hgh).symm.trans hres₂.2.symm))
  | none =>
    simp only [Thm.seq, a, hq] at hv
    have hc := hform hφ
    obtain ⟨r₁, hr₁, hres⟩ := compile_of_stdEnv hM hG hρ hps hds hc he rfl
    obtain rfl := Option.some_inj.mp (hr₁.symm.trans hr)
    have hFh := (compile_hom hM hG hρ hps hds _ _ _ _ hc hstd).1
    have htX := truth_hom hM hstd.1
    exact ⟨hres.1, hres.2.trans ((hside hFh).trans ((eval_op₂_congr 3 (eval_eq_of_holds hv)
      rfl).trans ((hside htX).symm.trans (truth_comp hM hx))))⟩

/-- The checker is sound: every rewriting a derivation performs is sound, and every formula it
proves holds, with sound unfoldings and valid earlier entries, when the model's definitions are
the compilations of the definitions of {lit}`G` wherever a certificate is checked. -/
theorem check_sound (hδ : DefnsOk M G) {E : Array Entry}
    (hE : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G)
    (hcert : ∀ cds, compileDefs G = some cds → G.base = sig.length → cds <+: defs) :
    ∀ d : Deriv, (∀ Γ Φ t t', (check G E n d).1 Γ Φ t = some t' → RwSound M ρ G n Γ Φ t t') ∧
      (∀ Γ Φ φ, (check G E n d).2 Γ Φ φ = true → FmSound M ρ G n Γ Φ φ) := by
  have hEl : ∀ (j : ℕ) (a : Thm), (E[j]?).bind Entry.language? = some a → a.Valid M G :=
    fun _ _ h ↦ Entry.valid_language hE h
  refine RoseTree.ind fun l cs ih ↦ ⟨fun Γ Φ t t' h ↦ ?_, fun Γ Φ φ h ↦ ?_⟩
  · rw [check_node] at h
    cases l
    case refl =>
      rcases cs with _ | ⟨c, cs⟩
      · obtain rfl : t = t' := Option.some_inj.mp h
        exact RwSound.refl Γ Φ t
      · simp [checkStep] at h
    case trans =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp [checkStep, rootStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        obtain ⟨v, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
        exact ((ih c₁ (by simp)).1 _ _ _ _ h₁).trans ((ih c₂ (by simp)).1 _ _ _ _ h₂)
      · simp [checkStep] at h
    case cong =>
      obtain ⟨l₀, ts, rfl⟩ : ∃ l cs, t = RoseTree.node l cs :=
        ⟨_, _, (RoseTree.node_label_children t).symm⟩
      simp only [checkStep, RoseTree.label_node, RoseTree.children_node] at h
      obtain ⟨Γs, hΓs, h⟩ := Option.bind_eq_some_iff.mp h
      split_ifs at h with hlen
      obtain ⟨ts', hts', h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some_inj.mp h
      have hR : List.Forall₂ (fun (p : (List Tree × List Term) × Term) u ↦
          RwSound M ρ G n p.1.1 p.1.2 p.2 u) (Γs.zip ts) ts' := by
        refine forall₂_zip_imp
          (P := fun x : Deriv × Checks ↦ ∀ Γ Φ t t', x.2.1 Γ Φ t = some t' →
            RwSound M ρ G n Γ Φ t t')
          (R := fun x r ↦ x.1.2.1 x.2.1.1 x.2.1.2 x.2.2 = some r)
          (fun _ _ _ hx hR ↦ hx _ _ _ _ hR) _ _ _ (by simp [hlen.1, hlen.2])
          (fun x hx ↦ ?_) (forall₂_of_mapM _ hts')
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
        exact (ih c hc).1
      unfold congCtxs at hΓs
      split_ifs at hΓs with hall
      · obtain rfl := Option.some_inj.mp hΓs
        refine cong_sound_same hM hG hρ hps hds (forall₂_zip_const
          (R := fun (p : List Tree × List Term) ↦ RwSound M ρ G n p.1 p.2) ts hR)
          fun i h₁ h₂ hs ↦ ?_
        obtain ⟨hl₁, hR₁⟩ := List.forall₂_iff_get.mp (forall₂_of_mapM _ hts')
        simp only [List.length_zip, List.length_map] at hl₁ hlen
        have hi : i < cs.length := by omega
        have hrefl : cs[i].label.isRefl = true := by
          have := List.all_eq_true.mp hall _
            (List.getElem_mem (l := (List.map Prod.fst
              (List.map (fun c ↦ (c, check G E n c)) cs)).zipIdx) (n := i) (by simpa using hi))
          simpa [List.getElem_zipIdx, hs] using this
        have hx := hR₁ i (by simp only [List.length_zip, List.length_map]; omega) h₂
        simp only [List.get_eq_getElem, List.getElem_zip, List.getElem_map] at hx
        exact check_isRefl hrefl hx
      · exact cong_sound hM hG hρ hps hds hΓs hR
    all_goals
      rcases cs with _ | ⟨c, cs⟩
      · exact rootStep_sound hM hG hρ hps hds hδ hEl
          (by simpa only [checkStep, List.map_nil] using h)
      · nomatch h
  · rw [check_node] at h
    cases l
    case join =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · rename_i t u htu
          split at h
          · rename_i v v' h₁ h₂
            obtain rfl := of_decide_eq_true h
            rw [eqParts_eq_some htu]
            exact join_sound hM hG hρ hps hds ((ih c₁ (by simp)).1 _ _ _ _ h₁)
              ((ih c₂ (by simp)).1 _ _ _ _ h₂)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case hyp i =>
      rcases cs with _ | ⟨c, cs⟩
      · exact hyp_sound (of_decide_eq_true h)
      · simp [checkStep] at h
    case cut ψ =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil, Bool.and_eq_true,
          decide_eq_true_eq] at h
        obtain ⟨⟨hψ, hp⟩, hq⟩ := h
        exact cut_sound hψ ((ih c₁ (by simp)).2 _ _ _ hp) ((ih c₂ (by simp)).2 _ _ _ hq)
      · simp [checkStep] at h
    case conv =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · rename_i φ' hd
          exact conv_sound ((ih c₁ (by simp)).1 _ _ _ _ hd) ((ih c₂ (by simp)).2 _ _ _ h)
        · simp at h
      · simp [checkStep] at h
    case convFrom ψ =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil, Bool.and_eq_true,
          decide_eq_true_eq] at h
        obtain ⟨⟨hψ, hd⟩, hp⟩ := h
        exact convFrom_sound hψ ((ih c₁ (by simp)).1 _ _ _ _ hd) ((ih c₂ (by simp)).2 _ _ _ hp)
      · simp [checkStep] at h
    case propExt =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · rename_i α β hαβ
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨⟨hα, -⟩, hp⟩, hq⟩ := h
          rw [eqParts_eq_some hαβ]
          exact propExt_sound hM hG hρ hps hds hα ((ih c₁ (by simp)).2 _ _ _ hp)
            ((ih c₂ (by simp)).2 _ _ _ hq)
        · simp at h
      · simp [checkStep] at h
    case funExt =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · rename_i f g hfg
          split at h
          · rename_i a b hab
            rw [eqParts_eq_some hfg]
            exact funExt_sound hM hG hρ hps hds hab ((ih c₁ (by simp)).2 _ _ _ h)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case natInd kz ks s =>
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · split at h
          · rename_i t u c Γ' htu _ _ C Φ' hC hlow
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨⟨rfl, hkz, hks, -, hsC⟩, hp₀⟩, hp₁⟩, hp₂⟩ := h
            rw [eqParts_eq_some htu]
            exact natInd_sound hM hG hρ hps hds hkz hks hlow hC hsC
              ((ih c₀ (by simp)).2 _ _ _ hp₀) ((ih c₁ (by simp)).2 _ _ _ hp₁)
              ((ih c₂ (by simp)).2 _ _ _ hp₂)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case listInd kn kc s =>
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · split at h
          · rename_i t u c Γ' htu _ _ _ C a Φ' hC ha hlow
            obtain rfl := listPart_eq_some.mp ha
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨⟨hkn, hkc, -, hsC⟩, hp₀⟩, hp₁⟩, hp₂⟩ := h
            rw [eqParts_eq_some htu]
            exact listInd_sound hM hG hρ hps hds hkn hkc hlow hC hsC
              ((ih c₀ (by simp)).2 _ _ _ hp₀) ((ih c₁ (by simp)).2 _ _ _ hp₁)
              ((ih c₂ (by simp)).2 _ _ _ hp₂)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case apply j θ σ =>
      simp only [checkStep] at h
      split at h
      · rename_i a ha
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨hok, rfl⟩, hlen⟩, hall⟩ := h
        refine apply_sound hM hG hρ hps hds hEl ha hok fun h hh ↦ ?_
        obtain ⟨x, hx, hxh⟩ := exists_of_all_zip _ _ hlen hall h hh
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
        exact (ih c hc).2 _ _ _ hxh
      · simp at h
    case natIndHyp kz ks =>
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · split at h
          · rename_i c Γ' _ Φ' hlow
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨rfl, hkz, hks, hφ⟩, hp₀⟩, hp₁⟩ := h
            exact natIndHyp_sound hM hG hρ hps hds hkz hks hlow hφ
              ((ih c₀ (by simp)).2 _ _ _ hp₀) ((ih c₁ (by simp)).2 _ _ _ hp₁)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case listIndHyp kn kc =>
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · split at h
          · rename_i c Γ' _ _ a Φ' ha hlow
            obtain rfl := listPart_eq_some.mp ha
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨hkn, hkc, hφ⟩, hp₀⟩, hp₁⟩ := h
            exact listIndHyp_sound hM hG hρ hps hds hkn hkc hlow hφ
              ((ih c₀ (by simp)).2 _ _ _ hp₀) ((ih c₁ (by simp)).2 _ _ _ hp₁)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case coprodInd kl kr =>
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · split at h
          · rename_i c Γ' _ _ a b Φ' hab hlow
            obtain rfl := coprodParts_eq_some.mp hab
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨hkl, hkr, hφ⟩, hp₀⟩, hp₁⟩ := h
            exact coprodInd_sound hM hG hρ hps hds hkl hkr hlow hφ
              ((ih c₀ (by simp)).2 _ _ _ hp₀) ((ih c₁ (by simp)).2 _ _ _ hp₁)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case roseInd kn kl kc s =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · split at h
          · rename_i t u r htu _ _ C a F hC hr
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨hkn, hkl, hkc, huC, hsC⟩, hp₁⟩, hp₂⟩ := h
            rw [eqParts_eq_some htu]
            exact roseInd_sound hM hG hρ hps hds hr hkn hkl hkc hC huC hsC
              ((ih c₁ (by simp)).2 _ _ _ hp₁) ((ih c₂ (by simp)).2 _ _ _ hp₂)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case roseIndHyp kn kl kc =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · split at h
          · rename_i r a F hr
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨hkn, hkl, hkc, hφ⟩, hp₁⟩ := h
            exact roseIndHyp_sound hM hG hρ hps hds hr hkn hkl hkc hφ
              ((ih c₁ (by simp)).2 _ _ _ hp₁)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case cert c =>
      rcases cs with _ | ⟨c₀, cs⟩
      · simp only [checkStep, List.map_nil] at h
        split at h
        · rename_i t u htu
          split at h
          · rename_i q hq
            rw [eqParts_eq_some htu]
            exact cert_sound hM hG hρ hps hds hE hcert hq h
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case certSeq c =>
      rcases cs with _ | ⟨c₀, cs⟩
      · simp only [checkStep, List.map_nil, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hΦ, hφ⟩, hc⟩ := h
        exact certSeq_sound hM hG hρ hps hds hE hcert hΦ hφ hc
      · simp [checkStep] at h
    case quotInd kq θ =>
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, cs⟩⟩
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · rename_i c Γ' p hp
          split at h
          · rename_i fg Φ' hfg hlow
            obtain ⟨f, g⟩ := fg
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨hl, hθ, rfl, hφ⟩, hp₀⟩ := h
            exact quotInd_sound hM hG hρ hps hds hp hfg hl hθ hlow hφ
              ((ih c₀ (by simp)).2 _ _ _ hp₀)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case zeroInd i =>
      rcases cs with _ | ⟨c₀, cs⟩
      · simp only [checkStep, List.map_nil, decide_eq_true_eq] at h
        exact zeroInd_sound hM hG hρ hps hds h.1 h.2
      · simp [checkStep] at h
    all_goals simp [checkStep] at h

end Proofs

end Geb.FreeTopos.Internal

end

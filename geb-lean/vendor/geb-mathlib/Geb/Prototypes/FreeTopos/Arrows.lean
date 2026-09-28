/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Infer

set_option doc.verso true in
/-!
# The arrows of a model of the theory

The structure of a model of the theory of an elementary topos, extended by definitions, stated
of the values of terms at an assignment: that an object term denotes an object
({lit}`IsObj`), and that an arrow term denotes an arrow between the objects two object terms
denote ({lit}`Hom`). The operations' typings and the equations of the cartesian closed structure
and the folds are derived from the axioms, each an instance of an axiom or a composite of such
instances, and each stated of the values of terms, so that a term's value is computed from its
subterms' values.

## Main definitions

* {lit}`IsObj` — an object term denotes an object.
* {lit}`Hom` — an arrow term denotes an arrow between two objects.

## Main statements

* {lit}`subst_x`, {lit}`subst_vars`, {lit}`subst_subst` — the unit laws and the associativity
  of substitution.
* {lit}`holds_inst` — an instance of an axiom holds when the instances of its hypotheses do.
* {lit}`comp_hom`, {lit}`pair_hom`, {lit}`curry_hom` — the typings of the operations.
* {lit}`comp_assoc`, {lit}`fst_pair`, {lit}`pair_comp`, {lit}`curry_comp` — the equations.
* {lit}`holds_monoCond_diag`, {lit}`chi_diag_hom`, {lit}`chi_diag_pair_self` — the diagonal is a
  monomorphism, whose characteristic map after the pairing of an arrow with itself is truth.

## Tags

elementary topos, cartesian closed category, model, partial Horn logic
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn Sorts
open scoped FinEnum

universe v

/-- Every axiom of a theory is an axiom of each iterated extension of it. -/
theorem mem_extendAll_axioms (ds : List Defn) :
    ∀ (T : Theory) {a : Seq}, a ∈ T.axioms → a ∈ (T.extendAll ds).axioms :=
  ds.rec (motive := fun ds ↦ ∀ (T : Theory) {a : Seq}, a ∈ T.axioms → a ∈ (T.extendAll ds).axioms)
    (fun _ _ h ↦ h) fun d _ ih T _ h ↦ ih (T.extend d) (List.mem_append_left _ h)

/-- An axiom by its index. -/
theorem axiom_mem {j : ℕ} {a : Seq} (h : axioms[j]? = some a) : a ∈ axioms :=
  List.mem_of_getElem? h

/-- Substitution in an application substitutes in the arguments. -/
theorem subst_op (ts : List Tree) (k : ℕ) (cs : List Tree) :
    subst ts (op k cs) = op k (cs.map (subst ts)) :=
  subst_node_succ ts k cs

/-- Substitution at a variable in the substitution's range. -/
theorem subst_x (ts : List Tree) (i : ℕ) : subst ts (x i) = ts[i]?.getD (x i) := by
  simp [x, var, subst_node_zero _ (rfl : (RoseTree.node i [] : Tree).children = [])]

/-- Substituting after a substitution is substituting the substituted terms, for a term in the
first substitution's scope. -/
theorem subst_subst (θ θ' : List Tree) :
    ∀ t : Tree, Scoped θ'.length t = true → subst θ (subst θ' t) = subst (θ'.map (subst θ)) t :=
  RoseTree.ind fun l cs ih ht ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [Scoped] at ht
      rotate_left
      · simp [Scoped] at ht
      obtain ⟨hc, ht⟩ := scoped_node_zero_iff.mp ht
      rw [subst_node_zero _ hc, subst_node_zero _ hc, List.getElem?_eq_getElem ht,
        List.getElem?_eq_getElem (by simpa using ht)]
      simp
    · rw [scoped_node_succ, List.all_eq_true] at ht
      rw [subst_node_succ, subst_node_succ, subst_node_succ, List.map_map]
      exact congrArg (RoseTree.node (k + 1))
        (List.map_congr_left fun c hc ↦ ih c hc (ht c hc))

/-- Substituting its variables for the variables of a term in their scope leaves the term: the
unit law of substitution on the right. -/
theorem subst_vars (n : ℕ) :
    ∀ t : Tree, Scoped n t = true → subst ((List.range n).map var) t = t :=
  RoseTree.ind fun l cs ih ht ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [Scoped] at ht
      rotate_left
      · simp [Scoped] at ht
      obtain ⟨hi, ht⟩ := scoped_node_zero_iff.mp ht
      rw [subst_node_zero _ hi, List.getElem?_map, List.getElem?_range ht]
      simp only [Option.map_some, Option.getD_some, var]
      rw [← hi, RoseTree.node_label_children]
    · rw [scoped_node_succ, List.all_eq_true] at ht
      rw [subst_node_succ]
      exact congrArg (RoseTree.node (k + 1))
        ((List.map_congr_left fun c hc ↦ ih c hc (ht c hc)).trans (List.map_id cs))

/-- Substitution in a composite. -/
theorem subst_comp (θ : List Tree) (g f : Tree) :
    subst θ (comp g f) = comp (subst θ g) (subst θ f) := subst_op θ 3 [g, f]

/-- Substitution in a pairing. -/
theorem subst_pair (θ : List Tree) (f g : Tree) :
    subst θ (pair f g) = pair (subst θ f) (subst θ g) := subst_op θ 9 [f, g]

/-- Substitution in a product. -/
theorem subst_prod (θ : List Tree) (a b : Tree) :
    subst θ (prod a b) = prod (subst θ a) (subst θ b) := subst_op θ 6 [a, b]

/-- Substitution in an exponential. -/
theorem subst_exp (θ : List Tree) (a b : Tree) :
    subst θ (exp a b) = exp (subst θ a) (subst θ b) := subst_op θ 22 [a, b]

/-- Substitution in a list object. -/
theorem subst_list (θ : List Tree) (a : Tree) : subst θ (list a) = list (subst θ a) :=
  subst_op θ 33 [a]

/-- Substitution in a first projection. -/
theorem subst_fst (θ : List Tree) (a b : Tree) :
    subst θ (fst a b) = fst (subst θ a) (subst θ b) := subst_op θ 7 [a, b]

/-- Substitution in a second projection. -/
theorem subst_snd (θ : List Tree) (a b : Tree) :
    subst θ (snd a b) = snd (subst θ a) (subst θ b) := subst_op θ 8 [a, b]

/-- Substitution in a currying. -/
theorem subst_curry (θ : List Tree) (c a f : Tree) :
    subst θ (curry c a f) = curry (subst θ c) (subst θ a) (subst θ f) := subst_op θ 24 [c, a, f]

/-- Substitution in an evaluation. -/
theorem subst_ev (θ : List Tree) (a b : Tree) :
    subst θ (ev a b) = ev (subst θ a) (subst θ b) := subst_op θ 23 [a, b]

/-- Substitution in an arrow to the terminal object. -/
theorem subst_bang (θ : List Tree) (a : Tree) : subst θ (bang a) = bang (subst θ a) :=
  subst_op θ 5 [a]

/-- Substitution in an identity. -/
theorem subst_idt (θ : List Tree) (a : Tree) : subst θ (idt a) = idt (subst θ a) :=
  subst_op θ 2 [a]

/-- Substitution in a fold of the natural numbers object. -/
theorem subst_natRec (θ : List Tree) (z s : Tree) :
    subst θ (natRec z s) = natRec (subst θ z) (subst θ s) := subst_op θ 32 [z, s]

/-- Substitution in a fold of a list object. -/
theorem subst_listRec (θ : List Tree) (a z s : Tree) :
    subst θ (listRec a z s) = listRec (subst θ a) (subst θ z) (subst θ s) :=
  subst_op θ 36 [a, z, s]

/-- Substitution in a fold of the rose-tree object. -/
theorem subst_roseRec (θ : List Tree) (s : Tree) : subst θ (roseRec s) = roseRec (subst θ s) :=
  subst_op θ 39 [s]

/-- Substitution in a rose-tree object over an object of labels. -/
theorem subst_lrose (θ : List Tree) (a : Tree) : subst θ (lrose a) = lrose (subst θ a) :=
  subst_op θ 40 [a]

/-- Substitution in a fold of a rose-tree object over an object of labels. -/
theorem subst_lroseRec (θ : List Tree) (a s : Tree) :
    subst θ (lroseRec a s) = lroseRec (subst θ a) (subst θ s) :=
  subst_op θ 42 [a, s]

/-- Substitution leaves the constants. -/
theorem subst_const (θ : List Tree) (k : ℕ) : subst θ (op k []) = op k [] := subst_op θ k []

/-- Substitution in a characteristic map. -/
theorem subst_chi (θ : List Tree) (m : Tree) : subst θ (chi m) = chi (subst θ m) :=
  subst_op θ 27 [m]

/-- Substitution in a diagonal. -/
theorem subst_diag (θ : List Tree) (a : Tree) : subst θ (diag a) = diag (subst θ a) := by
  rw [diag, subst_pair, subst_idt]
  rfl

/-- Substitution leaves the subobject classifier. -/
theorem subst_omega (θ : List Tree) : subst θ omega = omega := subst_const θ 25

/-- Substitution leaves the terminal object. -/
theorem subst_one (θ : List Tree) : subst θ one = one := subst_const θ 4

/-- Substitution leaves the natural numbers object. -/
theorem subst_nat (θ : List Tree) : subst θ nat = nat := subst_const θ 29

/-- Substitution leaves the rose-tree object. -/
theorem subst_rose (θ : List Tree) : subst θ rose = rose := subst_const θ 37

variable {defs : List Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}

/-- Applications of an operation to arguments of equal values have equal values. -/
theorem eval_op_congr (k : ℕ) {ts ts' : List Tree} (h : ts.map (eval M ρ) = ts'.map (eval M ρ)) :
    eval M ρ (op k ts) = eval M ρ (op k ts') := by
  rw [eval_op, eval_op, mapM_congr_map h]

/-- Unary applications of an operation to arguments of equal values have equal values. -/
theorem eval_op₁_congr (k : ℕ) {s s' : Tree} (h : eval M ρ s = eval M ρ s') :
    eval M ρ (op k [s]) = eval M ρ (op k [s']) :=
  eval_op_congr k (by simp [h])

/-- Binary applications of an operation to arguments of equal values have equal values. -/
theorem eval_op₂_congr (k : ℕ) {s s' t t' : Tree} (h : eval M ρ s = eval M ρ s')
    (h' : eval M ρ t = eval M ρ t') : eval M ρ (op k [s, t]) = eval M ρ (op k [s', t']) :=
  eval_op_congr k (by simp [h, h'])

/-- Ternary applications of an operation to arguments of equal values have equal values. -/
theorem eval_op₃_congr (k : ℕ) {s s' t t' u u' : Tree} (h : eval M ρ s = eval M ρ s')
    (h' : eval M ρ t = eval M ρ t') (h'' : eval M ρ u = eval M ρ u') :
    eval M ρ (op k [s, t, u]) = eval M ρ (op k [s', t', u']) :=
  eval_op_congr k (by simp [h, h', h''])

/-- An instance of an axiom of the theory holds at terms whose values have the sorts of its
context, when the instances of its hypotheses do. -/
theorem holds_inst (hM : IsModel (ext defs) M) {a : Seq} (ha : a ∈ axioms)
    (hsc : a.Scoped = true) {ts : List Tree} {ws : List M.Val}
    (hts : ts.map (eval M ρ) = ws.map Part.some) (hs : ws.map Sigma.fst = a.ctx)
    (hH : ∀ h ∈ a.hyps, (h.subst ts).Holds M ρ) : (a.concl.subst ts).Holds M ρ := by
  have hlen : ts.length = a.ctx.length := by
    rw [← hs, List.length_map, ← List.length_map (f := eval M ρ), hts, List.length_map]
  have key : ∀ q : Eqn, Scoped a.ctx.length q.lhs = true → Scoped a.ctx.length q.rhs = true →
      ((q.subst ts).Holds M ρ ↔ q.Holds M ws) := fun q hl hr ↦ by
    simp only [Eqn.Holds, Eqn.subst]
    rw [eval_subst hts _ (hlen ▸ hl), eval_subst hts _ (hlen ▸ hr)]
  obtain ⟨hl, hr⟩ := scoped_concl hsc
  refine (key _ hl hr).mpr (hM a (mem_extendAll_axioms defs theory ha) ws hs fun h hh ↦ ?_)
  obtain ⟨hl', hr'⟩ := scoped_hyps hsc h hh
  exact (key h hl' hr').mp (hH h hh)

/-- The iterated extension of a signature keeps its operations. -/
theorem sig_extendAll_getElem? (ds : List Defn) :
    ∀ (S : Sig) {k : ℕ}, k < S.length → (S.extendAll ds)[k]? = S[k]? :=
  ds.rec (motive := fun ds ↦ ∀ (S : Sig) {k : ℕ}, k < S.length → (S.extendAll ds)[k]? = S[k]?)
    (fun _ _ _ ↦ rfl) fun d _ ih S k hk ↦
      (ih (S.extend d) (by simp only [Sig.extend, List.length_append]; omega)).trans
        (getElem?_extend_of_lt hk)

/-- A signature is an initial segment of each of its iterated extensions. -/
theorem prefix_sig_extendAll (ds : List Defn) : ∀ S : Sig, S <+: S.extendAll ds :=
  ds.rec (fun S ↦ List.prefix_refl S) fun d _ ih S ↦
    (List.prefix_append S [(d.ctx, d.sort)]).trans (ih (S.extend d))

/-- The theory extended by an initial segment of a list of definitions has a signature that
begins the signature of the theory extended by the list, and axioms among its axioms. -/
theorem ext_prefix {cds defs : List Defn} (h : cds <+: defs) :
    (ext cds).sig <+: (ext defs).sig ∧ ∀ a ∈ (ext cds).axioms, a ∈ (ext defs).axioms := by
  obtain ⟨rest, rfl⟩ := h
  have hext : ext (cds ++ rest) = (ext cds).extendAll rest := List.foldl_append ..
  rw [hext]
  exact ⟨by rw [Theory.extendAll_sig rest (ext cds)]; exact prefix_sig_extendAll rest _,
    fun a ha ↦ mem_extendAll_axioms rest _ ha⟩

/-- A model of the theory extended by a list of definitions is a model in which the axioms of a
well-formed environment of an initial segment of the list are valid. -/
theorem ExtEnv.WF.sound {E : ExtEnv} (hE : E.WF) {defs : List Defn} (hdefs : E.defs <+: defs)
    {M : Model.{v} (ext defs).sig} (hM : IsModel (ext defs) M) : E.Sound M := by
  obtain ⟨hsig, hax⟩ := ext_prefix hdefs
  refine ⟨fun j a ha ↦ hM a (hax a (hE.axs j a ha)), fun k o ho ↦ ?_⟩
  rw [hE.sg] at ho
  obtain ⟨t, ht⟩ := hsig
  rw [← ht, List.getElem?_append_left (List.getElem?_eq_some_iff.mp ho).1, ho]

/-- The axioms of a definition of a list are axioms of the iterated extension, its operation's
index the theory's signature's length and its position. -/
theorem mem_extendAll_defn (ds : List Defn) :
    ∀ (T : Theory) {i : ℕ} {d : Defn}, ds[i]? = some d →
      ∀ a ∈ d.axioms (T.sig.length + i), a ∈ (T.extendAll ds).axioms :=
  ds.rec (motive := fun ds ↦ ∀ (T : Theory) {i : ℕ} {d : Defn}, ds[i]? = some d →
      ∀ a ∈ d.axioms (T.sig.length + i), a ∈ (T.extendAll ds).axioms)
    (fun _ _ _ hd _ _ ↦ by simp at hd) fun d' ds ih T i d hd a ha ↦ by
      rcases i with _ | j
      · obtain rfl : d' = d := by simpa using hd
        exact mem_extendAll_axioms ds (T.extend d') (List.mem_append_right _ ha)
      · have hl : (T.extend d').sig.length + j = T.sig.length + (j + 1) := by
          simp only [Theory.extend, Sig.extend, List.length_append, List.length_singleton]
          omega
        exact ih (T.extend d') (by simpa using hd) a (hl ▸ ha)

variable (M ρ) in
/-- An object term denotes an object at an assignment. -/
def IsObj (X : Tree) : Prop := ∃ w, eval M ρ X = Part.some w ∧ w.1 = obj

variable (M ρ) in
/-- An arrow term denotes an arrow at an assignment, from the object {lit}`X` denotes to the
object {lit}`Y` denotes. -/
def Hom (f X Y : Tree) : Prop :=
  ∃ w, eval M ρ f = Part.some w ∧ w.1 = arr ∧ IsObj M ρ X ∧ IsObj M ρ Y ∧
    eval M ρ (dom f) = eval M ρ X ∧ eval M ρ (cod f) = eval M ρ Y

/-- An instance of the axiom of index {lit}`j`, its hypotheses' and conclusion's instances
computed by {lit}`rfl`. -/
theorem ax_holds (hM : IsModel (ext defs) M) (j : ℕ) {a : Seq} (ha : axioms[j]? = some a)
    (hsc : a.Scoped = true) {ts : List Tree} {ws : List M.Val}
    (hts : ts.map (eval M ρ) = ws.map Part.some) (hs : ws.map Sigma.fst = a.ctx)
    {hs' : List Eqn} (hH' : a.hyps.map (Eqn.subst ts) = hs') (hH : hs'.Forall (Eqn.Holds M ρ))
    {q : Eqn} (hq : a.concl.subst ts = q) : q.Holds M ρ :=
  hq ▸ holds_inst hM (axiom_mem ha) hsc hts hs fun _ hh ↦
    List.forall_iff_forall_mem.mp hH _ (hH' ▸ List.mem_map_of_mem hh)

/-- The two sides of an equation that holds have one value. -/
theorem eval_eq_of_holds {s t : Tree} (h : Eqn.Holds M ρ ⟨s, t⟩) : eval M ρ s = eval M ρ t := by
  obtain ⟨w, hs, ht⟩ := h
  rw [hs, ht]

/-- An equation holds when its sides have one value. -/
theorem holds_of_eval_eq {s t : Tree} {w : M.Val} (h : eval M ρ s = eval M ρ t)
    (ht : eval M ρ t = Part.some w) : Eqn.Holds M ρ ⟨s, t⟩ :=
  ⟨w, h.trans ht, ht⟩

/-- The value of an application has the sort of the operation's result. -/
theorem sort_of_eval_op {k : ℕ} {ss : List ℕ} {s : ℕ} (hk : sig[k]? = some (ss, s))
    {ts : List Tree} {w : M.Val} (h : eval M ρ (op k ts) = Part.some w) : w.1 = s := by
  rw [eval_op] at h
  obtain ⟨vs, -, hw⟩ := part_bind_eq_some_iff.mp h
  have ho := M.op_sort (hw ▸ Part.mem_some w)
  have hlt : k < sig.length := (List.getElem?_eq_some_iff.mp hk).1
  have hsig : (ext defs).sig[k]? = sig[k]? :=
    (congrArg (·[k]?) (Theory.extendAll_sig defs theory)).trans
      (sig_extendAll_getElem? defs sig hlt)
  rw [hsig, hk] at ho
  exact (Option.some_inj.mp ho).symm

/-- An application with a value has arguments with values. -/
theorem exists_eval_of_eval_op {k : ℕ} {ts : List Tree} {w : M.Val}
    (h : eval M ρ (op k ts) = Part.some w) : ∀ t ∈ ts, ∃ v, eval M ρ t = Part.some v := by
  rw [eval_op] at h
  obtain ⟨vs, hvs, -⟩ := part_bind_eq_some_iff.mp h
  have hm := (mapM_part_eq_some_iff ts vs).mp hvs
  intro t ht
  obtain ⟨v, -, hv⟩ := List.mem_map.mp (hm ▸ List.mem_map_of_mem ht)
  exact ⟨v, hv.symm⟩

/-- The argument of a unary application with a value has a value. -/
theorem exists_eval_of_eval_op₁ {k : ℕ} {t : Tree} {w : M.Val}
    (h : eval M ρ (op k [t]) = Part.some w) : ∃ v, eval M ρ t = Part.some v :=
  exists_eval_of_eval_op h t List.mem_cons_self

/-- A term of the value of an object is an object. -/
theorem IsObj.congr {X X' : Tree} (h : IsObj M ρ X) (he : eval M ρ X' = eval M ρ X) :
    IsObj M ρ X' := by
  obtain ⟨w, hw, hs⟩ := h
  exact ⟨w, he.trans hw, hs⟩

/-- A term of the value of an arrow is an arrow between objects of the same values. -/
theorem Hom.congr {f X Y f' X' Y' : Tree} (h : Hom M ρ f X Y) (hf : eval M ρ f' = eval M ρ f)
    (hX : eval M ρ X' = eval M ρ X) (hY : eval M ρ Y' = eval M ρ Y) : Hom M ρ f' X' Y' := by
  obtain ⟨w, hw, hs, hXo, hYo, hd, hc⟩ := h
  have hb : ∀ o, eval M ρ (op o [f']) = eval M ρ (op o [f]) := fun o ↦
    eval_op_congr o (by simp [hf])
  exact ⟨w, hf.trans hw, hs, hXo.congr hX, hYo.congr hY, ((hb 0).trans hd).trans hX.symm,
    ((hb 1).trans hc).trans hY.symm⟩

/-- An arrow's value is an arrow. -/
theorem Hom.exists_eval {f X Y : Tree} (h : Hom M ρ f X Y) :
    ∃ w : M.Val, eval M ρ f = Part.some w ∧ w.1 = arr := by
  obtain ⟨w, hw, hs, -⟩ := h
  exact ⟨w, hw, hs⟩

section Objects

variable (hM : IsModel (ext defs) M)
include hM

/-- The terminal object. -/
theorem isObj_one : IsObj M ρ one := by
  obtain ⟨w, hw, -⟩ := ax_holds (ρ := ρ) hM 12 rfl (by decide) (ts := []) (ws := []) rfl rfl rfl
    trivial (q := ⟨one, one⟩) rfl
  exact ⟨w, hw, sort_of_eval_op rfl hw⟩

/-- The product of two objects. -/
theorem isObj_prod {A B : Tree} (hA : IsObj M ρ A) (hB : IsObj M ρ B) :
    IsObj M ρ (prod A B) := by
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨b, hb, hbs⟩ := hB
  obtain ⟨w, hw, -⟩ := ax_holds (ρ := ρ) hM 16 rfl (by decide) (ts := [A, B]) (ws := [a, b])
    (by simp [ha, hb]) (by simp [has, hbs]) rfl trivial (q := ⟨prod A B, prod A B⟩) rfl
  exact ⟨w, hw, sort_of_eval_op rfl hw⟩

/-- The exponential of two objects. -/
theorem isObj_exp {A B : Tree} (hA : IsObj M ρ A) (hB : IsObj M ρ B) :
    IsObj M ρ (exp A B) := by
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨b, hb, hbs⟩ := hB
  obtain ⟨w, hw, -⟩ := ax_holds (ρ := ρ) hM 74 rfl (by decide) (ts := [A, B]) (ws := [a, b])
    (by simp [ha, hb]) (by simp [has, hbs]) rfl trivial (q := ⟨exp A B, exp A B⟩) rfl
  exact ⟨w, hw, sort_of_eval_op rfl hw⟩

/-- The subobject classifier. -/
theorem isObj_omega : IsObj M ρ omega := by
  obtain ⟨w, hw, -⟩ := ax_holds (ρ := ρ) hM 83 rfl (by decide) (ts := []) (ws := []) rfl rfl rfl
    trivial (q := ⟨omega, omega⟩) rfl
  exact ⟨w, hw, sort_of_eval_op rfl hw⟩

/-- The natural numbers object. -/
theorem isObj_nat : IsObj M ρ nat := by
  obtain ⟨w, -, hw⟩ := ax_holds (ρ := ρ) hM 99 rfl (by decide) (ts := []) (ws := []) rfl rfl rfl
    trivial (q := ⟨cod zeroN, nat⟩) rfl
  exact ⟨w, hw, sort_of_eval_op rfl hw⟩

/-- The list object of an object. -/
theorem isObj_list {A : Tree} (hA : IsObj M ρ A) : IsObj M ρ (list A) := by
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨w, hw, -⟩ := ax_holds (ρ := ρ) hM 111 rfl (by decide) (ts := [A]) (ws := [a])
    (by simp [ha]) (by simp [has]) rfl trivial (q := ⟨list A, list A⟩) rfl
  exact ⟨w, hw, sort_of_eval_op rfl hw⟩

/-- The rose-tree object. -/
theorem isObj_rose : IsObj M ρ rose := by
  obtain ⟨w, -, hw⟩ := ax_holds (ρ := ρ) hM 126 rfl (by decide) (ts := []) (ws := []) rfl rfl rfl
    trivial (q := ⟨cod node, rose⟩) rfl
  exact ⟨w, hw, sort_of_eval_op rfl hw⟩

/-- The rose-tree object over an object of labels. -/
theorem isObj_lrose {A : Tree} (hA : IsObj M ρ A) : IsObj M ρ (lrose A) := by
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨w, hw, -⟩ := ax_holds (ρ := ρ) hM 133 rfl (by decide) (ts := [A]) (ws := [a])
    (by simp [ha]) (by simp [has]) rfl trivial (q := ⟨lrose A, lrose A⟩) rfl
  exact ⟨w, hw, sort_of_eval_op rfl hw⟩

end Objects

/-- An arrow's domain is an object. -/
theorem Hom.isObj_dom {f X Y : Tree} (h : Hom M ρ f X Y) : IsObj M ρ X := by
  obtain ⟨-, -, -, hX, -⟩ := h
  exact hX

/-- An arrow's codomain is an object. -/
theorem Hom.isObj_cod {f X Y : Tree} (h : Hom M ρ f X Y) : IsObj M ρ Y := by
  obtain ⟨-, -, -, -, hY, -⟩ := h
  exact hY

/-- The value of an arrow's domain is its domain's. -/
theorem Hom.eval_dom {f X Y : Tree} (h : Hom M ρ f X Y) : eval M ρ (dom f) = eval M ρ X := by
  obtain ⟨-, -, -, -, -, hd, -⟩ := h
  exact hd

/-- The value of an arrow's codomain is its codomain's. -/
theorem Hom.eval_cod {f X Y : Tree} (h : Hom M ρ f X Y) : eval M ρ (cod f) = eval M ρ Y := by
  obtain ⟨-, -, -, -, -, -, hc⟩ := h
  exact hc

/-- A term whose domain has a value has a value. -/
theorem exists_eval_of_dom {f : Tree} {w : M.Val} (h : eval M ρ (dom f) = Part.some w) :
    ∃ v, eval M ρ f = Part.some v :=
  exists_eval_of_eval_op₁ h

section Arrows

variable (hM : IsModel (ext defs) M)
include hM

/-- The identity of an object is an arrow from it to itself. -/
theorem idt_hom {X : Tree} (hX : IsObj M ρ X) : Hom M ρ (idt X) X X := by
  obtain ⟨a, ha, has⟩ := hX
  have hts : [X].map (eval M ρ) = [a].map Part.some := by simp [ha]
  have hs : [a].map Sigma.fst = [obj] := by simp [has]
  obtain ⟨w, hw, -⟩ := ax_holds hM 2 rfl (by decide) hts hs rfl trivial
    (q := ⟨idt X, idt X⟩) rfl
  exact ⟨w, hw, sort_of_eval_op rfl hw, ⟨a, ha, has⟩, ⟨a, ha, has⟩,
    eval_eq_of_holds (ax_holds hM 8 rfl (by decide) hts hs rfl trivial
      (q := ⟨dom (idt X), X⟩) rfl),
    eval_eq_of_holds (ax_holds hM 9 rfl (by decide) hts hs rfl trivial
      (q := ⟨cod (idt X), X⟩) rfl)⟩

/-- A composite of arrows end to end is an arrow. -/
theorem comp_hom {f g X Y Z : Tree} (hf : Hom M ρ f X Y) (hg : Hom M ρ g Y Z) :
    Hom M ρ (comp g f) X Z := by
  obtain ⟨wf, hwf, hfs, hX, ⟨y, hy, -⟩, hdf, hcf⟩ := hf
  obtain ⟨wg, hwg, hgs, -, hZ, hdg, hcg⟩ := hg
  have hts : [g, f].map (eval M ρ) = [wg, wf].map Part.some := by simp [hwg, hwf]
  have hs : [wg, wf].map Sigma.fst = [arr, arr] := by simp [hgs, hfs]
  obtain ⟨w, hw, -⟩ := ax_holds hM 4 rfl (by decide) hts hs (hs' := [⟨cod f, dom g⟩]) rfl
    (holds_of_eval_eq (hcf.trans hdg.symm) (hdg.trans hy)) (q := ⟨comp g f, comp g f⟩) rfl
  have hc : Eqn.Holds M ρ ⟨comp g f, comp g f⟩ := ⟨w, hw, hw⟩
  refine ⟨w, hw, sort_of_eval_op rfl hw, hX, hZ, ?_, ?_⟩
  · exact (eval_eq_of_holds (ax_holds hM 5 rfl (by decide) hts hs
      (hs' := [⟨comp g f, comp g f⟩]) rfl hc (q := ⟨dom (comp g f), dom f⟩) rfl)).trans hdf
  · exact (eval_eq_of_holds (ax_holds hM 6 rfl (by decide) hts hs
      (hs' := [⟨comp g f, comp g f⟩]) rfl hc (q := ⟨cod (comp g f), cod g⟩) rfl)).trans hcg

/-- The arrow from an object to the terminal object. -/
theorem bang_hom {X : Tree} (hX : IsObj M ρ X) : Hom M ρ (bang X) X one := by
  obtain ⟨a, ha, has⟩ := hX
  have hts : [X].map (eval M ρ) = [a].map Part.some := by simp [ha]
  have hs : [a].map Sigma.fst = [obj] := by simp [has]
  have hd := eval_eq_of_holds (ax_holds hM 13 rfl (by decide) hts hs rfl trivial
    (q := ⟨dom (bang X), X⟩) rfl)
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans ha)
  exact ⟨w, hw, sort_of_eval_op rfl hw, ⟨a, ha, has⟩, isObj_one hM, hd,
    eval_eq_of_holds (ax_holds hM 14 rfl (by decide) hts hs rfl trivial
      (q := ⟨cod (bang X), one⟩) rfl)⟩

/-- The first projection of a product. -/
theorem fst_hom {A B : Tree} (hA : IsObj M ρ A) (hB : IsObj M ρ B) :
    Hom M ρ (fst A B) (prod A B) A := by
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨b, hb, hbs⟩ := hB
  have hts : [A, B].map (eval M ρ) = [a, b].map Part.some := by simp [ha, hb]
  have hs : [a, b].map Sigma.fst = [obj, obj] := by simp [has, hbs]
  have hP := isObj_prod hM ⟨a, ha, has⟩ ⟨b, hb, hbs⟩
  obtain ⟨p, hp, -⟩ := hP
  have hd := eval_eq_of_holds (ax_holds hM 17 rfl (by decide) hts hs rfl trivial
    (q := ⟨dom (fst A B), prod A B⟩) rfl)
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans hp)
  exact ⟨w, hw, sort_of_eval_op rfl hw, isObj_prod hM ⟨a, ha, has⟩ ⟨b, hb, hbs⟩, ⟨a, ha, has⟩,
    hd, eval_eq_of_holds (ax_holds hM 18 rfl (by decide) hts hs rfl trivial
      (q := ⟨cod (fst A B), A⟩) rfl)⟩

/-- The second projection of a product. -/
theorem snd_hom {A B : Tree} (hA : IsObj M ρ A) (hB : IsObj M ρ B) :
    Hom M ρ (snd A B) (prod A B) B := by
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨b, hb, hbs⟩ := hB
  have hts : [A, B].map (eval M ρ) = [a, b].map Part.some := by simp [ha, hb]
  have hs : [a, b].map Sigma.fst = [obj, obj] := by simp [has, hbs]
  obtain ⟨p, hp, -⟩ := isObj_prod hM ⟨a, ha, has⟩ ⟨b, hb, hbs⟩
  have hd := eval_eq_of_holds (ax_holds hM 19 rfl (by decide) hts hs rfl trivial
    (q := ⟨dom (snd A B), prod A B⟩) rfl)
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans hp)
  exact ⟨w, hw, sort_of_eval_op rfl hw, isObj_prod hM ⟨a, ha, has⟩ ⟨b, hb, hbs⟩, ⟨b, hb, hbs⟩,
    hd, eval_eq_of_holds (ax_holds hM 20 rfl (by decide) hts hs rfl trivial
      (q := ⟨cod (snd A B), B⟩) rfl)⟩

/-- The pairing of two arrows of one domain. -/
theorem pair_hom {f g X A B : Tree} (hf : Hom M ρ f X A) (hg : Hom M ρ g X B) :
    Hom M ρ (pair f g) X (prod A B) := by
  obtain ⟨wf, hwf, hfs, ⟨x, hx, hxs⟩, hA, hdf, hcf⟩ := hf
  obtain ⟨wg, hwg, hgs, -, hB, hdg, hcg⟩ := hg
  have hts : [f, g].map (eval M ρ) = [wf, wg].map Part.some := by simp [hwf, hwg]
  have hs : [wf, wg].map Sigma.fst = [arr, arr] := by simp [hfs, hgs]
  obtain ⟨w, hw, -⟩ := ax_holds hM 22 rfl (by decide) hts hs (hs' := [⟨dom f, dom g⟩]) rfl
    (holds_of_eval_eq (hdf.trans hdg.symm) (hdg.trans hx)) (q := ⟨pair f g, pair f g⟩) rfl
  have hc : Eqn.Holds M ρ ⟨pair f g, pair f g⟩ := ⟨w, hw, hw⟩
  refine ⟨w, hw, sort_of_eval_op rfl hw, ⟨x, hx, hxs⟩, isObj_prod hM hA hB, ?_, ?_⟩
  · exact (eval_eq_of_holds (ax_holds hM 23 rfl (by decide) hts hs
      (hs' := [⟨pair f g, pair f g⟩]) rfl hc (q := ⟨dom (pair f g), dom f⟩) rfl)).trans hdf
  · exact (eval_eq_of_holds (ax_holds hM 24 rfl (by decide) hts hs
      (hs' := [⟨pair f g, pair f g⟩]) rfl hc (q := ⟨cod (pair f g), prod (cod f) (cod g)⟩)
      rfl)).trans (eval_op₂_congr 6 hcf hcg)

/-- The evaluation arrow of an exponential. -/
theorem ev_hom {A B : Tree} (hA : IsObj M ρ A) (hB : IsObj M ρ B) :
    Hom M ρ (ev A B) (prod (exp A B) A) B := by
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨b, hb, hbs⟩ := hB
  have hts : [A, B].map (eval M ρ) = [a, b].map Part.some := by simp [ha, hb]
  have hs : [a, b].map Sigma.fst = [obj, obj] := by simp [has, hbs]
  have hP := isObj_prod hM (isObj_exp hM ⟨a, ha, has⟩ ⟨b, hb, hbs⟩) ⟨a, ha, has⟩
  obtain ⟨p, hp, -⟩ := id hP
  have hd := eval_eq_of_holds (ax_holds hM 75 rfl (by decide) hts hs rfl trivial
    (q := ⟨dom (ev A B), prod (exp A B) A⟩) rfl)
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans hp)
  exact ⟨w, hw, sort_of_eval_op rfl hw, hP, ⟨b, hb, hbs⟩, hd,
    eval_eq_of_holds (ax_holds hM 76 rfl (by decide) hts hs rfl trivial
      (q := ⟨cod (ev A B), B⟩) rfl)⟩

/-- The currying of an arrow from a product. -/
theorem curry_hom {f X A B : Tree} (hX : IsObj M ρ X) (hA : IsObj M ρ A)
    (hf : Hom M ρ f (prod X A) B) : Hom M ρ (curry X A f) X (exp A B) := by
  obtain ⟨x, hx, hxs⟩ := hX
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨wf, hwf, hfs, ⟨p, hp, -⟩, hB, hdf, hcf⟩ := hf
  have hts : [X, A, f].map (eval M ρ) = [x, a, wf].map Part.some := by simp [hx, ha, hwf]
  have hs : [x, a, wf].map Sigma.fst = [obj, obj, arr] := by simp [hxs, has, hfs]
  obtain ⟨w, hw, -⟩ := ax_holds hM 78 rfl (by decide) hts hs (hs' := [⟨dom f, prod X A⟩]) rfl
    (holds_of_eval_eq hdf hp) (q := ⟨curry X A f, curry X A f⟩) rfl
  have hc : Eqn.Holds M ρ ⟨curry X A f, curry X A f⟩ := ⟨w, hw, hw⟩
  refine ⟨w, hw, sort_of_eval_op rfl hw, ⟨x, hx, hxs⟩, isObj_exp hM ⟨a, ha, has⟩ hB, ?_, ?_⟩
  · exact eval_eq_of_holds (ax_holds hM 79 rfl (by decide) hts hs
      (hs' := [⟨curry X A f, curry X A f⟩]) rfl hc (q := ⟨dom (curry X A f), X⟩) rfl)
  · exact (eval_eq_of_holds (ax_holds hM 80 rfl (by decide) hts hs
      (hs' := [⟨curry X A f, curry X A f⟩]) rfl hc
      (q := ⟨cod (curry X A f), exp A (cod f)⟩) rfl)).trans (eval_op₂_congr 22 rfl hcf)

/-- The fold of the natural numbers object from a start by a step. -/
theorem natRec_hom {z s C : Tree} (hz : Hom M ρ z one C) (hs : Hom M ρ s C C) :
    Hom M ρ (natRec z s) nat C := by
  obtain ⟨wz, hwz, hzs, ⟨o, ho, -⟩, ⟨c, hc, -⟩, hdz, hcz⟩ := hz
  obtain ⟨ws, hws, hss, -, hC, hds, hcs⟩ := hs
  have hts : [z, s].map (eval M ρ) = [wz, ws].map Part.some := by simp [hwz, hws]
  have hsr : [wz, ws].map Sigma.fst = [arr, arr] := by simp [hzs, hss]
  obtain ⟨w, hw, -⟩ := ax_holds hM 105 rfl (by decide) hts hsr
    (hs' := [⟨dom z, one⟩, ⟨cod z, dom s⟩, ⟨dom s, cod s⟩]) rfl
    ⟨holds_of_eval_eq hdz ho, holds_of_eval_eq (hcz.trans hds.symm) (hds.trans hc),
      holds_of_eval_eq (hds.trans hcs.symm) (hcs.trans hc)⟩
    (q := ⟨natRec z s, natRec z s⟩) rfl
  have hr : Eqn.Holds M ρ ⟨natRec z s, natRec z s⟩ := ⟨w, hw, hw⟩
  exact ⟨w, hw, sort_of_eval_op rfl hw, isObj_nat hM, hC,
    eval_eq_of_holds (ax_holds hM 106 rfl (by decide) hts hsr
      (hs' := [⟨natRec z s, natRec z s⟩]) rfl hr (q := ⟨dom (natRec z s), nat⟩) rfl),
    (eval_eq_of_holds (ax_holds hM 107 rfl (by decide) hts hsr
      (hs' := [⟨natRec z s, natRec z s⟩]) rfl hr (q := ⟨cod (natRec z s), cod z⟩) rfl)).trans
      hcz⟩

/-- The fold of a list object from a start by a step. -/
theorem listRec_hom {A z s C : Tree} (hA : IsObj M ρ A) (hz : Hom M ρ z one C)
    (hs : Hom M ρ s (prod A C) C) : Hom M ρ (listRec A z s) (list A) C := by
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨wz, hwz, hzs, ⟨o, ho, -⟩, ⟨c, hc, -⟩, hdz, hcz⟩ := hz
  obtain ⟨ws, hws, hss, ⟨p, hp, -⟩, hC, hds, hcs⟩ := hs
  have hts : [A, z, s].map (eval M ρ) = [a, wz, ws].map Part.some := by simp [ha, hwz, hws]
  have hsr : [a, wz, ws].map Sigma.fst = [obj, arr, arr] := by simp [has, hzs, hss]
  have hpc : eval M ρ (prod A (cod s)) = eval M ρ (prod A C) := eval_op₂_congr 6 rfl hcs
  obtain ⟨w, hw, -⟩ := ax_holds hM 119 rfl (by decide) hts hsr
    (hs' := [⟨dom z, one⟩, ⟨cod z, cod s⟩, ⟨dom s, prod A (cod s)⟩]) rfl
    ⟨holds_of_eval_eq hdz ho, holds_of_eval_eq (hcz.trans hcs.symm) (hcs.trans hc),
      holds_of_eval_eq (hds.trans hpc.symm) (hpc.trans hp)⟩
    (q := ⟨listRec A z s, listRec A z s⟩) rfl
  have hr : Eqn.Holds M ρ ⟨listRec A z s, listRec A z s⟩ := ⟨w, hw, hw⟩
  exact ⟨w, hw, sort_of_eval_op rfl hw, isObj_list hM ⟨a, ha, has⟩, hC,
    eval_eq_of_holds (ax_holds hM 120 rfl (by decide) hts hsr
      (hs' := [⟨listRec A z s, listRec A z s⟩]) rfl hr (q := ⟨dom (listRec A z s), list A⟩) rfl),
    (eval_eq_of_holds (ax_holds hM 121 rfl (by decide) hts hsr
      (hs' := [⟨listRec A z s, listRec A z s⟩]) rfl hr
      (q := ⟨cod (listRec A z s), cod z⟩) rfl)).trans hcz⟩

/-- The fold of the rose-tree object by a step. -/
theorem roseRec_hom {s C : Tree} (hs : Hom M ρ s (prod nat (list C)) C) :
    Hom M ρ (roseRec s) rose C := by
  obtain ⟨ws, hws, hss, ⟨p, hp, -⟩, hC, hds, hcs⟩ := hs
  have hts : [s].map (eval M ρ) = [ws].map Part.some := by simp [hws]
  have hsr : [ws].map Sigma.fst = [arr] := by simp [hss]
  have hpc : eval M ρ (prod nat (list (cod s))) = eval M ρ (prod nat (list C)) :=
    eval_op₂_congr 6 rfl (eval_op₁_congr 33 hcs)
  obtain ⟨w, hw, -⟩ := ax_holds hM 128 rfl (by decide) hts hsr
    (hs' := [⟨dom s, prod nat (list (cod s))⟩]) rfl
    (holds_of_eval_eq (hds.trans hpc.symm) (hpc.trans hp)) (q := ⟨roseRec s, roseRec s⟩) rfl
  have hr : Eqn.Holds M ρ ⟨roseRec s, roseRec s⟩ := ⟨w, hw, hw⟩
  exact ⟨w, hw, sort_of_eval_op rfl hw, isObj_rose hM, hC,
    eval_eq_of_holds (ax_holds hM 129 rfl (by decide) hts hsr
      (hs' := [⟨roseRec s, roseRec s⟩]) rfl hr (q := ⟨dom (roseRec s), rose⟩) rfl),
    (eval_eq_of_holds (ax_holds hM 130 rfl (by decide) hts hsr
      (hs' := [⟨roseRec s, roseRec s⟩]) rfl hr (q := ⟨cod (roseRec s), cod s⟩) rfl)).trans
      hcs⟩

/-- Composition is associative. -/
theorem comp_assoc {f g h X Y Z W : Tree} (hf : Hom M ρ f X Y) (hg : Hom M ρ g Y Z)
    (hh : Hom M ρ h Z W) : eval M ρ (comp h (comp g f)) = eval M ρ (comp (comp h g) f) := by
  obtain ⟨wf, hwf, hfs⟩ := hf.exists_eval
  obtain ⟨wg, hwg, hgs⟩ := hg.exists_eval
  obtain ⟨wh, hwh, hhs⟩ := hh.exists_eval
  obtain ⟨w, hw, -⟩ := comp_hom hM (comp_hom hM hf hg) hh
  exact eval_eq_of_holds (ax_holds hM 7 rfl (by decide) (ts := [h, g, f]) (ws := [wh, wg, wf])
    (by simp [hwh, hwg, hwf]) (by simp [hhs, hgs, hfs])
    (hs' := [⟨comp h (comp g f), comp h (comp g f)⟩]) rfl ⟨w, hw, hw⟩
    (q := ⟨comp h (comp g f), comp (comp h g) f⟩) rfl)

/-- The identity after an arrow is the arrow. -/
theorem idt_comp {f X Y : Tree} (hf : Hom M ρ f X Y) : eval M ρ (comp (idt Y) f) = eval M ρ f := by
  obtain ⟨wf, hwf, hfs⟩ := hf.exists_eval
  refine (eval_op₂_congr 3 (eval_op₁_congr 2 hf.eval_cod.symm) rfl).trans ?_
  exact eval_eq_of_holds (ax_holds hM 11 rfl (by decide) (ts := [f]) (ws := [wf])
    (by simp [hwf]) (by simp [hfs]) rfl trivial (q := ⟨comp (idt (cod f)) f, f⟩) rfl)

/-- An arrow after the identity is the arrow. -/
theorem comp_idt {f X Y : Tree} (hf : Hom M ρ f X Y) : eval M ρ (comp f (idt X)) = eval M ρ f := by
  obtain ⟨wf, hwf, hfs⟩ := hf.exists_eval
  refine (eval_op₂_congr 3 rfl (eval_op₁_congr 2 hf.eval_dom.symm)).trans ?_
  exact eval_eq_of_holds (ax_holds hM 10 rfl (by decide) (ts := [f]) (ws := [wf])
    (by simp [hwf]) (by simp [hfs]) rfl trivial (q := ⟨comp f (idt (dom f)), f⟩) rfl)

/-- The first projection after a pairing is the first arrow. -/
theorem fst_pair {f g X A B : Tree} (hf : Hom M ρ f X A) (hg : Hom M ρ g X B) :
    eval M ρ (comp (fst A B) (pair f g)) = eval M ρ f := by
  obtain ⟨wf, hwf, hfs⟩ := hf.exists_eval
  obtain ⟨wg, hwg, hgs⟩ := hg.exists_eval
  obtain ⟨w, hw, -⟩ := pair_hom hM hf hg
  refine (eval_op₂_congr 3 (eval_op₂_congr 7 hf.eval_cod.symm hg.eval_cod.symm) rfl).trans ?_
  exact eval_eq_of_holds (ax_holds hM 25 rfl (by decide) (ts := [f, g]) (ws := [wf, wg])
    (by simp [hwf, hwg]) (by simp [hfs, hgs]) (hs' := [⟨pair f g, pair f g⟩]) rfl ⟨w, hw, hw⟩
    (q := ⟨comp (fst (cod f) (cod g)) (pair f g), f⟩) rfl)

/-- The second projection after a pairing is the second arrow. -/
theorem snd_pair {f g X A B : Tree} (hf : Hom M ρ f X A) (hg : Hom M ρ g X B) :
    eval M ρ (comp (snd A B) (pair f g)) = eval M ρ g := by
  obtain ⟨wf, hwf, hfs⟩ := hf.exists_eval
  obtain ⟨wg, hwg, hgs⟩ := hg.exists_eval
  obtain ⟨w, hw, -⟩ := pair_hom hM hf hg
  refine (eval_op₂_congr 3 (eval_op₂_congr 8 hf.eval_cod.symm hg.eval_cod.symm) rfl).trans ?_
  exact eval_eq_of_holds (ax_holds hM 26 rfl (by decide) (ts := [f, g]) (ws := [wf, wg])
    (by simp [hwf, hwg]) (by simp [hfs, hgs]) (hs' := [⟨pair f g, pair f g⟩]) rfl ⟨w, hw, hw⟩
    (q := ⟨comp (snd (cod f) (cod g)) (pair f g), g⟩) rfl)

/-- An arrow into a product is the pairing of its composites with the projections. -/
theorem pair_eta {h X A B : Tree} (hA : IsObj M ρ A) (hB : IsObj M ρ B)
    (hh : Hom M ρ h X (prod A B)) :
    eval M ρ (pair (comp (fst A B) h) (comp (snd A B) h)) = eval M ρ h := by
  obtain ⟨wh, hwh, hhs⟩ := hh.exists_eval
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨b, hb, hbs⟩ := hB
  obtain ⟨p, hp, -⟩ := hh.isObj_cod
  exact eval_eq_of_holds (ax_holds hM 27 rfl (by decide) (ts := [h, A, B]) (ws := [wh, a, b])
    (by simp [hwh, ha, hb]) (by simp [hhs, has, hbs]) (hs' := [⟨cod h, prod A B⟩]) rfl
    (holds_of_eval_eq hh.eval_cod hp)
    (q := ⟨pair (comp (fst A B) h) (comp (snd A B) h), h⟩) rfl)

/-- An arrow to the terminal object is the arrow from its domain to it. -/
theorem bang_unique {h X : Tree} (hh : Hom M ρ h X one) : eval M ρ h = eval M ρ (bang X) := by
  obtain ⟨wh, hwh, hhs⟩ := hh.exists_eval
  obtain ⟨o, ho, -⟩ := hh.isObj_cod
  exact (eval_eq_of_holds (ax_holds hM 15 rfl (by decide) (ts := [h]) (ws := [wh])
    (by simp [hwh]) (by simp [hhs]) (hs' := [⟨cod h, one⟩]) rfl
    (holds_of_eval_eq hh.eval_cod ho) (q := ⟨h, bang (dom h)⟩) rfl)).trans
    (eval_op₁_congr 5 hh.eval_dom)

/-- The arrow to the terminal object after an arrow is the arrow from the arrow's domain. -/
theorem comp_bang {h X Y : Tree} (hh : Hom M ρ h Y X) :
    eval M ρ (comp (bang X) h) = eval M ρ (bang Y) :=
  bang_unique hM (comp_hom hM hh (bang_hom hM hh.isObj_cod))

/-- A pairing after an arrow is the pairing of the composites. -/
theorem pair_comp {f g h X Y A B : Tree} (hf : Hom M ρ f X A) (hg : Hom M ρ g X B)
    (hh : Hom M ρ h Y X) :
    eval M ρ (comp (pair f g) h) = eval M ρ (pair (comp f h) (comp g h)) := by
  have hp := pair_hom hM hf hg
  have hA := hf.isObj_cod
  have hB := hg.isObj_cod
  refine (pair_eta hM hA hB (comp_hom hM hh hp)).symm.trans (eval_op₂_congr 9 ?_ ?_)
  · exact (comp_assoc hM hh hp (fst_hom hM hA hB)).trans (eval_op₂_congr 3 (fst_pair hM hf hg) rfl)
  · exact (comp_assoc hM hh hp (snd_hom hM hA hB)).trans (eval_op₂_congr 3 (snd_pair hM hf hg) rfl)

/-- Evaluation after the product of a currying with the identity is the curried arrow. -/
theorem ev_curry {f X A B : Tree} (hX : IsObj M ρ X) (hA : IsObj M ρ A)
    (hf : Hom M ρ f (prod X A) B) :
    eval M ρ (comp (ev A B) (pair (comp (curry X A f) (fst X A)) (snd X A))) = eval M ρ f := by
  obtain ⟨x, hx, hxs⟩ := hX
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨wf, hwf, hfs⟩ := hf.exists_eval
  have hc := curry_hom hM ⟨x, hx, hxs⟩ ⟨a, ha, has⟩ hf
  obtain ⟨w, hw, -⟩ := hc.exists_eval
  have hd := hc.eval_dom
  refine (eval_op₂_congr 3 (eval_op₂_congr 23 rfl hf.eval_cod.symm)
    (eval_op₂_congr 9 (eval_op₂_congr 3 rfl (eval_op₂_congr 7 hd.symm rfl))
      (eval_op₂_congr 8 hd.symm rfl))).trans ?_
  exact eval_eq_of_holds (ax_holds hM 81 rfl (by decide) (ts := [X, A, f]) (ws := [x, a, wf])
    (by simp [hx, ha, hwf]) (by simp [hxs, has, hfs]) (hs' := [⟨curry X A f, curry X A f⟩]) rfl
    ⟨w, hw, hw⟩ (q := ⟨comp (ev A (cod f)) (prodMapLeft (curry X A f) A), f⟩) rfl)

/-- An arrow into an exponential is the currying of evaluation after its product with the
identity. -/
theorem curry_eta {k X A B : Tree} (hA : IsObj M ρ A) (hB : IsObj M ρ B)
    (hk : Hom M ρ k X (exp A B)) :
    eval M ρ (curry X A (comp (ev A B) (pair (comp k (fst X A)) (snd X A)))) = eval M ρ k := by
  obtain ⟨x, hx, hxs⟩ := hk.isObj_dom
  obtain ⟨a, ha, has⟩ := hA
  obtain ⟨b, hb, hbs⟩ := hB
  obtain ⟨e, he, -⟩ := hk.isObj_cod
  obtain ⟨wk, hwk, hks⟩ := hk.exists_eval
  have hd := hk.eval_dom
  refine (eval_op₃_congr 24 rfl rfl (eval_op₂_congr 3 rfl
    (eval_op₂_congr 9 (eval_op₂_congr 3 rfl (eval_op₂_congr 7 hd.symm rfl))
      (eval_op₂_congr 8 hd.symm rfl)))).trans ?_
  exact eval_eq_of_holds (ax_holds hM 82 rfl (by decide) (ts := [X, A, B, k])
    (ws := [x, a, b, wk]) (by simp [hx, ha, hb, hwk]) (by simp [hxs, has, hbs, hks])
    (hs' := [⟨dom k, X⟩, ⟨cod k, exp A B⟩]) rfl
    ⟨holds_of_eval_eq hd hx, holds_of_eval_eq hk.eval_cod he⟩
    (q := ⟨curry X A (comp (ev A B) (prodMapLeft k A)), k⟩) rfl)

/-- A currying after an arrow is the currying of the curried arrow after the product of the arrow
with the identity. -/
theorem curry_comp {f h X Y A B : Tree} (hA : IsObj M ρ A) (hf : Hom M ρ f (prod X A) B)
    (hh : Hom M ρ h Y X) : eval M ρ (comp (curry X A f) h) =
      eval M ρ (curry Y A (comp f (pair (comp h (fst Y A)) (snd Y A)))) := by
  have hX := hh.isObj_cod
  have hY := hh.isObj_dom
  have hB := hf.isObj_cod
  have hc := curry_hom hM hX hA hf
  have hk := comp_hom hM hh hc
  have fY := fst_hom hM hY hA
  have sY := snd_hom hM hY hA
  have fX := fst_hom hM hX hA
  have sX := snd_hom hM hX hA
  have hhf := comp_hom hM fY hh
  have hx := pair_hom hM hhf sY
  have cfX := comp_hom hM fX hc
  have pX := pair_hom hM cfX sX
  -- the product of the composite with the identity is the composite of the products
  have e1 : eval M ρ (pair (comp (comp (curry X A f) h) (fst Y A)) (snd Y A)) =
      eval M ρ (comp (pair (comp (curry X A f) (fst X A)) (snd X A))
        (pair (comp h (fst Y A)) (snd Y A))) := by
    refine Eq.symm ((pair_comp hM cfX sX hx).trans (eval_op₂_congr 9 ?_ (snd_pair hM hhf sY)))
    exact ((comp_assoc hM hx fX hc).symm.trans
      (eval_op₂_congr 3 rfl (fst_pair hM hhf sY))).trans (comp_assoc hM fY hh hc)
  -- evaluation after it is the curried arrow after the product of the arrow with the identity
  have e2 : eval M ρ (comp (ev A B) (pair (comp (comp (curry X A f) h) (fst Y A)) (snd Y A))) =
      eval M ρ (comp f (pair (comp h (fst Y A)) (snd Y A))) :=
    ((eval_op₂_congr 3 rfl e1).trans (comp_assoc hM hx pX (ev_hom hM hA hB))).trans
      (eval_op₂_congr 3 (ev_curry hM hX hA hf) rfl)
  exact (curry_eta hM hA hB hk).symm.trans (eval_op₃_congr 24 rfl rfl e2)

/-- An application of a definition's operation, at arguments of the definition's sorts at
whose values the body has a value, has the body's value there. -/
theorem eval_op_defn {i : ℕ} {d : Defn} (hd : defs[i]? = some d) {θ : List Tree}
    {ws : List M.Val} (hθ : θ.map (eval M ρ) = ws.map Part.some) (hs : ws.map Sigma.fst = d.ctx)
    {v : M.Val} (hb : eval M ws d.body = Part.some v) :
    eval M ρ (op (sig.length + i) θ) = Part.some v := by
  obtain ⟨w, h₁, h₂⟩ := hM _ (mem_extendAll_defn defs theory hd _ List.mem_cons_self) ws hs
    fun h hh ↦ (List.mem_singleton.mp hh) ▸ ⟨v, hb, hb⟩
  have hl : d.ctx.length = ws.length := by simpa using (congrArg List.length hs).symm
  have hw : w = v := Part.some_inj.mp (h₂.symm.trans hb)
  change eval M ws (opVars (sig.length + i) d.ctx.length) = Part.some w at h₁
  rw [opVars, eval_op, hl, mapM_vars, Part.bind_some] at h₁
  rw [eval_op, (mapM_part_eq_some_iff θ ws).mpr hθ, Part.bind_some, h₁, hw]

/-- Truth is an arrow from the terminal object to the subobject classifier. -/
theorem tru_hom : Hom M ρ tru one omega := by
  have hd := eval_eq_of_holds (ax_holds (ρ := ρ) hM 84 rfl (by decide) (ts := []) (ws := []) rfl
    rfl rfl trivial (q := ⟨dom tru, one⟩) rfl)
  obtain ⟨o, ho, -⟩ := isObj_one (ρ := ρ) hM
  obtain ⟨w, hw⟩ := exists_eval_of_dom (hd.trans ho)
  exact ⟨w, hw, sort_of_eval_op rfl hw, isObj_one hM, isObj_omega hM, hd,
    eval_eq_of_holds (ax_holds (ρ := ρ) hM 85 rfl (by decide) (ts := []) (ws := []) rfl rfl rfl
      trivial (q := ⟨cod tru, omega⟩) rfl)⟩

/-- The inclusion of the equalizer of two parallel arrows is an arrow into their domain, after
which they agree. -/
theorem eqIncl_hom {f g X Y : Tree} (hf : Hom M ρ f X Y) (hg : Hom M ρ g X Y) :
    Hom M ρ (eqIncl f g) (eqz f g) X ∧
      eval M ρ (comp f (eqIncl f g)) = eval M ρ (comp g (eqIncl f g)) := by
  obtain ⟨wf, hwf, hfs⟩ := hf.exists_eval
  obtain ⟨wg, hwg, hgs⟩ := hg.exists_eval
  obtain ⟨x, hx, -⟩ := hf.isObj_dom
  obtain ⟨y, hy, -⟩ := hf.isObj_cod
  have hts : [f, g].map (eval M ρ) = [wf, wg].map Part.some := by simp [hwf, hwg]
  have hs : [wf, wg].map Sigma.fst = [arr, arr] := by simp [hfs, hgs]
  obtain ⟨e, he, -⟩ := ax_holds hM 30 rfl (by decide) hts hs
    (hs' := [⟨dom f, dom g⟩, ⟨cod f, cod g⟩]) rfl
    ⟨holds_of_eval_eq (hf.eval_dom.trans hg.eval_dom.symm) (hg.eval_dom.trans hx),
      holds_of_eval_eq (hf.eval_cod.trans hg.eval_cod.symm) (hg.eval_cod.trans hy)⟩
    (q := ⟨eqz f g, eqz f g⟩) rfl
  have hz : Eqn.Holds M ρ ⟨eqz f g, eqz f g⟩ := ⟨e, he, he⟩
  obtain ⟨w, hw, -⟩ := ax_holds hM 32 rfl (by decide) hts hs (hs' := [⟨eqz f g, eqz f g⟩]) rfl hz
    (q := ⟨eqIncl f g, eqIncl f g⟩) rfl
  refine ⟨⟨w, hw, sort_of_eval_op rfl hw, ⟨e, he, sort_of_eval_op rfl he⟩, hf.isObj_dom, ?_, ?_⟩,
    eval_eq_of_holds (ax_holds hM 35 rfl (by decide) hts hs (hs' := [⟨eqz f g, eqz f g⟩]) rfl hz
      (q := ⟨comp f (eqIncl f g), comp g (eqIncl f g)⟩) rfl)⟩
  · exact eval_eq_of_holds (ax_holds hM 33 rfl (by decide) hts hs
      (hs' := [⟨eqz f g, eqz f g⟩]) rfl hz (q := ⟨dom (eqIncl f g), eqz f g⟩) rfl)
  · exact (eval_eq_of_holds (ax_holds hM 34 rfl (by decide) hts hs
      (hs' := [⟨eqz f g, eqz f g⟩]) rfl hz (q := ⟨cod (eqIncl f g), dom f⟩) rfl)).trans
      hf.eval_dom

/-- The diagonal is an arrow into the product of the object with itself. -/
theorem diag_hom {A : Tree} (hA : IsObj M ρ A) : Hom M ρ (diag A) A (prod A A) :=
  pair_hom hM (idt_hom hM hA) (idt_hom hM hA)

/-- The diagonal after an arrow is the pairing of the arrow with itself. -/
theorem diag_comp {f X A : Tree} (hf : Hom M ρ f X A) :
    eval M ρ (comp (diag A) f) = eval M ρ (pair f f) := by
  have hi := idt_hom hM hf.isObj_cod
  exact (pair_comp hM hi hi hf).trans (eval_op₂_congr 9 (idt_comp hM hf) (idt_comp hM hf))

/-- The diagonal is a monomorphism: the projections of its kernel pair are equal. -/
theorem holds_monoCond_diag {A : Tree} (hA : IsObj M ρ A) : (monoCond (diag A)).Holds M ρ := by
  change Eqn.Holds M ρ ⟨comp (fst (dom (diag A)) (dom (diag A))) (eqIncl
      (comp (diag A) (fst (dom (diag A)) (dom (diag A))))
      (comp (diag A) (snd (dom (diag A)) (dom (diag A))))),
    comp (snd (dom (diag A)) (dom (diag A))) (eqIncl
      (comp (diag A) (fst (dom (diag A)) (dom (diag A))))
      (comp (diag A) (snd (dom (diag A)) (dom (diag A)))))⟩
  have hm := diag_hom hM hA
  have hd := hm.eval_dom
  set a := dom (diag A) with ha_def
  set k := eqIncl (comp (diag A) (fst a a)) (comp (diag A) (snd a a)) with hk_def
  have hm' : Hom M ρ (diag A) a (prod A A) := hm.congr rfl hd rfl
  have hfst := fst_hom hM (hA.congr hd) (hA.congr hd)
  have hsnd := snd_hom hM (hA.congr hd) (hA.congr hd)
  obtain ⟨hk, hkk⟩ := eqIncl_hom hM (comp_hom hM hfst hm') (comp_hom hM hsnd hm')
  have hfk := comp_hom hM hk hfst
  have hsk := comp_hom hM hk hsnd
  -- the diagonal after a projection after the inclusion is that composite paired with itself
  have hpair : ∀ {p : Tree}, Hom M ρ p (prod a a) a →
      eval M ρ (comp (comp (diag A) p) k) = eval M ρ (pair (comp p k) (comp p k)) := fun hp ↦
    (comp_assoc hM hk hp hm').symm.trans
      (diag_comp hM ((comp_hom hM hk hp).congr rfl rfl hd.symm))
  have hpf := (hpair hfst).symm.trans (hkk.trans (hpair hsnd))
  have he : eval M ρ (comp (fst a a) k) = eval M ρ (comp (snd a a) k) :=
    (fst_pair hM hfk hfk).symm.trans ((eval_op₂_congr 3 rfl hpf).trans (fst_pair hM hsk hsk))
  obtain ⟨w, hw, -⟩ := hsk.exists_eval
  exact holds_of_eval_eq he hw

/-- The characteristic map of the diagonal is an arrow from the product of the object with itself
to the subobject classifier. -/
theorem chi_diag_hom {A : Tree} (hA : IsObj M ρ A) :
    Hom M ρ (chi (diag A)) (prod A A) omega := by
  have hm := diag_hom hM hA
  obtain ⟨wm, hwm, hms⟩ := hm.exists_eval
  have hts : [diag A].map (eval M ρ) = [wm].map Part.some := by simp [hwm]
  have hs : [wm].map Sigma.fst = [arr] := by simp [hms]
  obtain ⟨w, hw, -⟩ := ax_holds hM 87 rfl (by decide) hts hs (hs' := [monoCond (diag A)]) rfl
    (holds_monoCond_diag hM hA) (q := ⟨chi (diag A), chi (diag A)⟩) rfl
  have hc : Eqn.Holds M ρ ⟨chi (diag A), chi (diag A)⟩ := ⟨w, hw, hw⟩
  exact ⟨w, hw, sort_of_eval_op rfl hw, hm.isObj_cod, isObj_omega hM,
    (eval_eq_of_holds (ax_holds hM 88 rfl (by decide) hts hs
      (hs' := [⟨chi (diag A), chi (diag A)⟩]) rfl hc
      (q := ⟨dom (chi (diag A)), cod (diag A)⟩) rfl)).trans hm.eval_cod,
    eval_eq_of_holds (ax_holds hM 89 rfl (by decide) hts hs
      (hs' := [⟨chi (diag A), chi (diag A)⟩]) rfl hc
      (q := ⟨cod (chi (diag A)), omega⟩) rfl)⟩

/-- The characteristic map of the diagonal after the pairing of an arrow with itself is truth:
an equation between an arrow and itself is true. -/
theorem chi_diag_pair_self {f X A : Tree} (hf : Hom M ρ f X A) :
    eval M ρ (comp (chi (diag A)) (pair f f)) = eval M ρ (comp tru (bang X)) := by
  have hA := hf.isObj_cod
  have hm := diag_hom hM hA
  obtain ⟨wm, hwm, hms⟩ := hm.exists_eval
  have hc := chi_diag_hom hM hA
  obtain ⟨w, hw, -⟩ := hc.exists_eval
  have hts : [diag A].map (eval M ρ) = [wm].map Part.some := by simp [hwm]
  have hs : [wm].map Sigma.fst = [arr] := by simp [hms]
  -- the characteristic map after the diagonal is truth after the arrow to the terminal object
  have h90 := eval_eq_of_holds (ax_holds hM 90 rfl (by decide) hts hs
    (hs' := [⟨chi (diag A), chi (diag A)⟩]) rfl ⟨w, hw, hw⟩
    (q := ⟨comp (chi (diag A)) (diag A), comp tru (bang (dom (diag A)))⟩) rfl)
  have hb := bang_hom hM hA
  refine (eval_op₂_congr 3 rfl (diag_comp hM hf).symm).trans ?_
  refine (comp_assoc hM hf hm hc).trans ?_
  refine (eval_op₂_congr 3 (h90.trans (eval_op₂_congr 3 rfl (eval_op₁_congr 5 hm.eval_dom)))
    rfl).trans ?_
  exact (comp_assoc hM hf hb (tru_hom hM)).symm.trans (eval_op₂_congr 3 rfl (comp_bang hM hf))

end Arrows

end Geb.FreeTopos

end

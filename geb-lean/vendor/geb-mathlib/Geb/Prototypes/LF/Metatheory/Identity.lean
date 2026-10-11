/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Metatheory.Substitution
public import Geb.Prototypes.LF.Rewrite

set_option doc.verso true in
/-!
# The identity principles of canonical LF

The η-expansion of a variable is an identity for hereditary substitution, the syntactic content
of the identity principles of canonical LF (\[WatkinsEtAl2002\], Section 4.6; mentioned in
\[HarperLicata2007\], Section 2.3), in two senses: substituting a term for a variable into
the variable's expansion gives the term, and substituting a variable's expansion for another
variable renames that variable. Both hold of η-long terms and of expressions whose variables are
applied only to spines that fill their simple types, the forms the judgments accept
({lit}`judge_appliedAt`); the statements are about the syntax, with simple types in place of
contexts.

Substitution into the expansion of the substituted variable applied to a spine unfolds, by
induction on the simple type of the expansion, to the η-expansion of the reduction of the
substituted term applied to the spine ({lit}`hsub_eta_self`). The three principles
({lit}`ReduceEtaStmt`, {lit}`SubstEtaStmt`, {lit}`EtaReduceStmt`) then hold together by
induction on the simple type ({lit}`identity`): the reduction of a variable's expansion against
a spine that fills its type needs the expansion of the arguments to be identities at the
domains; the substitution of a variable's expansion needs that reduction at its own type; and
the expansion of an η-long term needs the substitution at the domain and the expansion at the
codomain.

## Main definitions

* {lit}`etaReduce` — the η-expansion at a simple type of a reduction.
* {lit}`Expr.AppliedAt` — that every occurrence of a variable is applied to a spine of a kind.
* {lit}`EtaLong`, {lit}`EtaLongSpine` — η-long terms, and spines that fill a simple type.

## Main statements

* {lit}`hsub_eta_ne`, {lit}`hsub_eta_self` — substitution into an η-expansion.
* {lit}`identity` — the identity principles.
* {lit}`hsub_eta_identity` — substituting a variable's expansion for it is the identity.
* {lit}`hsub_into_eta` — substituting an η-long term into a variable's expansion gives the term.

## References

* \[WatkinsEtAl2002\], Section 4.6.
* \[HarperLicata2007\], Section 2.3.

## Tags

logical framework, LF, hereditary substitution, η-expansion, identity substitution
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF

/-- The η-expansion at a base type is the application. -/
theorem eta_base (a : ℕ) (cs : List SimpleTy) (h : Head) (ms : List Expr) :
    eta (RoseTree.node (.base a) cs) h ms = Expr.app h ms := by
  rw [eta, RoseTree.elim_node]
  rfl

/-- The η-expansion at a function type abstracts over the domain's variable and expands at the
codomain the head applied to the spine, weakened, and to the variable's expansion. -/
theorem eta_arrow (α₁ α₂ : SimpleTy) (h : Head) (ms : List Expr) :
    eta (RoseTree.node .arrow [α₁, α₂]) h ms =
      Expr.lam (eta α₂ (h.rename Nat.succ) (ms.map Expr.shift ++ [eta α₁ (.var 0) []])) := by
  rw [eta, RoseTree.elim_node]
  rfl

/-- The η-expansion at a function type of other than two children is the application. -/
theorem eta_arrow_of_ne {cs : List SimpleTy} (hcs : ∀ α₁ α₂, cs ≠ [α₁, α₂]) (h : Head)
    (ms : List Expr) : eta (RoseTree.node .arrow cs) h ms = Expr.app h ms := by
  rw [eta, RoseTree.elim_node]
  rcases cs with _ | ⟨α₁, _ | ⟨α₂, _ | ⟨α₃, cs⟩⟩⟩
  · rfl
  · rfl
  · exact absurd rfl (hcs α₁ α₂)
  · rfl

/-- A list is a pair or is no pair. -/
theorem pair_or_ne {β : Type} (cs : List β) : (∃ a b, cs = [a, b]) ∨ ∀ a b, cs ≠ [a, b] := by
  rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · exact Or.inr fun _ _ h ↦ nomatch h
  · exact Or.inr fun _ _ h ↦ nomatch h
  · exact Or.inl ⟨a, b, rfl⟩
  · exact Or.inr fun _ _ h ↦ nomatch h

/-- Renaming an application renames its head and its spine. -/
theorem rename_app (h : Head) (ms : List Expr) (ρ : ℕ → ℕ) :
    (Expr.app h ms).rename ρ = Expr.app (h.rename ρ) (ms.map fun m ↦ m.rename ρ) := by
  rw [Expr.app, rename_node]
  rcases h with i | c <;>
    exact congrArg _ (List.ext_getElem (by simp) fun k _ _ ↦ by simp)

/-- Renaming a weakened head under a binder is weakening the renamed head. -/
theorem Head.rename_succ_liftR (h : Head) (ρ : ℕ → ℕ) :
    (h.rename Nat.succ).rename (liftR ρ) = (h.rename ρ).rename Nat.succ := by
  rcases h with i | c <;> rfl

/-- Renaming commutes with η-expansion. -/
theorem rename_eta : ∀ (α : SimpleTy) (h : Head) (ms : List Expr) (ρ : ℕ → ℕ),
    (eta α h ms).rename ρ = eta α (h.rename ρ) (ms.map fun m ↦ m.rename ρ) :=
  RoseTree.ind fun l cs ih h ms ρ ↦ by
    rcases l with a | _
    · rw [eta_base, eta_base, rename_app]
    · rcases pair_or_ne cs with hcs | hcs
      · obtain ⟨α₁, α₂, rfl⟩ := hcs
        rw [eta_arrow, eta_arrow, rename_lam, ih α₂ (by simp), Head.rename_succ_liftR,
          List.map_append, List.map_cons, List.map_nil, ih α₁ (by simp), List.map_map,
          List.map_map]
        simp only [Function.comp_def, ← shift_rename, List.map_nil]
        rfl
      · have hcs' : ∀ α₁ α₂, cs ≠ [α₁, α₂] := hcs
        rw [eta_arrow_of_ne hcs', eta_arrow_of_ne hcs', rename_app]

/-- Lists of partial values, every one of which has a value, carried along maps of the values that
preserve them. -/
theorem map_eq_map_some_of {f g : Expr → Option Expr} {φ ψ : Expr → Expr}
    (h : ∀ m m', f m = some m' → g (φ m) = some (ψ m')) {L L' : List Expr}
    (hL : L.map f = L'.map some) : (L.map φ).map g = (L'.map ψ).map some := by
  have hlen : L.length = L'.length := by simpa using congrArg List.length hL
  refine List.ext_getElem (by simp [hlen]) fun k h₁ h₂ ↦ ?_
  have hk := congrArg (·[k]?) hL
  simp only [List.getElem?_map, List.getElem?_eq_getElem (by simpa using h₁ : k < L.length),
    List.getElem?_eq_getElem (by simpa [hlen] using h₁ : k < L'.length), Option.map_some,
    Option.some.injEq] at hk
  simp only [List.getElem_map]
  exact h _ _ hk

/-- Substitution into an application of a variable other than the substituted one renumbers the
variable and substitutes into the spine. -/
theorem hsub_app_var_ne (α : SimpleTy) {n : Expr} {i j : ℕ} {L L' : List Expr} (hij : i ≠ j)
    (hL : L.map (fun m ↦ hsub α n m j) = L'.map some) :
    hsub α n (Expr.app (.var i) L) j = some (Expr.app (.var (renumber j i)) L') := by
  rw [hsub_eq, Expr.app, hsubWith_var]
  have hL' : (L.map fun c ↦ hsubWith (reduce α) c n j).mapM id = some L' :=
    (mapM_id_eq_some_iff _ _).mpr hL
  simp only [hL', Option.bind_some, hij, ↓reduceIte]
  rfl

/-- Substitution into a spine weakened under a binder and extended by an expression that the
weakened substitution leaves in place. -/
theorem map_hsub_shift_append (α : SimpleTy) {n x : Expr} {j : ℕ} {L L' : List Expr}
    (hL : L.map (fun m ↦ hsub α n m j) = L'.map some)
    (hx : hsub α n.shift x (j + 1) = some x) :
    (L.map Expr.shift ++ [x]).map (fun m ↦ hsub α n.shift m (j + 1)) =
      (L'.map Expr.shift ++ [x]).map some := by
  rw [List.map_append, List.map_append, List.map_cons, List.map_cons, List.map_nil, List.map_nil,
    hx]
  exact congrArg (· ++ _) (map_eq_map_some_of (fun m m' hm ↦ hsub_weaken α m n j 1 m' hm) hL)

/-- Substitution into the η-expansion of a variable other than the substituted one applied to a
spine renumbers the variable and substitutes into the spine. -/
theorem hsub_eta_ne (α : SimpleTy) : ∀ (β : SimpleTy) (n : Expr) (i j : ℕ) (L L' : List Expr),
    i ≠ j → L.map (fun m ↦ hsub α n m j) = L'.map some →
      hsub α n (eta β (.var i) L) j = some (eta β (.var (renumber j i)) L') :=
  RoseTree.ind fun l cs ih n i j L L' hij hL ↦ by
    rcases l with a | _
    · rw [eta_base, eta_base]
      exact hsub_app_var_ne α hij hL
    · rcases pair_or_ne cs with hcs | hcs
      · obtain ⟨α₁, α₂, rfl⟩ := hcs
        have h₁ := ih α₁ (by simp) n.shift 0 (j + 1) [] [] (by omega) rfl
        have hren : renumber (j + 1) 0 = 0 := rfl
        rw [hren] at h₁
        have hL₂ := map_hsub_shift_append α hL h₁
        rw [eta_arrow, eta_arrow, hsub_lam,
          show (Head.var i).rename Nat.succ = .var (i + 1) from rfl,
          ih α₂ (by simp) n.shift (i + 1) (j + 1) _ _ (by omega) hL₂]
        have hr : renumber (j + 1) (i + 1) = renumber j i + 1 := by
          unfold renumber
          split_ifs <;> omega
        rw [hr]
        rfl
      · have hcs' : ∀ α₁ α₂, cs ≠ [α₁, α₂] := hcs
        rw [eta_arrow_of_ne hcs', eta_arrow_of_ne hcs']
        exact hsub_app_var_ne α hij hL

/-- One step of the η-expansion at a simple type of the reduction of a term of the simple type
{lit}`α` applied to a spine, at a node of the simple type it expands at: at a function type, the
abstraction of the expansion at the codomain of the term weakened applied to the spine weakened
and to the expansion of the variable at the domain; otherwise the reduction. -/
def etaReduceStep (α : SimpleTy) (l : SimpleLabel)
    (cs : List (SimpleTy × (Expr → List Expr → Option Expr))) (n : Expr) (L : List Expr) :
    Option Expr :=
  match l, cs with
    | .arrow, [(α₁, _), (_, e₂)] =>
      Expr.lam <$> e₂ n.shift (L.map Expr.shift ++ [eta α₁ (.var 0) []])
    | _, _ => reduce α n L

/-- The η-expansion at the simple type {lit}`β` of the reduction of a term of the simple type
{lit}`α` applied to a spine: the substitution of the term for a variable into the variable's
η-expansion at {lit}`β` applied to the spine ({lit}`hsub_eta_self`). -/
def etaReduce (α : SimpleTy) : SimpleTy → Expr → List Expr → Option Expr :=
  RoseTree.para (etaReduceStep α)

/-- The computation rule of {name}`Geb.LF.etaReduce`. -/
theorem etaReduce_node (α : SimpleTy) (l : SimpleLabel) (cs : List SimpleTy) :
    etaReduce α (RoseTree.node l cs) = etaReduceStep α l (cs.map fun c ↦ (c, etaReduce α c)) :=
  RoseTree.para_node _ l cs

/-- Substitution into the η-expansion of the substituted variable applied to a spine is the
η-expansion of the reduction of the substituted term applied to the substituted spine. -/
theorem hsub_eta_self (α : SimpleTy) : ∀ (β : SimpleTy) (n : Expr) (j : ℕ) (L L' : List Expr),
    L.map (fun m ↦ hsub α n m j) = L'.map some →
      hsub α n (eta β (.var j) L) j = etaReduce α β n L' :=
  RoseTree.ind fun l cs ih n j L L' hL ↦ by
    have happ : hsub α n (Expr.app (.var j) L) j = reduce α n L' := by
      rw [hsub_eq, Expr.app, hsubWith_var]
      have hL' : (L.map fun c ↦ hsubWith (reduce α) c n j).mapM id = some L' :=
        (mapM_id_eq_some_iff _ _).mpr hL
      simp only [hL', Option.bind_some, ↓reduceIte]
    rcases l with a | _
    · rw [eta_base, happ, etaReduce_node]
      rfl
    · rcases pair_or_ne cs with hcs | hcs
      · obtain ⟨α₁, α₂, rfl⟩ := hcs
        have h₁ := hsub_eta_ne α α₁ n.shift 0 (j + 1) [] [] (by omega) rfl
        rw [show renumber (j + 1) 0 = 0 from rfl] at h₁
        rw [eta_arrow, hsub_lam, show (Head.var j).rename Nat.succ = .var (j + 1) from rfl,
          ih α₂ (by simp) n.shift (j + 1) _ _ (map_hsub_shift_append α hL h₁), etaReduce_node]
        rfl
      · have hcs' : ∀ α₁ α₂, cs ≠ [α₁, α₂] := hcs
        rw [eta_arrow_of_ne hcs', happ, etaReduce_node]
        rcases cs with _ | ⟨α₁, _ | ⟨α₂, _ | ⟨α₃, cs⟩⟩⟩
        · rfl
        · rfl
        · exact absurd rfl (hcs' α₁ α₂)
        · rfl

/-- The reduction at a function type of an abstraction applied to a spine substitutes the first
argument into the body and reduces the result at the codomain. -/
theorem reduce_lam (α₁ α₂ : SimpleTy) (b m : Expr) (L : List Expr) :
    reduce (RoseTree.node .arrow [α₁, α₂]) (Expr.lam b) (m :: L) =
      (hsub α₁ m b 0).bind fun b' ↦ reduce α₂ b' L := by
  rw [reduce_node]
  rfl

/-- The η-expansion of the reduction of an abstraction applied to a spine is that of the
reduction of the body, the first argument substituted into it, applied to the rest. -/
theorem etaReduce_lam (α₁ α₂ : SimpleTy) :
    ∀ (β : SimpleTy) (b m : Expr) (L : List Expr) (b' : Expr), hsub α₁ m b 0 = some b' →
      etaReduce (RoseTree.node .arrow [α₁, α₂]) β (Expr.lam b) (m :: L) = etaReduce α₂ β b' L :=
  RoseTree.ind fun l cs ih b m L b' hb ↦ by
    have hred : (∀ (γ : SimpleTy) (n : Expr) (L' : List Expr),
        etaReduceStep γ l (cs.map fun c ↦ (c, etaReduce γ c)) n L' = reduce γ n L') →
        etaReduce (RoseTree.node .arrow [α₁, α₂]) (RoseTree.node l cs) (Expr.lam b) (m :: L) =
          etaReduce α₂ (RoseTree.node l cs) b' L := fun hstep ↦ by
      rw [etaReduce_node, etaReduce_node, hstep, hstep, reduce_lam, hb, Option.bind_some]
    rcases l with a | _
    · exact hred fun _ _ _ ↦ rfl
    · rcases pair_or_ne cs with ⟨β₁, β₂, rfl⟩ | hcs
      · rw [etaReduce_node, etaReduce_node]
        simp only [List.map_cons, List.map_nil, etaReduceStep]
        have hb₁ : hsub α₁ m.shift (b.rename (liftR Nat.succ)) 0 = some b'.shift :=
          hsub_rename α₁ b m 0 Nat.succ b' hb
        rw [Expr.shift, rename_lam, List.cons_append,
          ih β₂ (by simp) (b.rename (liftR Nat.succ)) m.shift _ b'.shift hb₁]
      · refine hred fun γ n L' ↦ ?_
        rcases cs with _ | ⟨β₁, _ | ⟨β₂, _ | ⟨β₃, cs⟩⟩⟩
        · rfl
        · rfl
        · exact absurd rfl (hcs β₁ β₂)
        · rfl

/-- One step of whether every occurrence of a variable in an expression is an application to a
spine that satisfies a predicate: the occurrence at the node, if it is an application of the
variable, and those in every child, under the variables the node binds over it. -/
def appliedAtStep (sp : List Expr → Bool) (l : Label) (cs : List (Expr × (ℕ → Bool))) (j : ℕ) :
    Bool :=
  (match l with
    | .app (.var i) => !decide (i = j) || sp (cs.map Prod.fst)
    | _ => true) &&
  (cs.zipIdx.map fun p ↦ p.1.2 (j + l.binders p.2)).all id

/-- Whether every occurrence of the variable of index {lit}`j` in an expression is an
application to a spine that satisfies a predicate. -/
def Expr.AppliedAt (sp : List Expr → Bool) : Expr → ℕ → Bool := RoseTree.para (appliedAtStep sp)

/-- The computation rule of {name}`Geb.LF.Expr.AppliedAt`. -/
theorem appliedAt_node (sp : List Expr → Bool) (l : Label) (cs : List Expr) :
    Expr.AppliedAt sp (RoseTree.node l cs) =
      appliedAtStep sp l (cs.map fun c ↦ (c, Expr.AppliedAt sp c)) :=
  RoseTree.para_node _ l cs

/-- The occurrences of a variable in a node are applications to spines that satisfy a predicate
exactly when the occurrence at the node is, if it is one, and those in every child are. -/
theorem appliedAt_node_iff {sp : List Expr → Bool} {l : Label} {cs : List Expr} {j : ℕ} :
    Expr.AppliedAt sp (RoseTree.node l cs) j = true ↔
      (∀ i, l = .app (.var i) → i = j → sp cs = true) ∧
        ∀ (idx : ℕ) (h : idx < cs.length),
          Expr.AppliedAt sp cs[idx] (j + l.binders idx) = true := by
  have hall : ((cs.map fun c ↦ (c, Expr.AppliedAt sp c)).zipIdx.map
      fun p ↦ p.1.2 (j + l.binders p.2)).all id = true ↔ ∀ (idx : ℕ) (h : idx < cs.length),
        Expr.AppliedAt sp cs[idx] (j + l.binders idx) = true := by
    rw [List.all_eq_true]
    constructor
    · intro h idx hidx
      have := h _ (List.getElem_mem (l := (cs.map fun c ↦ (c, Expr.AppliedAt sp c)).zipIdx.map
        fun p ↦ p.1.2 (j + l.binders p.2)) (n := idx) (by simpa using hidx))
      simpa only [List.getElem_map, List.getElem_zipIdx, zero_add, id] using this
    · intro h x hx
      obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hx
      simp only [List.getElem_map, List.getElem_zipIdx, zero_add, id]
      exact h idx (by simpa using hidx)
  have nonvar : (∀ i, l ≠ .app (.var i)) → (Expr.AppliedAt sp (RoseTree.node l cs) j = true ↔
      (∀ i, l = .app (.var i) → i = j → sp cs = true) ∧
        ∀ (idx : ℕ) (h : idx < cs.length),
          Expr.AppliedAt sp cs[idx] (j + l.binders idx) = true) := by
    intro hl
    rw [appliedAt_node, appliedAtStep, Bool.and_eq_true, hall]
    · exact ⟨fun h ↦ ⟨fun i h' ↦ absurd h' (hl i), h.2⟩, fun h ↦ ⟨rfl, h.2⟩⟩
    · exact fun i h ↦ hl i h
  rcases l with _ | _ | _ | (i | c)
  · exact nonvar fun i h ↦ nomatch h
  · exact nonvar fun i h ↦ nomatch h
  · exact nonvar fun i h ↦ nomatch h
  · rw [appliedAt_node, appliedAtStep, Bool.and_eq_true, hall, List.map_map]
    simp only [Function.comp_def, List.map_id', Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not]
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨fun i' h' hi ↦ ?_, h₂⟩
      cases h'
      exact h₁.resolve_left fun hn ↦ hn hi
    · rintro ⟨h₁, h₂⟩
      refine ⟨?_, h₂⟩
      by_cases hi : i = j
      · exact Or.inr (h₁ i rfl hi)
      · exact Or.inl hi
  · exact nonvar fun i h ↦ nomatch h

/-- One step of whether a term is η-long at a simple type, and whether a spine is one of
η-long arguments that fills it, from those at the children of the simple type's node: at a base
type, every term is, and the empty spine; at a function type, an abstraction whose body is
η-long at the codomain and in which every occurrence of the bound variable is applied to a spine
that fills the domain, and a spine whose first argument is η-long at the domain and whose rest
fills the codomain. -/
def etaLongStep (l : SimpleLabel) (cs : List ((Expr → Bool) × (List Expr → Bool))) :
    (Expr → Bool) × (List Expr → Bool) :=
  match l, cs with
    | .base _, [] => (fun _ ↦ true, List.isEmpty)
    | .arrow, [(l₁, s₁), (l₂, s₂)] =>
      (fun m ↦ match m.label, m.children with
          | .lam, [b] => l₂ b && Expr.AppliedAt s₁ b 0
          | _, _ => false,
        fun ms ↦ match ms with
          | [] => false
          | m :: ms => l₁ m && s₂ ms)
    | _, _ => (fun _ ↦ false, fun _ ↦ false)

/-- Whether a term is η-long at a simple type, and whether a spine is one of η-long arguments that
fills it. -/
def etaLong : SimpleTy → (Expr → Bool) × (List Expr → Bool) := RoseTree.elim etaLongStep

/-- Whether a term is η-long at a simple type. -/
def EtaLong (α : SimpleTy) (m : Expr) : Bool := (etaLong α).1 m

/-- Whether a spine is one of η-long arguments that fills a simple type. -/
def EtaLongSpine (α : SimpleTy) (ms : List Expr) : Bool := (etaLong α).2 ms

/-- The computation rule of {name}`Geb.LF.etaLong`. -/
theorem etaLong_node (l : SimpleLabel) (cs : List SimpleTy) :
    etaLong (RoseTree.node l cs) = etaLongStep l (cs.map etaLong) :=
  RoseTree.elim_node _ l cs

/-- A simple type that is neither a base type of no children nor a function type of two. -/
def SimpleTy.Malformed (l : SimpleLabel) (cs : List SimpleTy) : Prop :=
  (∀ a, ¬(l = .base a ∧ cs = [])) ∧ ∀ α₁ α₂, ¬(l = .arrow ∧ cs = [α₁, α₂])

/-- No term is η-long, and no spine fills, at a malformed simple type. -/
theorem etaLong_malformed {l : SimpleLabel} {cs : List SimpleTy}
    (h : SimpleTy.Malformed l cs) :
    etaLong (RoseTree.node l cs) = (fun _ ↦ false, fun _ ↦ false) := by
  rw [etaLong_node]
  rcases l with a | _
  · rcases cs with _ | ⟨α₁, cs⟩
    · exact absurd ⟨rfl, rfl⟩ (h.1 a)
    · rfl
  · rcases cs with _ | ⟨α₁, _ | ⟨α₂, _ | ⟨α₃, cs⟩⟩⟩
    · rfl
    · rfl
    · exact absurd ⟨rfl, rfl⟩ (h.2 α₁ α₂)
    · rfl

/-- A spine fills a function type exactly when its first argument is η-long at the domain and
the rest fills the codomain. -/
theorem etaLongSpine_arrow (α₁ α₂ : SimpleTy) (m : Expr) (ms : List Expr) :
    EtaLongSpine (RoseTree.node .arrow [α₁, α₂]) (m :: ms) =
      (EtaLong α₁ m && EtaLongSpine α₂ ms) := by
  rw [EtaLongSpine, etaLong_node]
  rfl

/-- The η-long terms at a function type are the abstractions whose bodies are η-long at the
codomain and apply the bound variable only to spines that fill the domain. -/
theorem etaLong_arrow {α₁ α₂ : SimpleTy} {m : Expr}
    (h : EtaLong (RoseTree.node .arrow [α₁, α₂]) m = true) :
    ∃ b, m = Expr.lam b ∧ EtaLong α₂ b = true ∧
      Expr.AppliedAt (EtaLongSpine α₁) b 0 = true := by
  obtain ⟨l, cs, rfl⟩ := exists_node m
  rw [EtaLong, etaLong_node] at h
  simp only [List.map_cons, List.map_nil, etaLongStep, RoseTree.label_node,
    RoseTree.children_node] at h
  rcases l with _ | _ | _ | _
  · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true
  · rcases cs with _ | ⟨b, _ | ⟨d, cs⟩⟩
    · exact absurd h Bool.false_ne_true
    · rw [Bool.and_eq_true] at h
      exact ⟨b, rfl, h.1, h.2⟩
    · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true

/-- The reduction of the η-expansion of a variable applied to a spine, against a spine that fills
the type, is the application of the variable to both. -/
def ReduceEtaStmt (α : SimpleTy) : Prop :=
  ∀ (k : ℕ) (ms₀ ms : List Expr), EtaLongSpine α ms = true →
    reduce α (eta α (.var k) ms₀) ms = some (Expr.app (.var k) (ms₀ ++ ms))

/-- The substitution of the η-expansion of a variable for a variable whose every occurrence is
applied to a spine that fills the type, in an expression in which the substituting variable is
fresh, renames the substituted variable to the substituting one. -/
def SubstEtaStmt (α : SimpleTy) : Prop :=
  ∀ (E : Expr) (j : ℕ), Expr.AppliedAt (EtaLongSpine α) E j = true →
    hsub α (eta α (.var j) []) (E.rename (liftR^[j + 1] Nat.succ)) j = some E

/-- The η-expansion of an η-long term is the term. -/
def EtaReduceStmt (α : SimpleTy) : Prop :=
  ∀ m : Expr, EtaLong α m = true → etaReduce α α m [] = some m

/-- Substitution into the η-expansion of the substituted variable at its own type gives back the
substituted term, where the expansion of an η-long term is the term. -/
theorem hsub_eta_var {α : SimpleTy} (hE : EtaReduceStmt α) {m : Expr} (hm : EtaLong α m = true) :
    hsub α m (eta α (.var 0) []) 0 = some m :=
  (hsub_eta_self α α m 0 [] [] rfl).trans (hE m hm)

/-- Weakening an expression into a context and substituting for the fresh variable gives the
expression back. -/
theorem hsub_shift (α : SimpleTy) (m x : Expr) : hsub α m x.shift 0 = some x :=
  hsubWith_vacuous (reduce α) x m 0

/-- The reduction of an η-expansion at a function type, where the expansions at the domain are
identities and the reductions at the codomain are applications. -/
theorem reduceEta_arrow (α₁ α₂ : SimpleTy) (hE₁ : EtaReduceStmt α₁)
    (hC₂ : ReduceEtaStmt α₂) : ReduceEtaStmt (RoseTree.node .arrow [α₁, α₂]) := by
  intro k ms₀ ms hms
  rcases ms with _ | ⟨m, ms⟩
  · exact absurd hms Bool.false_ne_true
  rw [etaLongSpine_arrow, Bool.and_eq_true] at hms
  have hbody : hsub α₁ m (eta α₂ ((Head.var k).rename Nat.succ)
      (ms₀.map Expr.shift ++ [eta α₁ (.var 0) []])) 0 = some (eta α₂ (.var k) (ms₀ ++ [m])) := by
    have hren : renumber 0 (k + 1) = k := by
      unfold renumber
      split_ifs <;> omega
    rw [show (Head.var k).rename Nat.succ = .var (k + 1) from rfl,
      hsub_eta_ne α₁ α₂ m (k + 1) 0 _ (ms₀ ++ [m]) (by omega), hren]
    rw [List.map_append, List.map_append, List.map_map, List.map_cons, List.map_cons,
      List.map_nil, List.map_nil, hsub_eta_var hE₁ hms.1]
    exact congrArg (· ++ _) (List.map_congr_left fun x _ ↦ hsub_shift α₁ m x)
  rw [eta_arrow, reduce_lam, hbody, Option.bind_some, hC₂ k (ms₀ ++ [m]) ms hms.2,
    List.append_assoc, List.singleton_append]

/-- Weakening the η-expansion of a variable past {lit}`b` variables is the expansion of the
variable past them. -/
theorem iterate_shift_eta (α : SimpleTy) (j b : ℕ) :
    Expr.shift^[b] (eta α (.var j) []) = eta α (.var (j + b)) [] := by
  rw [iterate_shift, rename_eta]
  rfl

/-- Substituting the η-expansion of a variable for one applied only to spines that fill the type
renames it, where the reductions of the expansion are applications. -/
theorem substEta_of_reduceEta {α : SimpleTy} (hC : ReduceEtaStmt α) : SubstEtaStmt α :=
  RoseTree.ind fun l cs ih j h ↦ by
    obtain ⟨hhere, hch⟩ := appliedAt_node_iff.mp h
    have hchild : ∀ (b idx : ℕ) (hidx : idx < cs.length), l.binders idx = b →
        hsubWith (reduce α) (Expr.rename cs[idx] (liftR^[b] (liftR^[j + 1] Nat.succ)))
          (Expr.shift^[b] (eta α (.var j) [])) (j + b) = some cs[idx] := by
      intro b idx hidx hb
      have := ih _ (List.getElem_mem hidx) (j + b) (hb ▸ hch idx hidx)
      rwa [iterate_shift_eta, show liftR^[b] (liftR^[j + 1] Nat.succ) = liftR^[j + b + 1] Nat.succ
        by rw [← Function.iterate_add_apply, show b + (j + 1) = j + b + 1 by omega]]
    have nonvar : (∀ i, l ≠ .app (.var i)) →
        hsub α (eta α (.var j) []) (Expr.rename (RoseTree.node l cs) (liftR^[j + 1] Nat.succ)) j =
          some (RoseTree.node l cs) := by
      intro hl
      rw [rename_node, Label.rename_of_ne hl, hsub_eq, hsubWith_node_of_ne _ l hl]
      refine congrArg (Option.map _) (mapM_id_eq_some_of_getElem (by simp) fun k h₁ h₂ ↦ ?_)
      simp only [List.getElem_map, List.getElem_zipIdx, zero_add]
      exact hchild _ k h₂ rfl
    rcases l with _ | _ | _ | (i | c)
    · exact nonvar fun i h ↦ nomatch h
    · exact nonvar fun i h ↦ nomatch h
    · exact nonvar fun i h ↦ nomatch h
    · rw [rename_node]
      simp only [Label.rename, Head.rename, Label.binders_app, Function.iterate_zero_apply]
      rw [hsub_eq, hsubWith_var]
      have hcs : ((cs.zipIdx.map fun p ↦ Expr.rename p.1 (liftR^[j + 1] Nat.succ)).map
          fun c ↦ hsubWith (reduce α) c (eta α (.var j) []) j).mapM id = some cs :=
        mapM_id_eq_some_of_getElem (by simp) fun k h₁ h₂ ↦ by
          simp only [List.getElem_map, List.getElem_zipIdx, zero_add]
          simpa using hchild 0 k h₂ (Label.binders_app _ _)
      rw [hcs, Option.bind_some]
      have hτ : liftR^[j + 1] Nat.succ i = if i < j + 1 then i else i + 1 := by
        rw [iterate_liftR_apply]
        split_ifs with h
        · rfl
        · simp only [Nat.succ_eq_add_one]
          omega
      by_cases hij : i = j
      · subst hij
        have hτj : liftR^[i + 1] Nat.succ i = i := by
          rw [hτ]
          simp
        simp only [hτj, ↓reduceIte]
        rw [hC i [] cs (hhere i rfl rfl), List.nil_append]
        rfl
      · have hne : liftR^[j + 1] Nat.succ i ≠ j := by
          rw [hτ]
          split_ifs <;> omega
        simp only [hne, ↓reduceIte]
        congr 2
        rw [hτ]
        split_ifs <;> omega
    · exact nonvar fun i h ↦ nomatch h

/-- The η-expansion of an η-long term at a function type is the term, where substituting the
expansion of a variable at the domain renames it and the expansions at the codomain are
identities. -/
theorem etaReduce_arrow (α₁ α₂ : SimpleTy) (hB₁ : SubstEtaStmt α₁) (hE₂ : EtaReduceStmt α₂) :
    EtaReduceStmt (RoseTree.node .arrow [α₁, α₂]) := by
  intro m hm
  obtain ⟨b, rfl, hb, hocc⟩ := etaLong_arrow hm
  have hsb : hsub α₁ (eta α₁ (.var 0) []) (b.rename (liftR Nat.succ)) 0 = some b :=
    hB₁ b 0 hocc
  rw [etaReduce_node]
  simp only [List.map_cons, List.map_nil, etaReduceStep, List.nil_append]
  rw [Expr.shift, rename_lam, etaReduce_lam α₁ α₂ α₂ _ _ [] b hsb, hE₂ b hb]
  rfl

/-- The reduction of the η-expansion of a variable at a base type, against the empty spine, is
the application. -/
theorem reduceEta_base (a : ℕ) : ReduceEtaStmt (RoseTree.node (.base a) []) := by
  intro k ms₀ ms hms
  rcases ms with _ | ⟨m, ms⟩
  · rw [eta_base, reduce_node, List.append_nil]
    rfl
  · exact absurd hms Bool.false_ne_true

/-- The η-expansion of a term at a base type is the term. -/
theorem etaReduce_base (a : ℕ) : EtaReduceStmt (RoseTree.node (.base a) []) := by
  intro m _
  rw [etaReduce_node]
  change reduce _ m [] = some m
  rw [reduce_node]
  rfl

/-- The identity principles of hereditary substitution, in simple types (\[WatkinsEtAl2002\],
Section 4.6):
the reduction of the η-expansion of a variable against a spine that fills its type is the
variable's application, substituting the expansion of a variable for one applied only to such
spines renames it, and the η-expansion of an η-long term is the term. -/
theorem identity : ∀ α : SimpleTy, ReduceEtaStmt α ∧ SubstEtaStmt α ∧ EtaReduceStmt α :=
  RoseTree.ind fun l cs ih ↦ by
    have hmal : SimpleTy.Malformed l cs → ReduceEtaStmt (RoseTree.node l cs) ∧
        SubstEtaStmt (RoseTree.node l cs) ∧ EtaReduceStmt (RoseTree.node l cs) := fun hm ↦ by
      have hC : ReduceEtaStmt (RoseTree.node l cs) := fun k ms₀ ms hms ↦ by
        rw [EtaLongSpine, etaLong_malformed hm] at hms
        exact absurd hms Bool.false_ne_true
      refine ⟨hC, substEta_of_reduceEta hC, fun m hm' ↦ ?_⟩
      rw [EtaLong, etaLong_malformed hm] at hm'
      exact absurd hm' Bool.false_ne_true
    rcases l with a | _
    · rcases cs with _ | ⟨d, cs⟩
      · exact ⟨reduceEta_base a, substEta_of_reduceEta (reduceEta_base a), etaReduce_base a⟩
      · exact hmal ⟨(fun _ h ↦ nomatch h.2), fun _ _ h ↦ nomatch h.1⟩
    · rcases pair_or_ne cs with ⟨α₁, α₂, rfl⟩ | hcs
      · have h₁ := ih α₁ (by simp)
        have h₂ := ih α₂ (by simp)
        have hC := reduceEta_arrow α₁ α₂ h₁.2.2 h₂.1
        exact ⟨hC, substEta_of_reduceEta hC, etaReduce_arrow α₁ α₂ h₁.2.1 h₂.2.2⟩
      · exact hmal ⟨(fun _ h ↦ nomatch h.1), fun α₁ α₂ h ↦ hcs α₁ α₂ h.2⟩

/-- Substituting the η-expansion of a variable for the variable it renames is the identity: in
an expression in which every occurrence of the variable of index {lit}`0` is applied to a spine
that fills its simple type, weakened past a fresh variable above it, substituting the fresh
variable's expansion for it gives the expression back. -/
theorem hsub_eta_identity {α : SimpleTy} {E : Expr}
    (h : Expr.AppliedAt (EtaLongSpine α) E 0 = true) :
    hsub α (eta α (.var 0) []) (E.rename (liftR Nat.succ)) 0 = some E :=
  (identity α).2.1 E 0 h

/-- Substituting an η-long term for a variable into the variable's η-expansion gives the term. -/
theorem hsub_into_eta {α : SimpleTy} {m : Expr} (h : EtaLong α m = true) :
    hsub α m (eta α (.var 0) []) 0 = some m :=
  hsub_eta_var (identity α).2.2 h

end Geb.LF

end

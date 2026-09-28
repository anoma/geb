/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Theory
public import Geb.Prototypes.PartialHorn.Shared
public import Geb.Prototypes.PartialHorn.Definitional

set_option doc.verso true in
/-!
# Inferring the typing of terms of the theory of an elementary topos

The typing of a term of the theory {name}`Geb.FreeTopos.theory`, extended by definitions, in a
context under hypotheses: whether it is defined, and for an object its canonical form, for an
arrow the canonical forms of its domain and codomain ({lit}`Ann`). A canonical object is an
object whose domains and codomains of compound arrows are replaced by the objects the axioms
compute for them. The typing is inferred as the prover's typing computes it, by rules read off
the axioms: an application is defined by the axiom concluding its definedness from hypotheses
that the inference proves in turn, which are definedness and equations between objects of one
canonical form; or by strictness at an axiom without hypotheses; or, for a constant, by an axiom
without hypotheses whose right side it is; and its domain and codomain are the right sides of
the axioms whose left sides they are. An application of a definition has the typing of its
body's instance. The tables naming the axioms of each operation are not trusted: the inference
checks each axiom's shape where it uses it.

Every typing the inference computes holds in every model of the theory at every assignment of
the context at which the hypotheses hold ({lit}`infers_sound`), so a checker may accept the
definedness of an inferred term, and the equation of two objects of one canonical form,
without a certificate. The models are those of any signature extending the theory's in which
its axioms hold ({lit}`ExtEnv.Sound`), so that a typing inferred in a theory holds in every
model of its extensions.

## Main definitions

* {lit}`DfdRule`, {lit}`dfdRules`, {lit}`domRules`, {lit}`codRules` — how the axioms type each
  operation.
* {lit}`Ann`, {lit}`Ann.Holds` — a typing, and its truth in a model.
* {lit}`ExtEnv.Sound` — a model in which an environment's axioms hold.
* {lit}`inferOp`, {lit}`inferVar`, {lit}`infers` — the inference of an application's, a
  variable's, and a term's or pattern instance's typing.

## Main statements

* {lit}`infers_sound` — every typing the inference computes holds.

## Tags

elementary topos, type inference, partial Horn logic, soundness
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn Sorts
open scoped FinEnum

universe v

/-- How an axiom proves that an application of an operation is defined. -/
inductive DfdRule where
  /-- The axiom concludes the application's definedness. -/
  | direct (j : ℕ)
  /-- The axiom, without hypotheses, concludes an equation whose left side applies an
  operation to the application alone. -/
  | strict (j : ℕ)
  /-- The axiom, closed and without hypotheses, concludes an equation whose right side is the
  constant. -/
  | rhs (j : ℕ)

/-- The argument sorts of an operation. -/
def argSorts (k : ℕ) : List ℕ := (sig[k]?.map Prod.fst).getD []

/-- The axioms with their indices. -/
def indexedAxioms : List (Seq × ℕ) := axioms.zipIdx

/-- The rule by which the axioms prove an application of operation {lit}`k` defined. -/
def dfdRule (k : ℕ) : Option DfdRule :=
  let t := opVars k (argSorts k).length
  let direct := indexedAxioms.find? fun (a, _) ↦
    a.ctx == argSorts k && a.concl.lhs == t && a.concl.rhs == t
  let strict := indexedAxioms.find? fun (a, _) ↦
    a.ctx == argSorts k && a.hyps.isEmpty && a.concl.lhs.label != 0 &&
      a.concl.lhs.children == [t]
  let rhs := indexedAxioms.find? fun (a, _) ↦
    a.ctx.isEmpty && a.hyps.isEmpty && a.concl.rhs == t
  match direct, strict, rhs with
  | some (_, j), _, _ => some (.direct j)
  | none, some (_, j), _ => some (.strict j)
  | none, none, some (_, j) => some (.rhs j)
  | none, none, none => none

/-- The axiom whose left side is the application of operation {lit}`o` (the domain or the
codomain) to an application of operation {lit}`k`, under hypotheses of definedness alone. -/
def boundRule (o k : ℕ) : Option ℕ :=
  let t := opVars k (argSorts k).length
  (indexedAxioms.find? fun (a, _) ↦
    a.ctx == argSorts k && a.concl.lhs == op o [t] && a.hyps.all fun h ↦ h.lhs == h.rhs).map
    Prod.snd

/-- The definedness rules, by operation. -/
def dfdRules : List (Option DfdRule) := (List.range sig.length).map dfdRule

/-- The domain rules, by operation. -/
def domRules : List (Option ℕ) := (List.range sig.length).map (boundRule 0)

/-- The codomain rules, by operation. -/
def codRules : List (Option ℕ) := (List.range sig.length).map (boundRule 1)

/-- The index of the first axiom of the definition at position {lit}`i`, among the axioms of
the theory's extension by definitions: it equates the definition's application with its body
where the body is defined. -/
def defAxIdx (i : ℕ) : ℕ := axioms.length + 2 * i

/-- A term's typing: its sort, and for an object its canonical form, for an arrow the canonical
forms of its domain and codomain. For an object both are its canonical form. -/
structure Ann where
  /-- The sort. -/
  sort : ℕ
  /-- For an object, its canonical form; for an arrow, its domain's. -/
  lo : Tree
  /-- For an object, its canonical form; for an arrow, its codomain's. -/
  hi : Tree

/-- The theory extended by definitions. -/
abbrev ext (defs : List Defn) : Theory := theory.extendAll defs

/-- A typing holds of a term at an assignment: the term is defined with a value of the sort;
an object's canonical form has its value; an arrow's domain and codomain have the values of
their canonical forms. -/
def Ann.Holds {S : Sig} (M : Model S) (ρ : List M.Val) (t : Tree) (a : Ann) : Prop :=
  ∃ w, eval M ρ t = Part.some w ∧ w.1 = a.sort ∧
    (a.sort = obj → eval M ρ a.lo = Part.some w) ∧
    (a.sort = arr → (∃ d, eval M ρ (dom t) = Part.some d ∧ eval M ρ a.lo = Part.some d) ∧
      ∃ c, eval M ρ (cod t) = Part.some c ∧ eval M ρ a.hi = Part.some c)

/-- The theory extended by definitions, with its axioms, its signature and the rule tables as
arrays, for lookup by index. -/
structure ExtEnv where
  /-- The definitions. -/
  defs : List Defn
  /-- The extended theory's axioms. -/
  axs : Array Seq
  /-- The extended theory's signature. -/
  sg : Array (List ℕ × ℕ)
  /-- The definedness rules. -/
  dfds : Array (Option DfdRule)
  /-- The domain rules. -/
  doms : Array (Option ℕ)
  /-- The codomain rules. -/
  cods : Array (Option ℕ)

/-- The environment of the theory extended by definitions. -/
def ExtEnv.ofDefs (defs : List Defn) : ExtEnv :=
  ⟨defs, (ext defs).axioms.toArray, (ext defs).sig.toArray, dfdRules.toArray, domRules.toArray,
    codRules.toArray⟩

/-- An environment's arrays are its extended theory's axioms and signature. -/
structure ExtEnv.WF (E : ExtEnv) : Prop where
  /-- Every axiom of the array is an axiom of the extended theory. -/
  axs : ∀ (j : ℕ) (a : Seq), E.axs[j]? = some a → a ∈ (ext E.defs).axioms
  /-- The array's signature is the extended theory's. -/
  sg : ∀ k : ℕ, E.sg[k]? = (ext E.defs).sig[k]?

/-- The environment of a theory extended by definitions is well formed. -/
theorem ExtEnv.wf_ofDefs (defs : List Defn) : (ExtEnv.ofDefs defs).WF :=
  ⟨fun j a h ↦ List.mem_of_getElem? (by simpa [ExtEnv.ofDefs] using h),
    fun k ↦ by simp [ExtEnv.ofDefs]⟩

/-- A model in which an environment's axioms are valid, over a signature extending the
environment's: each operation of the environment's signature is the model's, with its arities
and sort. -/
structure ExtEnv.Sound (E : ExtEnv) {S : Sig} (M : Model.{v} S) : Prop where
  /-- Every axiom of the array is valid. -/
  axs : ∀ (j : ℕ) (a : Seq), E.axs[j]? = some a → a.Valid M
  /-- Every operation of the array's signature is one of the model's signature. -/
  sg : ∀ (k : ℕ) (o : List ℕ × ℕ), E.sg[k]? = some o → S[k]? = some o

/-- A model of a well-formed environment's theory is a model in which its axioms are valid. -/
theorem ExtEnv.WF.sound_self {E : ExtEnv} (hE : E.WF) {M : Model.{v} (ext E.defs).sig}
    (hM : IsModel (ext E.defs) M) : E.Sound M :=
  ⟨fun j a ha ↦ hM a (hE.axs j a ha), fun k _ ho ↦ (hE.sg k).symm.trans ho⟩

section Inference

variable (E : ExtEnv)

/-- Whether a hypothesis of an axiom holds at arguments of the given typings, by the typings of
its sides' instances, which {lit}`patInf` infers: a definedness when the side is typed, an
equation between objects when their canonical forms agree. -/
def hypOk (patInf : List (Tree × Ann) → Tree → Option (Tree × Ann)) (args : List (Tree × Ann))
    (h : Eqn) : Bool :=
  if h.lhs == h.rhs then (patInf args h.lhs).isSome
  else match patInf args h.lhs, patInf args h.rhs with
    | some (_, l), some (_, r) => l.sort == obj && r.sort == obj && l.lo == r.lo
    | _, _ => false

/-- The canonical bound of an application of operation {lit}`k`, by the axiom {lit}`j` whose left
side is the application of operation {lit}`o` to it, under hypotheses of definedness: the
canonical form of the axiom's right side at the arguments. -/
def bound (patInf : List (Tree × Ann) → Tree → Option (Tree × Ann)) (args : List (Tree × Ann))
    (o k j : ℕ) : Option Tree :=
  match E.axs[j]? with
  | some a =>
    if a.Scoped && a.ctx == args.map (·.2.sort) && a.concl.lhs == op o [opVars k args.length] &&
        a.hyps.all (fun h ↦ h.lhs == h.rhs &&
          (h.lhs == opVars k args.length || (patInf args h.lhs).isSome)) then
      match patInf args a.concl.rhs with
      | some (_, r) => if r.sort == obj then some r.lo else none
      | none => none
    else none
  | none => none

/-- Whether an axiom of the theory proves an application of operation {lit}`k` defined at
arguments of the given typings, by the rule the table names for it. -/
def dfdOk (patInf : List (Tree × Ann) → Tree → Option (Tree × Ann)) (args : List (Tree × Ann))
    (k : ℕ) : Bool :=
  let as := args.map (·.2.sort)
  let t := opVars k args.length
  match E.dfds[k]? with
  | some (some (.direct j)) => match E.axs[j]? with
    | some a => a.Scoped && a.ctx == as && a.concl.lhs == t && a.concl.rhs == t &&
        a.hyps.all (hypOk patInf args)
    | none => false
  | some (some (.strict j)) => match E.axs[j]? with
    | some a => a.ctx == as && a.hyps.isEmpty && a.concl.lhs.label != 0 &&
        a.concl.lhs.children == [t]
    | none => false
  | some (some (.rhs j)) => match E.axs[j]? with
    | some a => a.ctx.isEmpty && a.hyps.isEmpty && args.isEmpty && a.concl.rhs == t
    | none => false
  | _ => false

/-- The typing of an object-valued application of an operation of the signature: the domain
or codomain of an arrow has its canonical bound, and any other application is canonical with
its object arguments replaced by their canonical forms. -/
def inferObj (k : ℕ) (args : List (Tree × Ann)) : Option Ann :=
  match k, args with
  | 0, [(_, f)] => if f.sort == arr then some ⟨obj, f.lo, f.lo⟩ else none
  | 1, [(_, f)] => if f.sort == arr then some ⟨obj, f.hi, f.hi⟩ else none
  | k, args =>
    let c := op k (args.map fun p ↦ if p.2.sort == obj then p.2.lo else p.1)
    some ⟨obj, c, c⟩

/-- The typing of an arrow-valued application of an operation of the signature: the canonical
bounds its domain and codomain rules compute. -/
def inferArr (patInf : List (Tree × Ann) → Tree → Option (Tree × Ann)) (k : ℕ)
    (args : List (Tree × Ann)) : Option Ann :=
  match (E.doms[k]?).join.bind (bound E patInf args 0 k),
    (E.cods[k]?).join.bind (bound E patInf args 1 k) with
  | some lo, some hi => some ⟨arr, lo, hi⟩
  | _, _ => none

/-- The typing of an application of the definition of operation {lit}`k`: its body's instance's,
by the definition's first axiom. -/
def inferDef (patInf : List (Tree × Ann) → Tree → Option (Tree × Ann)) (k : ℕ)
    (args : List (Tree × Ann)) : Option Ann :=
  match E.defs[k - sig.length]?, E.axs[defAxIdx (k - sig.length)]? with
  | some d, some a =>
    if a.Scoped && a.ctx == args.map (·.2.sort) && a.hyps == [⟨d.body, d.body⟩] &&
        a.concl == ⟨opVars k args.length, d.body⟩ then
      (patInf args d.body).map Prod.snd
    else none
  | _, _ => none

/-- The typing of an application of operation {lit}`k` to terms of the given typings, the
instances of axioms' sides typed by {lit}`patInf`. -/
def inferOp (patInf : List (Tree × Ann) → Tree → Option (Tree × Ann)) (k : ℕ)
    (args : List (Tree × Ann)) : Option Ann :=
  match E.sg[k]? with
  | some (as, s) =>
    if args.map (·.2.sort) == as then
      if k < sig.length then
        if dfdOk E patInf args k then
          if s == obj then inferObj k args
          else if s == arr then inferArr E patInf k args
          else none
        else none
      else inferDef E patInf k args
    else none
  | none => none

/-- The typing of a variable of a context under hypotheses: an object is its own canonical form;
an arrow's domain and codomain are canonical unless a hypothesis equates them with an object,
whose canonical form, which {lit}`treeInf` infers, is theirs. -/
def inferVar (Γ : List ℕ) (H : List Eqn) (treeInf : Tree → Option Ann) (v : ℕ) : Option Ann :=
  match Γ[v]? with
  | some 0 => some ⟨obj, var v, var v⟩
  | some 1 =>
    let side (o : ℕ) : Option Tree :=
      if (match E.axs[o]? with
          | some a => a.ctx == [arr] && a.hyps.isEmpty && a.concl == dfd (op o [x 0])
          | none => false) then
        match H.find? (·.lhs == op o [var v]) with
        | some q => (treeInf q.rhs).bind fun a ↦ if a.sort == obj then some a.lo else none
        | none => some (op o [var v])
      else none
    (side 0).bind fun lo ↦ (side 1).map fun hi ↦ ⟨arr, lo, hi⟩
  | _ => none

/-- One step of inferring a pattern instance's typing: a variable's from the arguments, an
application's by {lit}`inferOp`. -/
def patStep (patInf : List (Tree × Ann) → Tree → Option (Tree × Ann)) (env : List (Tree × Ann))
    (l : ℕ) (cs : List (Tree × Option (Tree × Ann))) : Option (Tree × Ann) :=
  match l, cs with
  | 0, [(v, _)] => if v.children.isEmpty then env[v.label]? else none
  | k + 1, cs => do
    let args ← cs.mapM Prod.snd
    let a ← inferOp E patInf k args
    pure (op k (args.map Prod.fst), a)
  | _, _ => none

/-- One step of inferring a term's typing: a variable's by {lit}`inferVar`, an application's
by {lit}`inferOp`. -/
def treeStep (Γ : List ℕ) (H : List Eqn) (patInf : List (Tree × Ann) → Tree → Option (Tree × Ann))
    (treeInf : Tree → Option Ann) (l : ℕ) (cs : List (Tree × Option Ann)) : Option Ann :=
  match l, cs with
  | 0, [(v, _)] => if v.children.isEmpty then inferVar E Γ H treeInf v.label else none
  | k + 1, cs => do
    let as ← cs.mapM Prod.snd
    inferOp E patInf k ((cs.map Prod.fst).zip as)
  | _, _ => none

/-- The inferences at a fuel, in a context under hypotheses: of the instance of a pattern at
arguments of the given typings, with the instance; and of a term. Each types the instances of
axioms' sides it meets at the fuel below. -/
def infers (Γ : List ℕ) (H : List Eqn) :
    ℕ → (List (Tree × Ann) → Tree → Option (Tree × Ann)) × (Tree → Option Ann) :=
  Nat.rec (fun _ _ ↦ none, fun _ ↦ none) fun _ rec ↦
    (fun env ↦ RoseTree.para (patStep E rec.1 env),
      RoseTree.para (treeStep E Γ H rec.1 rec.2))

end Inference

section Soundness

variable {E : ExtEnv} {S : Sig} {M : Model.{v} S} {ρ : List M.Val}

/-- Pattern inference is sound at an assignment: an instance it types is the pattern's
substitution instance at the arguments, and its typing holds, when the arguments' typings
hold. -/
def PatSound (M : Model.{v} S) (ρ : List M.Val)
    (patInf : List (Tree × Ann) → Tree → Option (Tree × Ann)) : Prop :=
  ∀ env p r, patInf env p = some r → (∀ e ∈ env, e.2.Holds M ρ e.1) →
    r.1 = subst (env.map Prod.fst) p ∧ r.2.Holds M ρ r.1

/-- Terms whose typings hold have values of their sorts. -/
theorem exists_values (args : List (Tree × Ann)) :
    (∀ e ∈ args, e.2.Holds M ρ e.1) → ∃ ws : List M.Val,
      (args.map Prod.fst).map (eval M ρ) = ws.map Part.some ∧
        ws.map Sigma.fst = args.map (·.2.sort) :=
  args.rec (motive := fun args ↦ (∀ e ∈ args, e.2.Holds M ρ e.1) → ∃ ws : List M.Val,
      (args.map Prod.fst).map (eval M ρ) = ws.map Part.some ∧
        ws.map Sigma.fst = args.map (·.2.sort))
    (fun _ ↦ ⟨[], rfl, rfl⟩)
    (fun e args ih h ↦ by
      obtain ⟨w, hw, hs, -⟩ := h e List.mem_cons_self
      obtain ⟨ws, hws, hss⟩ := ih fun e' he' ↦ h e' (List.mem_cons_of_mem _ he')
      exact ⟨w :: ws, by simp [hw, hws], by simp [hs, hss]⟩)

/-- An application's value is the operation at its arguments' values. -/
theorem eval_op_of_values {ts : List Tree} {ws : List M.Val}
    (h : ts.map (eval M ρ) = ws.map Part.some) (k : ℕ) : eval M ρ (op k ts) = M.op k ws := by
  rw [eval_op, (mapM_part_eq_some_iff ts ws).mpr h, Part.bind_some]

/-- The application of an operation to the variables, at an assignment, is the operation at
the assignment. -/
theorem eval_opVars (k : ℕ) (ws : List M.Val) : eval M ws (opVars k ws.length) = M.op k ws := by
  rw [opVars, eval_op, mapM_vars, Part.bind_some]

/-- A typing holds of a term with the value of one it holds of. -/
theorem Ann.holds_of_eval_eq {a : Ann} {t t' : Tree} (he : eval M ρ t = eval M ρ t')
    (h : a.Holds M ρ t') : a.Holds M ρ t := by
  have hb : ∀ o, eval M ρ (op o [t]) = eval M ρ (op o [t']) := fun o ↦ by
    rw [eval_op, eval_op, mapM_congr_map (l₁ := [t]) (l₂ := [t']) (by simp [he])]
  obtain ⟨w, hw, hs, ho, ha⟩ := h
  refine ⟨w, he.trans hw, hs, ho, fun h' ↦ ?_⟩
  obtain ⟨⟨d, hd, hd'⟩, ⟨c, hc, hc'⟩⟩ := ha h'
  exact ⟨⟨d, (hb 0).trans hd, hd'⟩, ⟨c, (hb 1).trans hc, hc'⟩⟩

/-- A hypothesis the inference proves at arguments holds at their values, when its sides are
in the arguments' scope. -/
theorem holds_of_hypOk {patInf : List (Tree × Ann) → Tree → Option (Tree × Ann)}
    (hpat : PatSound M ρ patInf) {args : List (Tree × Ann)} (hargs : ∀ e ∈ args, e.2.Holds M ρ e.1)
    {ws : List M.Val} (hws : (args.map Prod.fst).map (eval M ρ) = ws.map Part.some) {h : Eqn}
    (hl : Scoped (args.map Prod.fst).length h.lhs = true)
    (hr : Scoped (args.map Prod.fst).length h.rhs = true)
    (hok : hypOk patInf args h = true) : h.Holds M ws := by
  unfold hypOk at hok
  split at hok
  · rename_i he
    rw [beq_iff_eq] at he
    obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.mp hok
    obtain ⟨hrt, w, hw, -⟩ := hpat args h.lhs r hr' hargs
    rw [hrt, eval_subst hws _ hl] at hw
    exact ⟨w, hw, he ▸ hw⟩
  · split at hok
    · rename_i u l u' r hlhs hrhs
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨hls, hrs⟩, hlo⟩ := hok
      obtain ⟨hu, w, hw, -, hwl, -⟩ := hpat args h.lhs _ hlhs hargs
      obtain ⟨hu', w', hw', -, hwl', -⟩ := hpat args h.rhs _ hrhs hargs
      simp only at hu hu' hw hw' hwl hwl'
      rw [hu, eval_subst hws _ hl] at hw
      rw [hu', eval_subst hws _ hr] at hw'
      have he : w = w' := Part.some_inj.mp ((hwl hls).symm.trans (hlo ▸ hwl' hrs))
      exact ⟨w, hw, he ▸ hw'⟩
    · simp at hok

/-- A scoped sequent's hypotheses are scoped in its context. -/
theorem scoped_hyps {a : Seq} (h : a.Scoped = true) :
    ∀ q ∈ a.hyps, Scoped a.ctx.length q.lhs = true ∧ Scoped a.ctx.length q.rhs = true := by
  simp only [Seq.Scoped, Bool.and_eq_true, List.all_eq_true, Eqn.Scoped] at h
  exact h.1

/-- A scoped sequent's conclusion is scoped in its context. -/
theorem scoped_concl {a : Seq} (h : a.Scoped = true) :
    Scoped a.ctx.length a.concl.lhs = true ∧ Scoped a.ctx.length a.concl.rhs = true := by
  simp only [Seq.Scoped, Bool.and_eq_true, List.all_eq_true, Eqn.Scoped] at h
  exact h.2

/-- An application the definedness rule proves defined has a value at the arguments'
values. -/
theorem exists_op_of_dfdOk (hM : E.Sound M)
    {patInf : List (Tree × Ann) → Tree → Option (Tree × Ann)} (hpat : PatSound M ρ patInf)
    {args : List (Tree × Ann)} (hargs : ∀ e ∈ args, e.2.Holds M ρ e.1) {ws : List M.Val}
    (hws : (args.map Prod.fst).map (eval M ρ) = ws.map Part.some)
    (hsorts : ws.map Sigma.fst = args.map (·.2.sort)) {k : ℕ}
    (hok : dfdOk E patInf args k = true) : ∃ w, M.op k ws = Part.some w := by
  have hlen : ws.length = args.length := by simpa using congrArg List.length hsorts
  unfold dfdOk at hok
  split at hok
  · split at hok
    · rename_i a ha
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
      obtain ⟨⟨⟨⟨hsc, hctx⟩, hl⟩, -⟩, hhyps⟩ := hok
      have hn : (args.map Prod.fst).length = a.ctx.length := by simp [hctx]
      have hH : ∀ h ∈ a.hyps, h.Holds M ws := fun h hh ↦
        holds_of_hypOk hpat hargs hws (hn ▸ (scoped_hyps hsc h hh).1)
          (hn ▸ (scoped_hyps hsc h hh).2) (hhyps h hh)
      obtain ⟨w, h₁, -⟩ := hM.axs _ _ ha ws (hsorts.trans hctx.symm) hH
      rw [hl, ← hlen, eval_opVars] at h₁
      exact ⟨w, h₁⟩
    · simp at hok
  · split at hok
    · rename_i a ha
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.isEmpty_iff] at hok
      obtain ⟨⟨⟨hctx, hhyps⟩, hlab⟩, hch⟩ := hok
      obtain ⟨w, h₁, -⟩ := hM.axs _ _ ha ws (hsorts.trans hctx.symm)
        (by simp [hhyps])
      obtain ⟨l', hl'⟩ : ∃ l', a.concl.lhs.label = l' + 1 := ⟨a.concl.lhs.label - 1, by omega⟩
      rw [← RoseTree.node_label_children a.concl.lhs, hl', hch, eval_node_succ,
        part_bind_eq_some_iff] at h₁
      obtain ⟨vs, hvs, -⟩ := h₁
      rw [mapM_part_eq_some_iff] at hvs
      obtain ⟨v, hv⟩ : ∃ v, eval M ws (opVars k args.length) = Part.some v := by
        cases vs with
        | nil => simp at hvs
        | cons v _ =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq] at hvs
          exact ⟨v, hvs.1⟩
      rw [← hlen, eval_opVars] at hv
      exact ⟨v, hv⟩
    · simp at hok
  · split at hok
    · rename_i a ha
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hok
      obtain ⟨⟨⟨hctx, hhyps⟩, hargs0⟩, hr⟩ := hok
      subst hargs0
      have hws0 : ws = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hws0
      obtain ⟨w, -, h₂⟩ := hM.axs _ _ ha [] (by simp [hctx]) (by simp [hhyps])
      rw [hr] at h₂
      exact ⟨w, (eval_opVars k ([] : List M.Val)).symm.trans h₂⟩
    · simp at hok
  · simp at hok

/-- The canonical bound the domain or codomain rule computes has the value of the operation
{lit}`o` at the application's value. -/
theorem bound_sound (hM : E.Sound M)
    {patInf : List (Tree × Ann) → Tree → Option (Tree × Ann)} (hpat : PatSound M ρ patInf)
    {args : List (Tree × Ann)} (hargs : ∀ e ∈ args, e.2.Holds M ρ e.1) {ws : List M.Val}
    (hws : (args.map Prod.fst).map (eval M ρ) = ws.map Part.some)
    (hsorts : ws.map Sigma.fst = args.map (·.2.sort)) {o k j : ℕ} {lo : Tree} {w : M.Val}
    (hw : M.op k ws = Part.some w) (h : bound E patInf args o k j = some lo) :
    ∃ d, M.op o [w] = Part.some d ∧ eval M ρ lo = Part.some d := by
  have hlen : ws.length = args.length := by simpa using congrArg List.length hsorts
  have ht : eval M ws (opVars k args.length) = Part.some w := by rw [← hlen, eval_opVars, hw]
  unfold bound at h
  split at h
  · rename_i a ha
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at hc
      obtain ⟨⟨⟨hsc, hctx⟩, hl⟩, hhyps⟩ := hc
      have hn : (args.map Prod.fst).length = a.ctx.length := by simp [hctx]
      have hH : ∀ h ∈ a.hyps, h.Holds M ws := by
        intro h hh
        obtain ⟨he, hd⟩ := hhyps h hh
        unfold Eqn.Holds
        rw [← he]
        rcases hd with ht' | hs
        · rw [ht']
          exact ⟨w, ht, ht⟩
        · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
          obtain ⟨hrt, v, hv, -⟩ := hpat args h.lhs r hr hargs
          rw [hrt, eval_subst hws _ (hn ▸ (scoped_hyps hsc h hh).1)] at hv
          exact ⟨v, hv, hv⟩
      obtain ⟨d, h₁, h₂⟩ := hM.axs _ _ ha ws (hsorts.trans hctx.symm) hH
      rw [hl, eval_op, show [opVars k args.length].mapM (eval M ws) = Part.some [w] by
        simp [ht, Part.bind_some, Part.pure_eq_some], Part.bind_some] at h₁
      split at h
      · rename_i u r hr
        split at h
        · rename_i hro
          cases h
          rw [beq_iff_eq] at hro
          obtain ⟨hu, v, hv, -, hvl, -⟩ := hpat args a.concl.rhs _ hr hargs
          simp only at hu hv hvl
          rw [hu, eval_subst hws _ (hn ▸ (scoped_concl hsc).2), h₂, Part.some_inj] at hv
          subst hv
          exact ⟨d, h₁, hvl hro⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- An object whose canonical form has the value of an application has the typing of an
object of that form. -/
theorem holds_canon {t c : Tree} {w : M.Val} (ht : eval M ρ t = Part.some w) (hw : w.1 = obj)
    (hc : eval M ρ c = Part.some w) : Ann.Holds M ρ t ⟨obj, c, c⟩ :=
  ⟨w, ht, hw, fun _ ↦ hc, fun h ↦ ((by decide : obj ≠ arr) h).elim⟩

/-- The typing the inference computes for an object-valued application of an operation of the
signature holds, when the application has an object as its value. -/
theorem inferObj_sound {k : ℕ} {args : List (Tree × Ann)} {a : Ann}
    (hargs : ∀ e ∈ args, e.2.Holds M ρ e.1) {w : M.Val}
    (hnode : eval M ρ (op k (args.map Prod.fst)) = Part.some w) (hw : w.1 = obj)
    (h : inferObj k args = some a) : a.Holds M ρ (op k (args.map Prod.fst)) := by
  unfold inferObj at h
  split at h
  next u f =>
    split at h
    next hf =>
      cases h
      rw [beq_iff_eq] at hf
      obtain ⟨-, -, -, -, hb⟩ := hargs (u, f) List.mem_cons_self
      obtain ⟨⟨d, hd, hd'⟩, -⟩ := hb hf
      have e : d = w := Part.some_inj.mp (hd.symm.trans hnode)
      exact holds_canon hnode hw (e ▸ hd')
    next => simp at h
  next u f =>
    split at h
    next hf =>
      cases h
      rw [beq_iff_eq] at hf
      obtain ⟨-, -, -, -, hb⟩ := hargs (u, f) List.mem_cons_self
      obtain ⟨-, ⟨c, hc, hc'⟩⟩ := hb hf
      have e : c = w := Part.some_inj.mp (hc.symm.trans hnode)
      exact holds_canon hnode hw (e ▸ hc')
    next => simp at h
  next =>
    cases h
    obtain ⟨ws, hws, -⟩ := exists_values args hargs
    refine holds_canon hnode hw ?_
    rw [← hnode, eval_op_of_values hws, eval_op_of_values (ws := ws)]
    rw [← hws, List.map_map, List.map_map]
    refine List.map_congr_left fun p hp ↦ ?_
    simp only [Function.comp_apply]
    split
    · rename_i hs
      rw [beq_iff_eq] at hs
      obtain ⟨v, hv, -, ho, -⟩ := hargs p hp
      rw [ho hs, hv]
    · rfl

/-- The typing the inference computes for an arrow-valued application of an operation of the
signature holds, when the application has an arrow as its value. -/
theorem inferArr_sound (hM : E.Sound M)
    {patInf : List (Tree × Ann) → Tree → Option (Tree × Ann)} (hpat : PatSound M ρ patInf)
    {k : ℕ} {args : List (Tree × Ann)} {a : Ann} (hargs : ∀ e ∈ args, e.2.Holds M ρ e.1)
    {ws : List M.Val} (hws : (args.map Prod.fst).map (eval M ρ) = ws.map Part.some)
    (hsorts : ws.map Sigma.fst = args.map (·.2.sort)) {w : M.Val} (hw : M.op k ws = Part.some w)
    (hw₁ : w.1 = arr) (h : inferArr E patInf k args = some a) :
    a.Holds M ρ (op k (args.map Prod.fst)) := by
  have hnode := eval_op_of_values hws k
  have hbnd : ∀ o, eval M ρ (op o [op k (args.map Prod.fst)]) = M.op o [w] := fun o ↦
    eval_op_of_values (ws := [w]) (by simp [hnode, hw]) o
  unfold inferArr at h
  split at h
  next lo hi hlo hhi =>
    cases h
    obtain ⟨j, -, hj⟩ := Option.bind_eq_some_iff.mp hlo
    obtain ⟨d, hd, hd'⟩ := bound_sound hM hpat hargs hws hsorts hw hj
    obtain ⟨j', -, hj'⟩ := Option.bind_eq_some_iff.mp hhi
    obtain ⟨c, hc, hc'⟩ := bound_sound hM hpat hargs hws hsorts hw hj'
    exact ⟨w, hnode.trans hw, hw₁, fun h ↦ ((by decide : arr ≠ obj) h).elim,
      fun _ ↦ ⟨⟨d, (hbnd 0).trans hd, hd'⟩, ⟨c, (hbnd 1).trans hc, hc'⟩⟩⟩
  next => simp at h

/-- The typing the inference computes for an application of a definition holds. -/
theorem inferDef_sound (hM : E.Sound M)
    {patInf : List (Tree × Ann) → Tree → Option (Tree × Ann)} (hpat : PatSound M ρ patInf)
    {k : ℕ} {args : List (Tree × Ann)} {a : Ann} (hargs : ∀ e ∈ args, e.2.Holds M ρ e.1)
    {ws : List M.Val} (hws : (args.map Prod.fst).map (eval M ρ) = ws.map Part.some)
    (hsorts : ws.map Sigma.fst = args.map (·.2.sort))
    (h : inferDef E patInf k args = some a) : a.Holds M ρ (op k (args.map Prod.fst)) := by
  have hlen : ws.length = args.length := by simpa using congrArg List.length hsorts
  unfold inferDef at h
  split at h
  next d ax _ hax =>
    split at h
    next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨hsc, hctx⟩, hhyps⟩, hconcl⟩ := hc
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hrt, hrh⟩ := hpat args d.body r hr hargs
      have hn : (args.map Prod.fst).length = ax.ctx.length := by simp [hctx]
      have hbsc : Scoped (args.map Prod.fst).length d.body = true := by
        have := (scoped_concl hsc).2
        rw [hconcl] at this
        exact hn ▸ this
      obtain ⟨v, hv, -⟩ := id hrh
      have hbv : eval M ws d.body = Part.some v := by
        rw [← eval_subst hws _ hbsc, ← hrt]
        exact hv
      obtain ⟨u, h₁, h₂⟩ := hM.axs _ _ hax ws (hsorts.trans hctx.symm)
        (by rw [hhyps]; simpa using ⟨v, hbv, hbv⟩)
      rw [hconcl] at h₁ h₂
      simp only at h₁ h₂
      rw [← hlen, eval_opVars] at h₁
      rw [hbv, Part.some_inj] at h₂
      subst h₂
      refine Ann.holds_of_eval_eq ?_ hrh
      rw [eval_op_of_values hws, h₁, hv]
    next => simp at h
  next => simp at h

/-- The typing the inference computes for an application holds of it, when its arguments'
typings hold and the pattern inference is sound. -/
theorem inferOp_sound (hM : E.Sound M)
    {patInf : List (Tree × Ann) → Tree → Option (Tree × Ann)} (hpat : PatSound M ρ patInf)
    {k : ℕ} {args : List (Tree × Ann)} {a : Ann} (hargs : ∀ e ∈ args, e.2.Holds M ρ e.1)
    (h : inferOp E patInf k args = some a) : a.Holds M ρ (op k (args.map Prod.fst)) := by
  obtain ⟨ws, hws, hsorts⟩ := exists_values args hargs
  unfold inferOp at h
  split at h
  next as s hsig =>
    split at h
    next =>
      split at h
      next =>
        split at h
        next hdfd =>
          obtain ⟨w, hw⟩ := exists_op_of_dfdOk hM hpat hargs hws hsorts hdfd
          have hw₁ : w.1 = s := by
            have := M.op_sort (Part.eq_some_iff.mp hw)
            rw [hM.sg _ _ hsig, Option.map_some, Option.some.injEq] at this
            exact this.symm
          split at h
          next hs =>
            exact inferObj_sound hargs ((eval_op_of_values hws k).trans hw)
              (hw₁.trans (beq_iff_eq.mp hs)) h
          next =>
            split at h
            next hs =>
              exact inferArr_sound hM hpat hargs hws hsorts hw
                (hw₁.trans (beq_iff_eq.mp hs)) h
            next => simp at h
        next => simp at h
      next => exact inferDef_sound hM hpat hargs hws hsorts h
    next => simp at h
  next => simp at h

/-- The typing the inference computes for a variable holds, at an assignment of the context at
which the hypotheses hold, when the typings the term inference computes hold. -/
theorem inferVar_sound (hM : E.Sound M) {Γ : List ℕ} {H : List Eqn}
    (hρ : ρ.map Sigma.fst = Γ) (hH : ∀ h ∈ H, h.Holds M ρ) {treeInf : Tree → Option Ann}
    (htree : ∀ t a, treeInf t = some a → a.Holds M ρ t) {v : ℕ} {a : Ann}
    (h : inferVar E Γ H treeInf v = some a) : a.Holds M ρ (var v) := by
  have hv : ∀ s, Γ[v]? = some s → ∃ w, ρ[v]? = some w ∧ w.1 = s := fun s hs ↦ by
    have e := congrArg (fun l ↦ l[v]?) hρ
    simp only [List.getElem?_map, hs] at e
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp e
    exact ⟨w, hw, rfl⟩
  unfold inferVar at h
  split at h
  next hs =>
    cases h
    obtain ⟨w, hw, hw₁⟩ := hv 0 hs
    have ht : eval M ρ (var v) = Part.some w := by simp [hw, Part.coe_some]
    exact ⟨w, ht, hw₁, fun _ ↦ ht, fun h ↦ ((by decide : obj ≠ arr) h).elim⟩
  next hs =>
    obtain ⟨w, hw, hw₁⟩ := hv 1 hs
    have ht : eval M ρ (var v) = Part.some w := by simp [hw, Part.coe_some]
    have hside : ∀ o b, (if (match E.axs[o]? with
          | some a => a.ctx == [arr] && a.hyps.isEmpty && a.concl == dfd (op o [x 0])
          | none => false) = true then
        match H.find? (·.lhs == op o [var v]) with
        | some q => (treeInf q.rhs).bind fun a ↦ if a.sort == obj then some a.lo else none
        | none => some (op o [var v])
        else none) = some b →
        ∃ d, eval M ρ (op o [var v]) = Part.some d ∧ eval M ρ b = Part.some d := by
      intro o b hb
      split at hb
      next A hA =>
        split at hb
        next hax =>
          simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hax
          obtain ⟨⟨hctx, hhyps⟩, hconcl⟩ := hax
          obtain ⟨d, hd, -⟩ := hM.axs _ _ hA [w] (by simp [hctx, hw₁])
            (by simp [hhyps])
          have hop : eval M ρ (op o [var v]) = Part.some d := by
            rw [hconcl] at hd
            have e₁ : eval M [w] (op o [x 0]) = M.op o [w] :=
              eval_op_of_values (ws := [w]) (by simp) o
            rw [eval_op_of_values (ws := [w]) (by simp [ht]) o, ← e₁]
            exact hd
          split at hb
          next q hq =>
            have hqh := hH q (List.mem_of_find?_eq_some hq)
            have hql : q.lhs = op o [var v] := by
              have := List.find?_some hq
              simpa using this
            obtain ⟨a', ha', hb'⟩ := Option.bind_eq_some_iff.mp hb
            split at hb'
            next hs' =>
              cases hb'
              obtain ⟨d', hd₁, hd₂⟩ := hqh
              rw [hql, hop, Part.some_inj] at hd₁
              subst hd₁
              obtain ⟨u, hu, -, hu', -⟩ := htree q.rhs a' ha'
              rw [hd₂, Part.some_inj] at hu
              subst hu
              exact ⟨d, hop, hu' (beq_iff_eq.mp hs')⟩
            next => simp at hb'
          next =>
            cases hb
            exact ⟨d, hop, hop⟩
        next => simp at hb
      next => simp at hb
    obtain ⟨lo, hlo, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hi, hhi, rfl⟩ := Option.map_eq_some_iff.mp h'
    obtain ⟨d, hd, hd'⟩ := hside 0 lo hlo
    obtain ⟨c, hc, hc'⟩ := hside 1 hi hhi
    exact ⟨w, ht, hw₁, fun h ↦ ((by decide : arr ≠ obj) h).elim,
      fun _ ↦ ⟨⟨d, hd, hd'⟩, ⟨c, hc, hc'⟩⟩⟩
  next => simp at h

/-- The children of an application whose results are all defined, each with a property of its
child and result. -/
theorem forall_of_mapM {α : Type _} {cs : List Tree} {f : Tree → Option α} {rs : List α}
    (h : (cs.map fun c ↦ (c, f c)).mapM Prod.snd = some rs) :
    cs.length = rs.length ∧
      ∀ i (h₁ : i < cs.length) (h₂ : i < rs.length), f cs[i] = some rs[i] := by
  rw [mapM_eq_some_iff, List.map_map] at h
  have hl : cs.length = rs.length := by simpa using congrArg List.length h
  refine ⟨hl, fun i h₁ h₂ ↦ ?_⟩
  have e := List.getElem_of_eq h (by simpa using h₁)
  simpa using e

/-- Every typing the inferences at a fuel compute holds, at an assignment of the context at
which the hypotheses hold. -/
theorem infers_sound (hM : E.Sound M) {Γ : List ℕ} {H : List Eqn}
    (hρ : ρ.map Sigma.fst = Γ) (hH : ∀ h ∈ H, h.Holds M ρ) (n : ℕ) :
    PatSound M ρ (infers E Γ H n).1 ∧
      ∀ t a, (infers E Γ H n).2 t = some a → a.Holds M ρ t :=
  n.rec (motive := fun n ↦ PatSound M ρ (infers E Γ H n).1 ∧
      ∀ t a, (infers E Γ H n).2 t = some a → a.Holds M ρ t)
    ⟨fun _ _ _ h ↦ by simp [infers] at h, fun _ _ h ↦ by simp [infers] at h⟩
    (fun n ih ↦ by
      refine ⟨fun env ↦ RoseTree.ind fun l cs ihp r h henv ↦ ?_,
        RoseTree.ind fun l cs iht a h ↦ ?_⟩
      · change RoseTree.para (patStep E (infers E Γ H n).1 env) (RoseTree.node l cs) =
          some r at h
        rw [RoseTree.para_node] at h
        rcases l with _ | k
        · rcases cs with _ | ⟨v, _ | ⟨v', cs⟩⟩
          · simp [patStep] at h
          · simp only [patStep, List.map_cons, List.map_nil, Option.ite_none_right_eq_some,
              List.isEmpty_iff] at h
            obtain ⟨hv, h⟩ := h
            refine ⟨?_, henv r (List.mem_of_getElem? h)⟩
            rw [subst_node_zero _ hv, List.getElem?_map, h, Option.map_some, Option.getD_some]
          · simp [patStep] at h
        · simp only [patStep, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
          obtain ⟨args, hargs, a, ha, hr⟩ := h
          cases hr
          obtain ⟨hl, hc⟩ := forall_of_mapM hargs
          have hch : ∀ i (h₁ : i < cs.length) (h₂ : i < args.length),
              args[i].1 = subst (env.map Prod.fst) cs[i] ∧ args[i].2.Holds M ρ args[i].1 :=
            fun i h₁ h₂ ↦ ihp cs[i] (List.getElem_mem h₁) _ (hc i h₁ h₂) henv
          have hfst : args.map Prod.fst = cs.map (subst (env.map Prod.fst)) :=
            List.ext_getElem (by simp [hl]) fun i h₁ h₂ ↦ by
              simp only [List.getElem_map]
              exact (hch i (by simpa using h₂) (by simpa using h₁)).1
          have hall : ∀ e ∈ args, e.2.Holds M ρ e.1 := fun e he ↦ by
            obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
            exact (hch i (hl ▸ hi) hi).2
          refine ⟨?_, inferOp_sound hM ih.1 hall ha⟩
          change op k (args.map Prod.fst) = _
          rw [hfst, subst_node_succ]
          rfl
      · change RoseTree.para (treeStep E Γ H (infers E Γ H n).1 (infers E Γ H n).2)
          (RoseTree.node l cs) = some a at h
        rw [RoseTree.para_node] at h
        rcases l with _ | k
        · rcases cs with _ | ⟨v, _ | ⟨v', cs⟩⟩
          · simp [treeStep] at h
          · simp only [treeStep, List.map_cons, List.map_nil, Option.ite_none_right_eq_some,
              List.isEmpty_iff] at h
            obtain ⟨hv, h⟩ := h
            refine Ann.holds_of_eval_eq ?_ (inferVar_sound hM hρ hH ih.2 h)
            rw [eval_node_zero hv, eval_var]
          · simp [treeStep] at h
        · simp only [treeStep, Option.bind_eq_bind, Option.bind_eq_some_iff, List.map_map] at h
          obtain ⟨as, has, ha⟩ := h
          obtain ⟨hl, hc⟩ := forall_of_mapM has
          have hfz : (cs.zip as).map Prod.fst = cs := by
            rw [List.map_fst_zip (by omega)]
          have hall : ∀ e ∈ cs.zip as, e.2.Holds M ρ e.1 := fun e he ↦ by
            obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
            have hi₁ : i < cs.length := by simp at hi; omega
            have hi₂ : i < as.length := by simp at hi; omega
            simp only [List.getElem_zip]
            exact iht cs[i] (List.getElem_mem hi₁) _ (hc i hi₁ hi₂)
          have := inferOp_sound hM ih.1 hall (by simpa [Function.comp_def] using ha)
          rw [hfz] at this
          exact this)

end Soundness

end Geb.FreeTopos

end

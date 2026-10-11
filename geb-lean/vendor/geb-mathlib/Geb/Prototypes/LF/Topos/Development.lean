/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.LF.Topos.ProofSound

set_option doc.verso true in
/-!
# The signature of a development

A development of the internal language, its constants {lit}`G` and its environment {lit}`E`,
determines an extension of the signature {name}`Geb.LF.Topos.sig`. Its table
({lit}`devIdx`) names, past the indices of the primitive arrows the signature's own constants
encode, each object definition of {lit}`G`, each definition of the language and each primitive
arrow, the unfolding of each definition, the induction on each primitive arrow that projects onto
a coequalizer, and each well-formed theorem of {lit}`E`, each with the numbers its declaration
takes, where {lit}`G` has the constant of those numbers as the extension declares it
({lit}`admits`). The extension declares each constant of the table at its position
({lit}`extTy`, {lit}`devSig`), where the extension is formed, the operations of its type
operations are unique and the table names each constant once, which {lit}`devSig` decides.

Where it does, the extension is one {name}`Geb.LF.Topos.SigExt` and
{name}`Geb.LF.Topos.ExtDecl` describe ({lit}`devSig_spec`), so that the decoding of every proof
in it is sound ({lit}`devSig_decPf_checks`): the soundness of the decoding of proofs holds in the
signature of every development whose primitive arrows include those the indices name.

## Main definitions

* {lit}`admits` — whether a development has the constant an entry of a table names.
* {lit}`devIdx` — the table of a development.
* {lit}`extTy` — the declaration of an entry of a table.
* {lit}`devSig` — the signature of a development.

## Main statements

* {lit}`devSig_spec` — the signature of a development is an extension that declares its table.
* {lit}`devSig_decPf_checks` — the soundness of the decoding of proofs in it.

## Tags

logical framework, LF, signature, development, theorem, definition, quotient, internal language
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF.Topos

open FreeTopos.Internal (Globals Entry Thm)
open scoped FinEnum

/-- The candidates for the table of a development: the object definitions of {lit}`G`, each
with the operation its position names; its definitions of the language and its primitive arrows,
as constants of the language; the unfoldings of its definitions; the inductions on its primitive
arrows, each with the operation at the root of the arrow's codomain; and the theorems of
{lit}`E`; each with the numbers of its object parameters and parameters. -/
def devConsts (G : Globals) (E : Array Entry) : List ExtConst :=
  G.defs.zipIdx.filterMap (fun x ↦ match x.1 with
      | .object m _ => some (.obj (G.base + x.2) m)
      | .language _ => none) ++
    G.defs.zipIdx.filterMap (fun x ↦ match x.1 with
      | .language d => some (.tm (.defn x.2) d.arity d.params.length)
      | .object _ _ => none) ++
    G.prims.zipIdx.map (fun x ↦ .tm (.arr x.2) x.1.arity 1) ++
    G.defs.zipIdx.filterMap (fun x ↦ match x.1 with
      | .language d => some (.delta x.2 d.arity d.params.length)
      | .object _ _ => none) ++
    G.prims.zipIdx.map (fun x ↦ .quotInd x.2 x.1.arity (x.1.cod.label - 1)) ++
    E.toList.zipIdx.filterMap fun x ↦ x.1.language?.map fun a ↦ .thm x.2 a.arity a.ctx.length

/-- Whether the constants {lit}`G` and the environment {lit}`E` have the constant an entry of a
table names, of the numbers it records, as an extension declares it: an object definition at the
operation; a definition of the language or a primitive arrow other than those the indices
{lit}`k₀` name, its parameters and value of types; the unfolding of a definition of a body that
compiles; the induction on a primitive arrow that projects onto a coequalizer, onto the object
definition at its object parameters; and a well-formed theorem. -/
def admits (k₀ : PrimIdx) (G : Globals) (E : Array Entry) : ExtConst → Bool
  | .obj op m => decide (G.base ≤ op) && match G.defs[op - G.base]? with
    | some (.object m' _) => m' == m
    | _ => false
  | .tm h m p => !k₀.fixedHead h && match h.rank G with
    | some r => m == r.arity && p == r.params.length && r.ok G
    | none => false
  | .delta kd m p => match G.defs[kd]? with
    | some (.language d) => m == d.arity && p == d.params.length &&
      (FreeTopos.Internal.Defn.compile G d).isSome
    | _ => false
  | .quotInd kq m op => match G.prims[kq]? with
    | some p => m == p.arity &&
      decide (p.cod = PartialHorn.op op (FreeTopos.Internal.objVars p.arity)) && p.coeqParts.isSome
    | none => false
  | .thm j m p => match (E[j]?).bind Entry.language? with
    | some a => m == a.arity && p == a.ctx.length && a.wellFormed G
    | none => false

/-- The table of a development: past the indices {lit}`k₀`, the candidates that it has as an
extension declares them. -/
def devIdx (k₀ : PrimIdx) (G : Globals) (E : Array Entry) : PrimIdx :=
  { k₀ with ext := (devConsts G E).filter (admits k₀ G E) }

/-- The declaration of an entry of a table: an object definition's, the products over the kind
of types into it; a constant of the language's, as {name}`Geb.LF.Topos.defTy` declares its rank;
the theorem that unfolds a definition's and a theorem's, as {name}`Geb.LF.Topos.thmTy` declares
them; and an induction on a quotient's, as {name}`Geb.LF.Topos.quotIndTy` declares it. -/
def extTy (G : Globals) (E : Array Entry) (k : PrimIdx) : ExtConst → Option Expr
  | .obj _ m => some (piTele (List.replicate m tp) tp)
  | .tm h _ _ => (h.rank G).bind (defTy k)
  | .delta kd _ _ => match G.defs[kd]? with
    | some (.language d) => thmTy G k (deltaThm kd d)
    | _ => none
  | .quotInd kq _ _ => (G.prims[kq]?).bind (quotIndTy k kq)
  | .thm j _ _ => ((E[j]?).bind Entry.language?).bind (thmTy G k)

/-- Whether the operations of the type operations of a table are unique to their entries. -/
def PrimIdx.tyUniqueB (k : PrimIdx) : Bool :=
  k.tyTable.all fun t ↦ k.tyTable.all fun t' ↦ !(t.1 == t'.1 && t.2.1 == t'.2.1) || t == t'

/-- The signature of a development: the signature followed by the declarations of the entries of
its table, where it is formed, the operations of its type operations are unique and its table
names each constant once. -/
def devSig (k₀ : PrimIdx) (G : Globals) (E : Array Entry) : Option Sig :=
  ((devIdx k₀ G E).ext.mapM (extTy G E (devIdx k₀ G E))).bind fun Ts ↦
    if (sig ++ Ts).ok && (devIdx k₀ G E).tyUniqueB && decide (devIdx k₀ G E).ext.Nodup then
      some (sig ++ Ts)
    else none

variable {k k₀ : PrimIdx} {G : Globals} {E : Array Entry} {sg : Sig}

/-- The operations of the type operations of a table the check accepts are unique. -/
theorem PrimIdx.tyUnique_of_tyUniqueB (h : k.tyUniqueB = true) : k.TyUnique :=
  fun t ht t' ht' h₁ h₂ ↦ by
    have := List.all_eq_true.mp (List.all_eq_true.mp h t ht) t' ht'
    rw [h₁, h₂, beq_self_eq_true, beq_self_eq_true, Bool.and_self, Bool.not_true,
      Bool.false_or] at this
    exact beq_iff_eq.mp this

/-- A constant of a list without repetitions is found at its position. -/
theorem ExtConst.find?_of_nodup (x : ExtConst) :
    ∀ (l : List ExtConst) (i : ℕ), l.Nodup → l[i]? = some x → x.find? l = some i := by
  intro l
  refine List.rec (motive := fun l ↦ ∀ i, l.Nodup → l[i]? = some x → x.find? l = some i)
    (fun _ _ h ↦ nomatch h) (fun y l ih i hnd h ↦ ?_) l
  change (if y = x then some 0 else (x.find? l).map (· + 1)) = some i
  obtain ⟨hy, hnd⟩ := List.nodup_cons.mp hnd
  rcases i with _ | i
  · rw [List.getElem?_cons_zero] at h
    rw [if_pos (Option.some.inj h)]
  · rw [List.getElem?_cons_succ] at h
    have hx : x ∈ l := List.mem_of_getElem? h
    rw [if_neg (fun e : y = x ↦ hy (e ▸ hx)), ih i hnd h]
    rfl

/-- The declaration of a theorem has the head of the family of proofs. -/
theorem headDepth_thmTy {a : Thm} {T : Expr} (h : thmTy G k a = some T) :
    T.headDepth.1 = some 17 := by
  obtain ⟨ΓT, Hs, C, -, -, -, rfl⟩ := thmTy_eq_some h
  rw [headDepth_piTele]
  refine List.rec (motive := fun Hs ↦ (arrows Hs (pf C)).headDepth.1 = some 17) rfl
    (fun H Hs ih ↦ ?_) (Hs.map pf)
  change (Expr.pi H (arrows Hs (pf C)).shift).headDepth.1 = some 17
  rw [Expr.pi, headDepth_node]
  change (headDepthStep .pi [H.headDepth, ((arrows Hs (pf C)).rename Nat.succ).headDepth]).1 = _
  rw [headDepth_rename]
  exact ih

/-- The declaration of a constant of the language has the head of the family of terms. -/
theorem headDepth_defTy {r : Rank} {T : Expr} (h : defTy k r = some T) :
    T.headDepth.1 = some 6 := by
  simp only [defTy, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨ΓT, -, A, -, rfl⟩ := h
  rw [headDepth_piTele]
  rfl

/-- The declaration of an entry of a table ends in the kind of types only at an object
definition, and in the family of terms only at a constant of the language. -/
theorem extTy_headDepth {x : ExtConst} {T : Expr} (h : extTy G E k x = some T) :
    (T.headDepth.1 = some 0 → ∃ op m, x = .obj op m) ∧
      (T.headDepth.1 = some 6 → ∃ h m p, x = .tm h m p) := by
  have h17 : T.headDepth.1 = some 17 → (T.headDepth.1 = some 0 → ∃ op m, x = .obj op m) ∧
      (T.headDepth.1 = some 6 → ∃ h m p, x = .tm h m p) := fun e ↦
    ⟨fun e' ↦ (nomatch e.symm.trans e'), fun e' ↦ (nomatch e.symm.trans e')⟩
  rcases x with ⟨j, m, p⟩ | ⟨hd, m, p⟩ | ⟨kd, m, p⟩ | ⟨op, m⟩ | ⟨kq, m, op⟩
  · obtain ⟨a, -, ha⟩ := Option.bind_eq_some_iff.mp h
    exact h17 (headDepth_thmTy ha)
  · obtain ⟨r, -, hr⟩ := Option.bind_eq_some_iff.mp h
    have e := headDepth_defTy hr
    exact ⟨fun e' ↦ (nomatch e.symm.trans e'), fun _ ↦ ⟨hd, m, p, rfl⟩⟩
  · simp only [extTy] at h
    split at h
    · exact h17 (headDepth_thmTy h)
    · exact nomatch h
  · obtain rfl := Option.some.inj h
    have e : (piTele (List.replicate m tp) tp).headDepth.1 = some 0 := by
      rw [headDepth_piTele]
      rfl
    exact ⟨fun _ ↦ ⟨op, m, rfl⟩, fun e' ↦ (nomatch e.symm.trans e')⟩
  · obtain ⟨p, -, hp⟩ := Option.bind_eq_some_iff.mp h
    simp only [quotIndTy, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hp
    obtain ⟨_, -, _, -, _, -, _, -, rfl⟩ := hp
    exact h17 (by rw [headDepth_piTele]; rfl)

/-- The facts the check of the signature of a development gives: the declarations of its table's
entries, the formation of the extension, the uniqueness of its type operations and of its
entries. -/
theorem devSig_eq_some (h : devSig k₀ G E = some sg) :
    ∃ Ts, (devIdx k₀ G E).ext.mapM (extTy G E (devIdx k₀ G E)) = some Ts ∧ sg = sig ++ Ts ∧
      sg.ok = true ∧ (devIdx k₀ G E).tyUniqueB = true ∧ (devIdx k₀ G E).ext.Nodup := by
  obtain ⟨Ts, hTs, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · next hc =>
    obtain rfl := (Option.some.inj h).symm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨Ts, hTs, rfl, hc.1.1, hc.1.2, hc.2⟩
  · exact nomatch h

/-- The entry of a table at a position, of a list of values of a partial function on it, has
its value at that position. -/
theorem getElem?_of_mapM {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) {i : ℕ} {x : α} (hx : xs[i]? = some x) :
    ∃ y, f x = some y ∧ ys[i]? = some y := by
  have hm := congrArg (·[i]?) ((PartialHorn.mapM_eq_some_iff xs ys).mp h)
  simp only [List.getElem?_map, hx, Option.map_some] at hm
  cases hy : ys[i]? with
  | none => rw [hy, Option.map_none] at hm; exact nomatch hm
  | some y => rw [hy, Option.map_some, Option.some.injEq] at hm; exact ⟨y, hm, rfl⟩

/-- The signature of a development is an extension of the signature with its constants and its
table, and declares the theorems, the unfoldings and the inductions on quotients that its table
names. -/
theorem devSig_spec (h : devSig k₀ G E = some sg) :
    SigExt G (devIdx k₀ G E) sg ∧ ExtDecl G E (devIdx k₀ G E) sg := by
  obtain ⟨Ts, hTs, rfl, hok, huniq, hnd⟩ := devSig_eq_some h
  have hadm : ∀ i x, (devIdx k₀ G E).ext[i]? = some x → admits k₀ G E x = true :=
    fun _ _ hx ↦ (List.mem_filter.mp (List.mem_of_getElem? hx)).2
  have hpos : ∀ i x, (devIdx k₀ G E).ext[i]? = some x →
      ∃ T, extTy G E (devIdx k₀ G E) x = some T ∧ (sig ++ Ts)[sig.length + i]? = some T :=
    fun i x hx ↦ by
      obtain ⟨T, hT, hi⟩ := getElem?_of_mapM hTs hx
      exact ⟨T, hT, by rw [List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left, hi]⟩
  have hinv : ∀ i T, (sig ++ Ts)[sig.length + i]? = some T →
      ∃ x, (devIdx k₀ G E).ext[i]? = some x ∧ extTy G E (devIdx k₀ G E) x = some T :=
    fun i T hT ↦ by
      rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at hT
      have hi : i < (devIdx k₀ G E).ext.length := by
        rw [← length_of_mapM hTs]
        exact (List.getElem?_eq_some_iff.mp hT).1
      obtain ⟨T', hT', hi'⟩ := hpos i _ (List.getElem?_eq_getElem hi)
      rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, hT,
        Option.some.injEq] at hi'
      exact ⟨_, List.getElem?_eq_getElem hi, hi' ▸ hT'⟩
  refine ⟨⟨hok, List.prefix_append sig Ts, ?_, fun i op m hi ↦ ?_,
    PrimIdx.tyUnique_of_tyUniqueB huniq, fun i T hT h0 ↦ ?_, fun i hd m p hi ↦ ?_,
    fun i T hT h6 ↦ ?_⟩, fun i j m p hi ↦ ?_, fun i kd m p hi ↦ ?_, fun i kq m op hi ↦ ?_⟩
  · rw [List.length_append, length_of_mapM hTs]
  · obtain ⟨T, hT, hs⟩ := hpos i _ hi
    have ha := hadm i _ hi
    simp only [admits, Bool.and_eq_true, decide_eq_true_eq] at ha
    obtain ⟨hb, hd⟩ := ha
    refine ⟨⟨hb, ?_⟩, (Option.some.inj hT) ▸ hs⟩
    split at hd
    · next m' b hdef => exact ⟨b, by rw [hdef, beq_iff_eq.mp hd]⟩
    · exact nomatch hd
  · obtain ⟨x, hx, hT'⟩ := hinv i T hT
    obtain ⟨op, m, rfl⟩ := (extTy_headDepth hT').1 h0
    exact ⟨op, m, hx⟩
  · obtain ⟨T, hT, hs⟩ := hpos i _ hi
    have ha := hadm i _ hi
    simp only [admits, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at ha
    obtain ⟨hf, hr⟩ := ha
    split at hr
    · next r hrank =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hr
      obtain ⟨⟨rfl, rfl⟩, hrok⟩ := hr
      rw [extTy, hrank, Option.bind_some] at hT
      exact ⟨r, T, ExtConst.find?_of_nodup _ _ _ hnd hi, hf, hrank, rfl, rfl, hrok, hT, hs⟩
    · exact nomatch hr
  · obtain ⟨x, hx, hT'⟩ := hinv i T hT
    obtain ⟨hd, m, p, rfl⟩ := (extTy_headDepth hT').2 h6
    exact ⟨hd, m, p, hx⟩
  · obtain ⟨T, hT, hs⟩ := hpos i _ hi
    have ha := hadm i _ hi
    simp only [admits] at ha
    split at ha
    · next a hj =>
      simp only [Bool.and_eq_true, beq_iff_eq] at ha
      obtain ⟨⟨rfl, rfl⟩, hwf⟩ := ha
      rw [extTy, hj, Option.bind_some] at hT
      exact ⟨a, T, hj, rfl, rfl, hwf, hT, hs⟩
    · exact nomatch ha
  · obtain ⟨T, hT, hs⟩ := hpos i _ hi
    have ha := hadm i _ hi
    simp only [admits] at ha
    split at ha
    · next d hdef =>
      simp only [Bool.and_eq_true, beq_iff_eq] at ha
      obtain ⟨⟨rfl, rfl⟩, hc⟩ := ha
      simp only [extTy, hdef] at hT
      exact ⟨d, T, hdef, rfl, rfl, Option.isSome_iff_exists.mp hc, hT, hs⟩
    · exact nomatch ha
  · obtain ⟨T, hT, hs⟩ := hpos i _ hi
    have ha := hadm i _ hi
    simp only [admits] at ha
    split at ha
    · next p hp =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ha
      obtain ⟨⟨rfl, hcod⟩, hq⟩ := ha
      rw [extTy, hp, Option.bind_some] at hT
      exact ⟨p, T, hp, rfl, hcod, hq, hT, hs⟩
    · exact nomatch ha

/-- The primitive arrows of a development's table are those the indices name. -/
theorem devIdx_valid (hk : k₀.Valid G) : (devIdx k₀ G E).Valid G :=
  ⟨hk.zero, hk.succ, hk.nil, hk.cons, hk.node, hk.lnode, hk.inl, hk.inr, hk.case⟩

/-- The soundness of the decoding of proofs in the signature of a development whose primitive
arrows include those the indices {lit}`k₀` name, at a proof of a formula in a context of
{lit}`n` variables of {lit}`tp` and term variables of encoded types, types in {lit}`n` object
variables: the proof decodes to a derivation that proves the formula's decoding as a theorem of
the internal language, with the development's constants and environment. -/
theorem devSig_decPf_checks (hk : k₀.Valid G) (h : devSig k₀ G E = some sg) {n : ℕ} {ΓLF : Ctx}
    {Γ : List PartialHorn.Tree} (hΓT : encCtx (devIdx k₀ G E) n Γ = some ΓLF)
    (hΓ : Γ.all (FreeTopos.Internal.IsTy G n) = true) {M F : Expr}
    (hF : judge sg F ΓLF (.check (tm omega)) = true)
    (hj : judge sg M ΓLF (.check (pf F)) = true) :
    ∃ D φ, decPf (devIdx k₀ G E) M (List.replicate Γ.length none) 0 = some D ∧
      termOf (devIdx k₀ G E) (List.replicate Γ.length none) F = some φ ∧
      FreeTopos.Internal.Thm.checks G E ⟨n, Γ, [], φ⟩ D = true :=
  decPf_checks E (devIdx_valid hk) (devSig_spec h).1 (devSig_spec h).2 hΓT hΓ hF hj

end Geb.LF.Topos

end

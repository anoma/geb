/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Topos.Complete

set_option doc.verso true in
/-!
# Theorems as constants of an extension of the signature

The theorems of a development of the internal language enter the signature
{name}`Geb.LF.Topos.sig` as constants of an extension of it, past its own declarations, as a
logical framework's signature takes each proved lemma as a constant
(\[HarperLicata2007\], Section 2). A theorem, of object variables, of variables of types in
them, of hypotheses and of a conclusion, is the constant of the product over the kind of types,
one for each object variable, of the product over a family of terms of each variable's type, the
outermost first, of the products over the families of proofs of its hypotheses, none in the scope
of another, into the family of proofs of its conclusion ({lit}`thmTy`): its context is encoded as
{name}`Geb.LF.Topos.encCtx` encodes one, and its formulas as {name}`Geb.LF.Topos.enc` encodes
them, in the scope of the variables. An application of the constant decodes to the language's
application of the theorem's entry ({lit}`Geb.LF.Topos.decPfThm`), its spine instantiated as
{name}`Geb.LF.Topos.spine_piTele_gen` instantiates a telescope.

A definition of the language, a constant of the extension that {name}`Geb.LF.Topos.defTy`
declares, has its unfolding, δ, as a further constant: the theorem, in the definition's object
variables and parameters, that the definition at its variables, applied to its parameters,
equals its body ({lit}`deltaThm`), declared as any theorem is. Its instance at objects and terms
is the equation of the definition at them with its body at them ({lit}`instTerm_defn_vars`),
which the language's unfolding at the left side proves.

The quotient a development declares is an object definition, and its projection a primitive
arrow, each a constant of the extension as {name}`Geb.LF.Topos.SigExt` declares it. The induction
on the quotient is a further constant, declared as the signature's case analysis on a coproduct
is: the products over the kind of types, one for each object parameter of the projection, of the
product over a motive, an LF abstraction from the quotient into the subobject classifier, of the
arrow from the motive's proof at the projection's image of a variable of its domain into its
proof at every element of the quotient ({lit}`quotBody`, {lit}`quotIndTy`). An extension of the
signature declares the theorems, the unfoldings and the inductions on quotients that the
indices' table names at their positions ({lit}`ExtDecl`).

## Main definitions

* {lit}`thmTy` — the declaration of a theorem.
* {lit}`deltaThm` — the theorem that unfolds a definition.
* {lit}`quotBody`, {lit}`quotIndTy` — the declaration of the induction on a quotient.
* {lit}`ExtDecl` — an extension of the signature declares the theorems, the unfoldings and the
  inductions on quotients that a table names.

## Main statements

* {lit}`scopedBelow_enc` — the encoding of a term that compiles is in the scope of its context.
* {lit}`instTerm_eq`, {lit}`instTerm_defn_vars` — the instances of an equation and of a
  definition at its variables.

## References

* \[HarperLicata2007\], Section 2, for signatures and their constants.

## Tags

logical framework, LF, signature, theorem, lemma, definition, unfolding, quotient, induction,
internal language
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF.Topos

open FreeTopos.Internal (Term Globals Entry Thm ctxObj stdEnv)

variable {k : PrimIdx}

open FreeTopos.Internal (IsTy compile) in
/-- The encoding of a term of the internal language that compiles in a context of types in
{lit}`n` object variables is in the scope of the context's variables and the object
variables. -/
theorem scopedBelow_enc {G : Globals} {sg : Sig} (hsg : SigExt G k sg) {n : ℕ} (hk : k.Valid G)
    {Γ : List PartialHorn.Tree}
    {ΓT : Ctx} (hty : ∀ a ∈ Γ, IsTy G n a = true) (hΓ : encCtx k n Γ = some ΓT) {s : MTerm}
    {r : PartialHorn.Tree × PartialHorn.Tree} (hc : compile G n s (ctxObj Γ) (stdEnv Γ) = some r)
    {X : Expr} (he : enc G n k s (ctxObj Γ) (stdEnv Γ) = some X) :
    ScopedBelow (Γ.length + n) X := by
  obtain ⟨-, A, -, hj⟩ := enc_checks hsg hk s _ (stdEnv Γ) ΓT X r
    (fun p hp ↦ hty p.2
      (by rw [← FreeTopos.Internal.map_snd_stdEnv Γ]; exact List.mem_map_of_mem hp))
    (by rw [FreeTopos.Internal.map_snd_stdEnv]; exact hΓ) he hc
  have := judgeWith_freeBelow X ΓT _ hj
  rw [length_encCtx hΓ] at this
  exact freeBelow_scoped X _ this

/-- The declaration of a theorem of the language: the products over the kind of types, one for
each of its object variables, of the products over the families of terms of its variables'
types, the outermost first, each encoded at the offset of the variables outside it, of the
products over the families of proofs of its hypotheses into the family of proofs of its
conclusion, the formulas encoded in the scope of the variables. -/
def thmTy (G : Globals) (k : PrimIdx) (a : Thm) : Option Expr := do
  let ΓT ← encCtx k a.arity a.ctx
  let Hs ← a.hyps.mapM fun h ↦ enc G a.arity k h (ctxObj a.ctx) (stdEnv a.ctx)
  let C ← enc G a.arity k a.concl (ctxObj a.ctx) (stdEnv a.ctx)
  pure (piTele ΓT.reverse (arrows (Hs.map pf) (pf C)))

/-- The parts of the declaration of a theorem. -/
theorem thmTy_eq_some {G : Globals} {k : PrimIdx} {a : Thm} {T : Expr} (h : thmTy G k a = some T) :
    ∃ ΓT Hs C, encCtx k a.arity a.ctx = some ΓT ∧
      a.hyps.mapM (fun h ↦ enc G a.arity k h (ctxObj a.ctx) (stdEnv a.ctx)) = some Hs ∧
      enc G a.arity k a.concl (ctxObj a.ctx) (stdEnv a.ctx) = some C ∧
      T = piTele ΓT.reverse (arrows (Hs.map pf) (pf C)) := by
  simp only [thmTy, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨ΓT, hΓ, Hs, hHs, C, hC, rfl⟩ := h
  exact ⟨ΓT, Hs, C, hΓ, hHs, hC, rfl⟩

open FreeTopos.Internal (Defn Definition) in
/-- The theorem that unfolds a definition: in the definition's object variables and parameters,
the definition at the variables, applied to the parameters, the innermost first, equals its
body. -/
def deltaThm (kd : ℕ) (d : Defn) : Thm where
  arity := d.arity
  ctx := d.params
  hyps := []
  concl := Term.eq (Term.defn kd ((List.range d.arity).map PartialHorn.var)
    ((List.range d.params.length).map Term.var)) d.body

open FreeTopos.Internal (instTerm) in
/-- The instance of an equation is the equation of the instances. -/
theorem instTerm_eq (θ : List PartialHorn.Tree) (σ : List Term) (t u : Term) :
    instTerm θ σ (Term.eq t u) = Term.eq (instTerm θ σ t) (instTerm θ σ u) := by
  rw [instTerm, Term.eq, FreeTopos.Internal.Term.osubst_node, FreeTopos.Internal.Term.subst_node]
  rfl

/-- Objects substituted for the object variables, the first for the innermost, give the
objects. -/
theorem map_subst_vars (θ : List PartialHorn.Tree) :
    ((List.range θ.length).map PartialHorn.var).map (PartialHorn.subst θ) = θ :=
  List.ext_getElem (by rw [List.length_map, List.length_map, List.length_range])
    fun i h₁ h₂ ↦ by
      rw [List.getElem_map, List.getElem_map, List.getElem_range, PartialHorn.var,
        PartialHorn.subst_node_zero θ rfl, RoseTree.label_node,
        List.getElem?_eq_getElem h₂, Option.getD_some]

/-- An operation at the object variables, with objects substituted for them, is the operation at
the objects. -/
theorem subst_op_vars (op : ℕ) (θ : List PartialHorn.Tree) :
    PartialHorn.subst θ (PartialHorn.op op (FreeTopos.Internal.objVars θ.length)) =
      PartialHorn.op op θ := by
  rw [PartialHorn.op, PartialHorn.subst_node_succ]
  exact congrArg _ (map_subst_vars θ)

open FreeTopos.Internal (instTerm) in
/-- The instance of a definition at its variables, applied to its parameters, is the definition
at the objects, applied to the terms, the instance gives. -/
theorem instTerm_defn_vars (kd : ℕ) (θ : List PartialHorn.Tree) (σ : List Term) :
    instTerm θ σ (Term.defn kd ((List.range θ.length).map PartialHorn.var)
      ((List.range σ.length).map Term.var)) = Term.defn kd θ σ := by
  rw [instTerm, Term.defn, FreeTopos.Internal.Term.osubst_node,
    FreeTopos.Internal.Term.subst_node]
  have hσ : (((List.range σ.length).map Term.var).map (Term.osubst θ)).map
      (fun c ↦ Term.subst c (Term.substList σ)) = σ :=
    List.ext_getElem (by rw [List.length_map, List.length_map, List.length_map,
      List.length_range]) fun i h₁ h₂ ↦ by
        rw [List.getElem_map, List.getElem_map, List.getElem_map, List.getElem_range]
        change Term.subst (Term.var i) (Term.substList σ) = σ[i]
        rw [FreeTopos.Internal.Term.subst_var, Term.substList, List.getElem?_eq_getElem h₂,
          Option.getD_some]
  change RoseTree.node (.defn kd (((List.range θ.length).map PartialHorn.var).map
      (PartialHorn.subst θ))) (((((List.range σ.length).map Term.var).map (Term.osubst θ)).map
      fun c ↦ (c, Term.subst c)).map fun c ↦ c.2 (Term.substList σ)) = _
  rw [map_subst_vars, List.map_map]
  exact congrArg _ hσ

/-- The body of the declaration of the induction on a quotient, in its object parameters: the
product over a motive, from the family of terms of the quotient {lit}`Q₀` into the family of terms
of the subobject classifier, of the arrow from the product over the family of terms of the
projection's domain {lit}`A` of the family of proofs of the motive at the projection's application
{lit}`M` to the variable, into the product over the family of terms of the quotient {lit}`Q₁` of
the family of proofs of the motive at the variable. Each type is encoded at the offset of the
variables in its scope. -/
def quotBody (Q₀ A Q₁ M : Expr) : Expr :=
  Expr.pi (Expr.arrow (tm Q₀) (tm omega))
    (Expr.arrow (Expr.pi (tm A) (pf (Expr.var 1 [M])))
      (Expr.pi (tm Q₁) (pf (Expr.var 1 [Expr.var 0]))))

/-- The declaration of the induction on a quotient whose projection is the primitive arrow of
index {lit}`kq`: the products over the kind of types, one for each object parameter of the
projection, into the body ({lit}`quotBody`) at the projection's codomain and domain, with the
projection applied to the object parameters, the outermost first, and to the variable of its
domain. -/
def quotIndTy (k : PrimIdx) (kq : ℕ) (p : FreeTopos.Internal.Prim) : Option Expr := do
  let c ← k.tmConst (.arr kq) p.arity 1
  let Q₀ ← encTy k 0 p.cod
  let A ← encTy k 1 p.dom
  let Q₁ ← encTy k 1 p.cod
  pure (piTele (List.replicate p.arity tp) (quotBody Q₀ A Q₁
    (Expr.const c ((List.range p.arity).reverse.map (fun i ↦ Expr.var (2 + i)) ++ [Expr.var 0]))))

/-- An extension of the signature declares the theorems that the table of the indices names:
at the position of each earlier theorem the table names, the declaration of that theorem, a
well-formed theorem of as many object variables and variables as the table records, and at the
position of each unfolding of a definition the table names, of a body that compiles, the
declaration of the theorem that unfolds it, of as many object variables and parameters as the
table records, and at the position of each induction on a quotient the table names, whose
projection is a primitive arrow that projects onto a coequalizer, of as many object parameters
as the table records and onto the table's object definition at them, the declaration of the
induction ({lit}`quotIndTy`). The
unfolding is well formed where its definition's parameters and value are also of types, which an
extension declaring the definition records ({name}`Geb.LF.Topos.SigExt`), and the induction where
the projection's domain and codomain are, which an extension declaring the projection records. -/
def ExtDecl (G : Globals) (E : Array Entry) (k : PrimIdx) (sg : Sig) : Prop :=
  (∀ i j m p, k.ext[i]? = some (.thm j m p) → ∃ a T,
    (E[j]?).bind Entry.language? = some a ∧ m = a.arity ∧ p = a.ctx.length ∧
    a.wellFormed G = true ∧ thmTy G k a = some T ∧ sg[sig.length + i]? = some T) ∧
  (∀ i kd m p, k.ext[i]? = some (.delta kd m p) → ∃ d T,
    G.defs[kd]? = some (.language d) ∧ m = d.arity ∧ p = d.params.length ∧
    (∃ cd, FreeTopos.Internal.Defn.compile G d = some cd) ∧ thmTy G k (deltaThm kd d) = some T ∧
    sg[sig.length + i]? = some T) ∧
  (∀ i kq m op, k.ext[i]? = some (.quotInd kq m op) → ∃ p T,
    G.prims[kq]? = some p ∧ m = p.arity ∧
    p.cod = PartialHorn.op op (FreeTopos.Internal.objVars p.arity) ∧ p.coeqParts.isSome = true ∧
    quotIndTy k kq p = some T ∧ sg[sig.length + i]? = some T)

/-- The signature, at indices whose table is empty, declares the theorems the table names. -/
theorem extDecl_sig (G : Globals) (E : Array Entry) (hk : k.ext = []) : ExtDecl G E k sig := by
  refine ⟨fun i _ _ _ h ↦ ?_, fun i _ _ _ h ↦ ?_, fun i _ _ _ h ↦ ?_⟩ <;>
    · rw [hk] at h
      exact nomatch h

end Geb.LF.Topos

end

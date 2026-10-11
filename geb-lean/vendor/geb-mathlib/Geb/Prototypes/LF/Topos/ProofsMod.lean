/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Conversion
public import Geb.Prototypes.LF.Topos.Proofs

set_option doc.verso true in
/-!
# The decoding of proofs modulo the computation rules

The canonical LF terms of the families of proofs of {name}`Geb.LF.Topos.sig` that check modulo
the rewrite rules {lit}`Geb.LF.Topos.rules` decode to certificates of the checker with a step of
conversion ({name}`Geb.FreeTopos.Internal.convCheck`). Modulo the rules, LF compares a proof's
type with the type it is checked against after normalizing both by the computation rules, which
the internal language's derivations do not; the certificates take the step of conversion where
LF compares. The step normalizes under the computation rules of the language ({lit}`normC`):
the β rule, the computation rules of pairs, those of the folds of the natural numbers, of lists
and of rose trees, and those of the case analysis, at the primitives the indices name.

Reflexivity and each computation rule decode to an equation whose sides normalize to one term
({lit}`eqvC`). The substitution of equals and the inductions decode as {name}`Geb.LF.Topos.leibD`
and {name}`Geb.LF.Topos.indD` do, with the formula they prove normalized first, and the β-reduct
of the motive's application, from which it is proved, normalized to it ({lit}`leibC`,
{lit}`indC`), congruence as the substitution of equals does, and the case analysis on a
coproduct and a formula from a term of the initial object as the inductions do; function
extensionality, with its formula normalized first; and an application of a theorem, of the
unfolding of a definition or of the induction on a quotient past the signature as
{name}`Geb.LF.Topos.decPfThm` decodes it, the theorem's application converted from its instance
to the formula it proves, both normalized ({lit}`applyC`), since LF applies the theorem's
declaration at any type its instance converts to, the unfolding with its sides normalized after
it ({lit}`deltaC`) and the induction as the inductions do. The decoding is not proved to
produce certificates that check: the conversion checker, sound relative to the base checker,
decides each.

## Main definitions

* {lit}`computationRules`, {lit}`normC` — the computation rules and the step of conversion under
  them.
* {lit}`eqvC`, {lit}`leibC`, {lit}`indC` — the certificates of reflexivity, of the substitution
  of equals and of an induction.
* {lit}`deltaC` — the certificate of the unfolding of a definition.
* {lit}`applyC` — the certificate of the application of a theorem.
* {lit}`decPfMod` — the decoding of a proof modulo the rules.

## Tags

logical framework, LF, rewriting, conversion, proof, derivation, internal language
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF.Topos

open FreeTopos.Internal (Term Deriv ConvRule ConvDeriv Entry weaken1)

/-- A node of a certificate at a rule of the language's derivations. -/
abbrev ndC (r : FreeTopos.Internal.Rule) (cs : List ConvDeriv) : ConvDeriv :=
  RoseTree.node (.base r) cs

/-- The bound on the depth of the normalization of a step of conversion. -/
def normFuel : ℕ := 4096

/-- The computation rules of the language at the primitives the indices name: the β rule, the
computation rules of pairs, those of the folds of the natural numbers, of lists and of rose trees
of either kind, and those of the case analysis. -/
def computationRules (k : PrimIdx) : List FreeTopos.Internal.Rule :=
  [.beta, .fstPair, .sndPair, .natZero k.zero, .natSucc k.succ, .listNil k.nil, .listCons k.cons,
    .roseNode k.node k.nil k.cons, .roseNode k.lnode k.nil k.cons, .caseInl k.case k.inl,
    .caseInr k.case k.inr]

/-- The step of conversion under the computation rules. -/
def normC (k : PrimIdx) : ConvDeriv :=
  RoseTree.node (.norm ((computationRules k).map .rule) normFuel) []

/-- An equation whose sides normalize to one term. -/
def eqvC (k : PrimIdx) : ConvDeriv := ndC .join [normC k, normC k]

/-- The unfolding of a definition: an equation whose left side, unfolded at its root, and right
side normalize to one term. -/
def deltaC (k : PrimIdx) : ConvDeriv := ndC .join [ndC .trans [ndC .delta [], normC k], normC k]

/-- A formula proved after its normalization. -/
def convertC (k : PrimIdx) (D : ConvDeriv) : ConvDeriv := ndC .conv [normC k, D]

/-- The certificate of the substitution of equals: {name}`Geb.LF.Topos.leibD`, the formula it
proves normalized first and the β-reduct of the motive's application at the right side normalized
to it. -/
def leibC (k : PrimIdx) (a : PartialHorn.Tree) (pb t u : Term) (m : ℕ) (Dh Dp : ConvDeriv) :
    ConvDeriv :=
  convertC k (ndC (.cut (Term.eq t u)) [Dh, ndC (.convFrom (Term.app (Term.lam a pb) u))
    [ndC .trans [ndC .beta [], normC k],
      ndC .conv [ndC .cong [ndC .refl [], ndC (.rwHyp m true) []], ndC .conv [ndC .beta [], Dp]]]])

/-- The certificate of an induction at a term: {name}`Geb.LF.Topos.indD`, the formula it proves
normalized first and the β-reduct of the motive's application at the term normalized to it. -/
def indC (k : PrimIdx) (c : PartialHorn.Tree) (r : FreeTopos.Internal.Rule) (pb n : Term) (m : ℕ)
    (Ds : List ConvDeriv) : ConvDeriv :=
  let L := Term.lam c pb
  let R := Term.lam c truth
  let refl := ndC .join [ndC .refl [], ndC .refl []]
  convertC k (ndC (.cut (Term.eq L R))
    [ndC .funExt [ndC .conv [ndC .cong [ndC .beta [], ndC .beta []],
        ndC .propExt [refl, ndC r Ds]]],
      ndC (.convFrom (Term.app L n)) [ndC .trans [ndC .beta [], normC k],
        ndC .conv [ndC .cong [ndC (.rwHyp m false) [], ndC .refl []],
          ndC .conv [ndC .beta [], refl]]]])

/-- The certificate of a rule at its premises' certificates, the application of a theorem of
the environment {lit}`E` converted from its instance to the formula it proves, both normalized:
LF applies the theorem's declaration at any type its instance converts to. -/
def applyC (k : PrimIdx) (E : Array Entry) (r : FreeTopos.Internal.Rule) (ps : List ConvDeriv) :
    ConvDeriv := match r with
  | .apply j θ σ => match (E[j]?).bind Entry.language? with
    | some a =>
      convertC k (ndC (.convFrom (FreeTopos.Internal.instTerm θ σ a.concl)) [normC k, ndC r ps])
    | none => ndC r ps
  | r => ndC r ps

section Decoding

variable (k : PrimIdx) (E : Array Entry)

/-- One step of the decoding of a proof modulo the rules, at a node of a label, from its
children's decodings, each a function of an environment and the number of hypotheses. -/
def decPfModStep (l : Label) (cs : List (Expr × (List (Option ℕ) → ℕ → Option ConvDeriv)))
    (env : List (Option ℕ)) (m : ℕ) : Option ConvDeriv :=
  match l, cs with
    | .app (.var i), [] => match env[i]? with
      | some (some h) => some (ndC (.hyp h) [])
      | _ => none
    | .app (.const 18), [_, _] => some (eqvC k)
    | .app (.const 19), [(A, _), (P, _), (t, _), (u, _), (_, dh), (_, dp)] => do
      let pb ← lamBody (← termOf k env P)
      pure (leibC k (← decTy k env.length A) pb (← termOf k env t) (← termOf k env u) m (← dh env m)
        (← dp env (m + 1)))
    | .app (.const 20), [_, _, _, _] => some (eqvC k)
    | .app (.const 21), [_, _, _, _] => some (eqvC k)
    | .app (.const 22), [_, _, _, _] => some (eqvC k)
    | .app (.const 23), [_, _, _] => some (ndC .join [ndC .pairEta [], ndC .refl []])
    | .app (.const 24), [_] => some (ndC .join [ndC .unitEta [], ndC .refl []])
    | .app (.const 25), [_, _, _] => some (eqvC k)
    | .app (.const 26), [_, _, _, _] => some (eqvC k)
    | .app (.const 27), [_, _, _, _, (_, dH)] => do
      pure (convertC k (ndC .funExt [← dH (none :: env) m]))
    | .app (.const 28), [_, _, (_, d₁), (_, d₂)] => do
      pure (ndC .propExt [← d₁ (some m :: env) (m + 1), ← d₂ (some m :: env) (m + 1)])
    | .app (.const 29), [(P, _), (_, d₀), (_, ds), (n, _)] => do
      let pb ← lamBody (← termOf k env P)
      pure (indC k FreeTopos.nat (.natIndHyp k.zero k.succ) pb (← termOf k env n) m
        [← d₀ env (m + 1), ← ds (some (m + 1) :: none :: env) (m + 2)])
    | .app (.const 34), [_, _, _, _] => some (eqvC k)
    | .app (.const 35), [_, _, _, _, _, _] => some (eqvC k)
    | .app (.const 36), [(A, _), (P, _), (_, d₀), (_, ds), (l, _)] => do
      let a ← decTy k env.length A
      let pb ← lamBody (← termOf k env P)
      pure (indC k (FreeTopos.list a) (.listIndHyp k.nil k.cons) pb (← termOf k env l) m
        [← d₀ env (m + 1), ← ds (some (m + 1) :: none :: none :: env) (m + 2)])
    | .app (.const 40), [_, _, _, _] => some (eqvC k)
    | .app (.const 41), [(P, _), (_, ds), (t, _)] => do
      let pb ← lamBody (← termOf k env P)
      pure (indC k FreeTopos.rose (.roseIndHyp k.node k.nil k.cons) pb (← termOf k env t) m
        [← ds (some (m + 1) :: none :: none :: env) (m + 2)])
    | .app (.const 45), [_, _, _, _, _] => some (eqvC k)
    | .app (.const 46), [(A, _), (P, _), (_, ds), (t, _)] => do
      let a ← decTy k env.length A
      let pb ← lamBody (← termOf k env P)
      pure (indC k (FreeTopos.lrose a) (.roseIndHyp k.lnode k.nil k.cons) pb (← termOf k env t) m
        [← ds (some (m + 1) :: none :: none :: env) (m + 2)])
    | .app (.const 47), [(A, _), _, (f, _), (a, _), (b, _), (_, dh)] => do
      let fb ← lamBody (← termOf k env f)
      let sa ← termOf k env a
      pure (leibC k (← decTy k env.length A) (congMotive fb sa) sa (← termOf k env b) m (← dh env m)
        (eqvC k))
    | .app (.const 53), [_, _, _, _, _, _] => some (eqvC k)
    | .app (.const 54), [_, _, _, _, _, _] => some (eqvC k)
    | .app (.const 55), [(A, _), (B, _), (P, _), (_, d₁), (_, d₂), (c, _)] => do
      let a ← decTy k env.length A
      let b ← decTy k env.length B
      let pb ← lamBody (← termOf k env P)
      pure (indC k (FreeTopos.coprod a b) (.coprodInd k.inl k.inr) pb (← termOf k env c) m
        [← d₁ (none :: env) (m + 1), ← d₂ (none :: env) (m + 1)])
    | .app (.const 56), [(z, _), (φ, _)] => do
      pure (indC k FreeTopos.zero (.zeroInd 0) (weaken1 (← termOf k env φ)) (← termOf k env z) m
        [])
    | .app (.const c), cs => decPfThm k (applyC k E) (deltaC k) (indC k) c cs env m
    | .lam, [(_, d)] => d env m
    | _, _ => none

/-- The decoding of a proof modulo the rules in an environment, under a number of hypotheses, the
theorems it applies those of the environment {lit}`E`. -/
def decPfMod : Expr → List (Option ℕ) → ℕ → Option ConvDeriv := RoseTree.para (decPfModStep k E)

end Decoding

end Geb.LF.Topos

end

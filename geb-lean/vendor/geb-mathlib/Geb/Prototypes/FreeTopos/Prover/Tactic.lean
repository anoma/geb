/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Prover.Rewrite

set_option doc.verso true in
/-!
# Tactics of the prover for the theory of an elementary topos

The prover's third layer: the steps a proof is written in, each computing a certificate. An
instance of an axiom or a theorem at terms has its hypotheses proved as the typing proves them.
The expansion of an arrow into a product by the uniqueness of pairing pairs its composites with
the projections. An equation holds by normalization when both sides have one normal form. A
sequent is proved in its own scope and added to the development, so that later proofs cite it.

## Main definitions

* {lit}`axIdx` — the index of an axiom by its block and its position there.
* {lit}`inst` — the instance of an axiom or theorem, with its certificate.
* {lit}`etaExpand` — the expansion of an arrow into a product.
* {lit}`deltaRule` — the unfolding of a definition, as a rule.
* {lit}`byNorm` — an equation by the normal forms of its sides.
* {lit}`proveSeq` — a sequent proved and added to the development.
* {lit}`normalizeThm` — a theorem of the development with its left side normalized, to rewrite
  with.

## Tags

elementary topos, tactic, proof certificate
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Prover

open PartialHorn Sorts
open scoped FinEnum

/-- The index among the axioms of the axiom at position {lit}`k` of the block after the blocks
{lit}`before`. -/
def axIdx (before : List (List Seq)) (k : ℕ) : ℕ := (before.map List.length).sum + k

/-- The blocks before the terminal object's. -/
def beforeTerminal : List (List Seq) := [categoryAxioms]

/-- The blocks before the products'. -/
def beforeProduct : List (List Seq) := beforeTerminal ++ [terminalAxioms]

/-- The blocks before the exponentials'. -/
def beforeExponential : List (List Seq) := beforeProduct ++ [productAxioms, equalizerAxioms,
  initialAxioms, coproductAxioms, coequalizerAxioms]

/-- The blocks before the natural numbers object's. -/
def beforeNat : List (List Seq) := beforeExponential ++ [exponentialAxioms, classifierAxioms]

/-- The blocks before the list objects'. -/
def beforeList : List (List Seq) := beforeNat ++ [natAxioms]

/-- The instance of a source's sequent at terms: its conclusion, with the certificate whose
hypotheses the typing proves. -/
def inst (s : Src) (σ : List Tree) : PM (Eqn × Tree) := do
  let a ← s.seq
  let tys ← σ.mapM typeTerm
  let hs ← a.hyps.mapM (proveHyp typePattern tys)
  pure (a.concl.subst σ, s.cert σ (tys.map Ty.dfd) hs)

/-- The expansion of an arrow into a product by the uniqueness of pairing:
{lit}`f = pair (comp (fst a b) f) (comp (snd a b) f)`, where {lit}`prod a b` is the canonical
codomain of {lit}`f`. -/
def etaExpand (f : Tree) : PM (Tree × Tree) := do
  let ty ← typeTerm f
  match ty.hi.label, ty.hi.children with
  | 7, [a, b] =>
    let (q, c) ← inst (.ax (axIdx beforeProduct 11)) [f, a, b]
    pure (q.lhs, Cert.symm c)
  | _, _ => failure

/-- The rule unfolding the definition at position {lit}`i`: its application rewrites to its
body. -/
def deltaRule (i : ℕ) : RwRule := { src := .ax (defAxIdx i) }

/-- The certificate of an equation whose sides have one normal form under rules. -/
def byNorm (rules : List RwRule) (q : Eqn) : PM Tree := do
  let (l, cl) ← normalize rules q.lhs
  let (r, cr) ← normalize rules q.rhs
  guard (l == r)
  pure (Cert.trans cl (Cert.symm cr))

/-- A sequent proved in its scope by a certificate the prover computes, with definitions in
force, added to the development; the result is its index there. -/
def proveSeq (a : Seq) (m : PM Tree) (defs : List Defn := []) (infer : Bool := false) :
    StateT Development Option ℕ :=
  fun dev ↦ do
    let (c, dev) ← run ⟨a.ctx, a.hyps⟩ dev m defs infer
    pure (dev.length, dev ++ [(a, c)])

/-- The theorem of the development at index {lit}`j` with its left side normalized under rules,
proved in its scope and added to the development; the result is its index there. A rule from
it rewrites where the normal form of the theorem's left side occurs. -/
def normalizeThm (rules : List RwRule) (j : ℕ) (defs : List Defn := []) (infer : Bool := false) :
    StateT Development Option ℕ := fun dev ↦ do
  let (a, _) ← dev[j]?
  let sc : Scope := ⟨a.ctx, a.hyps⟩
  let ((n, cn), dev) ← run sc dev (normalize rules a.concl.lhs) defs infer
  pure (dev.length, dev ++ [(sc.seq ⟨n, a.concl.rhs⟩, Cert.trans (Cert.symm cn) (sc.cite j))])

end Geb.FreeTopos.Prover

end

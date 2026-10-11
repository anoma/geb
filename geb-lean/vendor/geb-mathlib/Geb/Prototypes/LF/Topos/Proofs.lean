/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Topos.Adequacy

set_option doc.verso true in
/-!
# The decoding of the proofs of the representation of the internal language

The canonical LF terms of the families of proofs of {name}`Geb.LF.Topos.sig` decode to
derivations of the internal language ({name}`Geb.FreeTopos.Internal.check`). An LF context of
proofs declares, outermost, variables of {lit}`tp`, the internal language's object variables, and
inside them variables of families of terms of the fragment's types and of families of proofs of
its formulas, in any order; the second are the variables of the internal context, the third its
hypotheses. The decoding of a proof carries an environment that gives, for each LF variable inside
the variables of {lit}`tp`, whether it is a term variable or the index of its hypothesis, and the
number of hypotheses, which grows where the derivation a rule decodes to adds one of its own by a
cut. A type in the context decodes at the offset of the environment's variables.

Each rule of the signature decodes to the derivation of its conclusion from its premises'
decodings. Reflexivity, β, the computations of pairs and of the folds and the η rules decode to
joins of rewritings by the language's rules of the same names; function and propositional
extensionality to the rules of the same names. The substitution of equals decodes to the motive
as a function applied to the right side of the equation, cut as a hypothesis, whose argument the
equation rewrites to the left side, and whose β-reducts are the motive at either side
({lit}`leibD`), and congruence to the substitution of equals into the formula that the function
at the left side is equal to the function at a variable ({lit}`congMotive`), proved at the left
side by reflexivity. The inductions on the natural numbers, on lists and on rose trees, and case
analysis on a coproduct, prove the motive at a term from the equality of the motive and the
function constantly true, proved by function extensionality and induction or case analysis on the
fresh variable ({lit}`indD`); a formula from a term of the initial object is the formula as a
motive at it, proved on a fresh variable of the initial type. A constant past the signature, a
theorem of an extension of it that the indices' table names, decodes to the language's
application of the theorem's entry at its leading arguments' decodings, from its other arguments'
decodings, one the table names as the unfolding of a definition to the unfolding at the
equation's left side and reflexivity at its right, and one the table names as the induction on a
quotient as the inductions do, by the language's induction on the quotient ({lit}`decPfThm`).
No derivation cuts through a formula that substitutes into a motive, so that each formula the
checker types is the decoding of a term or built from such by the language's term formers.

## Main definitions

* {lit}`tmIdx` — the renaming of an LF context's term variables to the internal context's.
* {lit}`congMotive`, {lit}`leibD` — the motive of congruence, and the derivation of the
  substitution of equals.
* {lit}`indD` — the derivation of an induction at a term.
* {lit}`decPf` — the decoding of a proof.

## References

* \[HarperLicata2007\], Section 3.4, for the adequacy of the representation of judgments.

## Tags

logical framework, LF, adequacy, proof, derivation, internal language
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF.Topos

open FreeTopos.Internal (Term Deriv instVar weaken1)

/-- The renaming of an LF context's term variables to the internal context's: an environment
lists, for each LF variable, the innermost first, nothing for a term variable and the index of
its hypothesis for a proof variable; a term variable is renamed to the number of term variables
inside it, and a proof variable, which no term mentions, to zero. -/
def tmIdx : List (Option ℕ) → ℕ → ℕ :=
  List.rec id fun o _ r ↦ match o with
    | none => liftR r
    | some _ => fun i ↦ match i with
      | 0 => 0
      | j + 1 => r j

/-- The number of term variables of an environment. -/
def numTm : List (Option ℕ) → ℕ :=
  List.rec 0 fun o _ r ↦ match o with
    | none => r + 1
    | some _ => r

/-- The decoding of an LF term in an LF context of proofs, whose variables past the environment
are of {lit}`tp`: its term variables renamed to the internal context's, which moves the variables
of {lit}`tp` past the term variables, then decoded at the offset of the term variables. -/
def termOf (k : PrimIdx) (env : List (Option ℕ)) (e : Expr) : Option MTerm :=
  dec k (e.rename (tmIdx env)) (numTm env)

/-- A derivation of a rule and its children. -/
abbrev nd (r : FreeTopos.Internal.Rule) (cs : List Deriv) : Deriv := RoseTree.node r cs

/-- The identity rewriting. -/
abbrev reflD : Deriv := nd .refl []

/-- The proof of an equation by two rewritings to one term. -/
abbrev joinD (d₁ d₂ : Deriv) : Deriv := nd .join [d₁, d₂]

/-- A rewriting by a rule at the root. -/
abbrev ruleD (r : FreeTopos.Internal.Rule) : Deriv := nd r []

/-- The formula true, the equality of the terminal object's element with itself. -/
def truth : Term := Term.eq Term.star Term.star

/-- The derivation of a motive {lit}`pb`, a formula in a variable of the type {lit}`c`, at a term
{lit}`n`, by the induction rule {lit}`r` whose premises are {lit}`Ds`, under
{lit}`m` hypotheses: the motive as a function is cut as equal to the function constantly true, by
function extensionality and propositional extensionality, the converse direction by the
induction on the fresh variable; the motive at {lit}`n` is the β-reduct of the function's
application to {lit}`n`, which that equation rewrites to the true one's. -/
def indD (c : PartialHorn.Tree) (r : FreeTopos.Internal.Rule) (pb n : Term) (m : ℕ)
    (Ds : List Deriv) : Deriv :=
  let L := Term.lam c pb
  let R := Term.lam c truth
  nd (.cut (Term.eq L R))
    [nd .funExt [nd .conv [nd .cong [ruleD .beta, ruleD .beta],
        nd .propExt [joinD reflD reflD, nd r Ds]]],
      nd (.convFrom (Term.app L n))
        [ruleD .beta, nd .conv [nd .cong [ruleD (.rwHyp m false), reflD],
          nd .conv [ruleD .beta, joinD reflD reflD]]]]

/-- The motive of the congruence of a function, its body {lit}`fb` in a variable, at a term
{lit}`a`: the formula in a variable that the function at {lit}`a` is equal to the function at
it. -/
def congMotive (fb a : Term) : Term := Term.eq (weaken1 (Term.subst fb (instVar a))) fb

/-- The derivation of the substitution of equals: the motive {lit}`pb`, a formula in a variable of
the type {lit}`a`, at {lit}`u`, from the proof {lit}`Dh` of {lit}`t = u` and the proof
{lit}`Dp` of the motive at {lit}`t`, under {lit}`m` hypotheses: the equation is cut as a
hypothesis, and the goal is the β-reduct of the motive as a function applied to {lit}`u`, which
the equation rewrites to its application to {lit}`t`, whose β-reduct is the motive at
{lit}`t`. -/
def leibD (a : PartialHorn.Tree) (pb t u : Term) (m : ℕ) (Dh Dp : Deriv) : Deriv :=
  nd (.cut (Term.eq t u)) [Dh, nd (.convFrom (Term.app (Term.lam a pb) u))
    [ruleD .beta, nd .conv [nd .cong [reflD, ruleD (.rwHyp m true)],
      nd .conv [ruleD .beta, Dp]]]]

section Decoding

variable (k : PrimIdx)

/-- The decoding of an application of a constant past the signature to derivations whose nodes
{lit}`mk` forms. At a theorem of the extension, its first arguments, as many as the theorem's
object variables, the outermost first, are types, the next, as many as its variables, terms, and
the rest proofs of the theorem's hypotheses, and the application decodes to the language's
application of the theorem's entry at the types and the terms, the innermost first, with the
proofs' decodings. At the unfolding of a definition, the application decodes to {lit}`dδ`, the
proof of the unfolding's equation. At the induction on a quotient, its first arguments, as many
as the projection's object parameters, the outermost first, are types, and the next the motive,
the proof at the projection's image of a variable and the term, and the application decodes to
the derivation {lit}`ind` of the motive at the term by the language's induction on the quotient,
the quotient's object definition and the projection at the types, the innermost first. -/
def decPfThm {D : Type} (mk : FreeTopos.Internal.Rule → List D → D) (dδ : D)
    (ind : PartialHorn.Tree → FreeTopos.Internal.Rule → Term → Term → ℕ → List D → D) (c : ℕ)
    (cs : List (Expr × (List (Option ℕ) → ℕ → Option D))) (env : List (Option ℕ)) (m : ℕ) :
    Option D :=
  if sig.length ≤ c then match k.ext[c - sig.length]? with
    | some (.thm j n p) => do
      let θ ← (cs.take n).mapM fun x ↦ decTy k env.length x.1
      let σ ← ((cs.drop n).take p).mapM fun x ↦ termOf k env x.1
      let ps ← (cs.drop (n + p)).mapM fun x ↦ x.2 env m
      pure (mk (.apply j θ.reverse σ.reverse) ps)
    | some (.delta _ _ _) => some dδ
    | some (.quotInd kq n op) => match cs.drop n with
      | [(P, _), (_, d), (t, _)] => do
        let θ ← (cs.take n).mapM fun x ↦ decTy k env.length x.1
        let pb ← lamBody (← termOf k env P)
        pure (ind (PartialHorn.op op θ.reverse) (.quotInd kq θ.reverse) pb (← termOf k env t) m
          [← d (none :: env) (m + 1)])
      | _ => none
    | _ => none
  else none

/-- One step of the decoding of a proof at a node of a constant of coproducts or of the initial
object, from its children's decodings, each a function of an environment and the number of
hypotheses: the computations of the case analysis decode to joins of the rewritings of the
language's rules of the same names, and the case analysis and a formula from a term of the
initial object to the derivations of an induction ({lit}`indD`) by the language's case analysis
and its rule of the initial type; a constant past the signature, as {lit}`decPfThm` decodes it. -/
def decPfStepCoprod (c : ℕ) (cs : List (Expr × (List (Option ℕ) → ℕ → Option Deriv)))
    (env : List (Option ℕ)) (m : ℕ) : Option Deriv :=
  match c, cs with
    | 53, [_, _, _, _, _, _] => some (joinD (ruleD (.caseInl k.case k.inl)) reflD)
    | 54, [_, _, _, _, _, _] => some (joinD (ruleD (.caseInr k.case k.inr)) reflD)
    | 55, [(A, _), (B, _), (P, _), (_, d₁), (_, d₂), (c, _)] => do
      let a ← decTy k env.length A
      let b ← decTy k env.length B
      let pb ← lamBody (← termOf k env P)
      pure (indD (FreeTopos.coprod a b) (.coprodInd k.inl k.inr) pb (← termOf k env c) m
        [← d₁ (none :: env) (m + 1), ← d₂ (none :: env) (m + 1)])
    | 56, [(z, _), (φ, _)] => do
      pure (indD FreeTopos.zero (.zeroInd 0) (weaken1 (← termOf k env φ)) (← termOf k env z) m
        [])
    | c, cs => decPfThm k nd (joinD (ruleD .delta) reflD) indD c cs env m

/-- One step of the decoding of a proof, at a node of a label, from its children's decodings,
each a function of an environment and the number of hypotheses. -/
def decPfStep (l : Label) (cs : List (Expr × (List (Option ℕ) → ℕ → Option Deriv)))
    (env : List (Option ℕ)) (m : ℕ) : Option Deriv :=
  match l, cs with
    | .app (.var i), [] => match env[i]? with
      | some (some h) => some (ruleD (.hyp h))
      | _ => none
    | .app (.const 18), [_, _] => some (joinD reflD reflD)
    | .app (.const 19), [(A, _), (P, _), (t, _), (u, _), (_, dh), (_, dp)] => do
      let pb ← lamBody (← termOf k env P)
      pure (leibD (← decTy k env.length A) pb (← termOf k env t) (← termOf k env u) m (← dh env m)
        (← dp env (m + 1)))
    | .app (.const 20), [_, _, _, _] => some (joinD (ruleD .beta) reflD)
    | .app (.const 21), [_, _, _, _] => some (joinD (ruleD .fstPair) reflD)
    | .app (.const 22), [_, _, _, _] => some (joinD (ruleD .sndPair) reflD)
    | .app (.const 23), [_, _, _] => some (joinD (ruleD .pairEta) reflD)
    | .app (.const 24), [_] => some (joinD (ruleD .unitEta) reflD)
    | .app (.const 25), [_, _, _] => some (joinD (ruleD (.natZero k.zero)) reflD)
    | .app (.const 26), [_, _, _, _] => some (joinD (ruleD (.natSucc k.succ)) reflD)
    | .app (.const 27), [_, _, _, _, (_, dH)] => do
      pure (nd .funExt [← dH (none :: env) m])
    | .app (.const 28), [_, _, (_, d₁), (_, d₂)] => do
      pure (nd .propExt [← d₁ (some m :: env) (m + 1), ← d₂ (some m :: env) (m + 1)])
    | .app (.const 29), [(P, _), (_, d₀), (_, ds), (n, _)] => do
      let pb ← lamBody (← termOf k env P)
      pure (indD FreeTopos.nat (.natIndHyp k.zero k.succ) pb (← termOf k env n) m
        [← d₀ env (m + 1), ← ds (some (m + 1) :: none :: env) (m + 2)])
    | .app (.const 34), [_, _, _, _] => some (joinD (ruleD (.listNil k.nil)) reflD)
    | .app (.const 35), [_, _, _, _, _, _] => some (joinD (ruleD (.listCons k.cons)) reflD)
    | .app (.const 36), [(A, _), (P, _), (_, d₀), (_, ds), (l, _)] => do
      let a ← decTy k env.length A
      let pb ← lamBody (← termOf k env P)
      pure (indD (FreeTopos.list a) (.listIndHyp k.nil k.cons) pb (← termOf k env l) m
        [← d₀ env (m + 1), ← ds (some (m + 1) :: none :: none :: env) (m + 2)])
    | .app (.const 40), [_, _, _, _] => some (joinD (ruleD (.roseNode k.node k.nil k.cons)) reflD)
    | .app (.const 41), [(P, _), (_, ds), (t, _)] => do
      let pb ← lamBody (← termOf k env P)
      pure (indD FreeTopos.rose (.roseIndHyp k.node k.nil k.cons) pb (← termOf k env t) m
        [← ds (some (m + 1) :: none :: none :: env) (m + 2)])
    | .app (.const 45), [_, _, _, _, _] =>
      some (joinD (ruleD (.roseNode k.lnode k.nil k.cons)) reflD)
    | .app (.const 46), [(A, _), (P, _), (_, ds), (t, _)] => do
      let a ← decTy k env.length A
      let pb ← lamBody (← termOf k env P)
      pure (indD (FreeTopos.lrose a) (.roseIndHyp k.lnode k.nil k.cons) pb (← termOf k env t) m
        [← ds (some (m + 1) :: none :: none :: env) (m + 2)])
    | .app (.const 47), [(A, _), _, (f, _), (a, _), (b, _), (_, dh)] => do
      let fb ← lamBody (← termOf k env f)
      let sa ← termOf k env a
      pure (leibD (← decTy k env.length A) (congMotive fb sa) sa (← termOf k env b) m (← dh env m)
        (joinD reflD reflD))
    | .app (.const c), cs => decPfStepCoprod k c cs env m
    | .lam, [(_, d)] => d env m
    | _, _ => none

/-- The decoding of a proof in an environment, under a number of hypotheses. -/
def decPf : Expr → List (Option ℕ) → ℕ → Option Deriv := RoseTree.para (decPfStep k)

end Decoding

end Geb.LF.Topos

end

/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Basic

set_option doc.verso true in
/-!
# Elementary-affine decorations of kernel programs

A decoration of a kernel term assigns a number of boxes to every node of the term and a
number of {lit}`!` to every node of the simple types it introduces, in the style of
\[CoppolaMartini2006\]; the decorated term is a derivation of elementary affine logic
when the numbers satisfy linear constraints, so that checking a given decoration is
arithmetic on given numbers and needs no solver. The discipline checked is that of the
search {lit}`scripts/eal/eal.py`, with first-order data, the types without arrows, exempted:
data are contracted and promoted freely. The exemption is not proved sound for a machine of
optimal reduction \[BaillotCoppolaDalLago2011\]; the checker defines the discipline that
the bootstrap's programs are required to satisfy.

A decoration mirrors the term, each node labelled by its depth in boxes, the number of
boxes around it, rather than by the number of boxes on the edge above it, so that every
number is a natural number: a child at a greater depth than its parent enters boxes, and a
child at a smaller depth leaves them through doors. A decorated type mirrors a simple type,
each node also carrying its number of {lit}`!`, which is zero at a type without arrows.

The rules, for a term at depth {lit}`n`:

* a variable, or a place reached from one by projections, at a depth {lit}`p` greater than
  its binder's is seen with {lit}`p` fewer {lit}`!`, and needs at least {lit}`p`; a binder
  whose places are used more than once, or beside a place below them, needs a {lit}`!` at
  that place unless it is data (contraction); projecting a place pushes the place's
  {lit}`!` into its components;
* a child at depth {lit}`m` uses no variable bound deeper than {lit}`m`, and a child of a
  type with arrows leaving boxes keeps at least as many {lit}`!` as it leaves boxes; its
  type gains {lit}`m - n` {lit}`!`;
* there is no dereliction: a function applied, a pair projected other than at a place, a
  list consed onto and a list taken apart by case analysis have no {lit}`!`;
* the branches of a conditional, and of case analysis of lists applied to all three of its
  arguments, are additive: a variable used in both is used as often as in either;
* the constants are typed by their elementary-affine types: iteration at
  {lit}`!(A ⊸ A) ⊸ !A ⊸ T ⊸ !A`, the folds of trees at
  {lit}`!(T ⊸ List A ⊸ A) ⊸ T ⊸ !A`, and the right fold of lists at
  {lit}`!(A' ⊸ B ⊸ B) ⊸ !B ⊸ List A ⊸ !B` with {lit}`A = !A'`;
* a reference to a definition takes a decoration of the definition's term, an instance,
  under any number of boxes, the definition being closed.

A certificate is a list of instances, each a definition with a decoration of its term at
depth zero, an instance referring only to instances before it, so that a definition used at
several decorations has an instance for each.

## Main definitions

* {lit}`DTy` — decorated types.
* {lit}`Sem` — the check of a decorated term in a context.
* {lit}`step` — one node of the check, with the spine of a case analysis of lists.
* {lit}`check` — the check of a certificate against a program.

## Implementation notes

The check is the paramorphism {name}`Geb.RoseTree.para`, as {name}`Geb.Kernel.infer` is,
since a node's rule reads its children as trees: the annotations of types, the indices of
variables, and the places that chains of projections of a variable reach. Each node's result
also records, for an application whose head is case analysis of lists, the arguments
applied so far, so that the application of all three is checked with additive branches.

Equality of simple and decorated types is decided by {name}`WType.instDecidableEq` over the
enumeration of {lit}`Fin n` that the scope {lit}`FinEnum` supplies, which depends on no
axiom of choice, where mathlib's enumeration, selected otherwise, does.

## References

* \[CoppolaMartini2006\]
* \[BaillotCoppolaDalLago2011\]

## Tags

elementary affine logic, decoration, certificate, kernel, optimal reduction
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Affine

open Geb.Kernel
open scoped FinEnum

/-- Whether a simple type has no arrow: a type of first-order data. -/
def IsData : Tree → Bool := RoseTree.elim fun l rs ↦ l != Label.tyArrow && rs.all id

/-- A decorated type: a simple type whose every node also carries its number of {lit}`!`. -/
abbrev DTy : Type := RoseTree (ℕ × ℕ)

namespace DTy

/-- The simple type a decorated type decorates. -/
def ty (d : DTy) : Tree := d.map Prod.fst

/-- The number of {lit}`!` at the root. -/
def bang (d : DTy) : ℕ := d.label.2

/-- Whether the type decorated is data. -/
def data (d : DTy) : Bool := IsData d.ty

/-- A node of a decorated type. -/
def mk (l b : ℕ) (cs : List DTy) : DTy := RoseTree.node (l, b) cs

/-- A simple type with no {lit}`!`. -/
def zero (A : Tree) : DTy := A.map (·, 0)

/-- A function type with no {lit}`!` at its root. -/
def arrow (a b : DTy) : DTy := mk Label.tyArrow 0 [a, b]

/-- A list type with no {lit}`!` at its root. -/
def list (a : DTy) : DTy := mk Label.tyList 0 [a]

/-- The type with its root's number of {lit}`!` replaced, unless the type is data. -/
def withBang (d : DTy) (b : ℕ) : DTy := if d.data then d else mk d.label.1 b d.children

/-- The type under {lit}`e` more {lit}`!`. -/
def shift (d : DTy) (e : ℕ) : DTy := d.withBang (d.bang + e)

/-- The type with one {lit}`!` fewer. -/
def unbox (d : DTy) : DTy := d.withBang (d.bang - 1)

/-- One node of {lit}`decorate`: the node's label, and for each child the decoration of the
child's simple type by a tree of numbers of {lit}`!`. -/
def decorateStep (l : ℕ) (rs : List (Tree → Option DTy)) (b : Tree) : Option DTy := do
  guard (rs.length = b.children.length)
  let cs ← (rs.zip b.children).mapM fun (r, c) ↦ r c
  let data := l != Label.tyArrow && cs.all data
  some (mk l (if data then 0 else b.label) cs)

/-- A simple type decorated by a tree of the same shape whose labels are the numbers of
{lit}`!`, those at data ignored. -/
def decorate (A b : Tree) : Option DTy := RoseTree.elim decorateStep A b

/-- One node of {lit}`contracts`: whether the node's type is data, and, given the path of
the node from the variable and the {lit}`!` the places above it push into it, whether the
occurrences of the places at and below the node are admitted. -/
def contractsStep (paths : List (List ℕ)) (lb : ℕ × ℕ)
    (rs : List (Bool × (List ℕ → ℕ → Bool))) : Bool × (List ℕ → ℕ → Bool) :=
  let data := lb.1 != Label.tyArrow && rs.all (·.1)
  (data, fun p acc ↦
    let e := lb.2 + acc
    let direct := paths.count p
    let below := paths.any fun q ↦ p.length < q.length && p.isPrefixOf q
    data ||
      if 2 ≤ direct || (1 ≤ direct && below) then 1 ≤ e
      else direct != 0 || rs.zipIdx.all fun (r, i) ↦
        !(paths.any ((p ++ [i]).isPrefixOf ·)) || r.2 (p ++ [i]) e)

/-- Whether a variable of this decorated type admits occurrences of its places at these
paths: a place used more than once, or beside a place below it, has a {lit}`!` or is
data. -/
def contracts (paths : List (List ℕ)) (d : DTy) : Bool :=
  (RoseTree.elim (contractsStep paths) d).2 [] 0

/-- The decorated type of a place: each projection pushes the {lit}`!` of the pair into
its component. -/
def place (d : DTy) (path : List ℕ) : Option DTy :=
  path.foldlM (fun d i ↦ d.children[i]?.map fun c ↦ if d.data then c else c.shift d.bang) d

end DTy

open DTy

/-- The places a term reaches, a variable or a chain of projections of one: the variable's
index and the path of components from the variable outward. -/
def place : Tree → Option (ℕ × List ℕ) :=
  RoseTree.para fun l cs ↦
    match l, cs with
    | Label.var, [(n, _)] => some (n.label, [])
    | Label.fst, [(_, r)] => r.map fun (n, p) ↦ (n, p ++ [0])
    | Label.snd, [(_, r)] => r.map fun (n, p) ↦ (n, p ++ [1])
    | _, _ => none

/-- The occurrences of places in a term, each the index of its variable and its path, with
multiplicity. -/
abbrev Usage : Type := List (ℕ × List ℕ)

/-- The occurrences of two additive branches: each place as often as in either. -/
def Usage.max (u v : Usage) : Usage := u ++ v.diff u

/-- A context: each variable's decorated type and the depth of its binder. -/
abbrev Ctx : Type := List (DTy × ℕ)

/-- The instances checked so far: each one's definition and decorated type. -/
abbrev Env : Type := List (ℕ × DTy)

/-- The check of a decorated term: given the instances before it, a context and the term's
decoration, the term's decorated type and the occurrences of places in it, or nothing. The
term's depth is its decoration's label. -/
abbrev Sem : Type := Env → Ctx → Tree → Option (DTy × Usage)

/-- An occurrence of a place at a depth: seen with as many {lit}`!` fewer as the depth
exceeds its binder's, which it must have. -/
def occurrence (Γ : Ctx) (depth : ℕ) (pl : ℕ × List ℕ) : Option (DTy × Usage) := do
  let (d0, bound) ← Γ[pl.1]?
  let d ← d0.place pl.2
  guard (bound ≤ depth)
  if d.data then some (d, [pl])
  else do
    guard (depth - bound ≤ d.bang)
    some (d.withBang (d.bang - (depth - bound)), [pl])

/-- A child at a depth, under its parent at another: it uses no variable bound deeper, and,
unless it is data, it has as many more {lit}`!` as it is deeper, at least as many as it
leaves boxes. -/
def enter (Γ : Ctx) (depth child : ℕ) (r : DTy × Usage) : Option (DTy × Usage) := do
  guard (r.2.all fun pl ↦ Γ[pl.1]?.any fun e ↦ decide (e.2 ≤ child))
  if r.1.data then some r
  else do
    guard (depth ≤ r.1.bang + child)
    some (r.1.withBang (r.1.bang + child - depth), r.2)

/-- Iteration, with the decorated result type: {lit}`!(A ⊸ A) ⊸ !A ⊸ T ⊸ !A`. -/
def iterD (a : DTy) : DTy :=
  arrow (mk Label.tyArrow 1 [a, a]) (arrow (a.shift 1) (arrow (zero tT) (a.shift 1)))

/-- The folds of trees, with the decorated result type: {lit}`!(T ⊸ List A ⊸ A) ⊸ T ⊸ !A`.
-/
def foldD (a : DTy) : DTy :=
  arrow (mk Label.tyArrow 1 [zero tT, arrow (list a) a]) (arrow (zero tT) (a.shift 1))

/-- The right fold of lists, with the decorated element and result types:
{lit}`!(A' ⊸ B ⊸ B) ⊸ !B ⊸ List A ⊸ !B`, where {lit}`A = !A'`. -/
def foldrD (a b : DTy) : DTy :=
  arrow (mk Label.tyArrow 1 [a.unbox, arrow b b])
    (arrow (b.shift 1) (arrow (list a) (b.shift 1)))

/-- Case analysis of lists, with the decorated element and result types. -/
def lcaseD (a b : DTy) : DTy :=
  arrow (list a) (arrow b (arrow (arrow a (arrow (list a) b)) b))

/-- The arguments of an application whose head is case analysis of lists: its element and
result types and the checks of the arguments applied so far. -/
abbrev Spine : Type := Option (Tree × Tree × List Sem)

/-- The spine of a node: case analysis of lists starts one, and an application extends its
function's. -/
def spine : ℕ → List (Tree × Sem × Spine) → Spine
  | Label.lcase, [(A, _), (B, _)] => some (A, B, [])
  | Label.app, [(_, _, some (A, B, ss)), (_, x, _)] => some (A, B, ss ++ [x])
  | _, _ => none

/-- Case analysis of lists applied to a list, the result for the empty list and the
function for a head and a tail: the branches additive, the list and the function not
derelicted. -/
def lcaseSat (A B : Tree) (rl rn rc : DTy × Usage) : Option (DTy × Usage) := do
  guard (rl.1.ty = tList A ∧ rn.1.ty = B ∧ rc.1.ty = tArrow A (tArrow (tList A) B))
  guard (rl.1.data || rl.1.bang = 0)
  let [ca, cr] := rc.1.children | none
  let [crl, crb] := cr.children | none
  guard (rc.1.bang = 0 ∧ DTy.bang cr = 0 ∧ some ca = rl.1.children[0]? ∧ crl = rl.1 ∧
    crb = rn.1)
  some (rn.1, rl.2 ++ Usage.max rn.2 rc.2)

/-- A projection of a term that is not a place: the pair is not derelicted. -/
def project (i : ℕ) (r : DTy × Usage) : Option (DTy × Usage) := do
  guard (r.1.label.1 = Label.tyProd ∧ (r.1.data || r.1.bang = 0))
  let c ← r.1.children[i]?
  some (c, r.2)

/-- An abstraction, from its variable's decorated type and its body's check: the
occurrences of the variable's places admitted by its decorated type, and the variable no
longer among the occurrences. -/
def abstraction (a : DTy) (rb : DTy × Usage) : Option (DTy × Usage) := do
  guard (a.contracts (rb.2.filterMap fun (n, p) ↦ if n = 0 then some p else none))
  some (arrow a rb.1, rb.2.filterMap fun (n, p) ↦ if n = 0 then none else some (n - 1, p))

/-- One node of the check of a decorated term: the node's label, and each child as a tree
with its check and spine. -/
def semStep (l : ℕ) (cs : List (Tree × Sem × Spine)) : Sem := fun E Γ D ↦
  let depth := D.label
  let sub (s : Sem) (d : Tree) : Option (DTy × Usage) := s E Γ d >>= enter Γ depth d.label
  match l, cs, D.children with
  | Label.var, [(n, _)], [] => occurrence Γ depth (n.label, [])
  | Label.fst, [(p, s, _)], ds =>
    match place p, ds with
    | some (n, q), [] => occurrence Γ depth (n, q ++ [0])
    | none, [dp] => sub s dp >>= project 0
    | _, _ => none
  | Label.snd, [(p, s, _)], ds =>
    match place p, ds with
    | some (n, q), [] => occurrence Γ depth (n, q ++ [1])
    | none, [dp] => sub s dp >>= project 1
    | _, _ => none
  | Label.lam, [(A, _), (_, b, _)], [dA, db] => do
    guard (Geb.Kernel.Ty.IsTy A)
    let a ← decorate A dA
    let Γ' := (a, depth) :: Γ
    abstraction a (← b E Γ' db >>= enter Γ' depth db.label)
  | Label.app, [(_, _, some (A, B, [sl, sn])), (_, x, _)], [dl, dn, dc] => do
    lcaseSat A B (← sub sl dl) (← sub sn dn) (← sub x dc)
  | Label.app, [(_, _, some (_, _, [_, _])), _], _ => none
  | Label.app, [(_, f, _), (_, x, _)], [df, dx] => do
    let (rf, uf) ← sub f df
    let (rx, ux) ← sub x dx
    let [a, b] := rf.children | none
    guard (rf.label.1 = Label.tyArrow ∧ rf.bang = 0 ∧ a = rx)
    some (b, uf ++ ux)
  | Label.unit, [], [] => some (zero tUnit, [])
  | Label.quote, [_], [] => some (zero tT, [])
  | Label.pair, [(_, a, _), (_, b, _)], [da, db] => do
    let (ra, ua) ← sub a da
    let (rb, ub) ← sub b db
    some (mk Label.tyProd 0 [ra, rb], ua ++ ub)
  | Label.cond, [(_, c, _), (_, a, _), (_, b, _)], [dc, da, db] => do
    let (rc, uc) ← sub c dc
    let (ra, ua) ← sub a da
    let (rb, ub) ← sub b db
    guard (rc.ty = tT ∧ ra = rb)
    some (ra, uc ++ Usage.max ua ub)
  | Label.nil, [(A, _)], [dA] => do
    guard (Geb.Kernel.Ty.IsTy A)
    some (list (← decorate A dA), [])
  | Label.cons, [(_, x, _), (_, xs, _)], [dx, dl] => do
    let (rx, ux) ← sub x dx
    let (rl, ul) ← sub xs dl
    guard (rl.ty = tList rx.ty ∧ (rl.data || (rl.bang = 0 ∧ rl.children = [rx])))
    some (list rx, ux ++ ul)
  | Label.iter, [(A, _)], [dA] => do
    guard (Geb.Kernel.Ty.IsTy A)
    some (iterD (← decorate A dA), [])
  | Label.fold, [(A, _)], [dA] => do
    guard (Geb.Kernel.Ty.IsTy A)
    some (foldD (← decorate A dA), [])
  | Label.para, [(A, _)], [dA] => do
    guard (Geb.Kernel.Ty.IsTy A)
    some (foldD (← decorate A dA), [])
  | Label.foldr, [(A, _), (B, _)], [dA, dB] => do
    guard (Geb.Kernel.Ty.IsTy A && Geb.Kernel.Ty.IsTy B)
    let a ← decorate A dA
    guard (a.data || 1 ≤ a.bang)
    some (foldrD a (← decorate B dB), [])
  | Label.lcase, [(A, _), (B, _)], [dA, dB] => do
    guard (Geb.Kernel.Ty.IsTy A && Geb.Kernel.Ty.IsTy B)
    some (lcaseD (← decorate A dA) (← decorate B dB), [])
  | Label.prim, [(k, _)], [] => Geb.Kernel.prims[k.label]?.map fun g ↦ (zero g.1, [])
  | Label.ref, [(n, _)], [di, dk] => do
    let (i, d) ← E[di.label]?
    guard (i = n.label ∧ di.children = [] ∧ dk.children = [])
    some (d.shift dk.label, [])
  | _, _, _ => none

/-- One node of the check: the check of the decorated node and its spine. -/
def step (l : ℕ) (cs : List (Tree × Sem × Spine)) : Sem × Spine :=
  (semStep l cs, spine l cs)

/-- The check of a decorated term. -/
def sem (t : Tree) : Sem := (RoseTree.para step t).1

/-- The check of an instance after the instances before it: the definition's term at depth
zero in the empty context. -/
def instance? (prog : List Tree) (E : Env) (inst : Tree) : Option Env := do
  let body ← prog[inst.label]?
  let [D] := inst.children | none
  guard (D.label = 0)
  let (d, _) ← sem body E [] D
  some (E ++ [(inst.label, d)])

/-- The check of a certificate against a program, its definitions' terms in order: the
instances' definitions and decorated types, or nothing when an instance does not check. -/
def check (prog : List Tree) (cert : Tree) : Option Env :=
  cert.children.foldlM (instance? prog) []

end Geb.Affine

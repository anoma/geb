/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.FinEnum
public import Geb.Mathlib.Data.PFunctor.Slice.W
public import Geb.Mathlib.Data.PFunctor.Slice.Decidable
public import Geb.Mathlib.Data.PFunctor.Univariate.Finitary
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Cobham's class of bitstring functions

The syntax of a Cobham-style function algebra on bitstrings, whose recursion scheme
is bounded recursion on notation [Cobham1965], together with its interpretation over
every `sig`-tree. Terms are built from a constant zero, projections, two successors,
a smash and a concat generator, and are closed under a composition and a bounded
recursion. [HeraudNowak2011]'s grammar for `C` (`O | Πⁱₙ | S_b | # | Compⁿ | Rec`) has
no concatenation generator; the `concat` generator here is added, grounded in
[Strahm2003]'s operator list `[ε, I, s₀, s₁, ∗; COMP, BRN]`, and is what makes the
smash-free bound `SmashFree` names expressible at all. `sig` fixes the shape of the
syntax alone — each constructor's arity and the arity relation its subterms must
satisfy — and `eval` gives the meaning of any tree respecting that relation. Cobham's
class itself is the subtype `C` of trees whose recursions additionally respect the
length bound the scheme imposes, carrying `eval` down to `C.eval`.

A bitstring is `List Bool`, its head the word's last bit. `succ b` — `S_b` in
[HeraudNowak2011]'s notation, `s₀`/`s₁` in [Strahm2003]'s — prepends by consing `b`.
`boundedRec`'s recursion `evalRec` — [HeraudNowak2011]'s `Rec` — peels that head at
each step, passing the remaining bitstring on as the new recursion variable. `concat`
— `∗` in [Strahm2003]'s list — reads its second argument as the earlier part of the
word and its first as the later part, `fun x ↦ x 1 ++ x 0`, consistent with the same
convention.

`SmashFree` names the subalgebra `[ε, I, s₀, s₁, ∗; COMP, BRN]`, which [Strahm2003]
Theorem 1(2) contains in the functions computable simultaneously in polynomial time
and linear space, a characterization [Strahm2003] attributes to [Thompson1972] and
[Strahm2010] Theorem 5 restates. [Clote1999] Theorem 3.20 gives an arithmetic
analogue over the naturals. Linear space alone is the second Grzegorczyk class
[Ritchie1963] (via [Clote1999] Theorem 3.36 and its Corollary 3.37), the class
Bellantoni's safe recursion also characterizes [Bellantoni1992] (via [Clote1999]
Theorem 3.101).

## Main definitions

* `Cobham.Shape` — the seven constructor forms, with their arities as parameters.
* `Cobham.Direction` — the subterm positions of a shape.
* `Cobham.rc` — the arity each subterm position must carry.
* `Cobham.q` — the arity a shape produces.
* `Cobham.sig` — the signature, as a slice polynomial functor over `ℕ`.
* `Cobham.sigFinitary` — every shape has finitely many directions.
* `Cobham.Sem` — the meaning of an arity: a function of an environment of bitstrings.
* `Cobham.transport` — transport of a meaning along an equality of arities.
* `Cobham.evalRec` — the recursion `boundedRec` performs on its recursion variable.
* `Cobham.evalValue` — the meaning of one node from its children's meanings.
* `Cobham.evalStep` — `evalValue` as a slice algebra.
* `Cobham.eval` — the interpretation of a `sig`-tree, by the slice W-type's
  eliminator.
* `Cobham.arity` — the arity of a `sig`-tree.
* `Cobham.semAt` — the meaning of a tree at a given arity.
* `Cobham.RecBoundedValue` — the length bound one node imposes.
* `Cobham.RecBounded` — `RecBoundedValue` at every node, hereditarily.
* `Cobham.C` — Cobham's class: the trees satisfying `RecBounded`.
* `Cobham.C.arity` — the arity of an expression.
* `Cobham.COf` — the expressions of a given arity.
* `Cobham.C.eval` — the meaning of an expression, at its own arity.
* `Cobham.zeroAt`, `Cobham.zeroAtOf` — the empty bitstring at an arbitrary
  arity.
* `Cobham.concatRaw` / `Cobham.smashRaw` — the two generators as single nodes.
* `Cobham.concatOf` / `Cobham.smashOf` — those nodes as expressions of arity two.
* `Cobham.predRaw` / `Cobham.pred` — the predecessor, as a raw tree and as an
  expression of arity one.
* `Cobham.predSem` — the meaning of the predecessor.
* `Cobham.predIter`, `Cobham.predIterOf` — the iterated predecessor.
* `Cobham.prepend`, `Cobham.prependOf` — a fixed word prepended to an
  expression.
* `Cobham.constAt`, `Cobham.constAtOf` — the constant word at a given arity.
* `Cobham.diag`, `Cobham.diagOf` — a binary expression at its sole argument in
  both positions.
* `Cobham.concatCompRaw` — the concatenation of two raw trees of a common arity.
* `Cobham.condRaw` / `Cobham.cond` — the four-way conditional, as a raw tree and as
  an expression of arity four.
* `Cobham.condSem` — the meaning of the conditional.
* `Cobham.smashFreeBool` — whether no `smash` node occurs anywhere in a raw tree.
* `Cobham.SmashFree` — the subalgebra `[ε, I, s₀, s₁, ∗; COMP, BRN]`, excluding
  the `smash` generator.

## Main statements

* `Cobham.transport_transport` — transport along a composite equality is
  the composition of two transports.
* `Cobham.fst_eval` — the index component of a tree's interpretation is its arity.
* `Cobham.recBounded_mk` — `RecBounded` unfolded one level, on a raw node.
* `Cobham.predSem_eq` — the predecessor drops the word's last bit.
* `Cobham.wIndexRoot_predIterRaw`, `Cobham.wValid_predIterRaw`,
  `Cobham.recBounded_predIterRaw` — the iterated predecessor's arity,
  admissibility and recursion bound.
* `Cobham.wIndexRoot_prependRaw`, `Cobham.wValid_prependRaw`,
  `Cobham.recBounded_prependRaw` — prepending preserves the arity,
  admissibility and the recursion bound.
* `Cobham.wIndexRoot_diagRaw`, `Cobham.wValid_diagRaw`,
  `Cobham.recBounded_diagRaw` — the diagonal's arity, admissibility and
  recursion bound.
* `Cobham.condSem_eq` — the conditional branches on the emptiness and parity of its
  first argument.

## Implementation notes

Every `def` in this module is `@[expose]`, so a wrapper module and the tests can
unfold them across the module boundary; the `sigFinitary` instance, the
`Decidable (SmashFree ·)` instance, and the theorems need no such tag.

`concatRaw` and `smashRaw` are named apart from the expressions built on them
because instance search finds `Decidable (sig.WValid w)` when `w` is a constant but
not when it is a literal `WType.mk` application, with or without an ascription, so
`decide` discharges admissibility only of a named tree.

`Direction`, `rc` and `q` are `@[reducible]`. Instance search does not delta-reduce a
semireducible definition, and `sigFinitary` resolves `FinEnum (sig.B a)` against the
literal `Direction a` each branch produces.

`sigFinitary`'s `comp` branch resolves `FinEnum (Unit ⊕ Fin m)` through the
choice-free `FinEnum.unit` and `FinEnum.finSum`, and its other branches resolve
`FinEnum (Fin n)` through the choice-free `FinEnum.finFin`. Those instances are
`scoped` in `namespace FinEnum`; this module's `open scoped FinEnum` is required for
them to win resolution over mathlib's `Classical.choice`-dependent counterparts,
which `lake lint` rejects.

`evalValue` is a separate definition from `evalStep` because the match on `Shape`
must generalize the compatibility hypothesis, which arrives bundled in
`SliceDomPFunctor.Obj`. A child's meaning carries the index it was built at rather
than the index `rc` prescribes, equal but not definitionally so; `transport` carries
it across, with the motive of `▸` fixed once instead of at each use site.
`evalValue`'s `boundedRec` clause does not consult its bound child's meaning: the
bound is a side condition on admissibility, imposed by `RecBoundedValue`, not part
of a tree's value.

`eval` is a slice morphism, so the index it returns agrees with `arity` only by
`SlicePFunctor.W.comp_elim`, a `funext` theorem; `C.eval` is therefore
`transport (fst_eval _) (eval _).2` rather than the second projection alone, and the
index equation `RecBoundedValue` consumes is the node's compatibility composed with
`fst_eval`. `recBounded_mk` is stated on the raw `⟨WType.mk a f, _⟩` rather than on
`SlicePFunctor.W.mk`, at which the `WType.rec` of `RecProp` iota-reduces and the
unfolding is definitional; the index equation is a hypothesis, definitional proof
irrelevance making the choice of proof term immaterial. `C.arity` and `C.eval`
qualify `arity` and `eval` because the namespace of the declaration being elaborated
is in scope, which would otherwise make each body self-referential.

`zeroAtRaw` carries a free arity, at which `decide` does not apply; its
admissibility is the pair of an `Unit ⊕ Fin m` case analysis and the `funext`
the index condition asks for.

## References

* [Bellantoni1992]
* [Clote1999]
* [Cobham1965]
* [HeraudNowak2011]
* [Ritchie1963]
* [Strahm2003]
* [Strahm2010]
* [Thompson1972]

## Tags

Cobham, bounded recursion on notation, linear space, W-type, polynomial functor
-/

namespace Cobham

open scoped FinEnum

public section

/-- The seven constructor forms of Cobham's class, each carrying its arities as
parameters: `zero` the constant empty bitstring; `proj n i` the `i`th of `n`
variables; `succ b` the successor appending the bit `b`; `smash` and `concat` the two
bitstring generators; `comp n m` the composition of an `m`-ary expression with `m`
`n`-ary argument expressions; `boundedRec n` the bounded recursion producing arity
`n + 1`. -/
inductive Shape
  | zero
  | proj (n : ℕ) (i : Fin n)
  | succ (b : Bool)
  | smash
  | concat
  | comp (n m : ℕ)
  | boundedRec (n : ℕ)

/-- The subterm positions of a shape. The five base forms — `zero`, `proj`, `succ`,
`smash` and `concat` — have none, `smash` and `concat` being generators rather than
recursive constructions; `comp` has its head and its `m` argument expressions;
`boundedRec` has four, its base, its two step expressions and its bound. -/
@[expose, reducible] def Direction : Shape → Type
  | .zero => Fin 0
  | .proj _ _ => Fin 0
  | .succ _ => Fin 0
  | .smash => Fin 0
  | .concat => Fin 0
  | .comp _ m => Unit ⊕ Fin m
  | .boundedRec _ => Fin 4

/-- The arity each subterm position must carry: the hypotheses of the arity relation
of bounded recursion on notation [Cobham1965]. -/
@[expose, reducible] def rc : (a : Shape) → Direction a → ℕ
  | .zero, i => i.elim0
  | .proj _ _, i => i.elim0
  | .succ _, i => i.elim0
  | .smash, i => i.elim0
  | .concat, i => i.elim0
  | .comp _ m, .inl () => m
  | .comp n _, .inr _ => n
  | .boundedRec n, ⟨0, _⟩ => n
  | .boundedRec n, ⟨1, _⟩ => n + 2
  | .boundedRec n, ⟨2, _⟩ => n + 2
  | .boundedRec n, _ => n + 1

/-- The arity a shape produces: the conclusions of the arity relation of bounded
recursion on notation [Cobham1965]. -/
@[expose, reducible] def q : Shape → ℕ
  | .zero => 0
  | .proj n _ => n
  | .succ _ => 1
  | .smash => 2
  | .concat => 2
  | .comp n _ => n
  | .boundedRec n => n + 1

/-- The signature of Cobham's class as a slice polynomial functor over `ℕ`, the index
being the arity. -/
@[expose] def sig : SlicePFunctor ℕ ℕ where
  A := Shape
  B := Direction
  r := fun x ↦ rc x.1 x.2
  q := q

/-- Every shape has finitely many directions, which is what makes admissibility of a
`sig`-tree decidable. The branches ascribe their instances explicitly: instance
search stops at reducible transparency on the projection `sig.B a`, so a bare
`inferInstance` does not find them. -/
instance sigFinitary : sig.toPFunctor.Finitary
  | .zero => inferInstanceAs (FinEnum (Fin 0))
  | .proj _ _ => inferInstanceAs (FinEnum (Fin 0))
  | .succ _ => inferInstanceAs (FinEnum (Fin 0))
  | .smash => inferInstanceAs (FinEnum (Fin 0))
  | .concat => inferInstanceAs (FinEnum (Fin 0))
  | .comp _ m => inferInstanceAs (FinEnum (Unit ⊕ Fin m))
  | .boundedRec _ => inferInstanceAs (FinEnum (Fin 4))

/-- The meaning of an arity: a function of an environment of bitstrings, one per
argument, returning a bitstring. -/
@[expose] def Sem : ℕ → Type := fun n ↦ (Fin n → List Bool) → List Bool

/-- Transport of a meaning along an equality of arities. Named so that the motive of
`▸` is fixed once rather than inferred at each use in `evalValue`. -/
@[expose] def transport {i j : ℕ} (h : i = j) (v : Sem i) : Sem j := h ▸ v

/-- Transport composes. A transport along a composite equality and the
composition of two transports agree, which is not definitional when
neither index reduces: at a variable expression the arity equation is
opaque, so neither `Eq.rec` fires. Named for its left-hand side, as
core's `cast_cast` is. -/
theorem transport_transport {i j k : ℕ} (h : i = j) (g : j = k) (v : Sem i) :
    transport g (transport h v) = transport (h.trans g) v := by
  subst h
  subst g
  rfl

/-- The recursion `boundedRec` performs on its recursion variable, by `List.rec`,
matching [HeraudNowak2011]'s `Rec` (`f(y·i, x) = h_i(y, f(y,x), x)`), not
[Strahm2003]'s last-argument form. The base case is the empty bitstring; a step
consumes the low bit `b`, passes the remaining bitstring `v` as the new recursion
variable, and passes the recursive value alongside it. -/
@[expose] def evalRec {n : ℕ} (g : Sem n) (h₀ h₁ : Sem (n + 2)) :
    List Bool → Sem n :=
  List.rec g (fun b v ih x ↦
    (if b then h₁ else h₀) (Fin.cons v (Fin.cons (ih x) x)))

/-- The meaning of one node, from its children's meanings and the proof that each
child's index is the one `rc` prescribes. A separate definition from `evalStep`
because the match on `Shape` must generalize that proof.

The bitstring generators read the ambient environment directly, `Direction` being
`Fin 0` for each: `zero` returns the empty bitstring; `proj n i` returns the `i`th
argument; `succ b` prepends `b` to the argument. `smash` and `concat` are Cobham's
two generators: `smash` marks its result with a leading `true`, so
`|#(a, b)| = |a| · |b| + 1`; `concat` reads its second argument as the earlier part
of the word and its first as the later part, consistent with the list head
representing the word's last bit. `comp` applies its head's meaning to the argument
expressions' meanings, each read at the ambient environment. `boundedRec` performs
`evalRec` on its recursion variable, its base and two step children supplying `g`,
`h₀` and `h₁`. -/
@[expose] def evalValue : (a : Shape) → (c : Direction a → Σ i, Sem i) →
    (∀ b, (c b).1 = rc a b) → Sem (q a)
  | .zero, _, _ => fun _ ↦ []
  | .proj _ i, _, _ => fun x ↦ x i
  | .succ b, _, _ => fun x ↦ b :: x 0
  | .smash, _, _ => fun x ↦ true :: List.replicate ((x 0).length * (x 1).length) false
  | .concat, _, _ => fun x ↦ x 1 ++ x 0
  | .comp _ _, c, h => fun x ↦
      transport (h (.inl ())) (c (.inl ())).2
        (fun i ↦ transport (h (.inr i)) (c (.inr i)).2 x)
  | .boundedRec _, c, h => fun x ↦
      evalRec (transport (h 0) (c 0).2) (transport (h 1) (c 1).2)
        (transport (h 2) (c 2).2) (x 0) (Fin.tail x)

/-- `evalValue` as an algebra for `sig` in the slice over `ℕ`. Returning the shape's
own output index as the first component makes the eliminator's coherence obligation
hold by `rfl`. -/
@[expose] def evalStep :
    sig.toSliceDomPFunctor.Obj (Sigma.fst (β := Sem)) → Σ i, Sem i :=
  fun z ↦ ⟨sig.q z.val.1,
    evalValue z.val.1 z.val.2
      ((sig.toSliceDomPFunctor.compatible_iff _ z.val.1 z.val.2).mp z.property)⟩

/-- The interpretation of a `sig`-tree: its arity together with its meaning at that
arity, by the slice W-type's eliminator. -/
@[expose] def eval : sig.W → Σ n, Sem n :=
  SlicePFunctor.W.elim sig (Σ n, Sem n) (Sigma.fst (β := Sem)) evalStep rfl

/-- The arity of a `sig`-tree. -/
@[expose] def arity : sig.W → ℕ := sig.wIndex

/-- The index component of a tree's interpretation is the tree's arity. `eval` is a
morphism in the slice over `ℕ`, so composing it with the index projection gives
`sig.wIndex`; this is that equation read at a single tree, the form `transport`
consumes. -/
theorem fst_eval (z : sig.W) : (eval z).1 = arity z :=
  congrFun (SlicePFunctor.W.comp_elim sig (Σ n, Sem n) (Sigma.fst (β := Sem)) evalStep rfl) z

/-- The meaning of a tree at a given arity. -/
@[expose] def semAt (n : ℕ) (e : sig.W) (he : arity e = n) : Sem n :=
  transport ((fst_eval e).trans he) (eval e).2

/-- The recursion bound of one node, from its children and the proof that each
child's evaluated index is the one `rc` prescribes. It is vacuous at every shape but
`boundedRec`, where it is the side condition of bounded recursion on notation
[Cobham1965]: at every environment, the recursion's value is no longer than the
meaning of the bound child. `evalValue`'s `boundedRec` clause supplies the bounded
quantity, read at the same environment. -/
@[expose] def RecBoundedValue : (a : Shape) → (c : Direction a → sig.W) →
    (∀ b, (eval (c b)).1 = rc a b) → Prop
  | .zero, _, _ => True
  | .proj _ _, _, _ => True
  | .succ _, _, _ => True
  | .smash, _, _ => True
  | .concat, _, _ => True
  | .comp _ _, _, _ => True
  | .boundedRec n, c, h => ∀ x : Fin (n + 1) → List Bool,
      (evalRec (transport (h 0) (eval (c 0)).2) (transport (h 1) (eval (c 1)).2)
          (transport (h 2) (eval (c 2)).2) (x 0) (Fin.tail x)).length ≤
        (transport (h 3) (eval (c 3)).2 x).length

/-- The admissibility of a `sig`-tree: every node satisfies `RecBoundedValue`,
hereditarily. The fold over the tree is carried by the slice W-type's `Prop`-valued
paramorphism `SlicePFunctor.W.RecProp`; the index equation `RecBoundedValue` requires
is the node's compatibility (`SliceDomPFunctor.compatible_iff`) composed with
`fst_eval`, since compatibility constrains a child's `wIndex` rather than the index
its interpretation carries. -/
@[expose] def RecBounded : sig.W → Prop :=
  SlicePFunctor.W.RecProp (fun x ih ↦
    RecBoundedValue x.val.1 x.val.2
        (fun b ↦ (fst_eval (x.val.2 b)).trans
          ((sig.toSliceDomPFunctor.compatible_iff _ x.val.1 x.val.2).mp x.property b)) ∧
      ∀ b, ih b)

/-- One-level unfolding of `RecBounded` on a raw node `⟨WType.mk a f, hv⟩`: the
root's `RecBoundedValue` together with admissibility of every child. Stated on the
raw tree rather than on `SlicePFunctor.W.mk`, so that `WType.rec` iota-reduces and
the equation is definitional. -/
theorem recBounded_mk (a : Shape) (f : Direction a → sig.toPFunctor.W)
    (hv : sig.WValid (WType.mk a f))
    (h : ∀ b, (eval ⟨f b, ((sig.wValid_mk a f).mp hv).1 b⟩).1 = rc a b) :
    RecBounded ⟨WType.mk a f, hv⟩ =
      (RecBoundedValue a (fun b ↦ ⟨f b, ((sig.wValid_mk a f).mp hv).1 b⟩) h ∧
        ∀ b, RecBounded ⟨f b, ((sig.wValid_mk a f).mp hv).1 b⟩) :=
  rfl

/-- Cobham's class as a type of expressions: the `sig`-trees whose recursions
respect the length bound. -/
@[expose] def C : Type := { e : sig.W // RecBounded e }

/-- The arity of an expression, that of the underlying tree. -/
@[expose] def C.arity (e : C) : ℕ := Cobham.arity e.val

/-- The expressions of a given arity. -/
@[expose] def COf (n : ℕ) : Type := { e : C // e.arity = n }

/-- The meaning of an expression, at its own arity. The underlying tree's
interpretation carries the index `eval` computed, equal to the arity by `fst_eval`
but not definitionally so, hence the `transport`. -/
@[expose] def C.eval (e : C) : Sem e.arity :=
  transport (fst_eval e.val) (Cobham.eval e.val).2

/-- The empty bitstring at an arbitrary arity. -/
@[expose] def zeroAtRaw (n : ℕ) : sig.toPFunctor.W :=
  WType.mk (.comp n 0) fun d ↦
    match d with
    | .inl () => WType.mk .zero Fin.elim0
    | .inr i => i.elim0

/-- The empty bitstring as an expression of arity `n`. -/
@[expose] def zeroAt (n : ℕ) : C :=
  ⟨⟨zeroAtRaw n,
      ⟨fun d ↦ match d with
        | .inl () => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
        | .inr i => i.elim0,
      funext fun d ↦ match d with
        | .inl () => rfl
        | .inr i => i.elim0⟩⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr i => i.elim0⟩⟩

/-- `zeroAt n` at its declared arity. -/
@[expose] def zeroAtOf (n : ℕ) : COf n := ⟨zeroAt n, rfl⟩

/-- The `concat` generator as a single node, its `Direction` being empty. -/
@[expose] def concatRaw : sig.toPFunctor.W := WType.mk .concat Fin.elim0

/-- The `concat` generator as an expression of arity two, its `RecBoundedValue`
vacuous and its hereditary conjunct empty. -/
@[expose] def concatOf : COf 2 :=
  ⟨⟨⟨concatRaw, by decide⟩, ⟨trivial, fun b ↦ b.elim0⟩⟩, rfl⟩

/-- The `smash` generator as a single node, its `Direction` being empty. -/
@[expose] def smashRaw : sig.toPFunctor.W := WType.mk .smash Fin.elim0

/-- The `smash` generator as an expression of arity two, as `concatOf`. -/
@[expose] def smashOf : COf 2 :=
  ⟨⟨⟨smashRaw, by decide⟩, ⟨trivial, fun b ↦ b.elim0⟩⟩, rfl⟩

/-- The predecessor as a single `boundedRec` node, transcribing
[HeraudNowak2011] § 4's `Rec O Π⁰₂ Π⁰₂ Π⁰₁`: base the constant empty bitstring,
both steps the first of their two arguments, bound the sole argument. In an
`evalRec` step environment the first slot holds the bitstring remaining after the
last bit is peeled, so both steps return that remainder. -/
@[expose] def predRaw : sig.toPFunctor.W :=
  WType.mk (.boundedRec 0)
    ![WType.mk .zero Fin.elim0, WType.mk (.proj 2 0) Fin.elim0,
      WType.mk (.proj 2 0) Fin.elim0, WType.mk (.proj 1 0) Fin.elim0]

/-- The predecessor as an expression of arity one. Its recursion respects the bound
because its value at `y` is `y` with its last bit dropped, of length `|y| - 1`, while
the bound child returns `y`; at the empty bitstring the value is empty. -/
@[expose] def pred : COf 1 :=
  ⟨⟨⟨predRaw, by decide⟩, by
      refine ⟨fun x ↦ ?_, ?_⟩
      · change _ ≤ (x 0).length
        refine List.rec ?_ (fun b _ _ ↦ ?_) (x 0)
        · exact Nat.le_refl 0
        · cases b <;> exact Nat.le_succ _
      · refine fun b : Fin 4 ↦ ?_
        match b with
        | 0 | 1 | 2 | 3 => exact ⟨trivial, fun d ↦ d.elim0⟩⟩, rfl⟩

/-- The meaning of the predecessor, at arity one. -/
@[expose] def predSem : Sem 1 := transport pred.property pred.val.eval

/-- The predecessor drops the word's last bit, which is the Lean list's head. -/
theorem predSem_eq (u : List Bool) : predSem ![u] = u.tail := by
  match u with
  | [] => rfl
  | b :: _ => cases b <;> rfl

/-- The `k`-fold predecessor of the sole argument. -/
@[expose] def predIterRaw : ℕ → sig.toPFunctor.W :=
  Nat.rec (WType.mk (.proj 1 0) Fin.elim0)
    fun _ ih ↦
      WType.mk (.comp 1 1) fun d ↦
        match d with
        | .inl () => predRaw
        | .inr _ => ih

/-- The iterated predecessor has arity one, at every iterate. -/
theorem wIndexRoot_predIterRaw (k : ℕ) : sig.wIndexRoot (predIterRaw k) = 1 := by
  cases k with
  | zero => rfl
  | succ _ => rfl

/-- The iterated predecessor is admissible, at every iterate. -/
theorem wValid_predIterRaw (k : ℕ) : sig.WValid (predIterRaw k) :=
  Nat.rec ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
    (fun j ih ↦
      ⟨fun d ↦ match d with
        | .inl () => pred.val.val.property
        | .inr _ => ih,
      funext fun d ↦ match d with
        | .inl () =>
          (sig.wIndexValid_index_eq_wIndexRoot predRaw).trans pred.property
        | .inr _ =>
          (sig.wIndexValid_index_eq_wIndexRoot (predIterRaw j)).trans
            (wIndexRoot_predIterRaw j)⟩)
    k

/-- The iterated predecessor carries the predecessor's recursions and no
other. -/
theorem recBounded_predIterRaw (k : ℕ) :
    RecBounded ⟨predIterRaw k, wValid_predIterRaw k⟩ :=
  Nat.rec ⟨trivial, fun c ↦ c.elim0⟩
    (fun _ ih ↦ ⟨trivial, fun d ↦ match d with
      | .inl () => pred.val.property
      | .inr _ => ih⟩)
    k

/-- The iterated predecessor as an expression. -/
@[expose] def predIter (k : ℕ) : C :=
  ⟨⟨predIterRaw k, wValid_predIterRaw k⟩, recBounded_predIterRaw k⟩

/-- `predIter` at its declared arity. -/
@[expose] def predIterOf (k : ℕ) : COf 1 :=
  ⟨predIter k, wIndexRoot_predIterRaw k⟩

/-- A fixed word prepended to what an expression of arity `n` computes. -/
@[expose] def prependRaw (n : ℕ) (u : List Bool) (e : sig.toPFunctor.W) :
    sig.toPFunctor.W :=
  List.rec e (fun b _ ih ↦
    WType.mk (.comp n 1) fun d ↦
      match d with
      | .inl () => WType.mk (.succ b) Fin.elim0
      | .inr _ => ih) u

/-- Prepending preserves the arity. -/
theorem wIndexRoot_prependRaw (n : ℕ) (u : List Bool) (e : sig.toPFunctor.W)
    (he : sig.wIndexRoot e = n) : sig.wIndexRoot (prependRaw n u e) = n := by
  cases u with
  | nil => exact he
  | cons _ _ => rfl

/-- Prepending preserves admissibility. -/
theorem wValid_prependRaw (n : ℕ) (e : sig.toPFunctor.W) (hv : sig.WValid e)
    (he : sig.wIndexRoot e = n) :
    ∀ u : List Bool, sig.WValid (prependRaw n u e) :=
  List.rec hv (fun _ v ih ↦
    ⟨fun d ↦ match d with
      | .inl () => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
      | .inr _ => ih,
    funext fun d ↦ match d with
      | .inl () => rfl
      | .inr _ =>
        (sig.wIndexValid_index_eq_wIndexRoot (prependRaw n v e)).trans
          (wIndexRoot_prependRaw n v e he)⟩)

/-- Prepending introduces no recursion of its own. -/
theorem recBounded_prependRaw (n : ℕ) (e : sig.toPFunctor.W)
    (hv : sig.WValid e) (he : sig.wIndexRoot e = n) (hr : RecBounded ⟨e, hv⟩) :
    ∀ u : List Bool,
      RecBounded ⟨prependRaw n u e, wValid_prependRaw n e hv he u⟩ :=
  List.rec hr (fun _ _ ih ↦
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr _ => ih⟩)

/-- A fixed word prepended to an expression. -/
@[expose] def prepend {n : ℕ} (u : List Bool) (e : COf n) : C :=
  ⟨⟨prependRaw n u e.val.val.val, wValid_prependRaw n _ e.val.val.property e.property u⟩,
    recBounded_prependRaw n _ e.val.val.property e.property e.val.property u⟩

/-- `prepend` at its declared arity. -/
@[expose] def prependOf {n : ℕ} (u : List Bool) (e : COf n) : COf n :=
  ⟨prepend u e, wIndexRoot_prependRaw n u e.val.val.val e.property⟩

/-- The constant word at a given arity. -/
@[expose] def constAt (n : ℕ) (u : List Bool) : C := prepend u (zeroAtOf n)

/-- `constAt` at its declared arity. -/
@[expose] def constAtOf (n : ℕ) (u : List Bool) : COf n :=
  ⟨constAt n u, wIndexRoot_prependRaw n u _ (zeroAtOf n).property⟩

/-- A binary expression applied to its sole argument in both positions. -/
@[expose] def diagRaw (e : sig.toPFunctor.W) : sig.toPFunctor.W :=
  WType.mk (.comp 1 2) fun d ↦
    match d with
    | .inl () => e
    | .inr _ => WType.mk (.proj 1 0) Fin.elim0

/-- The diagonal has arity one, whatever it diagonalises. -/
theorem wIndexRoot_diagRaw (e : sig.toPFunctor.W) :
    sig.wIndexRoot (diagRaw e) = 1 := rfl

/-- The diagonal is admissible when what it diagonalises is, at arity two. -/
theorem wValid_diagRaw (e : sig.toPFunctor.W) (hv : sig.WValid e)
    (he : sig.wIndexRoot e = 2) : sig.WValid (diagRaw e) :=
  ⟨fun d ↦ match d with
    | .inl () => hv
    | .inr _ => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩,
  funext fun d ↦ match d with
    | .inl () => (sig.wIndexValid_index_eq_wIndexRoot e).trans he
    | .inr _ => rfl⟩

/-- The diagonal introduces no recursion of its own. -/
theorem recBounded_diagRaw (e : sig.W) (he : arity e = 2)
    (hr : RecBounded e) :
    RecBounded ⟨diagRaw e.val, wValid_diagRaw e.val e.property he⟩ :=
  ⟨trivial, fun d ↦ match d with
    | .inl () => hr
    | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩

/-- The diagonal as an expression. -/
@[expose] def diag (e : COf 2) : C :=
  ⟨⟨diagRaw e.val.val.val, wValid_diagRaw e.val.val.val e.val.val.property e.property⟩,
    recBounded_diagRaw e.val.val e.property e.val.property⟩

/-- `diag` at its declared arity. -/
@[expose] def diagOf (e : COf 2) : COf 1 := ⟨diag e, wIndexRoot_diagRaw _⟩

/-- The concatenation of two `n`-ary raw trees: a `comp` node of arity `n` whose
head is the `concat` generator, applied to `a` and `b` in that order. Its value at
any environment is `b`'s list followed by `a`'s, of length the sum of the two. -/
@[expose] def concatCompRaw (n : ℕ) (a b : sig.toPFunctor.W) : sig.toPFunctor.W :=
  WType.mk (.comp n 2) fun d ↦
    match d with
    | .inl () => concatRaw
    | .inr i => ![a, b] i

/-- The four-way conditional as a single `boundedRec` node, transcribing
[HeraudNowak2011] § 4's `Rec Π⁰₃ Π⁴₅ Π³₅ j` in its base and step children. `Rec`
peels the word's last bit, so `Π⁴₅` is the step taken on a last bit `0` and `Π³₅`
the step taken on a last bit `1`; the base is taken on the empty word.

The bound child departs from [HeraudNowak2011], which takes `#(S₁x, #(S₁y, S₁z))`
over the three branch arguments, the `S₁` wrappers keeping the smash's length
product away from zero at the empty word. The smash generator is excluded from the
subalgebra `SmashFree` names, so the bound here is instead the concatenation of the
same three arguments, of length `|x| + |y| + |z|`, which dominates each of them at
every environment including the empty one. -/
@[expose] def condRaw : sig.toPFunctor.W :=
  WType.mk (.boundedRec 3)
    ![WType.mk (.proj 3 0) Fin.elim0, WType.mk (.proj 5 4) Fin.elim0,
      WType.mk (.proj 5 3) Fin.elim0,
      concatCompRaw 4
        (concatCompRaw 4 (WType.mk (.proj 4 1) Fin.elim0) (WType.mk (.proj 4 2) Fin.elim0))
        (WType.mk (.proj 4 3) Fin.elim0)]

/-- The four-way conditional as an expression of arity four. Its recursion respects
the bound because its value is one of the three branch arguments, each no longer
than their concatenation. -/
@[expose] def cond : COf 4 :=
  ⟨⟨⟨condRaw, by decide⟩, by
      refine ⟨fun x ↦ ?_, ?_⟩
      · have h1 : (x 1).length ≤ (x 3 ++ (x 2 ++ x 1)).length := by
          simp only [List.length_append]
          omega
        have h2 : (x 2).length ≤ (x 3 ++ (x 2 ++ x 1)).length := by
          simp only [List.length_append]
          omega
        have h3 : (x 3).length ≤ (x 3 ++ (x 2 ++ x 1)).length := by
          simp only [List.length_append]
          omega
        refine List.rec ?_ (fun b _ _ ↦ ?_) (x 0)
        · exact h1
        · cases b
          · exact h3
          · exact h2
      · refine fun b : Fin 4 ↦ ?_
        match b with
        | 0 | 1 | 2 => exact ⟨trivial, fun d ↦ d.elim0⟩
        | 3 =>
          refine ⟨trivial, fun d ↦ ?_⟩
          match d with
          | .inl () | .inr 1 => exact ⟨trivial, fun c ↦ c.elim0⟩
          | .inr 0 =>
            refine ⟨trivial, fun e ↦ ?_⟩
            match e with
            | .inl () | .inr 0 | .inr 1 => exact ⟨trivial, fun c ↦ c.elim0⟩⟩, rfl⟩

/-- The meaning of the conditional, at arity four. -/
@[expose] def condSem : Sem 4 := transport cond.property cond.val.eval

/-- The conditional returns its second, third or fourth argument according as its
first is empty, odd or even, the parity being read off the Lean list's head. -/
theorem condSem_eq (u v w z : List Bool) :
    condSem ![u, v, w, z] =
      match u with
      | [] => v
      | true :: _ => w
      | false :: _ => z := by
  match u with
  | [] | true :: _ | false :: _ => rfl

/-- Whether no `smash` node occurs anywhere in a raw tree. -/
@[expose] def smashFreeBool : sig.toPFunctor.W → Bool :=
  WType.elim Bool fun x ↦
    match x with
    | ⟨.smash, _⟩ => false
    | ⟨_, c⟩ => decide (∀ b, c b = true)

/-- An expression of the subalgebra `[ε, I, s₀, s₁, ∗; COMP, BRN]`, which
[Strahm2003] Theorem 1(2) contains in the functions computable
simultaneously in polynomial time and linear space. Hereditary: a
top-node test would not exclude `#` from subterms. -/
@[expose] def SmashFree (e : C) : Prop := smashFreeBool e.val.val = true

/-- `SmashFree` is decidable, its `Bool` equation unfolded explicitly since a bare
`inferInstance` does not see through the definition. -/
instance (e : C) : Decidable (SmashFree e) :=
  inferInstanceAs (Decidable (smashFreeBool e.val.val = true))

end

end Cobham

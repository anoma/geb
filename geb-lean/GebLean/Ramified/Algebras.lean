import GebLean.Ramified.HigherOrder

/-!
# The canonical free-algebra instances

The three canonical free-algebra signatures of Leivant's higher-type ramified
recurrence and a smoke instantiation of the Phase 2 higher-order infrastructure
at each: the monadic word signature `natAlgSig` (`1 + X`;
`GebLean/Ramified/AlgSig.lean`), the polyadic binary-word signature
`binWordAlgSig` (`1 + 2X`), and the binary-tree signature `treeAlgSig`
(`1 + X²`). For each of the two new signatures the standard constructors are
exhibited at the base object sort, one flat recurrence (`RIdent.frec`), and one
ramified monotonic recurrence (`RIdent.mrec`) are built, confirming that the
higher-order presentation `higherOrder` and the schema identifiers `RIdent`
apply uniformly at an arbitrary base algebra. The numeric reading of the
`natAlgSig` carrier (`natToFreeAlg`/`freeAlgToNat`;
`GebLean/Ramified/AlgSig.lean`) is packaged as a computable equivalence
`natFreeAlgEquiv : FreeAlg natAlgSig ≃ ℕ`.

## Main definitions

* `binWordAlgSig` — the `1 + 2X` binary-word signature: one nullary and two
  unary constructors.
* `treeAlgSig` — the `1 + X²` binary-tree signature: one nullary and one binary
  constructor.
* `binEmpty`, `binCons` — the constructors of the binary-word carrier.
* `binLength` — the word length, a ramified monotonic recurrence over
  `binWordAlgSig`.
* `binTail` — the first-letter destructor, a flat recurrence over
  `binWordAlgSig`.
* `treeLeaf`, `treeNode` — the constructors of the binary-tree carrier.
* `treeSize` — the constructor-rebuild recurrence over `treeAlgSig`, a ramified
  monotonic recurrence extensionally the identity.
* `treeLeftChild` — the left-child destructor, a flat recurrence over
  `treeAlgSig`.
* `natFreeAlgEquiv` — the numeric reading packaged as a computable equivalence
  `FreeAlg natAlgSig ≃ ℕ`.

## Main statements

* `natToFreeAlg_freeAlgToNat` — the numeric reading is a right inverse of the
  encoding, the round trip `natToFreeAlg (freeAlgToNat t) = t`.

## Implementation notes

The two new signatures are presented in the free-algebra format of
`GebLean/Ramified/AlgSig.lean` (labels with arities), so their carriers, the
generic constructor `FreeAlg.mk`, the recurrence `FreeAlg.recurse`, and the
whole Phase 2 higher-order layer instantiate without further work. The smoke
recurrences are stated at the reduced contexts (`[Ω o]` for `mrec`, `[o]` for
`frec`); the step functions and clauses are supplied by a match over the
constructor labels, following the `natAlgSig` examples of
`GebLean/Ramified/Examples.lean`. `natFreeAlgEquiv` is a plain `Equiv` whose two
directions are `freeAlgToNat` and `natToFreeAlg`; both are computable and both
round trips are proved by structural recursion, `natToFreeAlg_freeAlgToNat` via
the dependent eliminator `PolyFix.ind` (decision 8) with the `⟨0, _⟩`
arity-normalization of the unary constructor's single child.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The free word and tree
algebras and the monadic/polyadic subdivision of the word algebras — a monadic
algebra has a single unary constructor, a polyadic one several — are section
2.1; the recurrence over a free algebra is section 2.1, eq. (1). The three
canonical signatures are the transcription targets of the spec's section 4.1
table. The equivalence `natFreeAlgEquiv` is novel packaging of the numeric
reading.

## Tags

ramified recurrence, free algebra, word algebra, tree algebra, monadic,
polyadic, signature, recurrence, equivalence
-/

namespace GebLean.Ramified

open CategoryTheory

/-- The `1 + 2X` binary-word signature (Leivant III section 2.1, a polyadic word
algebra): the nullary constructor `none` (the empty word) and the two unary
constructors `some false` and `some true` (append a letter). Polyadic because it
carries more than one unary constructor, in contrast with the monadic
`natAlgSig`. -/
def binWordAlgSig : AlgSig :=
  ⟨Option Bool, fun b => match b with | none => 0 | some _ => 1⟩

/-- The `1 + X²` binary-tree signature (Leivant III section 2.1): the nullary
constructor `false` (a leaf) and the binary constructor `true` (an internal node
with two subtrees). -/
def treeAlgSig : AlgSig := ⟨Bool, fun b => cond b 2 0⟩

/-- The empty binary word: the nullary constructor of `binWordAlgSig`. -/
def binEmpty : FreeAlg binWordAlgSig := FreeAlg.mk none finZeroElim

/-- Append the letter `b` to a binary word: the unary constructor `some b` of
`binWordAlgSig`. -/
def binCons (b : Bool) (w : FreeAlg binWordAlgSig) : FreeAlg binWordAlgSig :=
  FreeAlg.mk (some b) (fun _ => w)

/-- A leaf: the nullary constructor of `treeAlgSig`. -/
def treeLeaf : FreeAlg treeAlgSig := FreeAlg.mk false finZeroElim

/-- An internal node with two subtrees: the binary constructor of
`treeAlgSig`. -/
def treeNode (l r : FreeAlg treeAlgSig) : FreeAlg treeAlgSig :=
  FreeAlg.mk true ![l, r]

/-- The empty-word term over a `binWordAlgSig` definition signature. -/
def binTmEmpty {n : Nat} {h : Fin n → List RType × RType} {Γ : Ctx RType} :
    Tm (defnSig binWordAlgSig n h) Γ RType.o :=
  Tm.op (sig := defnSig binWordAlgSig n h)
    (Sum.inl (Sum.inl (Sum.inl (oObj, none)))) finZeroElim

/-- The append-`false`-letter term over a `binWordAlgSig` definition signature. -/
def binTmCons0 {n : Nat} {h : Fin n → List RType × RType} {Γ : Ctx RType}
    (t : Tm (defnSig binWordAlgSig n h) Γ RType.o) :
    Tm (defnSig binWordAlgSig n h) Γ RType.o :=
  Tm.op (sig := defnSig binWordAlgSig n h)
    (Sum.inl (Sum.inl (Sum.inl (oObj, some false)))) (Fin.cons t finZeroElim)

/-- The leaf term over a `treeAlgSig` definition signature. -/
def treeTmLeaf {n : Nat} {h : Fin n → List RType × RType} {Γ : Ctx RType} :
    Tm (defnSig treeAlgSig n h) Γ RType.o :=
  Tm.op (sig := defnSig treeAlgSig n h)
    (Sum.inl (Sum.inl (Sum.inl (oObj, false)))) finZeroElim

/-- The node term over a `treeAlgSig` definition signature. -/
def treeTmNode {n : Nat} {h : Fin n → List RType × RType} {Γ : Ctx RType}
    (l r : Tm (defnSig treeAlgSig n h) Γ RType.o) :
    Tm (defnSig treeAlgSig n h) Γ RType.o :=
  Tm.op (sig := defnSig treeAlgSig n h)
    (Sum.inl (Sum.inl (Sum.inl (oObj, true))))
    (Fin.cons l (Fin.cons r finZeroElim))

/-- The word-length step at the empty word: the empty word (the numeral `0`,
encoded in unary through the letter `false`). -/
def binLengthZero : RIdent binWordAlgSig [] RType.o :=
  RIdent.defn ⟨0, finZeroElim, binTmEmpty⟩ finZeroElim

/-- The word-length step at a letter: the successor of the recursive result,
encoded as one further `false` letter. Both letters increment the length, so the
two letter labels share this step. -/
def binLengthSucc : RIdent binWordAlgSig [RType.o] RType.o :=
  RIdent.defn ⟨0, finZeroElim, binTmCons0 (Tm.var 0)⟩ finZeroElim

/-- The step functions of the word-length recurrence: the empty word at the
nullary constructor, one further letter at each unary constructor. -/
def binLengthSteps : (i : binWordAlgSig.B) →
    RIdent binWordAlgSig ([] ++ List.replicate (binWordAlgSig.ar i) RType.o) RType.o
  | none => binLengthZero
  | some _ => binLengthSucc

/-- The word length over `binWordAlgSig`, a ramified monotonic recurrence
(Leivant III section 2.1, eq. (4)) on the recurrence argument at `Ω o`:
`length ε = 0` and `length (b · w) = length w + 1`. The length is encoded in the
same carrier as a unary chain of `false` letters, so its count under
concatenation is additive. -/
def binLength : RIdent binWordAlgSig [RType.omega RType.o] RType.o :=
  RIdent.mrec [] RType.o binLengthSteps

/-- The first-letter destructor clause at a letter: the immediate subterm (the
word with its first letter removed). -/
def binTailKeep : RIdent binWordAlgSig [RType.o] RType.o :=
  RIdent.defn ⟨0, finZeroElim, Tm.var 0⟩ finZeroElim

/-- The clauses of the first-letter destructor: the empty word at the nullary
constructor, the subterm at each unary constructor. -/
def binTailClauses : (i : binWordAlgSig.B) →
    RIdent binWordAlgSig ([] ++ List.replicate (binWordAlgSig.ar i) RType.o) RType.o
  | none => binLengthZero
  | some _ => binTailKeep

/-- The first-letter destructor over `binWordAlgSig`, a flat recurrence (Leivant
III section 2.1, eq. (5)) on the recurrence argument at `o`: `tail ε = ε` and
`tail (b · w) = w`. A case analysis reading the immediate subterm, with no
recursive results. -/
def binTail : RIdent binWordAlgSig [RType.o] RType.o :=
  RIdent.frec [] RType.o binTailClauses

/-- The tree-size step at a leaf: a leaf. -/
def treeSizeLeaf : RIdent treeAlgSig [] RType.o :=
  RIdent.defn ⟨0, finZeroElim, treeTmLeaf⟩ finZeroElim

/-- The tree-size step at a node: the node of the two recursive results,
rebuilding the node. -/
def treeSizeNode : RIdent treeAlgSig [RType.o, RType.o] RType.o :=
  RIdent.defn ⟨0, finZeroElim, treeTmNode (Tm.var 0) (Tm.var 1)⟩ finZeroElim

/-- The step functions of the tree-size recurrence: a leaf at the nullary
constructor, the rebuilt node at the binary constructor. -/
def treeSizeSteps : (i : treeAlgSig.B) →
    RIdent treeAlgSig ([] ++ List.replicate (treeAlgSig.ar i) RType.o) RType.o
  | false => treeSizeLeaf
  | true => treeSizeNode

/-- The tree size over `treeAlgSig`, a ramified monotonic recurrence (Leivant
III section 2.1, eq. (4)) on the recurrence argument at `Ω o`, mrec-shaped
exactly like the `natAlgSig` size function `ramSize`
(`GebLean/Ramified/Examples.lean`): the step rebuilds the recurrence argument
constructor by constructor from the recursive results, so `treeSize` is
extensionally the identity on `o`. -/
def treeSize : RIdent treeAlgSig [RType.omega RType.o] RType.o :=
  RIdent.mrec [] RType.o treeSizeSteps

/-- The left-child destructor clause at a node: the left subterm. -/
def treeLeftKeep : RIdent treeAlgSig [RType.o, RType.o] RType.o :=
  RIdent.defn ⟨0, finZeroElim, Tm.var 0⟩ finZeroElim

/-- The clauses of the left-child destructor: a leaf at the nullary constructor,
the left subterm at the binary constructor. -/
def treeLeftClauses : (i : treeAlgSig.B) →
    RIdent treeAlgSig ([] ++ List.replicate (treeAlgSig.ar i) RType.o) RType.o
  | false => treeSizeLeaf
  | true => treeLeftKeep

/-- The left-child destructor over `treeAlgSig`, a flat recurrence (Leivant III
section 2.1, eq. (5)) on the recurrence argument at `o`: `leftChild (leaf) =
leaf` and `leftChild (node l r) = l`. A case analysis reading a subterm, with no
recursive results. -/
def treeLeftChild : RIdent treeAlgSig [RType.o] RType.o :=
  RIdent.frec [] RType.o treeLeftClauses

/-- The right inverse of the numeric reading of the standard `natAlgSig`
carrier: `natToFreeAlg (freeAlgToNat t) = t`. Proved by the dependent eliminator
`PolyFix.ind` (decision 8); the nullary case reduces the empty child function by
`Fin 0` extensionality, the unary case rewrites the single child through the
induction hypothesis at `⟨0, _⟩`. Together with `freeAlgToNat_natToFreeAlg`
(`GebLean/Ramified/AlgSig.lean`) this makes the numeric reading a two-sided
inverse. -/
theorem natToFreeAlg_freeAlgToNat (t : FreeAlg natAlgSig) :
    natToFreeAlg (freeAlgToNat t) = t := by
  refine PolyFix.ind (P := natAlgSig.polyEndo)
    (motive := fun {_} t => natToFreeAlg (freeAlgToNat t) = t)
    (fun {x} b children ihc => ?_) t
  cases b with
  | false =>
    refine congrArg (FreeAlg.mk (A := natAlgSig) false) ?_
    funext e
    exact e.elim0
  | true =>
    refine congrArg (FreeAlg.mk (A := natAlgSig) true) ?_
    funext e
    have h0 : e.val = 0 := Nat.lt_one_iff.mp e.isLt
    have he : (⟨0, Nat.zero_lt_one⟩ : Fin (natAlgSig.ar true)) = e := Fin.ext h0.symm
    subst he
    exact ihc ⟨0, by decide⟩

/-- The numeric reading of the standard `natAlgSig` carrier as a computable
equivalence `FreeAlg natAlgSig ≃ ℕ`, packaging `freeAlgToNat` and
`natToFreeAlg` (`GebLean/Ramified/AlgSig.lean`) with their two round trips. This
is the numeric glue the Phase 5 and Phase 7 statements against `LawvereERCat`
compose with. Novel packaging. -/
def natFreeAlgEquiv : FreeAlg natAlgSig ≃ ℕ where
  toFun := freeAlgToNat
  invFun := natToFreeAlg
  left_inv := natToFreeAlg_freeAlgToNat
  right_inv := freeAlgToNat_natToFreeAlg

end GebLean.Ramified

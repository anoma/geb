import GebLean.Ramified.HigherOrder

/-!
# The canonical free-algebra instances and signature morphisms

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
`natFreeAlgEquiv : FreeAlg natAlgSig ≃ ℕ`. A morphism of free-algebra
signatures (`AlgSigHom`, e.g. `1 + X` into `1 + 2X`) induces a structural
transport of carriers (`freeAlgMap`) with image-point naturality for
recurrences (`recurse_freeAlgMap`); the interpretative-quotient syntactic
categories do not inherit a functor from a non-surjective signature morphism
(see the implementation notes).

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
* `AlgSigHom` — a morphism of free-algebra signatures: a label map preserving
  arities.
* `freeAlgMap` — the carrier transport induced by a signature morphism.
* `AlgSigHom.pullSteps` — the pullback of recurrence step functions along a
  signature morphism.
* `interpMapObj` — the transport of standard-carrier values at object sorts.

## Main statements

* `natToFreeAlg_freeAlgToNat` — the numeric reading is a right inverse of the
  encoding, the round trip `natToFreeAlg (freeAlgToNat t) = t`.
* `freeAlgMap_mk` — the carrier transport is an algebra homomorphism.
* `recurse_freeAlgMap` — image-point naturality: a recurrence over the target
  signature, run at a transported value, computes as the pulled-back recurrence
  over the source.

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

A signature morphism `h : AlgSigHom A B` does not induce a functor
`RMRecCat A ⥤ RMRecCat B` of the interpretative-quotient syntactic categories
unless `onB` is surjective, so the spec's section 4.3 statement of algebra-map
functoriality is superseded on this point. The morphisms of `RMRecCat` are
classes of terms under equality of denotation over every environment, and
environments over `FreeAlg B` range over values outside the image of
`freeAlgMap h` whenever `onB` misses a label — as `some true` is missed by the
`1 + X` into `1 + 2X` morphism. A recurrence identifier transports clause-wise
at the image labels only and must be completed by default clauses at the
others, while an explicit definition transports structurally, which pins its
behaviour off the image; the quotient identifies denotationally equal
`A`-identifiers of the two kinds, and the completed transport of the
recurrence and the structural transport of the definition differ at the
non-image values. Distinct such pairs constrain the same default clause
incompatibly, so no choice of defaults descends to the quotient. The transport
is functorial at the level of the unquotiented term clones (raw `HomTuple`s),
which is material for the deferred equational workstream (the spec's section
9). What is provided here is the fragment that does hold: the label-and-arity
morphism `AlgSigHom`, the carrier transport `freeAlgMap` (an algebra
homomorphism, `freeAlgMap_mk`), its object-sort extension `interpMapObj`, and
the image-point naturality `recurse_freeAlgMap` — every recurrence over `B`,
run at a transported value, computes as the pulled-back recurrence over `A`,
so transported recurrences interpret correctly at transported values.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The free word and tree
algebras and the monadic/polyadic subdivision of the word algebras — a monadic
algebra has a single unary constructor, a polyadic one several — are section
2.1; the recurrence over a free algebra is section 2.1, eq. (1). The three
canonical signatures are the transcription targets of the spec's section 4.1
table. The equivalence `natFreeAlgEquiv` is novel packaging of the numeric
reading. The signature morphisms and the induced transport realize the
algebra-map item of the spec's section 4.3, restricted per the implementation
notes; `AlgSigHom`, `freeAlgMap`, `AlgSigHom.pullSteps`, `interpMapObj`, and
`recurse_freeAlgMap` are novel packaging.

## Tags

ramified recurrence, free algebra, word algebra, tree algebra, monadic,
polyadic, signature, signature morphism, transport, recurrence, equivalence
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
(Leivant III section 2.3, eq. (4)) on the recurrence argument at `Ω o`:
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
III section 2.3, eq. (5)) on the recurrence argument at `o`: `tail ε = ε` and
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
III section 2.3, eq. (4)) on the recurrence argument at `Ω o`, mrec-shaped
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
section 2.3, eq. (5)) on the recurrence argument at `o`: `leftChild (leaf) =
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

/-- A morphism of free-algebra signatures (the spec's section 4.3): a
constructor-label map preserving arities, e.g. `1 + X` into `1 + 2X` (zero to
the empty word, successor to one chosen letter). Novel packaging of the
standard signature-morphism notion over `AlgSig`. -/
structure AlgSigHom (A B : AlgSig) where
  /-- The constructor-label map. -/
  onB : A.B → B.B
  /-- The label map preserves arities. -/
  ar_eq : ∀ b, B.ar (onB b) = A.ar b

/-- The carrier transport induced by a signature morphism: relabel each node by
`onB`, reindexing the subterms along `ar_eq`. An algebra homomorphism
(`freeAlgMap_mk`), realized by the recurrence `FreeAlg.recurse`. Novel
packaging (the spec's section 4.3). -/
def freeAlgMap {A B : AlgSig} (h : AlgSigHom A B) : FreeAlg A → FreeAlg B :=
  FreeAlg.recurse (A := A) (P := Unit)
    (fun b _ _sub rec => FreeAlg.mk (h.onB b) fun i => rec (Fin.cast (h.ar_eq b) i)) ()

/-- The carrier transport is an algebra homomorphism: it sends a constructor
node to the `onB`-relabelled node on the transported subterms, reindexed along
`ar_eq`. -/
@[simp] theorem freeAlgMap_mk {A B : AlgSig} (h : AlgSigHom A B) (b : A.B)
    (subterms : Fin (A.ar b) → FreeAlg A) :
    freeAlgMap h (FreeAlg.mk b subterms) =
      FreeAlg.mk (h.onB b) fun i => freeAlgMap h (subterms (Fin.cast (h.ar_eq b) i)) :=
  rfl

/-- The pullback of recurrence step functions along a signature morphism: the
step at label `b` is the given `B`-step at `onB b`, reading the transported
subterms and the recursive results reindexed along `ar_eq`. The `A`-recurrence
that `recurse_freeAlgMap` identifies with a `B`-recurrence at transported
values. Novel packaging. -/
def AlgSigHom.pullSteps {A B : AlgSig} {P C : Type} (h : AlgSigHom A B)
    (g : (b : B.B) → P → (Fin (B.ar b) → FreeAlg B) → (Fin (B.ar b) → C) → C)
    (b : A.B) (p : P) (subterms : Fin (A.ar b) → FreeAlg A)
    (rec : Fin (A.ar b) → C) : C :=
  g (h.onB b) p (fun i => freeAlgMap h (subterms (Fin.cast (h.ar_eq b) i)))
    (fun i => rec (Fin.cast (h.ar_eq b) i))

/-- Image-point naturality of the carrier transport: a recurrence over `B`, run
at a transported value `freeAlgMap h t`, computes as the recurrence over `A`
with the pulled-back step functions (`AlgSigHom.pullSteps`), run at `t`. The
statement is quantified over transported values only; at values of `FreeAlg B`
outside the image of `freeAlgMap h` the two sides are unrelated, and it is
there that the interpretative quotient obstructs an induced functor (see the
implementation notes). Novel packaging (the spec's section 4.3). -/
theorem recurse_freeAlgMap {A B : AlgSig} {P C : Type} (h : AlgSigHom A B)
    (g : (b : B.B) → P → (Fin (B.ar b) → FreeAlg B) → (Fin (B.ar b) → C) → C)
    (p : P) (t : FreeAlg A) :
    FreeAlg.recurse g p (freeAlgMap h t) = FreeAlg.recurse (h.pullSteps g) p t := by
  refine PolyFix.ind (P := A.polyEndo)
    (motive := fun {_} t => ∀ q : P,
      FreeAlg.recurse g q (freeAlgMap h t) = FreeAlg.recurse (h.pullSteps g) q t)
    (fun {x} b children ihc q => ?_) t p
  exact congrArg
    (g (h.onB b) q fun i => freeAlgMap h (children (Fin.cast (h.ar_eq b) i)))
    (funext fun i => ihc (Fin.cast (h.ar_eq b) i) q)

/-- The transport of standard-carrier values at an object sort: read the value
as a base-carrier element (`RType.interp_isObj`), transport by `freeAlgMap`,
and read back. The object sorts are the fragment of the r-types on which the
transport of denotations is defined; a transport at an arrow sort would need an
inverse transport for the domain. Novel packaging (the spec's section 4.3). -/
def interpMapObj {A B : AlgSig} (h : AlgSigHom A B) {s : RType} (hs : s.IsObj) :
    RType.interp (FreeAlg A) s → RType.interp (FreeAlg B) s := fun x =>
  cast (RType.interp_isObj (FreeAlg B) hs).symm
    (freeAlgMap h (cast (RType.interp_isObj (FreeAlg A) hs) x))

end GebLean.Ramified

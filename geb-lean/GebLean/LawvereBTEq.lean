import GebLean.LawvereBT
import GebLean.PolyAlgUMorph

/-!
# Equality Proof Polynomial for BTMor1

Defines the polynomial endofunctor on `Over ℕ` whose
initial algebra gives the equality proof tree type for
`BTMor1`.  The polynomial is a 7-component coproduct
encoding reflexivity, symmetry, transitivity, congruence
for branch, congruence for fold, fold-leaf computation,
and fold-branch computation.
-/

namespace GebLean

open CategoryTheory

/-- Reflexivity component of the equality polynomial.
At fiber `n`, positions carry a single `BTMor1 n` term.
No directions (leaf node). -/
def btMorEqReflPoly : PolyEndo ℕ :=
  polyBetweenConst (polyFixCarrier btMorPoly)

/-- Symmetry component of the equality polynomial.
At fiber `n`, positions carry a pair of `BTMor1 n`
terms (the two sides of the equality to be reversed).
One `PUnit` direction at fiber `n` (the proof of the
reversed equality). -/
def btMorEqSymmPoly : PolyEndo ℕ :=
  fun n => ccrObjMk
    (fun (_ : BTMor1 n × BTMor1 n) =>
      Over.mk (fun (_ : PUnit) => n))

/-- Transitivity component of the equality polynomial.
At fiber `n`, positions carry a triple of `BTMor1 n`
terms (the three endpoints of the two equalities to be
composed).  Two `Bool` directions at fiber `n` (the
two sub-proofs). -/
def btMorEqTransPoly : PolyEndo ℕ :=
  fun n => ccrObjMk
    (fun (_ : BTMor1 n × BTMor1 n × BTMor1 n) =>
      Over.mk (fun (_ : Bool) => n))

/-- Congruence-branch component of the equality
polynomial.  At fiber `n`, positions carry four
`BTMor1 n` terms (the left and right children of two
branch terms: l1, l2, r1, r2).  Two `Bool` directions
at fiber `n` (proofs that l1 = l2 and r1 = r2). -/
def btMorEqCongBranchPoly : PolyEndo ℕ :=
  fun n => ccrObjMk
    (fun (_ : BTMor1 n × BTMor1 n ×
        BTMor1 n × BTMor1 n) =>
      Over.mk (fun (_ : Bool) => n))

/-- Congruence-fold component of the equality
polynomial.  At fiber `n`, positions carry pairs of
base children, step children, and tree children for two
fold terms sharing the same output dimension `m` and
projection index `j : Fin m`.

Directions are `Fin (m + m + 1)` with the same fiber
map as `btMorFoldPoly`: the first `m` map to fiber `n`
(proofs that corresponding base children are equal),
the next `m` map to fiber `m + m` (proofs that
corresponding step children are equal), and the last
maps to fiber `n` (proof that the tree children are
equal). -/
def btMorEqCongFoldPoly : PolyEndo ℕ :=
  fun n => ccrObjMk
    (fun (pos : Σ m, Fin m ×
        (Fin m → BTMor1 n) ×
        (Fin m → BTMor1 n) ×
        (Fin m → BTMor1 (m + m)) ×
        (Fin m → BTMor1 (m + m)) ×
        BTMor1 n × BTMor1 n) =>
      let m := pos.1
      Over.mk
        (fun (d : Fin (m + m + 1)) =>
          if d.val < m then n
          else if d.val < m + m
            then m + m
          else n))

/-- Fold-leaf computation rule component of the
equality polynomial.  At fiber `n`, positions carry
the data of a fold applied to a leaf: output dimension
`m`, projection index `j : Fin m`, base children
`f : Fin m → BTMor1 n`, and step children
`g : Fin m → BTMor1 (m + m)`.

No directions (this is axiomatic, not derived from
sub-proofs). -/
def btMorEqFoldLeafPoly : PolyEndo ℕ :=
  fun n => ccrObjMk
    (fun (_ : Σ m, Fin m ×
        (Fin m → BTMor1 n) ×
        (Fin m → BTMor1 (m + m))) =>
      Over.mk
        (fun (e : PEmpty) => e.elim))

/-- Fold-branch computation rule component of the
equality polynomial.  At fiber `n`, positions carry
the data of a fold applied to a branch: output
dimension `m`, projection index `j : Fin m`, base
children `f : Fin m → BTMor1 n`, step children
`g : Fin m → BTMor1 (m + m)`, and the two subtrees
`t1 t2 : BTMor1 n`.

No directions (this is axiomatic, not derived from
sub-proofs). -/
def btMorEqFoldBranchPoly : PolyEndo ℕ :=
  fun n => ccrObjMk
    (fun (_ : Σ m, Fin m ×
        (Fin m → BTMor1 n) ×
        (Fin m → BTMor1 (m + m)) ×
        BTMor1 n × BTMor1 n) =>
      Over.mk
        (fun (e : PEmpty) => e.elim))

/-! ## Equality polynomial: coproduct -/

/-- The seven summands of the equality polynomial,
indexed by `Fin 7`. -/
def btMorEqComponents : Fin 7 → PolyEndo ℕ :=
  fun i => match i with
    | 0 => btMorEqReflPoly
    | 1 => btMorEqSymmPoly
    | 2 => btMorEqTransPoly
    | 3 => btMorEqCongBranchPoly
    | 4 => btMorEqCongFoldPoly
    | 5 => btMorEqFoldLeafPoly
    | 6 => btMorEqFoldBranchPoly

/-- The polynomial endofunctor on `Over ℕ` whose initial
algebra gives the equality proof tree type for `BTMor1`.
A seven-way coproduct of reflexivity, symmetry,
transitivity, congruence-branch, congruence-fold,
fold-leaf computation, and fold-branch computation
components. -/
def btMorEqPoly : PolyEndo ℕ :=
  polyBetweenCoprod (Fin 7) btMorEqComponents

/-! ## Proof tree type and constructors

The initial algebra of `btMorEqPoly` gives the type of
equality proof trees for `BTMor1`.  Each constructor
injects component evaluation data into the coproduct
polynomial via `polyBetweenInj` and applies the initial
algebra structure map `polyFixStrFamily`.
-/

/-- An equality proof tree witnessing equality between
two `BTMor1 n` terms.  Defined as the initial algebra
of the seven-component equality polynomial
`btMorEqPoly`. -/
abbrev BTMorEq (n : ℕ) : Type :=
  PolyFix btMorEqPoly n

private abbrev btMorEqCarrier :=
  polyFixCarrier btMorEqPoly

private def btMorEqInject (j : Fin 7) {n : ℕ}
    (eval : polyBetweenEvalFamily ℕ ℕ
      (btMorEqComponents j)
      btMorEqCarrier n) :
    BTMorEq n :=
  polyFixStrFamily btMorEqPoly n
    (polyEndoMorphEvalAt
      (polyBetweenInj (Fin 7)
        btMorEqComponents j)
      btMorEqCarrier n eval)

/-- Reflexivity: every `BTMor1 n` term is equal to
itself. -/
def BTMorEq.refl {n : ℕ} (t : BTMor1 n) :
    BTMorEq n :=
  btMorEqInject 0
    ⟨⟨⟨n, t⟩, rfl⟩,
      (overInitial_isInitial ℕ).to
        btMorEqCarrier⟩

/-- Symmetry: if `t1 = t2` then `t2 = t1`. -/
def BTMorEq.symm {n : ℕ}
    (t1 t2 : BTMor1 n)
    (child : BTMorEq n) :
    BTMorEq n :=
  btMorEqInject 1
    ⟨(t1, t2), Over.homMk
      (fun (_ : PUnit) => ⟨n, child⟩)
      (by funext _; rfl)⟩

/-- Transitivity: if `t1 = t2` and `t2 = t3` then
`t1 = t3`. -/
def BTMorEq.trans {n : ℕ}
    (t1 t2 t3 : BTMor1 n)
    (c1 c2 : BTMorEq n) :
    BTMorEq n :=
  btMorEqInject 2
    ⟨(t1, t2, t3), Over.homMk
      (fun (b : Bool) =>
        ⟨n, if b then c1 else c2⟩)
      (by funext _; rfl)⟩

/-- Congruence for branch: if `l1 = l2` and
`r1 = r2` then `branch l1 r1 = branch l2 r2`. -/
def BTMorEq.congBranch {n : ℕ}
    (l1 l2 r1 r2 : BTMor1 n)
    (c1 c2 : BTMorEq n) :
    BTMorEq n :=
  btMorEqInject 3
    ⟨(l1, l2, r1, r2), Over.homMk
      (fun (b : Bool) =>
        ⟨n, if b then c1 else c2⟩)
      (by funext _; rfl)⟩

/-- Congruence for fold: if base children, step
children, and tree children are pairwise equal,
then the fold results are equal. -/
def BTMorEq.congFold {n : ℕ}
    (m : ℕ) (j : Fin m)
    (f f' : Fin m → BTMor1 n)
    (g g' : Fin m → BTMor1 (m + m))
    (tree tree' : BTMor1 n)
    (baseProofs : Fin m → BTMorEq n)
    (stepProofs :
      Fin m → BTMorEq (m + m))
    (treeProof : BTMorEq n) :
    BTMorEq n :=
  btMorEqInject 4
    ⟨⟨m, j, f, f', g, g',
        tree, tree'⟩,
      Over.homMk
        (fun (d : Fin (m + m + 1)) =>
          if hb : d.val < m then
            ⟨n, baseProofs ⟨d.val, hb⟩⟩
          else if hs : d.val < m + m then
            ⟨m + m,
              stepProofs ⟨d.val - m,
                by omega⟩⟩
          else ⟨n, treeProof⟩)
        (by funext d
            dsimp [btMorEqCarrier,
              btMorEqComponents,
              btMorEqCongFoldPoly,
              polyFixCarrier,
              familySliceForward,
              familySliceForwardObj,
              ccrObjMk, ccrFamily,
              types_comp_apply]
            split_ifs <;> rfl)⟩

/-- Fold-leaf computation: folding a leaf yields
the `j`-th base component. -/
def BTMorEq.foldLeaf {n : ℕ}
    (m : ℕ) (j : Fin m)
    (f : Fin m → BTMor1 n)
    (g : Fin m → BTMor1 (m + m)) :
    BTMorEq n :=
  btMorEqInject 5
    ⟨⟨m, j, f, g⟩,
      Over.homMk
        (fun (e : PEmpty) => e.elim)
        (by funext e; exact e.elim)⟩

/-- Fold-branch computation: folding a branch yields
the `j`-th step component applied to the two recursive
fold results. -/
def BTMorEq.foldBranch {n : ℕ}
    (m : ℕ) (j : Fin m)
    (f : Fin m → BTMor1 n)
    (g : Fin m → BTMor1 (m + m))
    (t1 t2 : BTMor1 n) :
    BTMorEq n :=
  btMorEqInject 6
    ⟨⟨m, j, f, g, t1, t2⟩,
      Over.homMk
        (fun (e : PEmpty) => e.elim)
        (by funext e; exact e.elim)⟩

/-! ## Induction principle for BTMorEq

Built on `PolyFixCoprod.ind`, with one step per
coproduct component of `btMorEqPoly`. -/

/-- Induction/recursion principle for `BTMorEq`.
Each step receives a component index `i : Fin 7`,
the component's position, children, and induction
hypotheses.  Match on `i` to handle the seven
constructors (refl, symm, trans, congBranch,
congFold, foldLeaf, foldBranch). -/
def BTMorEq.ind
    {motive : ∀ {n : ℕ},
      BTMorEq n → Sort _}
    (step : ∀ (i : Fin 7) {n : ℕ}
      (p : polyBetweenIndex ℕ ℕ
        (btMorEqComponents i) n)
      (children :
        ∀ e : (polyBetweenFamily ℕ ℕ
          (btMorEqComponents i) n p).left,
          BTMorEq
            ((polyBetweenFamily ℕ ℕ
              (btMorEqComponents i) n
                p).hom e))
      (_ :
        ∀ e : (polyBetweenFamily ℕ ℕ
          (btMorEqComponents i) n p).left,
          motive (children e)),
      motive (PolyFix.mk n
        (show polyBetweenIndex ℕ ℕ
          (polyBetweenCoprod (Fin 7)
            btMorEqComponents) n from
          ⟨i, p⟩) children))
    {n : ℕ} (t : BTMorEq n) : motive t :=
  PolyFixCoprod.ind
    (motive := motive)
    (steps := step)
    t

/-! ## Endpoint extraction

Given an equality proof tree `BTMorEq n`, extract
the left and right `BTMor1 n` endpoints. -/

/-- Extract the left endpoint of an equality proof
tree.  For each constructor, return the left-hand
side of the equation it witnesses. -/
def eqLhs {n : ℕ} (proof : BTMorEq n) :
    BTMor1 n :=
  BTMorEq.ind
    (motive := fun {n} _ => BTMor1 n)
    (step := fun i => match i with
      | ⟨0, _⟩ => fun p _ _ =>
        cast (congrArg BTMor1 p.property)
          p.val.2
      | ⟨1, _⟩ => fun p _ _ => p.1
      | ⟨2, _⟩ => fun p _ _ => p.1
      | ⟨3, _⟩ => fun p _ _ =>
        BTMor1.branch p.1 p.2.2.1
      | ⟨4, _⟩ => fun p _ _ =>
        BTMor1.fold p.1 p.2.2.1
          p.2.2.2.2.1 p.2.2.2.2.2.2.1
          p.2.1
      | ⟨5, _⟩ => fun p _ _ =>
        BTMor1.fold p.1 p.2.2.1
          p.2.2.2 BTMor1.leaf p.2.1
      | ⟨6, _⟩ => fun p _ _ =>
        BTMor1.fold p.1 p.2.2.1
          p.2.2.2.1
          (BTMor1.branch
            p.2.2.2.2.1 p.2.2.2.2.2)
          p.2.1)
    proof

/-- Extract the right endpoint of an equality proof
tree.  For each constructor, return the right-hand
side of the equation it witnesses. -/
def eqRhs {n : ℕ} (proof : BTMorEq n) :
    BTMor1 n :=
  BTMorEq.ind
    (motive := fun {n} _ => BTMor1 n)
    (step := fun i => match i with
      | ⟨0, _⟩ => fun p _ _ =>
        cast (congrArg BTMor1 p.property)
          p.val.2
      | ⟨1, _⟩ => fun p _ _ => p.2
      | ⟨2, _⟩ => fun p _ _ => p.2.2
      | ⟨3, _⟩ => fun p _ _ =>
        BTMor1.branch p.2.1 p.2.2.2
      | ⟨4, _⟩ => fun p _ _ =>
        BTMor1.fold p.1 p.2.2.2.1
          p.2.2.2.2.2.1 p.2.2.2.2.2.2.2
          p.2.1
      | ⟨5, _⟩ => fun p _ _ =>
        p.2.2.1 p.2.1
      | ⟨6, _⟩ => fun p _ _ =>
        (p.2.2.2.1 p.2.1).subst
          (fun i =>
            if h : i.val < p.1
            then BTMor1.fold p.1
              p.2.2.1 p.2.2.2.1
              p.2.2.2.2.1 ⟨i.val, h⟩
            else BTMor1.fold p.1
              p.2.2.1 p.2.2.2.1
              p.2.2.2.2.2
              ⟨i.val - p.1, by omega⟩))
    proof

/-! ## Endpoint computation lemmas

Each lemma states that `eqLhs` or `eqRhs` applied to
a specific constructor returns the expected
`BTMor1 n` term. -/

/-- Left endpoint of reflexivity:
`eqLhs (refl t) = t`. -/
theorem eqLhs_refl {n : ℕ} (t : BTMor1 n) :
    eqLhs (BTMorEq.refl t) = t := rfl

/-- Right endpoint of reflexivity:
`eqRhs (refl t) = t`. -/
theorem eqRhs_refl {n : ℕ} (t : BTMor1 n) :
    eqRhs (BTMorEq.refl t) = t := rfl

/-- Left endpoint of symmetry:
`eqLhs (symm t1 t2 c) = t1`. -/
theorem eqLhs_symm {n : ℕ}
    (t1 t2 : BTMor1 n) (c : BTMorEq n) :
    eqLhs (BTMorEq.symm t1 t2 c) = t1 :=
  rfl

/-- Right endpoint of symmetry:
`eqRhs (symm t1 t2 c) = t2`. -/
theorem eqRhs_symm {n : ℕ}
    (t1 t2 : BTMor1 n) (c : BTMorEq n) :
    eqRhs (BTMorEq.symm t1 t2 c) = t2 :=
  rfl

/-- Left endpoint of transitivity:
`eqLhs (trans t1 t2 t3 c1 c2) = t1`. -/
theorem eqLhs_trans {n : ℕ}
    (t1 t2 t3 : BTMor1 n)
    (c1 c2 : BTMorEq n) :
    eqLhs (BTMorEq.trans t1 t2 t3 c1 c2) =
      t1 := rfl

/-- Right endpoint of transitivity:
`eqRhs (trans t1 t2 t3 c1 c2) = t3`. -/
theorem eqRhs_trans {n : ℕ}
    (t1 t2 t3 : BTMor1 n)
    (c1 c2 : BTMorEq n) :
    eqRhs (BTMorEq.trans t1 t2 t3 c1 c2) =
      t3 := rfl

/-- Left endpoint of branch congruence:
`eqLhs (congBranch l1 l2 r1 r2 c1 c2) =
  branch l1 r1`. -/
theorem eqLhs_congBranch {n : ℕ}
    (l1 l2 r1 r2 : BTMor1 n)
    (c1 c2 : BTMorEq n) :
    eqLhs (BTMorEq.congBranch
      l1 l2 r1 r2 c1 c2) =
      BTMor1.branch l1 r1 := rfl

/-- Right endpoint of branch congruence:
`eqRhs (congBranch l1 l2 r1 r2 c1 c2) =
  branch l2 r2`. -/
theorem eqRhs_congBranch {n : ℕ}
    (l1 l2 r1 r2 : BTMor1 n)
    (c1 c2 : BTMorEq n) :
    eqRhs (BTMorEq.congBranch
      l1 l2 r1 r2 c1 c2) =
      BTMor1.branch l2 r2 := rfl

/-- Left endpoint of fold congruence:
`eqLhs (congFold m j f f' g g' tree tree'
  bp sp tp) = fold m f g tree j`. -/
theorem eqLhs_congFold {n : ℕ}
    (m : ℕ) (j : Fin m)
    (f f' : Fin m → BTMor1 n)
    (g g' : Fin m → BTMor1 (m + m))
    (tree tree' : BTMor1 n)
    (bp : Fin m → BTMorEq n)
    (sp : Fin m → BTMorEq (m + m))
    (tp : BTMorEq n) :
    eqLhs (BTMorEq.congFold m j f f'
      g g' tree tree' bp sp tp) =
      BTMor1.fold m f g tree j := rfl

/-- Right endpoint of fold congruence:
`eqRhs (congFold m j f f' g g' tree tree'
  bp sp tp) = fold m f' g' tree' j`. -/
theorem eqRhs_congFold {n : ℕ}
    (m : ℕ) (j : Fin m)
    (f f' : Fin m → BTMor1 n)
    (g g' : Fin m → BTMor1 (m + m))
    (tree tree' : BTMor1 n)
    (bp : Fin m → BTMorEq n)
    (sp : Fin m → BTMorEq (m + m))
    (tp : BTMorEq n) :
    eqRhs (BTMorEq.congFold m j f f'
      g g' tree tree' bp sp tp) =
      BTMor1.fold m f' g' tree' j := rfl

/-- Left endpoint of fold-leaf computation:
`eqLhs (foldLeaf m j f g) =
  fold m f g leaf j`. -/
theorem eqLhs_foldLeaf {n : ℕ}
    (m : ℕ) (j : Fin m)
    (f : Fin m → BTMor1 n)
    (g : Fin m → BTMor1 (m + m)) :
    eqLhs (BTMorEq.foldLeaf m j f g) =
      BTMor1.fold m f g BTMor1.leaf j :=
  rfl

/-- Right endpoint of fold-leaf computation:
`eqRhs (foldLeaf m j f g) = f j`. -/
theorem eqRhs_foldLeaf {n : ℕ}
    (m : ℕ) (j : Fin m)
    (f : Fin m → BTMor1 n)
    (g : Fin m → BTMor1 (m + m)) :
    eqRhs (BTMorEq.foldLeaf m j f g) =
      f j := rfl

/-- Left endpoint of fold-branch computation:
`eqLhs (foldBranch m j f g t1 t2) =
  fold m f g (branch t1 t2) j`. -/
theorem eqLhs_foldBranch {n : ℕ}
    (m : ℕ) (j : Fin m)
    (f : Fin m → BTMor1 n)
    (g : Fin m → BTMor1 (m + m))
    (t1 t2 : BTMor1 n) :
    eqLhs (BTMorEq.foldBranch
      m j f g t1 t2) =
      BTMor1.fold m f g
        (BTMor1.branch t1 t2) j := rfl

/-- Right endpoint of fold-branch computation:
`eqRhs (foldBranch m j f g t1 t2) =
  (g j).subst (fun i => ...)`. -/
theorem eqRhs_foldBranch {n : ℕ}
    (m : ℕ) (j : Fin m)
    (f : Fin m → BTMor1 n)
    (g : Fin m → BTMor1 (m + m))
    (t1 t2 : BTMor1 n) :
    eqRhs (BTMorEq.foldBranch
      m j f g t1 t2) =
      (g j).subst (fun i =>
        if h : i.val < m
        then BTMor1.fold m f g t1
          ⟨i.val, h⟩
        else BTMor1.fold m f g t2
          ⟨i.val - m, by omega⟩) := rfl

/-! ## Substitution combinators for fold uniqueness

The fold uniqueness constructor `btMorRel.foldUniq`
states that any morphism tuple satisfying the leaf and
branch computation rules equals the fold.  Its
hypotheses and conclusion involve substitutions built
from these combinators. -/

/-- Extend a substitution `σ : Fin n → BTMor1 k` to
`Fin (n + 1) → BTMor1 k` by mapping the last variable
to `tree`. -/
def btSubstSnoc {n k : ℕ}
    (σ : Fin n → BTMor1 k)
    (tree : BTMor1 k) :
    Fin (n + 1) → BTMor1 k :=
  Fin.lastCases tree (fun v => σ v)

/-- Embed a substitution into a larger context:
`σ v ↦ (σ v).subst (proj ∘ castSucc ∘ castSucc)`,
i.e., shift all free variables by `d`. -/
def btSubstEmbed {n k : ℕ} (d : ℕ)
    (σ : Fin n → BTMor1 k) :
    Fin n → BTMor1 (k + d) :=
  fun v => (σ v).subst
    (fun u => BTMor1.proj ⟨u.val, by omega⟩)

/-- The fold-branch substitution target: for the
branch computation rule, the step function `g j` is
substituted with fold terms selecting the left or
right subtree. -/
def btFoldBranchSubst {n m k : ℕ}
    (f : Fin m → BTMor1 n)
    (g : Fin m → BTMor1 (m + m))
    (σ : Fin n → BTMor1 k) :
    Fin (m + m) → BTMor1 (k + 2) :=
  fun i =>
    if h : i.val < m
    then BTMor1.fold m
      (btSubstEmbed 2 (fun i' => (f i').subst σ))
      g
      (BTMor1.proj ⟨k, by omega⟩)
      ⟨i.val, h⟩
    else BTMor1.fold m
      (btSubstEmbed 2 (fun i' => (f i').subst σ))
      g
      (BTMor1.proj ⟨k + 1, by omega⟩)
      ⟨i.val - m, by omega⟩

/-- The fold-branch substitution for the branch
uniqueness premise, parameterized by `φ` rather
than `f` and `g`.  For each `i : Fin (m + m)`,
this selects `φ i` applied to the left subtree
projection (if `i < m`) or `φ (i - m)` applied to
the right subtree projection (if `i ≥ m`). -/
def btFoldBranchSubstPhi {n m k : ℕ}
    (φ : Fin m → BTMor1 (n + 1))
    (σ : Fin n → BTMor1 k) :
    Fin (m + m) → BTMor1 (k + 2) :=
  fun i =>
    if h : i.val < m
    then (φ ⟨i.val, h⟩).subst
      (btSubstSnoc (btSubstEmbed 2 σ)
        (BTMor1.proj ⟨k, by omega⟩))
    else (φ ⟨i.val - m, by omega⟩).subst
      (btSubstSnoc (btSubstEmbed 2 σ)
        (BTMor1.proj ⟨k + 1, by omega⟩))

/-- `btSubstSnoc` at `Fin.castSucc i` returns
`σ i`. -/
@[simp] theorem btSubstSnoc_castSucc
    {n k : ℕ}
    (σ : Fin n → BTMor1 k)
    (tree : BTMor1 k)
    (i : Fin n) :
    btSubstSnoc σ tree (Fin.castSucc i) =
      σ i := by
  unfold btSubstSnoc
  exact Fin.lastCases_castSucc i

/-- `btSubstSnoc` at `Fin.last n` returns
`tree`. -/
@[simp] theorem btSubstSnoc_last
    {n k : ℕ}
    (σ : Fin n → BTMor1 k)
    (tree : BTMor1 k) :
    btSubstSnoc σ tree (Fin.last n) = tree := by
  unfold btSubstSnoc
  exact Fin.lastCases_last

/-- `btSubstSnoc` at a raw `Fin` value known to be
less than `n` returns `σ` applied to the
corresponding `Fin n` value. -/
theorem btSubstSnoc_lt {n k : ℕ}
    (σ : Fin n → BTMor1 k)
    (tree : BTMor1 k)
    (i : Fin (n + 1)) (h : i.val < n) :
    btSubstSnoc σ tree i = σ ⟨i.val, h⟩ := by
  conv_lhs =>
    rw [show i = Fin.castSucc ⟨i.val, h⟩ from
      Fin.ext (by simp)]
  exact btSubstSnoc_castSucc σ tree ⟨i.val, h⟩

/-- `btSubstSnoc` at a raw `Fin` value equal to `n`
returns `tree`. -/
theorem btSubstSnoc_eq {n k : ℕ}
    (σ : Fin n → BTMor1 k)
    (tree : BTMor1 k)
    (i : Fin (n + 1)) (h : i.val = n) :
    btSubstSnoc σ tree i = tree := by
  conv_lhs =>
    rw [show i = Fin.last n from
      Fin.ext h]
  exact btSubstSnoc_last σ tree

/-- Composing `btSubstEmbed` with the nested
`btSubstSnoc` substitution used in the branch
case. -/
private theorem embed_subst_tau
    {n k m : ℕ}
    (σ_inner : Fin n → BTMor1 k)
    (σ_outer : Fin k → BTMor1 m)
    (v : Fin n) :
    (btSubstEmbed 2 σ_inner v).subst
      (btSubstSnoc
        (btSubstSnoc
          (btSubstEmbed 2 σ_outer)
          (BTMor1.proj ⟨m, by omega⟩))
        (BTMor1.proj
          ⟨m + 1, by omega⟩)) =
    btSubstEmbed 2
      (fun v => (σ_inner v).subst σ_outer)
      v := by
  unfold btSubstEmbed
  rw [BTMor1.subst_comp, BTMor1.subst_comp]
  congr 1; funext u
  rw [BTMor1.subst_proj]
  have h1 :
      (⟨u.val, by omega⟩ : Fin (k + 2)) =
      Fin.castSucc ⟨u.val, by omega⟩ := by
    ext; simp
  have h2 :
      (⟨u.val, by omega⟩ : Fin (k + 1)) =
      Fin.castSucc ⟨u.val, u.isLt⟩ := by
    ext; simp
  rw [h1, btSubstSnoc_castSucc,
    h2, btSubstSnoc_castSucc]

/-- Substituting the branch embedding into
`branch(proj k, proj(k+1))`. -/
private theorem branch_subst_tau
    {k m : ℕ}
    (σ_outer : Fin k → BTMor1 m) :
    (BTMor1.branch
      (BTMor1.proj ⟨k, by omega⟩)
      (BTMor1.proj ⟨k + 1, by omega⟩)
    ).subst
      (btSubstSnoc
        (btSubstSnoc
          (btSubstEmbed 2 σ_outer)
          (BTMor1.proj ⟨m, by omega⟩))
        (BTMor1.proj
          ⟨m + 1, by omega⟩)) =
    BTMor1.branch
      (BTMor1.proj ⟨m, by omega⟩)
      (BTMor1.proj ⟨m + 1, by omega⟩) := by
  rw [BTMor1.subst_branch,
    BTMor1.subst_proj,
    BTMor1.subst_proj]
  have h1 :
      (⟨k + 1, by omega⟩ : Fin (k + 2)) =
      Fin.last (k + 1) := by ext; simp
  have h2 :
      (⟨k, by omega⟩ : Fin (k + 2)) =
      Fin.castSucc (Fin.last k) := by
    ext; simp
  rw [h1, btSubstSnoc_last,
    h2, btSubstSnoc_castSucc,
    btSubstSnoc_last]

/-- Composing `btFoldBranchSubst` with the branch
embedding substitution. -/
private theorem foldBranchSubst_comp
    {n m_inner k m : ℕ}
    (f : Fin m_inner → BTMor1 n)
    (g : Fin m_inner → BTMor1
      (m_inner + m_inner))
    (σ_inner : Fin n → BTMor1 k)
    (σ_outer : Fin k → BTMor1 m) :
    (fun i =>
      (btFoldBranchSubst f g σ_inner i).subst
        (btSubstSnoc
          (btSubstSnoc
            (btSubstEmbed 2 σ_outer)
            (BTMor1.proj ⟨m, by omega⟩))
          (BTMor1.proj
            ⟨m + 1, by omega⟩))) =
    btFoldBranchSubst f g
      (fun v => (σ_inner v).subst σ_outer) := by
  funext i
  unfold btFoldBranchSubst
  have hsubst_comp_eq : ∀ v,
      ((f v).subst σ_inner).subst σ_outer =
      (f v).subst
        (fun w => (σ_inner w).subst σ_outer) :=
    fun v => BTMor1.subst_comp
      (t := f v) σ_inner σ_outer
  have hbase : ∀ v,
      (btSubstEmbed 2
        (fun i' => (f i').subst σ_inner)
        v).subst
        (btSubstSnoc
          (btSubstSnoc
            (btSubstEmbed 2 σ_outer)
            (BTMor1.proj ⟨m, by omega⟩))
          (BTMor1.proj
            ⟨m + 1, by omega⟩)) =
      btSubstEmbed 2
        (fun i' =>
          (f i').subst
            (fun v => (σ_inner v).subst
              σ_outer)) v := by
    intro v
    rw [embed_subst_tau
      (fun i' => (f i').subst σ_inner)
      σ_outer v]
    congr 1; funext w; exact hsubst_comp_eq w
  split_ifs with h_lt
  · rw [fold_subst_eq]; congr 1
    · exact funext hbase
    · rw [BTMor1.subst_proj]
      have h1 :
          (⟨k, by omega⟩ : Fin (k + 2)) =
          Fin.castSucc (Fin.last k) := by
        ext; simp
      rw [h1, btSubstSnoc_castSucc,
        btSubstSnoc_last]
  · rw [fold_subst_eq]; congr 1
    · exact funext hbase
    · rw [BTMor1.subst_proj]
      have h1 :
          (⟨k + 1, by omega⟩ :
            Fin (k + 2)) =
          Fin.last (k + 1) := by
        ext; simp
      rw [h1, btSubstSnoc_last]

/-- Composing `btFoldBranchSubstPhi` with the
branch embedding substitution. -/
private theorem btFoldBranchSubstPhi_comp
    {n m k l : ℕ}
    (φ : Fin m → BTMor1 (n + 1))
    (σ_inner : Fin n → BTMor1 k)
    (σ_outer : Fin k → BTMor1 l) :
    (fun i =>
      (btFoldBranchSubstPhi φ σ_inner i).subst
        (btSubstSnoc
          (btSubstSnoc
            (btSubstEmbed 2 σ_outer)
            (BTMor1.proj ⟨l, by omega⟩))
          (BTMor1.proj
            ⟨l + 1, by omega⟩))) =
    btFoldBranchSubstPhi φ
      (fun v => (σ_inner v).subst σ_outer) := by
  funext i
  unfold btFoldBranchSubstPhi
  split_ifs with h_lt
  · rw [BTMor1.subst_comp]; congr 1
    funext v
    refine Fin.lastCases ?_ ?_ v
    · simp only [btSubstSnoc_last,
        BTMor1.subst_proj]
      have h1 :
          (⟨k, by omega⟩ : Fin (k + 2)) =
          Fin.castSucc (Fin.last k) := by
        ext; simp
      rw [h1, btSubstSnoc_castSucc,
        btSubstSnoc_last]
    · intro w
      simp only [btSubstSnoc_castSucc]
      exact embed_subst_tau σ_inner σ_outer w
  · rw [BTMor1.subst_comp]; congr 1
    funext v
    refine Fin.lastCases ?_ ?_ v
    · simp only [btSubstSnoc_last,
        BTMor1.subst_proj]
      have h1 :
          (⟨k + 1, by omega⟩ : Fin (k + 2)) =
          Fin.last (k + 1) := by
        ext; simp
      rw [h1, btSubstSnoc_last]
    · intro w
      simp only [btSubstSnoc_castSucc]
      exact embed_subst_tau σ_inner σ_outer w

/-- Composing `btSubstSnoc` with a further
substitution distributes to the components. -/
theorem btSubstSnoc_comp {n k m : ℕ}
    (σ : Fin n → BTMor1 k)
    (tree : BTMor1 k)
    (τ : Fin k → BTMor1 m) :
    (fun v => (btSubstSnoc σ tree v).subst τ) =
    btSubstSnoc
      (fun v => (σ v).subst τ)
      (tree.subst τ) := by
  funext v
  refine Fin.lastCases ?_ ?_ v
  · simp [btSubstSnoc_last]
  · intro i
    simp [btSubstSnoc_castSucc]

/-! ## Equality relation

The equality relation on `BTMor1 n` as an inductive
proposition, with constructors mirroring those of the
polynomial proof tree type `BTMorEq`.  Defining the
relation inductively (rather than as existence of a
proof tree with matching endpoints) bakes the endpoint
invariants into the type indices, enabling induction
on the relation to produce hypotheses with the
correct endpoint types. -/

/-- Two `BTMor1 n` terms are related when connected
by the congruence closure of the fold computation
rules.  Constructors correspond to the seven
components of `btMorEqPoly`. -/
inductive btMorRel : (n : ℕ) →
    BTMor1 n → BTMor1 n → Prop where
  | refl {n : ℕ} (t : BTMor1 n) :
      btMorRel n t t
  | symm {n : ℕ} {t1 t2 : BTMor1 n} :
      btMorRel n t1 t2 →
      btMorRel n t2 t1
  | trans {n : ℕ}
      {t1 t2 t3 : BTMor1 n} :
      btMorRel n t1 t2 →
      btMorRel n t2 t3 →
      btMorRel n t1 t3
  | congBranch {n : ℕ}
      {l1 l2 r1 r2 : BTMor1 n} :
      btMorRel n l1 l2 →
      btMorRel n r1 r2 →
      btMorRel n (BTMor1.branch l1 r1)
        (BTMor1.branch l2 r2)
  | congFold {n : ℕ}
      {m : ℕ} {j : Fin m}
      {f f' : Fin m → BTMor1 n}
      {g g' : Fin m → BTMor1 (m + m)}
      {tree tree' : BTMor1 n} :
      (∀ i, btMorRel n (f i) (f' i)) →
      (∀ i,
        btMorRel (m + m) (g i) (g' i)) →
      btMorRel n tree tree' →
      btMorRel n
        (BTMor1.fold m f g tree j)
        (BTMor1.fold m f' g' tree' j)
  | foldLeaf {n : ℕ}
      (m : ℕ) (j : Fin m)
      (f : Fin m → BTMor1 n)
      (g : Fin m → BTMor1 (m + m)) :
      btMorRel n
        (BTMor1.fold m f g BTMor1.leaf j)
        (f j)
  | foldBranch {n : ℕ}
      (m : ℕ) (j : Fin m)
      (f : Fin m → BTMor1 n)
      (g : Fin m → BTMor1 (m + m))
      (t1 t2 : BTMor1 n) :
      btMorRel n
        (BTMor1.fold m f g
          (BTMor1.branch t1 t2) j)
        ((g j).subst (fun i =>
          if h : i.val < m
          then BTMor1.fold m f g t1
            ⟨i.val, h⟩
          else BTMor1.fold m f g t2
            ⟨i.val - m, by omega⟩))
  | foldEta {n : ℕ} (t : BTMor1 n) :
      btMorRel n
        (BTMor1.fold 1
          (fun _ => BTMor1.leaf)
          (fun _ => BTMor1.branch
            (BTMor1.proj 0) (BTMor1.proj 1))
          t ⟨0, by omega⟩)
        t
  | foldUniq {n m : ℕ} (j : Fin m)
      (φ : Fin m → BTMor1 (n + 1))
      (f : Fin m → BTMor1 n)
      (g : Fin m → BTMor1 (m + m))
      {k : ℕ} (σ : Fin n → BTMor1 k)
      (tree : BTMor1 k)
      (hℓ : ∀ j, btMorRel k
        ((φ j).subst (btSubstSnoc σ BTMor1.leaf))
        ((f j).subst σ))
      (hβ : ∀ j, btMorRel (k + 2)
        ((φ j).subst
          (btSubstSnoc
            (btSubstEmbed 2 σ)
            (BTMor1.branch
              (BTMor1.proj ⟨k, by omega⟩)
              (BTMor1.proj
                ⟨k + 1, by omega⟩))))
        ((g j).subst
          (btFoldBranchSubstPhi φ σ))) :
      btMorRel k
        ((φ j).subst (btSubstSnoc σ tree))
        (BTMor1.fold m
          (fun i => (f i).subst σ)
          g tree j)
  /-- Ground completeness: if two terms at
  arity `n` are `btMorRel 0` after every
  ground substitution, they are `btMorRel n`.
  This captures the parameterized universal
  property of the BTO: agreement at all ground
  instances implies agreement at the open
  level. -/
  | substReflect {n : ℕ}
      {t1 t2 : BTMor1 n}
      (h : ∀ σ : Fin n → BTMor1 0,
        btMorRel 0 (t1.subst σ)
          (t2.subst σ)) :
      btMorRel n t1 t2

/-! ## Setoid -/

/-- The setoid on `BTMor1 n` induced by `btMorRel`.
-/
instance btMor1Setoid (n : ℕ) :
    Setoid (BTMor1 n) where
  r := btMorRel n
  iseqv := {
    refl := btMorRel.refl
    symm := btMorRel.symm
    trans := btMorRel.trans
  }

/-! ## Substitution congruence

Right congruence: substitution preserves the equality
relation.  The proof proceeds by induction on the
`btMorRel` derivation. -/

/-- Substitution preserves `btMorRel`: if
`btMorRel n t1 t2` then
`btMorRel m (t1.subst σ) (t2.subst σ)`. -/
theorem subst_cong_right {n m : ℕ}
    (σ : Fin n → BTMor1 m)
    {t1 t2 : BTMor1 n}
    (h : btMorRel n t1 t2) :
    btMorRel m (t1.subst σ) (t2.subst σ) := by
  induction h generalizing m with
  | refl => exact btMorRel.refl _
  | symm _ ih =>
    exact btMorRel.symm (ih σ)
  | trans _ _ ih1 ih2 =>
    exact btMorRel.trans (ih1 σ) (ih2 σ)
  | congBranch _ _ ihl ihr =>
    exact btMorRel.congBranch
      (ihl σ) (ihr σ)
  | congFold hf hg ht ihf _ iht =>
    rw [fold_subst_eq, fold_subst_eq]
    exact btMorRel.congFold
      (fun i => ihf i σ)
      hg
      (iht σ)
  | foldLeaf m' j f g =>
    rw [fold_subst_eq]
    conv_lhs =>
      arg 4; rw [BTMor1.subst_leaf]
    exact btMorRel.foldLeaf m' j
      (fun i => (f i).subst σ)
      g
  | foldBranch m' j f g t1 t2 =>
    rw [fold_subst_eq]
    conv_lhs =>
      arg 4; rw [BTMor1.subst_branch]
    apply btMorRel.trans
    · exact btMorRel.foldBranch m' j
        (fun i => (f i).subst σ) g
        (t1.subst σ) (t2.subst σ)
    · rw [BTMor1.subst_comp]
      have : (fun i : Fin (m' + m') =>
          (if h : i.val < m'
          then BTMor1.fold m' f g t1
            ⟨i.val, h⟩
          else BTMor1.fold m' f g t2
            ⟨i.val - m', by omega⟩
            ).subst σ) =
          (fun i : Fin (m' + m') =>
          if h : i.val < m'
          then BTMor1.fold m'
            (fun i => (f i).subst σ) g
            (t1.subst σ) ⟨i.val, h⟩
          else BTMor1.fold m'
            (fun i => (f i).subst σ) g
            (t2.subst σ)
            ⟨i.val - m', by omega⟩) := by
        funext i
        split
        · rw [fold_subst_eq]
        · rw [fold_subst_eq]
      rw [this]
      exact btMorRel.refl _
  | foldEta t =>
    rw [fold_subst_eq]
    conv_lhs =>
      arg 2; ext _; rw [BTMor1.subst_leaf]
    exact btMorRel.foldEta (t.subst σ)
  | @foldUniq n_inner m_inner j φ f g k_inner
      σ_inner tree hℓ hβ ihℓ ihβ =>
    let σ' : Fin n_inner → BTMor1 m :=
      fun v => (σ_inner v).subst σ
    let tree' : BTMor1 m := tree.subst σ
    rw [BTMor1.subst_comp,
      btSubstSnoc_comp σ_inner tree σ]
    rw [fold_subst_eq]
    conv_rhs => arg 2; ext i; rw [BTMor1.subst_comp]
    exact btMorRel.foldUniq j φ f g σ' tree'
      (fun j' => by
        have h := ihℓ j' σ
        rw [BTMor1.subst_comp,
          btSubstSnoc_comp σ_inner
            BTMor1.leaf σ,
          BTMor1.subst_leaf] at h
        rw [BTMor1.subst_comp] at h
        exact h)
      (fun j' => by
        let τ : Fin (k_inner + 2) →
            BTMor1 (m + 2) :=
          btSubstSnoc
            (btSubstSnoc
              (btSubstEmbed 2 σ)
              (BTMor1.proj ⟨m, by omega⟩))
            (BTMor1.proj
              ⟨m + 1, by omega⟩)
        have h := ihβ j' τ
        rw [BTMor1.subst_comp,
          btSubstSnoc_comp] at h
        rw [BTMor1.subst_comp] at h
        have hlhs_embed :
            (fun v => (btSubstEmbed 2
              σ_inner v).subst τ) =
            btSubstEmbed 2 σ' :=
          funext (fun v =>
            embed_subst_tau σ_inner σ v)
        have hlhs_tree :
            (BTMor1.branch
              (BTMor1.proj
                ⟨k_inner, by omega⟩)
              (BTMor1.proj
                ⟨k_inner + 1, by omega⟩)
            ).subst τ =
            BTMor1.branch
              (BTMor1.proj ⟨m, by omega⟩)
              (BTMor1.proj
                ⟨m + 1, by omega⟩) :=
          branch_subst_tau σ
        rw [show btSubstSnoc
              (fun v => (btSubstEmbed 2
                σ_inner v).subst τ)
              ((BTMor1.branch
                (BTMor1.proj
                  ⟨k_inner, by omega⟩)
                (BTMor1.proj
                  ⟨k_inner + 1, by omega⟩)
              ).subst τ) =
            btSubstSnoc
              (btSubstEmbed 2 σ')
              (BTMor1.branch
                (BTMor1.proj ⟨m, by omega⟩)
                (BTMor1.proj
                  ⟨m + 1, by omega⟩))
            from by rw [hlhs_embed,
              hlhs_tree]] at h
        rw [btFoldBranchSubstPhi_comp φ
          σ_inner σ] at h
        exact h)
  | substReflect hground =>
    exact btMorRel.substReflect
      (fun τ => by
        rw [BTMor1.subst_comp,
          BTMor1.subst_comp]
        exact hground
          (fun i => (σ i).subst τ))

/-- Substitution preserves `btMorRel` on the left:
if `∀ i, btMorRel m (σ i) (σ' i)` then
`btMorRel m (t.subst σ) (t.subst σ')`. -/
theorem subst_cong_left {n m : ℕ}
    (t : BTMor1 n)
    {σ σ' : Fin n → BTMor1 m}
    (hs : ∀ i, btMorRel m (σ i) (σ' i)) :
    btMorRel m (t.subst σ) (t.subst σ') :=
  (BTMor1.ind
    (motive := fun {k} (t : BTMor1 k) =>
      ∀ (m' : ℕ)
        (σ σ' : Fin k → BTMor1 m'),
        (∀ i,
          btMorRel m' (σ i) (σ' i)) →
        btMorRel m'
          (t.subst σ) (t.subst σ'))
    (step := fun i => match i with
      | ⟨0, _⟩ =>
        fun p _ _ m' σ0 σ0' hs0 =>
          hs0 (p.property ▸ p.val.2)
      | ⟨1, _⟩ =>
        fun _ _ _ _ _ _ _ =>
          btMorRel.refl _
      | ⟨2, _⟩ =>
        fun _ _ ih m' σ0 σ0' hs0 =>
          btMorRel.congBranch
            (ih (Sum.inl PUnit.unit)
              m' σ0 σ0' hs0)
            (ih (Sum.inr PUnit.unit)
              m' σ0 σ0' hs0)
      | ⟨3, _⟩ =>
        fun pos children ih
          m' σ0 σ0' hs0 => by
          rename_i ni _
          let pm := pos.1
          have hlb (i : Fin pm) :
              i.val < pm + pm + 1 :=
            Nat.lt_of_lt_of_le i.isLt
              (Nat.le_add_right
                pm (pm + 1))
          have hlt :
              pm + pm < pm + pm + 1 :=
            Nat.lt_succ_self _
          have hbf (i : Fin pm) :
              (polyBetweenFamily ℕ ℕ
                (btMorComponents
                  ⟨3, by omega⟩)
                ni pos).hom
                ⟨i.val, hlb i⟩ = ni := by
            unfold btMorComponents
              btMorFoldPoly
              polyBetweenFamily
              polyToOverFamily ccrObjMk
              ccrFamily; dsimp
            split_ifs <;> omega
          have htf :
              (polyBetweenFamily ℕ ℕ
                (btMorComponents
                  ⟨3, by omega⟩)
                ni pos).hom
                ⟨pm + pm, hlt⟩ = ni := by
            unfold btMorComponents
              btMorFoldPoly
              polyBetweenFamily
              polyToOverFamily ccrObjMk
              ccrFamily; dsimp
            split_ifs <;> omega
          set lhs := BTMor1.subst _ σ0
            with hlhs
          unfold BTMor1.subst BTMor1.ind
            PolyFixCoprod.ind PolyFix.ind
            at hlhs
          dsimp only at hlhs
          set rhs := BTMor1.subst _ σ0'
            with hrhs
          unfold BTMor1.subst BTMor1.ind
            PolyFixCoprod.ind PolyFix.ind
            at hrhs
          dsimp only at hrhs
          rw [hlhs, hrhs]
          exact btMorRel.congFold
            (fun i => ih ⟨i, hlb i⟩
              m'
              (fun v => σ0
                (hbf i ▸ v))
              (fun v => σ0'
                (hbf i ▸ v))
              (fun v => hs0
                (hbf i ▸ v)))
            (fun i => btMorRel.refl _)
            (ih ⟨pm + pm, hlt⟩
              m'
              (fun v => σ0
                (htf ▸ v))
              (fun v => σ0'
                (htf ▸ v))
              (fun v => hs0
                (htf ▸ v))))
    t) m σ σ' hs

/-- Full substitution congruence: if
`btMorRel n t1 t2` and
`∀ i, btMorRel m (σ i) (σ' i)` then
`btMorRel m (t1.subst σ) (t2.subst σ')`. -/
theorem subst_cong {n m : ℕ}
    {t1 t2 : BTMor1 n}
    {σ σ' : Fin n → BTMor1 m}
    (ht : btMorRel n t1 t2)
    (hs : ∀ i, btMorRel m (σ i) (σ' i)) :
    btMorRel m
      (t1.subst σ) (t2.subst σ') :=
  btMorRel.trans
    (subst_cong_right σ ht)
    (subst_cong_left t2 hs)

end GebLean

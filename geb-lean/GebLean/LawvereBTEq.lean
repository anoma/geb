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

No directions (this is an axiom, not derived from
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

No directions (this is an axiom, not derived from
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

end GebLean

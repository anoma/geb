import GebLean.PLang.TreeCalcMeta

/-!
# Tree Calculus Metatheory Tests

Tests for PCA axioms and confluence
definitions.
-/

open GebLean

private abbrev VL : Value.{0} := Value.leaf
private abbrev VS := Value.stem
private abbrev VF := Value.fork

private abbrev EV (v : Value.{0}) :
    CompTree.{0} :=
  CompTree.embedValue v

private abbrev APP (ts : List CompTree.{0}) :
    CompTree.{0} := CompTree.app ts

private def reduceN (n fuel : Nat)
    (t : CompTree.{0}) : CompTree.{0} :=
  match n with
  | 0 => t
  | n + 1 => reduceN n fuel (reduce1 fuel t)

private def isValue
    (expected : Value.{0})
    (t : CompTree.{0}) : Bool :=
  CompTree.cases
    (fun v => compValueToValue v == expected)
    (fun _ => false)
    t

private def evalCheck
    (fuel steps : Nat)
    (t : CompTree.{0})
    (expected : Value.{0}) : Bool :=
  match evalToValue fuel steps t with
  | some v => v == expected
  | none => false

/-! ## PCA K ground tests -/

-- K leaf (stem leaf) = leaf
#guard evalCheck 10 2
  (APP [EV Value.K, EV VL, EV (VS VL)]) VL

-- K (stem leaf) leaf = stem leaf
#guard evalCheck 10 2
  (APP [EV Value.K, EV (VS VL), EV VL]) (VS VL)

-- K (fork leaf leaf) (fork leaf leaf) =
-- fork leaf leaf
#guard evalCheck 10 2
  (APP [EV Value.K, EV (VF VL VL),
        EV (VF VL VL)]) (VF VL VL)

/-! ## PCA S ground tests -/

-- s leaf leaf = fork(stem(leaf), leaf)
#guard evalCheck 10 10
  (APP [EV pcaS, EV VL, EV VL])
  (VF (VS VL) VL)

-- s K K leaf = leaf (S K K = I)
#guard evalCheck 10 10
  (APP [EV pcaS, EV Value.K, EV Value.K,
        EV VL]) VL

-- s K K (stem leaf) = stem leaf
#guard evalCheck 10 20
  (APP [EV pcaS, EV Value.K, EV Value.K,
        EV (VS VL)]) (VS VL)

/-! ## ParReduces structural tests

These are type-level checks: constructing the
proofs verifies the definitions are consistent.
Since `ParReduces` is `Prop`-valued, we cannot
pattern-match on proofs at runtime. -/

-- embed reduces to itself (typecheck)
example : ParReduces
    (CompTree.embed CompValue.leaf)
    (CompTree.embed CompValue.leaf) :=
  ParReduces.refl_embed CompValue.leaf

-- appNil reduces to itself (typecheck)
example : ParReduces
    (CompTree.app []) (CompTree.app []) :=
  ParReduces.refl_appNil

import GebLean.PLang.TreeCalcPrograms

/-!
# Tree Calculus Programs Tests

Tests for derived combinators and abstraction.
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

private def isValue
    (expected : Value.{0})
    (t : CompTree.{0}) : Bool :=
  CompTree.cases
    (fun v => compValueToValue v == expected)
    (fun _ => false)
    t

private def reduceN (n fuel : Nat)
    (t : CompTree.{0}) : CompTree.{0} :=
  match n with
  | 0 => t
  | n + 1 => reduceN n fuel (reduce1 fuel t)

/-! ## K combinator: K x y = x

K = stem(leaf).
K x = fork(leaf, x).
fork(leaf, x) y → x. -/

-- K leaf stem(leaf) = leaf
-- Step 1: stem(leaf) leaf = fork(leaf, leaf)
-- Step 2: fork(leaf, leaf) stem(leaf) → leaf
#guard isValue VL
  (reduceN 2 10 (APP [EV Value.K, EV VL,
    EV (VS VL)]))

-- K (stem leaf) leaf = stem leaf
#guard isValue (VS VL)
  (reduceN 2 10 (APP [EV Value.K, EV (VS VL),
    EV VL]))

/-! ## I combinator: I x = x

I = S K K = fork(stem(K), K).
I x = fork(stem(K), K) x → K x (K x)
    = fork(leaf, x) fork(leaf, x) → x. -/

-- I leaf = leaf (multiple reduction steps)
#guard isValue VL
  (reduceN 10 10 (APP [EV Value.I, EV VL]))

-- I (stem leaf) = stem leaf
#guard isValue (VS VL)
  (reduceN 10 10 (APP [EV Value.I, EV (VS VL)]))

/-! ## S encoding: S f g x = f x (g x) -/

-- S K K leaf = K leaf (K leaf) = leaf
-- (this is I leaf)
#guard isValue VL
  (reduceN 10 10
    (APP [EV (Value.S Value.K Value.K),
          EV VL]))

/-! ## triage -/

-- triage w x y leaf = w
#guard isValue VL
  (reduce1 10
    (APP [EV (Value.triage VL (VS VL)
      (VF VL VL)), EV VL]))

-- triage w x y (stem u) = x u
-- triage VL K VL applied to stem(leaf):
-- fork(fork(VL, K), VL) stem(leaf)
-- → K leaf (rule 3b) → fork(leaf, leaf)
-- (partial app of K = stem(leaf) to leaf)
#guard isValue (VF VL VL)
  (reduceN 2 10
    (APP [EV (Value.triage VL Value.K VL),
          EV (VS VL)]))

/-! ## Boolean tests -/

-- true = K = stem(leaf)
#guard Value.true == VS VL

-- true x y = x (takes 2 steps: partial app
-- then K)
#guard isValue VL
  (reduceN 2 10
    (APP [EV Value.true, EV VL, EV (VS VL)]))

-- false x y = y (K I x y: K applied to I and x
-- gives I, then I y = y)
#guard isValue (VS VL)
  (reduceN 10 10
    (APP [EV Value.false, EV VL,
          EV (VS VL)]))

/-! ## Query tests -/

-- isLeaf leaf = true
-- triage true (K false) (K(K false)) leaf = true
#guard isValue Value.true
  (reduce1 10
    (APP [EV Value.isLeaf, EV VL]))

-- isLeaf stem(leaf):
-- fork(fork(true, K false), K(K false))
-- stem(leaf) → K false leaf = false
-- Needs several steps
#guard isValue Value.false
  (reduceN 10 10
    (APP [EV Value.isLeaf, EV (VS VL)]))

-- isStem stem(leaf) = true
#guard isValue Value.true
  (reduceN 10 10
    (APP [EV Value.isStem, EV (VS VL)]))

-- isFork fork(leaf, leaf) = true
#guard isValue Value.true
  (reduceN 10 10
    (APP [EV Value.isFork, EV (VF VL VL)]))

/-! ## appArgs -/

#guard Value.appArgs VL [] == VL
#guard Value.appArgs VL [VL] == VF VL VL
#guard Value.appArgs VL [VL, VL] ==
  VF (VF VL VL) VL

/-! ## contains -/

#guard Value.contains VL VL == true
#guard Value.contains VL (VS VL) == true
#guard Value.contains VL (VF (VS VL) VL)
    == true
#guard Value.contains (VS VL) VL == false
#guard Value.contains (VS VL) (VS VL) == true
#guard Value.contains (VS VL)
    (VF VL (VS VL)) == true

/-! ## bracket abstraction -/

-- bracket x x = I
#guard Value.bracket VL VL == Value.I

-- bracket x (const) where x doesn't appear:
-- K const
-- bracket (stem leaf) leaf = fork(leaf, leaf)
-- = K leaf
#guard Value.bracket (VS VL) VL ==
  VF VL VL

/-! ## Y2 structure -/

-- Y2 f = fork(d, d) where d = S f I
#guard (Value.Y2 VL).cases
  false
  (fun _ => false)
  (fun l r => l == r)

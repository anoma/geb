import GebLean.PLang.TreeCalcReduction

/-!
# Tree Calculus Reduction Tests

Tests for the five triage rules and partial
application behavior.
-/

open GebLean

/-! ## Convenience abbreviations -/

private abbrev VL : CompValue.{0} := CompValue.leaf
private abbrev VS (x : CompValue.{0}) :
    CompValue.{0} := CompValue.stem x
private abbrev VF (l r : CompValue.{0}) :
    CompValue.{0} := CompValue.fork l r

private abbrev EV (v : CompValue.{0}) :
    CompTree.{0} := CompTree.embed v

private abbrev APP (ts : List CompTree.{0}) :
    CompTree.{0} := CompTree.app ts

/-- Check if a CompTree is an embed whose
underlying value converts to the given Value. -/
private def isValue
    (expected : Value.{0})
    (t : CompTree.{0}) : Bool :=
  CompTree.cases
    (fun v => compValueToValue v == expected)
    (fun _ => false)
    t

/-- Check if a CompTree is an app with the given
number of children. -/
private def isAppOfLength
    (n : Nat)
    (t : CompTree.{0}) : Bool :=
  CompTree.cases
    (fun _ => false)
    (fun ts => ts.length == n)
    t

/-- Check observation position (Fin 4 index). -/
private def obsTag
    (obs : BehaviorObs stepCarrier.{0}) :
    Fin 4 :=
  BehaviorObs.tag obs

/-! ## Partial application tests -/

-- leaf applied to leaf = stem(leaf)
#guard isValue (Value.stem Value.leaf)
  (reduce1 10 (APP [EV VL, EV VL]))

-- stem(a) applied to leaf = fork(a, leaf)
#guard isValue
  (Value.fork Value.leaf Value.leaf)
  (reduce1 10 (APP [EV (VS VL), EV VL]))

/-! ## K rule (Rule 1):
fork(leaf, b) x --> b -/

-- fork(leaf, leaf) applied to stem(leaf):
-- K discards argument, returns leaf
#guard isValue Value.leaf
  (reduce1 10
    (APP [EV (VF VL VL), EV (VS VL)]))

-- K with remaining args:
-- fork(leaf, b) x y --> app(b, y)
#guard isAppOfLength 2
  (reduce1 10
    (APP [EV (VF VL VL), EV (VS VL), EV VL]))

/-! ## S rule (Rule 2):
fork(stem(a), b) x --> app(a, x, app(b, x)) -/

-- fork(stem(leaf), leaf) applied to leaf:
-- S produces app(leaf, leaf, app(leaf, leaf))
#guard isAppOfLength 3
  (reduce1 10
    (APP [EV (VF (VS VL) VL), EV VL]))

/-! ## Triage rules (Rules 3a-3c) -/

-- Rule 3a: fork(fork(w, xf), y) leaf --> w
#guard isValue Value.leaf
  (reduce1 10
    (APP [EV (VF (VF VL VL) VL), EV VL]))

-- Rule 3b: fork(fork(w, xf), y) stem(u) -->
-- app(xf, u)
#guard isAppOfLength 2
  (reduce1 10
    (APP [EV (VF (VF VL (VS VL)) VL),
          EV (VS VL)]))

-- Rule 3c: fork(fork(w, xf), y) fork(u, v) -->
-- y u v
#guard isAppOfLength 3
  (reduce1 10
    (APP [EV (VF (VF VL VL) (VS VL)),
          EV (VF VL VL)]))

/-! ## observeValue tests -/

#guard obsTag (observeValue VL) == 0
#guard obsTag (observeValue (VS VL)) == 1
#guard obsTag (observeValue (VF VL VL)) == 2

/-! ## step on values -/

#guard obsTag (step 10 (EV VL)) == 0
#guard obsTag (step 10 (EV (VS VL))) == 1
#guard obsTag (step 10 (EV (VF VL VL))) == 2

/-! ## step on simple applications -/

-- app([]) -> doneLeaf (tag 0)
#guard obsTag (step 10 (APP [])) == 0

-- app([t]) -> cont (tag 3)
#guard obsTag (step 10 (APP [EV VL])) == 3

-- K rule through step: should reduce and
-- observe the result
-- fork(leaf, leaf) applied to leaf: K -> leaf
-- reduce1 produces embed(leaf), step observes
-- it as doneLeaf (tag 0)
#guard obsTag
  (step 10
    (APP [EV (VF VL VL), EV VL])) == 0

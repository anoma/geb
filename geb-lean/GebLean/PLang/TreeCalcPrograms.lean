import GebLean.PLang.TreeCalcReduction

/-!
# Tree Calculus Programs

Derived combinators defined as `Value` terms.

In tree calculus, all programs are binary trees.
The leaf `△` is the sole primitive; partial
application builds stems (`△ x = stem(x)`) and
forks (`△ x y = fork(x, y)`).  The five triage
reduction rules give these trees their
computational behavior.

Notation: `app v [x₁, ..., xₙ]` denotes the
tree obtained by successive left-associated
application: `fork(fork(...fork(v, x₁)..., xₙ₋₁), xₙ)`.
-/

namespace GebLean

universe u

/-! ## Primitive combinators -/

/-- The K combinator: `K x y = x`.
`K = stem(leaf)`.  Applying K to x:
`stem(leaf) x = fork(leaf, x)`.  Then
`fork(leaf, x) y → x` by rule 1 (K). -/
def Value.K : Value.{u} :=
  Value.stem Value.leaf

/-- Encode `S f g` as a value:
`S f g x = f x (g x)`.
`fork(stem(f), g) x` triggers the S rule:
`f x (g x)`. -/
def Value.S (f g : Value.{u}) : Value.{u} :=
  Value.fork (Value.stem f) g

/-- The identity combinator: `I x = x`.
`I = S K K = fork(stem(K), K)`.

Derivation: `fork(stem(K), K) x` triggers
the S rule: `K x (K x) = x`. -/
def Value.I : Value.{u} :=
  Value.S Value.K Value.K

/-- `triage w x y z` dispatches on the structure
of `z`: returns `w` if `z` is leaf, `x u` if
`z` is `stem(u)`, `y u v` if `z` is
`fork(u, v)`.
`triage = λw. λx. λy. fork(fork(w, x), y)`.

As a Value:
`triage w x y = fork(fork(w, x), y)`.
This is not a single value but a family
parametrized by w, x, y.  We define the
three-argument version as a function on Values,
and a zero-argument version as the combinator
that builds the triage. -/
def Value.triage
    (w x y : Value.{u}) : Value.{u} :=
  Value.fork (Value.fork w x) y

/-! ## Application helpers

Since tree-calculus programs are built by
successive application, we define a helper
that applies a value to a list of arguments,
building `fork(fork(..., x₁), x₂)` etc.
-/

/-- Left-associated application of a value
to a list of value arguments. -/
def Value.appArgs :
    Value.{u} → List Value.{u} → Value.{u}
  | v, [] => v
  | v, x :: xs =>
    Value.appArgs (Value.fork v x) xs

/-! ## Boolean combinators -/

/-- `true = K = fork(leaf, leaf)`. -/
abbrev Value.true : Value.{u} := Value.K

/-- `false = K I`.
`K I = stem(leaf) I = fork(leaf, I)`. -/
def Value.false : Value.{u} :=
  Value.fork Value.leaf Value.I

/-! ## Query combinators

These use `triage` to inspect the structure
of their argument.
-/

/-- Apply K to a value: `K v = fork(leaf, v)`.
This is the "constant v" function. -/
def Value.applyK (v : Value.{u}) : Value.{u} :=
  Value.fork Value.leaf v

/-- `isLeaf = triage true (K false) (K (K false))`.
Returns `true` on leaf, `false` on stem or
fork. -/
def Value.isLeaf : Value.{u} :=
  Value.triage
    Value.true
    (Value.applyK Value.false)
    (Value.applyK (Value.applyK Value.false))

/-- `isStem = triage false (K true) (K (K false))`.
Returns `true` on stem, `false` on leaf or
fork. -/
def Value.isStem : Value.{u} :=
  Value.triage
    Value.false
    (Value.applyK Value.true)
    (Value.applyK (Value.applyK Value.false))

/-- `isFork = triage false (K false) (K (K true))`.
Returns `true` on fork, `false` on leaf or
stem. -/
def Value.isFork : Value.{u} :=
  Value.triage
    Value.false
    (Value.applyK Value.false)
    (Value.applyK (Value.applyK Value.true))

/-! ## Bracket abstraction

`bracket v body` compiles an expression `body`
that may refer to a "variable" `v` (represented
as a specific Value) into a combinator that takes
`v` as an argument.  This is the tree-calculus
analogue of lambda abstraction.

The standard bracket abstraction rules:

- If `body = v` (the variable itself): result
  is `I`.
- If `body` does not contain `v`: result is
  `K body`.
- If `body = fork(f, x)`: result is
  `S (bracket v f) (bracket v x)`,
  where `S f g x = f x (g x)`.

For tree calculus, `S f g` is encoded as
`fork(stem(f), g)`.

`star v body` is an optimized variant that
avoids redundant S/K combinations when one
branch doesn't use the variable.
-/

/-- Check whether `target` appears as a subtree
of the given value.  Defined as a catamorphism
via `Value.fold` carrying the reconstructed
original subtree alongside the Boolean
result. -/
def Value.contains
    (target : Value.{0})
    (body : Value.{0}) : Bool :=
  (Value.fold
    (α := Value.{0} × Bool)
    (Value.leaf, Value.leaf == target)
    (fun ⟨orig, childHas⟩ =>
      let v := Value.stem orig
      (v, v == target || childHas))
    (fun ⟨origL, lHas⟩ ⟨origR, rHas⟩ =>
      let v := Value.fork origL origR
      (v, v == target || lHas || rHas))
    body).2

/-- Bracket abstraction: compile `body`
(which may contain `var`) into a combinator
that takes `var` as input.

Defined as a catamorphism via `Value.fold`
with carrier `Value × Value`, where the first
component reconstructs the original subtree
and the second is the bracket result.

- If `body = var`: `I`.
- If `body` is not a fork: `K body`.
- If `body = fork(f, x)`:
  `S (bracket var f) (bracket var x)`
  = `fork(stem(bracket var f), bracket var x)`.
-/
def Value.bracket
    (var : Value.{0})
    (body : Value.{0}) : Value.{0} :=
  (Value.fold
    (α := Value.{0} × Value.{0})
    ( Value.leaf,
      if Value.leaf == var then Value.I
      else Value.fork Value.leaf Value.leaf )
    (fun ⟨orig, _⟩ =>
      let v := Value.stem orig
      ( v,
        if v == var then Value.I
        else Value.fork Value.leaf v ))
    (fun ⟨origL, brL⟩ ⟨origR, brR⟩ =>
      let v := Value.fork origL origR
      ( v,
        if v == var then Value.I
        else Value.fork
          (Value.stem brL) brR ))
    body).2

/-- Star abstraction: optimized bracket
abstraction that avoids redundant S/K when
a branch does not use the variable.

- If `body = var`: `I`.
- If `body` does not contain `var`: `K body`.
- If `body = fork(f, x)` and `f` does not use
  `var`: `fork(stem(f), star var x)`.
- Otherwise:
  `fork(stem(star var f), star var x)`.

The optimization: when `f` is free of `var`,
`bracket var f = K f`, and
`S (K f) g x = f (g x)`, so `stem(f)` can
replace `stem(K f)` directly. -/
def Value.star
    (var : Value.{0})
    (body : Value.{0}) : Value.{0} :=
  (Value.fold
    (α := Value.{0} × Value.{0})
    ( Value.leaf,
      if Value.leaf == var then Value.I
      else Value.fork Value.leaf Value.leaf )
    (fun ⟨orig, _⟩ =>
      let v := Value.stem orig
      ( v,
        if v == var then Value.I
        else Value.fork Value.leaf v ))
    (fun ⟨origL, stL⟩ ⟨origR, stR⟩ =>
      let v := Value.fork origL origR
      ( v,
        if v == var then Value.I
        else
          let lFree :=
            !(Value.contains var origL)
          let rFree :=
            !(Value.contains var origR)
          if lFree && rFree then
            Value.fork Value.leaf v
          else if lFree then
            Value.fork
              (Value.stem origL) stR
          else
            Value.fork
              (Value.stem stL) stR ))
    body).2

/-! ## Fixpoint combinators -/

/-- `selfApply = fork(stem(I), I)`.
`selfApply x = I x (I x) = x x`. -/
def Value.selfApply : Value.{u} :=
  Value.fork (Value.stem Value.I) Value.I

/-- `omega2 = fork(selfApply, selfApply)`.
`omega2 f = selfApply f (selfApply f)
          = f f (f f) = ...` (diverges). -/
def Value.omega2 : Value.{u} :=
  Value.fork Value.selfApply Value.selfApply

/-- `Y2 f = omega2 (star x. f (x x))`.
Since we define `Y2` as a value, we build
it using `star` abstraction.

`Z f = omega2 (λx. f (λv. x x v))`
  = the standard strict fixpoint combinator.

For tree calculus, `Y_2{f}` is defined in the
book as `fork(d, d)` where `d = fork(stem(f), I)`.

`Y_2{f}` satisfies: `Y_2{f} x = f (Y_2{f}) x`.

We define the template: given `f : Value`,
produce `Y_2{f} : Value`. -/
def Value.Y2 (f : Value.{u}) : Value.{u} :=
  let d := Value.S f Value.I
  Value.fork d d

end GebLean

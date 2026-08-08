/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.ConcreteSyntax

/-!
# A readable spelling of the rose syntax

`Geb.Csexp.print` and `Geb.Ast.printViaRose` are both [RFC9804]
canonical: length-prefixed and whitespace-free, so neither has a
readable form. This module spells the same `Rose k` as parenthesized
text, a node's label followed by its children, so that
`fork (leaf 0) (fork (leaf 1) (leaf 2))` reads as `(0 (1 2))`.

The fragment lies inside [R7RS] `<datum>`: a reader conforming to that
grammar accepts it without new code, and tools operating on
parenthesized text apply to it directly. Labels are decimal numerals,
which the [RFC9804] advanced form cannot spell as tokens — § 4.3
requires a token not begin with a digit — where [R7RS] and [EDN] read a
digit-initial token as a number.

## Main definitions

* `Rsexp.print` — the readable spelling of a `Rose k`.
* `Rsexp.parse` — the parser matching it, built from `Rsexp.parseStep`,
  `Rsexp.parseAux` and the shared `Rose.parseChildren`.
* `Rsexp.skipWs` — the whitespace skip the stripping discipline runs.
* `Rsexp.printViaRose`, `Rsexp.parseViaRose` — the composites with the
  rose bijection, spelling an `Ast k`.

## Main statements

* `Rsexp.parse_print`, `Rsexp.parseViaRose_printViaRose` — the
  retraction law, on `Rose` and on `Ast`, with `Rsexp.format_idem` and
  `Rsexp.print_injective` instantiating the generic corollaries.

## Implementation notes

The parser strips whitespace on return rather than on entry:
`parseStep` is called on stripped input and returns a stripped
remainder. That discipline is what lets `Rose.parseChildren` be reused
verbatim — the loop tests its input's head against `')'` immediately,
so it must be called on already-stripped input — and what lets `parse`
match `some (r, [])` syntactically rather than testing a remainder for
whitespace.

A childless node prints as a bare numeral, so a printed tree can end in
a digit and `parseAux_print` carries a delimiting side condition on the
caller's remainder. Always parenthesizing would remove the obligation
and the spelling; `Csexp.readDigits_append` carries the same condition
for the same reason.

## References

* [R7RS] §§ 4.1.3, 7.1.1, 7.1.2 — the datum grammar this fragment lies
  inside.
* [EDN] — the second readable format the spelling agrees with.
* [RFC9804] §§ 4.3, 6, 8 — the token rule that rules out the advanced
  form, and the conformance of declining it.
* [RFC8259] § 2 — the `ws` production this whitespace class matches.

## Tags

concrete syntax, s-expression, parser, retraction, rose tree
-/

@[expose] public section

namespace Geb
namespace Rsexp

/-! ## Whitespace -/

/-- The whitespace class this syntax admits: space, horizontal tab,
carriage return and line feed. It is a subset of the class [R7RS]
§ 7.1.1 fixes, and admits the same four characters as [RFC8259]
§ 2's `ws`. -/
def isWs (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\r' || c = '\n'

/-- Drop a leading run of whitespace. Carried by `List.rec` rather than
by structural recursion, per the recursor rule. -/
def skipWs : List Char → List Char :=
  List.rec [] fun c cs ih ↦ if isWs c then ih else c :: cs

@[simp] theorem skipWs_nil : skipWs [] = [] := rfl

theorem skipWs_cons (c : Char) (cs : List Char) :
    skipWs (c :: cs) = if isWs c then skipWs cs else c :: cs := rfl

/-! ## Printer -/

/-- The readable spelling: a childless node is its label, a node with
children is its label and their spellings, parenthesized and each
preceded by one space. The uniform space is what makes every element of
the child block a cons, which the arity bound and the whitespace skip
both use. -/
def print {k : Nat} : Rose k → List Char :=
  WType.elim (List Char) fun x ↦
    match x with
    | ⟨(i, 0), _⟩ => Csexp.decOf i.val
    | ⟨(i, _ + 1), ch⟩ =>
      '(' :: (Csexp.decOf i.val
        ++ (((List.ofFn ch).map (fun s ↦ ' ' :: s)).flatten ++ [')']))

@[simp] theorem print_zero {k : Nat} (i : Fin k) (f : Fin 0 → Rose k) :
    print (Rose.node i f) = Csexp.decOf i.val := rfl

theorem print_succ {k n : Nat} (i : Fin k) (f : Fin (n + 1) → Rose k) :
    print (Rose.node i f)
      = '(' :: (Csexp.decOf i.val
          ++ (((List.ofFn f).map (fun t ↦ ' ' :: print t)).flatten
              ++ [')'])) := by
  unfold print Rose.node
  rw [WType.elim_mk]
  -- reduce the match `WType.elim_mk` exposed, picking the `n.succ` arm
  simp only []
  rw [List.map_ofFn, List.map_ofFn]
  rfl

/-! ## Character facts -/

/-- The two parentheses are distinct characters. -/
theorem open_ne_close : ('(' : Char) ≠ ')' := by decide

/-- An opening parenthesis is not whitespace, so the whitespace skip
stops at the head of a parenthesized spelling. -/
theorem open_not_ws : isWs '(' = false := by decide

/-- A closing parenthesis is not whitespace, so the whitespace skip
stops at a child block's terminator. -/
theorem close_not_ws : isWs ')' = false := by decide

/-- A space is whitespace, so the whitespace skip consumes the separator
the printer emits before each child. -/
theorem space_is_ws : isWs ' ' = true := by decide

/-! ## The decimal layer -/

/-- A printed numeral reads back whole, and leaves exactly what followed
it. The delimiting hypothesis on the remainder is what a
non-parenthesizing spelling of a childless node costs; it is the same
condition `Csexp.readDigits_append` carries. -/
theorem readNat_append (n : Nat) (rest : List Char)
    (h : ∀ c cs, rest = c :: cs → Csexp.charDigit c = none) :
    Csexp.readNat (Csexp.decOf n ++ rest) = some (n, rest) := by
  unfold Csexp.readNat
  rw [Csexp.readDigits_append _ _ (Csexp.decOf_all_digits n) h]
  simp [Csexp.decOf_ne_nil n, Csexp.digitsVal_decOf, List.isEmpty_iff]

/-- A digit is not whitespace. The conclusion is `isWs c = false` rather
than a disequality because the whitespace class has four members. -/
theorem digit_not_ws {c : Char} (h : (Csexp.charDigit c).isSome) :
    isWs c = false := by
  unfold isWs
  have h1 : ¬ c = ' ' := by rintro rfl; exact absurd h (by decide)
  have h2 : ¬ c = '\t' := by rintro rfl; exact absurd h (by decide)
  have h3 : ¬ c = '\r' := by rintro rfl; exact absurd h (by decide)
  have h4 : ¬ c = '\n' := by rintro rfl; exact absurd h (by decide)
  simp [h1, h2, h3, h4]

/-- A digit is not an opening parenthesis. -/
theorem digit_not_open {c : Char} (h : (Csexp.charDigit c).isSome) :
    c ≠ '(' := by
  rintro rfl
  exact absurd h (by decide)

/-- A digit is not a closing parenthesis. -/
theorem digit_not_close {c : Char} (h : (Csexp.charDigit c).isSome) :
    c ≠ ')' := by
  rintro rfl
  exact absurd h (by decide)

/-- `Csexp.decOf_ne_nil` in the form its consumers use: a shortest-form
decimal has a head. -/
theorem decOf_eq_cons (n : Nat) : ∃ c cs, Csexp.decOf n = c :: cs :=
  List.exists_cons_of_ne_nil (Csexp.decOf_ne_nil n)

/-- The head of a shortest-form decimal is a digit. -/
theorem decOf_head_digit (n : Nat) :
    ∀ c cs, Csexp.decOf n = c :: cs → (Csexp.charDigit c).isSome := by
  intro c cs hc
  refine Csexp.decOf_all_digits n c ?_
  rw [hc]
  simp

/-- A numeral is already stripped: the whitespace skip is the identity on
a printed decimal and whatever follows it. -/
theorem skipWs_decOf_append (n : Nat) (rest : List Char) :
    skipWs (Csexp.decOf n ++ rest) = Csexp.decOf n ++ rest := by
  obtain ⟨c, cs, hc⟩ := decOf_eq_cons n
  rw [hc, List.cons_append, skipWs_cons,
    if_neg (by simp [digit_not_ws (decOf_head_digit n c cs hc)])]

/-! ## The head of a spelling -/

/-- Every spelling begins with an opening parenthesis or with a digit,
according to whether the node has children. This is the readable
counterpart of `Rose.exists_print_eq_cons`, which has only the
parenthesized case. -/
theorem print_head {k : Nat} (r : Rose k) :
    ∃ c cs, print r = c :: cs ∧ (c = '(' ∨ (Csexp.charDigit c).isSome) := by
  obtain ⟨⟨i, n⟩, f⟩ := r
  cases n with
  | zero =>
    obtain ⟨c, cs, hc⟩ := decOf_eq_cons i.val
    exact ⟨c, cs, (print_zero i f).trans hc, Or.inr (decOf_head_digit i.val c cs hc)⟩
  | succ n => exact ⟨'(', _, print_succ i f, Or.inl rfl⟩

/-- A spelling is already stripped: neither possible head is whitespace,
so the skip is the identity on a spelling followed by anything. -/
theorem skipWs_print_append {k : Nat} (r : Rose k) (rest : List Char) :
    skipWs (print r ++ rest) = print r ++ rest := by
  obtain ⟨c, cs, hc, hd⟩ := print_head r
  have hw : isWs c = false := by
    rcases hd with rfl | hd
    · exact open_not_ws
    · exact digit_not_ws hd
  rw [hc, List.cons_append, skipWs_cons, if_neg (by simp [hw])]

/-- The `rest = []` instance of `skipWs_print_append`, which is the form
the entry point uses. -/
theorem skipWs_print {k : Nat} (r : Rose k) : skipWs (print r) = print r := by
  have h := skipWs_print_append r []
  rwa [List.append_nil] at h

/-- A child block with its terminator never begins with a digit: it
begins with the terminator when empty and with a separating space
otherwise. Stating it over the terminated block is what makes the empty
case true. -/
theorem block_append_head_not_digit {k : Nat} (ts : List (Rose k))
    (rest : List Char) :
    ∀ c cs, (ts.map (fun t ↦ ' ' :: print t)).flatten ++ ')' :: rest
        = c :: cs → Csexp.charDigit c = none := by
  intro c cs h
  cases ts with
  | nil =>
    simp only [List.map_nil, List.flatten_nil, List.nil_append] at h
    injection h with h1 _
    subst h1
    decide
  | cons t ts =>
    simp only [List.map_cons, List.flatten_cons, List.cons_append] at h
    injection h with h1 _
    subst h1
    decide

/-! ## Parser -/

/-- One layer of the recursive descent. A tree is a bare numeral or a
parenthesized list, so this branches on the first character. It strips
whitespace at four sites: after `(`, after the label in each branch,
and after the child list. The strip after the parenthesized branch's
label is the one the grammar makes least obvious:
`Rose.parseChildren` tests its input's head against `')'` immediately,
so it must be called on stripped input or `(0 1 2)` fails at its first
child. `parseStep` is called on stripped input and returns a stripped
remainder; that invariant is what lets the shared loop be reused. -/
def parseStep (k : Nat) (childParse : List Char → Option (Rose k × List Char))
    (loopFuel : Nat) : List Char → Option (Rose k × List Char)
  | [] => none
  | c :: cs =>
    if c = '(' then
      match Csexp.readNat (skipWs cs) with
      | some (m, cs1) =>
        if h : m < k then
          (Rose.parseChildren childParse loopFuel (skipWs cs1)).map
            fun p ↦ (Rose.ofList ⟨m, h⟩ p.1, skipWs p.2)
        else none
      | none => none
    else
      match Csexp.readNat (c :: cs) with
      | some (m, cs1) =>
        if h : m < k then some (Rose.node ⟨m, h⟩ Fin.elim0, skipWs cs1)
        else none
      | none => none

/-- Recursive descent over the readable spelling. The `Nat` bounds the
recursion and serves in two roles at each layer: undecremented as the
child loop's bound, and decremented as the child parser's fuel. -/
def parseAux (k : Nat) : Nat → List Char → Option (Rose k × List Char) :=
  Nat.rec (motive := fun _ ↦ List Char → Option (Rose k × List Char))
    (fun _ ↦ none) fun f ih ↦ parseStep k ih (f + 1)

@[simp] theorem parseAux_succ (k f : Nat) :
    parseAux k (f + 1) = parseStep k (parseAux k f) (f + 1) := rfl

/-- The parser of the readable spelling, rejecting trailing input. The
leading strip and the stripping invariant together are what let a
leading indent and a trailing newline parse. -/
def parse (k : Nat) (cs : List Char) : Option (Rose k) :=
  match parseAux k cs.length (skipWs cs) with
  | some (r, []) => some r
  | _ => none

theorem parseStep_open (k : Nat)
    (childParse : List Char → Option (Rose k × List Char))
    (loopFuel : Nat) (cs : List Char) :
    parseStep k childParse loopFuel ('(' :: cs)
      = match Csexp.readNat (skipWs cs) with
        | some (m, cs1) =>
          if h : m < k then
            (Rose.parseChildren childParse loopFuel (skipWs cs1)).map
              fun p ↦ (Rose.ofList ⟨m, h⟩ p.1, skipWs p.2)
          else none
        | none => none := rfl

theorem parseStep_other (k : Nat)
    (childParse : List Char → Option (Rose k × List Char))
    (loopFuel : Nat) (c : Char) (cs : List Char) (hc : c ≠ '(') :
    parseStep k childParse loopFuel (c :: cs)
      = match Csexp.readNat (c :: cs) with
        | some (m, cs1) =>
          if h : m < k then some (Rose.node ⟨m, h⟩ Fin.elim0, skipWs cs1)
          else none
        | none => none := if_neg hc

/-! ## The retraction law -/

/-- The child loop reads back a printed child sequence, given a child
parser that reads back each child from its own spelling and returns the
stripped remainder, and one unit of fuel per child plus one for the
closing parenthesis. The loop's input is stripped, as every call site's
is; the remainder it returns is not, since `parseStep` strips what it
returns. -/
theorem parseChildren_print {k : Nat}
    (childParse : List Char → Option (Rose k × List Char)) :
    ∀ (ts : List (Rose k)) (fuel : Nat) (rest : List Char),
      (∀ t ∈ ts, ∀ r : List Char,
        (∀ c cs, r = c :: cs → Csexp.charDigit c = none) →
        childParse (print t ++ r) = some (t, skipWs r)) →
      ts.length < fuel →
      Rose.parseChildren childParse fuel
          (skipWs ((ts.map (fun t ↦ ' ' :: print t)).flatten ++ ')' :: rest))
        = some (ts, rest) :=
  List.rec (motive := fun ts ↦ ∀ (fuel : Nat) (rest : List Char),
      (∀ t ∈ ts, ∀ r : List Char,
        (∀ c cs, r = c :: cs → Csexp.charDigit c = none) →
        childParse (print t ++ r) = some (t, skipWs r)) →
      ts.length < fuel →
      Rose.parseChildren childParse fuel
          (skipWs ((ts.map (fun t ↦ ' ' :: print t)).flatten ++ ')' :: rest))
        = some (ts, rest))
    (fun fuel rest _ hfuel ↦ by
      obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by omega⟩
      rw [List.map_nil, List.flatten_nil, List.nil_append, skipWs_cons,
        if_neg (by simp [close_not_ws]), Rose.parseChildren_succ_close])
    (fun t ts ih fuel rest hchild hfuel ↦ by
      obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by omega⟩
      obtain ⟨c, cs, hc, hd⟩ := print_head t
      have hlt : ts.length < g := by simp at hfuel; omega
      have hne : c ≠ ')' := by
        rcases hd with rfl | hd
        · exact open_ne_close
        · exact digit_not_close hd
      have hcons : ∀ u : List Char, print t ++ u = c :: (cs ++ u) := fun u ↦ by
        rw [hc, List.cons_append]
      rw [List.map_cons, List.flatten_cons, List.append_assoc, List.cons_append,
        skipWs_cons, if_pos (by simp [space_is_ws]), skipWs_print_append, hcons,
        Rose.parseChildren_succ_cons _ _ _ _ hne, ← hcons,
        hchild t (by simp) _ (block_append_head_not_digit ts rest),
        Option.bind_some, ih g rest (fun x hx ↦ hchild x (by simp [hx])) hlt,
        Option.map_some])

/-- The parser inverts the printer on printed input, given fuel at least
the printed length. The remainder returned is the caller's stripped: a
childless node's spelling ends in a digit, so the delimiting hypothesis
on the remainder is what keeps the label from running on, and the
stripping invariant makes what comes back `skipWs rest` rather than
`rest`. -/
theorem parseAux_print {k : Nat} (r : Rose k) :
    ∀ (f : Nat) (rest : List Char), (print r).length ≤ f →
      (∀ c cs, rest = c :: cs → Csexp.charDigit c = none) →
      parseAux k f (print r ++ rest) = some (r, skipWs rest) :=
  WType.rec (motive := fun r ↦ ∀ (f : Nat) (rest : List Char),
      (print r).length ≤ f →
      (∀ c cs, rest = c :: cs → Csexp.charDigit c = none) →
      parseAux k f (print r ++ rest) = some (r, skipWs rest))
    (fun s ch ih f rest hf hrest ↦ by
      obtain ⟨i, n⟩ := s
      change (print (Rose.node i ch)).length ≤ f at hf
      change parseAux k f (print (Rose.node i ch) ++ rest)
        = some (Rose.node i ch, skipWs rest)
      cases n with
      | zero =>
        rw [print_zero] at hf ⊢
        obtain ⟨c, cs, hc⟩ := decOf_eq_cons i.val
        obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 :=
          ⟨f - 1, by rw [hc] at hf; simp only [List.length_cons] at hf; omega⟩
        rw [parseAux_succ, hc, List.cons_append,
          parseStep_other _ _ _ _ _
            (digit_not_open (decOf_head_digit i.val c cs hc)),
          ← List.cons_append, ← hc, readNat_append _ _ hrest]
        -- reduce the match on the `some` just produced, exposing the label-bound check
        simp only []
        rw [dif_pos i.isLt]
        exact congrArg (fun t ↦ some (t, skipWs rest))
          (congrArg (Rose.node i) (funext fun j ↦ j.elim0))
      | succ m =>
        rw [print_succ] at hf ⊢
        cases f with
        | zero => simp at hf
        | succ g =>
          have hlen : (Csexp.decOf i.val).length
              + (((List.ofFn ch).map (fun t ↦ ' ' :: print t)).flatten).length
                + 2 ≤ g + 1 := by
            simp only [List.length_cons, List.length_append] at hf
            omega
          have hL : (((List.ofFn ch).map (fun t ↦ ' ' :: print t)).flatten).length
              ≤ g := by omega
          have hchild : ∀ t ∈ List.ofFn ch, ∀ r : List Char,
              (∀ c cs, r = c :: cs → Csexp.charDigit c = none) →
              parseAux k g (print t ++ r) = some (t, skipWs r) := by
            intro t ht r' hr'
            obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ht
            refine ih j g r' ?_ hr'
            have hmem : ' ' :: print (ch j)
                ∈ (List.ofFn ch).map (fun t ↦ ' ' :: print t) :=
              List.mem_map_of_mem (List.mem_ofFn.mpr ⟨j, rfl⟩)
            have hsub : (' ' :: print (ch j)).length
                ≤ (((List.ofFn ch).map (fun t ↦ ' ' :: print t)).flatten).length :=
              (List.sublist_flatten_of_mem hmem).length_le
            simp only [List.length_cons] at hsub
            omega
          have hfuel : (List.ofFn ch).length < g + 1 := by
            have hpos : ∀ x ∈ ((List.ofFn ch).map (fun t ↦ ' ' :: print t)).map
                List.length, 1 ≤ x := by
              intro x hx
              obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
              obtain ⟨t, _, rfl⟩ := List.mem_map.mp hy
              simp
            have h := List.length_le_sum_of_one_le _ hpos
            rw [List.length_map, List.length_map, ← List.length_flatten] at h
            omega
          rw [List.cons_append, parseAux_succ, parseStep_open]
          simp only [List.append_assoc, List.singleton_append]
          rw [skipWs_decOf_append,
            readNat_append _ _ (block_append_head_not_digit (List.ofFn ch) rest)]
          -- reduce the match on the `some` just produced, exposing the label-bound check
          simp only []
          rw [dif_pos i.isLt,
            parseChildren_print _ (List.ofFn ch) (g + 1) rest hchild hfuel,
            Option.map_some, Rose.ofList_ofFn]) r

/-- The retraction law for the readable spelling: printing a rose tree
and parsing the result returns that tree. -/
theorem parse_print {k : Nat} (r : Rose k) : parse k (print r) = some r := by
  unfold parse
  rw [skipWs_print, show print r = print r ++ [] by simp,
    parseAux_print r _ [] (by simp) (by simp), skipWs_nil]

/-! ## The generic corollaries, instantiated here -/

/-- `Geb.Retraction` at the readable spelling. -/
theorem retraction (k : Nat) : Retraction (parse k) (print (k := k)) :=
  parse_print

/-- `Geb.format_idem` at the readable spelling. -/
theorem format_idem (k : Nat) (c : List Char) :
    (format (parse k) print c).bind (format (parse k) print)
      = format (parse k) print c :=
  Geb.format_idem _ _ (retraction k) c

/-- `Geb.print_injective` at the readable spelling. -/
theorem print_injective (k : Nat) : Function.Injective (print (k := k)) :=
  Geb.print_injective _ _ (retraction k)

/-! ## The `Ast` composites -/

/-- The readable spelling of an `Ast k`, through the rose bijection. -/
def printViaRose {k : Nat} (a : Ast k) : List Char := print a.toRose

/-- The parser matching `printViaRose`. -/
def parseViaRose (k : Nat) (cs : List Char) : Option (Ast k) :=
  (parse k cs).map Ast.ofRose

/-- The retraction law for the `Ast` composites, transported along the
rose retraction by `Ast.ofRose_toRose`. -/
theorem parseViaRose_printViaRose {k : Nat} (a : Ast k) :
    parseViaRose k (printViaRose a) = some a := by
  rw [parseViaRose, printViaRose, parse_print, Option.map_some, Ast.ofRose_toRose]

end Rsexp
end Geb

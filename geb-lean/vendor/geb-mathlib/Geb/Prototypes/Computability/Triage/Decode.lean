/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Triage.Code

set_option doc.verso true

/-!
# Recognizing triage expressions among binary-tree bitstrings

The tokenizer consumes one bit per transition, retaining at most seven pending
header bits. The stack decoder then checks constructor arities and the prohibition
on applications below values. Acceptance requires exactly one complete expression.

## Main definitions

* {lit}`tokenize` recognizes the constructor prefix codes.
* {lit}`decode` returns the represented expression or rejects the word.
* {lit}`recognize` is the Boolean triage recognizer.

## Main statements

* {lit}`decode_encode` and {lit}`encode_of_decode` establish exact round trips.
* {lit}`recognize_iff` characterizes acceptance by representability.
* {lit}`validBool_of_recognize` refines the existing binary-tree recognizer.

## Tags

tree calculus, bitstring, recognizer, parsing, prefix code
-/

@[expose] public section

namespace Geb.Triage

/-- Recognize one complete constructor header. -/
def readSymbol (w : List Bool) : Option Symbol :=
  if w = Symbol.code .leaf then some .leaf else
  if w = Symbol.code .stem then some .stem else
  if w = Symbol.code .fork then some .fork else
  if w = Symbol.code .app then some .app else none

/-- A recognized header is exactly the code of its returned symbol. -/
theorem code_of_readSymbol {w : List Bool} {s : Symbol} (h : readSymbol w = some s) :
    s.code = w := by
  unfold readSymbol at h
  split at h
  · cases h
    symm
    assumption
  · split at h
    · cases h
      symm
      assumption
    · split at h
      · cases h
        symm
        assumption
      · split at h
        · cases h
          symm
          assumption
        · cases h

/-- Reverse completed tokens and the incomplete header; rejection is absorbing. -/
abbrev TokenState := Option (List Symbol × List Bool)

/-- Consume one bit. An incomplete header may contain at most seven bits. -/
def tokenStep (st : TokenState) (b : Bool) : TokenState := do
  let (ss, buf) ← st
  let next := buf ++ [b]
  match readSymbol next with
  | some s => pure (s :: ss, [])
  | none => if next.length < 8 then pure (ss, next) else none

/-- The consumed prefix represented by a live tokenizer state. -/
def tokenWord (ss : List Symbol) (buf : List Bool) : List Bool :=
  ss.reverse.flatMap Symbol.code ++ buf

/-- Each live tokenizer transition accounts for precisely its input bit. -/
theorem tokenStep_sound (ss : List Symbol) (buf : List Bool) (b : Bool)
    (ss' : List Symbol) (buf' : List Bool)
    (h : tokenStep (some (ss, buf)) b = some (ss', buf')) :
    tokenWord ss' buf' = tokenWord ss buf ++ [b] := by
  simp only [tokenStep, bind, Option.bind] at h
  cases hr : readSymbol (buf ++ [b]) with
  | some s =>
    simp only [hr] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [tokenWord, code_of_readSymbol hr, List.append_assoc]
  | none =>
    simp only [hr] at h
    split at h
    · cases h
      simp [tokenWord, List.append_assoc]
    · cases h

/-- Tokenizing a complete symbol starts the next header at an empty buffer. -/
theorem foldl_tokenStep_code (s : Symbol) (ss : List Symbol) :
    s.code.foldl tokenStep (some (ss, [])) = some (s :: ss, []) := by
  cases s <;> rfl

/-- The tokenizer's live state spells its entire consumed input. -/
theorem foldl_tokenStep_sound (w : List Bool) : ∀ ss buf ss' buf',
    w.foldl tokenStep (some (ss, buf)) = some (ss', buf') →
      tokenWord ss' buf' = tokenWord ss buf ++ w := by
  refine List.rec ?_ ?_ w
  · intro ss buf ss' buf' h
    cases h
    simp
  · intro b w ih ss buf ss' buf' h
    cases hs : tokenStep (some (ss, buf)) b with
    | none =>
      have hn : ∀ v : List Bool, v.foldl tokenStep none = none :=
        List.rec rfl (fun _ _ h ↦ h)
      simp only [List.foldl_cons, hs, hn] at h
      cases h
    | some pair =>
      obtain ⟨ts, rest⟩ := pair
      have hw : w.foldl tokenStep (some (ts, rest)) = some (ss', buf') := by
        simpa only [List.foldl_cons, hs] using h
      rw [ih ts rest ss' buf' hw, tokenStep_sound ss buf b ts rest hs]
      simp [List.append_assoc]

/-- Tokenization inverts the spelling of any complete token sequence. -/
theorem foldl_tokenStep_codes (ts : List Symbol) : ∀ ss,
    (ts.flatMap Symbol.code).foldl tokenStep (some (ss, [])) =
      some (ts.reverse ++ ss, []) :=
  List.rec (fun _ ↦ rfl) (fun s ts ih ss ↦ by
    simp only [List.flatMap_cons, List.foldl_append, foldl_tokenStep_code, ih]
    simp [List.append_assoc]) ts

/-- Split a word into constructor tokens, rejecting incomplete headers. -/
def tokenize (w : List Bool) : Option (List Symbol) :=
  match w.foldl tokenStep (some ([], [])) with
  | some (ss, []) => some ss.reverse
  | _ => none

/-- Tokenization is a left inverse to complete token spelling. -/
@[simp] theorem tokenize_codes (ss : List Symbol) :
    tokenize (ss.flatMap Symbol.code) = some ss := by
  simp [tokenize, foldl_tokenStep_codes]

/-- Successful tokenization accounts for every input bit. -/
theorem codes_of_tokenize {w : List Bool} {ss : List Symbol} (h : tokenize w = some ss) :
    ss.flatMap Symbol.code = w := by
  unfold tokenize at h
  cases ht : w.foldl tokenStep (some ([], [])) with
  | none => simp [ht] at h
  | some pair =>
    obtain ⟨ts, buf⟩ := pair
    cases buf with
    | cons b buf => simp [ht] at h
    | nil =>
      simp only [ht, Option.some.injEq] at h
      subst ss
      simpa [tokenWord] using foldl_tokenStep_sound w [] [] ts [] ht

/-- Decode exactly one well-formed triage expression, rejecting malformed input. -/
def decode (w : List Bool) : Option Expr := do
  let ss ← tokenize w
  let st ← runSymbols ss []
  match st with
  | [e] => some e
  | _ => none

/-- Decoding an encoded expression returns that expression. -/
@[simp] theorem decode_encode (e : Expr) : decode e.encode = some e := by
  simp [decode, e.encode_eq_symbols, runSymbols_expr]

/-- A successful decode is a complete account of the input bitstring. -/
theorem encode_of_decode {w : List Bool} {e : Expr} (h : decode w = some e) :
    e.encode = w := by
  unfold decode at h
  cases ht : tokenize w with
  | none => simp [ht] at h
  | some ss =>
    cases hr : runSymbols ss [] with
    | none => simp [ht, hr] at h
    | some st =>
      cases st with
      | nil => simp [ht, hr] at h
      | cons x st =>
        cases st with
        | cons _ _ => simp [ht, hr] at h
        | nil =>
          have hxe : x = e := by simpa [ht, hr] using h
          subst e
          have he : x.symbols = ss := by
            simpa [stackSymbols] using runSymbols_sound ss [] [x] hr
          rw [x.encode_eq_symbols, he]
          exact codes_of_tokenize ht

/-- The representation is injective. -/
theorem Expr.encode_injective : Function.Injective Expr.encode := fun e f h ↦
  Option.some.inj (by rw [← decode_encode e, h, decode_encode])

/-- Boolean recognition of the triage-expression subset. -/
def recognize (w : List Bool) : Bool := (decode w).isSome

/-- Recognition is precisely existence of a represented triage expression. -/
theorem recognize_iff (w : List Bool) : recognize w = true ↔ ∃ e : Expr, e.encode = w := by
  constructor
  · intro h
    cases hd : decode w with
    | none => simp [recognize, hd] at h
    | some e => exact ⟨e, encode_of_decode hd⟩
  · rintro ⟨e, rfl⟩
    simp [recognize]

/-- Triage recognition refines the established binary-tree recognition. -/
theorem validBool_of_recognize {w : List Bool} (h : recognize w = true) :
    BitTree.validBool w = true := by
  obtain ⟨e, rfl⟩ := (recognize_iff w).mp h
  exact e.validBool_encode

end Geb.Triage

/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Kernel.Reader

set_option doc.verso true

/-!
# The printer of kernel terms

The printer writes a kernel term as an S-expression of the kernel's readable syntax, which the
reader resolves back to the term. The printer is partial: it writes nothing for a term that is not
well formed ({lit}`TermWf`), a variable or reference out of range among them, or for names of
definitions that are repeated or could be read as something else ({lit}`namesOk`), so the
retraction law holds of whatever it writes, without hypotheses: {lit}`printTerm? t = some e`
implies {lit}`resolve e = some t` ({lit}`resolve_of_printTerm?`). Its program form reads the
printed definitions of a bundle back to the bundle ({lit}`readForms_printProgram`), each
definition referring to those before it by name, and every well-formed bundle is printed
({lit}`isSome_printProgram`). A variable is written as the
name of its binder, {lit}`_d` for the binder at depth {lit}`d`; an abstraction as
{lit}`(lam (_d A) body)`, its type written structurally; an application as {lit}`(f x)`; a
reference and a primitive by name; a quoted leaf as its numeral and another quoted tree as a
datum. The printed term uses no abbreviation, so it reads under any; the printer serves
generated code and decompilation, while the formatter, whose retraction is at the level of
documents, keeps what a person wrote.

## Main definitions

* {lit}`printType`, {lit}`printDatum` — types and quoted trees.
* {lit}`printTerm`, {lit}`printTerm?` — terms, on any tree and on well-formed terms alone.
* {lit}`printProgram` — the definitions of a well-formed bundle.
* {lit}`TermWf`, {lit}`nameOk`, {lit}`namesOk`, {lit}`ProgramWf` — the well-formed terms, names
  and bundles.

## Main statements

* {lit}`resolve_of_printTerm?` — the reader retracts the printer.
* {lit}`readForms_printProgram` — the reader retracts the printer on programs.
* {lit}`isSome_printProgram` — the printer prints every well-formed bundle.

## Tags

printer, reader, retraction, decompilation
-/

@[expose] public section

namespace Geb.Kernel

/-! ## Printing -/

/-- An atom of characters. -/
def atomS (s : List Char) : SExp := RoseTree.node (some s) []

/-- A list of S-expressions. -/
def listS (cs : List SExp) : SExp := RoseTree.node none cs

/-- A numeral's atom. -/
def numeralS (n : ℕ) : SExp := atomS (Csexp.decOf n)

/-- The name of the binder at a depth: an underscore and the depth's numeral. -/
def binderName (d : ℕ) : List Char := '_' :: Csexp.decOf d

/-- The names a term under binders to a depth sees, the innermost first: the scope of the reader
at that depth. -/
def scopeOf (d : ℕ) : List (List Char) := (List.range d).reverse.map binderName

/-- One node of a type written structurally, from its children's writings. -/
def printTypeStep (l : ℕ) (rs : List SExp) : SExp :=
  if l = Label.tyTree then atomS ['T']
  else if l = Label.tyUnit then atomS ['U', 'n', 'i', 't']
  else if l = Label.tyProd then listS (atomS ['P', 'r', 'o', 'd'] :: rs)
  else if l = Label.tyArrow then listS (atomS ['A', 'r', 'r', 'o', 'w'] :: rs)
  else listS (atomS ['L', 'i', 's', 't'] :: rs)

/-- A type written structurally: {lit}`T`, {lit}`Unit`, and the lists headed by {lit}`Prod`,
{lit}`Arrow` and {lit}`List`. -/
def printType : Tree → SExp := RoseTree.elim printTypeStep

/-- A quoted tree as a datum: a leaf as its label's numeral, and a node of children as the list
of its label's numeral and its children's data. -/
def printDatum : Tree → SExp :=
  RoseTree.elim fun l rs ↦ if rs.isEmpty then numeralS l else listS (numeralS l :: rs)

/-- One node of a term printed, from its children with their printings, under binders to a
depth, given the names of the definitions. -/
def printStep (defs : List (List Char)) (l : ℕ) (rs : List (Tree × (ℕ → SExp))) (d : ℕ) :
    SExp :=
  let cs := rs.map Prod.fst
  let ps := rs.map fun r ↦ r.2 d
  if l = Label.var then atomS (binderName (d - 1 - ((cs.head?.map RoseTree.label).getD 0)))
  else if l = Label.lam then
    match rs with
    | [(A, _), (_, b)] => listS [atomS ['l', 'a', 'm'], listS [atomS (binderName d), printType A],
        b (d + 1)]
    | _ => listS []
  else if l = Label.app then listS ps
  else if l = Label.unit then atomS ['u', 'n', 'i', 't']
  else if l = Label.pair then listS (atomS ['p', 'a', 'i', 'r'] :: ps)
  else if l = Label.fst then listS (atomS ['f', 's', 't'] :: ps)
  else if l = Label.snd then listS (atomS ['s', 'n', 'd'] :: ps)
  else if l = Label.cond then listS (atomS ['i', 'f'] :: ps)
  else if l = Label.cons then listS (atomS ['c', 'o', 'n', 's'] :: ps)
  else if l = Label.quote then
    match cs with
    | [c] => if c.children.isEmpty then numeralS c.label
        else listS [atomS ['q', 'u', 'o', 't', 'e'], printDatum c]
    | _ => listS []
  else if l = Label.nil then listS (atomS ['n', 'i', 'l'] :: cs.map printType)
  else if l = Label.fold then listS (atomS ['f', 'o', 'l', 'd'] :: cs.map printType)
  else if l = Label.para then listS (atomS ['p', 'a', 'r', 'a'] :: cs.map printType)
  else if l = Label.iter then listS (atomS ['i', 't', 'e', 'r'] :: cs.map printType)
  else if l = Label.foldr then listS (atomS ['f', 'o', 'l', 'd', 'r'] :: cs.map printType)
  else if l = Label.lcase then listS (atomS ['l', 'c', 'a', 's', 'e'] :: cs.map printType)
  else if l = Label.prim then
    atomS (primNames.getD ((cs.head?.map RoseTree.label).getD 0) [])
  else atomS (defs.getD ((cs.head?.map RoseTree.label).getD 0) [])

/-- A term printed under binders to a depth, given the names of the definitions. -/
def printTerm (defs : List (List Char)) (t : Tree) (d : ℕ) : SExp :=
  RoseTree.para (printStep defs) t d

/-! ## Numerals and names -/

/-- The digits' step of {name}`numeral?` over the characters of decimal digits, from a value,
appends them to it. -/
theorem foldl_digits : ∀ (ds : List ℕ) (a : ℕ), (∀ d ∈ ds, d < 10) →
    (ds.map Csexp.digitChar).foldl (fun n c ↦ n.bind fun n ↦
      if c.isDigit then some (10 * n + (c.toNat - '0'.toNat)) else none) (some a) =
    some (ds.foldl (fun n d ↦ 10 * n + d) a) :=
  List.rec (fun _ _ ↦ rfl) fun d ds ih a h ↦ by
    have hd : d < 10 := h d List.mem_cons_self
    have hc : (Csexp.digitChar d).isDigit = true ∧
        (Csexp.digitChar d).toNat - '0'.toNat = d := by
      unfold Csexp.digitChar
      match d, hd with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => exact ⟨rfl, rfl⟩
    simp only [List.map_cons, List.foldl_cons, Option.bind_some, hc.1, hc.2, ite_true]
    exact ih _ fun e he ↦ h e (List.mem_cons_of_mem d he)

/-- Digits read most significant first are the value of the digits least significant first. -/
theorem foldl_reverse_digits : ∀ ds : List ℕ,
    ds.reverse.foldl (fun n d ↦ 10 * n + d) 0 = Csexp.ofLE ds :=
  List.rec rfl fun d ds ih ↦ by
    rw [List.reverse_cons, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, Csexp.ofLE]
    omega

/-- A numeral reads back to its number. -/
theorem numeral?_decOf (n : ℕ) : numeral? (Csexp.decOf n) = some n := by
  unfold Csexp.decOf
  by_cases h : n = 0
  · subst h; rfl
  · simp only [h, ↓reduceIte]
    have hne : ((Csexp.digitsLE n).reverse.map Csexp.digitChar).isEmpty = false := by
      cases hd : (Csexp.digitsLE n).reverse with
      | nil => exact absurd (List.reverse_eq_nil_iff.mp hd) (Csexp.digitsLE_ne_nil h)
      | cons _ _ => rfl
    unfold numeral?
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    rw [foldl_digits _ 0 fun d hd ↦ Csexp.digitsLE_lt n d (List.mem_reverse.mp hd),
      foldl_reverse_digits, Csexp.ofLE_digitsLE]

/-- A binder's name is no numeral. -/
theorem numeral?_binderName (d : ℕ) : numeral? (binderName d) = none := by
  unfold numeral? binderName
  have : ('_' : Char).isDigit = false := rfl
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.foldl_cons,
    Option.bind_some, this]
  generalize Csexp.decOf d = l
  refine List.rec rfl (fun _ _ ih ↦ ?_) l
  exact ih

/-! ## Well-formed terms -/

/-- One node's well-formedness under binders to a depth, from its children's: a variable over a
leaf below the depth, an abstraction over a type and a body well formed one level deeper, an
application of two terms, the unit without children, a pair, projection, conditional or
construction of terms, a quotation of any tree, a constant over types, and a primitive or a
reference over a leaf in range. -/
def wfStep (nDefs : ℕ) (l : ℕ) (rs : List (Tree × (ℕ → Bool))) (d : ℕ) : Bool :=
  let cs := rs.map Prod.fst
  let leafBelow (n : ℕ) := match cs with
    | [c] => c.children.isEmpty && decide (c.label < n)
    | _ => false
  if l = Label.var then leafBelow d
  else if l = Label.lam then
    match rs with
    | [(A, _), (_, b)] => Ty.IsTy A && b (d + 1)
    | _ => false
  else if l = Label.app then cs.length == 2 && rs.all (·.2 d)
  else if l = Label.unit then cs.isEmpty
  else if l = Label.pair ∨ l = Label.fst ∨ l = Label.snd ∨ l = Label.cond ∨ l = Label.cons then
    rs.all (·.2 d)
  else if l = Label.quote then cs.length == 1
  else if l = Label.nil ∨ l = Label.fold ∨ l = Label.para ∨ l = Label.iter then
    cs.length == 1 && cs.all Ty.IsTy
  else if l = Label.foldr ∨ l = Label.lcase then cs.length == 2 && cs.all Ty.IsTy
  else if l = Label.prim then leafBelow primNames.length
  else if l = Label.ref then leafBelow nDefs
  else false

/-- Whether a term is well formed under binders to a depth, given the number of definitions it
may refer to. -/
def TermWf (nDefs : ℕ) (t : Tree) (d : ℕ) : Bool := RoseTree.para (wfStep nDefs) t d

/-- The printing of a node. -/
theorem printTerm_node (defs : List (List Char)) (l : ℕ) (cs : List Tree) (d : ℕ) :
    printTerm defs (RoseTree.node l cs) d =
      printStep defs l (cs.map fun c ↦ (c, printTerm defs c)) d := by
  simp only [printTerm, RoseTree.para_node]
  rfl

/-- The well-formedness of a node. -/
theorem termWf_node (nDefs l : ℕ) (cs : List Tree) (d : ℕ) :
    TermWf nDefs (RoseTree.node l cs) d =
      wfStep nDefs l (cs.map fun c ↦ (c, TermWf nDefs c)) d := by
  simp only [TermWf, RoseTree.para_node]
  rfl

/-- The resolution of a node. -/
theorem resolve_node (tys : TypeNames) (defs : List (List Char)) (a : Option (List Char))
    (cs : List SExp) (scope : List (List Char)) :
    resolve tys defs (RoseTree.node a cs) scope =
      resolveStep tys defs a (cs.map fun c ↦ (c, resolve tys defs c)) scope := by
  simp only [resolve, RoseTree.para_node]
  rfl

/-- The position of an element of a list without repetitions is its index. -/
theorem idxOf?_getElem {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List α), l.Nodup → ∀ (i : ℕ) (h : i < l.length), l.idxOf? l[i] = some i :=
  List.rec (fun _ _ h ↦ absurd h (Nat.not_lt_zero _)) fun x xs ih hnd i h ↦ by
    rw [List.idxOf?_cons]
    cases i with
    | zero => simp
    | succ j =>
      have hj : j < xs.length := Nat.lt_of_succ_lt_succ h
      have hne : x ≠ xs[j] := (List.nodup_cons.mp hnd).1 ∘ (· ▸ List.getElem_mem hj)
      have hb : (x == xs[j]) = false := beq_eq_false_iff_ne.mpr hne
      simp only [List.getElem_cons_succ, hb, Bool.false_eq_true, ↓reduceIte]
      rw [ih (List.nodup_cons.mp hnd).2 j hj]
      rfl

/-! ## Atoms -/

/-- Distinct depths have distinct binders' names. -/
theorem binderName_injective {a b : ℕ} (h : binderName a = binderName b) : a = b := by
  have h' : Csexp.decOf a = Csexp.decOf b := List.cons.inj h |>.2
  have := congrArg numeral? h'
  rw [numeral?_decOf, numeral?_decOf] at this
  exact Option.some.inj this

/-- The binder in a scope at a de Bruijn index. -/
theorem scopeOf_getElem (d i : ℕ) (h : i < (scopeOf d).length) :
    (scopeOf d)[i] = binderName (d - 1 - i) := by
  simp [scopeOf, List.getElem_reverse]

/-- A scope one binder deeper has that binder innermost. -/
theorem scopeOf_succ (d : ℕ) : scopeOf (d + 1) = binderName d :: scopeOf d := by
  simp [scopeOf, List.range_succ]

/-- The names in a scope are the names of binders above its depth. -/
theorem mem_scopeOf {n : List Char} {d : ℕ} (h : n ∈ scopeOf d) :
    ∃ k, k < d ∧ n = binderName k := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
  exact ⟨k, List.mem_range.mp (List.mem_reverse.mp hk), rfl⟩

/-- A scope repeats no name. -/
theorem scopeOf_nodup (d : ℕ) : (scopeOf d).Nodup :=
  Nat.rec List.nodup_nil (fun d ih ↦ by
    rw [scopeOf_succ]
    refine List.nodup_cons.mpr ⟨fun hm ↦ ?_, ih⟩
    obtain ⟨k, hk, he⟩ := mem_scopeOf hm
    exact absurd (binderName_injective he) (Nat.ne_of_gt hk)) d

/-- The names a program's definitions may take, apart from distinctness: no numeral, no binder's
name, and no reserved name. -/
def NameOk (n : List Char) : Prop :=
  numeral? n = none ∧ (∀ k, n ≠ binderName k) ∧ n ∉ reservedNames

/-- Whether a name is a binder's: an underscore followed by a numeral as the printer writes it. -/
def isBinderName (n : List Char) : Bool := (numeral? n.tail).any fun k ↦ binderName k == n

/-- A name is a binder's exactly when it is the name of the binder at some depth. -/
theorem isBinderName_iff (n : List Char) : isBinderName n = true ↔ ∃ k, n = binderName k := by
  constructor
  · intro h
    obtain ⟨k, -, hk⟩ := (Option.any_eq_true _ _).mp h
    exact ⟨k, (beq_iff_eq.mp hk).symm⟩
  · rintro ⟨k, rfl⟩
    rw [isBinderName, show (binderName k).tail = Csexp.decOf k from rfl, numeral?_decOf,
      Option.any_some]
    exact beq_iff_eq.mpr rfl

/-- Whether a name may be a definition's, decided. -/
def nameOk (n : List Char) : Bool :=
  (numeral? n).isNone && !isBinderName n && !reservedNames.contains n

/-- The decision of the names that may be definitions'. -/
theorem nameOk_iff (n : List Char) : nameOk n = true ↔ NameOk n := by
  rw [nameOk, Bool.and_eq_true, Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true',
    Bool.not_eq_true', Bool.eq_false_iff, Bool.eq_false_iff, and_assoc]
  unfold NameOk
  refine and_congr_right fun _ ↦
    and_congr ?_ (not_congr (List.contains_iff_mem (as := reservedNames) (a := n)))
  exact ⟨fun h k hk ↦ h ((isBinderName_iff n).mpr ⟨k, hk⟩),
    fun h hb ↦ ((isBinderName_iff n).mp hb).elim h⟩

/-- Whether names may be a program's definitions': distinct, and each a definition's. -/
def namesOk (defs : List (List Char)) : Bool := decide defs.Nodup && defs.all nameOk

/-- The decision of the names that may be a program's definitions'. -/
theorem namesOk_iff (defs : List (List Char)) :
    namesOk defs = true ↔ defs.Nodup ∧ ∀ n ∈ defs, NameOk n := by
  rw [namesOk, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true]
  exact and_congr_right fun _ ↦ forall₂_congr fun n _ ↦ nameOk_iff n

/-- A name that may be a definition's is no primitive's name. -/
theorem NameOk.not_prim {n : List Char} (h : NameOk n) : n ∉ primNames :=
  fun hm ↦ h.2.2 (List.mem_append_right _ hm)

/-- A name that may be a definition's is not the unit's. -/
theorem NameOk.ne_unit {n : List Char} (h : NameOk n) : n ≠ ['u', 'n', 'i', 't'] :=
  fun he ↦ h.2.2 (he ▸ by decide)

/-- A variable's binder's name resolves to the variable. -/
theorem resolve_var (tys : TypeNames) (defs : List (List Char)) (d i : ℕ) (h : i < d) :
    resolve tys defs (atomS (binderName (d - 1 - i))) (scopeOf d) =
      some (mk Label.var [leaf i]) := by
  have hl : i < (scopeOf d).length := by simpa [scopeOf] using h
  have hi := idxOf?_getElem (scopeOf d) (scopeOf_nodup d) i hl
  rw [scopeOf_getElem] at hi
  simp only [atomS, resolve_node, resolveStep, numeral?_binderName, hi]

/-- A definition's name resolves to the reference to it. -/
theorem resolve_ref (tys : TypeNames) (defs : List (List Char)) (hnd : defs.Nodup)
    (hok : ∀ n ∈ defs, NameOk n) (d j : ℕ) (h : j < defs.length) :
    resolve tys defs (atomS defs[j]) (scopeOf d) = some (mk Label.ref [leaf j]) := by
  have hn := hok _ (List.getElem_mem h)
  have hs : (scopeOf d).idxOf? defs[j] = none :=
    List.idxOf?_eq_none_iff.mpr fun hm ↦ by
      obtain ⟨k, -, hk⟩ := mem_scopeOf hm
      exact hn.2.1 k hk
  simp only [atomS, resolve_node, resolveStep, hn.1, hs,
    idxOf?_getElem defs hnd j h]

/-- A binder's name begins with an underscore. -/
theorem head?_binderName (k : ℕ) : (binderName k).head? = some '_' := rfl

/-- What resolution asks of a primitive's name: it is no numeral, does not begin with an
underscore, and is found at its index among the primitives' names. -/
theorem primNames_facts (k : ℕ) (hk : k < primNames.length) :
    numeral? (primNames.getD k []) = none ∧ (primNames.getD k []).head? ≠ some '_' ∧
      primNames.idxOf? (primNames.getD k []) = some k := by
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _
  | 12, _ | 13, _ => exact ⟨rfl, by decide, rfl⟩

/-- A name that does not begin with an underscore is in no scope. -/
theorem idxOf?_scopeOf_of_head {n : List Char} (h : n.head? ≠ some '_') (d : ℕ) :
    (scopeOf d).idxOf? n = none :=
  List.idxOf?_eq_none_iff.mpr fun hm ↦ by
    obtain ⟨k, -, hk⟩ := mem_scopeOf hm
    exact h (hk ▸ head?_binderName k)

/-- A primitive's name resolves to the primitive. -/
theorem resolve_prim (tys : TypeNames) (defs : List (List Char)) (hok : ∀ n ∈ defs, NameOk n)
    (d k : ℕ) (hk : k < primNames.length) :
    resolve tys defs (atomS (primNames.getD k [])) (scopeOf d) =
      some (mk Label.prim [leaf k]) := by
  obtain ⟨hn, hh, hp⟩ := primNames_facts k hk
  have hlen : k < primNames.length := hk
  have hmem : primNames.getD k [] ∈ primNames := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
    exact List.getElem_mem hlen
  have hd : defs.idxOf? (primNames.getD k []) = none :=
    List.idxOf?_eq_none_iff.mpr fun hm ↦ (hok _ hm).not_prim hmem
  simp only [atomS, resolve_node, resolveStep, hn, idxOf?_scopeOf_of_head hh, hd, hp]

/-- The unit's atom resolves to the unit. -/
theorem resolve_unit (tys : TypeNames) (defs : List (List Char)) (hok : ∀ n ∈ defs, NameOk n)
    (d : ℕ) : resolve tys defs (atomS ['u', 'n', 'i', 't']) (scopeOf d) =
      some (mk Label.unit []) := by
  have hd : defs.idxOf? ['u', 'n', 'i', 't'] = none :=
    List.idxOf?_eq_none_iff.mpr fun hm ↦ (hok _ hm).ne_unit rfl
  have hp : primNames.idxOf? ['u', 'n', 'i', 't'] = none := rfl
  have hn : numeral? ['u', 'n', 'i', 't'] = none := rfl
  have hs : (scopeOf d).idxOf? ['u', 'n', 'i', 't'] = none :=
    idxOf?_scopeOf_of_head (n := ['u', 'n', 'i', 't']) (by decide) d
  simp only [atomS, resolve_node, resolveStep, hn, hs, hd, hp]
  rfl

/-- A numeral's atom resolves to the quoted leaf. -/
theorem resolve_numeral (tys : TypeNames) (defs : List (List Char)) (scope : List (List Char))
    (n : ℕ) : resolve tys defs (numeralS n) scope = some (mk Label.quote [leaf n]) := by
  simp only [numeralS, atomS, resolve_node, resolveStep, numeral?_decOf]

/-! ## Types and data -/

/-- A product type is the node of its label over its two types. -/
theorem tProd_eq (A B : Tree) : tProd A B = RoseTree.node Label.tyProd [A, B] :=
  (RoseTree.node_eq_mk _ [A, B] rfl _ fun i ↦ match i with | 0 => rfl | 1 => rfl).symm

/-- A function type is the node of its label over its two types. -/
theorem tArrow_eq (A B : Tree) : tArrow A B = RoseTree.node Label.tyArrow [A, B] :=
  (RoseTree.node_eq_mk _ [A, B] rfl _ fun i ↦ match i with | 0 => rfl | 1 => rfl).symm

/-- A list type is the node of its label over its type. -/
theorem tList_eq (A : Tree) : tList A = RoseTree.node Label.tyList [A] :=
  (RoseTree.node_eq_mk _ [A] rfl _ fun i ↦ match i with | 0 => rfl).symm

/-- A type's shapes: the base type, the unit, and a product, function or list type of types. -/
theorem isTy_cases {A : Tree} (h : Ty.IsTy A = true) :
    A = leaf Label.tyTree ∨ A = leaf Label.tyUnit ∨
      (∃ a b, A = RoseTree.node Label.tyProd [a, b] ∧ Ty.IsTy a = true ∧ Ty.IsTy b = true) ∨
      (∃ a b, A = RoseTree.node Label.tyArrow [a, b] ∧ Ty.IsTy a = true ∧ Ty.IsTy b = true) ∨
      (∃ a, A = RoseTree.node Label.tyList [a] ∧ Ty.IsTy a = true) := by
  rw [← RoseTree.node_label_children A] at h ⊢
  generalize A.label = l, A.children = cs at h ⊢
  unfold Ty.IsTy at h
  rw [RoseTree.elim_node] at h
  match l, cs, h with
  | 0, [], _ => exact Or.inl rfl
  | 1, [], _ => exact Or.inr (Or.inl rfl)
  | 2, [a, b], h => exact Or.inr (Or.inr (Or.inl ⟨a, b, rfl, (Bool.and_eq_true _ _ ▸ h).1,
      (Bool.and_eq_true _ _ ▸ h).2⟩))
  | 3, [a, b], h => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, rfl,
      (Bool.and_eq_true _ _ ▸ h).1, (Bool.and_eq_true _ _ ▸ h).2⟩)))
  | 4, [a], h => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, rfl, h⟩)))

/-- The writing of a node of a type. -/
theorem printType_node (l : ℕ) (cs : List Tree) :
    printType (RoseTree.node l cs) = printTypeStep l (cs.map printType) :=
  RoseTree.elim_node _ _ _

/-- The reading of a list of S-expressions as a type. -/
theorem elim_readTypeStep_listS (tys : TypeNames) (cs : List SExp) :
    RoseTree.elim (readTypeStep tys) (listS cs) =
      readTypeStep tys none (cs.map (RoseTree.elim (readTypeStep tys))) :=
  RoseTree.elim_node _ _ _

/-- A product type's writing. -/
theorem printType_prod (a b : Tree) : printType (RoseTree.node Label.tyProd [a, b]) =
    listS [atomS ['P', 'r', 'o', 'd'], printType a, printType b] := by
  rw [printType_node]; rfl

/-- A function type's writing. -/
theorem printType_arrow (a b : Tree) : printType (RoseTree.node Label.tyArrow [a, b]) =
    listS [atomS ['A', 'r', 'r', 'o', 'w'], printType a, printType b] := by
  rw [printType_node]; rfl

/-- A list type's writing. -/
theorem printType_list (a : Tree) : printType (RoseTree.node Label.tyList [a]) =
    listS [atomS ['L', 'i', 's', 't'], printType a] := by
  rw [printType_node]; rfl

/-- A printed type reads back to the type, with the atom it is if it is one. -/
theorem elim_readTypeStep_printType (tys : TypeNames) : ∀ A : Tree, Ty.IsTy A = true →
    RoseTree.elim (readTypeStep tys) (printType A) =
      ((printType A).label, some A) :=
  RoseTree.ind fun l cs ih h ↦ by
    rcases isTy_cases h with h0 | h1 | ⟨a, b, he, ha, hb⟩ | ⟨a, b, he, ha, hb⟩ | ⟨a, he, ha⟩
    · rw [h0]; rfl
    · rw [h1]; rfl
    · have hcs : cs = [a, b] := by simpa using congrArg RoseTree.children he
      subst hcs
      rw [he, printType_prod, elim_readTypeStep_listS]
      simp only [List.map_cons, List.map_nil, ih a (by simp) ha, ih b (by simp) hb]
      rw [← tProd_eq]
      rfl
    · have hcs : cs = [a, b] := by simpa using congrArg RoseTree.children he
      subst hcs
      rw [he, printType_arrow, elim_readTypeStep_listS]
      simp only [List.map_cons, List.map_nil, ih a (by simp) ha, ih b (by simp) hb]
      rw [← tArrow_eq]
      rfl
    · have hcs : cs = [a] := by simpa using congrArg RoseTree.children he
      subst hcs
      rw [he, printType_list, elim_readTypeStep_listS]
      simp only [List.map_cons, List.map_nil, ih a (by simp) ha]
      rw [← tList_eq]
      rfl

/-- A printed type reads back to the type, under any abbreviations. -/
theorem readType_printType (tys : TypeNames) (A : Tree) (h : Ty.IsTy A = true) :
    readType tys (printType A) = some A := by
  unfold readType
  rw [elim_readTypeStep_printType tys A h]

/-! ## Forms -/

/-- The keywords of the forms the reader resolves specially, as characters. -/
def formKeywords : List (List Char) :=
  [['l', 'a', 'm'], ['l', 'e', 't'], ['p', 'a', 'i', 'r'], ['f', 's', 't'], ['s', 'n', 'd'],
    ['i', 'f'], ['q', 'u', 'o', 't', 'e'], ['c', 'o', 'n', 's'], ['n', 'i', 'l'],
    ['f', 'o', 'l', 'd'], ['p', 'a', 'r', 'a'], ['i', 't', 'e', 'r'], ['f', 'o', 'l', 'd', 'r'],
    ['l', 'c', 'a', 's', 'e']]

/-- A list whose head is no form's keyword resolves as an application of its head to the rest. -/
theorem resolveStep_app (tys : TypeNames) (defs : List (List Char)) (h : SExp)
    (rh : List (List Char) → Option Tree) (rest : List (SExp × (List (List Char) → Option Tree)))
    (scope : List (List Char)) (hh : ∀ s, h.label = some s → s ∉ formKeywords) :
    resolveStep tys defs none ((h, rh) :: rest) scope =
      (do apps (← rh scope) (← rest.mapM fun (x : SExp × (List (List Char) → Option Tree)) ↦
        x.2 scope)) := by
  unfold resolveStep
  dsimp only
  split
  all_goals first
    | (exfalso; exact hh _ (by assumption) (by simp [formKeywords]))
    | rfl

/-- Whether an S-expression's atom, if it is one, is no form's keyword: a printed term's head
resolves as a term. -/
def HeadOk (e : SExp) : Prop := ∀ s, e.label = some s → s ∉ formKeywords

/-- A list is no keyword. -/
theorem headOk_listS (cs : List SExp) : HeadOk (listS cs) := fun _ h ↦ nomatch h

/-- An atom that is no keyword. -/
theorem headOk_atomS {n : List Char} (h : n ∉ formKeywords) : HeadOk (atomS n) :=
  fun _ hs ↦ Option.some.inj hs ▸ h

/-- A choice between S-expressions whose heads resolve as terms. -/
theorem headOk_ite {p : Prop} [Decidable p] {a b : SExp} (ha : HeadOk a) (hb : HeadOk b) :
    HeadOk (if p then a else b) := by
  split
  · exact ha
  · exact hb

/-- A binder's name is no keyword. -/
theorem binderName_not_mem_formKeywords (d : ℕ) : binderName d ∉ formKeywords := fun hm ↦ by
  have : ∀ k ∈ formKeywords, k.head? ≠ some '_' := by decide
  exact this _ hm (head?_binderName d)

/-- A name that is not reserved is no keyword. -/
theorem not_mem_formKeywords_of_reserved {n : List Char} (h : n ∉ reservedNames) :
    n ∉ formKeywords := fun hm ↦ by
  have : ∀ k ∈ formKeywords, k ∈ reservedNames := by decide
  exact h (this n hm)

/-- A numeral is no keyword. -/
theorem decOf_not_mem_formKeywords (n : ℕ) : Csexp.decOf n ∉ formKeywords := fun hm ↦ by
  have : ∀ k ∈ formKeywords, ∃ c ∈ k, Csexp.charDigit c = none := by decide
  obtain ⟨c, hc, hn⟩ := this _ hm
  have := Csexp.decOf_all_digits n c hc
  rw [hn] at this
  exact Bool.false_ne_true this

/-- An entry of a list of names that are no keywords, or the empty name, is no keyword. -/
theorem getD_not_mem_formKeywords {l : List (List Char)} (hl : ∀ n ∈ l, n ∉ formKeywords)
    (k : ℕ) : l.getD k [] ∉ formKeywords := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[k]? with
  | none => exact fun hm ↦ by revert hm; decide
  | some n => exact hl n (List.mem_of_getElem? h)

/-- A printed term's head resolves as a term. -/
theorem headOk_printTerm (defs : List (List Char)) (hok : ∀ n ∈ defs, NameOk n) (t : Tree)
    (d : ℕ) : HeadOk (printTerm defs t d) := by
  rw [← RoseTree.node_label_children t, printTerm_node]
  unfold printStep
  have hp : ∀ n ∈ primNames, n ∉ formKeywords := by decide
  have hd : ∀ n ∈ defs, n ∉ formKeywords := fun n hn ↦
    not_mem_formKeywords_of_reserved (hok n hn).2.2
  dsimp only
  repeat' refine headOk_ite ?_ ?_
  all_goals try split
  all_goals try split
  all_goals first
    | exact headOk_listS _
    | exact headOk_atomS (binderName_not_mem_formKeywords _)
    | exact headOk_atomS (decOf_not_mem_formKeywords _)
    | exact headOk_atomS (getD_not_mem_formKeywords hp _)
    | exact headOk_atomS (getD_not_mem_formKeywords hd _)
    | exact headOk_atomS (n := ['u', 'n', 'i', 't']) (by decide)

/-- A list of values each found by a partial function is found whole. -/
theorem mapM_map_eq_some {α β γ : Type} (h : γ → α) (f : α → Option β) (g : γ → β) :
    ∀ cs : List γ, (∀ c ∈ cs, f (h c) = some (g c)) → (cs.map h).mapM f = some (cs.map g) :=
  List.rec (fun _ ↦ rfl) fun c cs ih H ↦ by
    simp only [List.map_cons, List.mapM_cons, H c List.mem_cons_self,
      ih fun x hx ↦ H x (List.mem_cons_of_mem c hx)]
    rfl

/-! ## Data -/

/-- The writing of a node of a datum. -/
theorem printDatum_node (l : ℕ) (cs : List Tree) :
    printDatum (RoseTree.node l cs) =
      if (cs.map printDatum).isEmpty then numeralS l else listS (numeralS l :: cs.map printDatum) :=
  RoseTree.elim_node _ _ _

/-- The lists of one tree each, joined, are the trees. -/
theorem flatten_map_singleton {α : Type} : ∀ l : List α, (l.map fun x ↦ [x]).flatten = l :=
  List.rec rfl fun x l ih ↦ by rw [List.map_cons, List.flatten_cons, ih]; rfl

/-- A printed datum contributes the tree it prints. -/
theorem elim_datumStep_printDatum :
    ∀ t : Tree, (RoseTree.elim datumStep (printDatum t)).2 = some [t] :=
  RoseTree.ind fun l cs ih ↦ by
    rw [printDatum_node]
    cases cs with
    | nil =>
      simp only [List.map_nil, List.isEmpty_nil, ↓reduceIte, numeralS, atomS, RoseTree.elim_node]
      simp only [datumStep, numeral?_decOf]
      rfl
    | cons c cs =>
      simp only [List.map_cons, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, listS,
        numeralS, atomS, RoseTree.elim_node]
      simp only [datumStep, numeral?_decOf]
      rw [show RoseTree.elim datumStep (printDatum c) ::
          (cs.map printDatum).map (RoseTree.elim datumStep) =
          (c :: cs).map (RoseTree.elim datumStep ∘ printDatum) by
            rw [List.map_cons, List.map_map]; rfl,
        mapM_map_eq_some (RoseTree.elim datumStep ∘ printDatum) Prod.snd (fun x ↦ [x]) (c :: cs)
          fun x hx ↦ ih x hx]
      simp only [Option.map_some, flatten_map_singleton]

/-- A quoted tree that is not a leaf reads back from its printed datum. -/
theorem readDatum_printDatum (l : ℕ) (cs : List Tree) (h : cs ≠ []) :
    readDatum (printDatum (RoseTree.node l cs)) = some (RoseTree.node l cs) := by
  have hl : (printDatum (RoseTree.node l cs)).label = none := by
    rw [printDatum_node]
    cases cs with
    | nil => exact absurd rfl h
    | cons => rfl
  unfold readDatum
  rw [hl]
  simp only [elim_datumStep_printDatum]

/-! ## The retraction -/

/-- The shapes of a well-formed node, with what the retraction needs of each. -/
theorem termWf_cases {nDefs l : ℕ} {cs : List Tree} {d : ℕ}
    (h : TermWf nDefs (RoseTree.node l cs) d = true) :
    (l = Label.var ∧ ∃ c, cs = [c] ∧ c.children = [] ∧ c.label < d) ∨
    (l = Label.lam ∧ ∃ A b, cs = [A, b] ∧ Ty.IsTy A = true ∧ TermWf nDefs b (d + 1) = true) ∨
    (l = Label.app ∧ ∃ f x, cs = [f, x] ∧ TermWf nDefs f d = true ∧ TermWf nDefs x d = true) ∨
    (l = Label.unit ∧ cs = []) ∨
    ((l = Label.pair ∨ l = Label.fst ∨ l = Label.snd ∨ l = Label.cond ∨ l = Label.cons) ∧
      ∀ c ∈ cs, TermWf nDefs c d = true) ∨
    (l = Label.quote ∧ ∃ c, cs = [c]) ∨
    ((l = Label.nil ∨ l = Label.fold ∨ l = Label.para ∨ l = Label.iter) ∧
      ∃ A, cs = [A] ∧ Ty.IsTy A = true) ∨
    ((l = Label.foldr ∨ l = Label.lcase) ∧
      ∃ A B, cs = [A, B] ∧ Ty.IsTy A = true ∧ Ty.IsTy B = true) ∨
    (l = Label.prim ∧ ∃ c, cs = [c] ∧ c.children = [] ∧ c.label < primNames.length) ∨
    (l = Label.ref ∧ ∃ c, cs = [c] ∧ c.children = [] ∧ c.label < nDefs) := by
  rw [termWf_node] at h
  unfold wfStep at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  · left; refine ⟨h1, ?_⟩
    match cs, h with
    | [c], h =>
      have h' : c.children = [] ∧ c.label < d := by
        simpa only [List.map_cons, List.map_nil, Bool.and_eq_true, List.isEmpty_iff,
          decide_eq_true_eq] using h
      exact ⟨c, rfl, h'.1, h'.2⟩
  · right; left; refine ⟨h2, ?_⟩
    match cs, h with
    | [A, b], h =>
      have h' : Ty.IsTy A = true ∧ TermWf nDefs b (d + 1) = true := by
        simpa only [List.map_cons, List.map_nil, Bool.and_eq_true] using h
      exact ⟨A, b, rfl, h'.1, h'.2⟩
  · right; right; left; refine ⟨h3, ?_⟩
    match cs, h with
    | [f, x], h =>
      have h' : TermWf nDefs f d = true ∧ TermWf nDefs x d = true := by
        simpa only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, zero_add,
          Nat.reduceAdd, Nat.reduceBEq, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and,
          Bool.and_eq_true] using h
      exact ⟨f, x, rfl, h'.1, h'.2⟩
  · right; right; right; left; refine ⟨h4, ?_⟩
    simpa only [List.map_map, List.isEmpty_map, List.isEmpty_iff] using h
  · right; right; right; right; left; refine ⟨h5, ?_⟩
    simpa only [List.all_map, List.all_eq_true, Function.comp_apply] using h
  · right; right; right; right; right; left; refine ⟨h6, ?_⟩
    match cs, h with
    | [c], _ => exact ⟨c, rfl⟩
  · right; right; right; right; right; right; left; refine ⟨h7, ?_⟩
    match cs, h with
    | [A], h => exact ⟨A, rfl, by simpa only [List.map_cons, List.map_nil, List.length_cons,
      List.length_nil, zero_add, Nat.reduceBEq, List.all_cons, List.all_nil, Bool.and_true,
      Bool.true_and] using h⟩
  · right; right; right; right; right; right; right; left; refine ⟨h8, ?_⟩
    match cs, h with
    | [A, B], h =>
      have h' : Ty.IsTy A = true ∧ Ty.IsTy B = true := by
        simpa only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, zero_add,
          Nat.reduceAdd, Nat.reduceBEq, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and,
          Bool.and_eq_true] using h
      exact ⟨A, B, rfl, h'.1, h'.2⟩
  · right; right; right; right; right; right; right; right; left; refine ⟨h9, ?_⟩
    match cs, h with
    | [c], h =>
      have h' : c.children = [] ∧ c.label < primNames.length := by
        simpa only [List.map_cons, List.map_nil, Bool.and_eq_true, List.isEmpty_iff,
          decide_eq_true_eq] using h
      exact ⟨c, rfl, h'.1, h'.2⟩
  · right; right; right; right; right; right; right; right; right; refine ⟨h10, ?_⟩
    match cs, h with
    | [c], h =>
      have h' : c.children = [] ∧ c.label < nDefs := by
        simpa only [List.map_cons, List.map_nil, Bool.and_eq_true, List.isEmpty_iff,
          decide_eq_true_eq] using h
      exact ⟨c, rfl, h'.1, h'.2⟩

/-- A leaf is the leaf of its label. -/
theorem leaf_label {c : Tree} (h : c.children = []) : leaf c.label = c := by
  rw [leaf, ← h, RoseTree.node_label_children]

/-- The reader retracts the printer: a well-formed term printed under binders to a depth
resolves, in the scope of those binders, to itself. -/
theorem resolve_printTerm (tys : TypeNames) (defs : List (List Char)) (hnd : defs.Nodup)
    (hok : ∀ n ∈ defs, NameOk n) : ∀ (t : Tree) (d : ℕ), TermWf defs.length t d = true →
      resolve tys defs (printTerm defs t d) (scopeOf d) = some t :=
  RoseTree.ind fun l cs ih d h ↦ by
    rw [printTerm_node]
    rcases termWf_cases h with ⟨rfl, c, rfl, hc, hlt⟩ | ⟨rfl, A, b, rfl, hA, hb⟩ |
      ⟨rfl, f, x, rfl, hf, hx⟩ | ⟨rfl, rfl⟩ | ⟨hl, hcs⟩ | ⟨rfl, c, rfl⟩ | ⟨hl, A, rfl, hA⟩ |
      ⟨hl, A, B, rfl, hA, hB⟩ | ⟨rfl, c, rfl, hc, hlt⟩ | ⟨rfl, c, rfl, hc, hlt⟩
    · change resolve tys defs (atomS (binderName (d - 1 - c.label))) (scopeOf d) = _
      rw [resolve_var tys defs d c.label hlt, leaf_label hc]
    · have hb' := ih b (by simp) (d + 1) hb
      rw [scopeOf_succ] at hb'
      change resolve tys defs (listS [atomS ['l', 'a', 'm'], listS [atomS (binderName d),
        printType A], printTerm defs b (d + 1)]) (scopeOf d) = _
      rw [listS, resolve_node]
      have hbs : binders (listS [RoseTree.node (some (binderName d)) [], printType A]) =
          [listS [atomS (binderName d), printType A]] := rfl
      simp only [List.map_cons, List.map_nil, resolveStep, atomS, RoseTree.label_node, hbs]
      simp only [List.mapM_cons, List.mapM_nil, listS, RoseTree.children_node,
        RoseTree.label_node, readType_printType tys A hA]
      change (resolve tys defs (printTerm defs b (d + 1)) (binderName d :: scopeOf d)).bind
        (fun t ↦ some (mk Label.lam [A, t])) = _
      rw [hb']
      rfl
    · change resolve tys defs (listS [printTerm defs f d, printTerm defs x d]) (scopeOf d) = _
      rw [listS, resolve_node, List.map_cons,
        resolveStep_app _ _ _ _ _ _ (headOk_printTerm defs hok f d)]
      simp only [List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil,
        ih f List.mem_cons_self d hf, ih x (List.mem_cons_of_mem _ List.mem_cons_self) d hx]
      rfl
    · exact resolve_unit tys defs hok d
    · have hargs : (((cs.map fun c ↦ (c, printTerm defs c)).map fun r ↦ r.2 d).map
          fun e ↦ (e, resolve tys defs e)).mapM
            (fun (x : SExp × (List (List Char) → Option Tree)) ↦ x.2 (scopeOf d)) = some cs := by
        rw [List.map_map, List.map_map]
        have hm := mapM_map_eq_some
          (fun c ↦ (printTerm defs c d, resolve tys defs (printTerm defs c d)))
          (fun (x : SExp × (List (List Char) → Option Tree)) ↦ x.2 (scopeOf d)) id cs
          fun c hc ↦ ih c hc d (hcs c hc)
        rw [List.map_id] at hm
        exact hm
      have key : ∀ (kw : List Char) (lab : ℕ),
          (∀ rest scope, resolveStep tys defs none ((atomS kw, resolve tys defs (atomS kw)) ::
            rest) scope = (rest.mapM fun (x : SExp × (List (List Char) → Option Tree)) ↦
              x.2 scope).map (mk lab)) →
          resolve tys defs (listS (atomS kw :: (cs.map fun c ↦ (c, printTerm defs c)).map
            fun r ↦ r.2 d)) (scopeOf d) = some (RoseTree.node lab cs) := fun kw lab hk ↦ by
        rw [listS, resolve_node, List.map_cons, hk, hargs]
        rfl
      rcases hl with rfl | rfl | rfl | rfl | rfl
      · exact key ['p', 'a', 'i', 'r'] Label.pair fun _ _ ↦ rfl
      · exact key ['f', 's', 't'] Label.fst fun _ _ ↦ rfl
      · exact key ['s', 'n', 'd'] Label.snd fun _ _ ↦ rfl
      · exact key ['i', 'f'] Label.cond fun _ _ ↦ rfl
      · exact key ['c', 'o', 'n', 's'] Label.cons fun _ _ ↦ rfl
    · obtain ⟨cl, ccs, rfl⟩ : ∃ cl ccs, c = RoseTree.node cl ccs :=
        ⟨_, _, (RoseTree.node_label_children c).symm⟩
      rcases ccs with _ | ⟨x, xs⟩
      · change resolve tys defs (numeralS cl) (scopeOf d) = _
        rw [resolve_numeral]
        rfl
      · let t := RoseTree.node cl (x :: xs)
        change resolve tys defs (if t.children.isEmpty then numeralS t.label
          else listS [atomS ['q', 'u', 'o', 't', 'e'], printDatum t]) (scopeOf d) = _
        simp only [t, RoseTree.children_node, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
        rw [listS, resolve_node]
        change (readDatum (printDatum (RoseTree.node cl (x :: xs)))).map
          (fun t ↦ mk Label.quote [t]) = _
        rw [readDatum_printDatum _ _ (List.cons_ne_nil _ _)]
        rfl
    · rcases hl with rfl | rfl | rfl | rfl
      all_goals
        change resolve tys defs (listS [atomS _, printType A]) (scopeOf d) = _
        rw [listS, resolve_node]
        simp only [List.map_cons, List.map_nil, resolveStep, atomS, RoseTree.label_node,
          readType_printType tys A hA]
        rfl
    · rcases hl with rfl | rfl
      all_goals
        change resolve tys defs (listS [atomS _, printType A, printType B]) (scopeOf d) = _
        rw [listS, resolve_node]
        simp only [List.map_cons, List.map_nil, resolveStep, atomS, RoseTree.label_node,
          readType_printType tys A hA, readType_printType tys B hB]
        rfl
    · change resolve tys defs (atomS (primNames.getD c.label [])) (scopeOf d) = _
      rw [resolve_prim tys defs hok d c.label hlt, leaf_label hc]
    · change resolve tys defs (atomS (defs.getD c.label [])) (scopeOf d) = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
        resolve_ref tys defs hnd hok d c.label hlt, leaf_label hc]

/-- A term printed under binders to a depth, given the names of the definitions, when the names
may be a program's definitions' and the term is well formed; nothing otherwise. -/
def printTerm? (defs : List (List Char)) (t : Tree) (d : ℕ) : Option SExp :=
  if namesOk defs && TermWf defs.length t d then some (printTerm defs t d) else none

/-- The reader retracts the printer: what the printer writes for a term under binders to a depth
resolves, in the scope of those binders, to the term. -/
theorem resolve_of_printTerm? (tys : TypeNames) (defs : List (List Char)) (t : Tree) (d : ℕ)
    (e : SExp) (h : printTerm? defs t d = some e) : resolve tys defs e (scopeOf d) = some t := by
  unfold printTerm? at h
  split at h
  · rename_i hc
    rw [Bool.and_eq_true, namesOk_iff] at hc
    rw [← Option.some.inj h]
    exact resolve_printTerm tys defs hc.1.1 hc.1.2 t d hc.2
  · exact absurd h (fun h' ↦ nomatch h')

/-! ## Programs -/

/-- Definitions printed after definitions of the names given: each {lit}`(def name term)`, its
references named by the names of the definitions before it; nothing when a name may not be a
definition's or is declared already, or a term is not well formed among the definitions before
it. -/
def printFrom (ds : List (List Char × Tree)) : List (List Char) → Option (List SExp) :=
  List.rec (motive := fun _ ↦ List (List Char) → Option (List SExp)) (fun _ ↦ some [])
    (fun d _ ih names ↦
      if nameOk d.1 && !names.contains d.1 && TermWf names.length d.2 0 then
        (ih (names ++ [d.1])).map
          (listS [atomS ['d', 'e', 'f'], atomS d.1, printTerm names d.2 0] :: ·)
      else none) ds

/-- A bundle's definitions printed, each referring to those before it by name, or nothing when
the bundle is not well formed. -/
def printProgram (ds : List (List Char × Tree)) : Option (List SExp) := printFrom ds []

/-- Expanding no numeral abbreviations leaves an S-expression as it is. -/
theorem expandNums_nil : ∀ e : SExp, expandNums [] e = e :=
  RoseTree.ind fun a cs ih ↦ by
    rw [expandNums, RoseTree.elim_node, ← expandNums, List.map_congr_left ih, List.map_id']
    cases a <;> rfl

/-- The bundles the printer writes so that they read back: distinct names that may be
definitions', and each definition's term well formed among the definitions before it. -/
def ProgramWf (ds : List (List Char × Tree)) : Prop :=
  (ds.map Prod.fst).Nodup ∧ (∀ n ∈ ds.map Prod.fst, NameOk n) ∧
    ∀ (i : ℕ) (h : i < ds.length), TermWf i ds[i].2 0 = true

/-- The printing of a definition followed by others. -/
theorem printFrom_cons (d : List Char × Tree) (ds : List (List Char × Tree))
    (names : List (List Char)) : printFrom (d :: ds) names =
      if nameOk d.1 && !names.contains d.1 && TermWf names.length d.2 0 then
        (printFrom ds (names ++ [d.1])).map
          (listS [atomS ['d', 'e', 'f'], atomS d.1, printTerm names d.2 0] :: ·)
      else none := rfl

/-- A printed definition after the definitions before it reads back to itself. -/
theorem readFormStep_printed (pre : List (List Char × Tree)) (n : List Char) (t : Tree)
    (hnd : (pre.map Prod.fst).Nodup) (hn : n ∉ pre.map Prod.fst)
    (hok : ∀ m ∈ pre.map Prod.fst, NameOk m) (hnok : NameOk n)
    (hwf : TermWf pre.length t 0 = true) :
    readFormStep (some ([], [], pre))
        (listS [atomS ['d', 'e', 'f'], atomS n, printTerm (pre.map Prod.fst) t 0]) =
      some ([], [], pre ++ [(n, t)]) := by
  have hfresh : isFresh ([] ++ [] ++ pre.map Prod.fst) n = true := by
    rw [isFresh, List.nil_append, List.nil_append, Bool.and_eq_true, Bool.not_eq_true',
      Bool.not_eq_true']
    exact ⟨Bool.eq_false_iff.mpr fun h ↦ hnok.2.2 (List.contains_iff_mem.mp h),
      Bool.eq_false_iff.mpr fun h ↦ hn (List.contains_iff_mem.mp h)⟩
  have hres : resolve [] (pre.map Prod.fst) (expandNums [] (printTerm (pre.map Prod.fst) t 0))
      [] = some t := by
    rw [expandNums_nil]
    exact resolve_printTerm [] _ hnd hok t 0 (by rwa [List.length_map])
  simp only [readFormStep, listS, atomS, RoseTree.children_node, RoseTree.label_node]
  change (guard (isFresh ([] ++ [] ++ pre.map Prod.fst) n = true) >>= fun _ ↦
    resolve [] (pre.map Prod.fst) (expandNums [] (printTerm (pre.map Prod.fst) t 0)) [] >>=
      fun r ↦ some (([] : TypeNames), ([] : NumNames), pre ++ [(n, r)])) = _
  rw [hfresh, hres]
  rfl

/-- Printed definitions after those before them read back to themselves. -/
theorem foldl_readFormStep_printFrom : ∀ (rest pre : List (List Char × Tree)) (es : List SExp),
    (pre.map Prod.fst).Nodup → (∀ m ∈ pre.map Prod.fst, NameOk m) →
      printFrom rest (pre.map Prod.fst) = some es →
        es.foldl readFormStep (some ([], [], pre)) = some ([], [], pre ++ rest) :=
  List.rec (fun pre es _ _ h ↦ by
      cases Option.some.inj h
      rw [List.append_nil]
      rfl)
    fun d rest ih pre es hnd hok h ↦ by
      rw [printFrom_cons] at h
      split at h
      · rename_i hc
        rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', nameOk_iff] at hc
        obtain ⟨⟨hnok, hc⟩, hwf⟩ := hc
        have hn : d.1 ∉ pre.map Prod.fst := fun hm ↦
          Bool.false_ne_true (hc.symm.trans (List.contains_iff_mem.mpr hm))
        rcases hr : printFrom rest (pre.map Prod.fst ++ [d.1]) with _ | es'
        · rw [hr] at h
          exact nomatch h
        · rw [hr, Option.map_some] at h
          cases Option.some.inj h
          have hmap : pre.map Prod.fst ++ [d.1] = (pre ++ [d]).map Prod.fst := by
            rw [List.map_append]
            rfl
          rw [List.foldl_cons,
            readFormStep_printed pre d.1 d.2 hnd hn hok hnok (by rwa [List.length_map] at hwf),
            ih (pre ++ [d]) es'
              (hmap ▸ List.nodup_append.mpr ⟨hnd, List.nodup_singleton _,
                fun a ha b hb ↦ by
                  rw [List.mem_singleton] at hb
                  intro hab
                  subst hb
                  subst hab
                  exact hn ha⟩)
              (fun m hm ↦ by
                rw [← hmap, List.mem_append, List.mem_singleton] at hm
                rcases hm with hm | rfl
                · exact hok m hm
                · exact hnok)
              (hmap ▸ hr),
            List.append_assoc]
          rfl
      · exact nomatch h

/-- The reader retracts the printer on programs: what the printer writes for a bundle reads back
to the bundle. -/
theorem readForms_printProgram (ds : List (List Char × Tree)) (es : List SExp)
    (h : printProgram ds = some es) : readForms es = some ds := by
  unfold readForms
  rw [foldl_readFormStep_printFrom ds [] es List.nodup_nil (fun _ hm ↦ nomatch hm) h]
  rfl

/-- The printer prints definitions after well-formed definitions before them, when the whole is
well formed. -/
theorem isSome_printFrom : ∀ (rest pre : List (List Char × Tree)),
    ProgramWf (pre ++ rest) → (printFrom rest (pre.map Prod.fst)).isSome :=
  List.rec (fun _ _ ↦ rfl) fun d rest ih pre h ↦ by
    obtain ⟨hnd, hok, hwf⟩ := h
    have hassoc : pre ++ d :: rest = (pre ++ [d]) ++ rest := by rw [List.append_assoc]; rfl
    have hnd' : ((pre ++ [d]).map Prod.fst).Nodup := by
      rw [hassoc, List.map_append] at hnd
      exact hnd.of_append_left
    rw [List.map_append, List.map_cons, List.map_nil] at hnd'
    have hlen : pre.length < (pre ++ d :: rest).length := by
      rw [List.length_append, List.length_cons]; omega
    have hd : (pre ++ d :: rest)[pre.length] = d := by
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
    have hc : (nameOk d.1 && !(pre.map Prod.fst).contains d.1 &&
        TermWf (pre.map Prod.fst).length d.2 0) = true := by
      have hmem : d.1 ∈ (pre ++ d :: rest).map Prod.fst := by
        rw [List.map_append]
        exact List.mem_append_right _ List.mem_cons_self
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', nameOk_iff, List.length_map]
      exact ⟨⟨hok d.1 hmem, Bool.eq_false_iff.mpr fun hm ↦
          List.disjoint_of_nodup_append hnd' (List.contains_iff_mem.mp hm) List.mem_cons_self⟩,
        hd ▸ hwf pre.length hlen⟩
    rw [printFrom_cons]
    simp only [hc, ↓reduceIte, Option.isSome_map]
    rw [show pre.map Prod.fst ++ [d.1] = (pre ++ [d]).map Prod.fst by rw [List.map_append]; rfl]
    exact ih (pre ++ [d]) (hassoc ▸ ⟨hnd, hok, hwf⟩)

/-- The printer prints every well-formed bundle. -/
theorem isSome_printProgram (ds : List (List Char × Tree)) (h : ProgramWf ds) :
    (printProgram ds).isSome :=
  isSome_printFrom ds [] h

end Geb.Kernel

end

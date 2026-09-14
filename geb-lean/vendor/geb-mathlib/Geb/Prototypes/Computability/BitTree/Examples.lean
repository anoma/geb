/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Encoding -- shake: keep

set_option doc.verso true

/-!
# Boundary cases of the binary-tree encoding

These calculations exercise tree tags, both payload bit values, string
terminators, incomplete input and trailing input.

## Main statements

* The empty string is a valid leaf payload, while an empty input is invalid.
* Forks may have empty or nonempty leaf payloads.
* Truncated escapes, unfinished forks and trailing trees are rejected.

## Tags

binary tree, encoding, recognizer, boundary cases
-/

public section

namespace Geb.BitTree

example : encode (leaf []) = [false, false] := rfl

example : encode (leaf [false, true]) = [false, true, false, true, true, false] := rfl

example : encode (fork (leaf []) (leaf [])) = [true, false, false, false, false] := rfl

example : validBool [] = false := rfl

example : validBool [false, false] = true := rfl

example : validBool [false, true, false, true, true, false] = true := rfl

example : validBool [true, false, false, false, false] = true := rfl

example : validBool [false, true] = false := rfl

example : validBool [false, true, false] = false := rfl

example : validBool [true, false, false] = false := rfl

example : validBool [false, false, false, false] = false := rfl

end Geb.BitTree

/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.Computability.BitTree.Elias.Tree -- shake: keep

set_option doc.verso true

/-!
# Elias code boundary examples

The calculations check the shifted delta code at its first binary-size boundaries and
complete tree decoding at empty, valid and trailing-input cases.

## Tags

prefix code, verification
-/

open Geb.BitTree.Elias

example : encodeNat 0 = [true] := rfl
example : encodeNat 1 = [false, true, false, false] := rfl
example : encodeNat 2 = [false, true, false, true] := rfl
example : encodeNat 3 = [false, true, true, false, false] := rfl
example : encode (Geb.BitTree.leaf []) = [false, true] := rfl
example : validBool [false, true] = true := rfl
example : validBool [] = false := rfl
example : validBool [false, true, true] = false := rfl

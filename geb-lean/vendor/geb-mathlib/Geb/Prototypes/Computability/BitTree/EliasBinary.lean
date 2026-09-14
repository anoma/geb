/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module


set_option doc.verso true

/-!
# Binary-counter recognition of the Elias-length encoding

A two-pass machine whose counters are binary and monotone recognizes the Elias-length tree
encoding in linear time and logarithmic work space. The size bound of the encoding is that of
the Elias-length representation itself.
-/

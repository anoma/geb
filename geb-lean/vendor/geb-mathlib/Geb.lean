/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module -- shake: keep-all, shake: keep-downstream

public import Geb.Cslib
public import Geb.Internal
public import Geb.Mathlib

/-!
# Geb root module

Root index for the `Geb` library. Subindexes:

- `Geb.Mathlib` — upstream-eligible content targeted at mathlib4
- `Geb.Cslib` — upstream-eligible content targeted at CSLib
- `Geb.Internal` — downstream-only content
-/

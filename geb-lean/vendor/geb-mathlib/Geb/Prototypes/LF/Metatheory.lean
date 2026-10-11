/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Metatheory.Composition
public import Geb.Prototypes.LF.Metatheory.Expansion
public import Geb.Prototypes.LF.Metatheory.HSubstRename
public import Geb.Prototypes.LF.Metatheory.Identity
public import Geb.Prototypes.LF.Metatheory.Rename
public import Geb.Prototypes.LF.Metatheory.Scope
public import Geb.Prototypes.LF.Metatheory.Strengthen
public import Geb.Prototypes.LF.Metatheory.Substitution
public import Geb.Prototypes.LF.Metatheory.TypeShape
public import Geb.Prototypes.LF.Metatheory.Weakening

set_option doc.verso true in
/-!
# The metatheory of canonical LF

The metatheory of Canonical LF of \[HarperLicata2007\], Section 2.3: the laws of renaming
and its commutation with hereditary substitution, vacuous substitution, the composition of
hereditary substitutions, the stability of the judgments under renaming, weakening among them,
and under a renaming that respects the types of the variables an expression mentions,
strengthening among them, the scoping of judged expressions, by which the declarations of a
formed signature are closed, the invariance of erasure under substitution, and the substitution
theorem: hereditary substitutions exist and preserve the judgments. Then the identity principles
(\[WatkinsEtAl2002\], Section 4.6): the η-expansion of a variable is an identity for
hereditary substitution, and the η-expansion of an atomic term checks against the type it
synthesizes.
-/

set_option doc.verso true

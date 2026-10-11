/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.HSubst
public import Geb.Prototypes.LF.Metatheory
public import Geb.Prototypes.LF.Rewrite
public import Geb.Prototypes.LF.Syntax
public import Geb.Prototypes.LF.Topos
public import Geb.Prototypes.LF.Typing

set_option doc.verso true in
/-!
# The logical framework LF

Canonical LF (\[HarperLicata2007\], Section 2), the presentation of the logical framework LF
of \[HarperHonsellPlotkin1993\] whose expressions are its canonical forms: its syntax, in
which the β-normal forms are the only expressions and each application is a head with its spine;
the hereditary substitution, which keeps them canonical; and its judgments, decided by a fold
over the expression each classifies, among them the formation of a signature, the declaration of
the constants, with their kinds and types, that an object language is represented by; and its
extension by rewrite rules on the constants (\[CousineauDowek2007\]). The expressions with
the rules are the input format of the type inhabitation solver of \[NormanAvigad2025\]. A
fragment of the internal language of the free topos with a natural numbers object is represented
in it.
-/

set_option doc.verso true

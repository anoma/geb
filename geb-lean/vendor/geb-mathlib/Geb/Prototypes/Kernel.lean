/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Annotation
public import Geb.Prototypes.Kernel.Basic
public import Geb.Prototypes.Kernel.Blake3
public import Geb.Prototypes.Kernel.Hole
public import Geb.Prototypes.Kernel.Identity
public import Geb.Prototypes.Kernel.Document
public import Geb.Prototypes.Kernel.Eval
public import Geb.Prototypes.Kernel.ModuleIdentity
public import Geb.Prototypes.Kernel.Modules
public import Geb.Prototypes.Kernel.Printer
public import Geb.Prototypes.Kernel.Loading
public import Geb.Prototypes.Kernel.Reader
public import Geb.Prototypes.Kernel.Strict
public import Geb.Prototypes.Kernel.Subst

set_option doc.verso true in
/-!
# The bootstrap kernel

The kernel language of the bootstrap, System T over rose trees with natural-number labels:
its types, its checker-evaluator, which is its denotation, its readable syntax, its bundles and
images, the host driver that builds and runs them, substitution in its terms, an evaluator of its
terms with fuel, adequate to the denotation, and the loading of a program one definition at a
time, each step checked by the kernel.
-/

set_option doc.verso true

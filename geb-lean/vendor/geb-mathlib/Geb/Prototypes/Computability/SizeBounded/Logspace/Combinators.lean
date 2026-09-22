/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Basic

set_option doc.verso true in
/-!
# Derived expressions of the logspace subalgebra

The tail, the four-way conditional and the diagonal, and the first two applied
to expressions of a common arity, as expressions of the successor-free
subalgebra {name}`Geb.SizeBounded.Logspace.LOf`. Each is the expression of
{name}`Geb.SizeBounded.S` that
{lit}`Geb.Prototypes.Computability.SizeBounded.Combinators` builds, paired with
the proof that it is successor-free, which
{name}`Geb.SizeBounded.Logspace.sbsFree_comp_iff` reduces to the same
property of its constituents. The meaning of each is the meaning of the
underlying expression, so the equations of that module apply unchanged.

# Main definitions

* {lit}`tailL`, {lit}`condL` — the tail and the four-way conditional.
* {lit}`cond4L`, {lit}`tailAppL`, {lit}`diagL` — the conditional and the tail
  applied to expressions of a common arity, and the diagonal.

# Main statements

* {lit}`sem_constL`, {lit}`sem_projL`, {lit}`sem_compL`, {lit}`sem_srnL_nil`,
  {lit}`sem_srnL_cons` — the meanings of the constructors of the subalgebra.
* {lit}`sem_cond4L`, {lit}`sem_tailAppL`, {lit}`sem_diagL` — the meanings of
  the derived expressions.

# Tags

logspace, function algebra, combinator, successor-free
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace

open Cobham (Sem)

public section

/-- The meaning of a constant. -/
theorem sem_constL (n : ℕ) (w : List Bool) (x : Fin n → List Bool) :
    (constL n w).sem x = w := rfl

/-- The meaning of a projection. -/
theorem sem_projL (n : ℕ) (i : Fin n) (x : Fin n → List Bool) : (projL n i).sem x = x i :=
  rfl

/-- The meaning of a substitution. -/
theorem sem_compL {n m : ℕ} (h : LOf m) (g : Fin m → LOf n) (x : Fin n → List Bool) :
    (compL h g).sem x = h.sem (fun i ↦ (g i).sem x) := rfl

/-- A recursion on the empty word is its base. -/
theorem sem_srnL_nil {a b : ℕ} (g : Fin b → LOf a) (h : Bool → Fin b → LOf (b + a + 1))
    (j : Fin b) (y : Fin a → List Bool) :
    (srnL g h j).sem (Fin.cons [] y) = (g j).sem y := rfl

/-- A recursion on {lit}`i :: v` is the step on {lit}`i`, at the environment
holding {lit}`v`, every component's value on {lit}`v`, and the parameters. -/
theorem sem_srnL_cons {a b : ℕ} (g : Fin b → LOf a) (h : Bool → Fin b → LOf (b + a + 1))
    (j : Fin b) (i : Bool) (v : List Bool) (y : Fin a → List Bool) :
    (srnL g h j).sem (Fin.cons (i :: v) y) =
      (h i j).sem (stepEnv v (fun l ↦ (srnL g h l).sem (Fin.cons v y)) y) :=
  sem_srnOf_cons (fun l ↦ (g l).1) (fun i l ↦ (h i l).1) j i v y

/-- The tail, {name}`Geb.SizeBounded.tailOf`, is successor-free. -/
@[expose] def tailL : LOf 1 := ⟨tailOf, rfl⟩

/-- The four-way conditional, {name}`Geb.SizeBounded.condOf`, is successor-free. -/
@[expose] def condL : LOf 4 := ⟨condOf, rfl⟩

/-- The conditional applied to four expressions of a common arity. -/
@[expose] def cond4L {n : ℕ} (s e t f : LOf n) : LOf n :=
  ⟨cond4 s.1 e.1 t.1 f.1, (sbsFree_comp_iff _ _).mpr
    ⟨rfl, fun i ↦ match i with | 0 => s.2 | 1 => e.2 | 2 => t.2 | 3 => f.2⟩⟩

/-- The meaning of an applied conditional. -/
theorem sem_cond4L {n : ℕ} (s e t f : LOf n) (x : Fin n → List Bool) :
    (cond4L s e t f).sem x = cond4Sem (s.sem x) (e.sem x) (t.sem x) (f.sem x) :=
  sem_cond4 s.1 e.1 t.1 f.1 x

/-- The tail applied to an expression. -/
@[expose] def tailAppL {n : ℕ} (e : LOf n) : LOf n :=
  ⟨tailApp e.1, (sbsFree_comp_iff _ _).mpr ⟨rfl, fun i ↦ match i with | 0 => e.2⟩⟩

/-- The meaning of an applied tail. -/
theorem sem_tailAppL {n : ℕ} (e : LOf n) (x : Fin n → List Bool) :
    (tailAppL e).sem x = (e.sem x).tail :=
  sem_tailApp e.1 x

/-- A binary expression at its sole argument in both positions. -/
@[expose] def diagL (e : LOf 2) : LOf 1 :=
  ⟨diagOf e.1, (sbsFree_comp_iff _ _).mpr ⟨e.2, fun _ ↦ rfl⟩⟩

/-- The meaning of the diagonal. -/
theorem sem_diagL (e : LOf 2) (w : List Bool) : (diagL e).sem ![w] = e.sem ![w, w] :=
  sem_diagOf e.1 w

end

end Geb.SizeBounded.Logspace

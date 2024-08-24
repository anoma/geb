module LanguageDef.SlicePolyDialg

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.SlicePolyCat
import public LanguageDef.SlicePolyUMorph
import public LanguageDef.MLDirichCat

-- Comma categories, algebras, coalgebras, and dialgebras of slice polynomial
-- functors.

---------------------------------
---------------------------------
---- Algebras and coalgebras ----
---------------------------------
---------------------------------

public export
spfdAlgAction : {x : Type} -> SPFData x x -> SliceObj x -> Type
spfdAlgAction {x} p a =
  SliceMorphism {a=x} (InterpSPFData {dom=x} {cod=x} p a) a

public export
spfdCoalgAction : {x : Type} -> SPFData x x -> SliceObj x -> Type
spfdCoalgAction {x} p a =
  SliceMorphism {a=x} a (InterpSPFData {dom=x} {cod=x} p a)

-------------------
-------------------
---- Monomials ----
-------------------
-------------------

-- A monomial is a polynomial all of whose positions have the same
-- direction type.
public export
spfdMonomial : {dom, cod : Type} -> SliceObj cod -> SliceObj dom ->
  SPFData dom cod
spfdMonomial {dom} {cod} coeff degree = SPFD coeff (\_, _ => degree)

-- A linear polynomial is a monomial of degree one (that is, the
-- degree is the terminal object).
public export
spfdLinear : {dom, cod : Type} -> SliceObj cod -> SPFData dom cod
spfdLinear {dom} {cod} coeff =
  spfdMonomial {dom} {cod} coeff (SliceObjTerminal dom)

-- A monomial with coefficient one (that is, terminal) is representable.
public export
spfdMonRep : {dom, cod : Type} -> (degree : SliceObj dom) ->
  spfdMonomial {dom} {cod} (SliceObjTerminal cod) degree =
  SPFDataRep degree cod
spfdMonRep {dom} {cod} degree = Refl

-- A "dynamical system" is a monomial whose coefficient and degree
-- are the same.
public export
spfdDynSys : {x : Type} -> SliceObj x -> SPFData x x
spfdDynSys {x} coeff = spfdMonomial {dom=x} {cod=x} coeff coeff

-- Formula 6.65 from _Polynomial Functors: A Mathematical Theory of
-- Interaction_.

public export
spfdMonNTtoInj : {dom, cod : Type} ->
  (coeff : SliceObj cod) -> (degree : SliceObj dom) -> (p : SPFData dom cod) ->
  SPFnt (spfdMonomial coeff degree) p ->
  SliceMorphism {a=cod} coeff (InterpSPFData p degree)
spfdMonNTtoInj {dom} {cod} coeff degree p alpha ec n =
  (spOnPos alpha ec n ** \ed, pd => spOnDir alpha ec n ed pd)

public export
spfdInjToMonNT : {dom, cod : Type} ->
  (coeff : SliceObj cod) -> (degree : SliceObj dom) -> (p : SPFData dom cod) ->
  SliceMorphism {a=cod} coeff (InterpSPFData p degree) ->
  SPFnt (spfdMonomial coeff degree) p
spfdInjToMonNT {dom} {cod} coeff degree p m =
  SPFDm (\ec, n => fst $ m ec n) (\ec, n => snd $ m ec n)

public export
spfdDynSysNTtoCoalg : {x : Type} ->
  (coeff : SliceObj x) -> (p : SPFData x x) ->
  SPFnt (spfdDynSys {x} coeff) p -> spfdCoalgAction {x} p coeff
spfdDynSysNTtoCoalg {x} coeff = spfdMonNTtoInj {dom=x} {cod=x} coeff coeff

public export
spfdCoalgToDynSysNT : {x : Type} ->
  (coeff : SliceObj x) -> (p : SPFData x x) ->
  spfdCoalgAction {x} p coeff -> SPFnt (spfdDynSys {x} coeff) p
spfdCoalgToDynSysNT {x} coeff = spfdInjToMonNT {dom=x} {cod=x} coeff coeff

-- Formula 6.66 from _Polynomial Functors: A Mathematical Theory of
-- Interaction_.

public export
spfdLinRepCompL : {w, x, y, z : Type} ->
  (a : SliceObj w) -> (b : SliceObj x) -> (p : SPFData y z) -> SPFData x w
spfdLinRepCompL {w} {x} {y} {z} a b p =
  SPFDcomp x z w
  (spfdLinear {dom=z} {cod=w} a)
  $ SPFDcomp x y z p (SPFDataRep {dom=x} b y)

public export
spfdLinRepCompR : {w, x, y, z : Type} ->
  (a : SliceObj w) -> (b : SliceObj x) -> (q : SPFData x w) -> SPFData y z
spfdLinRepCompR {w} {x} {y} {z} a b q =
  SPFDcomp y w z
  (SPFDataRep {dom=w} a z)
  $ SPFDcomp y x w q (spfdLinear {dom=y} {cod=x} b)

-------------------------------------------
-------------------------------------------
---- Polynomial slice comma categories ----
-------------------------------------------
-------------------------------------------

-- See for example https://en.wikipedia.org/wiki/Comma_category .
--
-- Here we define comma categories whose (two) domains and (one) codomain are
-- all slice categories, and whose functors are polynomial.

-- The morphism component of a comma-category object.
public export
SPCommaObjMor : {a, b, c : Type} ->
  (s : SPFData a c) -> (t : SPFData b c) -> SliceObj a -> SliceObj b -> Type
SPCommaObjMor {a} {b} {c} s t sa sb =
   SliceMorphism {a=c}
    (InterpSPFData {dom=a} {cod=c} s sa)
    (InterpSPFData {dom=b} {cod=c} t sb)

public export
SPCommaObj: {a, b, c : Type} -> (s : SPFData a c) -> (t : SPFData b c) -> Type
SPCommaObj {a} {b} {c} s t =
  (sab : (SliceObj a, SliceObj b) ** SPCommaObjMor s t (fst sab) (snd sab))

-------------------------------------------------------
-------------------------------------------------------
---- Objects and morphisms of algebraic categories ----
-------------------------------------------------------
-------------------------------------------------------

-- The evaluator for a dialgebra between two slice polynomial functors,
-- whose carrier is the given slice object.
public export
SPDialgEval : {c : Type} -> (dom, cod : SPFData c c) -> SliceObj c -> Type
SPDialgEval {c} f g x = SPCommaObjMor {a=c} {b=c} {c} f g x x

public export
SPDialg : {c : Type} -> IntMorSig (SPFData c c)
SPDialg {c} f g = Sigma {a=(SliceObj c)} $ SPDialgEval {c} f g

public export
SPAlgEval : {c : Type} -> SPFData c c -> SliceObj c -> Type
SPAlgEval {c} = flip (SPDialgEval {c}) (SPFDid c)

public export
SPCoalgEval : {c : Type} -> SPFData c c -> SliceObj c -> Type
SPCoalgEval {c} = SPDialgEval {c} (SPFDid c)

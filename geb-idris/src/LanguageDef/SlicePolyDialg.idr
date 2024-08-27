module LanguageDef.SlicePolyDialg

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.SlicePolyCat
import public LanguageDef.SlicePolyUMorph
import public LanguageDef.MLDirichCat

-- Comma categories, algebras, coalgebras, and dialgebras of slice polynomial
-- functors.

-----------------------------------------------
-----------------------------------------------
---- Algebras, coalgebras, and dialgebras  ----
-----------------------------------------------
-----------------------------------------------

-----------------
---- Objects ----
-----------------

public export
spfdAlgAction : {x : Type} -> SPFData x x -> SliceObj x -> Type
spfdAlgAction {x} p a =
  SliceMorphism {a=x} (InterpSPFData {dom=x} {cod=x} p a) a

public export
SPAlg : {x : Type} -> SliceObj (SPFData x x)
SPAlg {x} p = Sigma {a=(SliceObj x)} $ spfdAlgAction {x} p

public export
SPAlgCarrier : {x : Type} -> {f : SPFData x x} -> SPAlg {x} f -> SliceObj x
SPAlgCarrier {x} {f} = fst

public export
SPAlgAction : {x : Type} -> {f : SPFData x x} -> (alg : SPAlg {x} f) ->
  spfdAlgAction {x} f (SPAlgCarrier {x} {f} alg)
SPAlgAction {x} {f} = snd

public export
spfdCoalgAction : {x : Type} -> SPFData x x -> SliceObj x -> Type
spfdCoalgAction {x} p a =
  SliceMorphism {a=x} a (InterpSPFData {dom=x} {cod=x} p a)

public export
SPCoalg : {x : Type} -> SliceObj (SPFData x x)
SPCoalg {x} p = Sigma {a=(SliceObj x)} $ spfdCoalgAction {x} p

public export
SPCoalgCarrier : {x : Type} -> {f : SPFData x x} -> SPCoalg {x} f -> SliceObj x
SPCoalgCarrier {x} {f} = fst

public export
SPCoalgAction : {x : Type} -> {f : SPFData x x} -> (coalg : SPCoalg {x} f) ->
  spfdCoalgAction {x} f (SPCoalgCarrier {x} {f} coalg)
SPCoalgAction {x} {f} = snd

-- The evaluator for a dialgebra between two slice polynomial functors,
-- whose carrier is the given slice object.
public export
spfdDialgAction : {c, d : Type} -> (f, g : SPFData c d) -> SliceObj c -> Type
spfdDialgAction {c} {d} f g x =
   SliceMorphism {a=d}
    (InterpSPFData {dom=c} {cod=d} f x)
    (InterpSPFData {dom=c} {cod=d} g x)

public export
SPDialg : {c, d : Type} -> IntMorSig (SPFData c d)
SPDialg {c} {d} f g = Sigma {a=(SliceObj c)} $ spfdDialgAction {c} f g

public export
SPDialgCarrier : {c, d : Type} -> {f, g : SPFData c d} -> SPDialg {c} {d} f g ->
  SliceObj c
SPDialgCarrier {c} {d} {f} {g} = fst

public export
SPDialgAction : {c, d : Type} -> {f, g : SPFData c d} ->
  (dialg : SPDialg {c} {d} f g) ->
  spfdDialgAction {c} {d} f g (SPDialgCarrier {c} {d} {f} {g} dialg)
SPDialgAction {c} {d} {f} {g} = snd

-------------------
---- Morphisms ----
-------------------

public export
SPAlgMap : {x : Type} -> {f : SPFData x x} -> IntMorSig (SPAlg {x} f)
SPAlgMap {x} {f} a b =
  SliceMorphism {a=x} (SPAlgCarrier a) (SPAlgCarrier b)

public export
SPAlgComm : {x : Type} -> {f : SPFData x x} -> {a, b : SPAlg {x} f} ->
  SliceObj (SPAlgMap {x} {f} a b)
SPAlgComm {x} {f} {a} {b} m =
  SliceExtEq {a=x}
    (sliceComp
      {x=(InterpSPFData f $ SPAlgCarrier a)}
      {y=(SPAlgCarrier a)}
      {z=(SPAlgCarrier b)}
      m
      (SPAlgAction a))
    (sliceComp
      {x=(InterpSPFData f $ SPAlgCarrier a)}
      {y=(InterpSPFData f $ SPAlgCarrier b)}
      {z=(SPAlgCarrier b)}
      (SPAlgAction b)
      (InterpSPFDataMap {dom=x} {cod=x}
        f
        (SPAlgCarrier a)
        (SPAlgCarrier b)
        m))

public export
SPAlgMor : {x : Type} -> {f : SPFData x x} -> IntMorSig (SPAlg {x} f)
SPAlgMor {x} {f} a b =
  DPair (SPAlgMap {x} {f} a b) (SPAlgComm {x} {f} {a} {b})

public export
SPCoalgMap : {x : Type} -> {f : SPFData x x} -> IntMorSig (SPCoalg {x} f)
SPCoalgMap {x} {f} a b =
  SliceMorphism {a=x} (SPCoalgCarrier a) (SPCoalgCarrier b)

public export
SPCoalgComm : {x : Type} -> {f : SPFData x x} -> {a, b : SPCoalg {x} f} ->
  SliceObj (SPCoalgMap {x} {f} a b)
SPCoalgComm {x} {f} {a} {b} m =
  SliceExtEq {a=x}
    (sliceComp
      {x=(SPCoalgCarrier a)}
      {y=(SPCoalgCarrier b)}
      {z=(InterpSPFData f $ SPCoalgCarrier b)}
      (SPCoalgAction b)
      m)
    (sliceComp
      {x=(SPCoalgCarrier a)}
      {y=(InterpSPFData f $ SPCoalgCarrier a)}
      {z=(InterpSPFData f $ SPCoalgCarrier b)}
      (InterpSPFDataMap {dom=x} {cod=x}
        f
        (SPCoalgCarrier a)
        (SPCoalgCarrier b)
        m)
      (SPCoalgAction a))

public export
SPCoalgMor : {x : Type} -> {f : SPFData x x} -> IntMorSig (SPCoalg {x} f)
SPCoalgMor {x} {f} a b =
  DPair (SPCoalgMap {x} {f} a b) (SPCoalgComm {x} {f} {a} {b})

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

-- A symmetric monomial, whoes coefficient and degree are the same.
public export
spfdSymMon : {x : Type} -> SliceObj x -> SPFData x x
spfdSymMon {x} coeff = spfdMonomial {dom=x} {cod=x} coeff coeff

-- Definition 4.18 from _Polynomial Functors:  A Mathematical Theory
-- of Interaction_:  a "dynamical system" is a lens (natural transformation)
-- whose domain is a symmetric monomial.
public export
spfdDynSys : {x : Type} -> (sl : SliceObj x) -> SPFData x x -> Type
spfdDynSys {x} sl p = SPFnt {dom=x} {cod=x} (spfdSymMon sl) p

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
spfdDynSysToCoalg : {x : Type} ->
  (coeff : SliceObj x) -> (p : SPFData x x) ->
  spfdDynSys {x} coeff p -> spfdCoalgAction {x} p coeff
spfdDynSysToCoalg {x} coeff = spfdMonNTtoInj {dom=x} {cod=x} coeff coeff

public export
spfdCoalgToDynSys : {x : Type} ->
  (coeff : SliceObj x) -> (p : SPFData x x) ->
  spfdCoalgAction {x} p coeff -> spfdDynSys {x} coeff p
spfdCoalgToDynSys {x} coeff = spfdInjToMonNT {dom=x} {cod=x} coeff coeff

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

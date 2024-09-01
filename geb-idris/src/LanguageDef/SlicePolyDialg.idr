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
  FunExt ->
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
  FunExt ->
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

public export
SPDialgMap : {c, d : Type} -> {f, g : SPFData c d} ->
  IntMorSig (SPDialg {c} {d} f g)
SPDialgMap {c} {d} {f} a b =
  SliceMorphism {a=c} (SPDialgCarrier a) (SPDialgCarrier b)

public export
SPDialgComm : {c, d : Type} -> {f, g : SPFData c d} ->
  {a, b : SPDialg {c} {d} f g} ->
  SliceObj (SPDialgMap {c} {d} {f} {g} a b)
SPDialgComm {c} {d} {f} {g} {a} {b} m =
  FunExt ->
  SliceExtEq {a=d}
    (sliceComp
      {x=(InterpSPFData f $ SPDialgCarrier a)}
      {y=(InterpSPFData f $ SPDialgCarrier b)}
      {z=(InterpSPFData g $ SPDialgCarrier b)}
      (SPDialgAction b)
      (InterpSPFDataMap {dom=c} {cod=d}
        f
        (SPDialgCarrier a)
        (SPDialgCarrier b)
        m))
    (sliceComp
      {x=(InterpSPFData f $ SPDialgCarrier a)}
      {y=(InterpSPFData g $ SPDialgCarrier a)}
      {z=(InterpSPFData g $ SPDialgCarrier b)}
      (InterpSPFDataMap {dom=c} {cod=d}
        g
        (SPDialgCarrier a)
        (SPDialgCarrier b)
        m)
      (SPDialgAction a))

public export
SPDialgMor : {c, d : Type} -> {f, g : SPFData c d} ->
  IntMorSig (SPDialg {c} {d} f g)
SPDialgMor {c} {d} {f} a b =
  DPair (SPDialgMap {c} {d} {f} {g} a b) (SPDialgComm {c} {d} {f} {g} {a} {b})

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

-- A symmetric monomial, whose coefficient and degree are the same.
public export
spfdSymMon : {x : Type} -> SliceObj x -> SPFData x x
spfdSymMon {x} coeff = spfdMonomial {dom=x} {cod=x} coeff coeff

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

-- The covariant functor on `SPFData x y` represented by a monomial.
public export
spfdMonCovarRep : {dom, cod : Type} ->
  (coeff : SliceObj cod) -> (degree : SliceObj dom) -> SPFData dom cod -> Type
spfdMonCovarRep {dom} {cod} coeff degree =
  SPFnt {dom} {cod} (spfdMonomial {dom} {cod} coeff degree)

-- The contravariant functor on `SPFData x y` represented by a monomial.
public export
spfdMonContraRep : {dom, cod : Type} ->
  (coeff : SliceObj cod) -> (degree : SliceObj dom) -> SPFData dom cod -> Type
spfdMonContraRep {dom} {cod} coeff degree =
  flip (SPFnt {dom} {cod}) (spfdMonomial {dom} {cod} coeff degree)

-- A lens whose domain is a monomial -- put another way, a slice object
-- of the given polynomial functor whose total space is a monomial.
public export
spfdMonSl : {dom, cod : Type} -> SPFData dom cod -> Type
spfdMonSl {dom} {cod} p =
  (coeff : SliceObj cod ** degree : SliceObj dom **
   spfdMonCovarRep {dom} {cod} coeff degree p)

public export
spfdMonSlCoeff : {dom, cod : Type} -> {p : SPFData dom cod} ->
  spfdMonSl {dom} {cod} p -> SliceObj cod
spfdMonSlCoeff {dom} {cod} {p} = DPair.fst

public export
spfdMonSlDegree : {dom, cod : Type} -> {p : SPFData dom cod} ->
  spfdMonSl {dom} {cod} p -> SliceObj dom
spfdMonSlDegree {dom} {cod} {p} sl = DPair.fst $ DPair.snd sl

public export
spfdMonSlTot : {dom, cod : Type} -> {p : SPFData dom cod} ->
  spfdMonSl {dom} {cod} p -> SPFData dom cod
spfdMonSlTot {dom} {cod} {p} sl =
  spfdMonomial {dom} {cod} (spfdMonSlCoeff sl) (spfdMonSlDegree sl)

public export
spfdMonSlProj : {dom, cod : Type} -> {p : SPFData dom cod} ->
  (sl : spfdMonSl {dom} {cod} p) -> SPFnt {dom} {cod} (spfdMonSlTot {p} sl) p
spfdMonSlProj {dom} {cod} {p} sl = DPair.snd $ DPair.snd sl

-- We now see that a monomial slice object of a polynomial functor --
-- that is to say, a slice object over a polynomial functor whose domain
-- (total space) is a monomial -- has a projection component (which
-- is a natural transformation from the monomial to the functor being
-- sliced over) whose on-positions and on-directions functions are the
-- same (and in particular have the same type signature) as the components
-- of the generic factorization of the morphism which corresponds to
-- it under the equivalence of formula 6.65 above (which is witnessed by
-- `spfdMonNTtoInj` and `spfdInjToMonNT`).

public export
spfdMonSlOnPos : {dom, cod : Type} -> {p : SPFData dom cod} ->
  (sl : spfdMonSl {dom} {cod} p) ->
  SPFDmultiR1 {cod} (spfdPos p) (spfdMonSlCoeff {dom} {cod} {p} sl)
spfdMonSlOnPos {dom} {cod} {p} sl = spOnPos $ spfdMonSlProj {dom} {cod} {p} sl

public export
spfdMonSlOnDir : {dom, cod : Type} -> {p : SPFData dom cod} ->
  (sl : spfdMonSl {dom} {cod} p) ->
  SPFDmultiR2 {dom} {cod} p
    {b=(spfdMonSlCoeff {dom} {cod} {p} sl)}
    (spfdMonSlOnPos {dom} {cod} {p} sl)
    (spfdMonSlDegree {dom} {cod} {p} sl)
spfdMonSlOnDir {dom} {cod} {p} sl = spOnDir $ spfdMonSlProj {dom} {cod} {p} sl

-- Definition 4.18 from _Polynomial Functors:  A Mathematical Theory
-- of Interaction_:  a "dynamical system" is a lens (natural transformation)
-- whose domain is a symmetric monomial.
public export
spfdDynSysAct : {x : Type} -> (sl : SliceObj x) -> SPFData x x -> Type
spfdDynSysAct {x} sl = spfdMonCovarRep {dom=x} {cod=x} sl sl

public export
spfdDynSys : {x : Type} -> SPFData x x -> Type
spfdDynSys {x} p = (sl : SliceObj x ** spfdDynSysAct {x} sl p)

public export
SPDynSysCoeff : {x : Type} -> (f : SPFData x x) ->
  spfdDynSys {x} f -> SliceObj x
SPDynSysCoeff {x} f = DPair.fst

public export
SPDynSysAct : {x : Type} -> (f : SPFData x x) -> (sys : spfdDynSys {x} f) ->
  spfdDynSysAct {x} (SPDynSysCoeff f sys) f
SPDynSysAct {x} f = DPair.snd

public export
spfdDynSysToMonSl : {x : Type} -> {p : SPFData x x} ->
  spfdDynSys {x} p -> spfdMonSl {dom=x} {cod=x} p
spfdDynSysToMonSl {x} {p} sys =
  (SPDynSysCoeff {x} p sys ** SPDynSysCoeff {x} p sys ** SPDynSysAct {x} p sys)

public export
SPDynSysOnPos : {x : Type} -> (f : SPFData x x) -> (sys : spfdDynSys {x} f) ->
  SPFDmultiIdx f (SPDynSysCoeff f sys)
SPDynSysOnPos {x} f sys = spOnPos (SPDynSysAct f sys)

public export
spfdDynSysActToCoalgAct : {x : Type} ->
  (coeff : SliceObj x) -> (p : SPFData x x) ->
  spfdDynSysAct {x} coeff p -> spfdCoalgAction {x} p coeff
spfdDynSysActToCoalgAct {x} coeff = spfdMonNTtoInj {dom=x} {cod=x} coeff coeff

public export
spfdDynSysActToCoalg : {x : Type} ->
  (coeff : SliceObj x) -> (p : SPFData x x) ->
  spfdDynSysAct {x} coeff p -> SPCoalg {x} p
spfdDynSysActToCoalg {x} coeff p sys =
  (coeff ** spfdDynSysActToCoalgAct {x} coeff p sys)

public export
spfdCoalgActToDynSysAct : {x : Type} ->
  (coeff : SliceObj x) -> (p : SPFData x x) ->
  spfdCoalgAction {x} p coeff -> spfdDynSysAct {x} coeff p
spfdCoalgActToDynSysAct {x} coeff = spfdInjToMonNT {dom=x} {cod=x} coeff coeff

public export
spfdCoalgToDynSysAct : {x : Type} ->
  (p : SPFData x x) -> (coalg : SPCoalg {x} p) ->
  spfdDynSysAct {x} (SPCoalgCarrier {f=p} coalg) p
spfdCoalgToDynSysAct {x} p coalg =
  spfdCoalgActToDynSysAct {x} (SPCoalgCarrier coalg) p (SPCoalgAction coalg)

public export
spfdDynSysToCoalg : {x : Type} ->
  (p : SPFData x x) -> spfdDynSys {x} p -> SPCoalg {x} p
spfdDynSysToCoalg {x} p sys =
  (SPDynSysCoeff p sys **
   snd $ spfdDynSysActToCoalg (SPDynSysCoeff p sys) p (SPDynSysAct p sys))

public export
spfdCoalgToDynSys : {x : Type} ->
  (p : SPFData x x) -> (coalg : SPCoalg {x} p) -> spfdDynSys {x} p
spfdCoalgToDynSys {x} p coalg =
  (SPCoalgCarrier coalg **
   spfdCoalgActToDynSysAct {x} (SPCoalgCarrier coalg) p (SPCoalgAction coalg))

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

-------------------------------------------------------------
---- Polynomial coalgebra morphisms from slice morphisms ----
-------------------------------------------------------------

public export
spMonSlMultiIdx : {dom, cod : Type} ->
  (p : SPFData dom cod) -> spfdMonSl {dom} {cod} p -> SliceObj cod -> Type
spMonSlMultiIdx {dom} {cod} p sl =
  flip (SliceMorphism {a=cod}) (spfdMonSlCoeff {dom} {cod} {p} sl)

public export
spDynSysMultiIdx : {x : Type} ->
  (f : SPFData x x) -> spfdDynSys {x} f -> SliceObj x -> Type
spDynSysMultiIdx {x} f sys = flip (SliceMorphism {a=x}) (SPDynSysCoeff f sys)

public export
spMonSlCoeffCovarHom : {dom, cod : Type} ->
  (p : SPFData dom cod) -> spfdMonSl {dom} {cod} p -> SliceObj cod -> Type
spMonSlCoeffCovarHom {dom} {cod} p sl =
  SliceMorphism {a=cod} (spfdMonSlCoeff {dom} {cod} {p} sl)

public export
spDynSysCoeffCovarHom : {x : Type} ->
  (f : SPFData x x) -> (sys : spfdDynSys {x} f) ->
  (a : SliceObj x) -> Type
spDynSysCoeffCovarHom {x} f sys = SliceMorphism {a=x} (SPDynSysCoeff f sys)

public export
spMonSlDirChange : {dom, cod : Type} ->
  {p : SPFData dom cod} -> (sl : spfdMonSl {dom} {cod} p) ->
  (pos : SliceObj cod) -> spMonSlMultiIdx {dom} {cod} p sl pos ->
  Type
spMonSlDirChange {dom} {cod} {p} sl pos m =
  (ec : cod ** ep : pos ec ** ed : dom **
   spfdDir p ec (spfdMonSlOnPos {p} sl ec $ m ec ep) ed) ->
  spMonSlCoeffCovarHom {dom} {cod} p sl pos

public export
spDynSysDirChange : {x : Type} ->
  (f : SPFData x x) -> (sys : spfdDynSys {x} f) ->
  (a : SliceObj x) -> spDynSysMultiIdx {x} f sys a ->
  Type
spDynSysDirChange {x} f sys a m =
  spMonSlDirChange {dom=x} {cod=x} {p=f}
    (spfdDynSysToMonSl {x} {p=f} sys) a m

public export
spDynSysSlMor : {x : Type} ->
  (f : SPFData x x) -> spfdDynSys {x} f -> SliceObj x -> Type
spDynSysSlMor {x} f sys a =
   DPair (spDynSysMultiIdx {x} f sys a) (spDynSysDirChange {x} f sys a)

-- Given a dynamical system, the following data determine a slice
-- object of it -- that is, another dynamical system with the same
-- polynomial functor, together with a morphism from that system to
-- the given system.  What it means to be a morphism of dynamical
-- systems is determined by the equivalence of dynamical systems with
-- coalgebras -- there is a standard definition of coalgebra morphism
-- which must, and can, simply be translated directly into the notion
-- of a morphism between the corresponding dynamical systems.
public export
spDynSysSl : {x : Type} -> (f : SPFData x x) -> spfdDynSys {x} f -> Type
spDynSysSl {x} f sys = DPair (SliceObj x) (spDynSysSlMor {x} f sys)

public export
spDynSysSlCarrier :
  {x : Type} -> {f : SPFData x x} -> {sys : spfdDynSys {x} f} ->
  spDynSysSl {x} f sys -> SliceObj x
spDynSysSlCarrier {x} {f} {sys} = DPair.fst

public export
spDynSysSlPosChange :
  {x : Type} -> {f : SPFData x x} -> {sys : spfdDynSys {x} f} ->
  (sl : spDynSysSl {x} f sys) ->
  spDynSysMultiIdx {x} f sys (spDynSysSlCarrier {x} {f} {sys} sl)
spDynSysSlPosChange {x} {f} {sys} sl = DPair.fst $ DPair.snd sl

public export
spDynSysSlDirChange :
  {x : Type} -> {f : SPFData x x} -> {sys : spfdDynSys {x} f} ->
  (sl : spDynSysSl {x} f sys) ->
  spDynSysDirChange {x} f sys
    (spDynSysSlCarrier {x} {f} {sys} sl)
    (spDynSysSlPosChange {x} {f} {sys} sl)
spDynSysSlDirChange {x} {f} {sys} sl = DPair.snd $ DPair.snd sl

public export
spDynSysSlOnPos :
  {x : Type} -> {f : SPFData x x} -> {sys : spfdDynSys {x} f} ->
  (sl : spDynSysSl {x} f sys) ->
  SliceMorphism {a=x} (spDynSysSlCarrier {x} {f} {sys} sl) (spfdPos f)
spDynSysSlOnPos {x} {f} {sys} sl =
  sliceComp {a=x} (SPDynSysOnPos f sys) (spDynSysSlPosChange {x} {f} {sys} sl)

public export
spDynSysSlOnDir :
  {x : Type} -> {f : SPFData x x} -> {sys : spfdDynSys {x} f} ->
  (sl : spDynSysSl {x} f sys) ->
  (ex : x) -> (esl : fst sl ex) ->
  SliceMorphism {a=x}
    (spfdDir f ex (spOnPos (snd sys) ex (fst (snd sl) ex esl)))
    (fst sl)
spDynSysSlOnDir {x} {f} {sys=(b ** SPFDm bpos bdir)} (a ** mab ** dc)
  ex esl ex' dd =
    dc (ex ** esl ** ex' ** dd) ex' $ bdir ex (mab ex esl) ex' dd

public export
spDynSysSlAct :
  {x : Type} -> {f : SPFData x x} -> {sys : spfdDynSys {x} f} ->
  (sl : spDynSysSl {x} f sys) ->
  spfdDynSysAct {x} (spDynSysSlCarrier {x} {f} {sys} sl) f
spDynSysSlAct {x} {f} {sys} sl =
  SPFDm (spDynSysSlOnPos {x} {f} {sys} sl) (spDynSysSlOnDir {x} {f} {sys} sl)

public export
spDynSysSlTot :
  {x : Type} -> {f : SPFData x x} -> {sys : spfdDynSys {x} f} ->
  (sl : spDynSysSl {x} f sys) -> spfdDynSys {x} f
spDynSysSlTot {x} {f} {sys} sl = (spDynSysSlCarrier sl ** spDynSysSlAct sl)

public export
SPDynSysBun : {x : Type} -> SPFData x x -> Type
SPDynSysBun {x} f = DPair (spfdDynSys {x} f) (spDynSysSl {x} f)

public export
SPDynSysBunCod : {x : Type} -> {f : SPFData x x} ->
  SPDynSysBun {x} f -> spfdDynSys {x} f
SPDynSysBunCod {x} {f} = DPair.fst

public export
SPDynSysBunSl : {x : Type} -> {f : SPFData x x} ->
  (bun : SPDynSysBun {x} f) -> spDynSysSl {x} f (SPDynSysBunCod {x} {f} bun)
SPDynSysBunSl {x} {f} = DPair.snd

public export
SPDynSysBunDom : {x : Type} -> {f : SPFData x x} ->
  SPDynSysBun {x} f -> spfdDynSys {x} f
SPDynSysBunDom {x} {f} bun =
  spDynSysSlTot {x} {f}
    {sys=(SPDynSysBunCod {x} {f} bun)}
    (SPDynSysBunSl {x} {f} bun)

public export
data SPDynSysMorF : {x : Type} -> (f : SPFData x x) ->
    IntMorSig (spfdDynSys {x} f) where
  SDSm : {x : Type} -> {f : SPFData x x} ->
    (bun : SPDynSysBun {x} f) ->
    SPDynSysMorF {x} f (SPDynSysBunDom {x} {f} bun) (SPDynSysBunCod {x} {f} bun)

public export
SPCoalgMorF : {x : Type} -> (f : SPFData x x) -> IntMorSig (SPCoalg {x} f)
SPCoalgMorF {x} f a b =
  SPDynSysMorF {x} f (spfdCoalgToDynSys {x} f a) (spfdCoalgToDynSys {x} f b)

public export
data SPCoalgF : {x : Type} -> (f : SPFData x x) -> (aalg, balg : SPCoalg f) ->
    Type where
  SPcoalg : {x : Type} -> {f : SPFData x x} -> {a, b : SliceObj x} ->
    (m : SliceMorphism {a=x} a b) ->
    (bp : SliceMorphism {a=x} b (spfdPos f)) ->
    (bd : (ex : x) -> (eb : b ex) ->
      SliceMorphism {a=x} (spfdDir f ex $ bp ex eb) a) ->
    SPCoalgF {x} f
      (a ** \ex, ea => (bp ex (m ex ea) ** bd ex (m ex ea)))
      (b ** \ex, eb => (bp ex eb ** \ex' => m ex' . bd ex eb ex'))

public export
SPCoalgSl : {x : Type} -> (f : SPFData x x) -> (aalg, balg : SPCoalg f) -> Type
SPCoalgSl {x} (SPFD pos dir) (a ** aact) (b ** bact) =
  (m : SliceMorphism {a=x} a b **
   pcomm :
    (ex : x) -> (ea : a ex) -> fst (aact ex ea) = fst (bact ex $ m ex ea) **
   (ex, ex' : x) -> (ea : a ex) ->
    (dd : dir ex (fst $ bact ex $ m ex ea) ex') ->
    m ex' (snd (aact ex ea) ex' $ rewrite pcomm ex ea in dd) =
    snd (bact ex $ m ex ea) ex' dd)

public export
SPCoalgFtoSl : {x : Type} -> (f : SPFData x x) -> (aalg, balg : SPCoalg f) ->
  SPCoalgF {x} f aalg balg -> SPCoalgSl {x} f aalg balg
SPCoalgFtoSl {x} _ (a ** _) (b ** _)
  (SPcoalg {x} {f=(SPFD pos dir)} {a} {b} m bp bd) =
    (m ** \_, _ => Refl ** \ex, ex', ea, dd => Refl)

public export
spCoalgSlAct : {x : Type} -> (f : SPFData x x) -> (aalg, balg : SPCoalg f) ->
  SPCoalgSl {x} f aalg balg -> SPCoalgMap {f} aalg balg
spCoalgSlAct {x} (SPFD pos dir) (a ** aact) (b ** bact) sl =
  fst sl

public export
spCoalgSlComm : {x : Type} -> (f : SPFData x x) ->
  (aalg, balg : SPCoalg {x} f) -> (sl : SPCoalgSl {x} f aalg balg) ->
  SPCoalgComm {a=aalg} {b=balg} {f} (spCoalgSlAct {x} f aalg balg sl)
spCoalgSlComm {x} (SPFD pos dir) (a ** aact) (b ** bact)
    (m ** pcomm ** dcomm) fext ex ea
    with (aact ex ea) proof aeq
  spCoalgSlComm {x} (SPFD pos dir) (a ** aact) (b ** bact)
      (m ** pcomm ** dcomm) fext ex ea | (ai ** adm)
      with (bact ex $ m ex ea) proof beq
    spCoalgSlComm {x} (SPFD pos dir) (a ** aact) (b ** bact)
      (m ** pcomm ** dcomm) fext ex ea | (ai ** adm) | (bi ** bdm) =
        case trans (sym $ dpeq1 beq) (trans (sym $ pcomm ex ea) (dpeq1 aeq)) of
          Refl =>
            dpEq12
              Refl
              $ funExt $ \ex' => funExt $ \dd =>
                trans
                  (case dpeq1 beq of
                    Refl => fcongdep $ fcongdep (sym $ dpeq2 beq))
                (trans
                    (sym $ dcomm ex ex' ea (rewrite dpeq1 beq in dd))
                    (cong
                      (m ex')
                      (case dpeq1 aeq of
                        Refl => fcongdep $ fcongdep $ dpeq2 aeq)))

public export
spCoalgSlToMor : {x : Type} -> (f : SPFData x x) -> (aalg, balg : SPCoalg f) ->
  SPCoalgSl {x} f aalg balg -> SPCoalgMor {f} aalg balg
spCoalgSlToMor {x} f aalg balg sl =
  (spCoalgSlAct {x} f aalg balg sl ** spCoalgSlComm {x} f aalg balg sl)

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

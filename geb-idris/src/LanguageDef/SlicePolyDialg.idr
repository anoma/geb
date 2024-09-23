module LanguageDef.SlicePolyDialg

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.SlicePolyCat
import public LanguageDef.SlicePolyUMorph
import public LanguageDef.MLDirichCat

-- Profunctors, algebras, coalgebras, dialgebras, and comma categories of
-- slice polynomial functors.

--------------------------------------
--------------------------------------
---- Slice polynomial profunctors ----
--------------------------------------
--------------------------------------

-- We begin with a dependent-slice-polynomial expression of difunctors
-- on `Type` (that is, profunctors of the form `op(Type) -> Type -> Type`).

public export
record MLPolyDiFDirs (pos : Type) where
  mpdpContraDir : SliceObj pos
  mpdpCovarDir : SliceObj pos
  mpdpDepDir : (i : pos) -> mpdpCovarDir i -> mpdpContraDir i -> Type

public export
InterpMLPDFP : {pos : Type} -> (mpdp : MLPolyDiFDirs pos) ->
  pos -> ProfunctorSig
InterpMLPDFP {pos} mpdp i1 j z =
  (d1 : j -> mpdpContraDir mpdp i1 **
   (d2 : mpdpCovarDir mpdp i1) -> Pi {a=j} (mpdpDepDir mpdp i1 d2 . d1) -> z)

public export
record MLPolyDiF where
  mpdPos : Type
  mpdDirs : MLPolyDiFDirs mpdPos

public export
mpdContraDir : (mpd : MLPolyDiF) -> SliceObj (mpdPos mpd)
mpdContraDir mpd = mpdpContraDir $ mpdDirs mpd

public export
mpdCovarDir : (mpd : MLPolyDiF) -> SliceObj (mpdPos mpd)
mpdCovarDir mpd = mpdpCovarDir $ mpdDirs mpd

public export
mpdDepDir : (mpd : MLPolyDiF) ->
  (i : mpdPos mpd) -> mpdCovarDir mpd i -> mpdContraDir mpd i -> Type
mpdDepDir mpd = mpdpDepDir $ mpdDirs mpd

public export
InterpMLPDF : MLPolyDiF -> ProfunctorSig
InterpMLPDF mpd j z =
  (i1 : mpdPos mpd ** InterpMLPDFP {pos=(mpdPos mpd)} (mpdDirs mpd) i1 j z)

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

-- Formula 6.65 from _Polynomial Functors: A Mathematical Theory of
-- Interaction_.

public export
spfdMonNTtoInj : {dom, cod : Type} ->
  (coeff : SliceObj cod) -> (degree : SliceObj dom) -> (p : SPFData dom cod) ->
  spfdMonCovarRep {dom} {cod} coeff degree p ->
  SliceMorphism {a=cod} coeff (InterpSPFData p degree)
spfdMonNTtoInj {dom} {cod} coeff degree p alpha ec n =
  (spOnPos alpha ec n ** \ed, pd => spOnDir alpha ec n ed pd)

public export
spfdInjToMonNT : {dom, cod : Type} ->
  (coeff : SliceObj cod) -> (degree : SliceObj dom) -> (p : SPFData dom cod) ->
  SliceMorphism {a=cod} coeff (InterpSPFData p degree) ->
  spfdMonCovarRep {dom} {cod} coeff degree p
spfdInjToMonNT {dom} {cod} coeff degree p m =
  SPFDm (\ec, n => fst $ m ec n) (\ec, n => snd $ m ec n)

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

public export
spfdMonSlToSl : {dom, cod : Type} -> {p : SPFData dom cod} ->
  spfdMonSl {dom} {cod} p -> SPFDslObj {dom} {cod} p
spfdMonSlToSl {dom} {cod} {p} sl =
  (spfdMonSlTot {dom} {cod} {p} sl ** spfdMonSlProj {dom} {cod} {p} sl)

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

public export
spfdMonSlmultiR12 : {dom, cod : Type} -> {p : SPFData dom cod} ->
  (sl : spfdMonSl {dom} {cod} p) ->
  SPFDmultiR12 {dom} {cod} p (spfdMonSlCoeff {p} sl) (spfdMonSlDegree {p} sl)
spfdMonSlmultiR12 {dom} {cod} {p} sl =
  (spfdMonSlOnPos {p} sl ** spfdMonSlOnDir {p} sl)

public export
spfdMonSlmultiR : {dom, cod : Type} -> {p : SPFData dom cod} ->
  (sl : spfdMonSl {dom} {cod} p) ->
  SliceMorphism {a=cod}
    (spfdMonSlCoeff {p} sl)
    (SPFDmultiR p $ spfdMonSlDegree {p} sl)
spfdMonSlmultiR {dom} {cod} {p} sl =
  SPFDmultiRfrom12 {dom} {cod} {spfd=p}
    {a=(spfdMonSlDegree {p} sl)}
    {b=(spfdMonSlCoeff {p} sl)}
    (spfdMonSlmultiR12 {dom} {cod} {p} sl)

public export
spfdMonSlEquivMultiRInj : FunExt ->
  {dom, cod : Type} -> {p : SPFData dom cod} ->
  (sl : spfdMonSl {dom} {cod} p) ->
  (spfdMonSlmultiR {dom} {cod} {p} sl) =
  (spfdMonNTtoInj {dom} {cod}
    (spfdMonSlCoeff {p} sl) (spfdMonSlDegree {p} sl) p (spfdMonSlProj {p} sl))
spfdMonSlEquivMultiRInj fext {dom} {cod} {p} sl =
  funExt $ \ec => funExt $ \ep => Refl

public export
spfdMonSlEquivMonNTproj :
  {dom, cod : Type} -> {p : SPFData dom cod} ->
  (sl : spfdMonSl {dom} {cod} p) ->
  (spfdMonSlProj {dom} {cod} {p} sl) =
  (spfdInjToMonNT {dom} {cod}
    (spfdMonSlCoeff {p} sl) (spfdMonSlDegree {p} sl) p (spfdMonSlmultiR {p} sl))
spfdMonSlEquivMonNTproj {dom} {cod} {p}
  (coeff ** degree ** SPFDm onpos ondir) =
    Refl

-- A natural transformation between monomials takes a simple,
-- non-dependent form.

public export
spfdMonMonNTpos : {cod : Type} -> (dcoeff, ccoeff : SliceObj cod) -> Type
spfdMonMonNTpos {cod} dcoeff ccoeff = SliceMorphism {a=cod} dcoeff ccoeff

public export
spfdMonMonNTdir : {cod : Type} ->
  {dcoeff, ccoeff : SliceObj cod} ->
  spfdMonMonNTpos {cod} dcoeff ccoeff ->
  {dom : Type} ->
  (ddegree, cdegree : SliceObj dom) ->
  Type
spfdMonMonNTdir {cod} {dcoeff} {ccoeff} onpos {dom} ddegree cdegree =
  Sigma {a=cod} dcoeff -> SliceMorphism {a=dom} cdegree ddegree

public export
spfdMonMonNT : {dom, cod : Type} ->
  (dcoeff, ccoeff : SliceObj cod) ->
  (ddegree, cdegree : SliceObj dom) ->
  Type
spfdMonMonNT {dom} {cod} dcoeff ccoeff ddegree cdegree =
  (onpos : spfdMonMonNTpos {cod} dcoeff ccoeff **
   spfdMonMonNTdir {cod} onpos {dom} ddegree cdegree)

public export
spfdMonMonNTonpos : {dom, cod : Type} ->
  {dcoeff, ccoeff : SliceObj cod} ->
  {ddegree, cdegree : SliceObj dom} ->
  spfdMonMonNT {dom} {cod} dcoeff ccoeff ddegree cdegree ->
  spfdMonMonNTpos {cod} dcoeff ccoeff
spfdMonMonNTonpos {dom} {cod} {dcoeff} {ccoeff} {ddegree} {cdegree} = DPair.fst

public export
spfdMonMonNTondir : {dom, cod : Type} ->
  {dcoeff, ccoeff : SliceObj cod} ->
  {ddegree, cdegree : SliceObj dom} ->
  (nt : spfdMonMonNT {dom} {cod} dcoeff ccoeff ddegree cdegree) ->
  spfdMonMonNTdir {cod} (spfdMonMonNTonpos nt) {dom} ddegree cdegree
spfdMonMonNTondir {dom} {cod} {dcoeff} {ccoeff} {ddegree} {cdegree} = DPair.snd

public export
spfdMonMonNTtoSPFnt : {dom, cod : Type} ->
  {dcoeff, ccoeff : SliceObj cod} ->
  {ddegree, cdegree : SliceObj dom} ->
  spfdMonMonNT {dom} {cod} dcoeff ccoeff ddegree cdegree ->
  SPFnt {dom} {cod}
    (spfdMonomial {dom} {cod} dcoeff ddegree)
    (spfdMonomial {dom} {cod} ccoeff cdegree)
spfdMonMonNTtoSPFnt {dom} {cod} {dcoeff} {ccoeff} {ddegree} {cdegree} nt =
  SPFDm (spfdMonMonNTonpos nt) (\ec, edc => spfdMonMonNTondir nt (ec ** edc))

public export
spfdMonMonNTfromSPFnt : {dom, cod : Type} ->
  {dcoeff, ccoeff : SliceObj cod} ->
  {ddegree, cdegree : SliceObj dom} ->
  SPFnt {dom} {cod}
    (spfdMonomial {dom} {cod} dcoeff ddegree)
    (spfdMonomial {dom} {cod} ccoeff cdegree) ->
  spfdMonMonNT {dom} {cod} dcoeff ccoeff ddegree cdegree
spfdMonMonNTfromSPFnt {dom} {cod} {dcoeff} {ccoeff} {ddegree} {cdegree} nt =
  (spOnPos nt ** \ecdc => spOnDir nt (fst ecdc) (snd ecdc))

-- Definition 4.18 from _Polynomial Functors:  A Mathematical Theory
-- of Interaction_:  a "dynamical system" is a lens (natural transformation)
-- whose domain is a symmetric monomial.  The codomain (which may be any
-- polynomial functor) is known as the "interface".
public export
spfdDynSysLens : {x : Type} -> (sl : SliceObj x) -> SPFData x x -> Type
spfdDynSysLens {x} sl = spfdMonCovarRep {dom=x} {cod=x} sl sl

public export
spfdDynSys : {x : Type} -> SPFData x x -> Type
spfdDynSys {x} p = (sl : SliceObj x ** spfdDynSysLens {x} sl p)

-- When we interpret a lens whose domain is a symmetric monomial as
-- a dynamical system, the coefficient (which is the same as the degree,
-- hence the term "symmetric") of the domain monomial is the type of states.
public export
SPDynSysState : {x : Type} -> (f : SPFData x x) ->
  spfdDynSys {x} f -> SliceObj x
SPDynSysState {x} f = DPair.fst

public export
SpDynSysLens : {x : Type} -> (f : SPFData x x) -> (sys : spfdDynSys {x} f) ->
  spfdDynSysLens {x} (SPDynSysState f sys) f
SpDynSysLens {x} f = DPair.snd

public export
spfdDynSysToMonSl : {x : Type} -> {p : SPFData x x} ->
  spfdDynSys {x} p -> spfdMonSl {dom=x} {cod=x} p
spfdDynSysToMonSl {x} {p} sys =
  (SPDynSysState {x} p sys ** SPDynSysState {x} p sys ** SpDynSysLens {x} p sys)

-- When we interpret a lens whose domain is a symmetric monomial as
-- a dynamical system, the on-positions function is the "return function".
public export
SPDynSysReturn : {x : Type} -> (f : SPFData x x) -> (sys : spfdDynSys {x} f) ->
  SPFDmultiR1 {cod=x} (spfdPos f) (SPDynSysState {x} f sys)
SPDynSysReturn {x} f sys = spOnPos (SpDynSysLens f sys)

-- When we interpret a lens whose domain is a symmetric monomial as
-- a dynamical system, the on-positions function is the "update map".
public export
SPDynSysUpdate : {x : Type} -> {f : SPFData x x} ->
  (sys : spfdDynSys {x} f) ->
  SPFDmultiR2 {dom=x} {cod=x} f
    {b=(SPDynSysState {x} f sys)}
    (SPDynSysReturn {x} f sys)
    (SPDynSysState {x} f sys)
SPDynSysUpdate {x} {f} sys = spOnDir (SpDynSysLens f sys)

public export
spfdDynSysLensToCoalgAct : {x : Type} ->
  (coeff : SliceObj x) -> (p : SPFData x x) ->
  spfdDynSysLens {x} coeff p -> spfdCoalgAction {x} p coeff
spfdDynSysLensToCoalgAct {x} coeff = spfdMonNTtoInj {dom=x} {cod=x} coeff coeff

public export
spfdDynSysLensToCoalg : {x : Type} ->
  (coeff : SliceObj x) -> (p : SPFData x x) ->
  spfdDynSysLens {x} coeff p -> SPCoalg {x} p
spfdDynSysLensToCoalg {x} coeff p sys =
  (coeff ** spfdDynSysLensToCoalgAct {x} coeff p sys)

public export
spfdCoalgActToDynSysLens : {x : Type} ->
  (coeff : SliceObj x) -> (p : SPFData x x) ->
  spfdCoalgAction {x} p coeff -> spfdDynSysLens {x} coeff p
spfdCoalgActToDynSysLens {x} coeff = spfdInjToMonNT {dom=x} {cod=x} coeff coeff

public export
spfdCoalgToDynSysLens : {x : Type} ->
  (p : SPFData x x) -> (coalg : SPCoalg {x} p) ->
  spfdDynSysLens {x} (SPCoalgCarrier {f=p} coalg) p
spfdCoalgToDynSysLens {x} p coalg =
  spfdCoalgActToDynSysLens {x} (SPCoalgCarrier coalg) p (SPCoalgAction coalg)

public export
spfdDynSysToCoalg : {x : Type} ->
  (p : SPFData x x) -> spfdDynSys {x} p -> SPCoalg {x} p
spfdDynSysToCoalg {x} p sys =
  (SPDynSysState p sys **
   snd $ spfdDynSysLensToCoalg (SPDynSysState p sys) p (SpDynSysLens p sys))

public export
spfdCoalgToDynSys : {x : Type} ->
  (p : SPFData x x) -> (coalg : SPCoalg {x} p) -> spfdDynSys {x} p
spfdCoalgToDynSys {x} p coalg =
  (SPCoalgCarrier coalg **
   spfdCoalgActToDynSysLens {x} (SPCoalgCarrier coalg) p (SPCoalgAction coalg))

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
  SPFDmultiIdx {cod} (spfdMonSlTot {dom} {cod} sl)

public export
spDynSysMultiIdx : {x : Type} ->
  (f : SPFData x x) -> spfdDynSys {x} f -> SliceObj x -> Type
spDynSysMultiIdx {x} f sys =
  spMonSlMultiIdx {dom=x} {cod=x} f $ spfdDynSysToMonSl {x} {p=f} sys

public export
spMonSlCoeffCovarHom : {dom, cod : Type} ->
  (p : SPFData dom cod) -> spfdMonSl {dom} {cod} p -> SliceObj cod -> Type
spMonSlCoeffCovarHom {dom} {cod} p sl =
  SliceMorphism {a=cod} (spfdMonSlCoeff {dom} {cod} {p} sl)

public export
spDynSysStateCovarHom : {x : Type} ->
  (f : SPFData x x) -> (sys : spfdDynSys {x} f) ->
  (a : SliceObj x) -> Type
spDynSysStateCovarHom {x} f sys =
  SliceMorphism {a=x} (SPDynSysState f sys)

-- Given an on-positions function into the total space of a monomial
-- slice object, this composes the projection after it to produce
-- an on-positions function into the base functor (the one being
-- sliced over).
public export
spfdMonSlPullbackPos : {dom, cod : Type} ->
  {p : SPFData dom cod} -> (sl : spfdMonSl {dom} {cod} p) ->
  {pos : SliceObj cod} -> spMonSlMultiIdx {dom} {cod} p sl pos ->
  SPFDmultiR1 {cod} (spfdPos p) pos
spfdMonSlPullbackPos {dom} {cod} {p} sl {pos} =
  sliceComp {a=cod} (spfdMonSlOnPos {p} sl)

public export
spfdDynSysPullbackPos : {x : Type} ->
  {f : SPFData x x} -> (sys : spfdDynSys {x} f) ->
  {pos : SliceObj x} -> spDynSysMultiIdx {x} f sys pos ->
  SPFDmultiR1 {cod=x} (spfdPos f) pos
spfdDynSysPullbackPos {x} {f} sys {pos} =
  spfdMonSlPullbackPos {dom=x} {cod=x} (spfdDynSysToMonSl {x} {p=f} sys)

-- Given an on-positions function into the total space of a monomial
-- slice object, this pulls back the directions of the base functor
-- via the composition of the projection after the given on-positions
-- function given by `spfdMonSlPullbackPos`.
public export
spfdMonSlPosChangeDir : {dom, cod : Type} ->
  {p : SPFData dom cod} -> (sl : spfdMonSl {dom} {cod} p) ->
  {pos : SliceObj cod} -> spMonSlMultiIdx {dom} {cod} p sl pos ->
  SPFdirType dom cod pos
spfdMonSlPosChangeDir {dom} {cod} {p} sl {pos} =
  SPFDposChangeDir {dom} {cod} p {pos} .
    spfdMonSlPullbackPos {dom} {cod} {p} sl {pos}

public export
spfdDynSysPosChangeDir : {x : Type} ->
  {f : SPFData x x} -> (sys : spfdDynSys {x} f) ->
  {pos : SliceObj x} -> spDynSysMultiIdx {x} f sys pos ->
  SPFdirType x x pos
spfdDynSysPosChangeDir {x} {f} sys {pos} =
  spfdMonSlPosChangeDir {dom=x} {cod=x} $ spfdDynSysToMonSl {x} {p=f} sys

-- This is the functor resulting from pulling back the directions of the
-- base functor of a slice object along an on-positions function which is
-- a composition with the on-positions component of the slice object's
-- projection.
--
-- That makes it the intermediate object of a natural transformation
-- from a functor whose positions are specified by `pos` but whose
-- directions have not yet been specified, where that natural transformation
-- is a precomposition of a natural transformation to the total space
-- of the slice object, before the projection morphism of the slice object.
public export
spMonSlSPFchange : {dom, cod : Type} ->
  {p : SPFData dom cod} -> (sl : spfdMonSl {dom} {cod} p) ->
  {pos : SliceObj cod} -> spMonSlMultiIdx {dom} {cod} p sl pos ->
  SPFData dom cod
spMonSlSPFchange {dom} {cod} {p} sl {pos} m =
  SPFD pos (spfdMonSlPosChangeDir {dom} {cod} {p} sl {pos} m)

-- The total space of all directions of `spMonSlSPFchange` at the given
-- point in `dom`.
public export
spMonSlDirChangeDom : {dom, cod : Type} ->
  {p : SPFData dom cod} -> (sl : spfdMonSl {dom} {cod} p) ->
  (pos : SliceObj cod) -> spMonSlMultiIdx {dom} {cod} p sl pos ->
  SliceObj dom
spMonSlDirChangeDom {dom} {cod} {p} sl pos m ed =
  (ec : cod ** ep : pos ec **
   spfdDir (spMonSlSPFchange {dom} {cod} {p} sl {pos} m) ec ep ed)

-- The type of a morphism from the total directions of `spMonSlSPFchange`
-- to the type of the coefficient of the slice object -- which may be
-- viewed as a choice of a term of the coefficient for each such direction.
public export
spMonSlDirChange : {dom, cod : Type} ->
  {p : SPFData dom cod} -> (sl : spfdMonSl {dom} {cod} p) ->
  (pos : SliceObj cod) -> spMonSlMultiIdx {dom} {cod} p sl pos ->
  Type
spMonSlDirChange {dom} {cod} {p} sl pos m =
  SliceMorphism {a=dom}
    (spMonSlDirChangeDom {dom} {cod} {p} sl pos m)
    (\_ : dom => spMonSlCoeffCovarHom {dom} {cod} p sl pos)

public export
spDynSysDirChange : {x : Type} ->
  (f : SPFData x x) -> (sys : spfdDynSys {x} f) ->
  (a : SliceObj x) -> spDynSysMultiIdx {x} f sys a ->
  Type
spDynSysDirChange {x} f sys =
  spMonSlDirChange {dom=x} {cod=x} {p=f} $ spfdDynSysToMonSl {x} {p=f} sys

public export
spMonSlMor : {dom, cod : Type} ->
  (p : SPFData dom cod) -> spfdMonSl {dom} {cod} p -> SliceObj cod -> Type
spMonSlMor {dom} {cod} p sl a =
  DPair
    (spMonSlMultiIdx {dom} {cod} p sl a)
    (spMonSlDirChange {dom} {cod} {p} sl a)

public export
spDynSysSlMor : {x : Type} ->
  (f : SPFData x x) -> spfdDynSys {x} f -> SliceObj x -> Type
spDynSysSlMor {x} f sys a =
  spMonSlMor {dom=x} {cod=x} f (spfdDynSysToMonSl {x} {p=f} sys) a

public export
spMonSlGenEl : {dom, cod : Type} ->
  (p : SPFData dom cod) -> spfdMonSl {dom} {cod} p -> Type
spMonSlGenEl {dom} {cod} p sl =
  DPair (SliceObj cod) (spMonSlMor {dom} {cod} p sl)

public export
spMonSlGenElDom : {dom, cod : Type} ->
  {p : SPFData dom cod} -> {sl : spfdMonSl {dom} {cod} p} ->
  spMonSlGenEl {dom} {cod} p sl -> SliceObj cod
spMonSlGenElDom {dom} {cod} {p} {sl} = DPair.fst

public export
spMonSlGenElMor : {dom, cod : Type} ->
  {p : SPFData dom cod} -> {sl : spfdMonSl {dom} {cod} p} ->
  (el : spMonSlGenEl {dom} {cod} p sl) ->
  spMonSlMor {dom} {cod} p sl (spMonSlGenElDom {dom} {cod} {p} {sl} el)
spMonSlGenElMor {dom} {cod} {p} {sl} = DPair.snd

public export
spMonSlGenElPosChange : {dom, cod : Type} ->
  {p : SPFData dom cod} -> {sl : spfdMonSl {dom} {cod} p} ->
  (el : spMonSlGenEl {dom} {cod} p sl) ->
  spMonSlMultiIdx {dom} {cod} p sl (spMonSlGenElDom {dom} {cod} {p} {sl} el)
spMonSlGenElPosChange {dom} {cod} {p} {sl} el = DPair.fst $ DPair.snd el

public export
spMonSlGenElDirChange : {dom, cod : Type} -> {p : SPFData dom cod} ->
  {sl : spfdMonSl {dom} {cod} p} ->
  (el : spMonSlGenEl {dom} {cod} p sl) ->
  spMonSlDirChange {dom} {cod} {p} sl
    (spMonSlGenElDom {dom} {cod} {p} {sl} el)
    (spMonSlGenElPosChange {dom} {cod} {p} {sl} el)
spMonSlGenElDirChange {dom} {cod} {p} {sl} el = DPair.snd $ DPair.snd el

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
spDynSysSl {x} f sys =
  spMonSlGenEl {dom=x} {cod=x} f $ spfdDynSysToMonSl {x} {p=f} sys

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
  sliceComp {a=x} (SPDynSysReturn f sys) (spDynSysSlPosChange {x} {f} {sys} sl)

public export
spDynSysSlOnDir :
  {x : Type} -> {f : SPFData x x} -> {sys : spfdDynSys {x} f} ->
  (sl : spDynSysSl {x} f sys) ->
  (ex : x) -> (esl : fst sl ex) ->
  SliceMorphism {a=x}
    (spfdDir f
      ex
      (spOnPos
        (SpDynSysLens {x} f sys)
        ex
        (spDynSysSlPosChange {x} {f} {sys} sl ex esl)))
    (spDynSysSlCarrier {x} {f} {sys} sl)
spDynSysSlOnDir {x} {f} {sys=(b ** SPFDm bpos bdir)} (a ** mab ** dc)
  ex esl ex' dd =
    dc ex' (ex ** esl ** dd) ex' $ bdir ex (mab ex esl) ex' dd

public export
spDynSysSlAct :
  {x : Type} -> {f : SPFData x x} -> {sys : spfdDynSys {x} f} ->
  (sl : spDynSysSl {x} f sys) ->
  spfdDynSysLens {x} (spDynSysSlCarrier {x} {f} {sys} sl) f
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
SPDynSysMorFBun : {x : Type} -> {f : SPFData x x} ->
    {sysd, sysc : spfdDynSys {x} f} ->
    SPDynSysMorF {x} f sysd sysc -> SPDynSysBun {x} f
SPDynSysMorFBun {x} {f} (SDSm bun) = bun

public export
SPCoalgMorF : {x : Type} -> (f : SPFData x x) -> IntMorSig (SPCoalg {x} f)
SPCoalgMorF {x} f a b =
  SPDynSysMorF {x} f (spfdCoalgToDynSys {x} f a) (spfdCoalgToDynSys {x} f b)

public export
spfdCoalgR2 :
  {x : Type} -> (f : SPFData x x) -> {a, b : SliceObj x} ->
  (m : SliceMorphism {a=x} a b) ->
  (b1 : SliceMorphism {a=x} b (spfdPos f)) ->
  Type
spfdCoalgR2 {x} f {a} {b} m b1 =
  (ec : x) -> (ep : spfdPos f ec) ->
  SliceMorphism {a=x} (spfdDir f ec ep) a

public export
spfdCoalgDepMor : {x : Type} -> (f : SPFData x x) -> (a, b : SliceObj x) -> Type
spfdCoalgDepMor {x} f a b =
  (m : SliceMorphism {a=x} a b **
   b1 : SliceMorphism {a=x} b (spfdPos f) **
   spfdCoalgR2 {x} f {a} {b} m b1)

public export
spfdCoalgDepMorBase : {x : Type} -> {f : SPFData x x} -> {a, b : SliceObj x} ->
  spfdCoalgDepMor {x} f a b -> SliceMorphism {a=x} a b
spfdCoalgDepMorBase {x} {f} {a} {b} = DPair.fst

public export
spfdCoalgDepMorR1 : {x : Type} -> {f : SPFData x x} -> {a, b : SliceObj x} ->
  spfdCoalgDepMor {x} f a b -> SliceMorphism {a=x} b (spfdPos f)
spfdCoalgDepMorR1 {x} {f} {a} {b} dm = DPair.fst $ DPair.snd dm

public export
spfdCoalgDepMorCod1 : {x : Type} -> {f : SPFData x x} -> {a, b : SliceObj x} ->
  spfdCoalgDepMor {x} f a b -> SPFDmultiR1 {cod=x} (spfdPos f) b
spfdCoalgDepMorCod1 = spfdCoalgDepMorR1

public export
spfdCoalgDepMorDom1 : {x : Type} -> {f : SPFData x x} -> {a, b : SliceObj x} ->
  spfdCoalgDepMor {x} f a b -> SPFDmultiR1 {cod=x} (spfdPos f) a
spfdCoalgDepMorDom1 {x} {f} {a} {b} dm =
  sliceComp {a=x}
    (spfdCoalgDepMorR1 {x} {f} {a} {b} dm)
    (spfdCoalgDepMorBase {x} {f} {a} {b} dm)

public export
spfdCoalgDepMorR2 : {x : Type} -> {f : SPFData x x} -> {a, b : SliceObj x} ->
  (dm : spfdCoalgDepMor {x} f a b) ->
  spfdCoalgR2 {x} f {a} {b}
    (spfdCoalgDepMorBase {x} {f} {a} {b} dm)
    (spfdCoalgDepMorCod1 {x} {f} {a} {b} dm)
spfdCoalgDepMorR2 {x} {f} {a} {b} dm = DPair.snd $ DPair.snd dm

public export
spfdCoalgDepMorDom2 : {x : Type} -> {f : SPFData x x} -> {a, b : SliceObj x} ->
  (dm : spfdCoalgDepMor {x} f a b) ->
  SPFDmultiR2 {dom=x} {cod=x} f (spfdCoalgDepMorDom1 {x} {f} {a} {b} dm) a
spfdCoalgDepMorDom2 {x} {f} {a} {b} dm ec ea =
  spfdCoalgDepMorR2 dm ec
  $ spfdCoalgDepMorR1 dm ec
  $ spfdCoalgDepMorBase dm ec ea

public export
spfdCoalgDepMorCod2 : {x : Type} -> {f : SPFData x x} -> {a, b : SliceObj x} ->
  (dm : spfdCoalgDepMor {x} f a b) ->
  SPFDmultiR2 {dom=x} {cod=x} f (spfdCoalgDepMorCod1 {x} {f} {a} {b} dm) b
spfdCoalgDepMorCod2 {x} {f} {a} {b} dm ec eb ed dd =
  spfdCoalgDepMorBase dm ed
  $ spfdCoalgDepMorR2 dm ec (spfdCoalgDepMorR1 dm ec eb) ed dd

public export
spfdCoalgDepMorDomAct :
  {x : Type} -> {f : SPFData x x} -> {a, b : SliceObj x} ->
  (dm : spfdCoalgDepMor {x} f a b) ->
  SliceMorphism {a=x} a (SPFDmultiR {dom=x} {cod=x} f a)
spfdCoalgDepMorDomAct {x} {f} {a} {b} dm =
  SPFDmultiRfrom12 (spfdCoalgDepMorDom1 dm ** spfdCoalgDepMorDom2 dm)

public export
spfdCoalgDepMorCodAct :
  {x : Type} -> {f : SPFData x x} -> {a, b : SliceObj x} ->
  (dm : spfdCoalgDepMor {x} f a b) ->
  SliceMorphism {a=x} b (SPFDmultiR {dom=x} {cod=x} f b)
spfdCoalgDepMorCodAct {x} {f} {a} {b} dm =
  SPFDmultiRfrom12 (spfdCoalgDepMorCod1 dm ** spfdCoalgDepMorCod2 dm)

public export
spfdCoalgDepMorDomAlg :
  {x : Type} -> {f : SPFData x x} -> {a, b : SliceObj x} ->
  spfdCoalgDepMor {x} f a b -> SPCoalg f
spfdCoalgDepMorDomAlg {x} {f} {a} {b} dm = (a ** spfdCoalgDepMorDomAct {f} dm)

public export
spfdCoalgDepMorCodAlg :
  {x : Type} -> {f : SPFData x x} -> {a, b : SliceObj x} ->
  spfdCoalgDepMor {x} f a b -> SPCoalg f
spfdCoalgDepMorCodAlg {x} {f} {a} {b} dm = (b ** spfdCoalgDepMorCodAct {f} dm)

public export
data SPCoalgF : {x : Type} -> (f : SPFData x x) -> (aalg, balg : SPCoalg f) ->
    Type where
  SPcoalg : {x : Type} -> {f : SPFData x x} -> {a, b : SliceObj x} ->
    (dm : spfdCoalgDepMor {x} f a b) ->
    SPCoalgF {x} f (spfdCoalgDepMorDomAlg {f} dm) (spfdCoalgDepMorCodAlg {f} dm)

public export
SPCoalgMorFromF : {x : Type} -> {f : SPFData x x} -> {aalg, balg : SPCoalg f} ->
  SPCoalgF {x} f aalg balg -> SPCoalgMor {f} aalg balg
SPCoalgMorFromF {x} {f} (SPcoalg dm) =
  (spfdCoalgDepMorBase dm **
   \fext, ec, ea => dpEq12 Refl $ funExt $ \ed => funExt $ \dd => Refl)

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
  (SPcoalg {x} {f=(SPFD pos dir)} {a} {b} (m ** bp ** bd)) =
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

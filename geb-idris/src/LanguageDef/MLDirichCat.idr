module LanguageDef.MLDirichCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import LanguageDef.QType
import public LanguageDef.InternalCat
import public LanguageDef.SliceFuncCat
import public LanguageDef.IntUFamCat

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

-------------------------------
-------------------------------
---- Objects and morphisms ----
-------------------------------
-------------------------------

public export
MLDirichCatObjPos : Type
MLDirichCatObjPos = Type

public export
MLDirichCatObjDir : MLDirichCatObjPos -> Type
MLDirichCatObjDir = SliceObj

public export
MLDirichCatObj : Type
MLDirichCatObj = Sigma {a=MLDirichCatObjPos} MLDirichCatObjDir

public export
dfPos : MLDirichCatObj -> Type
dfPos = DPair.fst

public export
dfDir : (p : MLDirichCatObj) -> dfPos p -> Type
dfDir = DPair.snd

public export
dfTot : MLDirichCatObj -> Type
dfTot p = Sigma {a=(dfPos p)} $ dfDir p

public export
MLDirichCatOnPos : MLDirichCatObj -> MLDirichCatObj -> Type
MLDirichCatOnPos p q = dfPos p -> dfPos q

public export
MLDirichCatOnDir : (p, q : MLDirichCatObj) -> MLDirichCatOnPos p q -> Type
MLDirichCatOnDir p q onpos =
  SliceMorphism {a=(dfPos p)} (dfDir p) (dfDir q . onpos)

public export
MLDirichCatMor : MLDirichCatObj -> MLDirichCatObj -> Type
MLDirichCatMor p q = Sigma {a=(MLDirichCatOnPos p q)} (MLDirichCatOnDir p q)

----------------------------------------------
----------------------------------------------
---- Interpretation of Dirichlet functors ----
----------------------------------------------
----------------------------------------------

-- Interpret the same data as determine a polynomial functor --
-- namely, a dependent set, AKA arena -- as a Dirichlet functor
-- (rather than a polynomial functor).  While a polynomial
-- functor is a sum of covariant representables, a Dirichlet
-- functor is a sum of contravariant representables.
public export
InterpDirichFunc : MLDirichCatObj -> Type -> Type
InterpDirichFunc p x = (i : dfPos p ** x -> dfDir p i)

public export
idfPos : {p : MLDirichCatObj} -> {a : Type} -> InterpDirichFunc p a -> dfPos p
idfPos = fst

public export
idfDir : {p : MLDirichCatObj} -> {a : Type} -> InterpDirichFunc p a -> Type
idfDir {p} {a} idf = dfDir p (idfPos {p} {a} idf)

public export
idfDirMap : {p : MLDirichCatObj} -> {a : Type} ->
  (idf : InterpDirichFunc p a) -> a -> idfDir {p} {a} idf
idfDirMap = DPair.snd

public export
idfDirCSl : {p : MLDirichCatObj} -> {a : Type} ->
  InterpDirichFunc p a -> Type
idfDirCSl {p} {a} idf = CSliceObj (idfDir {p} {a} idf)

public export
idfDirSl : {p : MLDirichCatObj} -> {a : Type} ->
  InterpDirichFunc p a -> Type
idfDirSl {p} {a} idf = SliceObj (idfDir {p} {a} idf)

public export
idfCSl : {p : MLDirichCatObj} -> {a : Type} ->
  (idf : InterpDirichFunc p a) -> idfDirCSl {p} idf
idfCSl {p} {a} idf = (a ** idfDirMap {p} {a} idf)

public export
idfSl : {p : MLDirichCatObj} -> {a : Type} ->
  (idf : InterpDirichFunc p a) -> idfDirSl {p} idf
idfSl {p} {a} idf = WSliceFromCSlice {c=(idfDir idf)} $ idfCSl {p} {a} idf

public export
InterpDFMap : (p : MLDirichCatObj) -> {0 a, b : Type} ->
  (a -> b) -> InterpDirichFunc p b -> InterpDirichFunc p a
InterpDFMap p m = dpMapSnd (\i => (|>) m)

public export
(p : MLDirichCatObj) => Contravariant (InterpDirichFunc p) where
  contramap {p} = InterpDFMap p

-------------------------------------------------------
-------------------------------------------------------
---- Natural transformations on Dirichlet functors ----
-------------------------------------------------------
-------------------------------------------------------

public export
DirichNatTrans : MLDirichCatObj -> MLDirichCatObj -> Type
DirichNatTrans = MLDirichCatMor

public export
dntOnPos : {0 p, q : MLDirichCatObj} -> DirichNatTrans p q ->
  dfPos p -> dfPos q
dntOnPos = DPair.fst

public export
dntOnDir : {0 p, q : MLDirichCatObj} -> (alpha : DirichNatTrans p q) ->
  (i : dfPos p) -> dfDir p i -> dfDir q (dntOnPos {p} {q} alpha i)
dntOnDir = DPair.snd

-- A natural transformation between Dirichlet functors may be viewed as a
-- morphism in the slice category of `Type` over `Type`.
public export
InterpDirichNT : {0 p, q : MLDirichCatObj} -> DirichNatTrans p q ->
  SliceMorphism {a=Type} (InterpDirichFunc p) (InterpDirichFunc q)
InterpDirichNT {p} {q} alpha a =
  dpBimap (dntOnPos alpha) (\i => (.) $ dntOnDir alpha i)

-------------------------------------------------------------------
---- Vertical composition of Dirichlet natural transformations ----
-------------------------------------------------------------------

public export
dntId : (p : MLDirichCatObj) -> DirichNatTrans p p
dntId p = (id ** \_ => id)

-- Vertical composition of natural transformations, which is the categorial
-- composition in the category of Dirichlet functors.
public export
dntVCatCompOnPos : {p, q, r : MLDirichCatObj} ->
  DirichNatTrans q r -> DirichNatTrans p q -> MLDirichCatOnPos p r
dntVCatCompOnPos {p} {q} {r} beta alpha =
  dntOnPos {p=q} {q=r} beta . dntOnPos {p} {q} alpha

public export
dntVCatCompOnDir : {p, q, r : MLDirichCatObj} ->
  (qr : DirichNatTrans q r) -> (pq : DirichNatTrans p q) ->
  MLDirichCatOnDir p r (dntVCatCompOnPos {p} {q} {r} qr pq)
dntVCatCompOnDir {p} {q} {r} beta alpha i =
  dntOnDir {p=q} {q=r} beta (dntOnPos {p} {q} alpha i)
  . dntOnDir {p} {q} alpha i

public export
dntVCatComp : {p, q, r : MLDirichCatObj} ->
  DirichNatTrans q r -> DirichNatTrans p q -> DirichNatTrans p r
dntVCatComp {p} {q} {r} beta alpha =
  (dntVCatCompOnPos {p} {q} {r} beta alpha **
   dntVCatCompOnDir {p} {q} {r} beta alpha)

---------------------------------------------------------------------------
---- Vertical-Cartesian factoring of Dirichlet natural transformations ----
---------------------------------------------------------------------------

public export
arBaseChangePos : (p : MLDirichCatObj) -> {a : Type} -> (a -> dfPos p) -> Type
arBaseChangePos p {a} f = a

public export
arBaseChangeDir : (p : MLDirichCatObj) -> {a : Type} -> (f : a -> dfPos p) ->
  arBaseChangePos p {a} f -> Type
arBaseChangeDir p {a} f i = dfDir p $ f i

public export
arBaseChangeArena : (p : MLDirichCatObj) ->
  {a : Type} -> (a -> dfPos p) -> MLDirichCatObj
arBaseChangeArena p {a} f = (arBaseChangePos p {a} f ** arBaseChangeDir p {a} f)

-- The intermediate Dirichlet functor in the vertical-Cartesian
-- factoring of a natural transformation between Dirichlet functors.
public export
DirichVertCartFactFunc : {p, q : MLDirichCatObj} ->
  DirichNatTrans p q -> MLDirichCatObj
DirichVertCartFactFunc {p} {q} alpha =
  arBaseChangeArena q {a=(dfPos p)} (dntOnPos alpha)

public export
DirichVertCartFactPos : {p, q : MLDirichCatObj} -> DirichNatTrans p q -> Type
DirichVertCartFactPos {p} {q} alpha =
  dfPos (DirichVertCartFactFunc {p} {q} alpha)

public export
DirichVertCartFactDir : {p, q : MLDirichCatObj} ->
  (alpha : DirichNatTrans p q) -> DirichVertCartFactPos {p} {q} alpha -> Type
DirichVertCartFactDir {p} {q} alpha =
  dfDir (DirichVertCartFactFunc {p} {q} alpha)

public export
DirichVertFactOnPos : {0 p, q : MLDirichCatObj} ->
  (alpha : DirichNatTrans p q) ->
  dfPos p -> DirichVertCartFactPos {p} {q} alpha
DirichVertFactOnPos alpha = id

public export
DirichVertFactOnDir :
  {0 p, q : MLDirichCatObj} -> (alpha : DirichNatTrans p q) ->
  (i : dfPos p) -> dfDir p i ->
  DirichVertCartFactDir {p} {q} alpha (DirichVertFactOnPos {p} {q} alpha i)
DirichVertFactOnDir = dntOnDir

public export
DirichVertFactNatTrans : {0 p, q : MLDirichCatObj} ->
  (alpha : DirichNatTrans p q) ->
  DirichNatTrans p (DirichVertCartFactFunc {p} {q} alpha)
DirichVertFactNatTrans {p} {q} alpha =
  (DirichVertFactOnPos {p} {q} alpha ** DirichVertFactOnDir {p} {q} alpha)

public export
DirichCartFactOnPos : {0 p, q : MLDirichCatObj} ->
  (alpha : DirichNatTrans p q) ->
  DirichVertCartFactPos {p} {q} alpha -> dfPos q
DirichCartFactOnPos = dntOnPos

public export
DirichCartFactOnDir :
  {0 p, q : MLDirichCatObj} -> (alpha : DirichNatTrans p q) ->
  (i : DirichVertCartFactPos {p} {q} alpha) ->
  DirichVertCartFactDir {p} {q} alpha i ->
  dfDir q (DirichCartFactOnPos {p} {q} alpha i)
DirichCartFactOnDir alpha i = id

public export
DirichCartFactNatTrans : {0 p, q : MLDirichCatObj} ->
  (alpha : DirichNatTrans p q) ->
  DirichNatTrans (DirichVertCartFactFunc {p} {q} alpha) q
DirichCartFactNatTrans {p} {q} alpha =
  (DirichCartFactOnPos {p} {q} alpha ** DirichCartFactOnDir {p} {q} alpha)

public export
0 DirichVertCartFactIsCorrect : FunExt -> {0 p, q : MLDirichCatObj} ->
  (alpha : DirichNatTrans p q) ->
  (dntVCatComp {p} {q=(DirichVertCartFactFunc {p} {q} alpha)} {r=q}
    (DirichCartFactNatTrans {p} {q} alpha)
    (DirichVertFactNatTrans {p} {q} alpha))
  = alpha
DirichVertCartFactIsCorrect fext
  {p=(ppos ** pdir)} {q=(qpos ** qdir)} (onpos ** ondir) =
    dpEq12 Refl $ funExt $ \i => Refl

------------------------------------------------------
------------------------------------------------------
---- Categories of elements of Dirichlet functors ----
------------------------------------------------------
------------------------------------------------------

-------------------------------
---- Objects and morphisms ----
-------------------------------

-- This definition makes it explicit that that the category of elements of a
-- Dirichlet endofunctor on `Type` is (equivalent to) the (indexed) coproduct
-- category over the positions of the slice categories over the directions.
-- (For a polynomial endofunctor on `Type`, the corresponding statement would
-- hold with "slice" replaced by "coslice".)

public export
DirichCatElObjDir : (p : MLDirichCatObj) -> dfPos p -> Type
DirichCatElObjDir p = SliceObj . dfDir {p}

public export
DirichCatElObjDirPair : (p : MLDirichCatObj) -> dfPos p -> Type
DirichCatElObjDirPair p = ProductMonad . DirichCatElObjDir p

public export
DirichCatElObj : MLDirichCatObj -> Type
DirichCatElObj p = Sigma {a=(dfPos p)} $ DirichCatElObjDir p

public export
DirichCatElObjPos : {p : MLDirichCatObj} -> DirichCatElObj p -> dfPos p
DirichCatElObjPos {p} = DPair.fst

public export
DirichCatElObjPair : MLDirichCatObj -> Type
DirichCatElObjPair = ProductMonad . DirichCatElObj

public export
DirichCatElBaseT : (p : MLDirichCatObj) -> DirichCatElObj p -> Type
DirichCatElBaseT p el = Sigma {a=(dfDir p (fst el))} (snd el)

public export
DirichCatElProj : (p : MLDirichCatObj) -> (el : DirichCatElObj p) ->
  DirichCatElBaseT p el -> dfDir p (fst el)
DirichCatElProj p el = DPair.fst

public export
DirichCatElPosMor : (p : MLDirichCatObj) -> (i : dfPos p) ->
  SliceObj (dfDir p i) -> SliceObj (dfDir p i) -> Type
DirichCatElPosMor p i = SliceMorphism {a=(dfDir p i)}

public export
DirichCatElMorTotPos : (p : MLDirichCatObj) -> dfPos p -> Type
DirichCatElMorTotPos p i =
  Sigma {a=(DirichCatElObjDirPair p i)} $
    \xy => DirichCatElPosMor p i (fst xy) (snd xy)

public export
DirichCatElMorTot : MLDirichCatObj -> Type
DirichCatElMorTot p = Sigma {a=(dfPos p)} $ DirichCatElMorTotPos p

public export
DirichCatElMorPos : {p : MLDirichCatObj} -> DirichCatElMorTot p -> dfPos p
DirichCatElMorPos {p} m = fst m

public export
DirichCatElMorBaseObj : {p : MLDirichCatObj} -> DirichCatElMorTot p -> Type
DirichCatElMorBaseObj {p} = DirichCatElObjDir p . DirichCatElMorPos {p}

public export
DirichCatElMorBaseObjPair : {p : MLDirichCatObj} -> DirichCatElMorTot p -> Type
DirichCatElMorBaseObjPair {p} = ProductMonad . DirichCatElMorBaseObj {p}

public export
DirichCatElMorBaseSig : {p : MLDirichCatObj} ->
  (m : DirichCatElMorTot p) -> DirichCatElMorBaseObjPair {p} m
DirichCatElMorBaseSig {p} m = fst $ snd m

public export
DirichCatElMorDom : {p : MLDirichCatObj} ->
  (m : DirichCatElMorTot p) -> DirichCatElMorBaseObj {p} m
DirichCatElMorDom {p} m = fst $ DirichCatElMorBaseSig {p} m

public export
DirichCatElMorCod : {p : MLDirichCatObj} ->
  (m : DirichCatElMorTot p) -> DirichCatElMorBaseObj {p} m
DirichCatElMorCod {p} m = snd $ DirichCatElMorBaseSig {p} m

public export
DirichCatElMorSig : {p : MLDirichCatObj} ->
  DirichCatElMorTot p -> DirichCatElObjPair p
DirichCatElMorSig {p} m =
  ((DirichCatElMorPos m ** DirichCatElMorDom m),
   (DirichCatElMorPos m ** DirichCatElMorCod m))

public export
DirichCatElMorMor : {p : MLDirichCatObj} ->
  (m : DirichCatElMorTot p) ->
  SliceMorphism {a=(dfDir p $ DirichCatElMorPos {p} m)}
    (DirichCatElMorDom {p} m)
    (DirichCatElMorCod {p} m)
DirichCatElMorMor {p} m = snd $ snd m

public export
DirichCatElMorP : {p : MLDirichCatObj} -> SliceObj (DirichCatElObjPair p)
DirichCatElMorP {p} =
  WPreImage {a=(DirichCatElMorTot p)} {b=(DirichCatElObjPair p)}
    (DirichCatElMorSig {p})

public export
DirichCatElMor : {p : MLDirichCatObj} -> IntMorSig (DirichCatElObj p)
DirichCatElMor {p} = curry $ DirichCatElMorP {p}

-- A natural transformation induces a functor between categories of elements
-- which commutes with the projections.

public export
DirichNTCatElOMap : {p, q : MLDirichCatObj} ->
  DirichNatTrans p q -> DirichCatElObj p -> DirichCatElObj q
DirichNTCatElOMap {p} {q} alpha =
  dpBimap (dntOnPos alpha) $ \pi => SliceFibSigmaF $ dntOnDir alpha pi

public export
0 DirichNTCatElFMap : {p, q : MLDirichCatObj} ->
  (alpha : DirichNatTrans p q) ->
  (x, y : DirichCatElObj p) ->
  DirichCatElMor {p} x y ->
  DirichCatElMor {p=q}
    (DirichNTCatElOMap {p} {q} alpha x)
    (DirichNTCatElOMap {p} {q} alpha y)
DirichNTCatElFMap {p} {q} (onpos ** ondir) (pi ** slx) (pi ** sly)
  (SFS (pi ** ((slx, sly) ** m)) ()) =
    SFS
      (onpos pi **
       ((SliceFibSigmaF (ondir pi) slx, SliceFibSigmaF (ondir pi) sly) **
        sfsMap {f=(ondir pi)} slx sly m))
      ()

---------------------------
---- Outgoing functors ----
---------------------------

-- Because the category of elements of a Dirichlet functor is a coproduct
-- category, a functor out of it is a product of functors.
--
-- In particular, a _Dirichlet_ functor on the category of elements of
-- a Dirichlet functor is a product of Dirichlet functors on the slice
-- categories of the directions of the base functor.
--
-- Note that another way of looking at a presheaf (of which Dirichlet functors
-- are an example) on the category of elements of a presheaf is as an object
-- of the slice category of presheaves over the base presheaf, so if this
-- definition makes sense then it ought to agree with `MlDirichSlObj`.
public export
DirichDirichCatElArPos : (p : MLDirichCatObj) -> dfPos p -> Type
DirichDirichCatElArPos p i = (pos : Type ** pos -> DirichCatElObjDir p i)

public export
DirichDirichCatElAr : MLDirichCatObj -> Type
DirichDirichCatElAr p = Pi {a=(dfPos p)} $ DirichDirichCatElArPos p

public export
DirichDirichCatElArMorPos : (b : MLDirichCatObj) -> (i : dfPos b) ->
  DirichDirichCatElArPos b i -> DirichDirichCatElArPos b i -> Type
DirichDirichCatElArMorPos b i j k =
  (onpos : fst k -> fst j **
   (p : fst k) -> SliceMorphism {a=(snd b i)} (snd k p) (snd j $ onpos p))

public export
DirichDirichCatElArMor : (b : MLDirichCatObj) ->
  DirichDirichCatElAr b -> DirichDirichCatElAr b -> Type
DirichDirichCatElArMor b p q =
  (i : dfPos b) -> DirichDirichCatElArMorPos b i (p i) (q i)

-------------------
-------------------
---- Monomials ----
-------------------
-------------------

public export
dfMonomialPos : Type -> Type -> Type
dfMonomialPos a b = a

public export
dfMonomialDir : (a, b : Type) -> dfMonomialPos a b -> Type
dfMonomialDir a b i = b

public export
dfMonomialArena : Type -> Type -> MLDirichCatObj
dfMonomialArena a b = (dfMonomialPos a b ** dfMonomialDir a b)

-----------------------------------------
-----------------------------------------
---- Dirichlet morphism factorization ---
-----------------------------------------
-----------------------------------------

{- See `PFMonoToCofunc` and 6.65 from "A General Theory of Interaction". -}

public export
DFMonoToFunc : {p : MLDirichCatObj} -> {a, b : Type} ->
  DirichNatTrans p (dfMonomialArena a b) -> InterpDirichFunc p a -> b
DFMonoToFunc {p} {a} {b} alpha el =
  dntOnDir {q=(dfMonomialArena a b)} alpha (fst el)
  $ snd el
  $ dntOnPos {q=(dfMonomialArena a b)} alpha (fst el)

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Slice categories of Dirichlet functors (in categorial style) ----
----------------------------------------------------------------------
----------------------------------------------------------------------

public export
CDFSliceObj : MLDirichCatObj -> Type
CDFSliceObj p = (q : MLDirichCatObj ** MLDirichCatMor q p)

public export
0 CDFNatTransEq :
  (p, q : MLDirichCatObj) -> (alpha, beta : MLDirichCatMor p q) -> Type
CDFNatTransEq (ppos ** pdir) (qpos ** qdir)
  (aonpos ** aondir) (bonpos ** bondir) =
    Exists0
      (ExtEq {a=ppos} {b=qpos} aonpos bonpos)
      $ \onposeq =>
        (i : ppos) -> (d : pdir i) ->
        bondir i d = replace {p=qdir} (onposeq i) (aondir i d)

public export
CDFSliceMorph : (p : MLDirichCatObj) -> CDFSliceObj p -> CDFSliceObj p -> Type
CDFSliceMorph p (q ** qp) (r ** rp) =
  Subset0 (MLDirichCatMor q r) (\qr => CDFNatTransEq q p qp (dntVCatComp rp qr))

-- A convenient (free of proof obligations) form of `CDFSliceMorph`; see
-- the comment to `PFSliceMorph` above.
public export
DFSliceMorph : {0 p : MLDirichCatObj} -> CDFSliceObj p -> Type
DFSliceMorph {p} (ctot ** alpha) =
  (dtot : MLDirichCatObj ** MLDirichCatMor dtot ctot)

public export
DFSliceMorphDom : {p : MLDirichCatObj} -> {cod : CDFSliceObj p} ->
  DFSliceMorph {p} cod -> CDFSliceObj p
DFSliceMorphDom {p} {cod=(ctot ** alpha)} (dtot ** beta) =
  (dtot ** dntVCatComp alpha beta)

public export
DFSliceMorphToC : {0 p : MLDirichCatObj} -> {cod : CDFSliceObj p} ->
  (mor : DFSliceMorph {p} cod) ->
  CDFSliceMorph p (DFSliceMorphDom {p} {cod} mor) cod
DFSliceMorphToC {p=(ppos ** pdir)} {cod=((ctot ** cproj) ** (conpos ** condir))}
  ((dtot ** dproj) ** (donpos ** dondir)) =
    Element0
      (donpos ** dondir)
      (Evidence0
        (\_ => Refl)
        (\_, _ => Refl))

public export
DFSliceMorphFromC : {0 p : MLDirichCatObj} -> {dom, cod : CDFSliceObj p} ->
  CDFSliceMorph p dom cod -> DFSliceMorph {p} cod
DFSliceMorphFromC {p=(ppos ** pdir)} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)}
  (Element0 alpha nteq) =
    (dtot ** alpha)

public export
DFSliceMorphFromCDomObjEq : {0 p : MLDirichCatObj} ->
  {dom, cod : CDFSliceObj p} -> (mor : CDFSliceMorph p dom cod) ->
  fst (DFSliceMorphDom {p} {cod} (DFSliceMorphFromC {p} {dom} {cod} mor)) =
  fst dom
DFSliceMorphFromCDomObjEq {p=(ppos ** pdir)}
  {dom=(dtot ** dproj)} {cod=(ctot ** cproj)} (Element0 alpha nteq) =
    Refl

public export
0 DFSliceMorphFromCDomMorEq : {0 p : MLDirichCatObj} ->
  {dtot, ctot : MLDirichCatObj} ->
  {dproj : MLDirichCatMor dtot p} ->
  {cproj : MLDirichCatMor ctot p} ->
  (mor : CDFSliceMorph p (dtot ** dproj) (ctot ** cproj)) ->
  CDFNatTransEq
    dtot p
    dproj
    (replace {p=(flip MLDirichCatMor p)}
      (DFSliceMorphFromCDomObjEq {p} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)}
       mor)
     $ snd $ DFSliceMorphDom {p} {cod=(ctot ** cproj)}
     $ DFSliceMorphFromC {p} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)} mor)
DFSliceMorphFromCDomMorEq {p=(ppos ** pdir)}
  {dtot} {dproj} {ctot} {cproj} (Element0 alpha nteq) =
    nteq

--------------------------------------------------------------------------
--------------------------------------------------------------------------
---- Slice categories of Dirichlet functors (in dependent-type style) ----
--------------------------------------------------------------------------
--------------------------------------------------------------------------

-----------------------------
---- From representables ----
-----------------------------

-- A Dirichlet natural transformation from a representable is a choice
-- of a position of the ("base") functor being sliced over, together with a
-- function from the directions of the representable to the directions
-- of the base at the chosen position.  That is precisely the output of
-- the application of the base functor to the representing object of the
-- slice.  Consequently, a Dirichlet natural transformation from a representable
-- to an arbitrary Dirichlet functor is given precisely by an object of the
-- category of elements of the base functor.
public export
DirichRepSlObj : MLDirichCatObj -> Type
DirichRepSlObj = DirichCatElObj

public export
dirichRepSlObjTotPos : {b : MLDirichCatObj} -> DirichRepSlObj b -> Type
dirichRepSlObjTotPos {b} sl = Unit

public export
dirichRepSlObjTotDir : {b : MLDirichCatObj} -> (sl : DirichRepSlObj b) ->
  SliceObj (dirichRepSlObjTotPos {b} sl)
dirichRepSlObjTotDir {b} sl _ = DirichCatElBaseT b sl

public export
dirichRepSlObjTot : {b : MLDirichCatObj} -> DirichRepSlObj b -> MLDirichCatObj
dirichRepSlObjTot {b} sl =
  (dirichRepSlObjTotPos {b} sl ** dirichRepSlObjTotDir {b} sl)

public export
dirichRepSlObjOnPos : {b : MLDirichCatObj} -> (sl : DirichRepSlObj b) ->
  dirichRepSlObjTotPos {b} sl -> dfPos b
dirichRepSlObjOnPos {b} sl _ = DPair.fst sl

public export
dirichRepSlObjOnDir : {b : MLDirichCatObj} -> (sl : DirichRepSlObj b) ->
  (i : dirichRepSlObjTotPos {b} sl) ->
  dirichRepSlObjTotDir {b} sl i -> dfDir b (dirichRepSlObjOnPos {b} sl i)
dirichRepSlObjOnDir {b} sl _ = DPair.fst

public export
dirichRepSlObjProj : {b : MLDirichCatObj} -> (sl : DirichRepSlObj b) ->
  DirichNatTrans (dirichRepSlObjTot {b} sl) b
dirichRepSlObjProj {b} sl =
  (dirichRepSlObjOnPos {b} sl ** dirichRepSlObjOnDir {b} sl)

public export
dirichRepSlObjToC : {b : MLDirichCatObj} -> DirichRepSlObj b -> CDFSliceObj b
dirichRepSlObjToC {b} sl =
  (dirichRepSlObjTot {b} sl ** dirichRepSlObjProj {b} sl)

-- A Dirichlet functor is a coproduct of representables, so a natural
-- transformation from a Dirichlet functor is a product of natural
-- transformations from representables.  Hence, a slice of a Dirichlet
-- functor is determined by a product (a family) of objects of the
-- category of elements of that base functor.
public export
DirichSlObj : MLDirichCatObj -> Type
DirichSlObj = IntUFamObj . DirichRepSlObj

public export
dirichSlObjTotPos : {b : MLDirichCatObj} -> DirichSlObj b -> Type
dirichSlObjTotPos {b} = DPair.fst

public export
dirichSlObjTotDir : {b : MLDirichCatObj} -> (sl : DirichSlObj b) ->
  SliceObj (dirichSlObjTotPos {b} sl)
dirichSlObjTotDir {b} sl i = dirichRepSlObjTotDir {b} (snd sl i) ()

public export
dirichSlObjTot : {b : MLDirichCatObj} -> DirichSlObj b -> MLDirichCatObj
dirichSlObjTot {b} sl =
  (dirichSlObjTotPos {b} sl ** dirichSlObjTotDir {b} sl)

public export
dirichSlObjOnPos : {b : MLDirichCatObj} -> (sl : DirichSlObj b) ->
  dirichSlObjTotPos {b} sl -> dfPos b
dirichSlObjOnPos {b} sl i = dirichRepSlObjOnPos {b} (snd sl i) ()

public export
dirichSlObjOnDir : {b : MLDirichCatObj} -> (sl : DirichSlObj b) ->
  (i : dirichSlObjTotPos {b} sl) ->
  dirichSlObjTotDir {b} sl i -> dfDir b (dirichSlObjOnPos {b} sl i)
dirichSlObjOnDir {b} sl i = dirichRepSlObjOnDir {b} (snd sl i) ()

public export
dirichSlObjProj : {b : MLDirichCatObj} -> (sl : DirichSlObj b) ->
  DirichNatTrans (dirichSlObjTot {b} sl) b
dirichSlObjProj {b} sl = (dirichSlObjOnPos {b} sl ** dirichSlObjOnDir {b} sl)

public export
dirichSlObjToC : {b : MLDirichCatObj} -> DirichSlObj b -> CDFSliceObj b
dirichSlObjToC {b} sl = (dirichSlObjTot {b} sl ** dirichSlObjProj {b} sl)

public export
dirichSlObjTotPosFromC : {b : MLDirichCatObj} -> CDFSliceObj b -> Type
dirichSlObjTotPosFromC {b} sl = DPair.fst $ DPair.fst sl

public export
dirichSlObjTotDirFromC : {b : MLDirichCatObj} -> (sl : CDFSliceObj b) ->
  SliceObj (dirichSlObjTotPosFromC {b} sl)
dirichSlObjTotDirFromC {b} sl = DPair.snd (DPair.fst sl)

public export
dirichSlObjElFromC : {b : MLDirichCatObj} -> (sl : CDFSliceObj b) ->
  dirichSlObjTotPosFromC {b} sl -> DirichRepSlObj b
dirichSlObjElFromC {b} sl i =
  (fst (snd sl) i **
   WPreImage {a=(dirichSlObjTotDirFromC {b} sl i)} $ snd (snd sl) i)

public export
dirichSlObjFromC : {b : MLDirichCatObj} -> CDFSliceObj b -> DirichSlObj b
dirichSlObjFromC {b} sl =
  (dirichSlObjTotPosFromC {b} sl ** dirichSlObjElFromC {b} sl)

-----------------
---- Objects ----
-----------------

-- The natural transformations of both polynomial and Dirichlet functors have
-- on-positions functions from the domain to the codomain.  Thus, the
-- on-positions function of a natural transformation between either of those
-- types of objects (functors) may be viewed as a fibration of the arena
-- being sliced over.
public export
MlSlArProjOnPos : MLDirichCatObj -> Type
MlSlArProjOnPos = SliceObj . dfPos

-- Thus, the positions of the slice object's domain can be viewed as
-- the sum of all the fibers.
public export
MlSlArTotPos : {ar : MLDirichCatObj} -> MlSlArProjOnPos ar -> Type
MlSlArTotPos {ar} onpos = Sigma {a=(dfPos ar)} onpos

-- Consequently, the directions of the slice object's domain are a slice
-- of the sum of the fibers.
--
-- However, the on-directions part of the projection component of the slice
-- object will, in the case of Dirichlet functors, also go from the domain
-- to the object being sliced over.  Thus that too may be viewed as a fibration,
-- of pairs of the positions of the domain and the directions of the codomain,
-- where those two share the same position of the codomain.
--
-- That view only makes sense in the case of Dirichlet functors, not of
-- polynomials, because the on-directions part of the projection component of
-- an object in a polynomial-functor slice category goes in the opposite
-- direction.
--
-- Thus we can express the directions as follows:
public export
MlDirichSlDir : (ar : MLDirichCatObj) -> MlSlArProjOnPos ar -> Type
MlDirichSlDir ar onpos = (i : dfPos ar) -> onpos i -> dfDir ar i -> Type

public export
record MlDirichSlObj (ar : MLDirichCatObj) where
  constructor MDSobj
  mdsOnPos : MlSlArProjOnPos ar
  mdsDir : MlDirichSlDir ar mdsOnPos

-------------------
---- Morphisms ----
-------------------

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
---- Universal morphisms in the category of Dirichlet functors on `Type` ----
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

-----------------------
---- Representable ----
-----------------------

public export
dfRepObjPos : Type -> Type
dfRepObjPos _ = Unit

public export
dfRepObjDir : (a : Type) -> dfRepObjPos a -> Type
dfRepObjDir a _ = a

public export
dfRepObj : Type -> MLDirichCatObj
dfRepObj a = (dfRepObjPos a ** dfRepObjDir a)

-- The Dirichlet functor represented by `Void` has one position and no
-- directions.  Because it returns the hom-set from its input to `Void`,
-- in `Type` it returns `Unit` for any input type isomorphic to `Void`
-- and `Void` for input type not isomorphic to `Void.`
--
-- The category of elements of this functor is equivalent to the terminal
-- category, because only a choice of the input type `Void` (or something
-- isomorphic to it) produces a non-empty set to choose an element from, and
-- in that case it produces only the isomorphism from the input type into
-- `Void`.
--
-- Because the category of elements of this functor is equivalent to the
-- terminal category, the slice category of Dirichlet functors over it is
-- equivalent to the category of presheaves on the terminal category, which
-- in turn is equivalent to simply `Type` itself.
public export
dfRepVoid : MLDirichCatObj
dfRepVoid = dfRepObj Void

public export
dfRepVoidElToTerminal :
  (ty : Type) -> InterpDirichFunc MLDirichCat.dfRepVoid ty -> Unit
dfRepVoidElToTerminal ty d = ()

public export
dfTerminalToRepVoidEl :
  Unit -> (ty : Type ** InterpDirichFunc MLDirichCat.dfRepVoid ty)
dfTerminalToRepVoidEl u = (Void ** (() ** id))

public export
dfSlRepVoidToType : MlDirichSlObj MLDirichCat.dfRepVoid -> Type
dfSlRepVoidToType sl = mdsOnPos sl ()

public export
dfTypeToSlRepVoid : Type -> MlDirichSlObj MLDirichCat.dfRepVoid
dfTypeToSlRepVoid ty = MDSobj (\_ => ty) (\_, _, v => void v)

-- The Dirichlet functor represented by `Unit` has one position and one
-- direction.  Because it returns the hom-set from its input to `Unit`,
-- it returns `Unit` for any input type.
--
-- The category of elements of this functor is equivalent to `Type` itself,
-- because an object or morphism of it is determined precisely by an object
-- or morphism in `Type`, with the choice of element being uniquely determined
-- (`Unit` and the identity on `Unit`).
--
-- Because the category of elements of this functor is equivalent to
-- `Type` itself, the slice category of Dirichlet functors over it is
-- equivalent to the category of (polynomial) presheaves on `Type`, which in
-- turn is the category of Dirichlet functors on `Type`.
public export
dfRepUnit : MLDirichCatObj
dfRepUnit = dfRepObj Unit

public export
dfRepUnitElToType :
  (ty : Type) -> InterpDirichFunc MLDirichCat.dfRepUnit ty -> Type
dfRepUnitElToType ty d = ty

public export
dfTypeToRepUnitEl :
  Type -> (ty : Type ** InterpDirichFunc MLDirichCat.dfRepUnit ty)
dfTypeToRepUnitEl ty = (ty ** (() ** \_ => ()))

public export
dfSlRepUnitToDirich : MlDirichSlObj MLDirichCat.dfRepUnit -> MLDirichCatObj
dfSlRepUnitToDirich sl =
  (mdsOnPos sl () ** \sli => mdsDir sl () sli ())

public export
dfDirichToSlRepUnit : MLDirichCatObj -> MlDirichSlObj MLDirichCat.dfRepUnit
dfDirichToSlRepUnit ar = MDSobj (\_ => fst ar) (\_, x, _ => snd ar x)

----------------------------
---- (Parallel) product ----
----------------------------

public export
dfParProductPos : MLDirichCatObj -> MLDirichCatObj -> Type
dfParProductPos p q = Pair (dfPos p) (dfPos q)

public export
dfParProductDir : (p, q : MLDirichCatObj) -> dfParProductPos p q -> Type
dfParProductDir p q ipq = Pair (dfDir p $ fst ipq) (dfDir q $ snd ipq)

public export
dfParProductArena : MLDirichCatObj -> MLDirichCatObj -> MLDirichCatObj
dfParProductArena p q = (dfParProductPos p q ** dfParProductDir p q)

public export
dirichParProj1OnPos : (p, q : MLDirichCatObj) ->
  dfPos (dfParProductArena p q) -> dfPos p
dirichParProj1OnPos p q = Builtin.fst

public export
dirichParProj1OnDir : (p, q : MLDirichCatObj) ->
  (i : dfPos (dfParProductArena p q)) ->
  dfDir (dfParProductArena p q) i ->
  dfDir p (dirichParProj1OnPos p q i)
dirichParProj1OnDir p q i = Builtin.fst

public export
dirichParProj1 : (p, q : MLDirichCatObj) ->
  DirichNatTrans (dfParProductArena p q) p
dirichParProj1 p q = (dirichParProj1OnPos p q ** dirichParProj1OnDir p q)

public export
dirichParProj2OnPos : (p, q : MLDirichCatObj) ->
  dfPos (dfParProductArena p q) -> dfPos q
dirichParProj2OnPos p q = Builtin.snd

public export
dirichParProj2OnDir : (p, q : MLDirichCatObj) ->
  (i : dfPos (dfParProductArena p q)) ->
  dfDir (dfParProductArena p q) i ->
  dfDir q (dirichParProj2OnPos p q i)
dirichParProj2OnDir p q i = Builtin.snd

public export
dirichParProj2 : (p, q : MLDirichCatObj) ->
  DirichNatTrans (dfParProductArena p q) q
dirichParProj2 p q = (dirichParProj2OnPos p q ** dirichParProj2OnDir p q)

public export
dirichParPairOnPos : (p, q, r : MLDirichCatObj) ->
  DirichNatTrans p q -> DirichNatTrans p r ->
  dfPos p ->
  dfPos (dfParProductArena q r)
dirichParPairOnPos p q r pq pr pi =
  MkPair (dntOnPos pq pi) (dntOnPos pr pi)

public export
dirichParPairOnDir : (p, q, r : MLDirichCatObj) ->
  (f : DirichNatTrans p q) -> (g : DirichNatTrans p r) ->
  (pi : dfPos p) ->
  dfDir p pi ->
  dfDir (dfParProductArena q r) (dirichParPairOnPos p q r f g pi)
dirichParPairOnDir p q r pq pr pi pd =
  MkPair (dntOnDir pq pi pd) (dntOnDir pr pi pd)

public export
dirichParPair : {p, q, r : MLDirichCatObj} ->
  DirichNatTrans p q -> DirichNatTrans p r ->
  DirichNatTrans p (dfParProductArena q r)
dirichParPair {p} {q} {r} f g =
  (dirichParPairOnPos p q r f g ** dirichParPairOnDir p q r f g)

-------------------------------
---- Set-indexed coproduct ----
-------------------------------

public export
dfSetCoproductPos : {a : Type} -> (a -> MLDirichCatObj) -> Type
dfSetCoproductPos {a} ps = DPair a (fst . ps)

public export
dfSetCoproductDir : {a : Type} ->
  (ps : a -> MLDirichCatObj) -> dfSetCoproductPos ps -> Type
dfSetCoproductDir ps (x ** xpos) = snd (ps x) xpos

public export
dfSetCoproductArena : {a : Type} -> (a -> MLDirichCatObj) -> MLDirichCatObj
dfSetCoproductArena ps = (dfSetCoproductPos ps ** dfSetCoproductDir ps)

--------------------------------------
---- Set-indexed parallel product ----
--------------------------------------

public export
dfSetParProductPos : {a : Type} -> (a -> MLDirichCatObj) -> Type
dfSetParProductPos {a} ps = (x : a) -> fst $ ps x

public export
dfSetParProductDir : {a : Type} ->
  (ps : a -> MLDirichCatObj) -> dfSetParProductPos ps -> Type
dfSetParProductDir {a} ps fpos = ((x : a) -> snd (ps x) $ fpos x)

public export
dfSetParProductArena : {a : Type} -> (a -> MLDirichCatObj) -> MLDirichCatObj
dfSetParProductArena {a} ps = (dfSetParProductPos ps ** dfSetParProductDir ps)

-------------------
---- Equalizer ----
-------------------

public export
dfEqualizerPos : {p, q : MLDirichCatObj} ->
  DirichNatTrans p q -> DirichNatTrans p q -> Type
dfEqualizerPos {p} {q} alpha beta = Equalizer (dntOnPos alpha) (dntOnPos beta)

public export
0 dfEqualizerDir : {p, q : MLDirichCatObj} ->
  (alpha, beta : DirichNatTrans p q) ->
  dfEqualizerPos {p} {q} alpha beta -> Type
dfEqualizerDir {p} {q} alpha beta el =
  Equalizer {a=(dfDir p $ fst0 el)} {b=(dfDir q $ dntOnPos alpha $ fst0 el)}
    (dntOnDir alpha $ fst0 el)
    (replace
      {p=(\i' : dfPos q => dfDir p (fst0 el) -> dfDir q i')}
      (sym $ snd0 el)
      (dntOnDir beta $ fst0 el))

public export
0 dfEqualizer : {p, q : MLDirichCatObj} ->
  (alpha, beta : DirichNatTrans p q) -> MLDirichCatObj
dfEqualizer {p} {q} alpha beta =
  (dfEqualizerPos {p} {q} alpha beta ** dfEqualizerDir {p} {q} alpha beta)

---------------------
---- Hom-objects ----
---------------------

-- We begin with the hom-object from a representable Dirichlet functor to a
-- general Dirichlet functor.

public export
dfRepHomObjPos : Type -> MLDirichCatObj -> Type
dfRepHomObjPos a p = dfPos p

public export
dfRepHomObjDir : (a : Type) -> (p : MLDirichCatObj) ->
  dfRepHomObjPos a p -> Type
dfRepHomObjDir a p i = a -> dfDir p i

public export
dfRepHomObj : Type -> MLDirichCatObj -> MLDirichCatObj
dfRepHomObj a p = (dfRepHomObjPos a p ** dfRepHomObjDir a p)

public export
dfRepEvalPos : (a : Type) -> (p : MLDirichCatObj) ->
  dfPos (dfParProductArena (dfRepHomObj a p) (dfRepObj a)) ->
  dfPos p
dfRepEvalPos a p = Builtin.fst

public export
dfRepEvalDir : (a : Type) -> (p : MLDirichCatObj) ->
  (i : dfPos (dfParProductArena (dfRepHomObj a p) (dfRepObj a))) ->
  dfDir (dfParProductArena (dfRepHomObj a p) (dfRepObj a)) i ->
  dfDir p (dfRepEvalPos a p i)
dfRepEvalDir a p i f = fst f $ snd f

public export
dfRepEval : (a : Type) -> (p : MLDirichCatObj) ->
  DirichNatTrans (dfParProductArena (dfRepHomObj a p) (dfRepObj a)) p
dfRepEval a p = (dfRepEvalPos a p ** dfRepEvalDir a p)

public export
dfRepCurryPos : {a : Type} -> {p, r : MLDirichCatObj} ->
  DirichNatTrans (dfParProductArena p (dfRepObj a)) r ->
  dfPos p -> dfPos (dfRepHomObj a r)
dfRepCurryPos {a} {p} {r} alpha i = fst alpha (i, ())

public export
dfRepCurryDir : {a : Type} -> {p, r : MLDirichCatObj} ->
  (alpha : DirichNatTrans (dfParProductArena p (dfRepObj a)) r) ->
  (i : dfPos p) ->
  dfDir p i -> dfDir (dfRepHomObj a r) (dfRepCurryPos {a} {p} {r} alpha i)
dfRepCurryDir {a} {p} {r} alpha i d ea = snd alpha (i, ()) (d, ea)

public export
dfRepCurry : {a : Type} -> {p, r : MLDirichCatObj} ->
  DirichNatTrans (dfParProductArena p (dfRepObj a)) r ->
  DirichNatTrans p (dfRepHomObj a r)
dfRepCurry {a} {p} {r} alpha =
  (dfRepCurryPos {a} {p} {r} alpha ** dfRepCurryDir {a} {p} {r} alpha)

-- Now we use the hom-objects from representable Dirichlet functors to
-- compute the hom-objects between general Dirichlet functors by reasoning
-- that a natural transformation out of a Dirichlet functor, which is a
-- coproduct of representables, must be a product of natural transformations
-- out of representables.

public export
dfHomObj : MLDirichCatObj -> MLDirichCatObj -> MLDirichCatObj
dfHomObj p q =
  dfSetParProductArena {a=(dfPos p)} $ \i => dfRepHomObj (dfDir p i) q

public export
dfHomObjPos : MLDirichCatObj -> MLDirichCatObj -> Type
dfHomObjPos p q = dfPos (dfHomObj p q)

public export
dfHomObjPosIsHom : (p, q : MLDirichCatObj) ->
  dfHomObjPos p q = (dfPos p -> dfPos q)
dfHomObjPosIsHom p q = Refl

public export
dfHomObjDir : (p, q : MLDirichCatObj) -> dfHomObjPos p q -> Type
dfHomObjDir p q = dfDir (dfHomObj p q)

public export
dfHomObjDirIsHom : (p, q : MLDirichCatObj) -> (i : dfHomObjPos p q) ->
  dfHomObjDir p q i = SliceMorphism {a=(dfPos p)} (dfDir p) (dfDir q . i)
dfHomObjDirIsHom p q i = Refl

public export
dfEvalPos : (p, q : MLDirichCatObj) ->
  dfPos (dfParProductArena (dfHomObj p q) p) ->
  dfPos q
dfEvalPos p q i = fst i $ snd i

public export
dfEvalDir : (p, q : MLDirichCatObj) ->
  (i : dfPos (dfParProductArena (dfHomObj p q) p)) ->
  dfDir (dfParProductArena (dfHomObj p q) p) i ->
  dfDir q (dfEvalPos p q i)
dfEvalDir a p i f = fst f (snd i) $ snd f

public export
dfEval : (p, q : MLDirichCatObj) ->
  DirichNatTrans (dfParProductArena (dfHomObj p q) p) q
dfEval p q = (dfEvalPos p q ** dfEvalDir p q)

public export
dfCurryPos : {p, q, r : MLDirichCatObj} ->
  DirichNatTrans (dfParProductArena p q) r ->
  dfPos p -> dfPos (dfHomObj q r)
dfCurryPos {p} {q} {r} alpha pi qi = fst alpha (pi, qi)

public export
dfCurryDir : {p, q, r : MLDirichCatObj} ->
  (alpha : DirichNatTrans (dfParProductArena p q) r) ->
  (i : dfPos p) ->
  dfDir p i -> dfDir (dfHomObj q r) (dfCurryPos {p} {q} {r} alpha i)
dfCurryDir {p} {q} {r} alpha pi pd qi qd = snd alpha (pi, qi) (pd, qd)

public export
dfCurry : {p, q, r : MLDirichCatObj} ->
  DirichNatTrans (dfParProductArena p q) r ->
  DirichNatTrans p (dfHomObj q r)
dfCurry {p} {q} {r} alpha =
  (dfCurryPos {p} {q} {r} alpha ** dfCurryDir {p} {q} {r} alpha)

-----------------------------------------------------------------------
-----------------------------------------------------------------------
---- Universal morphisms in slice categories of Dirichlet functors ----
-----------------------------------------------------------------------
-----------------------------------------------------------------------

-------------------
---- Coproduct ----
-------------------

public export
dfSlCoproductPos : {b : MLDirichCatObj} ->
  MlDirichSlObj b -> MlDirichSlObj b -> MlSlArProjOnPos b
dfSlCoproductPos {b} p q bi =
  Either (mdsOnPos p bi) (mdsOnPos q bi)

public export
dfSlCoproductDir : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) ->
  MlDirichSlDir b (dfSlCoproductPos {b} p q)
dfSlCoproductDir {b} p q bi pqi bd =
  case pqi of
    Left pi => mdsDir p bi pi bd
    Right qi => mdsDir q bi qi bd

public export
dfSlCoproductArena : {b : MLDirichCatObj} ->
  MlDirichSlObj b -> MlDirichSlObj b -> MlDirichSlObj b
dfSlCoproductArena {b} p q =
  MDSobj (dfSlCoproductPos {b} p q) (dfSlCoproductDir {b} p q)

--------------------------
---- Parallel product ----
--------------------------

public export
dfSlParProductPos : {b : MLDirichCatObj} ->
  MlDirichSlObj b -> MlDirichSlObj b -> MlSlArProjOnPos b
dfSlParProductPos {b} p q bi =
  Pair (mdsOnPos p bi) (mdsOnPos q bi)

public export
dfSlParProductDir : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) ->
  MlDirichSlDir b (dfSlParProductPos {b} p q)
dfSlParProductDir {b} p q bi pqi bd =
  Pair (mdsDir p bi (fst pqi) bd) (mdsDir q bi (snd pqi) bd)

public export
dfSlParProductArena : {b : MLDirichCatObj} ->
  MlDirichSlObj b -> MlDirichSlObj b -> MlDirichSlObj b
dfSlParProductArena {b} p q =
  MDSobj (dfSlParProductPos {b} p q) (dfSlParProductDir {b} p q)

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

-- The projection of a Dirichlet functor on the category of elements at a
-- particular position is a Dirichlet functor on a slice object, which is
-- the category of elements of a _representable_ Dirichlet functor, so it
-- is a slice of a Dirichlet functor over a representable.  That consists
-- of a type of positions together with, for each position, a slice of
-- the base object of the representable.
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
--
-- Another way of seeing this is that a slice object in the category of
-- Dirichlet functors is a presheaf (specifically, a Dirichlet presheaf, i.e.
-- a sum of contravariant representables) over the category of elements of
-- the Dirichlet functor being sliced over, and a representable presheaf on a
-- category is determined by one object of that category.
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

public export
DirichFamCatObj : Type -> Type
DirichFamCatObj x = x -> MLDirichCatObj

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

public export
MlDirichSlPosDirSlP : (x : Type) -> (sl, sl' : SliceObj x) -> SliceObj x
MlDirichSlPosDirSlP x sl sl' = SliceObj . SliceProduct {a=x} sl sl'

-- Equivalent to `MlDirichSlPosDirSlP`.
public export
MlDirichSlPosDirSl : (x : Type) -> (sl, sl' : SliceObj x) -> SliceObj x
MlDirichSlPosDirSl x sl sl' i = sl i -> sl' i -> Type

public export
MlDirichSlPosDirSlToP : (x : Type) -> (sl, sl' : SliceObj x) ->
  SliceMorphism {a=x}
    (MlDirichSlPosDirSl x sl sl')
    (MlDirichSlPosDirSlP x sl sl')
MlDirichSlPosDirSlToP x sl sl' i = uncurry

public export
MlDirichSlPosDirSlFromP : (x : Type) -> (sl, sl' : SliceObj x) ->
  SliceMorphism {a=x}
    (MlDirichSlPosDirSlP x sl sl')
    (MlDirichSlPosDirSl x sl sl')
MlDirichSlPosDirSlFromP x sl sl' i = curry

public export
MlDirichSlPosDirM : (x : Type) -> (sl, sl' : SliceObj x) -> Type
MlDirichSlPosDirM x sl sl' =
  SliceMorphism {a=x} (SliceObjTerminal x) (MlDirichSlPosDirSl x sl sl')

-- Equivalent to `MlDirichSlPosDirM`.
public export
MlDirichSlPosDir : (x : Type) -> (sl, sl' : SliceObj x) -> Type
MlDirichSlPosDir x sl sl' = Pi {a=x} $ MlDirichSlPosDirSl x sl sl'

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
MlDirichSlDir ar onpos = MlDirichSlPosDir (dfPos ar) onpos (dfDir ar)

public export
record MlDirichSlObj (ar : MLDirichCatObj) where
  constructor MDSobj
  mdsOnPos : MlSlArProjOnPos ar
  mdsDir : MlDirichSlDir ar mdsOnPos

public export
MlDirichRepSlObj : {ar : MLDirichCatObj} ->
  DirichRepSlObj ar -> MlDirichSlObj ar
MlDirichRepSlObj {ar} el = MDSobj (\_ => snd ar $ fst el) (\i, d, _ => snd el d)

--------------------------------------------------------------------
---- Equivalence of dependent-type and categorial-style objects ----
--------------------------------------------------------------------

public export
mlDirichSlObjTotPos : {ar : MLArena} -> MlDirichSlObj ar -> Type
mlDirichSlObjTotPos {ar} sl = MlSlArTotPos {ar} $ mdsOnPos sl

public export
mlDirichSlObjTotDir : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  mlDirichSlObjTotPos {ar} sl -> Type
mlDirichSlObjTotDir {ar} sl ij =
  Sigma {a=(dfDir ar $ fst ij)} $ mdsDir sl (fst ij) (snd ij)

public export
mlDirichSlObjTot : {ar : MLArena} -> MlDirichSlObj ar -> MLArena
mlDirichSlObjTot {ar} sl =
  (mlDirichSlObjTotPos {ar} sl ** mlDirichSlObjTotDir {ar} sl)

public export
mlDirichSlObjTotTot : {ar : MLArena} -> MlDirichSlObj ar -> Type
mlDirichSlObjTotTot {ar} sl = dfTot (mlDirichSlObjTot {ar} sl)

public export
mlDirichSlObjProjOnPos : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  mlDirichSlObjTotPos sl -> dfPos ar
mlDirichSlObjProjOnPos {ar} sl = DPair.fst

public export
mlDirichSlObjProjOnDir : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  (i : mlDirichSlObjTotPos sl) ->
  mlDirichSlObjTotDir {ar} sl i -> dfDir ar (mlDirichSlObjProjOnPos sl i)
mlDirichSlObjProjOnDir {ar} sl _ = DPair.fst

public export
mlDirichSlObjProj : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  MLDirichCatMor (mlDirichSlObjTot {ar} sl) ar
mlDirichSlObjProj {ar} sl =
  (mlDirichSlObjProjOnPos {ar} sl ** mlDirichSlObjProjOnDir {ar} sl)

public export
mlDirichSlObjToC : {ar : MLArena} -> MlDirichSlObj ar -> CDFSliceObj ar
mlDirichSlObjToC {ar} sl =
  (mlDirichSlObjTot {ar} sl ** mlDirichSlObjProj {ar} sl)

public export
mlDirichSlOnPosFromC : {ar : MLArena} -> CDFSliceObj ar -> MlSlArProjOnPos ar
mlDirichSlOnPosFromC {ar} sl i = PreImage (fst $ snd sl) i

public export
mlDirichSlDirFromCBase : {ar : MLArena} -> (sl : CDFSliceObj ar) ->
  MlDirichSlDir ar (mlDirichSlOnPosFromC {ar} sl)
mlDirichSlDirFromCBase {ar} sl i j bd = snd (fst sl) (fst0 j)

public export
mlDirichSlDirFromCProp : {ar : MLArena} -> (sl : CDFSliceObj ar) ->
  (i : dfPos ar) -> (j : mlDirichSlOnPosFromC {ar} sl i) ->
  (bd : dfDir ar i) -> SliceObj (mlDirichSlDirFromCBase {ar} sl i j bd)
mlDirichSlDirFromCProp {ar} sl i j bd sld =
  snd (snd sl) (fst0 j) sld = replace {p=(dfDir {p=ar})} (sym $ snd0 j) bd

public export
mlDirichSlDirFromC : {ar : MLArena} -> (sl : CDFSliceObj ar) ->
  MlDirichSlDir ar (mlDirichSlOnPosFromC {ar} sl)
mlDirichSlDirFromC {ar} sl i j bd =
  Subset0
    (mlDirichSlDirFromCBase {ar} sl i j bd)
    (mlDirichSlDirFromCProp {ar} sl i j bd)

public export
mlDirichSlObjFromC : {ar : MLArena} -> CDFSliceObj ar -> MlDirichSlObj ar
mlDirichSlObjFromC {ar} sl =
  MDSobj (mlDirichSlOnPosFromC {ar} sl) (mlDirichSlDirFromC {ar} sl)

-------------------
---- Morphisms ----
-------------------

-- The morphisms of slice categories correspond to morphisms of the
-- base category which commute with the projections.

-- When we take the dependent-type view in the Dirichlet-functor category, the
-- commutativity conditions are hidden in the type-checking of dependent
-- functions.

public export
MlDirichSlMorOnPos : {ar : MLArena} ->
  MlDirichSlObj ar -> MlDirichSlObj ar -> Type
MlDirichSlMorOnPos {ar} dom cod =
  SliceMorphism {a=(dfPos ar)} (mdsOnPos dom) (mdsOnPos cod)

public export
MlDirichSlMorOnDir : {ar : MLArena} -> (dom, cod : MlDirichSlObj ar) ->
  MlDirichSlMorOnPos {ar} dom cod -> Type
MlDirichSlMorOnDir {ar} dom cod onpos =
  (i : dfPos ar) -> (j : mdsOnPos dom i) ->
    SliceMorphism {a=(dfDir ar i)}
      (mdsDir dom i j)
      (mdsDir cod i $ onpos i j)

public export
record MlDirichSlMor {ar : MLArena} (dom, cod : MlDirichSlObj ar) where
  constructor MDSM
  mdsmOnPos : MlDirichSlMorOnPos {ar} dom cod
  mdsmOnDir : MlDirichSlMorOnDir {ar} dom cod mdsmOnPos

public export
MlDirichSlObjToDirichCatElAr : {ar : MLArena} ->
  MlDirichSlObj ar -> DirichDirichCatElAr ar
MlDirichSlObjToDirichCatElAr {ar} sl bi = (mdsOnPos sl bi ** mdsDir sl bi)

public export
MlDirichCatElArToSlObj : {ar : MLArena} ->
  DirichDirichCatElAr ar -> MlDirichSlObj ar
MlDirichCatElArToSlObj {ar} sl =
  MDSobj (\bi => fst $ sl bi) (\bi => snd $ sl bi)

-------------------------------------------------------------
---- Categorial operations in Dirichlet slice categories ----
-------------------------------------------------------------

public export
mlDirichSlMorId : {ar : MLArena} -> (p : MlDirichSlObj ar) ->
  MlDirichSlMor {ar} p p
mlDirichSlMorId {ar} p =
  MDSM
    (sliceId $ mdsOnPos p)
    (\i, j => sliceId $ mdsDir p i j)

public export
mlDirichSlMorComp : {ar : MLArena} -> {p, q, r : MlDirichSlObj ar} ->
  MlDirichSlMor {ar} q r -> MlDirichSlMor {ar} p q -> MlDirichSlMor {ar} p r
mlDirichSlMorComp {ar} {p} {q} {r} m' m =
  MDSM
    (sliceComp (mdsmOnPos m') (mdsmOnPos m))
    (\i, j, bd, md =>
      mdsmOnDir m' i (mdsmOnPos m i j) bd $ mdsmOnDir m i j bd md)

----------------------------------------------------------------------
---- Equivalence of dependent-type and categorial-style morphisms ----
----------------------------------------------------------------------

public export
mlDirichSlMorToCBase : {ar : MLArena} -> {dom, cod : MlDirichSlObj ar} ->
  MlDirichSlMor dom cod ->
  MLDirichCatMor (fst (mlDirichSlObjToC dom)) (fst (mlDirichSlObjToC cod))
mlDirichSlMorToCBase {ar=(bpos ** bdir)}
  {dom=(MDSobj donpos ddir)} {cod=(MDSobj conpos cdir)} (MDSM onpos ondir) =
    (\ij => (fst ij ** onpos (fst ij) (snd ij)) **
     \(i ** j), (d ** dd) => (d ** ondir i j d dd))

public export
mlDirichSlMorToD : {ar : MLArena} -> {dom, cod : MlDirichSlObj ar} ->
  MlDirichSlMor dom cod -> DFSliceMorph {p=ar} (mlDirichSlObjToC cod)
mlDirichSlMorToD {ar=ar@(bpos ** bdir)}
  {dom=dom@(MDSobj donpos ddir)} {cod=cod@(MDSobj conpos cdir)}
  mor@(MDSM onpos ondir) =
    (fst (mlDirichSlObjToC dom) ** mlDirichSlMorToCBase {ar} {dom} {cod} mor)

public export
0 mlDirichSlMorToCD : {ar : MLArena} -> {dom, cod : MlDirichSlObj ar} ->
  MlDirichSlMor dom cod ->
  CDFSliceMorph ar (mlDirichSlObjToC dom) (mlDirichSlObjToC cod)
mlDirichSlMorToCD {ar=(ppos ** pdir)}
  {dom=dom@(MDSobj donpos ddir)} {cod=cod@(MDSobj conpos cdir)}
  mor@(MDSM monpos mondir)
      with
        (DFSliceMorphToC {p=(ppos ** pdir)} {cod=(mlDirichSlObjToC cod)}
          (mlDirichSlMorToD {dom} {cod} mor))
  mlDirichSlMorToCD {ar=(ppos ** pdir)}
    {dom=dom@(MDSobj donpos ddir)} {cod=cod@(MDSobj conpos cdir)}
    mor@(MDSM monpos mondir)
      | Element0 dmnt@(dmonpos ** dmondir) (Evidence0 opeq odeq) =
        Element0
         dmnt
         (Evidence0
            opeq
            $ \i : (DPair ppos donpos),
               d : (DPair (pdir (fst i)) (ddir (fst i) (snd i))) =>
                trans (odeq i d)
                $ case i of (i' ** j') => case d of (d' ** dd') => Refl)

public export
mlDirichSlMorFromD : {ar : MLArena} -> {cod : CDFSliceObj ar} ->
  (mor : DFSliceMorph {p=ar} cod) ->
  MlDirichSlMor
    (mlDirichSlObjFromC {ar} $ DFSliceMorphDom {p=ar} {cod} mor)
    (mlDirichSlObjFromC cod)
mlDirichSlMorFromD {ar=(ppos ** pdir)}
  {cod=((ctot ** cproj) ** (conpos ** condir))}
  ((mpos ** mdir) ** (monpos ** mondir)) =
    MDSM
      (\i, (Element0 j peq) => Element0 (monpos j) peq)
      (\i, (Element0 j peq), pd, (Element0 md deq) =>
        Element0 (mondir j md) deq)

public export
0 mlDirichSlMorFromCD : {ar : MLArena} -> {dom, cod : CDFSliceObj ar} ->
  (mor : CDFSliceMorph ar dom cod) ->
  MlDirichSlMor (mlDirichSlObjFromC {ar} dom) (mlDirichSlObjFromC {ar} cod)
mlDirichSlMorFromCD {ar=(ppos ** pdir)}
  {dom=((dtot ** dproj) ** (donpos ** dondir))}
  {cod=((ctot ** cproj) ** (conpos ** condir))}
  (Element0 (monpos ** mondir) (Evidence0 opeq odeq)) =
    MDSM
      (\i, (Element0 j peq) => Element0 (monpos j) $ trans (sym $ opeq j) peq)
      (\i, (Element0 j peq), pd, (Element0 md deq) =>
        Element0 (mondir j md) $
          trans (odeq j md) $ rewrite sym (opeq j) in deq)

-----------------------------------------------
---- Dirichlet slice objects as presheaves ----
-----------------------------------------------

-- A Dirichlet slice object is equivalent to a Dirichlet functor over
-- the base object's category of elements, so we can apply it to an
-- object or a morphism of that category of elements.

public export
DirichSlObjOmapPos : {ar : MLDirichCatObj} ->
  MlDirichSlObj ar -> DirichCatElObj ar -> Type
DirichSlObjOmapPos {ar} sl el = mdsOnPos sl (fst el)

public export
DirichSlObjOmapDir : {ar : MLDirichCatObj} ->
  (sl : MlDirichSlObj ar) -> (el : DirichCatElObj ar) ->
  DirichSlObjOmapPos {ar} sl el -> Type
DirichSlObjOmapDir {ar} sl el i =
  SliceMorphism {a=(snd ar $ fst el)} (snd el) (mdsDir sl (fst el) i)

public export
DirichSlObjOmap : {ar : MLDirichCatObj} ->
  MlDirichSlObj ar -> DirichCatElObj ar -> Type
DirichSlObjOmap {ar} sl el =
  Sigma {a=(DirichSlObjOmapPos {ar} sl el)} (DirichSlObjOmapDir {ar} sl el)

------------------------------------------------
------------------------------------------------
---- Slices of slices of Dirichlet functors ----
------------------------------------------------
------------------------------------------------

public export
MlDirichSlOfSl : {ar : MLArena} -> MlDirichSlObj ar -> Type
MlDirichSlOfSl {ar} sl = MlDirichSlObj $ mlDirichSlObjTot {ar} sl

public export
MlDirichBaseSlPosFromSlOfSl : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  MlDirichSlOfSl {ar} sl -> MlSlArProjOnPos ar
MlDirichBaseSlPosFromSlOfSl {ar} sl slsl i =
  DPair (mdsOnPos sl i) $ DPair.curry (mdsOnPos slsl) i

public export
MlDirichBaseSlDirFromSlOfSl : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  (slsl : MlDirichSlOfSl {ar} sl) ->
  MlDirichSlDir ar (MlDirichBaseSlPosFromSlOfSl {ar} sl slsl)
MlDirichBaseSlDirFromSlOfSl {ar} sl slsl i jk d =
  (sld : mdsDir sl i (fst jk) d **
   mdsDir slsl (i ** fst jk) (snd jk) (d ** sld))

public export
MlDirichBaseSlFromSlOfSl : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  MlDirichSlOfSl {ar} sl -> MlDirichSlObj ar
MlDirichBaseSlFromSlOfSl {ar} sl slsl =
  MDSobj
    (MlDirichBaseSlPosFromSlOfSl {ar} sl slsl)
    (MlDirichBaseSlDirFromSlOfSl {ar} sl slsl)

public export
mlDirichSlOfSlFromP : {ar : MLArena} -> {cod : MlDirichSlObj ar} ->
  DFSliceMorph {p=ar} (mlDirichSlObjToC {ar} cod) -> MlDirichSlOfSl {ar} cod
mlDirichSlOfSlFromP {ar} {cod=cod@(MDSobj _ _)} =
  mlDirichSlObjFromC {ar=(mlDirichSlObjTot {ar} cod)}

-----------------------------------------------
-----------------------------------------------
---- Factored slices of Dirichlet functors ----
-----------------------------------------------
-----------------------------------------------

-- The terminal object of the base category of Dirichlet functors.
public export
MLDirichCatObjTerminal : MLDirichCatObj
MLDirichCatObjTerminal = (Unit ** \_ => Unit)

---------------------------------
---- Cartesian-slice objects ----
---------------------------------

public export
DirichCartSlObj : MLDirichCatObj -> Type
DirichCartSlObj = SliceObj . dfPos

public export
DirichCartSlTotPos : {b : MLDirichCatObj} -> DirichCartSlObj b -> Type
DirichCartSlTotPos {b} = Sigma {a=(dfPos b)}

public export
DirichCartSlOnPos : {b : MLDirichCatObj} -> (p : DirichCartSlObj b) ->
  DirichCartSlTotPos {b} p -> dfPos b
DirichCartSlOnPos {b} p = DPair.fst

public export
DirichCartSlDir : {b : MLDirichCatObj} ->
  (p : DirichCartSlObj b) -> DirichCartSlTotPos {b} p -> Type
DirichCartSlDir {b} p = dfDir b . DirichCartSlOnPos {b} p

public export
DirichCartSlOnDir : {b : MLDirichCatObj} ->
  (p : DirichCartSlObj b) ->
  SliceMorphism {a=(DirichCartSlTotPos {b} p)}
    (DirichCartSlDir {b} p)
    (dfDir b . DirichCartSlOnPos {b} p)
DirichCartSlOnDir {b} p i = id {a=(DirichCartSlDir {b} p i)}

-- We can embed a Cartesian-slice Dirichlet functor into the base
-- category of Dirichlet functors on `Type`.
public export
DirichCartSlEmbed : {b : MLDirichCatObj} -> DirichCartSlObj b -> MLDirichCatObj
DirichCartSlEmbed {b} p = (DirichCartSlTotPos {b} p ** DirichCartSlDir {b} p)

public export
DirichCartSlTot : {b : MLDirichCatObj} -> DirichCartSlObj b -> Type
DirichCartSlTot {b} p = dfTot (DirichCartSlEmbed {b} p)

public export
DirichCartSlProj : {b : MLDirichCatObj} -> (p : DirichCartSlObj b) ->
  DirichNatTrans (DirichCartSlEmbed {b} p) b
DirichCartSlProj {b} p = (DirichCartSlOnPos {b} p ** DirichCartSlOnDir {b} p)

-- We can promote a Dirichlet functor in the base category of Dirichlet
-- functors on `Type` into any Cartesian-slice Dirichlet-functor category.
-- This is the logical functor called "pullback" and denoted `U*` at
-- https://ncatlab.org/nlab/show/generalized+element#in_toposes .
public export
DirichCartSlPullback : {b : MLDirichCatObj} ->
  MLDirichCatObj -> DirichCartSlObj b
DirichCartSlPullback {b} p bi =
  (pi : DPair.fst p ** DPair.snd b bi -> DPair.snd p pi)

-----------------------------------
---- Cartesian-slice morphisms ----
-----------------------------------

public export
DirichCartSlMor : {b : MLDirichCatObj} ->
  DirichCartSlObj b -> DirichCartSlObj b -> Type
DirichCartSlMor {b} = SliceMorphism {a=(dfPos b)}

public export
DirichCartSlId : {b : MLDirichCatObj} ->
  (p : DirichCartSlObj b) -> DirichCartSlMor {b} p p
DirichCartSlId = sliceId

public export
DirichCartSlComp : {b : MLDirichCatObj} ->
  {p, q, r : DirichCartSlObj b} ->
  DirichCartSlMor {b} q r -> DirichCartSlMor {b} p q -> DirichCartSlMor {b} p r
DirichCartSlComp = sliceComp

-- Now we show that the "embed" and "pullback" functors are adjoint --
-- in fact, they are special cases of `sigma` and `base-change`, between
-- `MLDirichCatObj` and `DirichCartSlObj b` for any `b`.  (The more general
-- cases are between `DirichCartSlObj b` and `DirichCartSlObj b'` for
-- any `b` and `b'`).
public export
DirichCartSlEmbedPullbackLeftAdjoint : {b : MLDirichCatObj} ->
  DirichCartSlObj b -> MLDirichCatObj
DirichCartSlEmbedPullbackLeftAdjoint = DirichCartSlEmbed

public export
DirichCartSlEmbedPullbackRightAdjoint : {b : MLDirichCatObj} ->
  MLDirichCatObj -> DirichCartSlObj b
DirichCartSlEmbedPullbackRightAdjoint = DirichCartSlPullback

public export
DirichCartSlEmbedPullbackLeftAdjunct : {b : MLDirichCatObj} ->
  (p : DirichCartSlObj b) -> (q : MLDirichCatObj) ->
  DirichNatTrans (DirichCartSlEmbedPullbackLeftAdjoint {b} p) q ->
  DirichCartSlMor {b} p (DirichCartSlEmbedPullbackRightAdjoint {b} q)
DirichCartSlEmbedPullbackLeftAdjunct p q alpha bi pi =
  (fst alpha (bi ** pi) ** snd alpha (bi ** pi))

public export
DirichCartSlEmbedPullbackRightAdjunct : {b : MLDirichCatObj} ->
  (p : DirichCartSlObj b) -> (q : MLDirichCatObj) ->
  DirichCartSlMor {b} p (DirichCartSlEmbedPullbackRightAdjoint {b} q) ->
  DirichNatTrans (DirichCartSlEmbedPullbackLeftAdjoint {b} p) q
DirichCartSlEmbedPullbackRightAdjunct p q m =
  (\pi => fst (m (fst pi) (snd pi)) ** \pi => snd (m (fst pi) (snd pi)))

-- We now show the correspondence between global elements (sections) in
-- Dirichlet-Cartesian slice categories and Cartesian morphisms (generalized
-- elements) in the base category, as described at
-- https://ncatlab.org/nlab/show/generalized+element#in_toposes .
public export
DirichCartSlTerminal : (b : MLDirichCatObj) -> DirichCartSlObj b
DirichCartSlTerminal b = DirichCartSlPullback {b} $ MLDirichCatObjTerminal

public export
DirichCartSlSection : (b, p : MLDirichCatObj) -> Type
DirichCartSlSection b p =
  DirichCartSlMor {b} (DirichCartSlTerminal b) (DirichCartSlPullback {b} p)

public export
DirichCartSlSectionToGenEl : {b, p : MLDirichCatObj} ->
  DirichCartSlSection b p -> MLDirichCatMor b p
DirichCartSlSectionToGenEl {b} {p} m =
  (\bi => fst (m bi (() ** \_ => ())) ** \bi => snd (m bi (() ** \_ => ())))

public export
DirichCartGenElToSlSection : {b, p : MLDirichCatObj} ->
  MLDirichCatMor b p -> DirichCartSlSection b p
DirichCartGenElToSlSection {b} {p} alpha bi termobj =
  (fst alpha bi ** snd alpha bi)

------------------------------------------
---- Dirichlet vertical-slice objects ----
------------------------------------------

public export
DirichBaseEmbed : MLDirichCatObj -> MLDirichCatObj
DirichBaseEmbed b = (dfTot b ** SliceObjTerminal $ dfTot b)

public export
DirichVertSlObj : MLDirichCatObj -> Type
DirichVertSlObj = DirichCartSlObj . DirichBaseEmbed

public export
DirichVertSlTotPos : {b : MLDirichCatObj} -> DirichVertSlObj b -> Type
DirichVertSlTotPos {b} p = dfPos b

public export
DirichVertSlOnPos : {b : MLDirichCatObj} -> (p : DirichVertSlObj b) ->
  DirichVertSlTotPos {b} p -> dfPos b
DirichVertSlOnPos {b} p = id

public export
DirichVertSlDir : {b : MLDirichCatObj} ->
  (p : DirichVertSlObj b) -> DirichVertSlTotPos {b} p -> Type
DirichVertSlDir {b} p i = Sigma {a=(dfDir b i)} $ DPair.curry p i

public export
DirichVertSlOnDir : {b : MLDirichCatObj} ->
  (p : DirichVertSlObj b) ->
  SliceMorphism {a=(DirichVertSlTotPos {b} p)}
    (DirichVertSlDir {b} p)
    (dfDir b . DirichVertSlOnPos {b} p)
DirichVertSlOnDir {b} p i = DPair.fst

public export
DirichVertSlEmbed : {b : MLDirichCatObj} -> DirichVertSlObj b -> MLDirichCatObj
DirichVertSlEmbed {b} p = (DirichVertSlTotPos {b} p ** DirichVertSlDir {b} p)

public export
DirichVertSlTot : {b : MLDirichCatObj} -> DirichVertSlObj b -> Type
DirichVertSlTot {b} p = dfTot (DirichVertSlEmbed {b} p)

public export
DirichVertSlProj : {b : MLDirichCatObj} -> (p : DirichVertSlObj b) ->
  DirichNatTrans (DirichVertSlEmbed {b} p) b
DirichVertSlProj {b} p = (DirichVertSlOnPos {b} p ** DirichVertSlOnDir {b} p)

--------------------------------------------
---- Dirichlet vertical-slice morphisms ----
--------------------------------------------

public export
DirichVertSlMor : {b : MLDirichCatObj} ->
  DirichVertSlObj b -> DirichVertSlObj b -> Type
DirichVertSlMor {b} = DirichCartSlMor {b=(DirichBaseEmbed b)}

public export
DirichVertSlId : {b : MLDirichCatObj} ->
  (p : DirichVertSlObj b) -> DirichVertSlMor {b} p p
DirichVertSlId = sliceId

public export
DirichVertSlComp : {b : MLDirichCatObj} ->
  {p, q, r : DirichVertSlObj b} ->
  DirichVertSlMor {b} q r -> DirichVertSlMor {b} p q -> DirichVertSlMor {b} p r
DirichVertSlComp = sliceComp

------------------------------------------
---- Factored-Dirichlet-slice objects ----
------------------------------------------

-- These are the objects of the slice categories of Dirichlet functors
-- (which are equivalent to Dirichlet presheaves on categories of elements
-- of Dirichlet functors), expressed in terms of vertical-Cartesian factoring.

-- The intermediate object of a factored slice of a Dirichlet functor.
public export
DirichFactSlIntObj : (b : MLDirichCatObj) -> DirichCartSlObj b -> Type
DirichFactSlIntObj b = DirichVertSlObj . DirichCartSlEmbed {b}

public export
DirichFactSlObj : MLDirichCatObj -> Type
DirichFactSlObj b = Sigma {a=(DirichCartSlObj b)} (DirichFactSlIntObj b)

public export
DirichFactSlCartObj : {b : MLDirichCatObj} ->
  DirichFactSlObj b -> DirichCartSlObj b
DirichFactSlCartObj = DPair.fst

public export
DirichFactSlIntEmbed : {b : MLDirichCatObj} ->
  DirichFactSlObj b -> MLDirichCatObj
DirichFactSlIntEmbed {b} = DirichCartSlEmbed {b} . DirichFactSlCartObj {b}

public export
DirichFactSlIntProjL : {b : MLDirichCatObj} ->
  (p : DirichFactSlObj b) ->
  DirichNatTrans (DirichFactSlIntEmbed {b} p) b
DirichFactSlIntProjL {b} p = DirichCartSlProj {b} (DirichFactSlCartObj {b} p)

public export
DirichFactSlVertObj : {b : MLDirichCatObj} ->
  (p : DirichFactSlObj b) -> DirichFactSlIntObj b (DirichFactSlCartObj {b} p)
DirichFactSlVertObj = DPair.snd

public export
DirichFactSlEmbed : {b : MLDirichCatObj} -> DirichFactSlObj b -> MLDirichCatObj
DirichFactSlEmbed {b} p =
  DirichVertSlEmbed {b=(DirichFactSlIntEmbed {b} p)} $ DirichFactSlVertObj {b} p

public export
DirichFactSlIntProjR : {b : MLDirichCatObj} ->
  (p : DirichFactSlObj b) ->
  DirichNatTrans (DirichFactSlEmbed {b} p) (DirichFactSlIntEmbed {b} p)
DirichFactSlIntProjR {b} p =
  DirichVertSlProj {b=(DirichFactSlIntEmbed {b} p)} $ DirichFactSlVertObj {b} p

public export
DirichFactSlTotPos : {b : MLDirichCatObj} -> DirichFactSlObj b -> Type
DirichFactSlTotPos {b} = dfPos . DirichFactSlEmbed {b}

public export
DirichFactSlTotDir : {b : MLDirichCatObj} -> (p : DirichFactSlObj b) ->
  SliceObj (DirichFactSlTotPos {b} p)
DirichFactSlTotDir {b} p = dfDir (DirichFactSlEmbed {b} p)

public export
DirichFactSlProj : {b : MLDirichCatObj} -> (p : DirichFactSlObj b) ->
  DirichNatTrans (DirichFactSlEmbed {b} p) b
DirichFactSlProj {b} p =
  dntVCatComp
    {p=(DirichFactSlEmbed {b} p)}
    {q=(DirichFactSlIntEmbed {b} p)}
    {r=b}
    (DirichFactSlIntProjL {b} p)
    (DirichFactSlIntProjR {b} p)

public export
DirichFactSlOnPos : {b : MLDirichCatObj} -> (p : DirichFactSlObj b) ->
  DirichFactSlTotPos {b} p -> dfPos b
DirichFactSlOnPos {b} p =
  dntOnPos {p=(DirichFactSlEmbed {b} p)} {q=b} (DirichFactSlProj {b} p)

public export
DirichFactSlDir : {b : MLDirichCatObj} ->
  (p : DirichFactSlObj b) -> DirichFactSlTotPos {b} p -> Type
DirichFactSlDir {b} p = dfDir (DirichFactSlEmbed {b} p)

public export
DirichFactSlOnDir : {b : MLDirichCatObj} ->
  (p : DirichFactSlObj b) ->
  SliceMorphism {a=(DirichFactSlTotPos {b} p)}
    (DirichFactSlDir {b} p)
    (dfDir b . DirichFactSlOnPos {b} p)
DirichFactSlOnDir {b} p =
  dntOnDir {p=(DirichFactSlEmbed {b} p)} {q=b} (DirichFactSlProj {b} p)

public export
DirichFactSlTot : {b : MLDirichCatObj} -> DirichFactSlObj b -> Type
DirichFactSlTot {b} p = dfTot (DirichFactSlEmbed {b} p)

--------------------------------------------
---- Factored-Dirichlet-slice morphisms ----
--------------------------------------------

-- The slice analogue of `arBaseChangeArena`.
public export
DirichSlBaseChangePos : {b : MLDirichCatObj} ->
  (p : DirichFactSlObj b) -> {x : SliceObj (dfPos b)} ->
  SliceMorphism {a=(dfPos b)} x (DirichFactSlCartObj {b} p) ->
  SliceObj (dfPos b)
DirichSlBaseChangePos {b} p {x} f = x

public export
DirichSlBaseChangeDir : {b : MLDirichCatObj} ->
  (p : DirichFactSlObj b) -> {x : SliceObj (dfPos b)} ->
  (f : SliceMorphism {a=(dfPos b)} x (DirichFactSlCartObj {b} p)) ->
  SliceObj (DirichCartSlTot {b} $ DirichSlBaseChangePos {b} p {x} f)
DirichSlBaseChangeDir {b} p {x} f = snd p . dpBimap (dpMapSnd f) (\_ => id)

public export
DirichSlBaseChange : {b : MLDirichCatObj} ->
  (p : DirichFactSlObj b) -> {x : SliceObj (dfPos b)} ->
  SliceMorphism {a=(dfPos b)} x (DirichFactSlCartObj {b} p) ->
  DirichFactSlObj b
DirichSlBaseChange {b} p {x} f =
  (DirichSlBaseChangePos {b} p {x} f ** DirichSlBaseChangeDir {b} p {x} f)

-- Because vertical morphisms do not change position, the only
-- position change between the positions of the domain and the
-- positions of the intermediate object of the codomain comes
-- from a single natural transformation -- the Cartesian component
-- of the total-space morphism of the slice category.  So the
-- first thing we choose in defining a slice morphism is an
-- on-positions function from the domain to the codomain (whose
-- codomain is also equal to the positions of the intermediate
-- object of the codomain projection, because the on-positions
-- component of the vertical component of that projection is
-- the identity).

-- The type of the on-positions function of a slice morphism.
public export
DirichFactSlCartMor : {b : MLDirichCatObj} ->
  DirichFactSlObj b -> DirichFactSlObj b -> Type
DirichFactSlCartMor {b} p q =
  DirichCartSlMor {b} (DirichFactSlCartObj {b} p) (DirichFactSlCartObj {b} q)

-- Because the positions of the domain and codomain are equal to those
-- of the intermediate objects of their respective projections, the
-- on-positions function which determines a Cartesian slice morphism
-- of their intermediate objects also determines an (identical) slice
-- morphism between the positions of the domain and codomain themselves.
-- That in turn induces a base change on the codomain.
public export
DirichFactSlMorIntObj : {b : MLDirichCatObj} -> (p, q : DirichFactSlObj b) ->
  DirichFactSlCartMor {b} p q -> DirichFactSlObj b
DirichFactSlMorIntObj {b} p q = DirichSlBaseChange {b} q {x=(fst p)}

-- The intermediate object has the same positions as the domain,
-- and the on-positions function constitutes a Cartesian morphism
-- from it to the codomain.  Thus, a vertical-slice morphism from
-- the domain to it will form a general-slice morphism from the
-- domain to the codomain.
public export
DirichFactSlVertMorSl : {b : MLDirichCatObj} -> (dom : DirichFactSlObj b) -> Type
DirichFactSlVertMorSl {b} dom =
  DPair (DirichFactSlTotPos {b} dom) (dfDir b . fst)

public export
DirichFactSlVertMorDom : {b : MLDirichCatObj} -> (p : DirichFactSlObj b) ->
  SliceObj (DirichFactSlVertMorSl {b} p)
DirichFactSlVertMorDom {b} = snd

public export
DirichFactSlVertMorCod : {b : MLDirichCatObj} -> (p, q : DirichFactSlObj b) ->
  DirichFactSlCartMor {b} p q ->
  SliceObj (DirichFactSlVertMorSl {b} p)
DirichFactSlVertMorCod {b} p q m = DirichSlBaseChangeDir {b} q {x=(fst p)} m

public export
DirichFactSlVertMor : {b : MLDirichCatObj} -> (p, q : DirichFactSlObj b) ->
  DirichFactSlCartMor {b} p q -> Type
DirichFactSlVertMor {b} p q m =
  SliceMorphism {a=(DirichFactSlVertMorSl {b} p)}
    (DirichFactSlVertMorDom {b} p)
    (DirichFactSlVertMorCod {b} p q m)

public export
DirichFactSlMor : {b : MLDirichCatObj} ->
  DirichFactSlObj b -> DirichFactSlObj b -> Type
DirichFactSlMor {b} p q =
  DPair (DirichFactSlCartMor {b} p q) (DirichFactSlVertMor {b} p q)

public export
DirichFactSlIdOnPos : {b : MLDirichCatObj} ->
  (p : DirichFactSlObj b) -> SliceMorphism {a=(dfPos b)} (fst p) (fst p)
DirichFactSlIdOnPos {b} p = sliceId {a=(dfPos b)} (fst p)

public export
DirichFactSlIdOnDir : {b : MLDirichCatObj} ->
  (p : DirichFactSlObj b) ->
  SliceMorphism {a=(DirichFactSlVertMorSl {b} p)}
    (DirichFactSlVertMorDom {b} p)
    (DirichFactSlVertMorCod {b} p p (DirichFactSlIdOnPos {b} p))
DirichFactSlIdOnDir {b} p itot = case itot of ((bi ** pi) ** bd) => id

public export
DirichFactSlId : {b : MLDirichCatObj} ->
  (p : DirichFactSlObj b) -> DirichFactSlMor {b} p p
DirichFactSlId {b} p =
  (DirichFactSlIdOnPos {b} p ** DirichFactSlIdOnDir {b} p)

public export
DirichFactSlCompOnPos : {b : MLDirichCatObj} ->
  {p, q, r : DirichFactSlObj b} ->
  DirichFactSlMor {b} q r -> DirichFactSlMor {b} p q ->
  SliceMorphism {a=(dfPos b)} (fst p) (fst r)
DirichFactSlCompOnPos {b} {p} {q} {r} g f = sliceComp (fst g) (fst f)

public export
DirichFactSlCompOnDirInt : {b : MLDirichCatObj} ->
  {p, q, r : DirichFactSlObj b} ->
  (g : DirichFactSlMor {b} q r) -> (f : DirichFactSlMor {b} p q) ->
  SliceMorphism {a=(DirichFactSlVertMorSl {b} p)}
    (DirichFactSlVertMorCod {b} p q (fst f))
    (DirichFactSlVertMorCod {b} p r (DirichFactSlCompOnPos {b} {p} {q} {r} g f))
DirichFactSlCompOnDirInt {b} {p} {q} {r} g f i =
  snd g ((fst (fst i) ** fst f (fst $ fst i) (snd $ fst i)) ** snd i)

public export
DirichFactSlCompOnDir : {b : MLDirichCatObj} ->
  {p, q, r : DirichFactSlObj b} ->
  (g : DirichFactSlMor {b} q r) -> (f : DirichFactSlMor {b} p q) ->
  SliceMorphism {a=(DirichFactSlVertMorSl {b} p)}
    (DirichFactSlVertMorDom {b} p)
    (DirichFactSlVertMorCod {b} p r (DirichFactSlCompOnPos {b} {p} {q} {r} g f))
DirichFactSlCompOnDir {b} {p} {q} {r} g f =
  sliceComp (DirichFactSlCompOnDirInt {b} {p} {q} {r} g f) (snd f)

public export
DirichFactSlComp : {b : MLDirichCatObj} ->
  {p, q, r : DirichFactSlObj b} ->
  DirichFactSlMor {b} q r -> DirichFactSlMor {b} p q -> DirichFactSlMor {b} p r
DirichFactSlComp {b} {p} {q} {r} g f =
  (DirichFactSlCompOnPos {b} {p} {q} {r} g f **
   DirichFactSlCompOnDir {b} {p} {q} {r} g f)

-------------------------------------------------------------------------
---- Translation between factored and standard Dirichlet slice forms ----
-------------------------------------------------------------------------

public export
MlDirichSlObjToFact : {ar : MLArena} -> MlDirichSlObj ar -> DirichFactSlObj ar
MlDirichSlObjToFact {ar} p =
  (mdsOnPos p ** \bd => mdsDir p (fst $ fst bd) (snd $ fst bd) (snd bd))

public export
MlDirichFactToSlObj : {ar : MLArena} -> DirichFactSlObj ar -> MlDirichSlObj ar
MlDirichFactToSlObj {ar} p =
  MDSobj (fst p) (\bi, pi, bd => snd p ((bi ** pi) ** bd))

public export
MlDirichSlMorToFact : {ar : MLArena} -> {p, q : MlDirichSlObj ar} ->
  MlDirichSlMor {ar} p q ->
  DirichFactSlMor {b=ar}
    (MlDirichSlObjToFact {ar} p)
    (MlDirichSlObjToFact {ar} q)
MlDirichSlMorToFact {ar} {p} {q} m =
  (mdsmOnPos m ** \i => mdsmOnDir m (fst $ fst i) (snd $ fst i) (snd i))

public export
MlDirichSlMorFromFact : {ar : MLArena} -> {p, q : MlDirichSlObj ar} ->
  DirichFactSlMor {b=ar}
    (MlDirichSlObjToFact {ar} p)
    (MlDirichSlObjToFact {ar} q) ->
  MlDirichSlMor {ar} p q
MlDirichSlMorFromFact {ar} {p} {q} m =
  MDSM (fst m) (\i, j, d => snd m ((i ** j) ** d))

public export
MlDirichFactToSlMor : {ar : MLArena} -> {p, q : DirichFactSlObj ar} ->
  DirichFactSlMor {b=ar} p q ->
  MlDirichSlMor {ar} (MlDirichFactToSlObj {ar} p) (MlDirichFactToSlObj {ar} q)
MlDirichFactToSlMor {ar} {p} {q} m =
  MDSM (fst m) (\i, j, d => snd m ((i ** j) ** d))

public export
MlDirichFactFromSlMor : {ar : MLArena} -> {p, q : DirichFactSlObj ar} ->
  MlDirichSlMor {ar}
    (MlDirichFactToSlObj {ar} p) (MlDirichFactToSlObj {ar} q) ->
  DirichFactSlMor {b=ar} p q
MlDirichFactFromSlMor {ar} {p} {q} m =
  (mdsmOnPos m ** \((bi ** pi) ** bd), pd => mdsmOnDir m bi pi bd pd)

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
dfHomObjIsTot : (p, q : MLDirichCatObj) ->
  dfTot (dfHomObj p q) = DirichNatTrans p q
dfHomObjIsTot p q = Refl

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

------------------------
---- Initial object ----
------------------------

public export
dfSlInitialPos : (b : MLDirichCatObj) -> MlSlArProjOnPos b
dfSlInitialPos b bi = Void

public export
dfSlInitialDir : (b : MLDirichCatObj) -> MlDirichSlDir b (dfSlInitialPos b)
dfSlInitialDir b bi v = void v

public export
dfSlInitial : (b : MLDirichCatObj) -> MlDirichSlObj b
dfSlInitial b = MDSobj (dfSlInitialPos b) (dfSlInitialDir b)

public export
dfSlFromInitOnPos : {b : MLDirichCatObj} ->
  (sl : MlDirichSlObj b) -> MlDirichSlMorOnPos {ar=b} (dfSlInitial b) sl
dfSlFromInitOnPos {b} sl i v = void v

public export
dfSlFromInitOnDir : {b : MLDirichCatObj} ->
  (sl : MlDirichSlObj b) ->
  MlDirichSlMorOnDir {ar=b} (dfSlInitial b) sl (dfSlFromInitOnPos {b} sl)
dfSlFromInitOnDir {b} sl i v = void v

public export
dfSlFromInit : {b : MLDirichCatObj} ->
  (sl : MlDirichSlObj b) -> MlDirichSlMor {ar=b} (dfSlInitial b) sl
dfSlFromInit {b} sl =
  MDSM (dfSlFromInitOnPos {b} sl) (dfSlFromInitOnDir {b} sl)

-------------------------
---- Terminal object ----
-------------------------

public export
dfSlTerminalPos : (b : MLDirichCatObj) -> MlSlArProjOnPos b
dfSlTerminalPos b bi = Unit

public export
dfSlTerminalDir : (b : MLDirichCatObj) -> MlDirichSlDir b (dfSlTerminalPos b)
dfSlTerminalDir b bi u bd = Unit

public export
dfSlTerminal : (b : MLDirichCatObj) -> MlDirichSlObj b
dfSlTerminal b = MDSobj (dfSlTerminalPos b) (dfSlTerminalDir b)

public export
dfSlToTermOnPos : {b : MLDirichCatObj} ->
  (sl : MlDirichSlObj b) -> MlDirichSlMorOnPos {ar=b} sl (dfSlTerminal b)
dfSlToTermOnPos {b} sl i j = ()

public export
dfSlToTermOnDir : {b : MLDirichCatObj} ->
  (sl : MlDirichSlObj b) ->
  MlDirichSlMorOnDir {ar=b} sl (dfSlTerminal b) (dfSlToTermOnPos {b} sl)
dfSlToTermOnDir {b} sl i j bd sd = ()

public export
dfSlToTerm : {b : MLDirichCatObj} ->
  (sl : MlDirichSlObj b) -> MlDirichSlMor {ar=b} sl (dfSlTerminal b)
dfSlToTerm {b} sl =
  MDSM (dfSlToTermOnPos {b} sl) (dfSlToTermOnDir {b} sl)

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
dfSlCoproduct : {b : MLDirichCatObj} ->
  MlDirichSlObj b -> MlDirichSlObj b -> MlDirichSlObj b
dfSlCoproduct {b} p q =
  MDSobj (dfSlCoproductPos {b} p q) (dfSlCoproductDir {b} p q)

public export
dfSlInjLOnPos : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) ->
  MlDirichSlMorOnPos {ar=b} p (dfSlCoproduct {b} p q)
dfSlInjLOnPos {b} p q bi = Left

public export
dfSlInjLOnDir : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) ->
  MlDirichSlMorOnDir {ar=b} p (dfSlCoproduct {b} p q)
    (dfSlInjLOnPos {b} p q)
dfSlInjLOnDir {b} p q bi pi bd = Prelude.id

public export
dfSlInjL : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) -> MlDirichSlMor {ar=b} p (dfSlCoproduct p q)
dfSlInjL {b} p q =
  MDSM (dfSlInjLOnPos {b} p q) (dfSlInjLOnDir {b} p q)

public export
dfSlInjROnPos : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) ->
  MlDirichSlMorOnPos {ar=b} q (dfSlCoproduct {b} p q)
dfSlInjROnPos {b} p q bi = Right

public export
dfSlInjROnDir : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) ->
  MlDirichSlMorOnDir {ar=b} q (dfSlCoproduct {b} p q)
    (dfSlInjROnPos {b} p q)
dfSlInjROnDir {b} p q bi qi bd = Prelude.id

public export
dfSlInjR : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) -> MlDirichSlMor {ar=b} q (dfSlCoproduct p q)
dfSlInjR {b} p q =
  MDSM (dfSlInjROnPos {b} p q) (dfSlInjROnDir {b} p q)

public export
dfSlCaseOnPos : {b : MLDirichCatObj} -> {p, q, r : MlDirichSlObj b} ->
  MlDirichSlMorOnPos {ar=b} p r ->
  MlDirichSlMorOnPos {ar=b} q r ->
  MlDirichSlMorOnPos {ar=b} (dfSlCoproduct {b} p q) r
dfSlCaseOnPos {b} {p} {q} {r} mpr mqr bi = eitherElim (mpr bi) (mqr bi)

public export
dfSlCaseOnDir : {b : MLDirichCatObj} -> {p, q, r : MlDirichSlObj b} ->
  {mpir : MlDirichSlMorOnPos {ar=b} p r} ->
  {mqir : MlDirichSlMorOnPos {ar=b} q r} ->
  MlDirichSlMorOnDir {ar=b} p r mpir ->
  MlDirichSlMorOnDir {ar=b} q r mqir ->
  MlDirichSlMorOnDir {ar=b} (dfSlCoproduct {b} p q) r
    (dfSlCaseOnPos {b} {p} {q} {r} mpir mqir)
dfSlCaseOnDir {b} {p} {q} {r} {mpir} {mqir} mpdr mqdr bi pqi bd pqd =
  case pqi of
    Left pi => mpdr bi pi bd pqd
    Right qi => mqdr bi qi bd pqd

public export
dfSlCase : {b : MLDirichCatObj} -> {p, q, r : MlDirichSlObj b} ->
  MlDirichSlMor {ar=b} p r -> MlDirichSlMor {ar=b} q r ->
  MlDirichSlMor {ar=b} (dfSlCoproduct {b} p q) r
dfSlCase {b} {p} {q} {r} mpr mqr =
  MDSM
    (dfSlCaseOnPos {b} {p} {q} {r} (mdsmOnPos mpr) (mdsmOnPos mqr))
    (dfSlCaseOnDir {b} {p} {q} {r} (mdsmOnDir mpr) (mdsmOnDir mqr))

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
dfSlParProduct : {b : MLDirichCatObj} ->
  MlDirichSlObj b -> MlDirichSlObj b -> MlDirichSlObj b
dfSlParProduct {b} p q =
  MDSobj (dfSlParProductPos {b} p q) (dfSlParProductDir {b} p q)

public export
dfSlProj1OnPos : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) ->
  MlDirichSlMorOnPos {ar=b} (dfSlParProduct {b} p q) p
dfSlProj1OnPos {b} p q bi = fst

public export
dfSlProj1OnDir : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) ->
  MlDirichSlMorOnDir {ar=b} (dfSlParProduct {b} p q) p
    (dfSlProj1OnPos {b} p q)
dfSlProj1OnDir {b} p q bi pi bd = fst

public export
dfSlProj1 : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) -> MlDirichSlMor {ar=b} (dfSlParProduct p q) p
dfSlProj1 {b} p q =
  MDSM (dfSlProj1OnPos {b} p q) (dfSlProj1OnDir {b} p q)

public export
dfSlProj2OnPos : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) ->
  MlDirichSlMorOnPos {ar=b} (dfSlParProduct {b} p q) q
dfSlProj2OnPos {b} p q bi = snd

public export
dfSlProj2OnDir : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) ->
  MlDirichSlMorOnDir {ar=b} (dfSlParProduct {b} p q) q
    (dfSlProj2OnPos {b} p q)
dfSlProj2OnDir {b} p q bi pi bd = snd

public export
dfSlProj2 : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) -> MlDirichSlMor {ar=b} (dfSlParProduct p q) q
dfSlProj2 {b} p q =
  MDSM (dfSlProj2OnPos {b} p q) (dfSlProj2OnDir {b} p q)

public export
dfSlMkProdOnPos : {b : MLDirichCatObj} -> {p, q, r : MlDirichSlObj b} ->
  MlDirichSlMorOnPos {ar=b} p q ->
  MlDirichSlMorOnPos {ar=b} p r ->
  MlDirichSlMorOnPos {ar=b} p (dfSlParProduct {b} q r)
dfSlMkProdOnPos {b} {p} {q} {r} mpq mpr bi pi = (mpq bi pi, mpr bi pi)

public export
dfSlMkProdOnDir : {b : MLDirichCatObj} -> {p, q, r : MlDirichSlObj b} ->
  {mpiq : MlDirichSlMorOnPos {ar=b} p q} ->
  {mpir : MlDirichSlMorOnPos {ar=b} p r} ->
  MlDirichSlMorOnDir {ar=b} p q mpiq ->
  MlDirichSlMorOnDir {ar=b} p r mpir ->
  MlDirichSlMorOnDir {ar=b} p (dfSlParProduct {b} q r)
    (dfSlMkProdOnPos {b} {p} {q} {r} mpiq mpir)
dfSlMkProdOnDir {b} {p} {q} {r} {mpiq} {mpir} mpdq mpdr bi pqi bd pqd =
  (mpdq bi pqi bd pqd, mpdr bi pqi bd pqd)

public export
dfSlMkProd : {b : MLDirichCatObj} -> {p, q, r : MlDirichSlObj b} ->
  MlDirichSlMor {ar=b} p q -> MlDirichSlMor {ar=b} p r ->
  MlDirichSlMor {ar=b} p (dfSlParProduct {b} q r)
dfSlMkProd {b} {p} {q} {r} mpq mpr =
  MDSM
    (dfSlMkProdOnPos {b} {p} {q} {r} (mdsmOnPos mpq) (mdsmOnPos mpr))
    (dfSlMkProdOnDir {b} {p} {q} {r} (mdsmOnDir mpq) (mdsmOnDir mpr))

---------------------
---- Hom-objects ----
---------------------

public export
dfSlHomObjPos : {b : MLDirichCatObj} ->
  MlDirichSlObj b -> MlDirichSlObj b -> MlSlArProjOnPos b
dfSlHomObjPos {b} p q bi = mdsOnPos p bi -> mdsOnPos q bi

public export
dfSlHomObjDir : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) ->
  MlDirichSlDir b (dfSlHomObjPos {b} p q)
dfSlHomObjDir {b} p q bi slp bd =
  SliceMorphism {a=(mdsOnPos p bi)}
    (flip (mdsDir p bi) bd)
    (flip (mdsDir q bi) bd . slp)

public export
dfSlHomObj : {b : MLDirichCatObj} ->
  MlDirichSlObj b -> MlDirichSlObj b -> MlDirichSlObj b
dfSlHomObj {b} p sl =
  MDSobj (dfSlHomObjPos {b} p sl) (dfSlHomObjDir {b} p sl)

-- Each base direction of the total object of a Dirichlet slice object
-- induces a Dirichlet functor on `Type`.
public export
dfSlObjDirF : {b : MLDirichCatObj} ->
  (p : MlDirichSlObj b) -> dfTot b -> MLDirichCatObj
dfSlObjDirF {b=(bpos ** bdir)} (MDSobj ppos pdir) (bi ** bd) =
  (ppos bi ** \pi => pdir bi pi bd)

-- Each direction of the total object of a Dirichlet slice object
-- includes a direction of the base object.
public export
dfSlObjBaseTot : {b : MLDirichCatObj} -> (p : MlDirichSlObj b) ->
  mlDirichSlObjTotTot {ar=b} p -> dfTot b
dfSlObjBaseTot {b} p sldt = (fst (fst sldt) ** fst (snd sldt))

-- Thus, each direction of the total object of a Dirichlet slice
-- object induces a Dirichlet functor on `Type`.
public export
dfSlObjTotF : {b : MLDirichCatObj} -> (p : MlDirichSlObj b) ->
  mlDirichSlObjTotTot {ar=b} p -> MLDirichCatObj
dfSlObjTotF {b} p sldt = dfSlObjDirF {b} p (dfSlObjBaseTot {b} p sldt)

-- Each base direction of a Dirichlet slice hom-object
-- induces two Dirichlet functors, one corresponding to the domain and
-- one corresponding to the codomain.
public export
dfSlHomObjDomF : {b : MLDirichCatObj} -> (p, q : MlDirichSlObj b) ->
  dfTot b -> MLDirichCatObj
dfSlHomObjDomF {b=(bpos ** bdir)} (MDSobj ppos pdir) (MDSobj qpos qdir)
  (bi ** bd) =
    (ppos bi ** \pi => pdir bi pi bd)

public export
dfSlHomObjCodF : {b : MLDirichCatObj} -> (p, q : MlDirichSlObj b) ->
  dfTot b -> MLDirichCatObj
dfSlHomObjCodF {b=(bpos ** bdir)} (MDSobj ppos pdir) (MDSobj qpos qdir)
  (bi ** bd) =
    (qpos bi ** \qi => qdir bi qi bd)

-- Thus, each direction of the total object of a Dirichlet slice hom-object
-- induces two Dirichlet functors, one corresponding to the domain and
-- one corresponding to the codomain.

public export
dfSlHomObjTotDomF : {b : MLDirichCatObj} -> (p, q : MlDirichSlObj b) ->
  mlDirichSlObjTotTot (dfSlHomObj p q) -> MLDirichCatObj
dfSlHomObjTotDomF {b} p q dt =
  dfSlHomObjDomF {b} p q (dfSlObjBaseTot (dfSlHomObj p q) dt)

public export
dfSlHomObjTotCodF : {b : MLDirichCatObj} -> (p, q : MlDirichSlObj b) ->
  mlDirichSlObjTotTot (dfSlHomObj p q) -> MLDirichCatObj
dfSlHomObjTotCodF {b} p q dt =
  dfSlHomObjCodF {b} p q (dfSlObjBaseTot (dfSlHomObj p q) dt)

-- Each direction of the total object of a Dirichlet slice hom-object
-- induces a natural transformation between the induced Dirichlet functors
-- on `Type`.
public export
dfSlHomObjTotNT : {b : MLDirichCatObj} -> (p, q : MlDirichSlObj b) ->
  (hdt : mlDirichSlObjTotTot {ar=b} $ dfSlHomObj {b} p q) ->
  DirichNatTrans (dfSlHomObjTotDomF {b} p q hdt) (dfSlHomObjTotCodF {b} p q hdt)
dfSlHomObjTotNT {b=(bpos ** bdir)} (MDSobj ppos pdir) (MDSobj qpos qdir) hdt =
  (snd (fst hdt) ** snd (snd hdt))

public export
dfSlEvalOnPos : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) ->
  MlDirichSlMorOnPos {ar=b} (dfSlParProduct {b} (dfSlHomObj {b} p q) p) q
dfSlEvalOnPos {b} p q bi slp = fst slp $ snd slp

public export
dfSlEvalOnDir : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) ->
  MlDirichSlMorOnDir {ar=b}
    (dfSlParProduct {b} (dfSlHomObj {b} p q) p)
    q
    (dfSlEvalOnPos {b} p q)
dfSlEvalOnDir {b} p q bi slp bd sld = fst sld (snd slp) $ snd sld

public export
dfSlEval : {b : MLDirichCatObj} ->
  (p, q : MlDirichSlObj b) ->
  MlDirichSlMor {ar=b} (dfSlParProduct {b} (dfSlHomObj {b} p q) p) q
dfSlEval {b} p q =
  MDSM (dfSlEvalOnPos {b} p q) (dfSlEvalOnDir {b} p q)

public export
dfSlCurryOnPos : {b : MLDirichCatObj} ->
  {p, q, r : MlDirichSlObj b} ->
  MlDirichSlMor {ar=b} (dfSlParProduct {b} p q) r ->
  MlDirichSlMorOnPos {ar=b} p (dfSlHomObj {b} q r)
dfSlCurryOnPos {b} {p} {q} {r} m bi pi qi =
  mdsmOnPos m bi (pi, qi)

public export
dfSlCurryOnDir : {b : MLDirichCatObj} ->
  {p, q, r : MlDirichSlObj b} ->
  (m : MlDirichSlMor {ar=b} (dfSlParProduct {b} p q) r) ->
  MlDirichSlMorOnDir {ar=b} p (dfSlHomObj {b} q r)
    (dfSlCurryOnPos {b} {p} {q} {r} m)
dfSlCurryOnDir {b} {p} {q} {r} m bi pi bd pd qi qd =
  mdsmOnDir m bi (pi, qi) bd (pd, qd)

public export
dfSlCurry : {b : MLDirichCatObj} ->
  {p, q, r : MlDirichSlObj b} ->
  MlDirichSlMor {ar=b} (dfSlParProduct {b} p q) r ->
  MlDirichSlMor {ar=b} p (dfSlHomObj {b} q r)
dfSlCurry {b} {p} {q} {r} m =
  MDSM
    (dfSlCurryOnPos {b} {p} {q} {r} m)
    (dfSlCurryOnDir {b} {p} {q} {r} m)

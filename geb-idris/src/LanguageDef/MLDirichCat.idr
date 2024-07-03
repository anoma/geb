module LanguageDef.MLDirichCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import LanguageDef.QType
import public LanguageDef.InternalCat
import public LanguageDef.SliceFuncCat

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
DirichCatElObjPos : (p : MLDirichCatObj) -> dfPos p -> Type
DirichCatElObjPos p = SliceObj . dfDir {p}

public export
DirichCatElObjPosPair : (p : MLDirichCatObj) -> dfPos p -> Type
DirichCatElObjPosPair p = ProductMonad . DirichCatElObjPos p

public export
DirichCatElObj : MLDirichCatObj -> Type
DirichCatElObj p = Sigma {a=(dfPos p)} $ DirichCatElObjPos p

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
  Sigma {a=(DirichCatElObjPosPair p i)} $
    \xy => DirichCatElPosMor p i (fst xy) (snd xy)

public export
DirichCatElMorTot : MLDirichCatObj -> Type
DirichCatElMorTot p = Sigma {a=(dfPos p)} $ DirichCatElMorTotPos p

public export
DirichCatElMorPos : {p : MLDirichCatObj} -> DirichCatElMorTot p -> dfPos p
DirichCatElMorPos {p} m = fst m

public export
DirichCatElMorBaseObj : {p : MLDirichCatObj} -> DirichCatElMorTot p -> Type
DirichCatElMorBaseObj {p} = DirichCatElObjPos p . DirichCatElMorPos {p}

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
DirichCatElMor : {p : MLDirichCatObj} -> IntMorSig (DirichCatElObj p)
DirichCatElMor {p} elx ely =
  PreImage {a=(DirichCatElMorTot p)} {b=(DirichCatElObjPair p)}
    (DirichCatElMorSig {p})
    (elx, ely)

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
  (Element0 (pi ** ((slx, sly) ** m)) Refl) =
    Element0
      (onpos pi **
       ((SliceFibSigmaF (ondir pi) slx, SliceFibSigmaF (ondir pi) sly) **
        sfsMap {f=(ondir pi)} slx sly m))
      Refl

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
DirichDirichCatElArPos p i = (pos : Type ** pos -> DirichCatElObjPos p i)

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

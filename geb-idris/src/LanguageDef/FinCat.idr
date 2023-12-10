module LanguageDef.FinCat

import Library.IdrisUtils
import Library.IdrisCategories

-------------------------------
-------------------------------
---- `FinSet` as interface ----
-------------------------------
-------------------------------

-----------------
---- Objects ----
-----------------

-- A minimal interface to objects of `FinSet` must provide at least a
-- terminal object and finite coproducts; the latter are equivalent to
-- an initial object and binary coproducts, so we decompose them as such.
public export
data FinSetObjF : Type -> Type where
  FSO0 : {0 a : Type} -> FinSetObjF a
  FSO1 : {0 a : Type} -> FinSetObjF a
  FSOC : {0 a : Type} -> a -> a -> FinSetObjF a

-- An algebra of `FinSetObjF` may be viewed as a container that can hold any
-- object of `FinSet` -- it can be constructed in all the ways that objects
-- of `FinSet` can be constructed.
public export
FinSetObjAlg : Type -> Type
FinSetObjAlg = Algebra FinSetObjF

-- A coalgebra of `FinSetObjF` may be viewed as a container that always
-- holds some object of `FinSet` -- it can always satisfy a pattern-match
-- on the type of objects of `FinSet`.
public export
FinSetObjCoalg : Type -> Type
FinSetObjCoalg = Coalgebra FinSetObjF

public export
FinSetObjProAlg : Type -> Type
FinSetObjProAlg = EndoProAlgebra FinSetObjF

public export
FinSetObjDialg : Type -> Type
FinSetObjDialg = EndoDialgebra FinSetObjF

public export
FinSetObjProToDialg : {0 a : Type} -> FinSetObjProAlg a -> FinSetObjDialg a
FinSetObjProToDialg = EndoProToDiAlg {f=FinSetObjF}

public export
FinSetObjFM : Type -> Type
FinSetObjFM = FreeMonad FinSetObjF

public export
finSetObjEval : FreeFEval FinSetObjF
finSetObjEval var term subst alg (InFree (TFV v)) = subst v
finSetObjEval var term subst alg (InFree (TFC t)) = alg $ case t of
  FSO0 => FSO0
  FSO1 => FSO1
  FSOC x y =>
    FSOC
      (finSetObjEval var term subst alg x)
      (finSetObjEval var term subst alg y)

public export
FinSetObjMu : Type
FinSetObjMu = Mu FinSetObjF

public export
finSetObjMuPure : {0 a : Type} -> Coalgebra FinSetObjFM a
finSetObjMuPure {a} = inFV {f=FinSetObjF} {a}

public export
finSetObjFreeAlg : {0 a : Type} -> FinSetObjAlg (FinSetObjFM a)
finSetObjFreeAlg {a} = inFC {f=FinSetObjF} {a}

public export
finSetObjInitAlg : FinSetObjAlg FinSetObjMu
finSetObjInitAlg = InitAlg {f=FinSetObjF}

public export
finSetObjInitAlgInv : FinSetObjCoalg FinSetObjMu
finSetObjInitAlgInv = InitAlgInv {f=FinSetObjF}

public export
FinSetObjCFCM : Type -> Type
FinSetObjCFCM = CofreeComonad FinSetObjF

public export
finSetObjTrace : CofreeFTrace FinSetObjF
finSetObjTrace label term ann coalg t = InCofree $ SFN (ann t) $ case coalg t of
  FSO0 => FSO0
  FSO1 => FSO1
  FSOC x y =>
    FSOC
      (finSetObjTrace label term ann coalg x)
      (finSetObjTrace label term ann coalg y)

public export
finSetObjErase : {0 a : Type} -> Algebra FinSetObjCFCM a
finSetObjErase {a} = CFCMerase {f=FinSetObjF} {a}

public export
finSetObjCofreeCoalg : {a : Type} -> FinSetObjCoalg (FinSetObjCFCM a)
finSetObjCofreeCoalg {a} = outCFC {f=FinSetObjF} {a}

public export
FinSetObjNu : Type
FinSetObjNu = Nu FinSetObjF

public export
finSetObjTermCoalg : FinSetObjCoalg FinSetObjNu
finSetObjTermCoalg = outNu {f=FinSetObjF}

public export
finSetObjTermCoalgInv : FinSetObjAlg FinSetObjNu
finSetObjTermCoalgInv = outNuInv {f=FinSetObjF}

---------------
---- Terms ----
---------------

public export
data FinSetTermF : (obj, term : Type) -> Type where
  FST1 : {0 obj, term : Type} -> FinSetTermF obj term
  FSTl : {0 obj, term : Type} -> (t : term) -> (r : obj) -> FinSetTermF obj term
  FSTr : {0 obj, term : Type} -> (l : obj) -> (t : term) -> FinSetTermF obj term

public export
FinSetTermAlg : Type -> Type -> Type
FinSetTermAlg obj = Algebra (FinSetTermF obj)

-- A coalgebra of `FinSetTermF` may be viewed as a container that always
-- holds some object of `FinSet` -- it can always satisfy a pattern-match
-- on the type of objects of `FinSet`.
public export
FinSetTermCoalg : Type -> Type -> Type
FinSetTermCoalg obj = Coalgebra (FinSetTermF obj)

public export
FinSetTermProAlg : Type -> Type -> Type
FinSetTermProAlg = EndoProAlgebra . FinSetTermF

public export
FinSetTermDialg : Type -> Type -> Type
FinSetTermDialg = EndoDialgebra . FinSetTermF

public export
FinSetTermProToDialg : {0 obj, a : Type} ->
  FinSetTermProAlg obj a -> FinSetTermDialg obj a
FinSetTermProToDialg {obj} = EndoProToDiAlg {f=(FinSetTermF obj)}

public export
FinSetTermFM : Type -> Type -> Type
FinSetTermFM = FreeMonad . FinSetTermF

public export
finSetTermEval : {0 obj : Type} -> FreeFEval (FinSetTermF obj)
finSetTermEval {obj} var term subst alg (InFree (TFV v)) = subst v
finSetTermEval {obj} var term subst alg (InFree (TFC t)) = alg $ case t of
  FST1 => FST1
  FSTl t r => FSTl (finSetTermEval {obj} var term subst alg t) r
  FSTr l t => FSTr l (finSetTermEval {obj} var term subst alg t)

public export
FinSetTermMu : Type -> Type
FinSetTermMu = Mu . FinSetTermF

public export
finSetTermMuPure : {obj : Type} -> {0 a : Type} ->
  Coalgebra (FinSetTermFM obj) a
finSetTermMuPure {obj} {a} = inFV {f=(FinSetTermF obj)} {a}

public export
finSetTermFreeAlg : {obj : Type} -> {0 a : Type} ->
  FinSetTermAlg obj (FinSetTermFM obj a)
finSetTermFreeAlg {obj} {a} = inFC {f=(FinSetTermF obj)} {a}

public export
finSetTermInitAlg : {obj : Type} -> FinSetTermAlg obj (FinSetTermMu obj)
finSetTermInitAlg {obj} = InitAlg {f=(FinSetTermF obj)}

public export
finSetTermInitAlgInv : {obj : Type} -> FinSetTermCoalg obj (FinSetTermMu obj)
finSetTermInitAlgInv {obj} = InitAlgInv {f=(FinSetTermF obj)}

public export
FinSetTermCFCM : Type -> Type -> Type
FinSetTermCFCM = CofreeComonad . FinSetTermF

public export
finSetTermTrace : {obj : Type} -> CofreeFTrace (FinSetTermF obj)
finSetTermTrace {obj} label term ann coalg t =
  InCofree $ SFN (ann t) $ case coalg t of
    FST1 => FST1
    FSTl t r => FSTl (finSetTermTrace {obj} label term ann coalg t) r
    FSTr l t => FSTr l (finSetTermTrace {obj} label term ann coalg t)

public export
finSetTermErase : {obj : Type} -> {0 a : Type} -> Algebra (FinSetTermCFCM obj) a
finSetTermErase {obj} {a} = CFCMerase {f=(FinSetTermF obj)} {a}

public export
finSetTermCofreeCoalg : {obj : Type} -> {a : Type} ->
  FinSetTermCoalg obj (FinSetTermCFCM obj a)
finSetTermCofreeCoalg {obj} {a} = outCFC {f=(FinSetTermF obj)} {a}

public export
FinSetTermNu : Type -> Type
FinSetTermNu = Nu . FinSetTermF

public export
finSetTermTermCoalg : {obj : Type} -> FinSetTermCoalg obj (FinSetTermNu obj)
finSetTermTermCoalg {obj} = outNu {f=(FinSetTermF obj)}

public export
finSetTermTermCoalgInv : {obj : Type} -> FinSetTermAlg obj (FinSetTermNu obj)
finSetTermTermCoalgInv {obj} = outNuInv {f=(FinSetTermF obj)}

----------------------------------------
---- Dependency of terms on objects ----
----------------------------------------

public export
data FinSetObjTermIdx : Type where
  FSOTo : FinSetObjTermIdx
  FSOTt : FinSetObjTermIdx

public export
FinSetObjTermObjSliceF : SliceFunctor FinSetObjTermIdx Unit
FinSetObjTermObjSliceF sl () = FinSetObjF (sl FSOTo)

public export
FinSetObjTermTermSliceF : SliceFunctor FinSetObjTermIdx Unit
FinSetObjTermTermSliceF sl () = FinSetTermF (sl FSOTo) (sl FSOTt)

public export
FinSetObjTermSliceF : SliceEndofunctor FinSetObjTermIdx
FinSetObjTermSliceF sl FSOTo = FinSetObjTermObjSliceF sl ()
FinSetObjTermSliceF sl FSOTt = FinSetObjTermTermSliceF sl ()

public export
FreeFinSetObjTermSlice : SliceEndofunctor FinSetObjTermIdx
FreeFinSetObjTermSlice = SliceFreeM {a=FinSetObjTermIdx} FinSetObjTermSliceF

public export
FinSetObjTermSliceEval : SliceFreeFEval FinSetObjTermSliceF
FinSetObjTermSliceEval sv sa subst alg i (InSlF i t) = case t of
  InSlV vt => subst i vt
  InSlC ct => alg i $ case i of
    FSOTo => case ct of
      FSO0 => FSO0
      FSO1 => FSO1
      FSOC x y =>
        FSOC
          (FinSetObjTermSliceEval sv sa subst alg FSOTo x)
          (FinSetObjTermSliceEval sv sa subst alg FSOTo y)
    FSOTt => case ct of
      FST1 => FST1
      FSTl lt r =>
        FSTl
          (FinSetObjTermSliceEval sv sa subst alg FSOTt lt)
          (FinSetObjTermSliceEval sv sa subst alg FSOTo r)
      FSTr l rt =>
        FSTr
          (FinSetObjTermSliceEval sv sa subst alg FSOTo l)
          (FinSetObjTermSliceEval sv sa subst alg FSOTt rt)

public export
FinSetTermDepF : (sl : SliceObj FinSetObjTermIdx) ->
  (dep : sl FSOTt -> sl FSOTo) ->
  FinSetObjTermSliceF sl FSOTt -> FinSetObjTermSliceF sl FSOTo
FinSetTermDepF sl dep FST1 = FSO1
FinSetTermDepF sl dep (FSTl t r) = FSOC (dep t) r
FinSetTermDepF sl dep (FSTr l t) = FSOC l (dep t)

public export
FreeFinSetTermDepSubst :
  (sl : SliceObj FinSetObjTermIdx) -> (dep : sl FSOTt -> sl FSOTo) ->
  (i : FinSetObjTermIdx) -> sl i -> FreeFinSetObjTermSlice sl FSOTo
FreeFinSetTermDepSubst sl dep i t = InSlFv $ case i of
  FSOTo => t
  FSOTt => dep t

FinSetObjTermSliceDep :
  (sl : SliceObj FinSetObjTermIdx) -> (i : FinSetObjTermIdx) ->
  FinSetObjTermSliceF (const $ FreeFinSetObjTermSlice sl FSOTo) i ->
  FreeFinSetObjTermSlice sl FSOTo
FinSetObjTermSliceDep sl i t = InSlFc $ case i of
  FSOTo => t
  FSOTt => case t of
    FST1 => FSO1
    FSTl l r => FSOC l r
    FSTr l r => FSOC l r

public export
FreeFinSetTermDep :
  (sl : SliceObj FinSetObjTermIdx) -> (dep : sl FSOTt -> sl FSOTo) ->
  FreeFinSetObjTermSlice sl FSOTt -> FreeFinSetObjTermSlice sl FSOTo
FreeFinSetTermDep sl dep =
  FinSetObjTermSliceEval
    sl
    (const $ FreeFinSetObjTermSlice sl FSOTo)
    (FreeFinSetTermDepSubst sl dep)
    (FinSetObjTermSliceDep sl)
    FSOTt

--------------------------
--------------------------
---- Finitary quivers ----
--------------------------
--------------------------

--------------------------------------------------
---- Quivers internal to arbitrary categories ----
--------------------------------------------------

-- An enriched quiver internal to a category which is itself internal to `Type`
-- is one whose edge-objects are drawn from some arbitrary category internal to
-- `Type` (possibly `Type` itself, which is self-enriched), and whose vertex
-- object comes from some other arbitrary category internal to `Type` (again
-- possibly `Type` itself).  A `QuivVE {vb} vp v e` is one whose vertex
-- category's objects are indexed by `vb` and are of the form `vb v'` for
-- some `v' : vb`, whose specific vertex-object is `v`, and whose edge-objects
-- are drawn from `e`.
public export
QuivVE : {0 vb : Type} -> SliceObj vb -> vb -> Type -> Type
QuivVE {vb} vp v = HomProf (ProductMonad $ vp v)

---------------------------------------------
---- Enriched quivers internal to `Type` ----
---------------------------------------------

-- An enriched quiver internal to `Type` is one whose edge-objects are drawn
-- from some arbitrary category internal to `Type` (possibly `Type` itself,
-- which is self-enriched), and whose vertex object comes from `Type` itself.
-- An `EnrQuivVE v e` is one whose vertex-object is `v` and whose edge-objects
-- are drawn from `e`.
public export
EnrQuivVE : Type -> Type -> Type
EnrQuivVE = QuivVE {vb=Type} id

------------------------------------------
---- `Type`-internal/enriched quivers ----
------------------------------------------

-- A quiver internal to and enriched over `Type` is one whose vertex object
-- and edge-objects are drawn from `Type`, the core category of the
-- metalanguage.  A `TypeQuivV v` is one whose vertex-object is `v`.
public export
TypeQuivV : Type -> Type
TypeQuivV = flip EnrQuivVE Type

-----------------------------------
---- `FinSet`-enriched quivers ----
-----------------------------------

-- A quiver internal to `Type` and enriched over `FinSet` is one whose
-- edge-objects are drawn from `FinSet` -- in other words, whose edge-sets are
-- all finite.  Such a quiver need not necessarily have a finite number of
-- _vertices_.  A `FinEnrQuivV v` is a `FinSet`-enriched quiver whose
-- vertex-object, which is an object of the metalanguage's core category
-- (`Type`), is `v`.
public export
FinEnrQuivV : Type -> Type
FinEnrQuivV = flip EnrQuivVE Nat

-----------------------------------
---- `FinSet`-internal quivers ----
-----------------------------------

-- A quiver internal to and enriched over `FinSet` is one whose vertex-objects
-- _and_ edge-objects are drawn from `FinSet`, so it has finite numbers of
-- both vertices and edges.  A `FinQuivN n` is one with `n` vertices.
public export
FinQuivN : Nat -> Type
FinQuivN = FinEnrQuivV . Fin

---------------------------
---- Reflexive quivers ----
---------------------------

-- A reflexive quiver is a quiver where every vertex has a distinguished
-- self-loop.

-- A reflexive quiver internal to and enriched over `Type` is one whose
-- vertex-object and edge-objects are drawn from `Type`, the core category
-- of the metalanguage, together with a distinguished self-loop for each vertex.
-- A `TypeRQuivSL {v} q` is a selection from a `TypeQuivV v` of self-loops for
-- each vertex object (which makes it a reflexive `Type-internal-and-enriched
-- quiver).
public export
TypeRQuivSL : {v : Type} -> TypeQuivV v -> Type
TypeRQuivSL {v} q = (x : v) -> q (x, x)

-- A reflexive quiver internal to `Type` and enriched over `FinSet` is a
-- reflexive quiver whose edge-objects are drawn from `FinSet`.
-- A `FinEnrQuivSL {v} q` is a selection from a `FinEnrQuivV v` of self-loops
-- for each vertex object (which makes it a reflexive
-- `Type-internal/FinSet-enriched quiver).
public export
FinEnrQuivSL : {v : Type} -> FinEnrQuivV v -> Type
FinEnrQuivSL {v} q = TypeRQuivSL {v} (Fin . q)

-- A reflexive quiver internal to and enriched over `FinSet` is one whose
-- vertex-objects _and_ edge-objects are drawn from `FinSet`, so it has finite
-- numbers of both vertices and edges.  A `FinQuivSL {n} q` is a selection
-- from a `FinQuivN n` of self-loops for each vertex object (which makes it
-- a reflexive FinSet-internal-and-enriched quiver).
public export
FinQuivSL : {n : Nat} -> FinQuivN n -> Type
FinQuivSL {n} = FinEnrQuivSL {v=(Fin n)}

-------------------------------
---- Compositional quivers ----
-------------------------------

-- A compositional quiver is a quiver with an assignment of each pair of
-- edges into and out of a shared vertex -- `x -- e --> y --> e' -- z` --
-- to a single edge following the same path -- `x -- e'' --> z`.

public export
TypeCQuivComp : {v : Type} -> TypeQuivV v -> Type
TypeCQuivComp {v} q = (x, y, z : v) -> q (y, z) -> q (x, y) -> q (x, z)

public export
FinEnrQuivComp : {v : Type} -> FinEnrQuivV v -> Type
FinEnrQuivComp {v} q = TypeCQuivComp {v} (Fin . q)

public export
FinQuivComp : {n : Nat} -> FinQuivN n -> Type
FinQuivComp {n} = FinEnrQuivComp {v=(Fin n)}

-----------------------------------------
-----------------------------------------
---- Universal properties of quivers ----
-----------------------------------------
-----------------------------------------

----------------------------------------------
---- Internal to and enriched over `Type` ----
----------------------------------------------

public export
TypeQuivInit : TypeQuivV Void
TypeQuivInit (v, _) = void v

public export
TypeQuivInitSL : TypeRQuivSL {v=Void} TypeQuivInit
TypeQuivInitSL v = void v

public export
TypeQuivInitComp : TypeCQuivComp {v=Void} TypeQuivInit
TypeQuivInitComp v = void v

public export
TypeQuivTerm : TypeQuivV Unit
TypeQuivTerm ((), ()) = Unit

public export
TypeQuivTermSL : TypeRQuivSL {v=Unit} TypeQuivTerm
TypeQuivTermSL () = ()

public export
TypeQuivTermComp : TypeCQuivComp {v=Unit} TypeQuivTerm
TypeQuivTermComp () () () () () = ()

public export
data TypeQuivCoprodV : {0 v, w : Type} ->
    TypeQuivV v -> TypeQuivV w -> TypeQuivV (Either v w) where
  TQCl : {0 v, w : Type} -> (qv : TypeQuivV v) -> (qw : TypeQuivV w) ->
    (x, y : v) -> qv (x, y) -> TypeQuivCoprodV qv qw (Left x, Left y)
  TQCr : {0 v, w : Type} -> (qv : TypeQuivV v) -> (qw : TypeQuivV w) ->
    (x, y : w) -> qw (x, y) -> TypeQuivCoprodV qv qw (Right x, Right y)

public export
TypeRQuivSLCoprod : {0 v, w : Type} ->
  {qv : TypeQuivV v} -> {qw : TypeQuivV w} ->
  TypeRQuivSL {v} qv -> TypeRQuivSL {v=w} qw ->
  TypeRQuivSL {v=(Either v w)} (TypeQuivCoprodV qv qw)
TypeRQuivSLCoprod {v} {w} {qv} {qw} slv slw evw = case evw of
  Left ev => TQCl {v} {w} qv qw ev ev $ slv ev
  Right ew => TQCr {v} {w} qv qw ew ew $ slw ew

public export
TypeCQuivCompCoprod : {0 v, w : Type} ->
  {qv : TypeQuivV v} -> {qw : TypeQuivV w} ->
  TypeCQuivComp {v} qv -> TypeCQuivComp {v=w} qw ->
  TypeCQuivComp {v=(Either v w)} (TypeQuivCoprodV qv qw)
TypeCQuivCompCoprod {v} {w} {qv} {qw} cv cw (Left ev) (Left ev') (Left ev'')
  (TQCl qv qw ev' ev'' eqv) (TQCl qv qw ev ev' eqv') =
    TQCl {v} {w} qv qw ev ev'' $ cv ev ev' ev'' eqv eqv'
TypeCQuivCompCoprod {v} {w} {qv} {qw} cv cw (Right ew) (Right ew') (Right ew'')
  (TQCr qv qw ew' ew'' eqw) (TQCr qv qw ew ew' eqw') =
    TQCr {v} {w} qv qw ew ew'' $ cw ew ew' ew'' eqw eqw'

----------------------------------------------
----------------------------------------------
---- Categories from quivers, inductively ----
----------------------------------------------
----------------------------------------------

-------------------------------------
-------------------------------------
---- (Co)presheaves from quivers ----
-------------------------------------
-------------------------------------

----------------------------------------------
---- Internal to and enriched over `Type` ----
----------------------------------------------

-- Given a quiver internal to and enriched over `Type`, a vertex
-- object, a slice object over the vertex object, and two vertices,
-- this is the type of the slice between those two vertices of the
-- morphism-map component of a presheaf on a category whose type of
-- objects is the quiver's vertex object and whose object-map component
-- is the given slice object.
public export
TypeQuivPrshfM : {0 v : Type} -> TypeQuivV v -> SliceObj v -> v -> v -> Type
TypeQuivPrshfM {v} q sl dom cod = sl cod -> sl dom

-- Given a quiver internal to and enriched over `Type`, a vertex
-- object, and a slice object over the vertex object, this type
-- generates the morphism-map component of a presheaf on a category
-- whose type of objects is the quiver's vertex object and whose
-- object-map component is the given slice object.
public export
TypeQuivPrshfMmap : {v : Type} -> TypeQuivV v -> SliceObj v -> Type
TypeQuivPrshfMmap {v} q sl =
  (dom, cod : v) -> TypeQuivPrshfM {v} q sl dom cod

-- Given a quiver internal to and enriched over `Type`, a vertex
-- object, a slice object over the vertex object, and two vertices,
-- this is the type of the slice between those two vertices of the
-- morphism-map component of a copresheaf on a category whose type of
-- objects is the quiver's vertex object and whose object-map component
-- is the given slice object.
public export
TypeQuivCoprshfM : {0 v : Type} -> TypeQuivV v -> SliceObj v -> v -> v -> Type
TypeQuivCoprshfM {v} q sl dom cod = sl dom -> sl cod

-- Given a quiver internal to and enriched over `Type`, a vertex
-- object, and a slice object over the vertex object, this type
-- generates the morphism-map component of a copresheaf on a category
-- whose type of objects is the quiver's vertex object and whose
-- object-map component is the given slice object.
public export
TypeQuivCoprshfMmap : {v : Type} -> TypeQuivV v -> SliceObj v -> Type
TypeQuivCoprshfMmap {v} q sl =
  (dom, cod : v) -> TypeQuivCoprshfM {v} q sl dom cod

--------------------------------
---- Enriched over `FinSet` ----
--------------------------------

-- Given a quiver internal to `Type` but enriched over `FinSet`, a vertex
-- object, a slice object over the vertex object, and two vertices,
-- this is the type of the slice between those two vertices of the
-- morphism-map component of a presheaf on a category whose type of
-- objects is the quiver's vertex object and whose object-map component
-- is the given slice object.
public export
FinEnrQuivPrshfM : {0 v : Type} ->
  FinEnrQuivV v -> SliceObj v -> v -> v -> Type
FinEnrQuivPrshfM {v} q sl dom cod = sl cod -> sl dom

-- Given a quiver internal to `Type` but enriched over `FinSet`, a vertex
-- object, and a slice object over the vertex object, this type
-- generates the morphism-map component of a presheaf on a category
-- whose type of objects is the quiver's vertex object and whose
-- object-map component is the given slice object.
public export
FinEnrQuivPrshfMmap : {v : Type} -> FinEnrQuivV v -> SliceObj v -> Type
FinEnrQuivPrshfMmap {v} q sl =
  (dom, cod : v) -> FinEnrQuivPrshfM {v} q sl dom cod

-- Given a quiver internal to `Type` but enriched over `FinSet`, a vertex
-- object, a slice object over the vertex object, and two vertices,
-- this is the type of the slice between those two vertices of the
-- morphism-map component of a copresheaf on a category whose type of
-- objects is the quiver's vertex object and whose object-map component
-- is the given slice object.
public export
FinEnrQuivCoprshfM : {0 v : Type} ->
  FinEnrQuivV v -> SliceObj v -> v -> v -> Type
FinEnrQuivCoprshfM {v} q sl dom cod = sl dom -> sl cod

-- Given a quiver internal to `Type` but enriched over `FinSet`, a vertex
-- object, and a slice object over the vertex object, this type
-- generates the morphism-map component of a copresheaf on a category
-- whose type of objects is the quiver's vertex object and whose
-- object-map component is the given slice object.
public export
FinEnrQuivCoprshfMmap : {v : Type} -> FinEnrQuivV v -> SliceObj v -> Type
FinEnrQuivCoprshfMmap {v} q sl =
  (dom, cod : v) -> FinEnrQuivCoprshfM {v} q sl dom cod

------------------------------------------------
---- Internal to and enriched over `FinSet` ----
------------------------------------------------

-- Given a quiver internal to and enriched over `FinSet`, a vertex
-- object, a slice object over the vertex object, and two vertices,
-- this is the type of the slice between those two vertices of the
-- morphism-map component of a presheaf on a category whose type of
-- objects is the quiver's vertex object and whose object-map component
-- is the given slice object.
public export
FinQuivPrshfM : {0 n : Nat} ->
  FinQuivN n -> SliceObj (Fin n) -> Fin n -> Fin n -> Type
FinQuivPrshfM {n} q sl dom cod = sl cod -> sl dom

-- Given a quiver internal to and enriched over `FinSet`, a vertex
-- object, and a slice object over the vertex object, this type
-- generates the morphism-map component of a presheaf on a category
-- whose type of objects is the quiver's vertex object and whose
-- object-map component is the given slice object.
public export
FinQuivPrshfMmap : {n : Nat} -> FinQuivN n -> SliceObj (Fin n) -> Type
FinQuivPrshfMmap {n} q sl =
  (dom, cod : Fin n) -> FinQuivPrshfM {n} q sl dom cod

-- Given a quiver internal to and enriched over `FinSet`, a vertex
-- object, a slice object over the vertex object, and two vertices,
-- this is the type of the slice between those two vertices of the
-- morphism-map component of a copresheaf on a category whose type of
-- objects is the quiver's vertex object and whose object-map component
-- is the given slice object.
public export
FinQuivCoprshfM : {0 n : Nat} ->
  FinQuivN n -> SliceObj (Fin n) -> Fin n -> Fin n -> Type
FinQuivCoprshfM {n} q sl dom cod = sl dom -> sl cod

-- Given a quiver internal to and enriched over `FinSet`, a vertex
-- object, and a slice object over the vertex object, this type
-- generates the morphism-map component of a copresheaf on a category
-- whose type of objects is the quiver's vertex object and whose
-- object-map component is the given slice object.
public export
FinQuivCoprshfMmap : {n : Nat} -> FinQuivN n -> SliceObj (Fin n) -> Type
FinQuivCoprshfMmap {n} q sl =
  (dom, cod : Fin n) -> FinQuivCoprshfM {n} q sl dom cod

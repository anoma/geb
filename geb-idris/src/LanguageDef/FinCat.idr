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

public export
Functor FinSetObjF where
  map f FSO0 = FSO0
  map f FSO1 = FSO1
  map f (FSOC x y) = FSOC (f x) (f y)

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
Bifunctor FinSetTermF where
  bimap f g FST1 = FST1
  bimap f g (FSTl t r) = FSTl (g t) (f r)
  bimap f g (FSTr l t) = FSTr (f l) (g t)

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
finSetTermEval {obj} var term subst alg (InFree (TFC t)) = alg $
  -- Equivalent to
  --  mapSnd (finSetTermEval {obj} var term subst alg) t
  -- but Idris can't determine that that would be terminating.
  case t of
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
FinSetTermMorphF : (sl : SliceObj FinSetObjTermIdx) ->
  (dep : sl FSOTt -> sl FSOTo) ->
  FinSetObjTermSliceF sl FSOTt -> FinSetObjTermSliceF sl FSOTo
FinSetTermMorphF sl dep FST1 = FSO1
FinSetTermMorphF sl dep (FSTl t r) = FSOC (dep t) r
FinSetTermMorphF sl dep (FSTr l t) = FSOC l (dep t)

public export
FreeFinSetTermDepSubst :
  (sl : SliceObj FinSetObjTermIdx) -> (dep : sl FSOTt -> sl FSOTo) ->
  (i : FinSetObjTermIdx) -> sl i -> FreeFinSetObjTermSlice sl FSOTo
FreeFinSetTermDepSubst sl dep i t = InSlFv $ case i of
  FSOTo => t
  FSOTt => dep t

FinSetObjTermSliceDep :
  (sl : SliceObj FinSetObjTermIdx) -> (i : FinSetObjTermIdx) ->
  FinSetObjTermSliceF (const $ sl FSOTo) i -> FinSetObjTermSliceF sl FSOTo
FinSetObjTermSliceDep sl i t = case i of
  FSOTo => t
  FSOTt => case t of
    FST1 => FSO1
    FSTl l r => FSOC l r
    FSTr l r => FSOC l r

FreeFinSetObjTermSliceDep :
  (sl : SliceObj FinSetObjTermIdx) -> (i : FinSetObjTermIdx) ->
  FinSetObjTermSliceF (const $ FreeFinSetObjTermSlice sl FSOTo) i ->
  FreeFinSetObjTermSlice sl FSOTo
FreeFinSetObjTermSliceDep sl i t =
  InSlFc $ FinSetObjTermSliceDep (FreeFinSetObjTermSlice sl) i t

public export
FreeFinSetTermDep :
  (sl : SliceObj FinSetObjTermIdx) -> (dep : sl FSOTt -> sl FSOTo) ->
  FreeFinSetObjTermSlice sl FSOTt -> FreeFinSetObjTermSlice sl FSOTo
FreeFinSetTermDep sl dep =
  FinSetObjTermSliceEval
    sl
    (const $ FreeFinSetObjTermSlice sl FSOTo)
    (FreeFinSetTermDepSubst sl dep)
    (FreeFinSetObjTermSliceDep sl)
    FSOTt

----------------------------------------
----------------------------------------
---- `FinSet` and its induced topoi ----
----------------------------------------
----------------------------------------

mutual
  public export
  data FinCat : Type where
    FCfs : FinCat -- `FinSet` itself
    FCsl : (fc : FinCat) -> FinSlCat fc -> FinCat -- Slice category

  public export
  data FinObj : FinCat -> Type where
    FOsigma :
      (fc : FinCat) -> (slc : FinSlCat fc) -> FinObj (FCsl fc slc) -> FinObj fc

  -- A slice category.
  public export
  record FinSlCat (fc : FinCat) where
    constructor MkFinSlCat
    fslBase : FinObj fc

  public export
  data FinMorph : (fc : FinCat) -> FinObj fc -> FinObj fc -> Type where

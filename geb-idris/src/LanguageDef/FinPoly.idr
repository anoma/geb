module LanguageDef.FinPoly

import Library.IdrisUtils
import Library.IdrisCategories

%hide Library.IdrisCategories.BaseChangeF

-- The double category of finitary polynomial functors.

-------------------------
-------------------------
---- Natural numbers ----
-------------------------
-------------------------

-- The parallel product of `Maybe` with itself.
public export
MaybeParProdF : Type -> Type
MaybeParProdF a =
  Either
    -- The first position corresponds to `Nothing` on both sides.
    Unit
  $ Either
    -- The second position corresponds to `Just a` on the left and `Nothing`
    -- on the right.  That's the product of one direction with zero, which
    -- is zero directions.
    Unit
  $ Either
    -- The third position corresponds to `Nothing` on the left and `Just a`
    -- on the right.
    Unit
    -- The fourth position corresponds to `Just a` on both sides.  That's
    -- the product of one direction with one, which is one direction.
    a

public export
MaybeParProdMu : Type
MaybeParProdMu = Mu MaybeParProdF

public export
MaybeParProdFM : Type -> Type
MaybeParProdFM = FreeMonad MaybeParProdF

public export
maybeParProdEval : FreeFEval MaybeParProdF
maybeParProdEval v a subst alg (InFree (TFV ev)) =
  subst ev
maybeParProdEval v a subst alg (InFree (TFC (Left ()))) =
  alg $ Left ()
maybeParProdEval v a subst alg (InFree (TFC (Right (Left ())))) =
  alg $ Right $ Left ()
maybeParProdEval v a subst alg (InFree (TFC (Right (Right (Left ()))))) =
  alg $ Right $ Right $ Left ()
maybeParProdEval v a subst alg (InFree (TFC (Right (Right (Right el))))) =
  alg $ Right $ Right $ Right $ maybeParProdEval v a subst alg el

public export
maybeParProdCata : Catamorphism MaybeParProdF
maybeParProdCata a = maybeParProdEval Void a (voidF a)

public export
maybeParProdMuToNatPairPredAlg : Algebra MaybeParProdF Type
maybeParProdMuToNatPairPredAlg (Left ()) = Unit
maybeParProdMuToNatPairPredAlg (Right (Left ())) = Void
maybeParProdMuToNatPairPredAlg (Right (Right (Left ()))) = Unit
maybeParProdMuToNatPairPredAlg (Right (Right (Right prf))) = prf

public export
MaybeParProdMuToNatPairPred : MaybeParProdMu -> Type
MaybeParProdMuToNatPairPred =
  maybeParProdCata Type maybeParProdMuToNatPairPredAlg

public export
MaybeParProdMuToNatPairPredUnique : (el : MaybeParProdMu) ->
  (p, p' : MaybeParProdMuToNatPairPred el) -> p = p'
MaybeParProdMuToNatPairPredUnique (InFree (TFV ev)) p p'
  = void ev
MaybeParProdMuToNatPairPredUnique (InFree (TFC (Left ()))) () ()
  = Refl
MaybeParProdMuToNatPairPredUnique (InFree (TFC (Right (Left ())))) ev ev'
  = void ev
MaybeParProdMuToNatPairPredUnique (InFree (TFC (Right (Right (Left ()))))) () ()
  = Refl
MaybeParProdMuToNatPairPredUnique (InFree (TFC (Right (Right (Right el))))) p p'
  = MaybeParProdMuToNatPairPredUnique el p p'

--------------------------------------------------------------
--------------------------------------------------------------
---- Mutual recursion as polynomial finite-slice functors ----
--------------------------------------------------------------
--------------------------------------------------------------

------------------------
---- Raw operations ----
------------------------

-- We will interpret a raw operation as a functor from a finite-product
-- category of the raw core category to the raw core category.  The number of
-- products is the number of sorts referenced in the operation.  (The
-- operation itself need not specify a sort -- it might be used by any
-- number of definitions of sorts in the theory as a whole.)
--
-- We bootstrap the implementation by first assuming an interpretation of
-- the raw core category into the metalanguage's `Type`, so our initial
-- interpretation of a raw operation will be as a functor of the form
-- `RawCore^N -> RawCore`.
--
-- Because we're modeling a multi-sorted theory, the arity is not just a
-- number; rather, it's a list of sorts.  So the first parameter here is
-- the number of sorts, and the second is the _length_ of the arity.
public export
RawOp : Nat -> Nat -> Type
RawOp s a = Vect a (Fin s)

-- A convenience for writing raw operations without having to
-- use `Fin` explicitly.
public export
rawOpFromListMaybe : {s, a : Nat} -> List Nat -> Maybe (RawOp s a)
rawOpFromListMaybe {s} {a} ns =
  fromListMaybe {a=Nat} {n=a} ns >>=
  (traverse {a=Nat} {b=(Fin s)} {f=Maybe} {t=(Vect a)} $ \n => natToFin n s)

public export
rawOpFromList : {s, a : Nat} ->
  (ns : List Nat) -> {auto 0 _ : ReturnsJust (rawOpFromListMaybe {s} {a}) ns} ->
  RawOp s a
rawOpFromList = MkMaybe rawOpFromListMaybe

-- A mapping of sorts to concrete types.  This is the interpretation (into
-- the metalanguage) of the domain of the interpretation of the raw operation.
public export
SortInterpretation : Nat -> Type
SortInterpretation = flip Vect Type

public export
SortInterpretationSl : Nat -> Type
SortInterpretationSl = SliceObj . Fin

public export
SortInterpretationToSl :
  {n : Nat} -> SortInterpretation n -> SortInterpretationSl n
SortInterpretationToSl {n} = flip $ index {len=n} {elem=Type}

public export
SortInterpretationFromSl :
  {n : Nat} -> SortInterpretationSl n -> SortInterpretation n
SortInterpretationFromSl {n} = finFToVect {n} {a=Type}

public export
SortMorphism : {s : Nat} ->
  SortInterpretation s -> SortInterpretation s -> Type
SortMorphism {s} sl sl' = HVect {n=s} $ map (uncurry HomProf) $ zip sl sl'

public export
SortMorphismToSl : {s : Nat} -> {sl, sl' : SortInterpretation s} ->
  SortMorphism {s} sl sl' ->
  SliceMorphism {a=(Fin s)}
    (SortInterpretationToSl sl) (SortInterpretationToSl sl')
SortMorphismToSl {s=(S s)} {sl=(ty :: tys)} {sl'=(ty' :: tys')}
  (m :: ms) FZ i =
    m i
SortMorphismToSl {s=(S s)} {sl=(ty :: tys)} {sl'=(ty' :: tys')}
  (m :: ms) (FS k) i =
    SortMorphismToSl {s} {sl=tys} {sl'=tys'} ms k i

public export
SortMorphismFromSl : {s : Nat} -> {sl, sl' : SortInterpretation s} ->
  SliceMorphism {a=(Fin s)}
    (SortInterpretationToSl sl) (SortInterpretationToSl sl') ->
  SortMorphism {s} sl sl'
SortMorphismFromSl {s=Z} {sl=[]} {sl'=[]} m = []
SortMorphismFromSl {s=(S s)} {sl=(ty :: tys)} {sl'=(ty' :: tys')} m =
  m FZ :: SortMorphismFromSl {s} {sl=tys} {sl'=tys'} (\i => m $ FS i)

-- Given a mapping of sorts to concrete types, compute the direction-set
-- of the operation.  This is a discrete representation of it, using a
-- vector of types and a vector of types dependent upon them, as opposed
-- to an explicit pi type.
public export
RawOpDir : {s, a : Nat} ->
  (op : RawOp s a) -> SortInterpretation s -> Vect a Type
RawOpDir {s} {a} op sorts = map (flip index sorts) op

-- Given a mapping of sorts to concrete types, compute an interpretation
-- of the raw operation:  that is, the result of applying the functor
-- to an object of the finite product category -- i.e., to a finite list
-- of types -- to obtain an object of `Type`.
--
-- This interpretation is a discrete 'pi' operation.
public export
InterpRawOpProd : {s, a : Nat} ->
  (op : RawOp s a) -> SortInterpretation s -> Type
InterpRawOpProd {s} {a} op sorts =
  HVect {n=a} $ RawOpDir {s} {a} op sorts

public export
InterpRawOpProdSl : {s, a : Nat} ->
  (op : RawOp s a) -> SortInterpretationSl s -> Type
InterpRawOpProdSl {s} {a} op sorts = Pi {a=(Fin a)} (sorts . flip index op)

public export
InterpRawOpProdToSl : {s, a : Nat} ->
  (op : RawOp s a) -> (sorts : SortInterpretation s) ->
  InterpRawOpProd {s} {a} op sorts ->
  InterpRawOpProdSl {s} {a} op (SortInterpretationToSl sorts)
InterpRawOpProdToSl {s} {a} op sorts v i =
  replace {p=id} (mapIndex {f=(flip index sorts)} op i) $ index i v

public export
InterpRawOpProdFromSl : {s, a : Nat} ->
  (op : RawOp s a) -> (sorts : SortInterpretation s) ->
  InterpRawOpProdSl {s} {a} op (SortInterpretationToSl sorts) ->
  InterpRawOpProd {s} {a} op sorts
InterpRawOpProdFromSl {s} {a=Z} [] sorts sl = []
InterpRawOpProdFromSl {s} {a=(S a)} (i :: v) sorts sl =
  sl FZ :: InterpRawOpProdFromSl {s} {a} v sorts (\ty => sl $ FS ty)

-- This interpretation, dual to `InterpRawOpProd`,  is a discrete
-- 'sigma' operation.
public export
InterpRawOpCop : {s, a : Nat} ->
  (op : RawOp s a) -> SortInterpretation s -> Type
InterpRawOpCop {s} {a} op sorts =
  (i : Fin a ** index i $ RawOpDir {s} {a} op sorts)

public export
InterpRawOpCopSl : {s, a : Nat} ->
  (op : RawOp s a) -> SortInterpretationSl s -> Type
InterpRawOpCopSl {s} {a} op sorts = Sigma {a=(Fin a)} (sorts . flip index op)

public export
InterpRawOpCopToSl : {s, a : Nat} ->
  (op : RawOp s a) -> (sorts : SortInterpretation s) ->
  InterpRawOpCop {s} {a} op sorts ->
  InterpRawOpCopSl {s} {a} op (SortInterpretationToSl sorts)
InterpRawOpCopToSl {s} {a} op sorts (i ** ty) =
  (i ** replace {p=id} (mapIndex {f=(flip index sorts)} op i) ty)

public export
InterpRawOpCopFromSl : {s, a : Nat} ->
  (op : RawOp s a) -> (sorts : SortInterpretation s) ->
  InterpRawOpCopSl {s} {a} op (SortInterpretationToSl sorts) ->
  InterpRawOpCop {s} {a} op sorts
InterpRawOpCopFromSl {s} {a} op sorts (i ** ty) =
  (i ** replace {p=id} (sym (mapIndex {f=(flip index sorts)} op i)) ty)

---------------------------
---- Tagged operations ----
---------------------------

public export
data OpTag : Type where
  OP_PI : OpTag
  OP_SIGMA : OpTag

public export
TaggedRawOp : Nat -> Nat -> Type
TaggedRawOp s a = (OpTag, RawOp s a)

public export
InterpTaggedRawOp : {s, a : Nat} ->
  (op : TaggedRawOp s a) -> SortInterpretation s -> Type
InterpTaggedRawOp {s} {a} (OP_PI, op) = InterpRawOpProd {s} {a} op
InterpTaggedRawOp {s} {a} (OP_SIGMA, op) = InterpRawOpCop {s} {a} op

public export
taggedRawOpFromListMaybe : {s, a : Nat} ->
  OpTag -> List Nat -> Maybe (TaggedRawOp s a)
taggedRawOpFromListMaybe {s} {a} tag ns =
  rawOpFromListMaybe {s} {a} ns >>= pure . MkPair tag

public export
taggedRawOpFromList : {s, a : Nat} ->
  (tag : OpTag) -> (ns : List Nat) ->
  {auto 0 j :
    ReturnsJust (uncurry $ taggedRawOpFromListMaybe {s} {a}) (tag, ns)} ->
  TaggedRawOp s a
taggedRawOpFromList {s} {a} tag ns =
  MkMaybe (uncurry $ taggedRawOpFromListMaybe {s} {a}) (tag, ns)

public export
InterpTaggedRawOpSl : {s, a : Nat} ->
  (op : TaggedRawOp s a) -> SortInterpretationSl s -> Type
InterpTaggedRawOpSl {s} {a} (OP_PI, op) = InterpRawOpProdSl {s} {a} op
InterpTaggedRawOpSl {s} {a} (OP_SIGMA, op) = InterpRawOpCopSl {s} {a} op

public export
InterpTaggedRawOpToSl : {s, a : Nat} ->
  (op : TaggedRawOp s a) -> (sorts : SortInterpretation s) ->
  InterpTaggedRawOp {s} {a} op sorts ->
  InterpTaggedRawOpSl {s} {a} op (SortInterpretationToSl sorts)
InterpTaggedRawOpToSl {s} {a} (OP_PI, v) sorts t =
  InterpRawOpProdToSl {s} {a} v sorts t
InterpTaggedRawOpToSl {s} {a} (OP_SIGMA, v) sorts t =
  InterpRawOpCopToSl {s} {a} v sorts t

public export
InterpTaggedRawOpFromSl : {s, a : Nat} ->
  (op : TaggedRawOp s a) -> (sorts : SortInterpretation s) ->
  InterpTaggedRawOpSl {s} {a} op (SortInterpretationToSl sorts) ->
  InterpTaggedRawOp {s} {a} op sorts
InterpTaggedRawOpFromSl {s} {a} (OP_PI, v) sorts t =
  InterpRawOpProdFromSl {s} {a} v sorts t
InterpTaggedRawOpFromSl {s} {a} (OP_SIGMA, v) sorts t =
  InterpRawOpCopFromSl {s} {a} v sorts t

-------------------------
---- Operation lists ----
-------------------------

public export
TaggedRawOpDP : Nat -> Type
TaggedRawOpDP = DPair Nat . TaggedRawOp

public export
taggedRawOpDPFromListMaybe : {s : Nat} ->
  OpTag -> List Nat -> Maybe (TaggedRawOpDP s)
taggedRawOpDPFromListMaybe {s} tag ns =
  map {f=Maybe} (MkDPair (length ns)) $
  taggedRawOpFromListMaybe {s} {a=(length ns)} tag ns

public export
taggedRawOpDPFromList : {s : Nat} ->
  (tag : OpTag) -> (ns : List Nat) ->
  {auto 0 j :
    ReturnsJust (uncurry $ taggedRawOpDPFromListMaybe {s}) (tag, ns)} ->
  TaggedRawOpDP s
taggedRawOpDPFromList {s} tag ns {j} =
  MkMaybe (uncurry $ taggedRawOpDPFromListMaybe {s}) (tag, ns) {j}

public export
InterpTaggedRawOpDP : {s : Nat} ->
  (op : TaggedRawOpDP s) -> SortInterpretation s -> Type
InterpTaggedRawOpDP {s} op = InterpTaggedRawOp {s} {a=(fst op)} (snd op)

public export
InterpTaggedRawOpDPSl : {s : Nat} ->
  (op : TaggedRawOpDP s) -> SortInterpretationSl s -> Type
InterpTaggedRawOpDPSl {s} op = InterpTaggedRawOpSl {s} {a=(fst op)} (snd op)

public export
InterpTaggedRawOpDPToSl : {s : Nat} ->
  (op : TaggedRawOpDP s) -> (sorts : SortInterpretation s) ->
  InterpTaggedRawOpDP op sorts ->
  InterpTaggedRawOpDPSl op (SortInterpretationToSl sorts)
InterpTaggedRawOpDPToSl {s} (ar ** op) sorts t =
  InterpTaggedRawOpToSl {a=ar} op sorts t

public export
InterpTaggedRawOpDPFromSl : {s : Nat} ->
  (op : TaggedRawOpDP s) -> (sorts : SortInterpretation s) ->
  InterpTaggedRawOpDPSl op (SortInterpretationToSl sorts) ->
  InterpTaggedRawOpDP op sorts
InterpTaggedRawOpDPFromSl {s} (ar ** op) sorts t =
  InterpTaggedRawOpFromSl {a=ar} op sorts t

-- `n` tagged operations with sorts drawn from `Fin s`.
public export
RawOpList : Nat -> Nat -> Type
RawOpList s n = Vect n (TaggedRawOpDP s)

public export
rawOpListFromListMaybe : {s, n : Nat} ->
  List (OpTag, List Nat) -> Maybe (RawOpList s n)
rawOpListFromListMaybe {s} {n} ops =
  fromListMaybe {a=(OpTag, List Nat)} {n} ops >>=
  (traverse {a=(OpTag, List Nat)} {b=(TaggedRawOpDP s)} {f=Maybe} {t=(Vect n)} $
   uncurry $ taggedRawOpDPFromListMaybe {s})

public export
rawOpListFromList : {s, n : Nat} ->
  (ops : List (OpTag, List Nat)) ->
  {auto 0 _ : ReturnsJust (rawOpListFromListMaybe {s} {n}) ops} ->
  RawOpList s n
rawOpListFromList = MkMaybe rawOpListFromListMaybe

public export
InterpRawOpListSl : {s, n : Nat} -> RawOpList s n ->
  SliceFunctor (Fin s) (Fin n)
InterpRawOpListSl {s} {n} ops sorts i =
  InterpTaggedRawOpDPSl {s} (index i ops) sorts

public export
RawEndoOpList : Nat -> Type
RawEndoOpList s = RawOpList s s

public export
InterpRawEndoOpListSl : {s : Nat} -> RawEndoOpList s ->
  SliceFunctor (Fin s) (Fin s)
InterpRawEndoOpListSl {s} = InterpRawOpListSl {s} {n=s}

public export
InterpRawOpList : {s, n : Nat} -> RawOpList s n ->
  SortInterpretation s -> SortInterpretation n
InterpRawOpList {s} {n} ops sorts =
  SortInterpretationFromSl
  $ InterpRawOpListSl {s} {n} ops
  $ SortInterpretationToSl sorts

public export
InterpRawOpListToSl : {s, n : Nat} -> (ops : RawOpList s n) ->
  (sorts : SortInterpretation s) ->
  SliceMorphism {a=(Fin n)}
    (SortInterpretationToSl (InterpRawOpList {s} {n} ops sorts))
    (InterpRawOpListSl {s} {n} ops (SortInterpretationToSl sorts))
InterpRawOpListToSl {s} {n} ops sorts i op =
  rewrite sym
    (finFToVectIdx
      (InterpRawOpListSl {s} {n} ops $ SortInterpretationToSl sorts) i) in
  op

public export
InterpRawOpListFromSl : {s, n : Nat} -> (ops : RawOpList s n) ->
  (sorts : SortInterpretation s) ->
  SliceMorphism {a=(Fin n)}
    (InterpRawOpListSl {s} {n} ops (SortInterpretationToSl sorts))
    (SortInterpretationToSl (InterpRawOpList {s} {n} ops sorts))
InterpRawOpListFromSl {s} {n} ops sorts i op =
  rewrite
    (finFToVectIdx
      (InterpRawOpListSl {s} {n} ops $ SortInterpretationToSl sorts) i) in
  op

public export
InterpRawEndoOpList : {s : Nat} -> RawEndoOpList s ->
  SortInterpretation s -> SortInterpretation s
InterpRawEndoOpList {s} = InterpRawOpList {s} {n=s}

public export
FreeTheorySl : {s : Nat} -> (ops : RawEndoOpList s) ->
  SliceFunctor (Fin s) (Fin s)
FreeTheorySl {s} = SliceFreeM . InterpRawEndoOpListSl {s}

public export
FreeTheory : {s : Nat} -> (ops : RawEndoOpList s) ->
  SortInterpretation s -> SortInterpretation s
FreeTheory {s} ops sorts =
  SortInterpretationFromSl
  $ FreeTheorySl {s} ops
  $ SortInterpretationToSl sorts

public export
FreeTheorySlEq : {s : Nat} -> (ops : RawEndoOpList s) ->
  (sl : SortInterpretation s) -> (i : Fin s) ->
  index i (FreeTheory {s} ops sl) =
    FreeTheorySl ops (SortInterpretationToSl sl) i
FreeTheorySlEq {s} ops sl i =
  finFToVectIdx (FreeTheorySl {s} ops $ SortInterpretationToSl sl) i

public export
InitialTheorySl : {s : Nat} -> (ops : RawEndoOpList s) -> SliceObj (Fin s)
InitialTheorySl {s} = SliceMu . InterpRawEndoOpListSl {s}

public export
CofreeTheorySl : {s : Nat} -> (ops : RawEndoOpList s) ->
  SliceFunctor (Fin s) (Fin s)
CofreeTheorySl {s} = SliceCofreeCM . InterpRawEndoOpListSl {s}

public export
CofreeTheory : {s : Nat} -> (ops : RawEndoOpList s) ->
  SortInterpretation s -> SortInterpretation s
CofreeTheory {s} ops sorts =
  SortInterpretationFromSl
  $ CofreeTheorySl {s} ops
  $ SortInterpretationToSl sorts

public export
CofreeTheorySlEq : {s : Nat} -> (ops : RawEndoOpList s) ->
  (sl : SortInterpretation s) -> (i : Fin s) ->
  index i (CofreeTheory {s} ops sl) =
    CofreeTheorySl ops (SortInterpretationToSl sl) i
CofreeTheorySlEq {s} ops sl i =
  finFToVectIdx (CofreeTheorySl {s} ops $ SortInterpretationToSl sl) i

public export
TerminalTheorySl : {s : Nat} -> (ops : RawEndoOpList s) -> SliceObj (Fin s)
TerminalTheorySl {s} = SliceNu . InterpRawEndoOpListSl {s}

mutual
  public export
  evalTheorySl : {s : Nat} -> (ops : RawEndoOpList s) ->
    SliceFreeFEval (InterpRawEndoOpListSl {s} ops)
  evalTheorySl {s} ops sv sa subst alg i (InSlF i t) =
    case t of
      InSlV vt => subst i vt
      InSlC ct => evalTheoryFSl {s} ops sv sa subst alg i ct

  public export
  evalTheoryFSl : {s : Nat} -> (ops : RawEndoOpList s) ->
    SliceFreeFEvalF (InterpRawEndoOpListSl {s} ops)
  evalTheoryFSl {s} ops sv sa subst alg i ct with (index i ops) proof opeq
    evalTheoryFSl {s} ops sv sa subst alg i ct | (ar ** (OP_PI, op)) =
      alg i $ rewrite opeq in
      \ty => evalTheorySl {s} ops sv sa subst alg (index ty op) (ct ty)
    evalTheoryFSl {s} ops sv sa subst alg i (ty ** t) | (ar ** (OP_SIGMA, op)) =
      alg i $ rewrite opeq in
      (ty ** evalTheorySl {s} ops sv sa subst alg (index ty op) t)

public export
evalTheory : {s : Nat} -> (ops : RawEndoOpList s) ->
  (sv, sa : SortInterpretation s) ->
  SortMorphism {s} sv sa ->
  SliceAlg (InterpRawEndoOpListSl {s} ops) (SortInterpretationToSl sa) ->
  SortMorphism {s} (FreeTheory ops sv) sa
evalTheory {s} ops sv sa subst alg =
  SortMorphismFromSl {s} {sl=(FreeTheory ops sv)} {sl'=sa} $
  \i, x =>
    evalTheorySl {s} ops
      (SortInterpretationToSl sv)
      (SortInterpretationToSl sa)
      (SortMorphismToSl subst)
      alg
      i
      (rewrite sym (FreeTheorySlEq {s} ops sv i) in x)

mutual
  public export
  traceTheorySl : {s : Nat} -> (ops : RawEndoOpList s) ->
    SliceCofreeFTrace (InterpRawEndoOpListSl {s} ops)
  traceTheorySl {s} ops sl sa label coalg i esa =
    InSlCF i $ InSlS (label i esa) $
      traceTheoryFSl {s} ops sl sa label coalg i esa

  public export
  traceTheoryFSl : {s : Nat} -> (ops : RawEndoOpList s) ->
    SliceCofreeFTraceF (InterpRawEndoOpListSl {s} ops)
  traceTheoryFSl {s} ops sl sa label coalg i esa =
    traceOpSl {s} ops sl sa label coalg i (coalg i esa)

  public export
  traceOpSl : {s : Nat} -> (ops : RawEndoOpList s) ->
    (sl, sa : SliceObj (Fin s)) -> SliceMorphism {a=(Fin s)} sa sl ->
    SliceCoalg (InterpRawEndoOpListSl {s} ops) sa ->
    (i : Fin s) -> InterpTaggedRawOpSl (snd (index i ops)) sa ->
    InterpTaggedRawOpSl (snd (index i ops)) (CofreeTheorySl {s} ops sl)
  traceOpSl {s} ops sl sa label coalg i t with (index i ops)
    traceOpSl {s} ops sl sa label coalg i t | (ar ** (OP_PI, op)) =
      \ty => traceTheorySl {s} ops sl sa label coalg (index ty op) $ t ty
    traceOpSl {s} ops sl sa label coalg i (ty ** t) | (ar ** (OP_SIGMA, op)) =
      (ty ** traceTheorySl {s} ops sl sa label coalg (index ty op) t)

public export
traceTheory : {s : Nat} -> (ops : RawEndoOpList s) ->
  (sl, sa : SortInterpretation s) -> SortMorphism {s} sa sl ->
  SliceCoalg (InterpRawEndoOpListSl {s} ops) (SortInterpretationToSl sa) ->
  SortMorphism {s} sa (CofreeTheory {s} ops sl)
traceTheory {s} ops sl sa label coalg =
  SortMorphismFromSl {s} {sl=sa} {sl'=(CofreeTheory ops sl)} $
  \i, x =>
    rewrite CofreeTheorySlEq {s} ops sl i in
    traceTheorySl {s} ops
      (SortInterpretationToSl sl)
      (SortInterpretationToSl sa)
      (SortMorphismToSl label)
      coalg
      i
      x

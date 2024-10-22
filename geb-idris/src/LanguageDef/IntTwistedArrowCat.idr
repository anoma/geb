module LanguageDef.IntTwistedArrowCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.InternalProfunctor

---------------------------------------------------------
---------------------------------------------------------
---- Polynomial functors on twisted-arrow categories ----
---------------------------------------------------------
---------------------------------------------------------

public export
PolyTwistF : Type
PolyTwistF =
  (polyPos : Type **
   contraPos : SliceObj polyPos **
   contraDir : Pi {a=polyPos} (SliceObj . contraPos) **
   covarPos : Pi {a=polyPos} (SliceObj . contraPos) **
   {- covarDir : -} (i : polyPos) -> (j : contraPos i) -> contraDir i j ->
    SliceObj (covarPos i j))

public export
ptwPolyPos : PolyTwistF -> Type
ptwPolyPos = DPair.fst

public export
ptwContraPos : (p : PolyTwistF) -> SliceObj (ptwPolyPos p)
ptwContraPos p = DPair.fst $ DPair.snd p

public export
ptwContraDir : (p : PolyTwistF) ->
  Pi {a=ptwPolyPos p} (SliceObj . ptwContraPos p)
ptwContraDir p = DPair.fst $ DPair.snd $ DPair.snd p

public export
ptwCovarPos : (p : PolyTwistF) ->
  Pi {a=ptwPolyPos p} (SliceObj . ptwContraPos p)
ptwCovarPos p = DPair.fst $ DPair.snd $ DPair.snd $ DPair.snd p

public export
ptwCovarDir : (p : PolyTwistF) ->
  (i : ptwPolyPos p) -> (j : ptwContraPos p i) -> ptwContraDir p i j ->
  SliceObj (ptwCovarPos p i j)
ptwCovarDir p = DPair.snd $ DPair.snd $ DPair.snd $ DPair.snd p

public export
ptwAssign : (p : PolyTwistF) ->
  (i : ptwPolyPos p) -> (j : ptwContraPos p i) ->
  (dcontra : ptwContraDir p i j) -> (k : ptwCovarPos p i j) ->
  ptwCovarDir p i j dcontra k -> ptwContraDir p i j
ptwAssign p i j dcontra k dcovar = dcontra

public export
InterpPTw : PolyTwistF -> TwArrCoprSig
InterpPTw p x y mxy =
  (i : ptwPolyPos p **
   (j : ptwContraPos p i) -> (ptwContraDir p i j -> x) -> ptwCovarPos p i j)

public export
iptwPos : {p : PolyTwistF} -> {x, y : Type} -> {mxy : x -> y} ->
  InterpPTw p x y mxy -> ptwPolyPos p
iptwPos {p} {x} {y} {mxy} el = DPair.fst el

public export
iptwProj1 : {p : PolyTwistF} -> {x, y : Type} -> {mxy : x -> y} ->
  (el : InterpPTw p x y mxy) ->
  (j : ptwContraPos p $ iptwPos {p} {x} {y} {mxy} el) ->
  (ptwContraDir p (iptwPos {p} {x} {y} {mxy} el) j -> x) ->
  ptwCovarPos p (iptwPos {p} {x} {y} {mxy} el) j
iptwProj1 {p} {x} {y} {mxy} el = DPair.snd el

public export
iptwProj2 : {p : PolyTwistF} -> {x, y : Type} -> {mxy : x -> y} ->
  (el : InterpPTw p x y mxy) ->
  (j : ptwContraPos p $ iptwPos {p} {x} {y} {mxy} el) ->
  (dmx : ptwContraDir p (iptwPos {p} {x} {y} {mxy} el) j -> x) ->
  (dcontra : ptwContraDir p (iptwPos {p} {x} {y} {mxy} el) j) ->
  ptwCovarDir p
    (iptwPos {p} {x} {y} {mxy} el)
    j
    dcontra
    (iptwProj1 {p} {x} {y} {mxy} el j dmx) ->
  y
iptwProj2 {p} {x} {y} {mxy} el j dmx dcontra =
    (mxy
     . dmx
     . ptwAssign p
      (iptwPos {p} {x} {y} {mxy} el)
      j
      dcontra
      (iptwProj1 {p} {x} {y} {mxy} el j dmx))

public export
iptwComm : {p : PolyTwistF} -> {x, y : Type} -> {mxy : x -> y} ->
  (el : InterpPTw p x y mxy) ->
  (j : ptwContraPos p $ iptwPos {p} {x} {y} {mxy} el) ->
  (dmx : ptwContraDir p (iptwPos {p} {x} {y} {mxy} el) j -> x) ->
  (dcontra : ptwContraDir p (iptwPos {p} {x} {y} {mxy} el) j) ->
  (mxy
   . dmx
   . ptwAssign p
    (iptwPos {p} {x} {y} {mxy} el)
    j
    dcontra
    (iptwProj1 {p} {x} {y} {mxy} el j dmx)) =
  (iptwProj2 {p} {x} {y} {mxy} el j dmx dcontra)
iptwComm {p} {x} {y} {mxy} el j dmx dcontra = Refl

----------------------------------------------
----------------------------------------------
---- Twisted-arrow commutativity property ----
----------------------------------------------
----------------------------------------------

-- The property that the diYoneda embedding of the endpoints of a pair
-- of arrows forms a commutative diagram.  Note the direction of the
-- arrows -- the `i` arrows go from `0` to `1`, whereas the `j` arrows
-- go from `1` to `0`.
public export
IntDiYoCommutes : {c : Type} -> {mor : IntDifunctorSig c} ->
  (comp : IntCompSig c mor) -> (eq : IntEqSig {c} mor) ->
  (i0, i1 : c) -> mor i0 i1 ->
  (j0, j1 : c) -> mor j1 j0 ->
  IntDiYonedaEmbedObj c mor i0 i1 j0 j1 ->
  Type
IntDiYoCommutes {c} {mor} comp eq i0 i1 mi0i1 j0 j1 mj1j0 e =
  eq i0 i1
    mi0i1
    (comp i0 j0 i1
      (intDiYoEmbedRL {mor} e)
    $ comp i0 j1 j0
      mj1j0
      (intDiYoEmbedLR {mor} e))

------------------------------------------
------------------------------------------
---- Twisted-arrow diYoneda embedding ----
------------------------------------------
------------------------------------------

-- We can extend the diYoneda embedding to pairs of twisted arrows by using the
-- commutativity condition.  This is the object component of the embedding.
-- We shall see from the morphism component below that it is an embedding
-- of `(TwArr(c), op(TwArr(op(c))))` into `Type`.  As such, it can be curried
-- from either side, like the Yoneda embedding, to be viewed equivalently as
-- either:
--
--  - An embedding of `TwArr(c)` into the category of presheaves on
--    `TwArr(op(c))`
--  - An embedding of `op(TwArr(op(c)))` into the category of copresheaves on
--    `TwArr(c)`
--
-- Thus it strongly resembles the Yoneda embedding of `TwArr(c)`, which
-- may be viewed as either an embedding of `TwArr(c)` into the category
-- of presheaves on `TwArr(c)` or an embedding of `op(TwArr(c))` into the
-- category of copresheaves on `TwArr(c)`.  The difference is the diYoneda
-- embedding's extra `op` inside the `TwArr`.

IntTwArrDiYoEmbedObj : {c : Type} -> {mor : IntDifunctorSig c} ->
  (comp : IntCompSig c mor) -> (eq : IntEqSig {c} mor) ->
  (i0, i1 : c) -> mor i0 i1 ->
  (j0, j1 : c) -> mor j1 j0 ->
  Type
IntTwArrDiYoEmbedObj {c} {mor} comp eq i0 i1 mi0i1 j0 j1 mj1j0 =
  Subset0
    (IntDiYonedaEmbedObj c mor i0 i1 j0 j1)
    (IntDiYoCommutes comp eq i0 i1 mi0i1 j0 j1 mj1j0)

public export
intTwArrDiYoE : {c : Type} -> {mor : IntDifunctorSig c} ->
  {comp : IntCompSig c mor} -> {eq : IntEqSig {c} mor} ->
  {i0, i1 : c} -> {mi0i1 : mor i0 i1} ->
  {j0, j1 : c} -> {mj1j0 : mor j1 j0} ->
  (e : IntTwArrDiYoEmbedObj {c} {mor} comp eq i0 i1 mi0i1 j0 j1 mj1j0) ->
  IntDiYonedaEmbedObj c mor i0 i1 j0 j1
intTwArrDiYoE {c} {mor} {comp} {eq} {i0} {i1} {mi0i1} {j0} {j1} {mj1j0} = fst0

public export
intTwArrDiYoRL : {c : Type} -> {mor : IntDifunctorSig c} ->
  {comp : IntCompSig c mor} -> {eq : IntEqSig {c} mor} ->
  {i0, i1 : c} -> {mi0i1 : mor i0 i1} ->
  {j0, j1 : c} -> {mj1j0 : mor j1 j0} ->
  IntTwArrDiYoEmbedObj {c} {mor} comp eq i0 i1 mi0i1 j0 j1 mj1j0 ->
  mor j0 i1
intTwArrDiYoRL {mor} e = intDiYoEmbedRL {mor} (intTwArrDiYoE e)

public export
intTwArrDiYoLR : {c : Type} -> {mor : IntDifunctorSig c} ->
  {comp : IntCompSig c mor} -> {eq : IntEqSig {c} mor} ->
  {i0, i1 : c} -> {mi0i1 : mor i0 i1} ->
  {j0, j1 : c} -> {mj1j0 : mor j1 j0} ->
  IntTwArrDiYoEmbedObj {c} {mor} comp eq i0 i1 mi0i1 j0 j1 mj1j0 ->
  mor i0 j1
intTwArrDiYoLR {mor} e = intDiYoEmbedLR {mor} (intTwArrDiYoE e)

public export
0 intTwArrDiYoComm : {c : Type} -> {mor : IntDifunctorSig c} ->
  {comp : IntCompSig c mor} -> {eq : IntEqSig {c} mor} ->
  {i0, i1 : c} -> {mi0i1 : mor i0 i1} ->
  {j0, j1 : c} -> {mj1j0 : mor j1 j0} ->
  (e : IntTwArrDiYoEmbedObj {c} {mor} comp eq i0 i1 mi0i1 j0 j1 mj1j0) ->
  IntDiYoCommutes {c} {mor} comp eq i0 i1 mi0i1 j0 j1 mj1j0
    (intTwArrDiYoE {c} {mor} {comp} {eq} {i0} {i1} {mi0i1} {j0} {j1} {mj1j0} e)
intTwArrDiYoComm = snd0

-- This is the `IntDiYonedaEmbedObj` component (that is, without the
-- commutativity condition) of the right side of the morphism component
-- of the embedding whose object component is
-- `IntTwArrDiYoEmbedObj {c} {mor} comp eq`.
public export
IntTwArrDiYoEmbedRmapBase : {c : Type} -> {mor : IntDifunctorSig c} ->
  (comp : IntCompSig c mor) ->
  (i0, i1 : c) -> {j0, j1 : c} -> {j0', j1' : c} ->
  -- The morphism components (that is, without the commutativity condition)
  -- of a twisted-arrow morphism from `mj1j0` to `mj1'j0'`.
  -- Alternatively, if we view `mj1j0` and `mj1'j0'` as morphisms
  -- of `op(c)`, then this becomes a morphism of `op(Tw(op(c)))`.
  (mj1j1' : mor j1 j1') -> (mj0'j0 : mor j0' j0) ->
  IntDiYonedaEmbedObj c mor i0 i1 j0 j1 ->
  IntDiYonedaEmbedObj c mor i0 i1 j0' j1'
IntTwArrDiYoEmbedRmapBase {c} {mor} comp
  i0 i1 {j0} {j1} {j0'} {j1'} =
    flip $ IntDiYonedaEmbedDimap c mor comp i0 i1 j0 j1 j0' j1'

-- This is the commutativity condition of the right side of the morphism
-- component of the embedding whose object component is
-- `IntTwArrDiYoEmbedObj {c} {mor} comp eq`.
public export
0 IntTwArrDiYoEmbedRmapCommutes : {c : Type} -> {mor : IntDifunctorSig c} ->
  {comp : IntCompSig c mor} -> {eq : IntEqSig {c} mor} ->
  (eqsym : IntEqSymSig {c} {mor} eq) ->
  (eqtrans : IntEqTransSig {c} {mor} eq) ->
  (eqcongl : IntEqCongLSig {c} {mor} comp eq) ->
  (eqcongr : IntEqCongRSig {c} {mor} comp eq) ->
  (eqassoc : IntEqAssocSig {c} {mor} comp eq) ->
  {i0, i1 : c} -> {mi0i1 : mor i0 i1} ->
  {j0, j1 : c} -> {mj1j0 : mor j1 j0} ->
  {j0', j1' : c} -> {mj1'j0' : mor j1' j0'} ->
  (mj1j1' : mor j1 j1') ->
  (mj0'j0 : mor j0' j0) ->
  eq j1 j0
    mj1j0
    (comp j1 j0' j0
      mj0'j0
    $ comp j1 j1' j0'
      mj1'j0'
      mj1j1') ->
  (e : IntDiYonedaEmbedObj c mor i0 i1 j0 j1) ->
  IntDiYoCommutes {c} {mor} comp eq i0 i1 mi0i1 j0 j1 mj1j0 e ->
  IntDiYoCommutes {c} {mor} comp eq i0 i1 mi0i1 j0' j1' mj1'j0'
    (IntTwArrDiYoEmbedRmapBase {c} {mor} comp
      i0 i1 {j0} {j1} {j0'} {j1'} mj1j1' mj0'j0 e)
IntTwArrDiYoEmbedRmapCommutes {c} {mor} {comp} {eq}
  eqsym eqtrans eqcongl eqcongr eqassoc
  {i0} {i1} {mi0i1} {j0} {j1} {mj1j0} {j0'} {j1'} {mj1'j0'}
  mj1j1' mj0'j0 mcomm e@(_, _) ecomm =
    eqtrans i0 i1
      mi0i1
      (comp i0 j0 i1
        (intDiYoEmbedRL {mor} e)
       $ comp i0 j1 j0
         mj1j0
         (intDiYoEmbedLR {mor} e))
      (comp i0 j0' i1
        (comp j0' j0 i1
          (intDiYoEmbedRL {mor} e)
          mj0'j0)
        (comp i0 j1' j0'
          mj1'j0'
         $ comp i0 j1 j1'
          mj1j1'
          (intDiYoEmbedLR {mor} e)))
      (eqtrans
        i0
        i1
        _
        _
        _
        (eqsym i0 i1 _ _
          $ eqassoc i0 j0' j0 i1
            (intDiYoEmbedRL {mor} e)
            mj0'j0
          (comp i0 j1' j0'
              mj1'j0'
            $ comp i0 j1 j1'
              mj1j1'
              (intDiYoEmbedLR {mor} e)))
        (eqcongr i0 j0 i1 _ _ _
         $ eqtrans _ _ _ _ _
          (eqtrans _ _ _ _ _
            (eqcongr _ _ _ _ _ mj0'j0
             $ eqassoc _ _ _ _ mj1'j0' mj1j1' (intDiYoEmbedLR {mor} e))
            (eqassoc _ _ _ _
              mj0'j0 (comp _ _ _ mj1'j0' mj1j1') (intDiYoEmbedLR {mor} e)))
          (eqcongl _ _ _ mj1j0
            (comp _ _ _ mj0'j0 $ comp _ _ _ mj1'j0' mj1j1')
            (intDiYoEmbedLR {mor} e) mcomm)))
      ecomm

-- This is the right side of the morphism component of the embedding whose
-- object component is `IntTwArrDiYoEmbedObj {c} {mor} comp eq`.
public export
IntTwArrDiYoEmbedRmap : {c : Type} -> {mor : IntDifunctorSig c} ->
  {comp : IntCompSig c mor} -> {eq : IntEqSig {c} mor} ->
  IntEqSymSig {c} {mor} eq ->
  IntEqTransSig {c} {mor} eq ->
  IntEqCongLSig {c} {mor} comp eq ->
  IntEqCongRSig {c} {mor} comp eq ->
  IntEqAssocSig {c} {mor} comp eq ->
  {i0, i1 : c} -> {mi0i1 : mor i0 i1} ->
  {j0, j1 : c} -> {mj1j0 : mor j1 j0} ->
  {j0', j1' : c} -> {mj1'j0' : mor j1' j0'} ->
  -- A twisted-arrow morphism from `mj1'j0'` to `mj1j0`.
  -- If we view `mj1j0` and `mj1'j0'` as morphisms of `op(c)`, then this
  -- is a morphism of `op(Tw(op(c)))`, from `(j0, j1, mj1j0)` to
  -- `(j0', j1', mj1'j0')`.
  (mj1j1' : mor j1 j1') ->
  (mj0'j0 : mor j0' j0) ->
  eq j1 j0
    mj1j0
    (comp j1 j0' j0
      mj0'j0
    $ comp j1 j1' j0'
      mj1'j0'
      mj1j1') ->
  -- A morphism of embeddings in `Type`.
  IntTwArrDiYoEmbedObj {c} {mor} comp eq i0 i1 mi0i1 j0 j1 mj1j0 ->
  IntTwArrDiYoEmbedObj {c} {mor} comp eq i0 i1 mi0i1 j0' j1' mj1'j0'
IntTwArrDiYoEmbedRmap {c} {mor} {comp} {eq}
  eqsym eqtrans eqcongl eqcongr eqassoc
  {i0} {i1} {mi0i1} {j0} {j1} {mj1j0} {j0'} {j1'} {mj1'j0'}
  mj1j1' mj0'j0 comm e =
    Element0
      (IntTwArrDiYoEmbedRmapBase {c} {mor} comp
        i0 i1 {j0} {j1} {j0'} {j1'} mj1j1' mj0'j0
        (intTwArrDiYoE e))
      (IntTwArrDiYoEmbedRmapCommutes {c} {mor} {comp} {eq}
        eqsym eqtrans eqcongl eqcongr eqassoc
        {mi0i1} {mj1j0} {mj1'j0'}
        mj1j1' mj0'j0 comm (intTwArrDiYoE e) (intTwArrDiYoComm e))

-- This is the `IntDiYonedaEmbedObj` component (that is, without the
-- commutativity condition) of the left side of the morphism component
-- of the embedding whose object component is
-- `IntTwArrDiYoEmbedObj {c} {mor} comp eq`.
public export
IntTwArrDiYoEmbedLmapBase : {c : Type} -> {mor : IntDifunctorSig c} ->
  (comp : IntCompSig c mor) ->
  {i0, i1 : c} -> (j0, j1 : c) -> {i0', i1' : c} ->
  -- The morphism components (that is, without the commutativity condition)
  -- of a twisted-arrow morphism from `mi0i1` to `mi0'i1'`.
  (mi0'i0 : mor i0' i0) -> (mi1i1' : mor i1 i1') ->
  IntDiYonedaEmbedObj c mor i0 i1 j0 j1 ->
  IntDiYonedaEmbedObj c mor i0' i1' j0 j1
IntTwArrDiYoEmbedLmapBase {c} {mor} comp
  {i0} {i1} j0 j1 {i0'} {i1'} mi0'i0 mi1i1' e =
    (comp j0 i1 i1' mi1i1' (intDiYoEmbedRL {mor} e),
     comp i0' i0 j1 (intDiYoEmbedLR {mor} e) mi0'i0)

-- This is the commutativity condition of the left side of the morphism
-- component of the embedding whose object component is
-- `IntTwArrDiYoEmbedObj {c} {mor} comp eq`.
public export
0 IntTwArrDiYoEmbedLmapCommutes : {c : Type} -> {mor : IntDifunctorSig c} ->
  {comp : IntCompSig c mor} -> {eq : IntEqSig {c} mor} ->
  (eqsym : IntEqSymSig {c} {mor} eq) ->
  (eqtrans : IntEqTransSig {c} {mor} eq) ->
  (eqcongl : IntEqCongLSig {c} {mor} comp eq) ->
  (eqcongr : IntEqCongRSig {c} {mor} comp eq) ->
  (eqassoc : IntEqAssocSig {c} {mor} comp eq) ->
  {i0, i1 : c} -> {mi0i1 : mor i0 i1} ->
  {i0', i1' : c} -> {mi0'i1' : mor i0' i1'} ->
  {j0, j1 : c} -> {mj1j0 : mor j1 j0} ->
  (mi0'i0 : mor i0' i0) -> (mi1i1' : mor i1 i1') ->
  eq i0' i1'
    mi0'i1'
    (comp i0' i1 i1'
      mi1i1'
    $ comp i0' i0 i1
      mi0i1
      mi0'i0) ->
  (e : IntDiYonedaEmbedObj c mor i0 i1 j0 j1) ->
  IntDiYoCommutes {c} {mor} comp eq i0 i1 mi0i1 j0 j1 mj1j0 e ->
  IntDiYoCommutes {c} {mor} comp eq i0' i1' mi0'i1' j0 j1 mj1j0
    (IntTwArrDiYoEmbedLmapBase {c} {mor} comp
      {i0} {i1} j0 j1 {i0'} {i1'} mi0'i0 mi1i1' e)
IntTwArrDiYoEmbedLmapCommutes {c} {mor} {comp} {eq}
  eqsym eqtrans eqcongl eqcongr eqassoc
  {i0} {i1} {mi0i1} {i0'} {i1'} {mi0'i1'} {j0} {j1} {mj1j0} mi0'i0 mi1i1'
  mcomm e@(_, _) ecomm =
    eqtrans _ _ _ _ _
      (eqtrans _ _ _ _ _
        (eqsym _ _ _ _ $ eqassoc _ _ _ _ _ _ _)
        (eqcongr _ _ _ _ _ _
        $ eqtrans _ _
          _
          _
          _
          (eqtrans _ _ _ _ _
            (eqcongr _ _ _ _ _ _
             $ eqassoc _ _ _ _ _ _ _)
            (eqassoc _ _ _ _
              _ (comp _ _ _ _ _) _))
          (eqcongl _ _ _ _ _ _ ecomm))
      )
      mcomm

-- This is the left side of the morphism component of the embedding whose
-- object component is `IntTwArrDiYoEmbedObj {c} {mor} comp eq`.
public export
0 IntTwArrDiYoEmbedLmap : {c : Type} -> {mor : IntDifunctorSig c} ->
  {comp : IntCompSig c mor} -> {eq : IntEqSig {c} mor} ->
  (eqsym : IntEqSymSig {c} {mor} eq) ->
  (eqtrans : IntEqTransSig {c} {mor} eq) ->
  (eqcongl : IntEqCongLSig {c} {mor} comp eq) ->
  (eqcongr : IntEqCongRSig {c} {mor} comp eq) ->
  (eqassoc : IntEqAssocSig {c} {mor} comp eq) ->
  {i0, i1 : c} -> {mi0i1 : mor i0 i1} ->
  {i0', i1' : c} -> {mi0'i1' : mor i0' i1'} ->
  {j0, j1 : c} -> {mj1j0 : mor j1 j0} ->
  -- A twisted-arrow morphism from `mi0i1` to `mi0'i1'`.
  (mi0'i0 : mor i0' i0) -> (mi1i1' : mor i1 i1') ->
  (comm : eq i0' i1'
    mi0'i1'
    (comp i0' i1 i1'
      mi1i1'
    $ comp i0' i0 i1
      mi0i1
      mi0'i0)) ->
  -- A morphism of embeddings in `Type`.
  IntTwArrDiYoEmbedObj {c} {mor} comp eq i0 i1 mi0i1 j0 j1 mj1j0 ->
  IntTwArrDiYoEmbedObj {c} {mor} comp eq i0' i1' mi0'i1' j0 j1 mj1j0
IntTwArrDiYoEmbedLmap {c} {mor} {comp} {eq}
  eqsym eqtrans eqcongl eqcongr eqassoc
  {i0} {i1} {mi0i1} {i0'} {i1'} {mi0'i1'} {j0} {j1} {mj1j0} mi0'i0 mi1i1'
  comm e =
    Element0
      (IntTwArrDiYoEmbedLmapBase {c} {mor} comp
        {i0} {i1} j0 j1 {i0'} {i1'} mi0'i0 mi1i1'
        (intTwArrDiYoE e))
      (IntTwArrDiYoEmbedLmapCommutes {c} {mor} {comp} {eq}
        eqsym eqtrans eqcongl eqcongr eqassoc
        {mi0i1} {mi0'i1'} {mj1j0}
        mi0'i0 mi1i1' comm (intTwArrDiYoE e) (intTwArrDiYoComm e))

-------------------------------------------------
-------------------------------------------------
---- Extended ("twisted") diYoneda embedding ----
-------------------------------------------------
-------------------------------------------------

-- The object-map component of the object-map component of the
-- "twisted diYoneda embedding", an embedding of `(op(c), c)` into
-- `IntDifunctorSig c/IntEndoProfNTSig c`.
public export
IntTwDiYoEmbedObj : {c : Type} ->
  (mor : IntDifunctorSig c) -> c -> c -> IntDifunctorSig c
IntTwDiYoEmbedObj {c} mor i0 i1 j0 j1 =
  (IntDiYonedaEmbedObj c mor i0 i1 j0 j1, mor i0 i1)

public export
tdyeL : {c : Type} -> {mor : IntDifunctorSig c} -> {i0, i1, j0, j1 : c} ->
  IntTwDiYoEmbedObj {c} mor i0 i1 j0 j1 -> mor j0 i1
tdyeL {c} {mor} {i0} {i1} {j0} {j1} = Builtin.fst . Builtin.fst

public export
tdyeR : {c : Type} -> {mor : IntDifunctorSig c} -> {i0, i1, j0, j1 : c} ->
  IntTwDiYoEmbedObj {c} mor i0 i1 j0 j1 -> mor i0 j1
tdyeR {c} {mor} {i0} {i1} {j0} {j1} = Builtin.snd . Builtin.fst

public export
tdyeRepAsn : {c : Type} -> {mor : IntDifunctorSig c} -> {i0, i1, j0, j1 : c} ->
  IntTwDiYoEmbedObj {c} mor i0 i1 j0 j1 -> mor i0 i1
tdyeRepAsn {c} {mor} {i0} {i1} {j0} {j1} = Builtin.snd

public export
0 TdyeEmbCond : {c : Type} -> {mor : IntDifunctorSig c} ->
  (comp : IntCompSig c mor) -> (eq : IntEqSig {c} mor) ->
  {i0, i1, j0, j1 : c} ->
  IntTwDiYoEmbedObj {c} mor i0 i1 j0 j1 -> mor j1 j0 -> Type
TdyeEmbCond {c} {mor} comp eq {i0} {i1} {j0} {j1} e easn =
  eq i0 i1
    (tdyeRepAsn {mor} e)
    (comp i0 j0 i1 (tdyeL {mor} e) (comp i0 j1 j0 easn (tdyeR {mor} e)))

-- The morphism-map components of the object-map component of the
-- twisted diYoneda embedding.

public export
IntTwDiYoEmbedLmap : {c : Type} -> {mor : IntDifunctorSig c} ->
  (comp : IntCompSig c mor) ->
  (s, t : c) -> IntEndoLmapSig c mor (IntTwDiYoEmbedObj {c} mor s t)
IntTwDiYoEmbedLmap {c} {mor} comp s t a b i cmia e =
  ((comp i a t (tdyeL {mor} e) cmia, tdyeR {mor} e), tdyeRepAsn {mor} e)

public export
IntTwDiYoEmbedRmap : {c : Type} -> {mor : IntDifunctorSig c} ->
  (comp : IntCompSig c mor) ->
  (s, t : c) -> IntEndoRmapSig c mor (IntTwDiYoEmbedObj {c} mor s t)
IntTwDiYoEmbedRmap {c} {mor} comp s t a b i cmbi e =
  ((tdyeL {mor} e, comp s b i cmbi (tdyeR {mor} e)), tdyeRepAsn {mor} e)

public export
IntTwDiYoEmbedDimap : {c : Type} -> {mor : IntDifunctorSig c} ->
  (comp : IntCompSig c mor) ->
  (s, t : c) -> IntEndoDimapSig c mor (IntTwDiYoEmbedObj {c} mor s t)
IntTwDiYoEmbedDimap {c} {mor} comp s t =
  IntEndoDimapFromLRmaps c mor (IntTwDiYoEmbedObj {c} mor s t)
    (IntTwDiYoEmbedLmap {c} {mor} comp s t)
    (IntTwDiYoEmbedRmap {c} {mor} comp s t)

-- The morphism-map components of the twisted diYoneda embedding itself.
-- This shows that the twisted diYoneda embedding is itself a difunctor,
-- enriched over `IntDifunctorSig c/IntEndoProfNTSig c`.  Put another
-- way, it is an embedding of `(op(c), c)` into
-- `IntDifunctorSig c/IntEndoProfNTSig c`.  As such, it has the same type
-- signature as the Yoneda embedding of `(op(c), c)` into its category
-- of copresheaves (copresheaves on `(op(c), c)` are precisely endoprofunctors
-- on `c`), but it differs from the Yoneda embedding in two respects:
--
-- 1) While it has a hom-functor component, that component is neither
--    the covariant nor the contravariant hom-functor on `(op(c), c)`, but
--    a twisted version -- the diYoneda embedding.
-- 2) It also includes a component which constitutes a morphism between
--    the two components of the objects of `(op(c), c)`.  In particular
--    one of the effects of this is that for any `i0, i1` where there _is_
--    no morphism from `i0` to `i1`, the difunctor embedding of `(i0, i1)`
--    is the constant `Void` (initial object).

public export
IntTwDiYoEmbedMorL : {c : Type} -> {mor : IntDifunctorSig c} ->
  (comp : IntCompSig c mor) ->
  (s, t, a : c) -> mor a s ->
  IntEndoProfNTSig c
    (IntTwDiYoEmbedObj {c} mor s t)
    (IntTwDiYoEmbedObj {c} mor a t)
IntTwDiYoEmbedMorL {c} {mor} comp s t a mas x y e =
  ((tdyeL {mor} e,
    comp a s y (tdyeR {mor} e) mas),
   comp a s t (tdyeRepAsn {mor} e) mas)

public export
IntTwDiYoEmbedMorR : {c : Type} -> {mor : IntDifunctorSig c} ->
  (comp : IntCompSig c mor) ->
  (s, t, b : c) -> mor t b ->
  IntEndoProfNTSig c
    (IntTwDiYoEmbedObj {c} mor s t)
    (IntTwDiYoEmbedObj {c} mor s b)
IntTwDiYoEmbedMorR {c} {mor} comp s t b mtb x y e =
  ((comp x t b mtb (tdyeL {mor} e),
    tdyeR {mor} e),
   comp s t b mtb (tdyeRepAsn {mor} e))

public export
IntTwDiYoEmbedMor : {c : Type} -> {mor : IntDifunctorSig c} ->
  (comp : IntCompSig c mor) ->
  (s, t, a, b : c) -> mor a s -> mor t b ->
  IntEndoProfNTSig c
    (IntTwDiYoEmbedObj {c} mor s t)
    (IntTwDiYoEmbedObj {c} mor a b)
IntTwDiYoEmbedMor {c} {mor} comp s t a b mas mtb x y =
  IntTwDiYoEmbedMorL {c} {mor} comp s b a mas x y
  . IntTwDiYoEmbedMorR {c} {mor} comp s t b mtb x y

public export
0 IntTwDiYoEmbedMorIsNatural : {c : Type} -> {mor : IntDifunctorSig c} ->
  {comp : IntCompSig c mor} -> (assoc : IntAssocSig c mor comp) ->
  (s, t, a, b : c) -> (mas : mor a s) -> (mtb : mor t b) ->
  IntProfNTNaturality c c mor mor
    (IntTwDiYoEmbedObj {c} mor s t)
    (IntTwDiYoEmbedObj {c} mor a b)
    (IntTwDiYoEmbedDimap {c} {mor} comp s t)
    (IntTwDiYoEmbedDimap {c} {mor} comp a b)
    (IntTwDiYoEmbedMor {c} {mor} comp s t a b mas mtb)
IntTwDiYoEmbedMorIsNatural {c} {mor} {comp} assoc s t a b mas mtb w x y z
  myw mxz ((mwt, msx), mst) =
    pairEqCong
      (pairEqCong
        (assoc y w t b mtb mwt myw)
        (sym $ assoc a s x z mxz msx mas))
      Refl

public export
IntTwDiYonedaLemmaNT : {c : Type} -> (mor, p : IntDifunctorSig c) ->
  IntDifunctorSig c
IntTwDiYonedaLemmaNT {c} mor p i j =
  IntEndoProfNTSig c (IntTwDiYoEmbedObj {c} mor j i) p

public export
0 IntTwDiYonedaLemmaNTDimap : (0 c : Type) ->
  (0 mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (0 p : IntDifunctorSig c) ->
  IntEndoDimapSig c mor (IntTwDiYonedaLemmaNT {c} mor p)
IntTwDiYonedaLemmaNTDimap c mor comp p s t a b mas mtb embed i j e =
  embed i j
    ((comp i a s mas (tdyeL {mor} e),
      comp t b j (tdyeR {mor} e) mtb),
     comp t a s mas $ comp t b a (tdyeRepAsn {mor} e) mtb)

public export
0 IntTwDiYonedaLemmaL : (0 c : Type) -> (0 mor : IntDifunctorSig c) ->
  (0 p : IntDifunctorSig c) -> (pdm : IntEndoDimapSig c mor p) ->
  IntEndoProfNTSig c p (IntTwDiYonedaLemmaNT {c} mor p)
IntTwDiYonedaLemmaL c mor p pdm i j pij x y e =
  pdm i j x y (tdyeL {mor} e) (tdyeR {mor} e) pij

module LanguageDef.DiPolyFunc

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.InternalProfunctor
import public LanguageDef.SlicePolyCat
import public LanguageDef.PolyDifunc

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

------------------------------------------------------
------------------------------------------------------
---- Dipolynomial functors: objects and morphisms ----
------------------------------------------------------
------------------------------------------------------

-- A dipolynomial functor is a coproduct of direpresentables -- that is,
-- diYoneda-embedded objects of `opProd(c)` for some category `c`.  It
-- is determined by the same data as a polynomial endo-profunctor, but
-- interpreted differently -- in other words, the category of dipolynomial
-- functors has the same objects as the category of polynomial endo-profunctors,
-- but has different morphisms.  (This resembles the way in which polynomial
-- and Dirichlet functors are determined by the same arenas but have different
-- morphisms and interpretations as functors.)

public export
PolyDiSig : (c : Type) -> Type
PolyDiSig = IntEndoProAr

public export
pdPos : {c : Type} -> PolyDiSig c -> Type
pdPos {c} = ipaPos {c}

public export
pdDirL : {c : Type} -> (pd : PolyDiSig c) -> pdPos {c} pd -> c
pdDirL {c} = ipaCovar {c}

public export
pdDirR : {c : Type} -> (pd : PolyDiSig c) -> pdPos {c} pd -> c
pdDirR {c} = ipaContra {c}

public export
RepPolyDi : {c : Type} -> (x, y : c) -> PolyDiSig c
RepPolyDi {c} x y = (Unit ** (\_ => x, \_ => y))

public export
InterpPolyDi : {c : Type} -> (mor : IntDifunctorSig c) -> PolyDiSig c ->
  IntDifunctorSig c
InterpPolyDi {c} mor p a b =
  (i : pdPos p ** IntDiYonedaEmbedObj c mor (pdDirR p i) (pdDirL p i) a b)

public export
InterpPolyDiDiag : {c : Type} -> (mor : IntDifunctorSig c) -> PolyDiSig c ->
  c -> Type
InterpPolyDiDiag {c} mor p a = InterpPolyDi {c} mor p a a

public export
ipdPos : {c : Type} -> {mor : IntDifunctorSig c} -> {p : PolyDiSig c} ->
  {x, y : c} -> InterpPolyDi {c} mor p x y -> pdPos p
ipdPos {c} {mor} {p} = DPair.fst

public export
ipdDirL : {c : Type} -> {mor : IntDifunctorSig c} -> {p : PolyDiSig c} ->
  {x, y : c} -> (ipd : InterpPolyDi {c} mor p x y) ->
  mor x (pdDirL p $ ipdPos {c} {mor} {p} {x} {y} ipd)
ipdDirL {c} {mor} {p} ipd = Builtin.fst (DPair.snd ipd)

public export
ipdDirR : {c : Type} -> {mor : IntDifunctorSig c} -> {p : PolyDiSig c} ->
  {x, y : c} -> (ipd : InterpPolyDi {c} mor p x y) ->
  mor (pdDirR p $ ipdPos {c} {mor} {p} {x} {y} ipd) y
ipdDirR {c} {mor} {p} ipd = Builtin.snd (DPair.snd ipd)

public export
InterpPolyLmap : {c : Type} -> {mor : IntDifunctorSig c} ->
  IntCompSig c mor ->
  (p : PolyDiSig c) -> IntEndoLmapSig c mor (InterpPolyDi {c} mor p)
InterpPolyLmap {c} {mor} comp p s t a mas =
  dpMapSnd $ \pi => mapFst (flip (comp a s (pdDirL p pi)) mas)

public export
InterpPolyRmap : {c : Type} -> {mor : IntDifunctorSig c} ->
  IntCompSig c mor ->
  (p : PolyDiSig c) -> IntEndoRmapSig c mor (InterpPolyDi {c} mor p)
InterpPolyRmap {c} {mor} comp p s t b mtb =
  dpMapSnd $ \pi => mapSnd (comp (pdDirR p pi) t b mtb)

public export
InterpPolyDimap : {c : Type} -> {mor : IntDifunctorSig c} ->
  IntCompSig c mor ->
  (p : PolyDiSig c) -> IntEndoDimapSig c mor (InterpPolyDi {c} mor p)
InterpPolyDimap {c} {mor} comp p =
  IntEndoDimapFromLRmaps c mor (InterpPolyDi {c} mor p)
    (InterpPolyLmap {c} {mor} comp p) (InterpPolyRmap {c} {mor} comp p)

------------------------------------------------
---- Polynomial paranatural transformations ----
------------------------------------------------

public export
PPNTonPos : {c : Type} -> {mor : IntDifunctorSig c} ->
  (p, q : PolyDiSig c) -> Type
PPNTonPos {c} {mor} p q =
  (pi : pdPos p) -> mor (pdDirR p pi) (pdDirL p pi) -> pdPos q

public export
PPNTonL : {c : Type} -> {mor : IntDifunctorSig c} ->
  (p, q : PolyDiSig c) -> PPNTonPos {c} {mor} p q -> Type
PPNTonL {c} {mor} p q onpos =
  (pi : pdPos p) -> (asn : mor (pdDirR p pi) (pdDirL p pi)) ->
  mor (pdDirL p pi) (pdDirL q (onpos pi asn))

public export
PPNTonR : {c : Type} -> {mor : IntDifunctorSig c} ->
  (p, q : PolyDiSig c) -> PPNTonPos {c} {mor} p q -> Type
PPNTonR {c} {mor} p q onpos =
  (pi : pdPos p) -> (asn : mor (pdDirR p pi) (pdDirL p pi)) ->
  mor (pdDirR q (onpos pi asn)) (pdDirR p pi)

public export
PolyParaNT : {c : Type} -> (mor : IntDifunctorSig c) -> IntMorSig (PolyDiSig c)
PolyParaNT {c} mor p q =
  (onpos : (pi : pdPos p) -> (mor (pdDirR p pi) (pdDirL p pi)) -> pdPos q **
   ((pi : pdPos p) -> (asn : mor (pdDirR p pi) (pdDirL p pi)) ->
      mor (pdDirL p pi) (pdDirL q (onpos pi asn)),
    (pi : pdPos p) -> (asn : mor (pdDirR p pi) (pdDirL p pi)) ->
      mor (pdDirR q (onpos pi asn)) (pdDirR p pi)))

public export
ppntOnPos : {c : Type} -> {mor : IntDifunctorSig c} -> {p, q : PolyDiSig c} ->
  PolyParaNT {c} mor p q -> PPNTonPos {c} {mor} p q
ppntOnPos {c} {mor} {p} {q} = DPair.fst

public export
ppntOnL : {c : Type} -> {mor : IntDifunctorSig c} -> {p, q : PolyDiSig c} ->
  (nt : PolyParaNT {c} mor p q) ->
  PPNTonL {c} {mor} p q (ppntOnPos {c} {mor} {p} {q} nt)
ppntOnL {c} {mor} {p} {q} nt = Builtin.fst $ DPair.snd nt

public export
ppntOnR : {c : Type} -> {mor : IntDifunctorSig c} -> {p, q : PolyDiSig c} ->
  (nt : PolyParaNT {c} mor p q) ->
  PPNTonR {c} {mor} p q (ppntOnPos {c} {mor} {p} {q} nt)
ppntOnR {c} {mor} {p} {q} nt = Builtin.snd $ DPair.snd nt

public export
InterpPolyParaNT :
  {c : Type} -> {mor : IntDifunctorSig c} -> (comp : IntCompSig c mor) ->
  {p, q : PolyDiSig c} ->
  PolyParaNT {c} mor p q ->
  IntDiNTSig c (InterpPolyDi {c} mor p) (InterpPolyDi {c} mor q)
InterpPolyParaNT {c} {mor} comp {p} {q} nt x ipd =
  let
    pasn :
      mor
        (pdDirR p (ipdPos {c} {mor} {p} ipd))
        (pdDirL p (ipdPos {c} {mor} {p} ipd)) =
      comp (fst (p .snd) (ipd .fst)) x (snd (p .snd) (ipd .fst))
        (ipdDirL {c} {mor} {p} ipd)
        (ipdDirR {c} {mor} {p} ipd)
  in
  (ppntOnPos {mor} {p} {q} nt (ipdPos {mor} ipd) pasn **
   (comp
      x
      (pdDirL p (ipdPos {mor} ipd))
      (pdDirL q (ppntOnPos {mor} {p} {q} nt (ipdPos {mor} ipd) pasn))
      (ppntOnL {mor} {p} {q} nt (ipdPos {mor} ipd) pasn)
      (ipdDirL {mor} ipd),
    comp
      (pdDirR q (ppntOnPos {mor} {p} {q} nt (ipdPos {mor} ipd) pasn))
      (pdDirR p (ipdPos {mor} ipd))
      x
      (ipdDirR {mor} ipd)
      (ppntOnR {mor} {p} {q} nt (ipdPos {mor} ipd) pasn)))

-------------------------------
-------------------------------
---- Paranaturality proofs ----
-------------------------------
-------------------------------

public export
0 PolyParaNTisParanatural :
  {c : Type} -> {mor : IntDifunctorSig c} -> (comp : IntCompSig c mor) ->
  (assoc : IntAssocSig c mor comp) ->
  {p, q : PolyDiSig c} ->
  (nt : PolyParaNT {c} mor p q) ->
  IntParaNTCond c mor
    (InterpPolyDi {c} mor p) (InterpPolyDi {c} mor q)
    (InterpPolyLmap {c} {mor} comp p) (InterpPolyRmap {c} {mor} comp p)
    (InterpPolyLmap {c} {mor} comp q) (InterpPolyRmap {c} {mor} comp q)
    (InterpPolyParaNT {c} {mor} comp {p} {q} nt)
PolyParaNTisParanatural {c} {mor} comp assoc
  {p=(ppos ** (pdirL, pdirR))} {q=(qpos ** (qdirL, qdirR))}
  (onpos ** (onL, onR)) i0 i1 i2
  (pi0 ** (mi0pr, mpli0)) (pi1 ** (mi1pr, mpli1)) cond =
    case dpeq1 cond of
      Refl => case (fstEq $ dpeq2 cond) of
        Refl => case (sndEq $ dpeq2 cond) of
          Refl =>
            rewrite assoc _ _ _ _ mi1pr i2 mpli0 in
            dpEq12
              Refl
            $ pairEqCong
              (rewrite assoc _ _ _ _
                (onL pi0
                  (comp (pdirL pi0) i1 (pdirR pi0) mi1pr (comp (pdirL pi0)
                    i0 i1 i2 mpli0)))
                mi1pr
                i2
               in Refl)
              (rewrite assoc _ _ _ _
                i2
                mpli0
                (onR pi0
                  (comp (pdirL pi0) i1 (pdirR pi0) mi1pr (comp (pdirL pi0)
                    i0 i1 i2 mpli0)))
               in Refl)

-----------------------------------------
-----------------------------------------
---- Categories of diagonal elements ----
-----------------------------------------
-----------------------------------------

-- We define the category of diagonal elements as in "Paranatural Category
-- Theory" by Neumann; it corresponds precisely to what is referred to as the
-- "D is the one-object category" case of the definition of an algebra for a
-- profunctor at
-- https://ncatlab.org/nlab/show/algebra+for+a+profunctor#definition .

public export
PolyDiagElemObj : {c : Type} -> (mor : IntDifunctorSig c) ->
  PolyDiSig c -> Type
PolyDiagElemObj {c} mor p = (x : c ** InterpPolyDiDiag {c} mor p x)

public export
pdeObj : {c : Type} -> {mor : IntDifunctorSig c} ->
  {p : PolyDiSig c} -> PolyDiagElemObj {c} mor p -> c
pdeObj {c} {mor} {p} = DPair.fst

public export
pdeEl : {c : Type} -> {mor : IntDifunctorSig c} ->
  {p : PolyDiSig c} -> (el : PolyDiagElemObj {c} mor p) ->
  InterpPolyDiDiag {c} mor p (pdeObj {c} {mor} {p} el)
pdeEl {c} {mor} {p} = DPair.snd

public export
data PolyDiagElemMor :
    {c : Type} -> {mor : IntDifunctorSig c} -> {comp : IntCompSig c mor} ->
    {p : PolyDiSig c} -> IntMorSig (PolyDiagElemObj {c} mor p) where
  PDEM :
    -- `pos`, `dirR`, and `dirL` together form a `PolyDiSig c`.
    {pos : Type} -> {dirL : pos -> c} -> {dirR : pos -> c} ->
    -- `mxy` is the morphism of the underlying category (`c`) which
    -- underlies the morphism of the category of elements.
    {x, y : c} -> (mxy : mor x y) ->
    -- `i`, `mR`, and `mL` together comprise a term of
    -- `InterpPolyDi c mor (pos ** (dirL, dirR)) y x`; `y` and
    -- `mcontra` together comprise an object of the slice category of
    -- `contra i`; `x` and `mcovar` together comprise an object of the coslice
    -- category of `covar i`.
    (mi : pos) -> (mR : mor (dirR mi) x) -> (mL : mor y (dirL mi)) ->
    PolyDiagElemMor {c} {mor} {comp} {p=(pos ** (dirR, dirL))}
      (x ** mi ** (comp x y (dirL mi) mL mxy, mR))
      (y ** mi ** (mL, comp (dirR mi) x y mxy mR))

public export
pdeMor :
  {c : Type} -> {mor : IntDifunctorSig c} -> {comp : IntCompSig c mor} ->
  {p : PolyDiSig c} -> {x, y : PolyDiagElemObj {c} mor p} ->
  PolyDiagElemMor {c} {mor} {comp} {p} x y ->
  mor (pdeObj {mor} {p} x) (pdeObj {mor} {p} y)
pdeMor {c} {mor} (PDEM mxy mi mR mL) = mxy

public export
pdeCrossEl :
  {c : Type} -> {mor : IntDifunctorSig c} -> {comp : IntCompSig c mor} ->
  {p : PolyDiSig c} -> {x, y : PolyDiagElemObj {c} mor p} ->
  PolyDiagElemMor {c} {mor} {comp} {p} x y ->
  InterpPolyDi {c} mor p (pdeObj {mor} {p} y) (pdeObj {mor} {p} x)
pdeCrossEl {c} {mor} (PDEM mxy mi mR mL) = (mi ** (mL, mR))

-- Here we show the equivalence of our definition of `PolyDiagElemMor`
-- with the standard definition in terms of lmap/rmap equality.

public export
0 PolyDiagElemMorToCommutingEl :
  {c : Type} -> {mor : IntDifunctorSig c} -> {comp : IntCompSig c mor} ->
  {p : PolyDiSig c} ->
  (x, y : PolyDiagElemObj {c} mor p) ->
  PolyDiagElemMor {c} {mor} {comp} {p} x y ->
  (mxy : mor (pdeObj {mor} {p} x) (pdeObj {mor} {p} y) **
   InterpPolyLmap {c} {mor} comp p
    (pdeObj {mor} {p} y) (pdeObj {mor} {p} y) (pdeObj {mor} {p} x)
    mxy (pdeEl {mor} {p} y) =
   InterpPolyRmap {c} {mor} comp p
    (pdeObj {mor} {p} x) (pdeObj {mor} {p} x) (pdeObj {mor} {p} y)
    mxy (pdeEl {mor} {p} x))
PolyDiagElemMorToCommutingEl {c} {mor} {comp} {p=(pos ** (pdirL, pdirR))}
  (x ** (_ ** (_, _))) (y ** (_ ** (_, _))) (PDEM mxy mi mR mL) =
    (mxy ** Refl)

public export
0 PolyDiagElemMorFromCommutingEl :
  {c : Type} -> {mor : IntDifunctorSig c} -> {comp : IntCompSig c mor} ->
  {p : PolyDiSig c} ->
  (x, y : PolyDiagElemObj {c} mor p) ->
  (mxy : mor (pdeObj {mor} {p} x) (pdeObj {mor} {p} y) **
   InterpPolyLmap {c} {mor} comp p
    (pdeObj {mor} {p} y) (pdeObj {mor} {p} y) (pdeObj {mor} {p} x)
    mxy (pdeEl {mor} {p} y) =
   InterpPolyRmap {c} {mor} comp p
    (pdeObj {mor} {p} x) (pdeObj {mor} {p} x) (pdeObj {mor} {p} y)
    mxy (pdeEl {mor} {p} x)) ->
  PolyDiagElemMor {c} {mor} {comp} {p} x y
PolyDiagElemMorFromCommutingEl {c} {mor} {comp} {p=(pos ** (pdirL, pdirR))}
  (x ** (xi ** (_, xL))) (y ** (_ ** (yR, _))) (mxy ** Refl) =
    PDEM mxy xi xL yR

public export
0 PolyDiagElemMorCommutingElIdL :
  {c : Type} -> {mor : IntDifunctorSig c} -> {comp : IntCompSig c mor} ->
  {p : PolyDiSig c} ->
  (x, y : PolyDiagElemObj {c} mor p) ->
  (elmor : (mxy : mor (pdeObj {mor} {p} x) (pdeObj {mor} {p} y) **
   InterpPolyLmap {c} {mor} comp p
    (pdeObj {mor} {p} y) (pdeObj {mor} {p} y) (pdeObj {mor} {p} x)
    mxy (pdeEl {mor} {p} y) =
   InterpPolyRmap {c} {mor} comp p
    (pdeObj {mor} {p} x) (pdeObj {mor} {p} x) (pdeObj {mor} {p} y)
    mxy (pdeEl {mor} {p} x))) ->
  PolyDiagElemMorToCommutingEl {c} {mor} {comp} {p} x y
    (PolyDiagElemMorFromCommutingEl {c} {mor} {comp} {p} x y elmor) = elmor
PolyDiagElemMorCommutingElIdL {c} {mor} {comp} {p=(pos ** (pdirL, pdirR))}
  (x ** (xi ** (_, xL))) (y ** (_ ** (yR, _))) (mxy ** Refl) =
    Refl

public export
0 PolyDiagElemMorCommutingElIdR :
  {c : Type} -> {mor : IntDifunctorSig c} -> {comp : IntCompSig c mor} ->
  {p : PolyDiSig c} ->
  (x, y : PolyDiagElemObj {c} mor p) ->
  (elmor : PolyDiagElemMor {c} {mor} {comp} {p} x y) ->
  PolyDiagElemMorFromCommutingEl {c} {mor} {comp} {p} x y
    (PolyDiagElemMorToCommutingEl {c} {mor} {comp} {p} x y elmor) = elmor
PolyDiagElemMorCommutingElIdR {c} {mor} {comp} {p=(pos ** (pdirL, pdirR))}
  (x ** (_ ** (_, _))) (y ** (_ ** (_, _))) (PDEM mxy mi mR mL) =
    Refl

-- Here we show that a paranatural transformation induces a functor
-- between categories of diagonal elements which commutes with the
-- projections (meaning, the induced functor is the identity on objects
-- and morphisms, and transforms the associated elements functorially).

public export
PolyParaToCatElemObjMap :
  {c : Type} -> {mor : IntDifunctorSig c} -> {comp : IntCompSig c mor} ->
  {p, q : PolyDiSig c} -> PolyParaNT {c} mor p q ->
  PolyDiagElemObj {c} mor p -> PolyDiagElemObj {c} mor q
PolyParaToCatElemObjMap {c} {mor} {comp}
  {p=(ppos ** (pdirR, pdirL))} {q=(qpos ** (qdirR, qdirL))}
  (onpos ** (onL, onR)) (x ** pi ** (pdmR, pdmL)) =
    let asn = comp (pdirR pi) x (pdirL pi) pdmR pdmL in
    (x **
     onpos pi asn **
     (comp x (pdirL pi) (qdirL (onpos pi asn)) (onL pi asn) pdmR,
      comp (qdirR (onpos pi asn)) (pdirR pi) x pdmL (onR pi asn)))

public export
PolyParaToCatElemFMap :
  {c : Type} -> {mor : IntDifunctorSig c} -> {comp : IntCompSig c mor} ->
  {assoc : IntAssocSig c mor comp} ->
  {p, q : PolyDiSig c} -> (gamma : PolyParaNT {c} mor p q) ->
  (x, y : PolyDiagElemObj {c} mor p) ->
  PolyDiagElemMor {c} {mor} {comp} {p} x y ->
  PolyDiagElemMor {c} {mor} {comp} {p=q}
    (PolyParaToCatElemObjMap {c} {mor} {comp} {p} {q} gamma x)
    (PolyParaToCatElemObjMap {c} {mor} {comp} {p} {q} gamma y)
PolyParaToCatElemFMap {c} {mor} {comp} {assoc}
  {p=(_ ** (_, _))} {q=(qpos ** (qdirR, qdirL))}
  (onpos ** (onL, onR))
  (x ** _ ** (_, _)) (y ** _ ** (_, _))
  (PDEM {c} {mor} {comp} {pos} {x} {y} {dirL} {dirR} mxy mi mR mL) =
   rewrite assoc _ _ _ _ mL mxy mR in
   rewrite sym $ assoc _ _ _ _
    (onL mi $ comp (dirR mi) y (dirL mi) mL (comp (dirR mi) x y mxy mR))
    mL
    mxy
   in
   rewrite assoc _ _ _ _
    mxy
    mR
    (onR mi $ comp (dirR mi) y (dirL mi) mL (comp (dirR mi) x y mxy mR))
   in
   PDEM {c} {mor} {comp} {pos=qpos} {dirL=qdirL} {dirR=qdirR}
    mxy
    (onpos mi $ comp (dirR mi) y (dirL mi) mL (comp (dirR mi) x y mxy mR))
    (comp
      (qdirR (onpos mi $
        comp (dirR mi) y (dirL mi) mL (comp (dirR mi) x y mxy mR)))
      (dirR mi)
      x
      mR
      (onR mi $ comp (dirR mi) y (dirL mi) mL (comp (dirR mi) x y mxy mR)))
    (comp
      y
      (dirL mi)
      (qdirL (onpos mi $
        comp (dirR mi) y (dirL mi) mL (comp (dirR mi) x y mxy mR)))
      (onL mi $ comp (dirR mi) y (dirL mi) mL (comp (dirR mi) x y mxy mR))
      mL)

-----------------------------------------------
-----------------------------------------------
---- Categorical structure of paranaturals ----
-----------------------------------------------
-----------------------------------------------

public export
polyParaNTid :
  {c : Type} -> {mor : IntDifunctorSig c} -> {cid : IntIdSig c mor} ->
  (p : PolyDiSig c) -> PolyParaNT {c} mor p p
polyParaNTid {c} {mor} {cid} p =
  (\pi, asn => pi **
   (\pi, asn => cid (pdDirL p pi),
    \pi, asn => cid (pdDirR p pi)))

public export
polyParaNTvcomp :
  {c : Type} -> {mor : IntDifunctorSig c} -> {comp : IntCompSig c mor} ->
  {p, q, r : PolyDiSig c} ->
  PolyParaNT {c} mor q r -> PolyParaNT {c} mor p q -> PolyParaNT {c} mor p r
polyParaNTvcomp {c} {mor} {comp} {p} {q} {r} gamma delta =
  let
    qasn :
      ((pi : pdPos p) -> (asn : mor (pdDirR p pi) (pdDirL p pi)) ->
       mor
        (pdDirR q $ ppntOnPos {mor} delta pi asn)
        (pdDirL q $ ppntOnPos {mor} delta pi asn)) =
          \pi, asn =>
            comp
              (pdDirR q $ ppntOnPos {mor} delta pi asn)
              (pdDirL p pi)
              (pdDirL q $ ppntOnPos {mor} delta pi asn)
              (ppntOnL {mor} delta pi asn)
            $ comp
              (pdDirR q $ ppntOnPos {mor} delta pi asn)
              (pdDirR p pi)
              (pdDirL p pi)
              asn
            $ ppntOnR {mor} delta pi asn
  in
  (\pi, asn =>
    ppntOnPos {mor} gamma (ppntOnPos {mor} delta pi asn) (qasn pi asn) **
   (\pi, asn =>
      comp _ _ _
        (ppntOnL {mor} gamma (ppntOnPos {mor} delta pi asn) (qasn pi asn))
        (ppntOnL {mor} delta pi asn),
    \pi, asn =>
      comp _ _ _
        (ppntOnR {mor} delta pi asn)
        (ppntOnR {mor} gamma (ppntOnPos {mor} delta pi asn) (qasn pi asn))))

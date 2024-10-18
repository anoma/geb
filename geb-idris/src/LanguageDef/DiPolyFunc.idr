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
InterpPolyDi : {c : Type} -> (mor : IntDifunctorSig c) -> PolyDiSig c ->
  IntDifunctorSig c
InterpPolyDi {c} mor p a b =
  (i : ipaPos p ** IntDiYonedaEmbedObj c mor (pdDirR p i) (pdDirL p i) a b)

public export
ipdPos : {c : Type} -> {mor : IntDifunctorSig c} -> {p : PolyDiSig c} ->
  {x, y : c} -> InterpPolyDi {c} mor p x y -> ipaPos p
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

-- The set of paranatural transformations from a direpresentable,
-- (IntDiYonedaEmbedObj i j), to an arbitrary difunctor `p`.
public export
ParaNTfromDirep : (0 c : Type) -> (0 mor : IntDifunctorSig c) ->
  (s, t : c) -> (p : IntDifunctorSig c) -> Type
ParaNTfromDirep c mor s t p = p t s

-- The set of paranatural transformations from a direpresentable,
-- (IntDiYonedaEmbedObj i j), to an arbitrary polynomial difunctor `p`.
public export
PolyParaNTfromDirep : (c : Type) -> (mor : IntDifunctorSig c) ->
  (s, t : c) -> (p : PolyDiSig c) -> Type
PolyParaNTfromDirep c mor s t p = ParaNTfromDirep c mor s t (InterpPolyDi mor p)

-- The set of paranatural transformations between arbitrary
-- polynomial difunctors.
public export
PolyParaNTasProd : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntMorSig (PolyDiSig c)
PolyParaNTasProd c mor p q =
  (pi : ipaPos p) ->
  PolyParaNTfromDirep c mor (pdDirR p pi) (pdDirL p pi) q

-- Having defined the set of paranatural transformations between polynomial
-- difunctors via the Yoneda lemma, we now write it in a more explicit form
-- and show they are the same.
public export
PolyParaNT : (c : Type) -> (mor : IntDifunctorSig c) -> IntMorSig (PolyDiSig c)
PolyParaNT c mor p q =
  (onpos : ipaPos p -> ipaPos q **
   ((pi : ipaPos p) -> mor (pdDirL p pi) (pdDirL q (onpos pi)),
    (pi : ipaPos p) -> mor (pdDirR q (onpos pi)) (pdDirR p pi)))

public export
ppntOnPos : {c : Type} -> {mor : IntDifunctorSig c} -> {p, q : PolyDiSig c} ->
  PolyParaNT c mor p q -> ipaPos p -> ipaPos q
ppntOnPos {c} {mor} {p} {q} = DPair.fst

public export
ppntOnL : {c : Type} -> {mor : IntDifunctorSig c} -> {p, q : PolyDiSig c} ->
  (nt : PolyParaNT c mor p q) -> (pi : ipaPos p) ->
  mor (pdDirL p pi) (pdDirL q (ppntOnPos {c} {mor} {p} {q} nt pi))
ppntOnL {c} {mor} {p} {q} nt = Builtin.fst $ DPair.snd nt

public export
ppntOnR : {c : Type} -> {mor : IntDifunctorSig c} -> {p, q : PolyDiSig c} ->
  (nt : PolyParaNT c mor p q) -> (pi : ipaPos p) ->
  mor (pdDirR q (ppntOnPos {c} {mor} {p} {q} nt pi)) (pdDirR p pi)
ppntOnR {c} {mor} {p} {q} nt = Builtin.snd $ DPair.snd nt

public export
PolyParaNTisoL : {c : Type} -> {mor : IntDifunctorSig c} ->
  {p, q : PolyDiSig c} ->
  PolyParaNTasProd c mor p q -> PolyParaNT c mor p q
PolyParaNTisoL {c} {mor} gamma =
  (\pi => fst (gamma pi) **
   (\pi => fst (snd $ gamma pi),
    \pi => snd (snd $ gamma pi)))

public export
PolyParaNTisoR : {c : Type} -> {mor : IntDifunctorSig c} ->
  {p, q : PolyDiSig c} ->
  PolyParaNT c mor p q -> PolyParaNTasProd c mor p q
PolyParaNTisoR {c} {mor} {p} {q} nt =
  \pi : ipaPos p =>
    (ppntOnPos {mor} {p} {q} nt pi **
     (ppntOnL {mor} {p} {q} nt pi,
      ppntOnR {mor} {p} {q} nt pi))

public export
InterpPolyParaNT :
  {c : Type} -> {mor : IntDifunctorSig c} -> (comp : IntCompSig c mor) ->
  {p, q : PolyDiSig c} ->
  PolyParaNT c mor p q ->
  IntDiNTSig c (InterpPolyDi {c} mor p) (InterpPolyDi {c} mor q)
InterpPolyParaNT {c} {mor} comp {p} {q} nt x ipd =
  (ppntOnPos {mor} {p} {q} nt (ipdPos {mor} ipd) **
   (comp
      x
      (pdDirL p (ipdPos {mor} ipd))
      (pdDirL q (ppntOnPos {mor} {p} {q} nt (ipdPos {mor} ipd)))
      (ppntOnL {mor} {p} {q} nt (ipdPos {mor} ipd))
      (ipdDirL {mor} ipd),
    comp
      (pdDirR q (ppntOnPos {mor} {p} {q} nt (ipdPos {mor} ipd)))
      (pdDirR p (ipdPos {mor} ipd))
      x
      (ipdDirR {mor} ipd)
      (ppntOnR {mor} {p} {q} nt (ipdPos {mor} ipd))))

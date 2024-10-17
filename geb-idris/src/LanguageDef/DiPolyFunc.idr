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
InterpPolyDi : {c : Type} -> (mor : IntDifunctorSig c) -> PolyDiSig c ->
  IntDifunctorSig c
InterpPolyDi {c} mor p a b =
  (i : ipaPos p ** IntDiYonedaEmbedObj c mor (ipaContra p i) (ipaCovar p i) a b)

public export
InterpPolyDimap : {c : Type} -> {mor : IntDifunctorSig c} ->
  IntCompSig c mor ->
  (p : PolyDiSig c) -> IntEndoDimapSig c mor (InterpPolyDi {c} mor p)
InterpPolyDimap {c} {mor} comp p s t a b mas mtb =
  dpMapSnd $ \pi =>
    bimap (flip (comp a s (ipaCovar p pi)) mas) (comp (ipaContra p pi) t b mtb)

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
PolyParaNT : (c : Type) -> (mor : IntDifunctorSig c) -> IntMorSig (PolyDiSig c)
PolyParaNT c mor (ppos ** (pcontra, pcovar)) q =
  (pi : ppos) -> PolyParaNTfromDirep c mor (pcontra pi) (pcovar pi) q

-- Having defined the set of paranatural transformations between polynomial
-- difunctors via the Yoneda lemma, we now write it in a more explicit form
-- and show they are the same.
public export
PolyParaNT' : (c : Type) -> (mor : IntDifunctorSig c) -> IntMorSig (PolyDiSig c)
PolyParaNT' c mor (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar)) =
  (onpos : ppos -> qpos **
   ((pi : ppos) -> mor (pcovar pi) (qcovar (onpos pi)),
    (pi : ppos) -> mor (qcontra (onpos pi)) (pcontra pi)))

public export
PolyParaNTisoL : {c : Type} -> {mor : IntDifunctorSig c} ->
  {p, q : PolyDiSig c} ->
  PolyParaNT c mor p q -> PolyParaNT' c mor p q
PolyParaNTisoL {c} {mor}
  {p=(ppos ** (pcontra, pcovar))} {q=(qpos ** (qcontra, qcovar))} gamma =
    (\pi => fst (gamma pi) **
     (\pi => fst (snd $ gamma pi),
      \pi => snd (snd $ gamma pi)))

public export
PolyParaNTisoR : {c : Type} -> {mor : IntDifunctorSig c} ->
  {p, q : PolyDiSig c} ->
  PolyParaNT' c mor p q -> PolyParaNT c mor p q
PolyParaNTisoR {c} {mor}
  {p=(ppos ** (pcontra, pcovar))} {q=(qpos ** (qcontra, qcovar))}
  (onpos ** (oncovar, oncontra)) =
    \pi : ppos => (onpos pi ** (oncovar pi, oncontra pi))

public export
InterpPolyParaNT :
  {c : Type} -> {mor : IntDifunctorSig c} -> (comp : IntCompSig c mor) ->
  {p, q : PolyDiSig c} ->
  PolyParaNT' c mor p q ->
  IntDiNTSig c (InterpPolyDi {c} mor p) (InterpPolyDi {c} mor q)
InterpPolyParaNT {c} {mor} comp
  {p=(ppos ** (pcontra, pcovar))} {q=(qpos ** (qcontra, qcovar))}
  (onpos ** (oncovar, oncontra)) x (pi ** (mxcov, mcontx)) =
    (onpos pi **
     (comp x (pcovar pi) (qcovar (onpos pi)) (oncovar pi) mxcov,
      comp (qcontra (onpos pi)) (pcontra pi) x mcontx (oncontra pi)))

module LanguageDef.SpanCospan

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra

-----------------------------------------------------------------------
-----------------------------------------------------------------------
---- Objects of span and cospan categories in dependent-type style ----
-----------------------------------------------------------------------
-----------------------------------------------------------------------

-- A span is a diagram with three objects and two non-identity arrows, both of
-- which emanate from a common domain, each to one of the other two objects.
-- (The index category underlying such a diagram we call the "span index
-- category".)
--
-- Because that constitutes a DAG (ignoring the identity self-loops), we can
-- equivalently express it as one object (the domain) fibered over two
-- (the codomains).
--
-- The colimit of a span is a pushout, so a span is sometimes called a
-- "pushout diagram".
public export
record SpanObj where
  constructor Span
  spCodL : Type
  spCodR : Type
  spDom : spCodL -> spCodR -> Type

-- A cospan is a diagram with three objects and two non-identity arrows, each
-- of which emanates from a different domain, both to a common domain.
-- (The index category underlying such a diagram we call the "cospan index
-- category".)
--
-- Because that constitutes a DAG (ignoring the identity self-loops), we can
-- equivalently express it as two objects (the domains) each fibered over a
-- single object (the codomain).
--
-- The limit of a span is a pullback, so a cospan is sometimes called a
-- "pullback diagram".
public export
record CospanObj where
  constructor Cospan
  cospCod : Type
  cospDomL : cospCod -> Type
  cospDomR : cospCod -> Type

-------------------------------------------------------------------------
-------------------------------------------------------------------------
---- Morphisms of span and cospan categories in dependent-type style ----
-------------------------------------------------------------------------
-------------------------------------------------------------------------

-- A span is a functor (from the span index category), so a morphism
-- of spans is a natural transformation.  A morphism of spans in `Type` (the
-- base category of the metalanguage), when the spans themselves are
-- represented in dependent-type style as above, can be expressed as
-- metalanguage functions (which are the morphisms of `Type`) between
-- corresponding objects in the diagram, with the commutativity conditions
-- being represented by the functions' respecting the dependent-type
-- relationships.
public export
record SpanMorph (dom, cod : SpanObj) where
  constructor SpanM
  spmCodL : spCodL dom -> spCodL cod
  spmCodR : spCodR dom -> spCodR cod
  spmDom : (l : spCodL dom) -> (r : spCodR dom) ->
    spDom dom l r -> spDom cod (spmCodL l) (spmCodR r)

public export
spanId : (0 a : SpanObj) -> SpanMorph a a
spanId (Span codl codr dom) = SpanM id id (\_, _ => id)

public export
spanComp : {0 a, a', a'' : SpanObj} ->
  SpanMorph a' a'' -> SpanMorph a a' -> SpanMorph a a''
spanComp
  {a=(Span codl codr dom)}
  {a'=(Span codl' codr' dom')}
  {a''=(Span codl'' codr'' dom'')}
  (SpanM mcodl' mcodr' mdom') (SpanM mcodl mcodr mdom) =
    SpanM
      (mcodl' . mcodl)
      (mcodr' . mcodr)
      $ \l, r, d => mdom' (mcodl l) (mcodr r) $ mdom l r d

-- A cospan is a functor (from the cospan index category), so a morphism
-- of cospans is a natural transformation.  A morphism of cospans in `Type` (the
-- base category of the metalanguage), when the cospans themselves are
-- represented in dependent-type style as above, can be expressed as
-- metalanguage functions (which are the morphisms of `Type`) between
-- corresponding objects in the diagram, with the commutativity conditions
-- being represented by the functions' respecting the dependent-type
-- relationships.
public export
record CospanMorph (dom, cod : CospanObj) where
  constructor CospanM
  cospmCod : cospCod dom -> cospCod cod
  cospmDomL : (ed : cospCod dom) ->
    cospDomL dom ed -> cospDomL cod (cospmCod ed)
  cospmDomR : (ed : cospCod dom) ->
    cospDomR dom ed -> cospDomR cod (cospmCod ed)

export
cospanId : (0 b : CospanObj) -> CospanMorph b b
cospanId (Cospan cod doml domr) = CospanM id (\_ => id) (\_ => id)

public export
cospanComp : {0 b, b', b'' : CospanObj} ->
  CospanMorph b' b'' -> CospanMorph b b' -> CospanMorph b b''
cospanComp
  {b=(Cospan cod doml domr)}
  {b'=(Cospan cod' doml' domr')}
  {b''=(Cospan cod'' doml'' domr'')}
  (CospanM mcod' mdoml' mdomr') (CospanM mcod mdoml mdomr) =
    CospanM
      (mcod' . mcod)
      (\ed, ed' => mdoml' (mcod ed) $ mdoml ed ed')
      (\ed, ed' => mdomr' (mcod ed) $ mdomr ed ed')

---------------------------------------------------------------
---------------------------------------------------------------
---- Adjunctions defining pullbacks and pushouts in `Type` ----
---------------------------------------------------------------
---------------------------------------------------------------

---------------------------
---- Diagonal functors ----
---------------------------

-- The object-map component of the diagonal functor from `Type` to the category
-- of spans in `Type` (which is the functor category from the span index
-- category to `Type`).
--
-- The diagonal functor sends an object `x` of `Type` to the object of the
-- functor category `SpanObj` whose objects are all `x`.  Because we have
-- expressed `SpanObj` in a dependent-type style, we have to represent the
-- common domain as a type which depends upon pairs of terms of `x` yet is
-- equivalent to just `x` itself.  We must pare an input of cardinality
-- `|x|^2` down to one of cardinality `|x|`.
--
-- This is possible, in one straightforward way:  treat the type family as
-- `Void` for all non-diagonal inputs, and `Unit` for all diagonal inputs.
--
-- The effect of this on the implicit morphisms which we have represented in
-- `SpanObj` as type dependencies is to make each morphism the equivalent of the
-- identity morphism (which makes sense because we have mapped each object of
-- the span index category to the same object), as required by the definition
-- of the diagonal functor.
export
SpanDiagObj : Type -> SpanObj
SpanDiagObj x = Span x x (\ex, ex' => FunExt -> ex = ex')

-- The object-map component of the diagonal functor from `Type` to the category
-- of cospans in `Type` (which is the functor category from the cospan index
-- category to `Type`).
--
-- In this case, dually for what we had to do with `SpanDiagObj`, we must make
-- the common codomain simply `x`, and make each of the common domains a type
-- (family) which depends upon terms of `x` yet is equivalent to simply `x`.
-- This we can do by making each type of the family `Unit`.
export
CospanDiagObj : Type -> CospanObj
CospanDiagObj x = Cospan x (\_ => Unit) (\_ => Unit)

-- The morphism-map component of the diagonal functor from `Type` to the
-- category of spans in `Type`.
--
-- The diagonal functor takes each morphism of `Type` to the identity morphism
-- in the category of spans (which is sensible because it takes each object of
-- the span index category to the same object).
export
SpanDiagMorph : (0 x, y : Type) ->
  (x -> y) -> SpanMorph (SpanDiagObj x) (SpanDiagObj y)
SpanDiagMorph x y f = SpanM f f (\l, r, eqlr, fext => cong f $ eqlr fext)

-- The morphism-map component of the diagonal functor from `Type` to the
-- category of cospans in `Type`, defined dually to `SpanDiagMorph`.
export
CospanDiagMorph : (0 x, y : Type) ->
  (x -> y) -> CospanMorph (CospanDiagObj x) (CospanDiagObj y)
CospanDiagMorph x y f = CospanM f (\_, _ => ()) (\_, _ => ())

-------------------------------------------------------
---- Pushouts/pullbacks as co(limits) of (co)spans ----
-------------------------------------------------------

-- The pushout functor from the category of spans to `Type` is left
-- adjoint to the diagonal functor (pushouts are colimits).
--
-- In the pushout-defining functor, therefore,
-- `SpanDiagObj`/`SpanDiagMorph` is the right adjoint.

export
PushoutRAdjointObj : Type -> SpanObj
PushoutRAdjointObj = SpanDiagObj

export
PushoutRAdjointMorph : (0 b, b' : Type) -> (b -> b') ->
  SpanMorph (PushoutRAdjointObj b) (PushoutRAdjointObj b')
PushoutRAdjointMorph = SpanDiagMorph

-- The pullback functor from the category of cospans to `Type` is right
-- adjoint to the diagonal functor (pullbacks are limits).
--
-- In the pullback-defining functor, therefore,
-- `CospanDiagObj`/`CospanDiagMorph` is the left adjoint.

export
PullbackLAdjointObj : Type -> CospanObj
PullbackLAdjointObj = CospanDiagObj

export
PullbackLAdjointMorph : (0 a, a' : Type) -> (a -> a') ->
  CospanMorph (PullbackLAdjointObj a) (PullbackLAdjointObj a')
PullbackLAdjointMorph = CospanDiagMorph

-- To compute the left adjoint of the pushout adjunction -- the pushout
-- functor -- we reason as follows:  if `L` is the pushout functor, `R` is
-- the span-diagonal functor, `a` is a span, and `b` is an object of `Type`,
-- then `L a -> b ~=~ a -> R b`; hence, `L a` must be "that which is eliminated
-- [to a given `b`] by an `a -> R b` [which is a `SpanMorph`]".  For it to be
-- possible to map out (eliminate) the pushout to `b` by an `a -> R b` means
-- that we must have a natural transformation:  for each `b`, we can get from
-- `a -> R b` to `b`.  (Note that that that natural transformation is
-- precisely the right Kan extension of the identity along `R`.)  Hence
-- we define:
export
PushoutElimSig : SpanObj -> Type -> Type
PushoutElimSig = (|>) SpanDiagObj . SpanMorph

export
PushoutElimMap : (a : SpanObj) -> (0 b, b' : Type) ->
  (b -> b') -> PushoutElimSig a b -> PushoutElimSig a b'
PushoutElimMap (Span codl codr dom) b b' m (SpanM mcodl mcodr mdom) =
  SpanM (m . mcodl) (m . mcodr) (\l, r, d, fext => cong m $ mdom l r d fext)

export
PushoutLAdjointObj : SpanObj -> Type
PushoutLAdjointObj a =
  Subset0
    (NaturalTransformation (PushoutElimSig a) (id {a=Type}))
    (NaturalityCondition (PushoutElimMap a) (\_, _ => id))

export
PushoutLAdjointMorph : (0 a, a' : SpanObj) ->
  SpanMorph a a' -> PushoutLAdjointObj a -> PushoutLAdjointObj a'
PushoutLAdjointMorph (Span codl codr dom) (Span codl' codr' dom')
  (SpanM mcodl mcodr mdom) (Element0 alpha natural) =
    Element0
      (\x, m' => alpha x $ spanComp m' (SpanM mcodl mcodr mdom))
      (\b, b', mb, m'@(SpanM mcodl' mcodr' mdom') =>
        natural b b' mb (spanComp m' (SpanM mcodl mcodr mdom)))

-- Note that we could also have defined the left adjoint of the pullback
-- functor via an existential quantifier rather than a universal one,
-- as follows -- note however that the definition is partial, because it is
-- recursive with the type being defined in a negative position, so
-- for left adjoints we use the universal forms:
export
partial
data PushoutLAdjointObjExist : SpanObj -> Type where
  PLAOE : {0 a : SpanObj} ->
    NaturalTransformation
      (HomProf (PushoutLAdjointObjExist a))
      (PushoutElimSig a) ->
    PushoutLAdjointObjExist a

-- To compute the right adjoint of the pullback adjunction -- the pullback
-- functor -- we reason as follows:  if `R` is the pullback functor, `L` is
-- the cospan-diagonal functor, `a` is an object of `Type`, and `b` is a cospan,
-- then `L a -> b ~=~ a -> R b`; hence, `R b` must be "that which is introduced
-- [from a given `a`] by an `L a -> b` [which is a `CospanMorph`]".  Hence we
-- define:
export
PullbackIntroSig : CospanObj -> Type -> Type
PullbackIntroSig a b = (b, CospanMorph (CospanDiagObj b) a)

-- Note that this is precisely the left Kan extension of the identity
-- along `L` (`CospanDiagObj`).
export
PullbackRAdjointObj : CospanObj -> Type
PullbackRAdjointObj a = Exists {type=Type} $ PullbackIntroSig a

export
PullbackRAdjointMorph : (0 b, b' : CospanObj) ->
  CospanMorph b b' -> PullbackRAdjointObj b -> PullbackRAdjointObj b'
PullbackRAdjointMorph b b' m (Evidence x (ex, m')) =
  Evidence x (ex, cospanComp m m')

-- Note that we could also have defined the right adjoint of the pullback
-- functor via a universal quantifier rather than an existential one,
-- as follows -- note however that the definition is recursive, so for
-- right adjoints we use the existential form:
export
data PullbackRAdjointObjUniv : CospanObj -> Type where
  PRAOU : {0 b : CospanObj} ->
    NaturalTransformation
      (PullbackIntroSig b)
      (flip HomProf (PullbackRAdjointObjUniv b)) ->
    PullbackRAdjointObjUniv b

-- Next we define the adjuncts.

export
PushoutLAdjunct : (a : SpanObj) -> (b : Type) ->
  (PushoutLAdjointObj a -> b) -> SpanMorph a (SpanDiagObj b)
PushoutLAdjunct s@(Span codl codr dom) b f =
  SpanM
    (\l =>
      f (Element0 (\x, m => spmCodL m l)
        $ \b, b', m, sm => case sm of SpanM mcodl mcodr mdom => Refl))
    (\r =>
      f (Element0 (\x, m => spmCodR m r)
        $ \b, b', m, sm => case sm of SpanM mcodl mcodr mdom => Refl))
    (\l, r, ed, fext =>
      let
        feq :
          ((\x : Type, m : SpanMorph s (SpanDiagObj x) => spmCodL m l) =
           (\x : Type, m : SpanMorph s (SpanDiagObj x) => spmCodR m r)) =
          funExt $ \x => funExt $ \(SpanM mcodl mcodr mdom) => mdom l r ed fext
      in
      rewrite feq in
      cong f $
      s0Eq12 Refl
        (funExt $ \b => funExt $ \b' => funExt $ \m => funExt $
          \(SpanM _ _ _) => uip))

export
PushoutRAdjunct : (a : SpanObj) -> (b : Type) ->
  SpanMorph a (SpanDiagObj b) -> PushoutLAdjointObj a -> b
PushoutRAdjunct a b m (Element0 alpha natural) = alpha b m

export
PullbackLAdjunct : (a : Type) -> (b : CospanObj) ->
  CospanMorph (CospanDiagObj a) b -> a -> PullbackRAdjointObj b
PullbackLAdjunct a b m ea = Evidence a (ea, m)

export
PullbackRAdjunct : (a : Type) -> (b : CospanObj) ->
  (a -> PullbackRAdjointObj b) -> CospanMorph (CospanDiagObj a) b
PullbackRAdjunct a (Cospan cod doml domr) m =
  CospanM
    (\ea => cospmCod (snd (snd $ m ea)) (fst (snd $ m ea)))
    (\ea, () => cospmDomL (snd (snd $ m ea)) (fst (snd $ m ea)) ())
    (\ea, () => cospmDomR (snd (snd $ m ea)) (fst (snd $ m ea)) ())

-- Now that we have defined the adjoints of the pushout and pullback
-- adjunctions, we can define the monads and comonads by composition.

export
PushoutMonadObj : SpanObj -> SpanObj
PushoutMonadObj = PushoutRAdjointObj . PushoutLAdjointObj

export
PushoutMonadMorph : (a, a' : SpanObj) ->
  SpanMorph a a' -> SpanMorph (PushoutMonadObj a) (PushoutMonadObj a')
PushoutMonadMorph a a' m =
  PushoutRAdjointMorph (PushoutLAdjointObj a) (PushoutLAdjointObj a')
    (PushoutLAdjointMorph a a' m)

export
PushoutComonadObj : Type -> Type
PushoutComonadObj = PushoutLAdjointObj . PushoutRAdjointObj

export
PushoutComonadMorph : (b, b' : Type) ->
  (b -> b') -> PushoutComonadObj b -> PushoutComonadObj b'
PushoutComonadMorph b b' m =
  PushoutLAdjointMorph (PushoutRAdjointObj b) (PushoutRAdjointObj b')
    (PushoutRAdjointMorph b b' m)

export
PullbackMonadObj : Type -> Type
PullbackMonadObj = PullbackRAdjointObj . PullbackLAdjointObj

export
PullbackMonadMorph : (a, a' : Type) ->
  (a -> a') -> PullbackMonadObj a -> PullbackMonadObj a'
PullbackMonadMorph a a' m =
  PullbackRAdjointMorph (PullbackLAdjointObj a) (PullbackLAdjointObj a')
    (PullbackLAdjointMorph a a' m)

export
PullbackComonadObj : CospanObj -> CospanObj
PullbackComonadObj = PullbackLAdjointObj . PullbackRAdjointObj

export
PullbackComonadMorph : (b, b' : CospanObj) ->
  CospanMorph b b' -> CospanMorph (PullbackComonadObj b) (PullbackComonadObj b')
PullbackComonadMorph b b' m =
  PullbackLAdjointMorph (PullbackRAdjointObj b) (PullbackRAdjointObj b')
    (PullbackRAdjointMorph b b' m)

-- We now define the units and counits of the adjunctions, which are also the
-- units and counits of the monads and comonads.  (The units are sometimes
-- also known as "pure" or "return", and the counits are sometimes known as
-- "erase" or "extract".)

export
PushoutUnit : (a : SpanObj) -> SpanMorph a (PushoutMonadObj a)
PushoutUnit a = PushoutLAdjunct a (PushoutLAdjointObj a) id

export
PushoutCounit : NaturalTransformation PushoutComonadObj (id {a=Type})
PushoutCounit x =
  PushoutRAdjunct (PushoutRAdjointObj x) x (spanId $ PushoutRAdjointObj x)

export
PullbackUnit : NaturalTransformation (id {a=Type}) PullbackMonadObj
PullbackUnit x =
  PullbackLAdjunct x (PullbackLAdjointObj x) (cospanId $ PullbackLAdjointObj x)

export
PullbackCounit : (a : CospanObj) -> CospanMorph (PullbackComonadObj a) a
PullbackCounit x = PullbackRAdjunct (PullbackRAdjointObj x) x id

-- Now we define the other monad and comonad natural transformations:
-- the multiplications (joins) and comultiplications (duplicates).

export
0 pushoutJoin : (a : SpanObj) ->
  SpanMorph (PushoutMonadObj $ PushoutMonadObj a) (PushoutMonadObj a)
pushoutJoin (Span codl codr dom) =
  SpanM
    (\(Element0 l lnat) => ?pushoutJoin_hole_codl)
    (\(Element0 r rnat) => ?pushoutJoin_hole_codr)
    ?pushoutJoin_hole_dom

export
0 pushoutDup : (b : Type) ->
  PushoutComonadObj b -> PushoutComonadObj (PushoutComonadObj b)
pushoutDup b cmo@(Element0 alpha anat) =
  Element0
    (\a, m => spmCodL m cmo)
    (\a, a', ma, sm =>
      let
        mcodl = spmCodL sm
        mcodr = spmCodR sm
        mdom = spmDom sm
      in
      ?pushoutDup_hole)

export
pullbackJoin : (a : Type) ->
  PullbackMonadObj (PullbackMonadObj a) -> PullbackMonadObj a
pullbackJoin a (Evidence x (ex, m)) =
  Evidence x
    (ex,
     CospanM
      (\eb =>
        let mc = cospmCod m eb in (cospmCod $ snd $ snd mc) $ fst $ snd mc)
      (\_, _ => ())
      (\_, _ => ()))

export
pullbackDup : (b : CospanObj) ->
  CospanMorph (PullbackComonadObj b) (PullbackComonadObj $ PullbackComonadObj b)
pullbackDup (Cospan cod doml domr) =
  CospanM
    (\pb =>
      Evidence
        (fst pb)
        (fst $ snd pb, CospanM (\ea' => pb) (\_, _ => ()) (\_, _ => ())))
    (\_, _ => ())
    (\_, _ => ())

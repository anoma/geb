module LanguageDef.DiPolyFunc

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.DisliceCat
import LanguageDef.PolyCat
import LanguageDef.Geb
import LanguageDef.InternalCat

---------------------------------------------------
---------------------------------------------------
---- Dipolynomial functors from dislice arenas ----
---------------------------------------------------
---------------------------------------------------

public export
record ADiArena where
  constructor DiAr
  daPos : Type
  daCat : daPos -> ADisliceCat

public export
DAobj : (da : ADiArena) -> SliceObj (daPos da)
DAobj da = ADisliceObj . daCat da

public export
DAbase : (da : ADiArena) -> SliceObj (daPos da)
DAbase da = adscBase . daCat da

public export
DAcobase : (da : ADiArena) -> (i : daPos da) -> SliceObj (DAbase da i)
DAcobase da i = adscCobase (daCat da i)

public export
DAtot : {da : ADiArena} -> {i : daPos da} -> SliceObj (DAobj da i)
DAtot {da} {i} = Sigma {a=(DAbase da i)} . adsoTot {cat=(daCat da i)}

public export
record InterpDAf (da : ADiArena) (x : Type) where
  constructor IDAf
  idafPos : daPos da
  idafProj : x -> DAbase da idafPos
  idafDir :
    SliceMorphism {a=(DAbase da idafPos)}
      (DAcobase da idafPos)
      (SliceFromCSlice (x ** idafProj))

-- An object of the category of elements of `InterpDAF da` is
-- a dislice object.
export
IDAfobj : {da : ADiArena} -> {x : Type} ->
  (e : InterpDAf da x) -> DAobj da (idafPos e)
IDAfobj {da} {x} (IDAf pos proj dir) = ADSO (SliceFromCSlice (x ** proj)) dir

------------------------------------------------------------------
------------------------------------------------------------------
---- Dependent (dislice) dipolynomial functors and difunctors ----
------------------------------------------------------------------
------------------------------------------------------------------

--------------------------
---- Categorial-style ----
--------------------------

---------------------
---- Inductively ----
---------------------

export
ADSLbc : {b, b' : Type} -> {cb : SliceObj b} ->
  (m : b' -> b) -> ADSLomap (ADSC b cb) (ADSC b' (cb . m))
ADSLbc {b} {b'} {cb} m (ADSO tot inj) = ADSO (tot . m) (\eb' => inj $ m eb')

export
ADSLcbc : {b : Type} -> {cb, cb' : SliceObj b} ->
  SliceMorphism {a=b} cb' cb -> ADSLomap (ADSC b cb) (ADSC b cb')
ADSLcbc {b} {cb} {cb'} m (ADSO tot inj) =
  ADSO tot (\eb, ecb' => inj eb $ m eb ecb')

-- Dichange: simultaneous base and cobase change.
export
ADSLdc : {b, b' : Type} -> {cb : SliceObj b} -> {cb' : SliceObj b'} ->
  (mb : b' -> b) -> SliceMorphism {a=b'} cb' (cb . mb) ->
  ADSLomap (ADSC b cb) (ADSC b' cb')
ADSLdc {b} {b'} {cb} {cb'} mb mc =
  ADSLcbc {b=b'} {cb=(cb . mb)} {cb'} mc . ADSLbc {b} {b'} {cb} mb

export
ADSLsigma : {b : Type} -> (p : SliceObj b) -> {cb : SliceObj (Sigma {a=b} p)} ->
  ADSLomap
    (ADSC (Sigma {a=b} p) cb)
    (ADSC b $ \eb => Sigma {a=(p eb)} $ DPair.curry cb eb)
ADSLsigma {b} p {cb} (ADSO tot inj) =
  ADSO
    (\eb => Sigma {a=(p eb)} $ DPair.curry tot eb)
    (\eb, (ep ** ecb) => (ep ** inj (eb ** ep) ecb))

export
ADSLpi : {b : Type} -> (p : SliceObj b) -> {cb : SliceObj (Sigma {a=b} p)} ->
  ADSLomap
    (ADSC (Sigma {a=b} p) cb)
    (ADSC b $ \eb => Pi {a=(p eb)} $ DPair.curry cb eb)
ADSLpi {b} p {cb} (ADSO tot inj) =
  ADSO
    (\eb => Pi {a=(p eb)} $ DPair.curry tot eb)
    (\eb, pi, ep => inj (eb ** ep) $ pi ep)

--------------------------------------------------
--------------------------------------------------
---- Polynomial profunctors as curried arenas ----
--------------------------------------------------
--------------------------------------------------

-- If we consider `ADiArena`s where `pos : Type` is `Type` itself,
-- then, given that `ADiArena` actually has effectively the same
-- signature as `PolyFunc`, then we are considering arenas of type
-- `Type -> PolyFunc`.  If we absorb the type parameter into the
-- structure, we obtain a position functor and a natural transformation
-- from that functor to the constant functor which returns `Type`
-- itself.
--
-- In order to obtain a profunctor, it turns out that we must make
-- the position functor contravariant, i.e. into a functor not
-- `Type -> Type`, but `op(Type) -> Type`.
--
-- However, that definition by itself requires multiple pieces of
-- other attendant definitions and proof content:  the position
-- functor requires a `contramap`, which must be proven to obey the
-- functor laws, and the natural transformation requires a proof of
-- the naturality condition.
--
-- Furthermore, it is unclear in that definition whether we should
-- consider the resulting profunctor "polynomial", in particular because
-- there is no constraint on the contravariant position functor.
--
-- Thus, we can take a further step and require that the position functor
-- be _Dirichlet_ -- a "contravariant polynomial functor".  This provides
-- an implicit `contramap` which is guaranteed to obey the functor laws,
-- and furthermore provides a notion of Dirichlet natural transformation
-- which is guaranteed to obey the naturality condition.
--
-- It also allows a reduction of some components of the structure,
-- for example to eliminate functions to `Unit`, which are redundant
-- as they can only be the unique morphism to the terminal object.
--
-- Once such reductions are performed, it results in the `PolyProAr`
-- structure below.  This structure specializes to polynomial functors
-- when all the `ppContra`s are `Unit`, and to Dirichlet functors when
-- all the `ppCovar`s are `Void`.  It also corresponds to the notion
-- of a slice polynomial functor where the domain is `Fin(2)` and the
-- codomain is `Fin(1)`, which is isomorphic to just `Type` -- in
-- effect, an uncurried form of the signature of an endoprofunctor on
-- `Type`, i.e. `(Type, Type) -> Type` -- but interpreted so that the
-- first parameter is contravariant.
public export
record PolyProAr where
  constructor PPA
  ppPos : Type
  ppContra : SliceObj ppPos
  ppCovar : SliceObj ppPos

export
InterpPPA : PolyProAr -> ProfunctorSig
InterpPPA (PPA pos contra covar) x y =
  (i : pos ** (x -> contra i, covar i -> y))

export
InterpPPAdimap : (ppa : PolyProAr) -> TypeDimapSig (InterpPPA ppa)
InterpPPAdimap (PPA pos contra covar) s t a b mas mtb (i ** (dx, dy)) =
  (i ** (dx . mas, mtb . dy))

PPAEndBase : PolyProAr -> Type
PPAEndBase ppa = (x : Type) -> InterpPPA ppa x x

-- This could be seen as a natural transformation from the hom-profunctor
-- to `InterpPPA ppa`.  It induces a functor from the category of
-- elements of the hom-profunctor (which is the twisted-arrow category)
-- to the category of elements of `InterpPPA`.
public export
PPAProdP : PolyProAr -> Type
PPAProdP ppa = (a, b : Type) -> (a -> b) -> InterpPPA ppa a b

public export
ppaWedgeRight : (ppa : PolyProAr) -> PPAEndBase ppa -> PPAProdP ppa
ppaWedgeRight (PPA pos contra covar) eb a b f with (eb a)
  ppaWedgeRight (PPA pos contra covar) eb a b f | (i ** (dx, dy)) =
    (i ** (dx, f . dy))

public export
ppaWedgeLeft : (ppa : PolyProAr) -> PPAEndBase ppa -> PPAProdP ppa
ppaWedgeLeft (PPA pos contra covar) eb a b f with (eb b)
  ppaWedgeLeft (PPA pos contra covar) eb a b f | (i ** (dx, dy)) =
    (i ** (dx . f, dy))

public export
PPAEnd : PolyProAr -> Type
PPAEnd ppa@(PPA pos contra covar) =
  (ebi : pos **
   ebcont : (x : Type) -> x -> contra ebi **
   ebcov : (x : Type) -> covar ebi -> x **
   (a, b : Type) -> (f : a -> b) ->
    (ExtEq (ebcont b . f) (ebcont a), ExtEq (ebcov b) (f . ebcov a)))

-- This may be viewed as an object of the category of diagonal
-- elements of `InterpPPA ppa`.
PPACoendBase : PolyProAr -> Type
PPACoendBase ppa = (x : Type ** InterpPPA ppa x x)

PPASumP : PolyProAr -> Type
PPASumP ppa =
  (ab : (Type, Type) ** (snd ab -> fst ab, InterpPPA ppa (fst ab) (snd ab)))

public export
ppaCowedgeLeft : (ppa : PolyProAr) -> PPASumP ppa -> PPACoendBase ppa
ppaCowedgeLeft (PPA pos contra covar) ((a, b) ** (mba, (i ** (dcont, dcov)))) =
  (b ** i ** (dcont . mba, dcov))

public export
ppaCowedgeRight : (ppa : PolyProAr) -> PPASumP ppa -> PPACoendBase ppa
ppaCowedgeRight (PPA pos contra covar) ((a, b) ** (mba, (i ** (dcont, dcov)))) =
  (a ** i ** (dcont, mba . dcov))

-- Again viewing a polynomial endoprofunctor on `Type` as a slice functor
-- from `Fin(2)` to `Fin(1)` but with different variances, we can define
-- natural transformations in the style of slice natural transformations.
record PPAnt (p, q : PolyProAr) where
  constructor MkPPAnt
  ppaOnPos : ppPos p -> ppPos q
  ppaOnContra : (i : ppPos p) -> ppContra p i -> ppContra q (ppaOnPos i)
  ppaOnCovar : (i : ppPos p) -> ppCovar q (ppaOnPos i) -> ppCovar p i

-- Modulo coequalization, we could view the hom-profunctor as a polynomial
-- functor whose position-set is `Type` and whose direction-slice-objects
-- are both `id`.  Then we can ask what natural transformations to the
-- hom-profunctor look like.
PHomProf : PolyProAr
PHomProf = PPA Type id id

-- Note that this structure resembles a category of elements itself,
-- if we imagine `InterpPPA` as a functor into the slice category of
-- `Type` over the positions of `p`.`
record PPAntToHom (p : PolyProAr) where
  constructor NTtoHP
  pthOnPos : SliceObj (ppPos p)
  pthOnContra : SliceMorphism {a=(ppPos p)} (ppContra p) pthOnPos
  pthOnCovar : SliceMorphism {a=(ppPos p)} pthOnPos (ppCovar p)

--------------------------------------------------
--------------------------------------------------
---- Experiments with natural transformations ----
--------------------------------------------------
--------------------------------------------------

-- A natural transformation between covariant representable functors `p, q` of
-- the form `SliceObj c -> Type` is, by the Yoneda lemma, determined by a
-- morphism in the opposite direction between their representing objects --
-- so, `SliceMorphism(rep(q), rep(p))`.
--
-- If `q` is a _sum_ of representable functors (but `p` is still representable),
-- then a natural transformation from `p` to `q` is a natural transformation
-- into a sum, which, in the case of polynomial functors, amounts to a choice
-- of a single one of the representing objects of the functors of which `q`
-- is a sum.  So for `q` as a sum over `qpos` of representables, a natural
-- transformation from a representable `p` is takes the form
-- `(qi : qpos ** SliceMorphism (q[qi], rep(p)))`.
--
-- If `p` is _also_ a sum of representables, then a natural transformation
-- from `p` to `q` is a natural transformation _from_ a sum, which is a
-- product of natural transformations.  Thus such a transformation takes the
-- form `(pi : ppos) -> (qi : qpos ** SliceMorphism(q[qi], p[pi]))`.
-- We can factor this into
-- `(onpos : ppos -> qpos ** (pi : ppos) -> SliceMorphism(q[onpos pi], p[pi]))`,
-- which we might expand to be more explicit as
-- `(onpos : ppos -> qpos **
--   (pi : ppos) -> (ec : c) -> q[onpos pi](ec) -> p[pi](ec))`.
--
-- Finally, _any_ functor of the form `SliceObj c -> SliceObj d` can be
-- factored into `d` functors of the form `SliceObj c -> SliceObj d`, and
-- we know that the category of polynomial functors is closed under products,
-- so a polynomial natural transformation between functors of the form
-- `SliceObj(c) -> SliceObj(d)` must be a natural transformation between
-- products:

-- So if `p` and `q`
-- of the form `SliceObj c -> SliceObj d` are both products of `d` representable
-- functors, then a natural transformation between them takes the form
-- `SliceMorphism(sum(d)(rep(q[_])), sum(d)(rep(p[_])))`, where the morphism
-- is still in the slice category over `c`, between `d`-indexed set-coproducts
-- of objects of the slice category over `c`.
record PSS (c, d : Type) where
  constructor MkPSS
  pssPos : SliceObj d
  pssDir : (ed : d) -> pssPos ed -> SliceObj c

InterpCovPSS : (c, d : Type) -> PSS c d -> SliceObj c -> SliceObj d
InterpCovPSS c d pss slc eld =
  (i : pssPos pss eld ** SliceMorphism {a=c} (pssDir pss eld i) slc)

interpCovPSSfmap : (c, d : Type) -> (pss : PSS c d) -> (sc, sc' : SliceObj c) ->
  SliceMorphism {a=c} sc sc' ->
  SliceMorphism {a=d} (InterpCovPSS c d pss sc) (InterpCovPSS c d pss sc')
interpCovPSSfmap c d pss sc sc' m ed (i ** di) = (i ** sliceComp {a=c} m di)

record PSnt (c, d : Type) (p, q : PSS c d) where
  constructor MkPSNT
  psntOnPos : SliceMorphism {a=d} (pssPos p) (pssPos q)
  psntOnDir : (ed : d) -> (i : pssPos p ed) ->
    SliceMorphism {a=c} (pssDir q ed (psntOnPos ed i)) (pssDir p ed i)

InterpPSnt : (c, d : Type) -> (p, q : PSS c d) -> PSnt c d p q ->
  (sc : SliceObj c) ->
  SliceMorphism {a=d} (InterpCovPSS c d p sc) (InterpCovPSS c d q sc)
InterpPSnt c d (MkPSS ppos pdir) (MkPSS qpos qdir) (MkPSNT op od)
  sc ed (i ** pdi) =
    (op ed i ** \ec, qdi => pdi ec $ od ed i ec qdi)

--------------------------------------
--------------------------------------
---- Slice polynomial profunctors ----
--------------------------------------
--------------------------------------

-- The data which determine a slice polynomial profunctor from
-- `(op(Type)/d, Type/c)`, to (enriched over) `Type/v`.
record SlProAr (d, c, v : Type) where
  constructor SPA
  spaPos : SliceObj v
  spaContra : (ev : v) -> spaPos ev -> SliceObj d
  spaCovar : (ev : v) -> spaPos ev -> SliceObj c

InterpSPA : (d, c, v : Type) -> SlProAr d c v ->
  SliceObj d -> SliceObj c -> SliceObj v
InterpSPA d c v (SPA pos contra covar) sld slc elv =
  (i : pos elv **
   (SliceMorphism {a=d} sld (contra elv i),
    SliceMorphism {a=c} (covar elv i) slc))

spaLmap : (d, c, v : Type) -> (spa : SlProAr d c v) ->
  (sld, sld' : SliceObj d) -> (slc : SliceObj c) ->
  SliceMorphism {a=d} sld' sld ->
  SliceMorphism {a=v}
    (InterpSPA d c v spa sld slc)
    (InterpSPA d c v spa sld' slc)
spaLmap d c v (SPA pos contra covar) sld sld' slc md'd elv
  (i ** (dd, dc)) =
    (i ** (sliceComp {a=d} dd md'd, dc))

spaRmap : (d, c, v : Type) -> (spa : SlProAr d c v) ->
  (sld : SliceObj d) -> (slc, slc' : SliceObj c) ->
  SliceMorphism {a=c} slc slc' ->
  SliceMorphism {a=v}
    (InterpSPA d c v spa sld slc)
    (InterpSPA d c v spa sld slc')
spaRmap d c v (SPA pos contra covar) sld slc slc' mcc' elv
  (i ** (dd, dc)) =
    (i ** (dd, sliceComp {a=c} mcc' dc))

spaDimap : (d, c, v : Type) -> (spa : SlProAr d c v) ->
  (sld, sld' : SliceObj d) -> (slc, slc' : SliceObj c) ->
  SliceMorphism {a=d} sld' sld ->
  SliceMorphism {a=c} slc slc' ->
  SliceMorphism {a=v}
    (InterpSPA d c v spa sld slc)
    (InterpSPA d c v spa sld' slc')
spaDimap d c v spa sld sld' slc slc' md'd mcc' elv =
  spaLmap d c v spa sld sld' slc' md'd elv
  . spaRmap d c v spa sld slc slc' mcc' elv

-------------------------------------------------------------------------
-------------------------------------------------------------------------
---- Polynomial functors enriched over polynomial functors on `Type` ----
-------------------------------------------------------------------------
-------------------------------------------------------------------------

public export
record PolyEnrAr where
  constructor PEA
  peaPos : Type
  peaDir : peaPos -> PolyFunc

export
InterpPEA : PolyEnrAr -> PolyFunc -> PolyFunc
InterpPEA (PEA epos edir) pf =
  pfSetCoproductArena $ (\i : epos => pfHomObj (edir i) pf)

export
peaMapOnPos : (pea : PolyEnrAr) ->
  (p, q : PolyFunc) -> PolyNatTrans p q ->
  pfPos (InterpPEA pea p) -> pfPos (InterpPEA pea q)
peaMapOnPos (PEA epos edir) (ppos ** pdir) (qpos ** qdir) (onpos ** ondir)
  (i ** d) with (edir i) proof eq
    peaMapOnPos (PEA epos edir) (ppos ** pdir) (qpos ** qdir) (onpos ** ondir)
      (i ** d) | (pdi ** pdd) =
        (i ** \edii => case d (replace {p=fst} eq edii) of
          (pi ** pd) => (onpos pi ** \qdi => rewrite eq in pd (ondir pi qdi)))

export
peaMapOnDir : (pea : PolyEnrAr) ->
  (p, q : PolyFunc) -> (alpha : PolyNatTrans p q) ->
  (i : pfPos (InterpPEA pea p)) ->
  pfDir {p=(InterpPEA pea q)} (peaMapOnPos pea p q alpha i) ->
  pfDir {p=(InterpPEA pea p)} i
peaMapOnDir (PEA epos edir) (ppos ** pdir) (qpos ** qdir) (onpos ** ondir)
  (ei ** pd) d with (edir ei) proof eeq
    peaMapOnDir (PEA epos edir) (ppos ** pdir) (qpos ** qdir) (onpos ** ondir)
      (ei ** pd) (ed ** (qd ** pcd)) | (pdi ** pdp)
          with (pd $ replace {p=fst} eeq ed) proof peq
        peaMapOnDir (PEA epos edir) (ppos ** pdir) (qpos ** qdir)
          (onpos ** ondir)
          (ei ** pd) (ed ** (qd ** pcd)) | (pdi ** pdp) | (pi ** pdd) =
            (replace {p=fst} eeq ed **
             rewrite peq in ondir pi qd **
             rewrite peq in case dpeq2 eeq of Refl => pcd)

export
peaMap : (pea : PolyEnrAr) ->
  (p, q : PolyFunc) -> PolyNatTrans p q ->
  PolyNatTrans (InterpPEA pea p) (InterpPEA pea q)
peaMap pea p q alpha = (peaMapOnPos pea p q alpha ** peaMapOnDir pea p q alpha)

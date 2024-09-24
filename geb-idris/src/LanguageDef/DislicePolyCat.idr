module LanguageDef.DislicePolyCat

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.DisliceCat
import LanguageDef.PolyCat
import LanguageDef.SlicePolyCat
import LanguageDef.InternalCat

--------------------------------------------------------
--------------------------------------------------------
---- Polynomial functors between dislice categories ----
--------------------------------------------------------
--------------------------------------------------------

----------------------------------------------
---- Dependent-type style (`ABundleObj`) ----
----------------------------------------------

export
ADSLbc : {b, b' : Type} -> {cb : SliceObj b} ->
  (m : b' -> b) -> ADSLomap (b ** cb) (b' ** (cb . m))
ADSLbc {b} {b'} {cb} m (ADSO tot inj) = ADSO (tot . m) (\eb' => inj $ m eb')

export
ADSLbcMap : {b, b' : Type} -> {cb : SliceObj b} ->
  (m : b' -> b) -> ADSLfmap (ADSLbc {b} {b'} {cb} m)
ADSLbcMap {b} {b'} {cb} m (ADSO tot inj) (ADSO tot' inj') (ADSM mor _ {eq}) =
  ADSM (\eb' => mor (m eb')) (\eb' => inj' (m eb')) {eq=(\eb' => eq $ m eb')}

export
ADSLbcFunc : {b, b' : Type} -> {cb : SliceObj b} ->
  (m : b' -> b) -> ADSLfunc (b ** cb) (b' ** (cb . m))
ADSLbcFunc {b} {b'} {cb} m = ADSLf (ADSLbc m) (ADSLbcMap m)

export
ADSLcbc : {b : Type} -> {cb, cb' : SliceObj b} ->
  SliceMorphism {a=b} cb' cb -> ADSLomap (b ** cb) (b ** cb')
ADSLcbc {b} {cb} {cb'} m (ADSO tot inj) =
  ADSO tot (\eb, ecb' => inj eb $ m eb ecb')

export
ADSLcbcMap : {b : Type} -> {cb, cb' : SliceObj b} ->
  (m : SliceMorphism {a=b} cb' cb) -> ADSLfmap (ADSLcbc {b} {cb} {cb'} m)
ADSLcbcMap {b} {cb} {cb'} m (ADSO tot inj) (ADSO tot' inj') (ADSM mor _ {eq}) =
  ADSM mor (\eb => inj' eb . m eb) {eq=(\eb, ecb' => eq eb (m eb ecb'))}

export
ADSLcbcFunc : {b : Type} -> {cb, cb' : SliceObj b} ->
  SliceMorphism {a=b} cb' cb -> ADSLfunc (b ** cb) (b ** cb')
ADSLcbcFunc {b} {cb} {cb'} m = ADSLf (ADSLcbc m) (ADSLcbcMap m)

-- Dibase change: simultaneous base and cobase change.  For a dislice category,
-- this is the analogue of base change to a slice category, or cobase change
-- to a cobase category.
export
ADSLdc : {b, b' : Type} -> {cb : SliceObj b} -> {cb' : SliceObj b'} ->
  ABundleMor (b' ** cb') (b ** cb) ->
  ADSLomap (b ** cb) (b' ** cb')
ADSLdc {b} {b'} {cb} {cb'} (mb ** mc) =
  ADSLcbc {b=b'} {cb=(cb . mb)} {cb'} mc . ADSLbc {b} {b'} {cb} mb

export
ADSLdcMap : {b, b' : Type} -> {cb : SliceObj b} -> {cb' : SliceObj b'} ->
  (mb : ABundleMor (b' ** cb') (b ** cb)) ->
  ADSLfmap (ADSLdc {b} {b'} {cb} {cb'} mb)
ADSLdcMap {b} {b'} {cb} {cb'} (mb ** mc) x y =
  ADSLcbcMap {b=b'} {cb=(cb . mb)} {cb'} mc (ADSLbc mb x) (ADSLbc mb y)
  . ADSLbcMap {b} {b'} {cb} mb x y

export
ADSLdcFunc : {b, b' : Type} -> {cb : SliceObj b} -> {cb' : SliceObj b'} ->
  (mb : ABundleMor (b' ** cb') (b ** cb)) ->
  ADSLfunc (b ** cb) (b' ** cb')
ADSLdcFunc {b} {b'} {cb} {cb'} mb = ADSLf (ADSLdc mb) (ADSLdcMap mb)

export
ADSLsigma : {b : Type} -> (p : SliceObj b) -> {cb : SliceObj (Sigma {a=b} p)} ->
  ADSLomap ((Sigma {a=b} p) ** cb) (b ** SliceSigmaF {c=b} p cb)
ADSLsigma {b} p {cb} (ADSO tot inj) =
  ADSO (SliceSigmaF {c=b} p tot) (ssMap {c=b} {sl=p} cb tot inj)

export
ADSLsigmaMap : {b : Type} ->
  (p : SliceObj b) -> {cb : SliceObj (Sigma {a=b} p)} ->
  ADSLfmap (ADSLsigma {b} p {cb})
ADSLsigmaMap {b} p {cb} (ADSO tot inj) (ADSO tot' inj') (ADSM mor _ {eq}) =
  ADSM
    (ssMap {c=b} {sl=p} tot tot' mor)
    (ssMap {c=b} {sl=p} cb tot' inj')
    {eq=(\eb, (ep ** ecb) => dpEq12 Refl $ eq (eb ** ep) ecb)}

export
ADSLsigmaFunc : {b : Type} ->
  (p : SliceObj b) -> (cb : SliceObj (Sigma {a=b} p)) ->
  ADSLfunc ((Sigma {a=b} p) ** cb) (b ** SliceSigmaF {c=b} p cb)
ADSLsigmaFunc {b} p cb = ADSLf (ADSLsigma {b} p {cb}) (ADSLsigmaMap {b} p {cb})

export
ADSLfibSigma : {b, b' : Type} -> (p : SliceObj b) -> (mb : b -> b') ->
  ADSLomap (b ** p) (b' ** SliceFibSigmaF {c=b} mb p)
ADSLfibSigma {b} {b'} p mb (ADSO tot inj) =
  ADSO (SliceFibSigmaF mb tot) (sfsMap {f=mb} p tot inj)

export
ADSLfibSigmaMap : {b, b' : Type} ->
  (p : SliceObj b) -> (mb : b -> b') ->
  ADSLfmap (ADSLfibSigma {b} {b'} p mb)
ADSLfibSigmaMap {b} {b'} p mb
  (ADSO tot inj) (ADSO tot' inj') (ADSM mor _ {eq}) =
    ADSM
      (sfsMap tot tot' mor)
      (sfsMap p tot' inj')
      {eq=(\eb', (SFS eb ep) => rewrite eq eb ep in Refl)}

export
ADSLfibSigmaFunc : {b, b': Type} ->
  (p : SliceObj b) -> (mb : b -> b') ->
  ADSLfunc (b ** p) (b' ** SliceFibSigmaF {c=b} mb p)
ADSLfibSigmaFunc {b} {b'} p mb =
  ADSLf (ADSLfibSigma {b} {b'} p mb) (ADSLfibSigmaMap {b} {b'} p mb)

export
ADSLcbcSigma :
  {b, b' : Type} -> {cb : SliceObj b} -> {cb' : SliceObj b'} ->
  (mb : b -> b') -> SliceMorphism {a=b'} cb' (SliceFibSigmaF mb cb) ->
  ADSLomap (b ** cb) (b' ** cb')
ADSLcbcSigma {b} {b'} {cb} {cb'} mb mcb =
  ADSLcbc mcb . ADSLfibSigma {b} {b'} cb mb

export
ADSLcbcSigmaMap :
  {b, b' : Type} -> {cb : SliceObj b} -> {cb' : SliceObj b'} ->
  (mb : b -> b') -> (mcb : SliceMorphism {a=b'} cb' (SliceFibSigmaF mb cb)) ->
  ADSLfmap (ADSLcbcSigma {b} {b'} {cb} {cb'} mb mcb)
ADSLcbcSigmaMap {b} {b'} {cb} {cb'} mb mcb x y =
  ADSLcbcMap {cb=(SliceFibSigmaF mb cb)} {cb'} mcb
      (ADSLfibSigma cb mb x) (ADSLfibSigma cb mb y)
  . ADSLfibSigmaMap cb mb x y

-- An analogue of `SPFpoCell` -- a twisted-arrow morphism which
-- induces a functor between dislice categories.
export
ADSLcbcSigmaFunc :
  {b, b' : Type} -> {cb : SliceObj b} -> {cb' : SliceObj b'} ->
  (mb : b -> b') -> (mcb : SliceMorphism {a=b'} cb' (SliceFibSigmaF mb cb)) ->
  ADSLfunc (b ** cb) (b' ** cb')
ADSLcbcSigmaFunc mb mcb = ADSLf (ADSLcbcSigma mb mcb) (ADSLcbcSigmaMap mb mcb)

export
ADSLpi : {b : Type} -> (p : SliceObj b) -> {cb : SliceObj (Sigma {a=b} p)} ->
  ADSLomap ((Sigma {a=b} p) ** cb) (b ** SlicePiF {c=b} p cb)
ADSLpi {b} p {cb} (ADSO tot inj) =
  ADSO (SlicePiF {c=b} p tot) (spMap {c=b} {sl=p} cb tot inj)

export
ADSLpiMap : FunExt -> {b : Type} ->
  (p : SliceObj b) -> {cb : SliceObj (Sigma {a=b} p)} ->
  ADSLfmap (ADSLpi {b} p {cb})
ADSLpiMap fext {b} p {cb} (ADSO tot inj) (ADSO tot' inj') (ADSM mor _ {eq}) =
  ADSM
    (spMap {c=b} {sl=p} tot tot' mor)
    (spMap {c=b} {sl=p} cb tot' inj')
    {eq=(\eb, picb => funExt $ \ep => eq (eb ** ep) $ picb ep)}

export
ADSLpiFunc : FunExt -> {b : Type} ->
  (p : SliceObj b) -> (cb : SliceObj (Sigma {a=b} p)) ->
  ADSLfunc ((Sigma {a=b} p) ** cb) (b ** SlicePiF {c=b} p cb)
ADSLpiFunc fext {b} p cb = ADSLf (ADSLpi {b} p {cb}) (ADSLpiMap fext {b} p {cb})

------------------------------------------
---- Categorial-style (`CBundleObj`) ----
------------------------------------------

export
CDSLbc : {b, b', cb : Type} -> {proj : cb -> b} ->
  (m : b' -> b) ->
  CDSLomap (CBO b cb proj) (cbPullback (CBO b cb proj) m)
CDSLbc {b} {b'} {cb} {proj} m (CDSO tot f1 f2 comm) =
  CDSO
    (Pullback f2 m)
    (\(Element0 (eb', ecb) eqpm) =>
      Element0 (f1 ecb, eb') $ trans (comm ecb) $ sym eqpm)
    (pbProj2 {f=f2} {g=m})
    (\(Element0 (eb', ecb) eqpm) => Refl)

export
CDSLbcMap : {b, b', cb : Type} -> {proj : cb -> b} ->
  (m : b' -> b) ->
  CDSLfmap (CDSLbc {b} {b'} {proj} m)
CDSLbcMap {b} {b'} {cb} {proj} m (CDSO tot f1 f2 comm) (CDSO tot' f1' f2' comm')
  (CDSM mtot meq1 meq2) =
    CDSM
      (\(Element0 (et, eb') eqf2m) =>
        Element0 (mtot et, eb') $ trans (sym $ meq2 et) eqf2m)
      (\(Element0 (eb', ecb) eqpm) =>
        s0Eq12
          (rewrite meq1 ecb in Refl)
          (rewrite meq1 ecb in uip))
      (\(Element0 (et, eb') eqf2m) => Refl)

export
CDSLbcFunc : {b, b', cb : Type} -> {proj : cb -> b} ->
  (m : b' -> b) ->
  CDSLfunc (CBO b cb proj) (cbPullback (CBO b cb proj) m)
CDSLbcFunc {b} {b'} {cb} {proj} m = CDSLf (CDSLbc m) (CDSLbcMap m)

export
CDSLcbc : {b, cb, cb' : Type} -> {proj : cb -> b} -> {proj' : cb' -> b} ->
  CSliceMorphism {c=b} (cb' ** proj') (cb ** proj) ->
  CDSLomap (CBO b cb proj) (CBO b cb' proj')
CDSLcbc {b} {cb} {cb'} {proj} {proj'}
  (Element0 mcb mcomm) (CDSO tot f1 f2 fcomm) =
    CDSO
      tot
      (f1 . mcb)
      f2
      (\ecb' => trans (fcomm $ mcb ecb') $ sym $ mcomm ecb')

export
CDSLcbcMap : {b, cb, cb' : Type} -> {proj : cb -> b} -> {proj' : cb' -> b} ->
  (m : CSliceMorphism {c=b} (cb' ** proj') (cb ** proj)) ->
  CDSLfmap (CDSLcbc {b} {cb} {cb'} {proj} {proj'} m)
CDSLcbcMap {b} {cb} {cb'} {proj} {proj'}
  (Element0 mcb mcomm) (CDSO xtot xf1 xf2 xfcomm) (CDSO ytot yf1 yf2 yfcomm)
  (CDSM mtot meq1 meq2) =
    CDSM mtot (\ecb' => meq1 $ mcb ecb') meq2

export
CDSLcbcFunc : {b, cb, cb' : Type} -> {proj : cb -> b} -> {proj' : cb' -> b} ->
  (m : CSliceMorphism {c=b} (cb' ** proj') (cb ** proj)) ->
  CDSLfunc (CBO b cb proj) (CBO b cb' proj')
CDSLcbcFunc {b} {cb} {cb'} {proj} {proj'} m = CDSLf (CDSLcbc m) (CDSLcbcMap m)

export
CDSLdc : {b, b', cb, cb' : Type} -> {proj : cb -> b} -> {proj' : cb' -> b'} ->
  CBundleMor (CBO b' cb' proj') (CBO b cb proj) ->
  CDSLomap (CBO b cb proj) (CBO b' cb' proj')
CDSLdc {b} {b'} {cb} {cb'} {proj} {proj'} (CBM mb mp) =
  CDSLcbc
    {b=b'} {cb=(Pullback mb proj)} {cb'}
    {proj=(pbProj1 {f=mb} {g=proj})} {proj'}
    mp
  . CDSLbc
    {b} {b'} {cb} {proj}
    mb

export
CDSLdcMap : {b, b', cb, cb' : Type} -> {proj : cb -> b} -> {proj' : cb' -> b'} ->
  (mb : CBundleMor (CBO b' cb' proj') (CBO b cb proj)) ->
  CDSLfmap (CDSLdc {b} {b'} {cb} {cb'} {proj} {proj'} mb)
CDSLdcMap {b} {b'} {cb} {cb'} {proj} {proj'} (CBM mb mcb) x y =
  CDSLcbcMap {b=b'} {cb=(Pullback mb proj)} {cb'}
    {proj=(pbProj1 {f=mb} {g=proj})} {proj'}
    mcb (CDSLbc mb x) (CDSLbc mb y)
  . CDSLbcMap {b} {b'} {cb} {proj} mb x y

-- Dibase change: simultaneous base and cobase change.  For a dislice category,
-- this is the analogue of base change to a slice category, or cobase change
-- to a cobase category.
export
CDSLdcFunc : {b, b', cb, cb' : Type} ->
  {proj : cb -> b} -> {proj' : cb' -> b'} ->
  CBundleMor (CBO b' cb' proj') (CBO b cb proj) ->
  CDSLfunc (CBO b cb proj) (CBO b' cb' proj')
CDSLdcFunc mb = CDSLf (CDSLdc mb) (CDSLdcMap mb)

export
CDSLsigma : {b, b', cb : Type} -> {proj : cb -> b} ->
  (m : b -> b') ->
  CDSLomap (CBO b cb proj) (CBO b' cb (m . proj))
CDSLsigma {b} {b'} {cb} {proj} m (CDSO tot f1 f2 comm) =
  CDSO
    (fst $ CSSigma {c=b} {d=b'} m (tot ** f2))
    f1
    (snd $ CSSigma {c=b} {d=b'} m (tot ** f2))
    (\ecb => cong m $ comm ecb)

export
CDSLsigmaMap : {b, b', cb : Type} -> {proj : cb -> b} ->
  (m : b -> b') ->
  CDSLfmap (CDSLsigma {proj} m)
CDSLsigmaMap {b} {b'} {cb} {proj}
  m (CDSO xtot xf1 xf2 xcomm) (CDSO ytot yf1 yf2 ycomm) (CDSM mtot meq1 meq2) =
    CDSM
      (fst0
       $ csSigmaMap {c=b} {d=b'} {f=m} (xtot ** xf2) (ytot ** yf2)
       $ Element0 mtot meq2)
      meq1
      (snd0
       $ csSigmaMap {c=b} {d=b'} {f=m} (xtot ** xf2) (ytot ** yf2)
       $ Element0 mtot meq2)

export
CDSLsigmaFunc : {b, b', cb : Type} -> {proj : cb -> b} ->
  (m : b -> b') ->
  CDSLfunc (CBO b cb proj) (CBO b' cb (m . proj))
CDSLsigmaFunc m = CDSLf (CDSLsigma m) (CDSLsigmaMap m)

export
CDSLcbcSigma :
  {b, b', cb, cb' : Type} -> {proj : cb -> b} -> {proj' : cb' -> b'} ->
  (mb : b -> b') ->
  CSliceMorphism {c=b'} (cb' ** proj') (CSSigma mb (cb ** proj)) ->
  CDSLomap (CBO b cb proj) (CBO b' cb' proj')
CDSLcbcSigma {b} {b'} {cb} {cb'} {proj} {proj'} mb mcb =
  CDSLcbc mcb . CDSLsigma {b} {b'} {cb} {proj} mb

export
CDSLcbcSigmaMap :
  {b, b', cb, cb' : Type} -> {proj : cb -> b} -> {proj' : cb' -> b'} ->
  (mb : b -> b') ->
  (mcb : CSliceMorphism {c=b'} (cb' ** proj') (CSSigma mb (cb ** proj))) ->
  CDSLfmap (CDSLcbcSigma {proj} {proj'} mb mcb)
CDSLcbcSigmaMap {b} {b'} {cb} {cb'} {proj} {proj'} mb mcb x y =
  CDSLcbcMap {proj=(mb . proj)} mcb (CDSLsigma mb x) (CDSLsigma mb y)
  . CDSLsigmaMap {proj} mb x y

-- An analogue of `SPFpoCell` -- a twisted-arrow morphism which
-- induces a functor between dislice categories.
export
CDSLcbcSigmaFunc :
  {b, b', cb, cb' : Type} -> {proj : cb -> b} -> {proj' : cb' -> b'} ->
  (mb : b -> b') ->
  CSliceMorphism {c=b'} (cb' ** proj') (CSSigma mb (cb ** proj)) ->
  CDSLfunc (CBO b cb proj) (CBO b' cb' proj')
CDSLcbcSigmaFunc mb mcb = CDSLf (CDSLcbcSigma mb mcb) (CDSLcbcSigmaMap mb mcb)

export
CDSLpi : {b, p, cb : Type} ->
  (pproj : p -> b) -> {cbbproj : cb -> b} ->
  (cbpproj : CSliceMorphism {c=b} (cb ** cbbproj) (p ** pproj)) ->
  CDSLomap
    (CBO p cb $ fst0 cbpproj)
    (CBO
      b
      (CSliceObjDomain $ CSPi {c=p} {d=b} pproj (cb ** fst0 cbpproj))
      (CSliceObjMap $ CSPi {c=p} {d=b} pproj (cb ** fst0 cbpproj)))
CDSLpi {b} {p} {cb} pproj {cbbproj} (Element0 cbpproj cbpeq)
  (CDSO tot fact1 fact2 comm) =
    CDSO
      (fst $ CSPi {c=p} {d=b} pproj (tot ** fact2))
      (\(eb ** Element0 pcb pcbeq) =>
        (eb **
         (Element0 (fact1 . pcb)
          (\ep => trans (pcbeq ep) $ sym $ comm $ pcb $ ep))))
      (snd $ CSPi {c=p} {d=b} pproj (tot ** fact2))
      (\(eb ** Element0 ep pcbeq) => Refl)

export
CDSLpiMap : FunExt -> {b, p, cb : Type} ->
  (pproj : p -> b) -> {cbbproj : cb -> b} ->
  (cbpproj : CSliceMorphism {c=b} (cb ** cbbproj) (p ** pproj)) ->
  CDSLfmap (CDSLpi pproj cbpproj)
CDSLpiMap fext {b} {p} {cb} pproj {cbbproj} (Element0 cbpproj cbpeq)
  x@(CDSO xtot xfact1 xfact2 xcomm)
  y@(CDSO ytot yfact1 yfact2 ycomm)
  m@(CDSM mtot meq1 meq2) =
    CDSM
      (fst0
       $ csPiMap {f=pproj} (xtot ** xfact2) (ytot ** yfact2)
       $ Element0 mtot meq2)
      (\(eb ** Element0 xmap xmeq) =>
        dpEq12
          Refl
          $ s0Eq12
            (funExt $ \ep => meq1 $ xmap $ ep)
            $ rewrite funExt meq1 in funExt $ \ep => uip)
       (snd0
        $ csPiMap {f=pproj} (xtot ** xfact2) (ytot ** yfact2)
        $ Element0 mtot meq2)

export
CDSLpiFunc : FunExt -> {b, p, cb : Type} ->
  (pproj : p -> b) -> {cbbproj : cb -> b} ->
  (cbpproj : CSliceMorphism {c=b} (cb ** cbbproj) (p ** pproj)) ->
  CDSLfunc
    (CBO p cb $ fst0 cbpproj)
    (CBO
      b
      (CSliceObjDomain $ CSPi {c=p} {d=b} pproj (cb ** fst0 cbpproj))
      (CSliceObjMap $ CSPi {c=p} {d=b} pproj (cb ** fst0 cbpproj)))
CDSLpiFunc fext pproj cbpproj =
  CDSLf (CDSLpi pproj cbpproj) (CDSLpiMap fext pproj cbpproj)

---------------------------------------------------
---------------------------------------------------
---- Dipolynomial functors from dislice arenas ----
---------------------------------------------------
---------------------------------------------------

public export
record ADiArena where
  constructor DiAr
  daPos : Type
  daCat : daPos -> ABundleObj

public export
DAobj : (da : ADiArena) -> SliceObj (daPos da)
DAobj da = ADisliceObj . daCat da

public export
DAbase : (da : ADiArena) -> SliceObj (daPos da)
DAbase da = abBase . daCat da

public export
DAcoTot : (da : ADiArena) -> SliceObj (daPos da)
DAcoTot da = abTot . daCat da

public export
DAcobase : (da : ADiArena) -> (i : daPos da) -> SliceObj (DAbase da i)
DAcobase da i = abCobase (daCat da i)

public export
DAtot : {da : ADiArena} -> {i : daPos da} -> DAobj da i ->
  SliceObj (DAbase da i)
DAtot {da} {i} = adsoTot {cat=(daCat da i)}

public export
DAsigma : {da : ADiArena} -> {i : daPos da} -> SliceObj (DAobj da i)
DAsigma {da} {i} = Sigma {a=(DAbase da i)} . DAtot {da} {i}

public export
DAinj : {da : ADiArena} -> {i : daPos da} -> (x : DAobj da i) ->
  SliceMorphism {a=(DAbase da i)} (DAcobase da i) (DAtot {da} {i} x)
DAinj {da} {i} = adsoInj {cat=(daCat da i)}

public export
data InterpDAf : ADiArena -> Type -> Type where
  IDAf :
    {0 da : ADiArena} -> (i : daPos da) -> (obj : DAobj da i) ->
    InterpDAf da (DAsigma {da} {i} obj)

export
IDAfpos : {da : ADiArena} -> {x : Type} -> (e : InterpDAf da x) -> daPos da
IDAfpos {da} (IDAf {da} i obj) = i

export
IDAfobj : {da : ADiArena} -> {x : Type} ->
  (e : InterpDAf da x) -> DAobj da (IDAfpos e)
IDAfobj {da} (IDAf {da} i obj) = obj

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
InterpPPAdimap : (ppa : PolyProAr) -> (0 s, t, a, b : Type) ->
  (a -> s) -> (t -> b) -> InterpPPA ppa s t -> InterpPPA ppa a b
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

-------------------------------------------------------------------------------
---- Embedding of slice polynomial functors within polynomial endofunctors ----
-------------------------------------------------------------------------------

public export
PSStoPos : {dom, cod : Type} -> PSS dom cod -> Type
PSStoPos {dom} {cod} (MkPSS pos dir) = Pair (Sigma {a=cod} pos) dom

public export
PSStoDir : {dom, cod : Type} -> (pss : PSS dom cod) ->
  PSStoPos {dom} {cod} pss -> Type
PSStoDir {dom} {cod} (MkPSS pos dir) ((i ** ec), ed) = dir i ec ed

public export
PSStoPoly : {dom, cod : Type} -> PSS dom cod -> PolyFunc
PSStoPoly {dom} {cod} pss =
  (PSStoPos {dom} {cod} pss ** PSStoDir {dom} {cod} pss)

public export
PSSDomSlice : {dom, cod : Type} -> (pss : PSS dom cod) ->
  MLPolyCatElemObj (PSStoPoly {dom} {cod} pss) -> dom
PSSDomSlice {dom} {cod} (MkPSS pos dir) (x ** ((ec ** i), ed) ** d) = ed

public export
PSSCodSlice : {dom, cod : Type} -> (pss : PSS dom cod) ->
  MLPolyCatElemObj (PSStoPoly {dom} {cod} pss) -> cod
PSSCodSlice {dom} {cod} (MkPSS pos dir) (x ** ((ec ** i), ed) ** d) = ec

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

public export
record SlProNT {d, c, v : Type} (p, q : SlProAr d c v) where
  constructor SProNT
  sproPos : SliceMorphism {a=v} (spaPos p) (spaPos q)
  sproContra : (ev : v) -> (ep : spaPos p ev) ->
    SliceMorphism {a=d} (spaContra p ev ep) (spaContra q ev (sproPos ev ep))
  sproCovar : (ev : v) -> (ep : spaPos p ev) ->
    SliceMorphism {a=c} (spaCovar q ev (sproPos ev ep)) (spaCovar p ev ep)

InterpSlProNT : {d, c, v : Type} -> {p, q : SlProAr d c v} ->
  SlProNT {d} {c} {v} p q ->
  (sld : SliceObj d) -> (slc : SliceObj c) ->
  SliceMorphism {a=v} (InterpSPA d c v p sld slc) (InterpSPA d c v q sld slc)
InterpSlProNT {d} {c} {v}
  {p=(SPA ppos pcontra pcovar)} {q=(SPA qpos qcontra qcovar)}
  (SProNT onpos oncont oncov) sld slc ev (i ** (mcont, mcovar)) =
    (onpos ev i **
     (sliceComp (oncont ev i) mcont,
      sliceComp mcovar (oncov ev i)))

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

-------------------
---- Poly-poly ----
-------------------

-- Interpret a `PolyEnrAr` as a (covariant) polynomial functor on the
-- category of (covariant) polynomial functors.
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

public export
HomToCompPEA : PolyFunc -> PolyFunc -> PolyEnrAr
HomToCompPEA p q = PEA (pfPos p -> pfPos q) (pfPosChangeArena p q)

public export
0 HomToCompPEAcorrect : (p, q, r : PolyFunc) ->
  InterpPEA (HomToCompPEA p q) r = pfHomToCompArena p q r
HomToCompPEAcorrect p q r = Refl

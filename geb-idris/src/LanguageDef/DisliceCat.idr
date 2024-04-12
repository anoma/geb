module LanguageDef.DisliceCat

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.InternalCat
import public LanguageDef.BundleCat

--------------------------------------
--------------------------------------
---- Dislice categories of `Type` ----
--------------------------------------
--------------------------------------

--------------------------
---- Categorial-style ----
--------------------------

-- A dislice category is indexed by a bundle, analogously to how
-- a slice or coslice category is indexed by an object of the base category.
-- In particular:
--
--  - A slice category over `j` is equivalent to a dislice category
--    over `Void, j, 0j` (where `0j` is the unique function from `Void` to `j`).
--  - A coslice category under `i` is equivalent to a dislice category
--   over `i, Unit, i1` (where `i1` is the unique function from `i` to `Unit`).
--  - A splice category of `i, j` is equivalent to the coproduct category
--    over all `m : i -> j` of the dislice categories `i, j, m`.
public export
record CDisliceObj (cat : CBundleObj) where
  constructor CDSO
  cdsoTot : Type
  cdsoFact1 : cbBase cat -> cdsoTot
  cdsoFact2 : cdsoTot -> cbTot cat
  0 cdsoEq :
    ExtEq {a=(cbBase cat)} {b=cbTot cat}
      (cdsoFact2 . cdsoFact1)
      (cbProj cat)

public export
record CDisliceMorph {0 cat : CBundleObj} (dom, cod : CDisliceObj cat) where
  constructor CDSM
  cdsmTot : cdsoTot dom -> cdsoTot cod
  0 cdsmEq1 :
    ExtEq {a=(cbBase cat)} {b=(cdsoTot cod)}
      (cdsoFact1 cod)
      (cdsmTot . cdsoFact1 dom)
  0 cdsmEq2 :
    ExtEq {a=(cdsoTot dom)} {b=(cbTot cat)}
      (cdsoFact2 dom)
      (cdsoFact2 cod . cdsmTot)

public export
cdsmId : {0 cat : CBundleObj} ->
  (x : CDisliceObj cat) -> CDisliceMorph {cat} x x
cdsmId {cat} x = CDSM id (\_ => Refl) (\_ => Refl)

public export
cdsmComp : {cat : CBundleObj} -> {x, y, z : CDisliceObj cat} ->
  CDisliceMorph {cat} y z ->
  CDisliceMorph {cat} x y ->
  CDisliceMorph {cat} x z
cdsmComp (CDSM gtot geq1 geq2) (CDSM ftot feq1 feq2) =
  CDSM
    (gtot . ftot)
    (\ecb => trans (geq1 ecb) $ cong gtot $ feq1 ecb)
    (\et => trans (feq2 et) $ geq2 $ ftot et)

---------------------
---- Arena-style ----
---------------------

public export
record ADisliceObj (cat : ADisliceCat) where
  constructor ADSO
  adsoTot : ASliceBase cat
  adsoInj : ADSOinj cat adsoTot

public export
ADSbaseMor : {cat : ADisliceCat} -> ADisliceObj cat -> ASliceBase cat -> Type
ADSbaseMor {cat} = SliceMorphism {a=(adscBase cat)} . adsoTot

public export
ADSMinj : {cat : ADisliceCat} ->
  (dom : ADisliceObj cat) -> (cod : SliceObj $ adscBase cat) ->
  ADSbaseMor dom cod -> ADSOinj cat cod
ADSMinj {cat} dom cod mor =
  sliceComp {x=(adscCobase cat)} {y=(adsoTot dom)} {z=cod} mor (adsoInj dom)

public export
data ADisliceMorph : {0 cat : ADisliceCat} ->
    (dom, cod : ADisliceObj cat) -> Type where
  ADSM : {0 cat : ADisliceCat} ->
    {0 dom : ADisliceObj cat} ->
    {codtot : ASliceBase cat} ->
    (mor : ADSbaseMor dom codtot) ->
    (codinj : ADSOinj cat codtot) ->
    {auto 0 eq : SliceExtEq codinj (ADSMinj dom codtot mor)} ->
    ADisliceMorph {cat} dom (ADSO codtot codinj)

public export
adsmId : {0 cat : ADisliceCat} ->
  (x : ADisliceObj cat) -> ADisliceMorph {cat} x x
adsmId {cat} x@(ADSO tot inj) = ADSM {dom=x} (\_ => id) inj {eq=(\_, _ => Refl)}

public export
adsmComp : {cat : ADisliceCat} -> {x, y, z : ADisliceObj cat} ->
  ADisliceMorph {cat} y z ->
  ADisliceMorph {cat} x y ->
  ADisliceMorph {cat} x z
adsmComp
  {cat=(ADSC base cobase)}
  {x=(ADSO xtot xinj)} {y=(ADSO ytot _)} {z=(ADSO ztot _)}
  (ADSM dmor dinj {eq=deq}) (ADSM cmor cinj {eq=ceq}) =
    ADSM (sliceComp dmor cmor) dinj
      {eq=(\eb, ec => trans (deq eb ec) $ cong (dmor eb) $ ceq eb ec)}

public export
ADSMr : {cat : ADisliceCat} -> {dom : ADisliceObj cat} ->
  (codtot : ASliceBase cat) ->
  (mor : ADSbaseMor dom codtot) ->
  ADisliceMorph {cat} dom (ADSO codtot (ADSMinj dom codtot mor))
ADSMr {cat} {dom} codtot mor =
  ADSM {cat} {dom} {codtot} mor (ADSMinj dom codtot mor) {eq=(\_, _ => Refl)}

---------------------------------------
---- Categorial-arena translations ----
---------------------------------------

export
DscCtoA : CBundleObj -> ADisliceCat
DscCtoA cat =
  ADSC (cbTot cat) $
    \ea => PreImage {a=(cbBase cat)} {b=(cbTot cat)} (cbProj cat) ea

export
DscAtoC : ADisliceCat -> CBundleObj
DscAtoC cat =
  CDSC (adscBase cat) (Sigma {a=(adscBase cat)} $ adscCobase cat) DPair.fst

DsoCtoA : {0 cat : CBundleObj} ->
  CDisliceObj cat -> ADisliceObj (DscCtoA cat)
DsoCtoA {cat} obj =
  ADSO
    (\eb => PreImage {a=(cdsoTot obj)} {b=(cbTot cat)} (cdsoFact2 obj) eb)
    (\eb, ecc =>
      Element0
        (cdsoFact1 obj $ fst0 ecc)
        $ trans (cdsoEq obj $ fst0 ecc) $ snd0 ecc)

DsoCfromA : {cat : CBundleObj} ->
  ADisliceObj (DscCtoA cat) -> CDisliceObj cat
DsoCfromA {cat=(CDSC base cobase proj)} (ADSO tot inj) =
  CDSO
    (Sigma {a=base} tot)
    (\ecb => (proj ecb ** inj (proj ecb) (Element0 ecb Refl)))
    DPair.fst
    (\_ => Refl)

DsoAtoC : {cat : ADisliceCat} -> ADisliceObj cat -> CDisliceObj (DscAtoC cat)
DsoAtoC {cat} obj =
  CDSO
    (Sigma {a=(adscBase cat)} $ adsoTot obj)
    (\(eb ** ec) => (eb ** adsoInj obj eb ec))
    DPair.fst
    (\(eb ** ec) => Refl)

DsoAfromC : {cat : ADisliceCat} -> CDisliceObj (DscAtoC cat) -> ADisliceObj cat
DsoAfromC {cat=(ADSC base cobase)} (CDSO tot fact1 fact2 eq) =
  ADSO
    (\eb => Subset0 tot $ \et => fact2 et = eb)
    (\eb, ecb => Element0 (fact1 (eb ** ecb)) $ eq (eb ** ecb))

DsmCtoA : {cat : CBundleObj} -> {dom, cod : CDisliceObj cat} ->
  CDisliceMorph {cat} dom cod ->
  ADisliceMorph {cat=(DscCtoA cat)}
    (DsoCtoA {cat} dom)
    (DsoCtoA {cat} cod)
DsmCtoA
  {cat=(CDSC base cobase proj)}
  {dom=(CDSO dtot df1 df2 deq)}
  {cod=(CDSO ctot cf1 cf2 ceq)}
  (CDSM mtot meq1 meq2) =
    ADSM
      {cat=(DscCtoA (CDSC base cobase proj))}
      {dom=(DsoCtoA {cat=(CDSC base cobase proj)} (CDSO dtot df1 df2 deq))}
      {codtot=(\eb => PreImage {a=ctot} {b=base} cf2 eb)}
      (\eb, (Element0 ed deq) =>
        Element0 (mtot ed) $ trans (sym $ meq2 ed) deq)
      (\eb, ecb =>
        Element0 (cf1 $ fst0 ecb) $ trans (ceq $ fst0 ecb) $ snd0 ecb)
      {eq=(\eb, (Element0 ecb cbeq) => rewrite meq1 ecb in s0Eq12 Refl uip)}

DsmCfromA : {cat : CBundleObj} -> {dom, cod : CDisliceObj cat} ->
  ADisliceMorph {cat=(DscCtoA cat)}
    (DsoCtoA {cat} dom)
    (DsoCtoA {cat} cod) ->
  CDisliceMorph {cat} dom cod
DsmCfromA {cat=(CDSC base cobase proj)}
  {dom=(CDSO dtot df1 df2 deq)} {cod=(CDSO ctot cf1 cf2 ceq)}
  (ADSM mor _ {eq=injeq}) =
    CDSM
      (\edt => fst0 $ mor (df2 edt) $ Element0 edt Refl)
      (\ecb =>
        trans
          (s0Eq1 (injeq (proj ecb) (Element0 ecb Refl)))
          $ rewrite sym (deq ecb) in cong (Subset0.fst0 . mor (df2 $ df1 ecb))
          $ s0Eq12 Refl uip)
      (\edt => sym $ snd0 (mor (df2 edt) (Element0 edt Refl)))

DsmAtoC : {0 cat : ADisliceCat} -> {0 dom, cod : ADisliceObj cat} ->
  ADisliceMorph {cat} dom cod ->
  CDisliceMorph {cat=(DscAtoC cat)} (DsoAtoC {cat} dom) (DsoAtoC {cat} cod)
DsmAtoC {cat} {dom} {cod=(ADSO _ _)} (ADSM mor inj {eq}) =
  CDSM
    (\(eb ** ed) => (eb ** mor eb ed))
    (\(eb ** ed) => rewrite eq eb ed in Refl)
    (\(eb ** ed) => Refl)

DsmAfromC : {0 cat : ADisliceCat} -> {dom, cod : ADisliceObj cat} ->
  CDisliceMorph {cat=(DscAtoC cat)} (DsoAtoC {cat} dom) (DsoAtoC {cat} cod) ->
  ADisliceMorph {cat} dom cod
DsmAfromC {cat=(ADSC base cobase)} {dom=(ADSO dtot dinj)} {cod=(ADSO ctot cinj)}
  (CDSM mtot meq1 meq2) =
    ADSM
      (\eb, edt => rewrite meq2 (eb ** edt) in snd (mtot (eb ** edt)))
      cinj
      {eq=(\eb, ecb => rewrite sym (meq1 (eb ** ecb)) in Refl)}

export
DsmAtoCf : (c, d : CBundleObj) ->
  (x, y : ADisliceObj (DscCtoA c)) ->
  ADisliceMorph x y -> CDisliceMorph (DsoCfromA {cat=c} x) (DsoCfromA {cat=c} y)
DsmAtoCf (CDSC cb ccb cproj) (CDSC db dcb dproj)
  (ADSO xtot xinj) (ADSO codtot minj)
  (ADSM {codtot} mor minj {eq}) =
    CDSM
      (\(ecb ** ext) => (ecb ** mor ecb ext))
      (\ecb => dpEq12 Refl $ eq (cproj ecb) $ Element0 ecb Refl)
      (\(ecb ** ext) => Refl)

export
DsmCtoAf : (c, d : ADisliceCat) ->
  (x, y : CDisliceObj (DscAtoC c)) ->
  CDisliceMorph x y -> ADisliceMorph (DsoAfromC {cat=c} x) (DsoAfromC {cat=c} y)
DsmCtoAf (ADSC cb ccb) (ADSC db dcb)
  (CDSO xtot xf1 xf2 xeq) (CDSO ytot yf1 yf2 yeq)
  (CDSM mtot meq1 meq2) =
    ADSM
      {codtot=(\ecb => PreImage {a=ytot} yf2 ecb)}
      (\ecb, (Element0 ext xeq2) =>
        Element0 (mtot ext) $ trans (sym $ meq2 ext) xeq2)
      (\ecb, eccb => Element0 (yf1 (ecb ** eccb)) $ yeq (ecb ** eccb))
      {eq=(\ecb, eccb => s0Eq12 (meq1 (ecb ** eccb)) $
        uipHet
          {eq=(yeq (ecb ** eccb))}
          {eq'=(trans (sym (meq2 (xf1 (ecb ** eccb)))) (xeq (ecb ** eccb)))}
          {eq''=(cong yf2 $ meq1 (ecb ** eccb))})}

--------------------------
--------------------------
---- Dislice functors ----
--------------------------
--------------------------

--------------------------
---- On `CBundleObj` ----
--------------------------

public export
CDSLomap : CBundleObj -> CBundleObj -> Type
CDSLomap c d = CDisliceObj c -> CDisliceObj d

public export
CDSLfmap : {c, d : CBundleObj} -> CDSLomap c d -> Type
CDSLfmap {c} {d} omap =
  (x, y : CDisliceObj c) ->
  CDisliceMorph {cat=c} x y -> CDisliceMorph {cat=d} (omap x) (omap y)

public export
record CDSLfunc (c, d : CBundleObj) where
  constructor CDSLf
  cdslO : CDSLomap c d
  cdslF : CDSLfmap {c} {d} cdslO

--------------------------
---- On `ADisliceCat` ----
--------------------------

public export
ADSLomap : ADisliceCat -> ADisliceCat -> Type
ADSLomap c d = ADisliceObj c -> ADisliceObj d

public export
ADSLfmap : {c, d : ADisliceCat} -> ADSLomap c d -> Type
ADSLfmap {c} {d} omap =
  (x, y : ADisliceObj c) ->
  ADisliceMorph {cat=c} x y -> ADisliceMorph {cat=d} (omap x) (omap y)

public export
record ADSLfunc (c, d : ADisliceCat) where
  constructor ADSLf
  adslO : ADSLomap c d
  adslF : ADSLfmap {c} {d} adslO

--------------------------------------------------------------
---- Translations between `CBundleObj` and `ADisliceCat` ----
--------------------------------------------------------------

export
DsomCtoA : {c, d : CBundleObj} ->
  CDSLomap c d -> ADSLomap (DscCtoA c) (DscCtoA d)
DsomCtoA {c} {d} omap = DsoCtoA . omap . DsoCfromA

export
DsomCfromA : {c, d : CBundleObj} ->
  ADSLomap (DscCtoA c) (DscCtoA d) -> CDSLomap c d
DsomCfromA {c} {d} omap = DsoCfromA . omap . DsoCtoA

export
DsomAtoC : {c, d : ADisliceCat} ->
  ADSLomap c d -> CDSLomap (DscAtoC c) (DscAtoC d)
DsomAtoC {c} {d} omap = DsoAtoC . omap . DsoAfromC

export
DsomAfromC : {c, d : ADisliceCat} ->
  CDSLomap (DscAtoC c) (DscAtoC d) -> ADSLomap c d
DsomAfromC {c} {d} omap = DsoAfromC . omap . DsoAtoC

export
DsfmCtoA : {c, d : CBundleObj} ->
  (omap : CDSLomap c d) ->
  CDSLfmap {c} {d} omap ->
  ADSLfmap {c=(DscCtoA c)} {d=(DscCtoA d)} (DsomCtoA omap)
DsfmCtoA {c} {d} omap fmap x y =
  DsmCtoA . fmap (DsoCfromA x) (DsoCfromA y) . DsmCfromA . DsmCtoA
  . DsmAtoCf c d x y

export
DsfCtoA : {c, d : CBundleObj} ->
  CDSLfunc c d -> ADSLfunc (DscCtoA c) (DscCtoA d)
DsfCtoA {c} {d} (CDSLf omap fmap) = ADSLf (DsomCtoA omap) (DsfmCtoA omap fmap)

export
DsfmCfromA : {c, d : CBundleObj} ->
  (omap : ADSLomap (DscCtoA c) (DscCtoA d)) ->
  ADSLfmap {c=(DscCtoA c)} {d=(DscCtoA d)} omap ->
  CDSLfmap {c} {d} (DsomCfromA omap)
DsfmCfromA {c} {d} omap fmap x y m =
  DsmAtoCf d d (omap $ DsoCtoA x) (omap $ DsoCtoA y)
  $ fmap (DsoCtoA x) (DsoCtoA y) (DsmCtoA m)

export
DsfCfromA : {c, d : CBundleObj} ->
  ADSLfunc (DscCtoA c) (DscCtoA d) -> CDSLfunc c d
DsfCfromA {c} {d} (ADSLf omap fmap) =
  CDSLf (DsomCfromA omap) (DsfmCfromA omap fmap)

export
DsfmAtoC : {c, d : ADisliceCat} ->
  (omap : ADSLomap c d) ->
  ADSLfmap {c} {d} omap ->
  CDSLfmap {c=(DscAtoC c)} {d=(DscAtoC d)} (DsomAtoC omap)
DsfmAtoC {c} {d} omap fmap x y =
  DsmAtoC . fmap (DsoAfromC x) (DsoAfromC y) . DsmAfromC . DsmAtoC
    . DsmCtoAf c d x y

export
DsfAtoC : {c, d : ADisliceCat} ->
  ADSLfunc c d -> CDSLfunc (DscAtoC c) (DscAtoC d)
DsfAtoC {c} {d} (ADSLf omap fmap) = CDSLf (DsomAtoC omap) (DsfmAtoC omap fmap)

export
DsfmAfromC : {c, d : ADisliceCat} ->
  (omap : CDSLomap (DscAtoC c) (DscAtoC d)) ->
  CDSLfmap {c=(DscAtoC c)} {d=(DscAtoC d)} omap ->
  ADSLfmap {c} {d} (DsomAfromC omap)
DsfmAfromC {c} {d} omap fmap x y m =
  DsmCtoAf d d (omap $ DsoAtoC x) (omap $ DsoAtoC y)
  $ fmap (DsoAtoC x) (DsoAtoC y) (DsmAtoC m)

export
DsfAfromC : {c, d : ADisliceCat} ->
  CDSLfunc (DscAtoC c) (DscAtoC d) -> ADSLfunc c d
DsfAfromC {c} {d} (CDSLf omap fmap) =
  ADSLf (DsomAfromC omap) (DsfmAfromC omap fmap)

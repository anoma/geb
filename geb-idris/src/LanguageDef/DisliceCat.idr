module LanguageDef.DisliceCat

import Library.IdrisUtils
import Library.IdrisCategories

--------------------------------------
--------------------------------------
---- Dislice categories of `Type` ----
--------------------------------------
--------------------------------------

--------------------------
---- Categorial-style ----
--------------------------

public export
record CDisliceCat where
  constructor CDSC
  cdscBase : Type
  cdscCobase : Type
  0 cdscProj : cdscCobase -> cdscBase

public export
record CDisliceObj (cat : CDisliceCat) where
  constructor CDSO
  cdsoTot : Type
  cdsoFact1 : cdscCobase cat -> cdsoTot
  cdsoFact2 : cdsoTot -> cdscBase cat
  0 cdsoEq :
    ExtEq {a=(cdscCobase cat)} {b=cdscBase cat}
      (cdsoFact2 . cdsoFact1)
      (cdscProj cat)

public export
record CDisliceMorphOut {0 cat : CDisliceCat} (dom : CDisliceObj cat) where
  constructor CDSMO
  cdsmoCod : CSliceObj (cdscBase cat)
  cdsmoMor :
    CSliceMorphism {c=(cdscBase cat)} (cdsoTot dom ** cdsoFact2 dom) cdsmoCod

export
CDSMOCod : {0 cat : CDisliceCat} -> (dom : CDisliceObj cat) ->
  CDisliceMorphOut {cat} dom -> CDisliceObj cat
CDSMOCod {cat} dom mor =
  CDSO
    (fst $ cdsmoCod mor)
    (fst0 (cdsmoMor mor) . cdsoFact1 dom)
    (snd $ cdsmoCod mor)
    $ \ec =>
      trans (sym $ (snd0 $ cdsmoMor mor) $ cdsoFact1 dom ec) (cdsoEq dom ec)

public export
record CDisliceMorph {0 cat : CDisliceCat} (dom, cod : CDisliceObj cat) where
  constructor CDSM
  cdsmTot : cdsoTot dom -> cdsoTot cod
  0 cdsmEq1 :
    ExtEq {a=(cdscCobase cat)} {b=(cdsoTot cod)}
      (cdsoFact1 cod)
      (cdsmTot . cdsoFact1 dom)
  0 cdsmEq2 :
    ExtEq {a=(cdsoTot dom)} {b=(cdscBase cat)}
      (cdsoFact2 dom)
      (cdsoFact2 cod . cdsmTot)

export
CDSMOtoCDSM : {0 cat : CDisliceCat} -> {dom : CDisliceObj cat} ->
  (cdsmo : CDisliceMorphOut {cat} dom) ->
  CDisliceMorph {cat} dom (CDSMOCod {cat} dom cdsmo)
CDSMOtoCDSM {cat} {dom} mor =
  CDSM (fst0 $ cdsmoMor mor) (\_ => Refl) (snd0 $ cdsmoMor mor)

export
CDSMtoCDSMO : {0 cat : CDisliceCat} -> {dom, cod : CDisliceObj cat} ->
  CDisliceMorph {cat} dom cod -> CDisliceMorphOut {cat} dom
CDSMtoCDSMO {cat} {dom} {cod} mor =
  CDSMO (cdsoTot cod ** cdsoFact2 cod) $ Element0 (cdsmTot mor) (cdsmEq2 mor)

---------------------
---- Arena-style ----
---------------------

public export
record ADisliceCat where
  constructor ADSC
  adscBase : Type
  adscCobase : SliceObj adscBase

public export
record ADisliceObj (cat : ADisliceCat) where
  constructor ADSO
  adsoTot : SliceObj (adscBase cat)
  adsoInj : SliceMorphism {a=(adscBase cat)} (adscCobase cat) adsoTot

public export
record ADisliceMorphOut {0 cat : ADisliceCat} (dom : ADisliceObj cat) where
  constructor ADSMO
  adsmoCod : SliceObj (adscBase cat)
  adsmoMor : SliceMorphism {a=(adscBase cat)} (adsoTot dom) adsmoCod

export
ADSMOCod : {cat : ADisliceCat} -> (dom : ADisliceObj cat) ->
  ADisliceMorphOut {cat} dom -> ADisliceObj cat
ADSMOCod {cat} dom cod =
  ADSO (adsmoCod cod) $ sliceComp (adsmoMor cod) $ adsoInj dom

public export
data ADisliceMorph : {0 cat : ADisliceCat} ->
    (dom, cod : ADisliceObj cat) -> Type where
  ADSM : {0 cat : ADisliceCat} -> {0 dom : ADisliceObj cat} ->
    (adsmo : ADisliceMorphOut dom) ->
    ADisliceMorph {cat} dom (ADSMOCod {cat} dom adsmo)
  ADSMrew : {0 cat : ADisliceCat} -> {0 dom : ADisliceObj cat} ->
    (codtot : SliceObj $ adscBase cat) ->
    (codinj, codinj' :
      SliceMorphism {a=(adscBase cat)} (adscCobase cat) codtot) ->
    (0 reweq :
      (eb : adscBase cat) ->
        ExtEq {a=(adscCobase cat eb)} {b=(codtot eb)}
          (codinj eb) (codinj' eb)) ->
    ADisliceMorph {cat} dom (ADSO codtot codinj) ->
    ADisliceMorph {cat} dom (ADSO codtot codinj')

---------------------------------------
---- Categorial-arena translations ----
---------------------------------------

export
DscCtoA : CDisliceCat -> ADisliceCat
DscCtoA cat =
  ADSC (cdscBase cat) $
    \ea => PreImage {a=(cdscCobase cat)} {b=(cdscBase cat)} (cdscProj cat) ea

export
DscAtoC : ADisliceCat -> CDisliceCat
DscAtoC cat =
  CDSC (adscBase cat) (Sigma {a=(adscBase cat)} $ adscCobase cat) DPair.fst

DsoCtoA : {0 cat : CDisliceCat} -> CDisliceObj cat -> ADisliceObj (DscCtoA cat)
DsoCtoA {cat} obj =
  ADSO
    (\eb => PreImage {a=(cdsoTot obj)} {b=(cdscBase cat)} (cdsoFact2 obj) eb)
    (\eb, ecc =>
      Element0
        (cdsoFact1 obj $ fst0 ecc)
        $ trans (cdsoEq obj $ fst0 ecc) $ snd0 ecc)

DsoAtoC : {cat : ADisliceCat} -> ADisliceObj cat -> CDisliceObj (DscAtoC cat)
DsoAtoC {cat} obj =
  CDSO
    (Sigma {a=(adscBase cat)} $ adsoTot obj)
    (\(eb ** ec) => (eb ** adsoInj obj eb ec))
    DPair.fst
    (\(eb ** ec) => Refl)

DsmoCtoA : {0 cat : CDisliceCat} -> {dom, cod : CDisliceObj cat} ->
  CDisliceMorphOut {cat} dom ->
  ADisliceMorphOut {cat=(DscCtoA cat)} (DsoCtoA {cat} dom)
DsmoCtoA {cat} {dom} mor =
  ADSMO
    (\eb =>
      Subset0 (fst $ cdsmoCod mor) $ \ecc => snd (cdsmoCod mor) ecc = eb)
    (\eb, ed =>
      Element0 (fst0 (cdsmoMor mor) $ fst0 ed)
        $ trans (sym $ snd0 (cdsmoMor mor) $ fst0 ed) $ snd0 ed)

DsmCtoAo : {0 cat : CDisliceCat} -> {dom, cod : CDisliceObj cat} ->
  (cmor : CDisliceMorph {cat} dom cod) ->
  ADisliceMorph {cat=(DscCtoA cat)}
    (DsoCtoA {cat} dom)
    (ADSMOCod
      (DsoCtoA {cat} dom)
      (DsmoCtoA {cat} {dom} {cod} $ CDSMtoCDSMO cmor))
DsmCtoAo {cat} {dom} {cod} cmor =
  ADSM {cat=(DscCtoA cat)} {dom=(DsoCtoA {cat} dom)}
    $ DsmoCtoA {cod} $ CDSMtoCDSMO cmor

DsmCtoA : {cat : CDisliceCat} -> {dom, cod : CDisliceObj cat} ->
  CDisliceMorph {cat} dom cod ->
  ADisliceMorph {cat=(DscCtoA cat)}
    (DsoCtoA {cat} dom)
    (DsoCtoA {cat} cod)
DsmCtoA {cat=(CDSC base cobase proj)}
  {dom=(CDSO dtot df1 df2 deq)} {cod=(CDSO ctot cf1 cf2 ceq)}
  (CDSM tot meq1 meq2) =
    ADSMrew
      {cat=(DscCtoA $ CDSC base cobase proj)}
      {dom=(DsoCtoA {cat=(CDSC base cobase proj)} $ CDSO dtot df1 df2 deq)}
      (\eb => Subset0 ctot (\ecc => cf2 ecc = eb))
      ?DsmCtoA_hole_1
      ?DsmCtoA_hole_2
      (\eb, (Element0 ecc eceq) =>
        s0Eq12 (sym $ meq1 ecc) $ rewrite (sym $ meq1 ecc) in uip)
      (DsmCtoAo
        {cat=(CDSC base cobase proj)}
        {dom=(CDSO dtot df1 df2 deq)}
        {cod=(CDSO ctot cf1 cf2 ceq)}
        (CDSM tot meq1 meq2))

DsmAtoC : {0 cat : ADisliceCat} -> {0 dom, cod : ADisliceObj cat} ->
  ADisliceMorph {cat} dom cod ->
  CDisliceMorph {cat=(DscAtoC cat)} (DsoAtoC {cat} dom) (DsoAtoC {cat} cod)
DsmAtoC {cat} {dom} {cod=(ADSO _ _)} (ADSM $ ADSMO cod mor) =
  CDSM
    (\(eb ** ed) => (eb ** mor eb ed))
    (\(eb ** ed) => Refl)
    (\(eb ** ed) => Refl)
DsmAtoC {cat} {dom} {cod=(ADSO _ _)} (ADSMrew codtot codinj codinj' eq mor) =
  let (CDSM tot eq1 eq2) = DsmAtoC mor in
  CDSM
    tot
    (\(eb ** ec) => trans (rewrite sym (eq eb ec) in Refl) $ eq1 (eb ** ec))
    eq2

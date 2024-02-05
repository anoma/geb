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
CDSMOCod {cat}
  (CDSO dtot fact1 fact2 deq) (CDSMO (ctot ** cproj) (Element0 mor ceq)) =
    CDSO ctot (mor . fact1) cproj $ \ec => trans (sym $ ceq $ fact1 ec) (deq ec)

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
CDSMOtoCDSM {cat} {dom=(CDSO dtot dfact1 dfact2 deq)}
  (CDSMO (ctot ** cproj) (Element0 mor ceq)) =
    CDSM mor (\_ => Refl) ceq

export
CDSMtoCDSMO : {0 cat : CDisliceCat} -> {dom, cod : CDisliceObj cat} ->
  CDisliceMorph {cat} dom cod -> CDisliceMorphOut {cat} dom
CDSMtoCDSMO {cat}
  {dom=(CDSO dtot dfact1 dfact2 deq)} {cod=(CDSO ctot cfact1 cfact2 ceq)}
  (CDSM mor eq1 eq2) =
    CDSMO (ctot ** cfact2) $ Element0 mor eq2

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
ADSMOCod {cat} (ADSO tot inj) (ADSMO cod mor) = ADSO cod $ sliceComp mor inj

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
    (0 _ : (eb : adscBase cat) -> ExtEq (codinj eb) (codinj' eb)) ->
    ADisliceMorph {cat} dom (ADSO codtot codinj) ->
    ADisliceMorph {cat} dom (ADSO codtot codinj')

---------------------------------------
---- Categorial-arena translations ----
---------------------------------------

export
DscCtoA : CDisliceCat -> ADisliceCat
DscCtoA (CDSC base cobase proj) =
  ADSC base $ \ea => PreImage {a=cobase} {b=base} proj ea

export
DscAtoC : ADisliceCat -> CDisliceCat
DscAtoC (ADSC base cobase) =
  CDSC base (Sigma {a=base} cobase) DPair.fst

DsoCtoA : {0 cat : CDisliceCat} -> CDisliceObj cat -> ADisliceObj (DscCtoA cat)
DsoCtoA {cat=(CDSC base cobase proj)} (CDSO tot fact1 fact2 eq) =
  ADSO
    (\eb => PreImage {a=tot} {b=base} fact2 eb)
    (\eb, (Element0 ec pcbeq) => Element0 (fact1 ec) $ trans (eq ec) pcbeq)

DsoAtoC : {cat : ADisliceCat} -> ADisliceObj cat -> CDisliceObj (DscAtoC cat)
DsoAtoC {cat=(ADSC base cobase)} (ADSO tot inj) =
  CDSO
    (Sigma {a=base} tot)
    (\(eb ** ec) => (eb ** inj eb ec))
    DPair.fst
    (\(eb ** ec) => Refl)

DsmoCtoA : {0 cat : CDisliceCat} -> {dom, cod : CDisliceObj cat} ->
  CDisliceMorphOut {cat} dom ->
  ADisliceMorphOut {cat=(DscCtoA cat)} (DsoCtoA {cat} dom)
DsmoCtoA {cat=cat@(CDSC base cobase proj)} {dom=dom@(CDSO dtot df1 df2 deq)}
  (CDSMO (ccod ** cproj) (Element0 mtot meq)) =
    ADSMO
      (\eb => Subset0 ccod $ \ecc => cproj ecc = eb)
      (\eb, (Element0 ed deq) =>
        Element0 (mtot ed) $ trans (sym $ meq ed) $ deq)

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

DsmAtoAfromC : {0 cat : CDisliceCat} -> {dom, cod : CDisliceObj cat} ->
  (cmor : CDisliceMorph {cat} dom cod) ->
  ADisliceMorph {cat=(DscCtoA cat)}
    (ADSMOCod
      (DsoCtoA {cat} dom)
      (DsmoCtoA {cat} {dom} {cod} $ CDSMtoCDSMO cmor))
    (DsoCtoA {cat} cod)
DsmAtoAfromC {cat=(CDSC base cobase proj)}
  {dom=(CDSO dtot df1 df2 deq)} {cod=(CDSO ctot cf1 cf2 ceq)}
  (CDSM tot meq1 meq2) =
    ?DsmAtoAfromC_hole

DsmCtoA : {0 cat : CDisliceCat} -> {dom, cod : CDisliceObj cat} ->
  CDisliceMorph {cat} dom cod ->
  ADisliceMorph {cat=(DscCtoA cat)}
    (DsoCtoA {cat} dom)
    (DsoCtoA {cat} cod)
DsmCtoA {cat=(CDSC base cobase proj)}
  {dom=(CDSO dtot df1 df2 deq)} {cod=(CDSO ctot cf1 cf2 ceq)}
  cmor@(CDSM tot meq1 meq2) =
    ?DsmCtoA_hole

DsmAtoC : {0 cat : ADisliceCat} -> {0 dom, cod : ADisliceObj cat} ->
  ADisliceMorph {cat} dom cod ->
  CDisliceMorph {cat=(DscAtoC cat)} (DsoAtoC {cat} dom) (DsoAtoC {cat} cod)
DsmAtoC {cat=(ADSC base cobase)} {dom=(ADSO dtot dinj)} {cod=(ADSO _ _)}
  (ADSM $ ADSMO cod mor) =
    CDSM
      (\(eb ** ed) => (eb ** mor eb ed))
      (\(eb ** ed) => Refl)
      (\(eb ** ed) => Refl)
DsmAtoC {cat=(ADSC base cobase)} {dom=(ADSO dtot dinj)} {cod=(ADSO _ _)}
  (ADSMrew codtot codinj codinj' eq mor) =
    let (CDSM tot eq1 eq2) = DsmAtoC mor in
    CDSM
      tot
      (\(eb ** ec) => trans (rewrite sym (eq eb ec) in Refl) $ eq1 (eb ** ec))
      eq2

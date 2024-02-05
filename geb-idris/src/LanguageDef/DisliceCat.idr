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
CDSMOtoCDSM {cat} {dom=(CDSO dtot dfact1 fact2 deq)}
  (CDSMO (ctot ** cproj) (Element0 mor ceq)) =
    CDSM mor (\_ => Refl) ceq

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
ADSMOCod {cat} dom adsmo =
  (ADSO (adsmoCod adsmo) $ sliceComp (adsmoMor adsmo) (adsoInj dom))

public export
data ADisliceMorph : {0 cat : ADisliceCat} ->
    (dom, cod : ADisliceObj cat) -> Type where
  ADSM : {0 cat : ADisliceCat} -> {0 dom : ADisliceObj cat} ->
    (adsmo : ADisliceMorphOut dom) ->
    ADisliceMorph {cat} dom (ADSMOCod {cat} dom adsmo)

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

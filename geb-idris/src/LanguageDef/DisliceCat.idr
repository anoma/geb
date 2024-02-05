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
record CDisliceMorph {0 cat : CDisliceCat} (dom, cod : CDisliceObj cat) where
  constructor CDSM
  cdsmTot : cdsoTot dom -> cdsoTot cod
  cdsmEq1 :
    ExtEq {a=(cdscCobase cat)} {b=(cdsoTot cod)}
      (cdsoFact1 cod)
      (cdsmTot . cdsoFact1 dom)
  cdsmEq2 :
    ExtEq {a=(cdsoTot dom)} {b=(cdscBase cat)}
      (cdsoFact2 dom)
      (cdsoFact2 cod . cdsmTot)

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
  adscTot : SliceObj (adscBase cat)
  adscInj : SliceMorphism {a=(adscBase cat)} (adscCobase cat) adscTot

public export
record ADisliceMorphOut {0 cat : ADisliceCat} (dom : ADisliceObj cat) where
  constructor ADSMO
  adsmoCod : SliceObj (adscBase cat)
  adsmoMor : SliceMorphism {a=(adscBase cat)} (adscTot dom) adsmoCod

public export
data ADisliceMorph : {0 cat : ADisliceCat} ->
    (dom, cod : ADisliceObj cat) -> Type where
  ADSM : {0 cat : ADisliceCat} -> {0 dom : ADisliceObj cat} ->
    (adsmo : ADisliceMorphOut dom) ->
    ADisliceMorph {cat}
      dom
      (ADSO (adsmoCod adsmo) $ sliceComp (adsmoMor adsmo) (adscInj dom))

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

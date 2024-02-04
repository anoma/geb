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

---------------------
---- Arena-style ----
---------------------

public export
record ADisliceCat where
  constructor ADSC
  adscBase : Type
  cdscCobase : SliceObj adscBase

public export
record ADisliceObj (cat : ADisliceCat) where
  constructor ADSO
  adscTot : SliceObj (adscBase cat)
  adscInj : SliceMorphism {a=(adscBase cat)} (cdscCobase cat) adscTot

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

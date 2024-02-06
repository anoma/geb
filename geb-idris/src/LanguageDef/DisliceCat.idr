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
  0 cdsmEq1 :
    ExtEq {a=(cdscCobase cat)} {b=(cdsoTot cod)}
      (cdsoFact1 cod)
      (cdsmTot . cdsoFact1 dom)
  0 cdsmEq2 :
    ExtEq {a=(cdsoTot dom)} {b=(cdscBase cat)}
      (cdsoFact2 dom)
      (cdsoFact2 cod . cdsmTot)

public export
cdsmId : {0 cat : CDisliceCat} ->
  (x : CDisliceObj cat) -> CDisliceMorph {cat} x x
cdsmId {cat} x = CDSM id (\_ => Refl) (\_ => Refl)

public export
cdsmComp : {cat : CDisliceCat} -> {x, y, z : CDisliceObj cat} ->
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
record ADisliceCat where
  constructor ADSC
  adscBase : Type
  adscCobase : SliceObj adscBase

public export
ASliceBase : ADisliceCat -> Type
ASliceBase = SliceObj . adscBase

public export
ADSOinj : (cat : ADisliceCat) -> ASliceBase cat -> Type
ADSOinj cat = SliceMorphism {a=(adscBase cat)} (adscCobase cat)

public export
record ADisliceObj (cat : ADisliceCat) where
  constructor ADSO
  adsoTot : ASliceBase cat
  adsoInj : ADSOinj cat adsoTot

public export
ADSmor : {cat : ADisliceCat} -> ADisliceObj cat -> ASliceBase cat -> Type
ADSmor {cat} = SliceMorphism {a=(adscBase cat)} . adsoTot

export
ADSMinj : {cat : ADisliceCat} ->
  (dom : ADisliceObj cat) -> (cod : SliceObj $ adscBase cat) ->
  ADSmor dom cod -> ADSOinj cat cod
ADSMinj {cat} dom cod mor =
  sliceComp {x=(adscCobase cat)} {y=(adsoTot dom)} {z=cod} mor (adsoInj dom)

public export
data ADisliceMorph : {0 cat : ADisliceCat} ->
    (dom, cod : ADisliceObj cat) -> Type where
  ADSM : {0 cat : ADisliceCat} ->
    {0 dom : ADisliceObj cat} ->
    {codtot : ASliceBase cat} ->
    (mor : ADSmor dom codtot) ->
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

DsmCtoA : {cat : CDisliceCat} -> {dom, cod : CDisliceObj cat} ->
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

DsmAtoC : {0 cat : ADisliceCat} -> {0 dom, cod : ADisliceObj cat} ->
  ADisliceMorph {cat} dom cod ->
  CDisliceMorph {cat=(DscAtoC cat)} (DsoAtoC {cat} dom) (DsoAtoC {cat} cod)
DsmAtoC {cat} {dom} {cod=(ADSO _ _)} (ADSM mor inj {eq}) =
  CDSM
    (\(eb ** ed) => (eb ** mor eb ed))
    (\(eb ** ed) => rewrite eq eb ed in Refl)
    (\(eb ** ed) => Refl)

--------------------------
--------------------------
---- Dislice functors ----
--------------------------
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

export
ADSLbc : {b, b' : Type} -> {cb : SliceObj b} ->
  (m : b' -> b) -> ADSLomap (ADSC b cb) (ADSC b' (cb . m))
ADSLbc {b} {b'} {cb} m (ADSO tot inj) = ADSO (tot . m) (\eb' => inj $ m eb')

export
ADSLcbc : {b : Type} -> {cb, cb' : SliceObj b} ->
  SliceMorphism {a=b} cb' cb -> ADSLomap (ADSC b cb) (ADSC b cb')
ADSLcbc {b} {cb} {cb'} m (ADSO tot inj) =
  ADSO tot (\eb, ecb' => inj eb $ m eb ecb')

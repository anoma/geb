module LanguageDef.HelixCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.InternalProfunctor
import public LanguageDef.SlicePolyCat

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

------------------------
------------------------
---- Helix category ----
------------------------
------------------------

-----------------
---- Objects ----
-----------------

-- These four objects will be treated as a twisted-arrow morphism from
-- 'Copoly -> Poly' to 'Codirich -> Dirich' -- but with the morphisms
-- themselves unspecified, so that we can view the composite "Helix" object
-- as parametrically polymorphic in _which_ morphisms connect the component
-- objects.
--
-- When the object is used, the user will (directly or indirectly) choose
-- morphisms (if they exist -- otherwise the object _can't_ be used!)
-- `Codirich -> Copoly`, `Copoly -> Poly`, and `Poly -> Dirich`, whose
-- composite will form a morphism `Coridich -> Dirich` which completes the
-- diagram of a twisted arrow (from 'Copoly -> Poly' to 'Codirich -> Dirich').
--
-- We will sometimes call the `Codirich -> Dirich` arrow the "Dirichlet arrow",
-- the `Copoly -> Poly` arrow the "Poly(nomial) arrow", the `Coridich -> Copoly`
-- arrow the "co-assignment", and the `Poly -> Dirich` arrow the "assignment".
public export
record HelixObj where
  constructor HObj
  hCodirich : Type
  hCopoly : Type
  hPoly : Type
  hDirich : Type

public export
record HelixReqMorphs (h : HelixObj) where
  constructor HRM
  hrmCoasn : hCodirich h -> hCopoly h
  hrmPolyArr : hCopoly h -> hPoly h
  hrmAsn : hPoly h -> hDirich h

-------------------
---- Morphisms ----
-------------------

-- The seven morphisms of the underlying category which comprise a helix
-- morphism form a chain (it is acycling and unbranching), and it orders
-- the eight components of the two helix objects, so that the seven
-- morphisms and their composites specify the internal morphisms of the
-- (parametrically polymorphic) helix objects as well as four morphisms that
-- connect the two helix objects:
--
--  `hmDirich`: coDirich(dom) -> coDirich(cod)
--  `hmCopoly`: coPoly(cod) -> coPoly(dom)
--  `hmPoly`: Poly(dom) -> Poly(cod)
--  `hmDirich`: Dirich(cod) -> Dirich(dom)
public export
record HelixMor (h, h' : HelixObj) where
  constructor HMor
  hmCodirich : hCodirich h -> hCodirich h'
  hmCodCoasn : hCodirich h' -> hCopoly h'
  hmCopoly : hCopoly h' -> hCopoly h
  hmDomPolyArr : hCopoly h -> hPoly h
  hmPoly : hPoly h -> hPoly h'
  hmCodAsn : hPoly h' -> hDirich h'
  hmDirich : hDirich h' -> hDirich h

public export
hmDomCoasn : {h, h' : HelixObj} -> HelixMor h h' -> hCodirich h -> hCopoly h
hmDomCoasn {h} {h'} hm = hmCopoly hm . hmCodCoasn hm . hmCodirich hm

public export
hmCodPolyArr : {h, h' : HelixObj} -> HelixMor h h' -> hCopoly h' -> hPoly h'
hmCodPolyArr {h} {h'} hm = hmPoly hm . hmDomPolyArr hm . hmCopoly hm

public export
hmDomAsn : {h, h' : HelixObj} -> HelixMor h h' -> hPoly h -> hDirich h
hmDomAsn {h} {h'} hm = hmDirich hm . hmCodAsn hm . hmPoly hm

public export
hmCodDirichArr : {h, h' : HelixObj} ->
  HelixMor h h' -> hCodirich h' -> hDirich h'
hmCodDirichArr {h} {h'} hm = hmCodAsn hm . hmCodPolyArr hm . hmCodCoasn hm

public export
hmDomDirichArr : {h, h' : HelixObj} ->
  HelixMor h h' -> hCodirich h -> hDirich h
hmDomDirichArr {h} {h'} hm = hmDomAsn hm . hmDomPolyArr hm . hmDomCoasn hm

----------------------------
---- Category structure ----
----------------------------

public export
hmId : {h : HelixObj} -> HelixReqMorphs h -> HelixMor h h
hmId {h} hrm = HMor id (hrmCoasn hrm) id (hrmPolyArr hrm) id (hrmAsn hrm) id

public export
record HelixCompReqMorphs (dom, cod : HelixObj) where
  constructor HCRM
  hcrmCoasn : hCodirich cod -> hCopoly cod
  hcrmPolyArr : hCopoly dom -> hPoly dom
  hcrmAsn : hPoly cod -> hDirich cod

public export
hmComp : {hx, hy, hz : HelixObj} -> HelixCompReqMorphs hx hz ->
  HelixMor hy hz -> HelixMor hx hy -> HelixMor hx hz
hmComp {hx} {hy} {hz} hcrm hm' hm =
  HMor
    (hmCodirich hm' . hmCodirich hm)
    (hcrmCoasn hcrm)
    (hmCopoly hm . hmCopoly hm')
    (hcrmPolyArr hcrm)
    (hmPoly hm' . hmPoly hm)
    (hcrmAsn hcrm)
    (hmDirich hm . hmDirich hm')

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

-----------------------
-----------------------
---- Tetrafunctors ----
-----------------------
-----------------------

public export
record MLTetraFunc where
  constructor MLTF
  mltfPos : Type
  mltfDir : mltfPos -> HelixObj

public export
mltfCodirich : (mltf : MLTetraFunc) -> mltfPos mltf -> Type
mltfCodirich mltf = hCodirich . mltfDir mltf

public export
mltfCopoly : (mltf : MLTetraFunc) -> mltfPos mltf -> Type
mltfCopoly mltf = hCopoly . mltfDir mltf

public export
mltfPoly : (mltf : MLTetraFunc) -> mltfPos mltf -> Type
mltfPoly mltf = hPoly . mltfDir mltf

public export
mltfDirich : (mltf : MLTetraFunc) -> mltfPos mltf -> Type
mltfDirich mltf = hDirich . mltfDir mltf

public export
record InterpMLTF (mltf: MLTetraFunc) (h : HelixObj) where
  constructor IMLTF
  imltfPos : mltfPos mltf
  imltfDirAsn : HelixMor (mltfDir mltf imltfPos) h

public export
imltfDirich : {h : HelixObj} -> {mltf : MLTetraFunc} ->
  (el : InterpMLTF mltf h) -> hDirich h -> mltfDirich mltf (imltfPos el)
imltfDirich {h} {mltf} el = hmDirich (imltfDirAsn el)

public export
imltfPoly : {h : HelixObj} -> {mltf : MLTetraFunc} ->
  (el : InterpMLTF mltf h) -> mltfPoly mltf (imltfPos el) -> hPoly h
imltfPoly {h} {mltf} el = hmPoly (imltfDirAsn el)

public export
imltfCodirich : {h : HelixObj} -> {mltf : MLTetraFunc} ->
  (el : InterpMLTF mltf h) -> mltfCodirich mltf (imltfPos el) -> hCodirich h
imltfCodirich {h} {mltf} el = hmCodirich (imltfDirAsn el)

public export
imltfCopoly : {h : HelixObj} -> {mltf : MLTetraFunc} ->
  (el : InterpMLTF mltf h) -> hCopoly h -> mltfCopoly mltf (imltfPos el)
imltfCopoly {h} {mltf} el = hmCopoly (imltfDirAsn el)

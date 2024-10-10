module LanguageDef.RopeCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.PolyCat
import public LanguageDef.SliceFuncCat
import public LanguageDef.InternalCat
import public LanguageDef.HelixCat

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

-------------------------------
-------------------------------
---- Ropes (tetrafunctors) ----
-------------------------------
-------------------------------

public export
record MLRope where
  constructor MLR
  mlrPos : Type
  mlrDir : mlrPos -> HelixObj

public export
mlrCodirich : (mlr : MLRope) -> mlrPos mlr -> Type
mlrCodirich mlr = hCodirich . mlrDir mlr

public export
mlrCopoly : (mlr : MLRope) -> mlrPos mlr -> Type
mlrCopoly mlr = hCopoly . mlrDir mlr

public export
mlrPoly : (mlr : MLRope) -> mlrPos mlr -> Type
mlrPoly mlr = hPoly . mlrDir mlr

public export
mlrDirich : (mlr : MLRope) -> mlrPos mlr -> Type
mlrDirich mlr = hDirich . mlrDir mlr

public export
record InterpMLR (mlr: MLRope) (h : HelixObj) where
  constructor Imlr
  imlrPos : mlrPos mlr
  imlrDirAsn : HelixMor (mlrDir mlr imlrPos) h

public export
imlrDirich : {h : HelixObj} -> {mlr : MLRope} ->
  (el : InterpMLR mlr h) -> hDirich h -> mlrDirich mlr (imlrPos el)
imlrDirich {h} {mlr} el = hmDirich (imlrDirAsn el)

public export
imlrPoly : {h : HelixObj} -> {mlr : MLRope} ->
  (el : InterpMLR mlr h) -> mlrPoly mlr (imlrPos el) -> hPoly h
imlrPoly {h} {mlr} el = hmPoly (imlrDirAsn el)

public export
imlrCodirich : {h : HelixObj} -> {mlr : MLRope} ->
  (el : InterpMLR mlr h) -> mlrCodirich mlr (imlrPos el) -> hCodirich h
imlrCodirich {h} {mlr} el = hmCodirich (imlrDirAsn el)

public export
imlrCopoly : {h : HelixObj} -> {mlr : MLRope} ->
  (el : InterpMLR mlr h) -> hCopoly h -> mlrCopoly mlr (imlrPos el)
imlrCopoly {h} {mlr} el = hmCopoly (imlrDirAsn el)

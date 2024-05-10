module LanguageDef.InternalHigherCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.SlicePolyCat

---------------------------
---------------------------
---- Double categories ----
---------------------------
---------------------------

public export
IntCellSig : (obj : Type) ->
  (vmor : IntMorSig obj) -> (hmor : IntMorSig obj) ->
  Type
IntCellSig obj vmor hmor =
  (x0, x1, y0, y1 : obj) ->
  (_ : vmor x0 y0) -> (_ : vmor x1 y1) ->
  (_ : hmor x0 x1) -> (_ : hmor y0 y1) ->
  Type

public export
IntCellToV2Sig : {obj : Type} ->
  {vmor : IntMorSig obj} -> {hmor : IntMorSig obj} ->
  (_ : IntIdSig obj hmor) ->
  (cell : IntCellSig obj vmor hmor) ->
  Int2MorphSig obj vmor
IntCellToV2Sig {obj} {vmor} {hmor} hid cell x y g f =
  cell x x y y g f (hid x) (hid y)

public export
IntCellToH2Sig : {obj : Type} ->
  {vmor : IntMorSig obj} -> {hmor : IntMorSig obj} ->
  (_ : IntIdSig obj vmor) ->
  (cell : IntCellSig obj vmor hmor) ->
  Int2MorphSig obj hmor
IntCellToH2Sig {obj} {vmor} {hmor} vid cell x y =
  cell x y x y (vid x) (vid y)

public export
IntCellIdSig : {obj : Type} ->
  {vmor : IntMorSig obj} -> {hmor : IntMorSig obj} ->
  (vid : IntIdSig obj vmor) ->
  IntCellSig obj vmor hmor ->
  Type
IntCellIdSig {obj} {vmor} {hmor} vid cell =
  (x, y : obj) -> (f : hmor x y) -> cell x y x y (vid x) (vid y) f f

public export
IntCellToH2Id : {obj : Type} ->
  {vmor : IntMorSig obj} -> {hmor : IntMorSig obj} ->
  (vid : IntIdSig obj vmor) ->
  (cell : IntCellSig obj vmor hmor) ->
  IntCellIdSig {obj} {vmor} {hmor} vid cell ->
  Int2IdSig {obj} {mor=hmor} (IntCellToH2Sig {obj} {vmor} {hmor} vid cell)
IntCellToH2Id {obj} {vmor} {hmor} vid cell = id

public export
IntCellVHId : {obj : Type} ->
  {vmor : IntMorSig obj} -> {hmor : IntMorSig obj} ->
  {vid : IntIdSig obj vmor} -> {cell : IntCellSig obj vmor hmor} ->
  (hid : IntIdSig obj hmor) ->
  (cid : IntCellIdSig {obj} {vmor} {hmor} vid cell) ->
  (x : obj) -> cell x x x x (vid x) (vid x) (hid x) (hid x)
IntCellVHId {obj} {vmor} {hmor} {vid} {cell} hid cid x = cid x x (hid x)

public export
IntCellVCompSig : {obj : Type} ->
  {vmor : IntMorSig obj} -> {hmor : IntMorSig obj} ->
  (vcomp : IntCompSig obj vmor) ->
  (cell : IntCellSig obj vmor hmor) ->
  Type
IntCellVCompSig {obj} {vmor} {hmor} vcomp cell =
  {x0, x1, y0, y1, z0, z1 : obj} ->
  (vmxy0 : vmor x0 y0) -> (vmxy1 : vmor x1 y1) ->
  (vmyz0 : vmor y0 z0) -> (vmyz1 : vmor y1 z1) ->
  (hmx : hmor x0 x1) -> (hmy : hmor y0 y1) -> (hmz : hmor z0 z1) ->
  cell y0 y1 z0 z1
    vmyz0 vmyz1 hmy hmz ->
  cell x0 x1 y0 y1
    vmxy0 vmxy1 hmx hmy ->
  cell x0 x1 z0 z1
    (vcomp x0 y0 z0 vmyz0 vmxy0) (vcomp x1 y1 z1 vmyz1 vmxy1) hmx hmz

public export
IntCellHCompSig : {obj : Type} ->
  {vmor : IntMorSig obj} -> {hmor : IntMorSig obj} ->
  (hcomp : IntCompSig obj hmor) ->
  (cell : IntCellSig obj vmor hmor) ->
  Type
IntCellHCompSig {obj} {vmor} {hmor} hcomp cell =
  {x0, x1, x2, y0, y1, y2 : obj} ->
  (vmxy0 : vmor x0 y0) -> (vmxy1 : vmor x1 y1) -> (vmxy2 : vmor x2 y2) ->
  (hmx01 : hmor x0 x1) -> (hmx12 : hmor x1 x2) ->
  (hmy01 : hmor y0 y1) -> (hmy12 : hmor y1 y2) ->
  cell x1 x2 y1 y2
    vmxy1 vmxy2 hmx12 hmy12 ->
  cell x0 x1 y0 y1
    vmxy0 vmxy1 hmx01 hmy01 ->
  cell x0 x2 y0 y2
    vmxy0 vmxy2 (hcomp x0 x1 x2 hmx12 hmx01) (hcomp y0 y1 y2 hmy12 hmy01)

public export
IntCellTo2MorSig : {obj : Type} ->
  {vmor : IntMorSig obj} -> {hmor : IntMorSig obj} ->
  (vcomp : IntCompSig obj vmor) ->
  (cell : IntCellSig obj vmor hmor) ->
  (vid : IntIdSig obj vmor) ->
  Type
IntCellTo2MorSig {obj} {vmor} {hmor} vcomp cell vid =
  (x, y : obj) -> (f, g : hmor x y) ->
  cell x y x y
    (vcomp x x x (vid x) (vid x))
    (vcomp y y y (vid y) (vid y))
    f g ->
  cell x y x y
    (vid x)
    (vid y)
    f g

public export
IntCellTo2VComp : {obj : Type} ->
  {vmor : IntMorSig obj} -> {hmor : IntMorSig obj} ->
  {cell : IntCellSig obj vmor hmor} ->
  (vid : IntIdSig obj vmor) ->
  (vcomp : IntCompSig obj vmor) ->
  (c2m : IntCellTo2MorSig {obj} {vmor} {hmor} vcomp cell vid) ->
  (_ : IntCellVCompSig {obj} {vmor} {hmor} vcomp cell) ->
  Int2VCompSig {obj} {mor=hmor} (IntCellToH2Sig {obj} {vmor} {hmor} vid cell)
IntCellTo2VComp vid vcomp c2m cvcomp x y f g h beta alpha =
  c2m x y f h $ cvcomp (vid x) (vid y) (vid x) (vid y) f g h beta alpha

public export
IntCellTo2WhiskerL : {obj : Type} ->
  {vmor : IntMorSig obj} -> {hmor : IntMorSig obj} ->
  {hcomp : IntCompSig obj hmor} ->
  (vid : IntIdSig obj vmor) ->
  (cell : IntCellSig obj vmor hmor) ->
  (cid : IntCellIdSig {obj} {vmor} {hmor} vid cell) ->
  (_ : IntCellHCompSig {obj} {vmor} {hmor} hcomp cell) ->
  Int2WhiskerLSig {obj} {mor=hmor}
    hcomp (IntCellToH2Sig {obj} {vmor} {hmor} vid cell)
IntCellTo2WhiskerL {vmor} {hmor} {hcomp} vid cell cid chcomp x y f z g g' =
  flip (chcomp (vid x) (vid y) (vid z) f g f g') $ cid x y f

public export
IntCellTo2WhiskerR : {obj : Type} ->
  {vmor : IntMorSig obj} -> {hmor : IntMorSig obj} ->
  {hcomp : IntCompSig obj hmor} ->
  (vid : IntIdSig obj vmor) ->
  (cell : IntCellSig obj vmor hmor) ->
  (cid : IntCellIdSig {obj} {vmor} {hmor} vid cell) ->
  (_ : IntCellHCompSig {obj} {vmor} {hmor} hcomp cell) ->
  Int2WhiskerRSig {obj} {mor=hmor}
    hcomp (IntCellToH2Sig {obj} {vmor} {hmor} vid cell)
IntCellTo2WhiskerR {vmor} {hmor} {hcomp} vid cell cid chcomp y z g x f f' =
  chcomp (vid x) (vid y) (vid z) f g f' g $ cid y z g

public export
IntCellTo2HComp : {obj : Type} ->
  {vmor : IntMorSig obj} -> {hmor : IntMorSig obj} ->
  {hcomp : IntCompSig obj hmor} ->
  (vid : IntIdSig obj vmor) ->
  (cell : IntCellSig obj vmor hmor) ->
  (_ : IntCellHCompSig {obj} {vmor} {hmor} hcomp cell) ->
  Int2HCompSig {obj} {mor=hmor}
    hcomp (IntCellToH2Sig {obj} {vmor} {hmor} vid cell)
IntCellTo2HComp {obj} {vmor} {hmor} {hcomp} vid cell chcomp x z y f f' g g' =
  chcomp (vid x) (vid y) (vid z) f g f' g'

public export
record IntDblCatSig where
  constructor IDCat
  idcObj : Type
  idcVmics : MorIdCompSig idcObj
  idcHmics : MorIdCompSig idcObj
  idcCell : IntCellSig idcObj (micsMor idcVmics) (micsMor idcHmics)
  idcCid : IntCellIdSig (micsId idcVmics) idcCell
  idcCvcomp : IntCellVCompSig (micsComp idcVmics) idcCell
  idcChcomp : IntCellHCompSig (micsComp idcHmics) idcCell
  idcC2m : IntCellTo2MorSig (micsComp idcVmics) idcCell (micsId idcVmics)

public export
idcVcat : IntDblCatSig -> IntCatSig
idcVcat idc = ICat (idcObj idc) (idcVmics idc)

public export
idcVmor : (idc : IntDblCatSig) -> IntMorSig (idcObj idc)
idcVmor idc = icMor (idcVcat idc)

public export
idcVid : (idc : IntDblCatSig) -> IntIdSig (idcObj idc) (idcVmor idc)
idcVid idc = icId (idcVcat idc)

public export
idcVcomp : (idc : IntDblCatSig) -> IntCompSig (idcObj idc) (idcVmor idc)
idcVcomp idc = icComp (idcVcat idc)

public export
idcHcat : IntDblCatSig -> IntCatSig
idcHcat idc = ICat (idcObj idc) (idcHmics idc)

public export
idcHmor : (idc : IntDblCatSig) -> IntMorSig (idcObj idc)
idcHmor idc = icMor (idcHcat idc)

public export
idcHid : (idc : IntDblCatSig) -> IntIdSig (idcObj idc) (idcHmor idc)
idcHid idc = icId (idcHcat idc)

public export
idcHcomp : (idc : IntDblCatSig) -> IntCompSig (idcObj idc) (idcHmor idc)
idcHcomp idc = icComp (idcHcat idc)

public export
idc2mics : (idc : IntDblCatSig) -> (dom, cod : idcObj idc) ->
  MorIdCompSig (idcHmor idc dom cod)
idc2mics idc dom cod =
  MICS
    (\f, g => IntCellToH2Sig (idcVid idc) (idcCell idc) dom cod f g)
  $ ICS
    (IntCellToH2Id (idcVid idc) (idcCell idc) (idcCid idc) dom cod)
    (\f, g, h, beta, alpha =>
      IntCellTo2VComp
        (idcVid idc) (idcVcomp idc) (idcC2m idc) (idcCvcomp idc)
        dom cod f g h beta alpha)

public export
idc2cat : IntDblCatSig -> Int2CatSig
idc2cat idc =
  I2Cat
    (idcHcat idc)
  $ I2CS
    (idc2mics idc)
    (\c, d, e, f =>
      IntCellTo2WhiskerL
        (idcVid idc) (idcCell idc) (idcCid idc) (idcChcomp idc)
        c d f e)
    (\c, d, e, f =>
      IntCellTo2WhiskerR
        (idcVid idc) (idcCell idc) (idcCid idc) (idcChcomp idc)
        d e f c)

module LanguageDef.IntUCofamCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.IntArena
import public LanguageDef.IntEFamCat

-----------------
-----------------
---- Objects ----
-----------------
-----------------

public export
IntUCofamObj : Type -> Type
IntUCofamObj = IntArena

public export
ICFUO : {0 c : Type} -> (idx : Type) -> (idx -> c) -> IntUCofamObj c
ICFUO {c} idx obj = (idx ** obj)

public export
icfuoIdx : {0 c : Type} -> IntUCofamObj c -> Type
icfuoIdx {c} = DPair.fst {a=Type} {p=(ContravarHomFunc c)}

public export
icfuoObj : {0 c : Type} -> (uf : IntUCofamObj c) -> icfuoIdx {c} uf -> c
icfuoObj {c} = DPair.snd {a=Type} {p=(ContravarHomFunc c)}

-------------------
-------------------
---- Morphisms ----
-------------------
-------------------

-- Morphisms of the category of universal cofamilies of objects from a given
-- category.  (A "cofamily" of objects from `c` is simply a family of objects
-- from the opposite of `c`; see `IntUFamCat` for the notion of "universal
-- family".)
public export
IntUCofamMor : {c : Type} -> (mor : IntDifunctorSig c) ->
  (dom, cod : IntUCofamObj c) -> Type
IntUCofamMor {c} mor dom cod =
  (onidx : icfuoIdx cod -> icfuoIdx dom **
   (ci : icfuoIdx cod) -> mor (icfuoObj cod ci) (icfuoObj dom $ onidx ci))

-- Note that this category is the opposite category of
-- the category of existential families (AKA Dirichlet functors).
export
IntUCofamIsOpEFam : {c : Type} -> (mor : IntDifunctorSig c) ->
  (dom, cod : IntUCofamObj c) ->
  IntUCofamMor {c} mor dom cod = IntEFamMor {c} mor cod dom
IntUCofamIsOpEFam {c} mor dom cod = Refl

public export
icfum : {c : Type} -> {mor : IntDifunctorSig c} -> {dom, cod : IntUCofamObj c} ->
  (onidx : icfuoIdx cod -> icfuoIdx dom) ->
  (onobj : (ci : icfuoIdx cod) ->
    mor (icfuoObj cod ci) (icfuoObj dom $ onidx ci)) ->
  IntUCofamMor {c} mor dom cod
icfum {c} {mor} {dom} {cod} onidx onobj = (onidx ** onobj)

public export
icfumOnIdx : {c : Type} -> {mor : IntDifunctorSig c} ->
  {dom, cod : IntUCofamObj c} -> IntUCofamMor {c} mor dom cod ->
  (icfuoIdx cod -> icfuoIdx dom)
icfumOnIdx = DPair.fst

public export
icfumOnObj : {c : Type} -> {mor : IntDifunctorSig c} ->
  {dom, cod : IntUCofamObj c} -> (m : IntUCofamMor {c} mor dom cod) ->
  (ci : icfuoIdx cod) ->
  mor (icfuoObj cod ci) (icfuoObj dom $ icfumOnIdx {mor} {dom} {cod} m ci)
icfumOnObj = DPair.snd

public export
icfumId : {c : Type} -> (mor : IntDifunctorSig c) -> (cid : IntIdSig c mor) ->
  (obj : IntUCofamObj c) -> IntUCofamMor mor obj obj
icfumId {c} mor cid =
  IntOpCatId (IntEFamObj c) (IntEFamMor {c} mor) (ifemId {c} mor cid)

public export
icfumComp : {c : Type} ->
  (mor : IntDifunctorSig c) -> (comp : IntComp c mor) ->
  {x, y, z : IntUCofamObj c} ->
  IntUCofamMor mor y z ->
  IntUCofamMor mor x y ->
  IntUCofamMor mor x z
icfumComp {c} mor comp {x} {y} {z} =
  IntOpCatComp
    (IntEFamObj c)
    (IntEFamMor {c} mor)
    (\_, _, _ => ifemComp {c} mor comp)
    x y z

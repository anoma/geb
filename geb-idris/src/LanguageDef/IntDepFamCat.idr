module LanguageDef.IntDepFamCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.InternalProfunctor
import public LanguageDef.IntArena
import public LanguageDef.IntUFamCat
import public LanguageDef.IntEFamCat
import public LanguageDef.IntUCofamCat
import public LanguageDef.IntECofamCat

-----------------
-----------------
---- Objects ----
-----------------
-----------------

public export
IntDepFamObj : Type -> Type
IntDepFamObj = IntArena

public export
IDFO : {c : Type} -> (idx : Type) -> (idx -> c) -> IntDepFamObj c
IDFO {c} idx obj = (idx ** obj)

public export
idfoIdx : {c : Type} -> IntDepFamObj c -> Type
idfoIdx {c} = DPair.fst {a=Type} {p=(ContravarHomFunc c)}

public export
idfoObj : {c : Type} -> (uf : IntDepFamObj c) -> idfoIdx {c} uf -> c
idfoObj {c} = DPair.snd {a=Type} {p=(ContravarHomFunc c)}

-------------------------------
-------------------------------
---- Predicates on objects ----
-------------------------------
-------------------------------

public export
IDFsigma : {c : Type} -> SliceObj c -> IntDepFamObj c -> Type
IDFsigma {c} sl idf = Sigma {a=(idfoIdx idf)} (sl . idfoObj idf)

public export
IDFpi : {c : Type} -> SliceObj c -> IntDepFamObj c -> Type
IDFpi {c} sl idf = Pi {a=(idfoIdx idf)} (sl . idfoObj idf)

-------------------
-------------------
---- Morphisms ----
-------------------
-------------------

---------------------
---- Existential ----
---------------------

public export
IntEDepFamMorOnIdxFst : {c : Type} -> SliceObj c ->
  (dom, cod : IntDepFamObj c) -> Type
IntEDepFamMorOnIdxFst {c} sl dom cod =
  (i : idfoIdx dom) -> sl (idfoObj dom i) -> idfoIdx cod

public export
IntEDepFamMorOnIdxSnd : {c : Type} ->
  {mor : IntDifunctorSig c} -> {sl : SliceObj c} ->
  {dom, cod : IntDepFamObj c} ->
  IntEDepFamMorOnIdxFst {c} sl dom cod -> Type
IntEDepFamMorOnIdxSnd {c} {mor} {sl} {dom} {cod} onidx =
  (di : idfoIdx dom) ->
  (dd : sl (idfoObj dom di)) -> sl (idfoObj cod $ onidx di dd)

public export
IntEDepFamMorOnIdx : {c : Type} -> (mor : IntDifunctorSig c) -> SliceObj c ->
  (dom, cod : IntDepFamObj c) -> Type
IntEDepFamMorOnIdx {c} mor sl dom cod =
  Sigma
    {a=(IntEDepFamMorOnIdxFst {c} sl dom cod)}
    (IntEDepFamMorOnIdxSnd {c} {mor} {sl} {dom} {cod})

public export
IntEDepFamMorOnMor : {c : Type} ->
  {mor : IntDifunctorSig c} -> {sl : SliceObj c} ->
  {dom, cod : IntDepFamObj c} ->
  (onidx : IntEDepFamMorOnIdx {c} mor sl dom cod) ->
  Type
IntEDepFamMorOnMor {c} {mor} {sl} {dom} {cod} onidx =
  ?IntEDepFamMorOnMor_hole

public export
IntEDepFamMor : {c : Type} -> (mor : IntDifunctorSig c) -> SliceObj c ->
  (dom, cod : IntDepFamObj c) -> Type
IntEDepFamMor {c} mor sl dom cod =
  Sigma
    {a=(IntEDepFamMorOnIdx {c} mor sl dom cod)}
    (IntEDepFamMorOnMor {c} {mor} {sl} {dom} {cod})

-------------------
---- Universal ----
-------------------

public export
IntUDepFamMorOnIdxFst : {c : Type} -> SliceObj c ->
  (dom, cod : IntDepFamObj c) -> Type
IntUDepFamMorOnIdxFst {c} sl dom cod =
  IntEDepFamMorOnIdxFst {c=(IntOpCatObj c)} sl cod dom

public export
IntUDepFamMorOnIdxSnd : {c : Type} ->
  {mor : IntDifunctorSig c} -> {sl : SliceObj c} ->
  {dom, cod : IntDepFamObj c} ->
  IntUDepFamMorOnIdxFst {c} sl dom cod -> Type
IntUDepFamMorOnIdxSnd {c} {mor} {sl} {dom} {cod} =
  IntEDepFamMorOnIdxSnd
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {sl}
    {dom=cod}
    {cod=dom}

public export
IntUDepFamMorOnIdx : {c : Type} -> (mor : IntDifunctorSig c) -> SliceObj c ->
  (dom, cod : IntDepFamObj c) -> Type
IntUDepFamMorOnIdx {c} mor sl dom cod =
  IntEDepFamMorOnIdx {c=(IntOpCatObj c)} (IntOpCatMor c mor) sl cod dom

public export
IntUDepFamMorOnMor : {c : Type} ->
  {mor : IntDifunctorSig c} -> {sl : SliceObj c} ->
  {dom, cod : IntDepFamObj c} ->
  (onidx : IntUDepFamMorOnIdx {c} mor sl dom cod) ->
  Type
IntUDepFamMorOnMor {c} {mor} {sl} {dom} {cod} =
  IntEDepFamMorOnMor
    {c=(IntOpCatObj c)}
    {mor=(IntOpCatMor c mor)}
    {sl}
    {dom=cod}
    {cod=dom}

public export
IntUDepFamMor : {c : Type} -> (mor : IntDifunctorSig c) -> SliceObj c ->
  (dom, cod : IntDepFamObj c) -> Type
IntUDepFamMor {c} mor sl dom cod =
  IntEDepFamMor {c=(IntOpCatObj c)} (IntOpCatMor c mor) sl cod dom

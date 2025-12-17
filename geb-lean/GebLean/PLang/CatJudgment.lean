/-!
# Categorical Judgments for PLang

This module defines the copresheaf of judgments about categories.
-/

namespace GebLean

namespace PLang

def ObjCopr.{u} : Type u := Sort u

def ObjMorObj.{u, v} : Type (max u v) := ObjCopr.{u} × Sort v

def ObjMorProj.{u, v} (om : ObjMorObj.{u, v}) : Sort (imax v u) := om.2 → om.1

def ObjMorMor.{u, v} (om : ObjMorObj.{u + 1, v + 1}) : Type (max u v) :=
  ObjMorProj.{u + 1, v + 1} om × ObjMorProj.{u + 1,v + 1} om

def ObjMorCopr.{u, v} : Type (max u v + 1) :=
  Σ (o : ObjMorObj.{u + 1, v + 1}), ObjMorMor.{u, v} o

def ObjMorIdObj.{u, v, w} : Type (max u v w) :=
  ObjMorObj.{u, v} × Sort w

def IdProj.{u, v, w} (omi : ObjMorIdObj.{u, v, w}) : Sort (imax w v) :=
  omi.2 → omi.1.2

def ObjMorIdMor.{u, v, w} (omi : ObjMorIdObj.{u + 1, v + 1, w + 1}) :
  Type (max u v w) :=
    ObjMorMor.{u, v} omi.1 × IdProj.{u + 1, v + 1, w + 1} omi

def ObjMorIdObjMor.{u, v, w} : Type (max u v w + 1) :=
  Σ (omi : ObjMorIdObj.{u + 1, v + 1, w + 1}), ObjMorIdMor.{u, v, w} omi

def ObjMorIdObjMorEndo.{u, v, w} (omim : ObjMorIdObjMor.{u, v, w} ) : Prop :=
  omim.2.1.1 ∘ omim.2.2 = omim.2.1.2 ∘ omim.2.2

def ObjMorIdCopr.{u, v, w} : Type (max u v w + 1) :=
  {omim : ObjMorIdObjMor.{u, v, w} // ObjMorIdObjMorEndo.{u, v, w} omim}

def ObjMorCompObj.{u, v, w} : Type (max u v w) :=
  ObjMorObj.{u, v} × Sort w

def CompProj.{u, v, w} (om : ObjMorCompObj.{u, v, w}) : Sort (imax w v) :=
  om.2 → om.1.2

def ObjMorCompProj.{u, v, w} (omi : ObjMorCompObj.{u + 1, v + 1, w + 1}) :
  Type (max v w) :=
    CompProj.{u + 1, v + 1, w + 1} omi × -- .1 = left
    CompProj.{u + 1, v + 1, w + 1} omi × -- .2.1 = right
    CompProj.{u + 1, v + 1, w + 1} omi   -- .2.2 = composite

def ObjMorCompMor.{u, v, w} (omi : ObjMorCompObj.{u + 1, v + 1, w + 1}) :
  Type (max u v w) :=
    ObjMorMor.{u, v} omi.1 × ObjMorCompProj.{u, v, w} omi

def ObjMorCompObjMor.{u, v, w} : Type (max u v w + 1) :=
  Σ (omc : ObjMorCompObj.{u + 1, v + 1, w + 1}), ObjMorCompMor.{u, v, w} omc

def ObjMorCompObjMorMatch.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) : Prop :=
  omcm.2.1.2 ∘ omcm.2.2.2.1 = omcm.2.1.1 ∘ omcm.2.2.1

def ObjMorCompObjMorCompDom.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) : Prop :=
  omcm.2.1.1 ∘ omcm.2.2.2.2 = omcm.2.1.1 ∘ omcm.2.2.2.1

def ObjMorCompObjMorCompCod.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) : Prop :=
  omcm.2.1.2 ∘ omcm.2.2.2.2 = omcm.2.1.2 ∘ omcm.2.2.1

def ObjMorCompObjMorCond.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) : Prop :=
  ObjMorCompObjMorMatch.{u, v, w} omcm ∧
  ObjMorCompObjMorCompDom.{u, v, w} omcm ∧
  ObjMorCompObjMorCompCod.{u, v, w} omcm

def ObjMorCompCopr.{u, v, w} : Type (max u v w + 1) :=
  {omim : ObjMorCompObjMor.{u, v, w} // ObjMorCompObjMorCond.{u, v, w} omim}

def CatJudgObj.{u, v, w, x} : Type (max u v w x) :=
  ObjMorObj.{u, v} × (Sort w × Sort x)

def CatJudgMor.{u, v, w, x} (cjo : CatJudgObj.{u + 1, v + 1, w + 1, x + 1}) :
    Type (max u v w x) :=
  ObjMorMor.{u, v} cjo.1 ×
  IdProj.{u + 1, v + 1, w + 1} (cjo.1, cjo.2.1) ×
  ObjMorCompProj.{u, v, x} (cjo.1, cjo.2.2)

def CatJudgObjMor.{u, v, w, x} : Type (max u v w x + 1) :=
  Σ (cjo : CatJudgObj.{u + 1, v + 1, w + 1, x + 1}), CatJudgMor.{u, v, w, x} cjo

def CatJudgObjMorCond.{u, v, w, x} (cjom : CatJudgObjMor.{u, v, w, x}) : Prop :=
  ObjMorIdObjMorEndo.{u, v, w} ⟨ ⟨cjom.1.1, cjom.1.2.1⟩, ⟨cjom.2.1, cjom.2.2.1⟩⟩ ∧
  ObjMorCompObjMorCond.{u, v, x} ⟨ ⟨cjom.1.1, cjom.1.2.2⟩, ⟨cjom.2.1, cjom.2.2.2⟩⟩

end PLang

end GebLean

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

def IdProj.{u, v, w} (om : ObjMorObj.{u, v}) (i : Sort w) : Sort (imax w v) :=
  i → om.2

def ObjMorIdObj.{u, v, w} : Type (max u v w) :=
  ObjMorObj.{u, v} × Sort w

def ObjMorIdMor.{u, v, w} (omi : ObjMorIdObj.{u + 1, v + 1, w + 1}) :
  Type (max u v w) :=
    ObjMorMor.{u, v} omi.1 × IdProj.{u + 1, v + 1, w + 1} omi.1 omi.2

def ObjMorIdObjMor.{u, v, w} : Type (max u v w + 1) :=
  Σ (omi : ObjMorIdObj.{u + 1, v + 1, w + 1}), ObjMorIdMor.{u, v, w} omi

def ObjMorIdObjMorEndo.{u, v, w} (omim : ObjMorIdObjMor.{u, v, w} ) : Prop :=
  omim.2.1.1 ∘ omim.2.2 = omim.2.1.2 ∘ omim.2.2

def ObjMorIdCopr.{u, v, w} : Type (max u v w + 1) :=
  {omim : ObjMorIdObjMor.{u, v, w} // ObjMorIdObjMorEndo.{u, v, w} omim}

def CompProj.{u, v, w} (om : ObjMorObj.{u, v}) (i : Sort w) : Sort (imax w v) :=
  i → om.2

def ObjMorCompObj.{u, v, w} : Type (max u v w) :=
  ObjMorObj.{u, v} × Sort w

def ObjMorCompMor.{u, v, w} (omi : ObjMorIdObj.{u + 1, v + 1, w + 1}) :
  Type (max u v w) :=
    ObjMorMor.{u, v} omi.1 ×
    (CompProj.{u + 1, v + 1, w + 1} omi.1 omi.2 × -- .1 = left
     CompProj.{u + 1, v + 1, w + 1} omi.1 omi.2 × -- .2 = right
     CompProj.{u + 1, v + 1, w + 1} omi.1 omi.2)  -- .3 = composite

end PLang

end GebLean

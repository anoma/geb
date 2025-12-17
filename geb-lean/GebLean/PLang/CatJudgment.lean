/-!
# Categorical Judgments for PLang

This module defines the copresheaf of judgments about categories.
-/

namespace GebLean

namespace PLang

namespace Obj

/-- The type of objects in a category-judgment copresheaf. -/
def ObjCopr.{u} : Type u := Sort u

/-- A pair consisting of an object type and a morphism type.
    The first component is the type of objects, the second is the type
    of morphisms. -/
def ObjMorObj.{u, v} : Type (max u v) := ObjCopr.{u} × Sort v

/-- Access the object type from an ObjMorObj pair. -/
abbrev ObjMorObj.obj.{u, v} (om : ObjMorObj.{u, v}) : Sort u := om.1

/-- Access the morphism type from an ObjMorObj pair. -/
abbrev ObjMorObj.mor.{u, v} (om : ObjMorObj.{u, v}) : Sort v := om.2

/-- The type of a projection function from morphisms to objects.
    Used for domain and codomain functions. -/
def ObjMorProj.{u, v} (om : ObjMorObj.{u, v}) : Sort (imax v u) := om.mor → om.obj

/-- A pair of projection functions (domain and codomain) for a given
    object-morphism pair. -/
def ObjMorMor.{u, v} (om : ObjMorObj.{u + 1, v + 1}) : Type (max u v) :=
  ObjMorProj.{u + 1, v + 1} om × ObjMorProj.{u + 1, v + 1} om

/-- Access the domain function from an ObjMorMor pair. -/
abbrev ObjMorMor.dom.{u, v} {om : ObjMorObj.{u + 1, v + 1}}
    (omm : ObjMorMor.{u, v} om) : ObjMorProj om := omm.1

/-- Access the codomain function from an ObjMorMor pair. -/
abbrev ObjMorMor.cod.{u, v} {om : ObjMorObj.{u + 1, v + 1}}
    (omm : ObjMorMor.{u, v} om) : ObjMorProj om := omm.2

/-- A quiver copresheaf: object type, morphism type, domain and codomain
    functions bundled together. This is the base layer before adding
    identity and composition structure. -/
def ObjMorCopr.{u, v} : Type (max u v + 1) :=
  Σ (o : ObjMorObj.{u + 1, v + 1}), ObjMorMor.{u, v} o

/-- Access the object-morphism pair from a quiver copresheaf. -/
abbrev ObjMorCopr.objMor.{u, v} (omc : ObjMorCopr.{u, v}) :
    ObjMorObj.{u + 1, v + 1} := omc.1

/-- Access the object type from a quiver copresheaf. -/
abbrev ObjMorCopr.obj.{u, v} (omc : ObjMorCopr.{u, v}) : Type u := omc.objMor.obj

/-- Access the morphism type from a quiver copresheaf. -/
abbrev ObjMorCopr.mor.{u, v} (omc : ObjMorCopr.{u, v}) : Type v := omc.objMor.mor

/-- Access the domain/codomain pair from a quiver copresheaf. -/
abbrev ObjMorCopr.domCod.{u, v} (omc : ObjMorCopr.{u, v}) :
    ObjMorMor.{u, v} omc.objMor := omc.2

/-- Access the domain function from a quiver copresheaf. -/
abbrev ObjMorCopr.dom.{u, v} (omc : ObjMorCopr.{u, v}) : omc.mor → omc.obj :=
  ObjMorMor.dom omc.domCod

/-- Access the codomain function from a quiver copresheaf. -/
abbrev ObjMorCopr.cod.{u, v} (omc : ObjMorCopr.{u, v}) : omc.mor → omc.obj :=
  ObjMorMor.cod omc.domCod

/-- A triple consisting of an object-morphism pair and an identity witness type.
    The identity witness type represents "proofs" that a morphism is an identity. -/
def ObjMorIdObj.{u, v, w} : Type (max u v w) :=
  ObjMorObj.{u, v} × Sort w

/-- Access the object-morphism pair from an identity object. -/
abbrev ObjMorIdObj.objMor.{u, v, w} (omi : ObjMorIdObj.{u, v, w}) :
    ObjMorObj.{u, v} := omi.1

/-- Access the object type from an identity object. -/
abbrev ObjMorIdObj.obj.{u, v, w} (omi : ObjMorIdObj.{u, v, w}) :
    Sort u := omi.objMor.obj

/-- Access the morphism type from an identity object. -/
abbrev ObjMorIdObj.mor.{u, v, w} (omi : ObjMorIdObj.{u, v, w}) :
    Sort v := omi.objMor.mor

/-- Access the identity witness type from an identity object. -/
abbrev ObjMorIdObj.idType.{u, v, w} (omi : ObjMorIdObj.{u, v, w}) :
    Sort w := omi.2

/-- The type of a function from identity witnesses to morphisms.
    Given an identity witness, returns the morphism that is the identity. -/
def IdProj.{u, v, w} (omi : ObjMorIdObj.{u, v, w}) : Sort (imax w v) :=
  omi.idType → omi.mor

/-- The morphism data for an identity structure: domain/codomain functions
    plus a function assigning identity morphisms to identity witnesses. -/
def ObjMorIdMor.{u, v, w} (omi : ObjMorIdObj.{u + 1, v + 1, w + 1}) :
  Type (max u v w) :=
    ObjMorMor.{u, v} omi.objMor × IdProj.{u + 1, v + 1, w + 1} omi

/-- Access the domain/codomain pair from identity morphism data. -/
abbrev ObjMorIdMor.domCod.{u, v, w} {omi : ObjMorIdObj.{u + 1, v + 1, w + 1}}
    (omim : ObjMorIdMor.{u, v, w} omi) : ObjMorMor.{u, v} omi.objMor := omim.1

/-- Access the domain function from identity morphism data. -/
abbrev ObjMorIdMor.dom.{u, v, w} {omi : ObjMorIdObj.{u + 1, v + 1, w + 1}}
    (omim : ObjMorIdMor.{u, v, w} omi) : ObjMorProj omi.objMor :=
  ObjMorMor.dom omim.domCod

/-- Access the codomain function from identity morphism data. -/
abbrev ObjMorIdMor.cod.{u, v, w} {omi : ObjMorIdObj.{u + 1, v + 1, w + 1}}
    (omim : ObjMorIdMor.{u, v, w} omi) : ObjMorProj omi.objMor :=
  ObjMorMor.cod omim.domCod

/-- Access the identity morphism assignment function. -/
abbrev ObjMorIdMor.idMor.{u, v, w} {omi : ObjMorIdObj.{u + 1, v + 1, w + 1}}
    (omim : ObjMorIdMor.{u, v, w} omi) : IdProj omi := omim.2

/-- Bundled identity data: object type, morphism type, identity witness type,
    domain/codomain functions, and identity morphism assignment.
    This is the full data before imposing the endomorphism condition. -/
def ObjMorIdObjMor.{u, v, w} : Type (max u v w + 1) :=
  Σ (omi : ObjMorIdObj.{u + 1, v + 1, w + 1}), ObjMorIdMor.{u, v, w} omi

/-- Access the identity object from bundled identity data. -/
abbrev ObjMorIdObjMor.objMorIdObj.{u, v, w} (omim : ObjMorIdObjMor.{u, v, w}) :
    ObjMorIdObj.{u + 1, v + 1, w + 1} := omim.1

/-- Access the identity morphism data from bundled identity data. -/
abbrev ObjMorIdObjMor.objMorIdMor.{u, v, w} (omim : ObjMorIdObjMor.{u, v, w}) :
    ObjMorIdMor.{u, v, w} omim.objMorIdObj := omim.2

/-- Access the object type from bundled identity data. -/
abbrev ObjMorIdObjMor.obj.{u, v, w} (omim : ObjMorIdObjMor.{u, v, w}) :
    Type u := omim.objMorIdObj.obj

/-- Access the morphism type from bundled identity data. -/
abbrev ObjMorIdObjMor.mor.{u, v, w} (omim : ObjMorIdObjMor.{u, v, w}) :
    Type v := omim.objMorIdObj.mor

/-- Access the identity witness type from bundled identity data. -/
abbrev ObjMorIdObjMor.idType.{u, v, w} (omim : ObjMorIdObjMor.{u, v, w}) :
    Type w := omim.objMorIdObj.idType

/-- Access the domain function from bundled identity data. -/
abbrev ObjMorIdObjMor.dom.{u, v, w} (omim : ObjMorIdObjMor.{u, v, w}) :
    omim.mor → omim.obj := ObjMorIdMor.dom omim.objMorIdMor

/-- Access the codomain function from bundled identity data. -/
abbrev ObjMorIdObjMor.cod.{u, v, w} (omim : ObjMorIdObjMor.{u, v, w}) :
    omim.mor → omim.obj := ObjMorIdMor.cod omim.objMorIdMor

/-- Access the identity morphism function from bundled identity data. -/
abbrev ObjMorIdObjMor.idMor.{u, v, w} (omim : ObjMorIdObjMor.{u, v, w}) :
    omim.idType → omim.mor := ObjMorIdMor.idMor omim.objMorIdMor

/-- The condition that identity morphisms are endomorphisms: for each identity
    witness, the domain and codomain of the identity morphism are equal. -/
def ObjMorIdObjMorEndo.{u, v, w} (omim : ObjMorIdObjMor.{u, v, w}) : Prop :=
  omim.dom ∘ omim.idMor = omim.cod ∘ omim.idMor

/-- A quiver with identity structure satisfying the endomorphism condition.
    This is a subtype ensuring identity morphisms are endomorphisms. -/
def ObjMorIdCopr.{u, v, w} : Type (max u v w + 1) :=
  {omim : ObjMorIdObjMor.{u, v, w} // ObjMorIdObjMorEndo.{u, v, w} omim}

/-- Access the underlying identity data from an identity copresheaf. -/
abbrev ObjMorIdCopr.data.{u, v, w} (omic : ObjMorIdCopr.{u, v, w}) :
    ObjMorIdObjMor.{u, v, w} := omic.val

/-- Access the endomorphism proof from an identity copresheaf. -/
abbrev ObjMorIdCopr.endoProof.{u, v, w} (omic : ObjMorIdCopr.{u, v, w}) :
    ObjMorIdObjMorEndo omic.data := omic.property

/-- A triple consisting of an object-morphism pair and a composition witness type.
    The composition witness type represents "proofs" that a triple of morphisms
    form a valid composition (left ∘ right = composite). -/
def ObjMorCompObj.{u, v, w} : Type (max u v w) :=
  ObjMorObj.{u, v} × Sort w

/-- Access the object-morphism pair from a composition object. -/
abbrev ObjMorCompObj.objMor.{u, v, w} (omc : ObjMorCompObj.{u, v, w}) :
    ObjMorObj.{u, v} := omc.1

/-- Access the object type from a composition object. -/
abbrev ObjMorCompObj.obj.{u, v, w} (omc : ObjMorCompObj.{u, v, w}) :
    Sort u := omc.objMor.obj

/-- Access the morphism type from a composition object. -/
abbrev ObjMorCompObj.mor.{u, v, w} (omc : ObjMorCompObj.{u, v, w}) :
    Sort v := omc.objMor.mor

/-- Access the composition witness type from a composition object. -/
abbrev ObjMorCompObj.compType.{u, v, w} (omc : ObjMorCompObj.{u, v, w}) :
    Sort w := omc.2

/-- The type of a function from composition witnesses to morphisms.
    Given a composition witness, returns one of the three morphisms involved. -/
def CompProj.{u, v, w} (om : ObjMorCompObj.{u, v, w}) : Sort (imax w v) :=
  om.compType → om.mor

/-- A triple of projection functions for composition: left morphism (post-composed),
    right morphism (pre-composed), and the resulting composite. -/
def ObjMorCompProj.{u, v, w} (omi : ObjMorCompObj.{u + 1, v + 1, w + 1}) :
  Type (max v w) :=
    CompProj.{u + 1, v + 1, w + 1} omi ×
    CompProj.{u + 1, v + 1, w + 1} omi ×
    CompProj.{u + 1, v + 1, w + 1} omi

/-- Access the left morphism projection (the morphism being post-composed). -/
abbrev ObjMorCompProj.left.{u, v, w} {omi : ObjMorCompObj.{u + 1, v + 1, w + 1}}
    (ocp : ObjMorCompProj.{u, v, w} omi) : CompProj omi := ocp.1

/-- Access the right morphism projection (the morphism being pre-composed). -/
abbrev ObjMorCompProj.right.{u, v, w} {omi : ObjMorCompObj.{u + 1, v + 1, w + 1}}
    (ocp : ObjMorCompProj.{u, v, w} omi) : CompProj omi := ocp.2.1

/-- Access the composite morphism projection. -/
abbrev ObjMorCompProj.composite.{u, v, w} {omi : ObjMorCompObj.{u + 1, v + 1, w + 1}}
    (ocp : ObjMorCompProj.{u, v, w} omi) : CompProj omi := ocp.2.2

/-- The morphism data for a composition structure: domain/codomain functions
    plus left, right, and composite morphism projections. -/
def ObjMorCompMor.{u, v, w} (omi : ObjMorCompObj.{u + 1, v + 1, w + 1}) :
  Type (max u v w) :=
    ObjMorMor.{u, v} omi.objMor × ObjMorCompProj.{u, v, w} omi

/-- Access the domain/codomain pair from composition morphism data. -/
abbrev ObjMorCompMor.domCod.{u, v, w} {omi : ObjMorCompObj.{u + 1, v + 1, w + 1}}
    (ocm : ObjMorCompMor.{u, v, w} omi) : ObjMorMor.{u, v} omi.objMor := ocm.1

/-- Access the domain function from composition morphism data. -/
abbrev ObjMorCompMor.dom.{u, v, w} {omi : ObjMorCompObj.{u + 1, v + 1, w + 1}}
    (ocm : ObjMorCompMor.{u, v, w} omi) : ObjMorProj omi.objMor :=
  ObjMorMor.dom ocm.domCod

/-- Access the codomain function from composition morphism data. -/
abbrev ObjMorCompMor.cod.{u, v, w} {omi : ObjMorCompObj.{u + 1, v + 1, w + 1}}
    (ocm : ObjMorCompMor.{u, v, w} omi) : ObjMorProj omi.objMor :=
  ObjMorMor.cod ocm.domCod

/-- Access the composition projections from composition morphism data. -/
abbrev ObjMorCompMor.compProj.{u, v, w} {omi : ObjMorCompObj.{u + 1, v + 1, w + 1}}
    (ocm : ObjMorCompMor.{u, v, w} omi) : ObjMorCompProj.{u, v, w} omi := ocm.2

/-- Access the left morphism projection from composition morphism data. -/
abbrev ObjMorCompMor.left.{u, v, w} {omi : ObjMorCompObj.{u + 1, v + 1, w + 1}}
    (ocm : ObjMorCompMor.{u, v, w} omi) : CompProj omi :=
  ObjMorCompProj.left ocm.compProj

/-- Access the right morphism projection from composition morphism data. -/
abbrev ObjMorCompMor.right.{u, v, w} {omi : ObjMorCompObj.{u + 1, v + 1, w + 1}}
    (ocm : ObjMorCompMor.{u, v, w} omi) : CompProj omi :=
  ObjMorCompProj.right ocm.compProj

/-- Access the composite morphism projection from composition morphism data. -/
abbrev ObjMorCompMor.composite.{u, v, w} {omi : ObjMorCompObj.{u + 1, v + 1, w + 1}}
    (ocm : ObjMorCompMor.{u, v, w} omi) : CompProj omi :=
  ObjMorCompProj.composite ocm.compProj

/-- Bundled composition data: object type, morphism type, composition witness type,
    domain/codomain functions, and left/right/composite projections.
    This is the full data before imposing composition conditions. -/
def ObjMorCompObjMor.{u, v, w} : Type (max u v w + 1) :=
  Σ (omc : ObjMorCompObj.{u + 1, v + 1, w + 1}), ObjMorCompMor.{u, v, w} omc

/-- Access the composition object from bundled composition data. -/
abbrev ObjMorCompObjMor.objMorCompObj.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) :
    ObjMorCompObj.{u + 1, v + 1, w + 1} := omcm.1

/-- Access the composition morphism data from bundled composition data. -/
abbrev ObjMorCompObjMor.objMorCompMor.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) :
    ObjMorCompMor.{u, v, w} omcm.objMorCompObj := omcm.2

/-- Access the object type from bundled composition data. -/
abbrev ObjMorCompObjMor.obj.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) :
    Type u := omcm.objMorCompObj.obj

/-- Access the morphism type from bundled composition data. -/
abbrev ObjMorCompObjMor.mor.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) :
    Type v := omcm.objMorCompObj.mor

/-- Access the composition witness type from bundled composition data. -/
abbrev ObjMorCompObjMor.compType.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) :
    Type w := omcm.objMorCompObj.compType

/-- Access the domain function from bundled composition data. -/
abbrev ObjMorCompObjMor.dom.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) :
    omcm.mor → omcm.obj :=
  ObjMorCompMor.dom omcm.objMorCompMor

/-- Access the codomain function from bundled composition data. -/
abbrev ObjMorCompObjMor.cod.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) :
    omcm.mor → omcm.obj :=
  ObjMorCompMor.cod omcm.objMorCompMor

/-- Access the left morphism projection from bundled composition data. -/
abbrev ObjMorCompObjMor.left.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) :
    omcm.compType → omcm.mor :=
  ObjMorCompMor.left omcm.objMorCompMor

/-- Access the right morphism projection from bundled composition data. -/
abbrev ObjMorCompObjMor.right.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) :
    omcm.compType → omcm.mor :=
  ObjMorCompMor.right omcm.objMorCompMor

/-- Access the composite morphism projection from bundled composition data. -/
abbrev ObjMorCompObjMor.composite.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) :
    omcm.compType → omcm.mor :=
  ObjMorCompMor.composite omcm.objMorCompMor

/-- The composability condition: the codomain of the right morphism equals
    the domain of the left morphism. -/
def ObjMorCompObjMorMatch.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) : Prop :=
  omcm.cod ∘ omcm.right = omcm.dom ∘ omcm.left

/-- The domain preservation condition: the domain of the composite equals
    the domain of the right morphism. -/
def ObjMorCompObjMorCompDom.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) : Prop :=
  omcm.dom ∘ omcm.composite = omcm.dom ∘ omcm.right

/-- The codomain preservation condition: the codomain of the composite equals
    the codomain of the left morphism. -/
def ObjMorCompObjMorCompCod.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) : Prop :=
  omcm.cod ∘ omcm.composite = omcm.cod ∘ omcm.left

/-- The conjunction of all composition conditions: composability, domain
    preservation, and codomain preservation. -/
def ObjMorCompObjMorCond.{u, v, w} (omcm : ObjMorCompObjMor.{u, v, w}) : Prop :=
  ObjMorCompObjMorMatch.{u, v, w} omcm ∧
  ObjMorCompObjMorCompDom.{u, v, w} omcm ∧
  ObjMorCompObjMorCompCod.{u, v, w} omcm

/-- Access the composability proof from composition conditions. -/
abbrev ObjMorCompObjMorCond.matchProof.{u, v, w} {omcm : ObjMorCompObjMor.{u, v, w}}
    (cond : ObjMorCompObjMorCond.{u, v, w} omcm) : ObjMorCompObjMorMatch omcm :=
  cond.1

/-- Access the domain and codomain preservation proofs from composition
    conditions. -/
abbrev ObjMorCompObjMorCond.domCodProof.{u, v, w} {omcm : ObjMorCompObjMor.{u, v, w}}
    (cond : ObjMorCompObjMorCond.{u, v, w} omcm) :
    ObjMorCompObjMorCompDom omcm ∧ ObjMorCompObjMorCompCod omcm :=
  cond.2

/-- Access the domain preservation proof from composition conditions. -/
abbrev ObjMorCompObjMorCond.domProof.{u, v, w} {omcm : ObjMorCompObjMor.{u, v, w}}
    (cond : ObjMorCompObjMorCond.{u, v, w} omcm) : ObjMorCompObjMorCompDom omcm :=
  cond.domCodProof.1

/-- Access the codomain preservation proof from composition conditions. -/
abbrev ObjMorCompObjMorCond.codProof.{u, v, w} {omcm : ObjMorCompObjMor.{u, v, w}}
    (cond : ObjMorCompObjMorCond.{u, v, w} omcm) : ObjMorCompObjMorCompCod omcm :=
  cond.domCodProof.2

/-- A quiver with composition structure satisfying all composition conditions.
    This is a subtype ensuring the composition data is well-formed. -/
def ObjMorCompCopr.{u, v, w} : Type (max u v w + 1) :=
  {omim : ObjMorCompObjMor.{u, v, w} // ObjMorCompObjMorCond.{u, v, w} omim}

/-- Access the underlying composition data from a composition copresheaf. -/
abbrev ObjMorCompCopr.data.{u, v, w} (omcc : ObjMorCompCopr.{u, v, w}) :
    ObjMorCompObjMor.{u, v, w} := omcc.val

/-- Access the composition conditions proof from a composition copresheaf. -/
abbrev ObjMorCompCopr.condProof.{u, v, w} (omcc : ObjMorCompCopr.{u, v, w}) :
    ObjMorCompObjMorCond omcc.data := omcc.property

/-- Access the composability proof from a composition copresheaf. -/
abbrev ObjMorCompCopr.matchProof.{u, v, w} (omcc : ObjMorCompCopr.{u, v, w}) :
    ObjMorCompObjMorMatch omcc.data := omcc.condProof.matchProof

/-- Access the domain preservation proof from a composition copresheaf. -/
abbrev ObjMorCompCopr.domProof.{u, v, w} (omcc : ObjMorCompCopr.{u, v, w}) :
    ObjMorCompObjMorCompDom omcc.data := omcc.condProof.domProof

/-- Access the codomain preservation proof from a composition copresheaf. -/
abbrev ObjMorCompCopr.codProof.{u, v, w} (omcc : ObjMorCompCopr.{u, v, w}) :
    ObjMorCompObjMorCompCod omcc.data := omcc.condProof.codProof

/-- The object types for a full category judgment: object type, morphism type,
    identity witness type, and composition witness type. -/
def CatJudgObj.{u, v, w, x} : Type (max u v w x) :=
  ObjMorObj.{u, v} × (Sort w × Sort x)

/-- Access the object-morphism pair from a category judgment object. -/
abbrev CatJudgObj.objMor.{u, v, w, x} (cjo : CatJudgObj.{u, v, w, x}) :
    ObjMorObj.{u, v} := cjo.1

/-- Access the object type from a category judgment object. -/
abbrev CatJudgObj.obj.{u, v, w, x} (cjo : CatJudgObj.{u, v, w, x}) :
    Sort u := cjo.objMor.obj

/-- Access the morphism type from a category judgment object. -/
abbrev CatJudgObj.mor.{u, v, w, x} (cjo : CatJudgObj.{u, v, w, x}) :
    Sort v := cjo.objMor.mor

/-- Access the identity and composition type pair from a category judgment object. -/
abbrev CatJudgObj.idCompTypes.{u, v, w, x} (cjo : CatJudgObj.{u, v, w, x}) :
    Sort w × Sort x := cjo.2

/-- Access the identity witness type from a category judgment object. -/
abbrev CatJudgObj.idType.{u, v, w, x} (cjo : CatJudgObj.{u, v, w, x}) :
    Sort w := cjo.idCompTypes.1

/-- Access the composition witness type from a category judgment object. -/
abbrev CatJudgObj.compType.{u, v, w, x} (cjo : CatJudgObj.{u, v, w, x}) :
    Sort x := cjo.idCompTypes.2

/-- Construct an ObjMorIdObj from a CatJudgObj by pairing the object-morphism
    pair with the identity witness type. -/
abbrev CatJudgObj.toObjMorIdObj.{u, v, w, x} (cjo : CatJudgObj.{u, v, w, x}) :
    ObjMorIdObj.{u, v, w} :=
  (cjo.objMor, cjo.idType)

/-- Construct an ObjMorCompObj from a CatJudgObj by pairing the object-morphism
    pair with the composition witness type. -/
abbrev CatJudgObj.toObjMorCompObj.{u, v, w, x} (cjo : CatJudgObj.{u, v, w, x}) :
    ObjMorCompObj.{u, v, x} :=
  (cjo.objMor, cjo.compType)

/-- The morphism data for a full category judgment: domain/codomain functions,
    identity morphism assignment, and composition projections. -/
def CatJudgMor.{u, v, w, x} (cjo : CatJudgObj.{u + 1, v + 1, w + 1, x + 1}) :
    Type (max u v w x) :=
  ObjMorMor.{u, v} cjo.objMor ×
  IdProj.{u + 1, v + 1, w + 1} cjo.toObjMorIdObj ×
  ObjMorCompProj.{u, v, x} cjo.toObjMorCompObj

/-- Access the domain/codomain pair from category judgment morphism data. -/
abbrev CatJudgMor.domCod.{u, v, w, x} {cjo : CatJudgObj.{u + 1, v + 1, w + 1, x + 1}}
    (cjm : CatJudgMor.{u, v, w, x} cjo) : ObjMorMor.{u, v} cjo.objMor := cjm.1

/-- Access the identity and composition data pair from category judgment
    morphism data. -/
abbrev CatJudgMor.idMorCompProj.{u, v, w, x}
    {cjo : CatJudgObj.{u + 1, v + 1, w + 1, x + 1}}
    (cjm : CatJudgMor.{u, v, w, x} cjo) :
    IdProj.{u + 1, v + 1, w + 1} cjo.toObjMorIdObj ×
    ObjMorCompProj.{u, v, x} cjo.toObjMorCompObj := cjm.2

/-- Access the identity morphism projection from category judgment morphism data. -/
abbrev CatJudgMor.idMor.{u, v, w, x} {cjo : CatJudgObj.{u + 1, v + 1, w + 1, x + 1}}
    (cjm : CatJudgMor.{u, v, w, x} cjo) :
    IdProj.{u + 1, v + 1, w + 1} cjo.toObjMorIdObj :=
  cjm.idMorCompProj.1

/-- Access the composition projections from category judgment morphism data. -/
abbrev CatJudgMor.compProj.{u, v, w, x} {cjo : CatJudgObj.{u + 1, v + 1, w + 1, x + 1}}
    (cjm : CatJudgMor.{u, v, w, x} cjo) :
    ObjMorCompProj.{u, v, x} cjo.toObjMorCompObj :=
  cjm.idMorCompProj.2

/-- Bundled category judgment data: all object types and all morphism functions.
    This is the full data before imposing conditions. -/
def CatJudgObjMor.{u, v, w, x} : Type (max u v w x + 1) :=
  Σ (cjo : CatJudgObj.{u + 1, v + 1, w + 1, x + 1}), CatJudgMor.{u, v, w, x} cjo

/-- Access the category judgment object from bundled category judgment data. -/
abbrev CatJudgObjMor.catJudgObj.{u, v, w, x} (cjom : CatJudgObjMor.{u, v, w, x}) :
    CatJudgObj.{u + 1, v + 1, w + 1, x + 1} := cjom.1

/-- Access the object type from bundled category judgment data. -/
abbrev CatJudgObjMor.obj.{u, v, w, x} (cjom : CatJudgObjMor.{u, v, w, x}) :
    Type u := cjom.catJudgObj.obj

/-- Access the morphism type from bundled category judgment data. -/
abbrev CatJudgObjMor.mor.{u, v, w, x} (cjom : CatJudgObjMor.{u, v, w, x}) :
    Type v := cjom.catJudgObj.mor

/-- Access the identity witness type from bundled category judgment data. -/
abbrev CatJudgObjMor.idType.{u, v, w, x} (cjom : CatJudgObjMor.{u, v, w, x}) :
    Type w := cjom.catJudgObj.idType

/-- Access the composition witness type from bundled category judgment data. -/
abbrev CatJudgObjMor.compType.{u, v, w, x} (cjom : CatJudgObjMor.{u, v, w, x}) :
    Type x := cjom.catJudgObj.compType

/-- Access the morphism data from bundled category judgment data. -/
abbrev CatJudgObjMor.catJudgMor.{u, v, w, x} (cjom : CatJudgObjMor.{u, v, w, x}) :
    CatJudgMor.{u, v, w, x} cjom.catJudgObj := cjom.2

/-- Access the domain/codomain pair from bundled category judgment data. -/
abbrev CatJudgObjMor.domCod.{u, v, w, x} (cjom : CatJudgObjMor.{u, v, w, x}) :
    ObjMorMor.{u, v} cjom.catJudgObj.objMor :=
  CatJudgMor.domCod cjom.catJudgMor

/-- Access the domain function from bundled category judgment data. -/
abbrev CatJudgObjMor.dom.{u, v, w, x} (cjom : CatJudgObjMor.{u, v, w, x}) :
    cjom.mor → cjom.obj := ObjMorMor.dom cjom.domCod

/-- Access the codomain function from bundled category judgment data. -/
abbrev CatJudgObjMor.cod.{u, v, w, x} (cjom : CatJudgObjMor.{u, v, w, x}) :
    cjom.mor → cjom.obj := ObjMorMor.cod cjom.domCod

/-- Access the identity morphism function from bundled category judgment data. -/
abbrev CatJudgObjMor.idMor.{u, v, w, x} (cjom : CatJudgObjMor.{u, v, w, x}) :
    cjom.idType → cjom.mor :=
  CatJudgMor.idMor cjom.catJudgMor

/-- Access the composition projections from bundled category judgment data. -/
abbrev CatJudgObjMor.compProj.{u, v, w, x} (cjom : CatJudgObjMor.{u, v, w, x}) :
    ObjMorCompProj.{u, v, x} cjom.catJudgObj.toObjMorCompObj :=
  CatJudgMor.compProj cjom.catJudgMor

/-- Access the left morphism projection from bundled category judgment data. -/
abbrev CatJudgObjMor.left.{u, v, w, x} (cjom : CatJudgObjMor.{u, v, w, x}) :
    cjom.compType → cjom.mor :=
  ObjMorCompProj.left cjom.compProj

/-- Access the right morphism projection from bundled category judgment data. -/
abbrev CatJudgObjMor.right.{u, v, w, x} (cjom : CatJudgObjMor.{u, v, w, x}) :
    cjom.compType → cjom.mor :=
  ObjMorCompProj.right cjom.compProj

/-- Access the composite morphism projection from bundled category judgment data. -/
abbrev CatJudgObjMor.composite.{u, v, w, x} (cjom : CatJudgObjMor.{u, v, w, x}) :
    cjom.compType → cjom.mor :=
  ObjMorCompProj.composite cjom.compProj

/-- Construct an ObjMorIdObjMor from bundled category judgment data by
    extracting the identity-related components. -/
abbrev CatJudgObjMor.toObjMorIdObjMor.{u, v, w, x}
    (cjom : CatJudgObjMor.{u, v, w, x}) : ObjMorIdObjMor.{u, v, w} :=
  ⟨cjom.catJudgObj.toObjMorIdObj, ⟨cjom.domCod, CatJudgMor.idMor cjom.catJudgMor⟩⟩

/-- Construct an ObjMorCompObjMor from bundled category judgment data by
    extracting the composition-related components. -/
abbrev CatJudgObjMor.toObjMorCompObjMor.{u, v, w, x}
    (cjom : CatJudgObjMor.{u, v, w, x}) : ObjMorCompObjMor.{u, v, x} :=
  ⟨cjom.catJudgObj.toObjMorCompObj, ⟨cjom.domCod, cjom.compProj⟩⟩

/-- The combined conditions for a category judgment: identity endomorphism and
    all composition conditions must hold. -/
def CatJudgObjMorCond.{u, v, w, x} (cjom : CatJudgObjMor.{u, v, w, x}) : Prop :=
  ObjMorIdObjMorEndo.{u, v, w} cjom.toObjMorIdObjMor ∧
  ObjMorCompObjMorCond.{u, v, x} cjom.toObjMorCompObjMor

/-- Access the identity endomorphism proof from category judgment conditions. -/
abbrev CatJudgObjMorCond.endoProof.{u, v, w, x} {cjom : CatJudgObjMor.{u, v, w, x}}
    (cond : CatJudgObjMorCond.{u, v, w, x} cjom) :
    ObjMorIdObjMorEndo.{u, v, w} cjom.toObjMorIdObjMor :=
  cond.1

/-- Access the composition conditions proof from category judgment conditions. -/
abbrev CatJudgObjMorCond.compCondProof.{u, v, w, x} {cjom : CatJudgObjMor.{u, v, w, x}}
    (cond : CatJudgObjMorCond.{u, v, w, x} cjom) :
    ObjMorCompObjMorCond.{u, v, x} cjom.toObjMorCompObjMor :=
  cond.2

/-- A full category-judgment copresheaf: all data satisfying all conditions. -/
def CatJudgCopr.{u, v, w, x} : Type (max u v w x + 1) :=
  {cjom : CatJudgObjMor.{u, v, w, x} // CatJudgObjMorCond.{u, v, w, x} cjom}

/-- Access the underlying data from a category judgment copresheaf. -/
abbrev CatJudgCopr.data.{u, v, w, x} (cjc : CatJudgCopr.{u, v, w, x}) :
    CatJudgObjMor.{u, v, w, x} := cjc.val

/-- Access the conditions proof from a category judgment copresheaf. -/
abbrev CatJudgCopr.condProof.{u, v, w, x} (cjc : CatJudgCopr.{u, v, w, x}) :
    CatJudgObjMorCond cjc.data := cjc.property

/-- Access the identity endomorphism proof from a category judgment copresheaf. -/
abbrev CatJudgCopr.endoProof.{u, v, w, x} (cjc : CatJudgCopr.{u, v, w, x}) :
    ObjMorIdObjMorEndo.{u, v, w} cjc.data.toObjMorIdObjMor :=
  cjc.condProof.endoProof

/-- Access the composition conditions proof from a category judgment copresheaf. -/
abbrev CatJudgCopr.compCondProof.{u, v, w, x} (cjc : CatJudgCopr.{u, v, w, x}) :
    ObjMorCompObjMorCond.{u, v, x} cjc.data.toObjMorCompObjMor :=
  cjc.condProof.compCondProof

/-- Access the composability proof from a category judgment copresheaf. -/
abbrev CatJudgCopr.compMatchProof.{u, v, w, x} (cjc : CatJudgCopr.{u, v, w, x}) :
    ObjMorCompObjMorMatch.{u, v, x} cjc.data.toObjMorCompObjMor :=
  cjc.compCondProof.matchProof

/-- Access the domain preservation proof from a category judgment copresheaf. -/
abbrev CatJudgCopr.compDomProof.{u, v, w, x} (cjc : CatJudgCopr.{u, v, w, x}) :
    ObjMorCompObjMorCompDom.{u, v, x} cjc.data.toObjMorCompObjMor :=
  cjc.compCondProof.domProof

/-- Access the codomain preservation proof from a category judgment copresheaf. -/
abbrev CatJudgCopr.compCodProof.{u, v, w, x} (cjc : CatJudgCopr.{u, v, w, x}) :
    ObjMorCompObjMorCompCod.{u, v, x} cjc.data.toObjMorCompObjMor :=
  cjc.compCondProof.codProof

/-- Access the object type from a category judgment copresheaf. -/
abbrev CatJudgCopr.obj.{u, v, w, x} (cjc : CatJudgCopr.{u, v, w, x}) :
    Type u := cjc.data.obj

/-- Access the morphism type from a category judgment copresheaf. -/
abbrev CatJudgCopr.mor.{u, v, w, x} (cjc : CatJudgCopr.{u, v, w, x}) :
    Type v := cjc.data.mor

/-- Access the identity witness type from a category judgment copresheaf. -/
abbrev CatJudgCopr.idType.{u, v, w, x} (cjc : CatJudgCopr.{u, v, w, x}) :
    Type w := cjc.data.idType

/-- Access the composition witness type from a category judgment copresheaf. -/
abbrev CatJudgCopr.compType.{u, v, w, x} (cjc : CatJudgCopr.{u, v, w, x}) :
    Type x := cjc.data.compType

/-- Access the domain function from a category judgment copresheaf. -/
abbrev CatJudgCopr.dom.{u, v, w, x} (cjc : CatJudgCopr.{u, v, w, x}) :
    cjc.mor → cjc.obj := cjc.data.dom

/-- Access the codomain function from a category judgment copresheaf. -/
abbrev CatJudgCopr.cod.{u, v, w, x} (cjc : CatJudgCopr.{u, v, w, x}) :
    cjc.mor → cjc.obj := cjc.data.cod

/-- Access the identity morphism function from a category judgment copresheaf. -/
abbrev CatJudgCopr.idMor.{u, v, w, x} (cjc : CatJudgCopr.{u, v, w, x}) :
    cjc.idType → cjc.mor := cjc.data.idMor

/-- Access the left morphism projection from a category judgment copresheaf. -/
abbrev CatJudgCopr.left.{u, v, w, x} (cjc : CatJudgCopr.{u, v, w, x}) :
    cjc.compType → cjc.mor := cjc.data.left

/-- Access the right morphism projection from a category judgment copresheaf. -/
abbrev CatJudgCopr.right.{u, v, w, x} (cjc : CatJudgCopr.{u, v, w, x}) :
    cjc.compType → cjc.mor := cjc.data.right

/-- Access the composite morphism projection from a category judgment copresheaf. -/
abbrev CatJudgCopr.composite.{u, v, w, x} (cjc : CatJudgCopr.{u, v, w, x}) :
    cjc.compType → cjc.mor := cjc.data.composite

end Obj

namespace Mor

end Mor

end PLang

end GebLean

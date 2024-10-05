module LanguageDef.PolyDifunc

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.DisliceCat
import public LanguageDef.PolyCat
import public LanguageDef.DislicePolyCat
import public LanguageDef.IntECofamCat
import public LanguageDef.GenPolyFunc
import public LanguageDef.IntDisheafCat

%default total
%hide Library.IdrisCategories.BaseChangeF
%hide Prelude.Ops.infixl.(|>)

-------------------------------------
-------------------------------------
---- Simple difunctors on `Type` ----
-------------------------------------
-------------------------------------

------------------------------------------------------------------
---- Aliases for polynomial difunctors specifically on `Type` ----
------------------------------------------------------------------

public export
0 TypeProDimap : ProfunctorSig -> Type
TypeProDimap = IntEndoDimapSig Type TypeMor

public export
0 TypeProLmap : ProfunctorSig -> Type
TypeProLmap = IntEndoLmapSig Type TypeMor

public export
0 TypeProRmap : ProfunctorSig -> Type
TypeProRmap = IntEndoRmapSig Type TypeMor

public export
0 TypeLmapFromDimap : (p : ProfunctorSig) -> TypeProDimap p -> TypeProLmap p
TypeLmapFromDimap = IntEndoLmapFromDimap Type TypeMor typeId

public export
0 TypeRmapFromDimap : (p : ProfunctorSig) -> TypeProDimap p -> TypeProRmap p
TypeRmapFromDimap = IntEndoRmapFromDimap Type TypeMor typeId

public export
0 TypeProfNT : IntMorSig ProfunctorSig
TypeProfNT = IntEndoProfNTSig Type

public export
0 TypeProfDiNT : IntMorSig ProfunctorSig
TypeProfDiNT = IntDiNTSig Type

public export
0 TypeNTNaturality : (p, q : ProfunctorSig) ->
  TypeProDimap p -> TypeProDimap q -> TypeProfNT p q -> Type
TypeNTNaturality = IntProfNTNaturality Type Type TypeMor TypeMor

public export
0 TypeNTParanaturality : (p, q : ProfunctorSig) ->
  TypeProDimap p -> TypeProDimap q -> TypeProfDiNT p q -> Type
TypeNTParanaturality p q pdm qdm =
  IntParaNTCond Type TypeMor p q
    (TypeLmapFromDimap p pdm) (TypeRmapFromDimap p pdm)
    (TypeLmapFromDimap q qdm) (TypeRmapFromDimap q qdm)

public export
TypeProAr : Type
TypeProAr = IntEndoProAr Type

public export
InterpTypeProAr : TypeProAr -> Type -> Type -> Type
InterpTypeProAr = InterpIEPPobj Type TypeMor

public export
0 TypeProDimapSig : TypeProAr -> Type
TypeProDimapSig = TypeProDimap . InterpTypeProAr

public export
0 TypeProLmapSig : TypeProAr -> Type
TypeProLmapSig = TypeProLmap . InterpTypeProAr

public export
0 TypeProRmapSig : TypeProAr -> Type
TypeProRmapSig = TypeProRmap . InterpTypeProAr

public export
TypeProArDimap : (ar : TypeProAr) -> TypeProDimapSig ar
TypeProArDimap = InterpIEPPdimap Type TypeMor typeComp

public export
0 TypeProArLmap : (ar : TypeProAr) -> TypeProLmapSig ar
TypeProArLmap ar = TypeLmapFromDimap (InterpTypeProAr ar) (TypeProArDimap ar)

public export
0 TypeProArRmap : (ar : TypeProAr) -> TypeProRmapSig ar
TypeProArRmap ar = TypeRmapFromDimap (InterpTypeProAr ar) (TypeProArDimap ar)

public export
0 TypeProNTSig : IntMorSig TypeProAr
TypeProNTSig p q = TypeProfNT (InterpTypeProAr p) (InterpTypeProAr q)

public export
0 TypeDiNTSig : IntMorSig TypeProAr
TypeDiNTSig p q = TypeProfDiNT (InterpTypeProAr p) (InterpTypeProAr q)

public export
TypeProNTar : IntMorSig TypeProAr
TypeProNTar = IntEPPNTar Type TypeMor

public export
TypeProNTid : IntIdSig TypeProAr TypeProNTar
TypeProNTid = intPPNTid Type Type TypeMor TypeMor typeId typeId

public export
TypeProNTvcomp : IntCompSig TypeProAr TypeProNTar
TypeProNTvcomp = intPPNTvcomp Type Type TypeMor TypeMor typeComp typeComp

public export
InterpTypeProNT : (p, q : TypeProAr) -> TypeProNTar p q -> TypeProNTSig p q
InterpTypeProNT = InterpIEPPnt Type TypeMor typeComp

public export
TypeDiNTar : IntMorSig TypeProAr
TypeDiNTar = IntPDiNTar Type TypeMor

public export
TypeDiNTid : IntIdSig TypeProAr TypeDiNTar
TypeDiNTid = intPDiNTid Type TypeMor typeId

public export
TypeDiNTvcomp : IntCompSig TypeProAr TypeDiNTar
TypeDiNTvcomp = intPDiNTvcomp Type TypeMor typeComp

public export
InterpTypeDiNT : (p, q : TypeProAr) -> TypeDiNTar p q -> TypeDiNTSig p q
InterpTypeDiNT = InterpIEPPdint Type TypeMor typeComp

public export
0 TypeProArNaturality : (p, q : TypeProAr) -> TypeProNTSig p q -> Type
TypeProArNaturality p q =
  TypeNTNaturality (InterpTypeProAr p) (InterpTypeProAr q)
    (TypeProArDimap p) (TypeProArDimap q)

public export
0 TypeProArParanaturality : (p, q : TypeProAr) -> TypeDiNTSig p q -> Type
TypeProArParanaturality p q =
  TypeNTParanaturality (InterpTypeProAr p) (InterpTypeProAr q)
    (TypeProArDimap p) (TypeProArDimap q)

-------------------------------------------------
---- Completeness of natural transformations ----
-------------------------------------------------

public export
TypeProArFromNT : (p, q : TypeProAr) -> TypeProNTSig p q -> TypeProNTar p q
TypeProArFromNT (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar)) alpha =
  let nti = \pi : ppos => alpha (pcontra pi) (pcovar pi) (pi ** (id, id)) in
  (\pi => fst (nti pi) **
   (\pi => fst (snd $ nti pi),
    \pi => snd (snd $ nti pi)))

public export
0 TypeProArComplete : (p, q : TypeProAr) -> (alpha : TypeProNTSig p q) ->
  (cond : TypeProArNaturality p q alpha) ->
  (x, y : Type) ->
  ExtEq {a=(InterpTypeProAr p x y)} {b=(InterpTypeProAr q x y)}
    (alpha x y)
    (InterpTypeProNT p q (TypeProArFromNT p q alpha) x y)
TypeProArComplete (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar)) alpha
  cond x y (pi ** (dmx, dmy)) =
    sym $ cond (pcontra pi) (pcovar pi) x y dmx dmy (pi ** (id, id))

-----------------------------------------------------
---- Completeness of paranatural transformations ----
-----------------------------------------------------

public export
TypeDiArFromDi: (p, q : TypeProAr) ->
  (gamma : TypeDiNTSig p q) -> TypeProArParanaturality p q gamma ->
  TypeDiNTar p q
TypeDiArFromDi (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar)) gamma
  cond =
    (\pi, asn =>
      fst $ gamma (pcovar pi) (pi ** (asn, id)) **
     (\pi, asn, pcont =>
        rewrite
          sym (dpeq1 $
            cond (pcovar pi) (pcontra pi) asn
              (pi ** (asn, id))
              (pi ** (id, asn))
              Refl)
        in
        fst (snd $ gamma (pcontra pi) (pi ** (id, asn))) pcont,
      \pi, asn =>
        snd $ snd $ gamma (pcovar pi) (pi ** (asn, id))))

public export
0 TypeDiArCompleteFst :
  (p, q : TypeProAr) -> (gamma : TypeDiNTSig p q) ->
  (cond : TypeProArParanaturality p q gamma) ->
  (x : Type) ->
  (i : InterpTypeProAr p x x) ->
    fst (gamma x i) =
    (fst $ InterpTypeDiNT p q (TypeDiArFromDi p q gamma cond) x i)
TypeDiArCompleteFst (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar))
  gamma cond x (pi ** (dmx, dmy)) =
    rewrite dpeq1 $
      cond (pcovar pi) x dmy (pi ** (dmx . dmy, id)) (pi ** (dmx, dmy)) Refl in
    Refl

public export
0 TypeDiArCompleteFstSnd :
  (p, q : TypeProAr) -> (gamma : TypeDiNTSig p q) ->
  (cond : TypeProArParanaturality p q gamma) ->
  (x : Type) ->
  (i : InterpTypeProAr p x x) ->
    fst (snd $ gamma x i) =
    (rewrite TypeDiArCompleteFst p q gamma cond x i in
     fst (snd $ InterpTypeDiNT p q (TypeDiArFromDi p q gamma cond) x i))
TypeDiArCompleteFstSnd
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar))
  gamma cond x (pi ** (dmx, dmy)) =
    let
      condapp =
        cond x (pcontra pi) dmx (pi ** (dmx, dmy)) (pi ** (id, dmx . dmy)) Refl
    in
    rewrite sym $ dpeq1 condapp in
    sym $ fstEqHet $ dpeq2 condapp

public export
0 TypeDiArCompleteSndSnd :
  (p, q : TypeProAr) -> (gamma : TypeDiNTSig p q) ->
  (cond : TypeProArParanaturality p q gamma) ->
  (x : Type) ->
  (i : InterpTypeProAr p x x) ->
    snd (snd $ gamma x i) =
    (rewrite TypeDiArCompleteFst p q gamma cond x i in
     snd (snd $ InterpTypeDiNT p q (TypeDiArFromDi p q gamma cond) x i))
TypeDiArCompleteSndSnd
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar))
  gamma cond x (pi ** (dmx, dmy)) =
    sndEqHet $ dpeq2 $
      cond (pcovar pi) x dmy (pi ** (dmx . dmy, id)) (pi ** (dmx, dmy)) Refl

public export
0 TypeDiArComplete :
  (p, q : TypeProAr) -> (gamma : TypeDiNTSig p q) ->
  (cond : TypeProArParanaturality p q gamma) ->
  (x : Type) ->
  ExtEq {a=(InterpTypeProAr p x x)} {b=(InterpTypeProAr q x x)}
    (gamma x)
    (InterpTypeDiNT p q (TypeDiArFromDi p q gamma cond) x)
TypeDiArComplete
  p@(ppos ** (pcontra, pcovar)) q@(qpos ** (qcontra, qcovar))
  gamma cond x i@(pi ** (dmx, dmy)) =
    rewrite sym $ TypeDiArCompleteFst p q gamma cond x i in
    rewrite sym $ TypeDiArCompleteFstSnd p q gamma cond x i in
    rewrite dpEqPat {dp=(gamma x (pi ** (dmx, dmy)))} in
    dpEq12
      Refl
    $ rewrite pairFstSnd (snd $ gamma x (pi ** (dmx, dmy))) in
      pairEqCong Refl (TypeDiArCompleteSndSnd p q gamma cond x i)

---------------------------------------------------------
---- Categorical laws of paranatural transformations ----
---------------------------------------------------------

public export
TypeDiNTcompIdL : {p, q : TypeProAr} ->
  (gamma : TypeDiNTar p q) ->
  TypeDiNTvcomp p q q (TypeDiNTid q) gamma = gamma
TypeDiNTcompIdL
  {p=(ppos ** (pcontra, pcovar))} {q=(qpos ** (qcontra, qcovar))}
  (onpos ** (oncontra, oncovar)) =
    Refl

public export
TypeDiNTcompIdR : {p, q : TypeProAr} ->
  (gamma : TypeDiNTar p q) ->
  TypeDiNTvcomp p p q gamma (TypeDiNTid p) = gamma
TypeDiNTcompIdR
  {p=(ppos ** (pcontra, pcovar))} {q=(qpos ** (qcontra, qcovar))}
  (onpos ** (oncontra, oncovar)) =
    Refl

public export
TypeDiNTcompAssoc : {p, q, r, s : TypeProAr} ->
  (gamma : TypeDiNTar r s) ->
  (beta : TypeDiNTar q r) ->
  (alpha : TypeDiNTar p q) ->
  TypeDiNTvcomp p r s gamma (TypeDiNTvcomp p q r beta alpha) =
  TypeDiNTvcomp p q s (TypeDiNTvcomp q r s gamma beta) alpha
TypeDiNTcompAssoc
  {p=(ppos ** (pcontra, pcovar))}
  {q=(qpos ** (qcontra, qcovar))}
  {r=(rpos ** (rcontra, rcovar))}
  (gonpos ** (goncontra, goncovar))
  (bonpos ** (boncontra, boncovar))
  (aonpos ** (aoncontra, aoncovar)) =
    Refl

------------------------------------
---- Laws of composition monoid ----
------------------------------------

public export
TypeProArId : TypeProAr
TypeProArId = IntProArId Type

public export
TypeProArComp : TypeProAr -> TypeProAr -> TypeProAr
TypeProArComp = IntEndoProArComp Type TypeMor

public export
TypeProCompToIdL : (p : TypeProAr) ->
  TypeProNTar p (TypeProArComp TypeProArId p)
TypeProCompToIdL (ppos ** (pcontra, pcovar)) =
  (\pi => (pi ** pcontra pi ** id) **
   (\_ => id,
    \_ => id))

public export
TypeProCompFromIdL : (p : TypeProAr) ->
  TypeProNTar (TypeProArComp TypeProArId p) p
TypeProCompFromIdL (ppos ** (pcontra, pcovar)) =
  (fst **
   (\(pi ** qi ** mqp) => mqp,
    \(pi ** qi ** mqp) => id))

public export
TypeProCompToIdR : (p : TypeProAr) ->
  TypeProNTar p (TypeProArComp p TypeProArId)
TypeProCompToIdR (ppos ** (pcontra, pcovar)) =
  (\pi => (pcovar pi ** pi ** id) **
   (\pi => id,
    \pi => id))

public export
TypeProCompFromIdR : (p : TypeProAr) ->
  TypeProNTar (TypeProArComp p TypeProArId) p
TypeProCompFromIdR (ppos ** (pcontra, pcovar)) =
  (\(x ** pi ** dmcov) => pi **
   (\(x ** pi ** dmcov) => id,
    \(x ** pi ** dmcov) => dmcov))

public export
TypeProCompAssocL : (p, q, r : TypeProAr) ->
  TypeProNTar
    (TypeProArComp r (TypeProArComp q p))
    (TypeProArComp (TypeProArComp r q) p)
TypeProCompAssocL
  (rpos ** (rcontra, rcovar))
  (qpos ** (qcontra, qcovar))
  (ppos ** (pcontra, pcovar)) =
    (\((ri ** qi ** mqr) ** pi ** mpq) =>
      (ri ** (qi ** pi ** mpq) ** mqr) **
     (\((ri ** qi ** mqr) ** pi ** mpq) => id,
      \((ri ** qi ** mqr) ** pi ** mpq) => id))

public export
TypeProCompAssocR : (p, q, r : TypeProAr) ->
  TypeProNTar
    (TypeProArComp (TypeProArComp r q) p)
    (TypeProArComp r (TypeProArComp q p))
TypeProCompAssocR
  (rpos ** (rcontra, rcovar))
  (qpos ** (qcontra, qcovar))
  (ppos ** (pcontra, pcovar)) =
    (\(ri ** (qi ** pi ** mpq) ** mqr) => ((ri ** qi ** mqr) ** (pi ** mpq)) **
     (\(ri ** (qi ** pi ** mpq) ** mqr) => id,
      \(ri ** (qi ** pi ** mpq) ** mqr) => id))

public export
TypeProCompRelToInterp : (q, p : TypeProAr) -> (s, t, x : Type) ->
  InterpTypeProAr q s x -> InterpTypeProAr p x t ->
  InterpTypeProAr (TypeProArComp q p) s t
TypeProCompRelToInterp
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t x
  (qi ** (qdmcont, qdmcovar)) (pi ** (pdmcont, pdmcovar)) =
    ((pi ** qi ** pdmcont . qdmcovar) ** (qdmcont, pdmcovar))

public export
TypeProDimapDistrib : (q, p : TypeProAr) -> (s, t, a, b, x : Type) ->
  (qsx : InterpTypeProAr q s x) -> (pxt : InterpTypeProAr p x t) ->
  (mas : a -> s) -> (mtb : t -> b) ->
  TypeProArDimap (TypeProArComp q p) s t a b mas mtb
    (TypeProCompRelToInterp q p s t x qsx pxt) =
  TypeProCompRelToInterp q p a b x
    (TypeProArDimap q s x a x mas Prelude.id qsx)
    (TypeProArDimap p x t x b Prelude.id mtb pxt)
TypeProDimapDistrib
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t x
  qsx pst (qi ** (qdmcont, qdmcovar)) (pi ** (pdmcont, pdmcovar)) mas mtb =
    Refl

public export
TypeProCompIntObj : (q, p : TypeProAr) -> (s, t : Type) ->
  InterpTypeProAr (TypeProArComp q p) s t -> Type
TypeProCompIntObj
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t
  ((pi ** qi ** mqp) ** (dmcont, dmcov)) =
    pcontra pi

public export
TypeProCompFactFst : (q, p : TypeProAr) -> (s, t : Type) ->
  (qpst : InterpTypeProAr (TypeProArComp q p) s t) ->
  InterpTypeProAr p (TypeProCompIntObj q p s t qpst) t
TypeProCompFactFst
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t
  ((pi ** qi ** mqp) ** (dmcont, dmcov)) =
    (pi ** (id, dmcov))

public export
TypeProCompFactSnd : (q, p : TypeProAr) -> (s, t : Type) ->
  (qpst : InterpTypeProAr (TypeProArComp q p) s t) ->
  InterpTypeProAr q s (TypeProCompIntObj q p s t qpst)
TypeProCompFactSnd
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t
  ((pi ** qi ** mqp) ** (dmcont, dmcov)) =
    (qi ** (dmcont, mqp))

public export
TypeDiArId : TypeProAr
TypeDiArId = IntProArId Type

public export
TypeDiArComp : TypeProAr -> TypeProAr -> TypeProAr
TypeDiArComp = IntDiArComp Type TypeMor

public export
TypeDiCompToIdL : (p : TypeProAr) ->
  TypeDiNTar p (TypeDiArComp TypeDiArId p)
TypeDiCompToIdL (ppos ** (pcontra, pcovar)) =
  ((\pi, asn =>
    (pi **
     pcontra pi **
     id)) **
   (\_, _ => id,
    \_, _ => id))

public export
TypeDiCompFromIdL : (p : TypeProAr) ->
  TypeDiNTar (TypeDiArComp TypeDiArId p) p
TypeDiCompFromIdL (ppos ** (pcontra, pcovar)) =
  ((\pi, asn => fst pi) **
   (\(pi ** x ** dmcont), dmcov => dmcont,
    \(pi ** x ** dmcont), dmcov => id))

public export
TypeDiCompToIdR : (p : TypeProAr) ->
  TypeDiNTar p (TypeDiArComp p TypeDiArId)
TypeDiCompToIdR (ppos ** (pcontra, pcovar)) =
  (\pi, asn => (pcovar pi ** pi ** id) **
   (\_, _ => id,
    \_, _ => id))

public export
TypeDiCompFromIdR : (p : TypeProAr) ->
  TypeDiNTar (TypeDiArComp p TypeDiArId) p
TypeDiCompFromIdR (ppos ** (pcontra, pcovar)) =
  (\(x ** pi ** dmcov), dmcont => pi **
   (\(x ** pi ** dmcov), dmcont => id,
    \(x ** pi ** dmcov), dmcont => dmcov))

public export
TypeDiCompAssocL : (p, q, r : TypeProAr) ->
  TypeDiNTar
    (TypeDiArComp r (TypeDiArComp q p))
    (TypeDiArComp (TypeDiArComp r q) p)
TypeDiCompAssocL
  (rpos ** (rcontra, rcovar))
  (qpos ** (qcontra, qcovar))
  (ppos ** (pcontra, pcovar)) =
    (\((ri ** qi ** mqr) ** (pi ** mpq)), mrp =>
      (ri ** (qi ** pi ** mpq) ** mqr) **
     (\((ri ** qi ** mqr) ** (pi ** mpq)), mrp => id,
      \((ri ** qi ** mqr) ** (pi ** mpq)), mrp => id))

public export
TypeDiCompAssocR : (p, q, r : TypeProAr) ->
  TypeDiNTar
    (TypeDiArComp (TypeDiArComp r q) p)
    (TypeDiArComp r (TypeDiArComp q p))
TypeDiCompAssocR
  (rpos ** (rcontra, rcovar))
  (qpos ** (qcontra, qcovar))
  (ppos ** (pcontra, pcovar)) =
    (\(ri ** (qi ** pi ** mpq) ** mqr), mrp =>
      ((ri ** qi ** mqr) ** (pi ** mpq)) **
     (\(ri ** (qi ** pi ** mpq) ** mqr), mrp => id,
      \(ri ** (qi ** pi ** mpq) ** mqr), mrp => id))

public export
TypeDiCompRelToInterp : (q, p : TypeProAr) -> (s, t, x : Type) ->
  InterpTypeProAr q s x -> InterpTypeProAr p x t ->
  InterpTypeProAr (TypeDiArComp q p) s t
TypeDiCompRelToInterp
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t x
  (qi ** (qdmcont, qdmcovar)) (pi ** (pdmcont, pdmcovar)) =
    ((pi ** qi ** pdmcont . qdmcovar) ** (qdmcont, pdmcovar))

public export
TypeDiDimapDistrib : (q, p : TypeProAr) -> (s, t, a, b, x : Type) ->
  (qsx : InterpTypeProAr q s x) -> (pxt : InterpTypeProAr p x t) ->
  (mas : a -> s) -> (mtb : t -> b) ->
  TypeProArDimap (TypeDiArComp q p) s t a b mas mtb
    (TypeDiCompRelToInterp q p s t x qsx pxt) =
  TypeDiCompRelToInterp q p a b x
    (TypeProArDimap q s x a x mas Prelude.id qsx)
    (TypeProArDimap p x t x b Prelude.id mtb pxt)
TypeDiDimapDistrib
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t x
  qsx pst (qi ** (qdmcont, qdmcovar)) (pi ** (pdmcont, pdmcovar)) mas mtb =
    Refl

public export
TypeDiCompIntObj : (q, p : TypeProAr) -> (s, t : Type) ->
  InterpTypeProAr (TypeDiArComp q p) s t -> Type
TypeDiCompIntObj
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t
  ((pi ** qi ** mqp) ** (dmcont, dmcov)) =
    pcontra pi

public export
TypeDiCompFactFst : (q, p : TypeProAr) -> (s, t : Type) ->
  (qpst : InterpTypeProAr (TypeDiArComp q p) s t) ->
  InterpTypeProAr p (TypeDiCompIntObj q p s t qpst) t
TypeDiCompFactFst
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t
  ((pi ** qi ** mqp) ** (dmcont, dmcov)) =
    (pi ** (id, dmcov))

public export
TypeDiCompFactSnd : (q, p : TypeProAr) -> (s, t : Type) ->
  (qpst : InterpTypeProAr (TypeDiArComp q p) s t) ->
  InterpTypeProAr q s (TypeDiCompIntObj q p s t qpst)
TypeDiCompFactSnd
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) s t
  ((pi ** qi ** mqp) ** (dmcont, dmcov)) =
    (qi ** (dmcont, mqp))

----------------------------------------------
---- Interpretation of composition monoid ----
----------------------------------------------

public export
TypeProIdToIdInterp :
  TypeProfNT (InterpTypeProAr (IntProArId Type)) HomProf
TypeProIdToIdInterp x y (i ** (mxi, miy)) = miy . mxi

public export
TypeIdInterpToProId :
  TypeProfNT HomProf (InterpTypeProAr (IntProArId Type))
TypeIdInterpToProId x y mxy = (x ** (id, mxy))

public export
TypeProInterpCompToCompInterp : (q, p : TypeProAr) ->
  TypeProfNT
    (InterpTypeProAr (IntEndoProArComp Type TypeMor q p))
    (EndoProfCompose (InterpTypeProAr q) (InterpTypeProAr p))
TypeProInterpCompToCompInterp
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) x y
  ((pi ** qi ** mqp) ** (dmx, dmy)) =
    (pcontra pi ** ((qi ** (dmx, mqp)), (pi ** (id, dmy))))

public export
TypeProCompInterpToInterpComp : (q, p : TypeProAr) ->
  TypeProfNT
    (EndoProfCompose (InterpTypeProAr q) (InterpTypeProAr p))
    (InterpTypeProAr (IntEndoProArComp Type TypeMor q p))
TypeProCompInterpToInterpComp
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) x y
  (b ** ((qi ** (qcontm, qcovm)), (pi ** (pcontm, pcovm)))) =
    ((pi ** qi ** pcontm . qcovm) ** (qcontm, pcovm))

public export
TypeDiIdToIdInterp :
  TypeProfDiNT (InterpTypeProAr (IntProArId Type)) HomProf
TypeDiIdToIdInterp x (i ** (mxi, mix)) = mix . mxi

public export
TypeIdInterpToDiId :
  TypeProfDiNT HomProf (InterpTypeProAr (IntProArId Type))
TypeIdInterpToDiId x mxx = (x ** (id, mxx))

public export
TypeDiInterpCompToCompInterp : (q, p : TypeProAr) ->
  TypeProfDiNT
    (InterpTypeProAr (TypeDiArComp q p))
    (EndoProfCompose (InterpTypeProAr q) (InterpTypeProAr p))
TypeDiInterpCompToCompInterp
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) x
  ((pi ** qi ** asn) ** (dmx, dmy)) =
    (pcontra pi ** ((qi ** (dmx, asn)), (pi ** (id, dmy))))

public export
TypeDiCompInterpToInterpComp : (q, p : TypeProAr) ->
  TypeProfDiNT
    (EndoProfCompose (InterpTypeProAr q) (InterpTypeProAr p))
    (InterpTypeProAr (TypeDiArComp q p))
TypeDiCompInterpToInterpComp
  (qpos ** (qcontra, qcovar)) (ppos ** (pcontra, pcovar)) x
  (b ** ((qi ** (xqc, qcb)), (pi ** (mbp, pcx)))) =
    ((pi ** qi ** mbp . qcb) ** (xqc, pcx))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
---- Universal morphisms of poly-(para)natural transformations on `Type` ----
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

-------------------------------------
---- Utility types and functions ----
-------------------------------------

public export
TypeProNTpos : (p, q : TypeProAr) -> Type
TypeProNTpos = IntPPNTpos {d=Type} {c=Type} {dmor=TypeMor} {cmor=TypeMor}

public export
TypeProNTcontra : (p, q : TypeProAr) -> TypeProNTpos p q -> Type
TypeProNTcontra = IntPPNTcontra {d=Type} {c=Type} {dmor=TypeMor} {cmor=TypeMor}

public export
TypeProNTcovar : (p, q : TypeProAr) -> TypeProNTpos p q -> Type
TypeProNTcovar = IntPPNTcovar {d=Type} {c=Type} {dmor=TypeMor} {cmor=TypeMor}

public export
typeProNTpos : {p, q : TypeProAr} -> TypeProNTar p q -> TypeProNTpos p q
typeProNTpos = intPPNTpos {c=Type} {cmor=TypeMor} {d=Type} {dmor=TypeMor}

public export
typeProNTcontra : {p, q : TypeProAr} -> (ar : TypeProNTar p q) ->
  TypeProNTcontra p q (typeProNTpos {p} {q} ar)
typeProNTcontra = intPPNTcontra {c=Type} {cmor=TypeMor} {d=Type} {dmor=TypeMor}

public export
typeProNTcovar : {p, q : TypeProAr} -> (ar : TypeProNTar p q) ->
  TypeProNTcovar p q (typeProNTpos {p} {q} ar)
typeProNTcovar = intPPNTcovar {c=Type} {cmor=TypeMor} {d=Type} {dmor=TypeMor}

public export
TypeDiNTpos : (p, q : TypeProAr) -> Type
TypeDiNTpos = IntPDiNTpos {c=Type} {mor=TypeMor}

public export
TypeDiNTcontra : (p, q : TypeProAr) -> TypeDiNTpos p q -> Type
TypeDiNTcontra = IntPDiNTcontra {c=Type} {mor=TypeMor}

public export
TypeDiNTcovar : (p, q : TypeProAr) -> TypeDiNTpos p q -> Type
TypeDiNTcovar = IntPDiNTcovar {c=Type} {mor=TypeMor}

public export
TypeProNTrestrict : (p, q : TypeProAr) -> TypeProNTar p q -> TypeDiNTar p q
TypeProNTrestrict p q = intPPNTrestrict {c=Type} {cmor=TypeMor} {p} {q}

public export
typeDiNTpos : {p, q : TypeProAr} -> TypeDiNTar p q -> TypeDiNTpos p q
typeDiNTpos = intPDiNTpos {c=Type} {mor=TypeMor}

public export
typeDiNTcontra : {p, q : TypeProAr} -> (ar : TypeDiNTar p q) ->
  TypeDiNTcontra p q (typeDiNTpos {p} {q} ar)
typeDiNTcontra = intPDiNTcontra {c=Type} {mor=TypeMor}

public export
typeDiNTcovar : {p, q : TypeProAr} -> (ar : TypeDiNTar p q) ->
  TypeDiNTcovar p q (typeDiNTpos {p} {q} ar)
typeDiNTcovar = intPDiNTcovar {c=Type} {mor=TypeMor}

-------------------------
---- Initial object ----
-------------------------

public export
TypeParaInitialPos : Type
TypeParaInitialPos = Void

public export
TypeParaInitialContra : TypeParaInitialPos -> Type
TypeParaInitialContra v = void v

public export
TypeParaInitialCovar : TypeParaInitialPos -> Type
TypeParaInitialCovar v = void v

public export
TypeParaInitial : TypeProAr
TypeParaInitial =
  (TypeParaInitialPos ** (TypeParaInitialContra, TypeParaInitialCovar))

public export
typeProFromInitialPos : (p : TypeProAr) -> TypeProNTpos TypeParaInitial p
typeProFromInitialPos p v = void v

public export
typeProFromInitialContra : (p : TypeProAr) ->
  TypeProNTcontra TypeParaInitial p (typeProFromInitialPos p)
typeProFromInitialContra p v = void v

public export
typeProFromInitialCovar : (p : TypeProAr) ->
  TypeProNTcovar TypeParaInitial p (typeProFromInitialPos p)
typeProFromInitialCovar p v = void v

public export
typeProFromInitial : (p : TypeProAr) -> TypeProNTar TypeParaInitial p
typeProFromInitial p =
  (typeProFromInitialPos p **
   (typeProFromInitialContra p,
    typeProFromInitialCovar p))

public export
typeParaFromInitial : (p : TypeProAr) -> TypeDiNTar TypeParaInitial p
typeParaFromInitial p =
  TypeProNTrestrict TypeParaInitial p $ typeProFromInitial p

public export
typeParaFromInitialPos : (p : TypeProAr) -> TypeDiNTpos TypeParaInitial p
typeParaFromInitialPos p =
  typeDiNTpos {p=TypeParaInitial} {q=p} $ typeParaFromInitial p

public export
typeParaFromInitialContra : (p : TypeProAr) ->
  TypeDiNTcontra TypeParaInitial p (typeParaFromInitialPos p)
typeParaFromInitialContra p =
  typeDiNTcontra {p=TypeParaInitial} {q=p} $ typeParaFromInitial p

public export
typeParaFromInitialCovar : (p : TypeProAr) ->
  TypeDiNTcovar TypeParaInitial p (typeParaFromInitialPos p)
typeParaFromInitialCovar p =
  typeDiNTcovar {p=TypeParaInitial} {q=p} $ typeParaFromInitial p

-------------------------
---- Terminal object ----
-------------------------

public export
TypeParaTerminalPos : Type
TypeParaTerminalPos = Unit

public export
TypeParaTerminalContra : TypeParaTerminalPos -> Type
TypeParaTerminalContra u = Unit

public export
TypeParaTerminalCovar : TypeParaTerminalPos -> Type
TypeParaTerminalCovar u = Void

public export
TypeParaTerminal : TypeProAr
TypeParaTerminal =
  (TypeParaTerminalPos ** (TypeParaTerminalContra, TypeParaTerminalCovar))

public export
typeProToTerminalPos : (p : TypeProAr) -> TypeProNTpos p TypeParaTerminal
typeProToTerminalPos p i = ()

public export
typeProToTerminalContra : (p : TypeProAr) ->
  TypeProNTcontra p TypeParaTerminal (typeProToTerminalPos p)
typeProToTerminalContra p i asn = ()

public export
typeProToTerminalCovar : (p : TypeProAr) ->
  TypeProNTcovar p TypeParaTerminal (typeProToTerminalPos p)
typeProToTerminalCovar p i v = void v

public export
typeProToTerminal : (p : TypeProAr) -> TypeProNTar p TypeParaTerminal
typeProToTerminal p =
  (typeProToTerminalPos p **
   (typeProToTerminalContra p,
    typeProToTerminalCovar p))

public export
typeParaToTerminal : (p : TypeProAr) -> TypeDiNTar p TypeParaTerminal
typeParaToTerminal p =
  TypeProNTrestrict p TypeParaTerminal $ typeProToTerminal p

public export
typeParaToTerminalPos : (p : TypeProAr) -> TypeDiNTpos p TypeParaTerminal
typeParaToTerminalPos p =
  typeDiNTpos {p} {q=TypeParaTerminal} $ typeParaToTerminal p

public export
typeParaToTerminalContra : (p : TypeProAr) ->
  TypeDiNTcontra p TypeParaTerminal (typeParaToTerminalPos p)
typeParaToTerminalContra p =
  typeDiNTcontra {p} {q=TypeParaTerminal} $ typeParaToTerminal p

public export
typeParaToTerminalCovar : (p : TypeProAr) ->
  TypeDiNTcovar p TypeParaTerminal (typeParaToTerminalPos p)
typeParaToTerminalCovar p =
  typeDiNTcovar {p} {q=TypeParaTerminal} $ typeParaToTerminal p

-------------------
---- Constants ----
-------------------

public export
TypeParaConst : Type -> TypeProAr
TypeParaConst x = (x ** (\_ => Unit, \_ => Void))

------------------------
---- Representables ----
------------------------

public export
TypeParaRepPos : Type -> Type -> Type
TypeParaRepPos x y = Unit

public export
TypeParaRepContra : (x, y : Type) -> TypeParaRepPos x y -> Type
TypeParaRepContra x y _ = x

public export
TypeParaRepCovar : (x, y : Type) -> TypeParaRepPos x y -> Type
TypeParaRepCovar x y _ = y

public export
TypeParaRep : Type -> Type -> TypeProAr
TypeParaRep x y =
  (TypeParaRepPos x y ** (TypeParaRepContra x y, TypeParaRepCovar x y))

public export
TypeParaContraRep : Type -> TypeProAr
TypeParaContraRep x = TypeParaRep x Void

public export
TypeParaCovarRep : Type -> TypeProAr
TypeParaCovarRep y = TypeParaRep Unit y

public export
TypeParaCovarId : TypeProAr
TypeParaCovarId = TypeParaCovarRep Unit

---------------------------
---- Binary coproducts ----
---------------------------

public export
TypeParaCoproductPos : TypeProAr -> TypeProAr -> Type
TypeParaCoproductPos p q = Either (ipaPos p) (ipaPos q)

public export
TypeParaCoproductContra : (p, q : TypeProAr) ->
  TypeParaCoproductPos p q -> Type
TypeParaCoproductContra p q i =
  case i of
    Left pi => ipaContra p pi
    Right qi => ipaContra q qi

public export
TypeParaCoproductCovar : (p, q : TypeProAr) ->
  TypeParaCoproductPos p q -> Type
TypeParaCoproductCovar p q i =
  case i of
    Left pi => ipaCovar p pi
    Right qi => ipaCovar q qi

public export
TypeParaCoproduct : TypeProAr -> TypeProAr -> TypeProAr
TypeParaCoproduct p q =
  (TypeParaCoproductPos p q **
   (TypeParaCoproductContra p q,
    TypeParaCoproductCovar p q))

public export
typeProInjLpos : (p, q : TypeProAr) -> TypeProNTpos p (TypeParaCoproduct p q)
typeProInjLpos p q = Left

public export
typeProInjLcontra : (p, q : TypeProAr) ->
  TypeProNTcontra p (TypeParaCoproduct p q) (typeProInjLpos p q)
typeProInjLcontra p q = sliceId (ipaContra p)

public export
typeProInjLcovar : (p, q : TypeProAr) ->
  TypeProNTcovar p (TypeParaCoproduct p q) (typeProInjLpos p q)
typeProInjLcovar p q = sliceId (ipaCovar p)

public export
typeProInjL : (p, q : TypeProAr) -> TypeProNTar p (TypeParaCoproduct p q)
typeProInjL p q =
  (typeProInjLpos p q **
   (typeProInjLcontra p q,
    typeProInjLcovar p q))

public export
typeParaInjL : (p, q : TypeProAr) -> TypeDiNTar p (TypeParaCoproduct p q)
typeParaInjL p q = TypeProNTrestrict p (TypeParaCoproduct p q) $ typeProInjL p q

public export
typeParaInjLpos : (p, q : TypeProAr) -> TypeDiNTpos p (TypeParaCoproduct p q)
typeParaInjLpos p q =
  typeDiNTpos {p} {q=(TypeParaCoproduct p q)} $ typeParaInjL p q

public export
typeParaInjLcontra : (p, q : TypeProAr) ->
  TypeDiNTcontra p (TypeParaCoproduct p q) (typeParaInjLpos p q)
typeParaInjLcontra p q =
  typeDiNTcontra {p} {q=(TypeParaCoproduct p q)} $ typeParaInjL p q

public export
typeParaInjLcovar : (p, q : TypeProAr) ->
  TypeDiNTcovar p (TypeParaCoproduct p q) (typeParaInjLpos p q)
typeParaInjLcovar p q =
  typeDiNTcovar {p} {q=(TypeParaCoproduct p q)} $ typeParaInjL p q

public export
typeProInjRpos : (p, q : TypeProAr) -> TypeProNTpos q (TypeParaCoproduct p q)
typeProInjRpos p q = Right

public export
typeProInjRcontra : (p, q : TypeProAr) ->
  TypeProNTcontra q (TypeParaCoproduct p q) (typeProInjRpos p q)
typeProInjRcontra p q = sliceId (ipaContra q)

public export
typeProInjRcovar : (p, q : TypeProAr) ->
  TypeProNTcovar q (TypeParaCoproduct p q) (typeProInjRpos p q)
typeProInjRcovar p q = sliceId (ipaCovar q)

public export
typeProInjR : (p, q : TypeProAr) -> TypeProNTar q (TypeParaCoproduct p q)
typeProInjR p q =
  (typeProInjRpos p q **
   (typeProInjRcontra p q,
    typeProInjRcovar p q))

public export
typeParaInjR : (p, q : TypeProAr) -> TypeDiNTar q (TypeParaCoproduct p q)
typeParaInjR p q = TypeProNTrestrict q (TypeParaCoproduct p q) $ typeProInjR p q

public export
typeParaInjRpos : (p, q : TypeProAr) -> TypeDiNTpos q (TypeParaCoproduct p q)
typeParaInjRpos p q =
  typeDiNTpos {p=q} {q=(TypeParaCoproduct p q)} $ typeParaInjR p q

public export
typeParaInjRcontra : (p, q : TypeProAr) ->
  TypeDiNTcontra q (TypeParaCoproduct p q) (typeParaInjRpos p q)
typeParaInjRcontra p q =
  typeDiNTcontra {p=q} {q=(TypeParaCoproduct p q)} $ typeParaInjR p q

public export
typeParaInjRcovar : (p, q : TypeProAr) ->
  TypeDiNTcovar q (TypeParaCoproduct p q) (typeParaInjRpos p q)
typeParaInjRcovar p q =
  typeDiNTcovar {p=q} {q=(TypeParaCoproduct p q)} $ typeParaInjR p q

public export
typeDiCasePos : {p, q, r : TypeProAr} ->
  TypeDiNTar p r -> TypeDiNTar q r ->
  TypeDiNTpos (TypeParaCoproduct p q) r
typeDiCasePos {p} {q} {r} pr qr i asn with (i)
  typeDiCasePos {p} {q} {r} pr qr i asn | Left pi = typeDiNTpos pr pi asn
  typeDiCasePos {p} {q} {r} pr qr i asn | Right qi = typeDiNTpos qr qi asn

public export
typeDiCaseContra : {p, q, r : TypeProAr} ->
  (pr : TypeDiNTar p r) -> (qr : TypeDiNTar q r) ->
  TypeDiNTcontra (TypeParaCoproduct p q) r (typeDiCasePos {p} {q} {r} pr qr)
typeDiCaseContra {p} {q} {r} pr qr i asn with (i)
  typeDiCaseContra {p} {q} {r} pr qr i asn | Left pi = typeDiNTcontra pr pi asn
  typeDiCaseContra {p} {q} {r} pr qr i asn | Right qi = typeDiNTcontra qr qi asn

public export
typeDiCaseCovar : {p, q, r : TypeProAr} ->
  (pr : TypeDiNTar p r) -> (qr : TypeDiNTar q r) ->
  TypeDiNTcovar (TypeParaCoproduct p q) r (typeDiCasePos {p} {q} {r} pr qr)
typeDiCaseCovar {p} {q} {r} pr qr i asn with (i)
  typeDiCaseCovar {p} {q} {r} pr qr i asn | Left pi = typeDiNTcovar pr pi asn
  typeDiCaseCovar {p} {q} {r} pr qr i asn | Right qi = typeDiNTcovar qr qi asn

public export
typeDiCase : {p, q, r : TypeProAr} ->
  TypeDiNTar p r -> TypeDiNTar q r -> TypeDiNTar (TypeParaCoproduct p q) r
typeDiCase {p} {q} {r} pr qr =
  (typeDiCasePos pr qr **
   (typeDiCaseContra pr qr,
    typeDiCaseCovar pr qr))

-------------------------
---- Binary products ----
-------------------------

public export
TypeParaProductPos : TypeProAr -> TypeProAr -> Type
TypeParaProductPos p q = Pair (ipaPos p) (ipaPos q)

public export
TypeParaProductContra : (p, q : TypeProAr) ->
  TypeParaProductPos p q -> Type
TypeParaProductContra p q i = Pair (ipaContra p (fst i)) (ipaContra q (snd i))

public export
TypeParaProductCovar : (p, q : TypeProAr) ->
  TypeParaProductPos p q -> Type
TypeParaProductCovar p q i = Either (ipaCovar p (fst i)) (ipaCovar q (snd i))

public export
TypeParaProduct : TypeProAr -> TypeProAr -> TypeProAr
TypeParaProduct p q =
  (TypeParaProductPos p q **
   (TypeParaProductContra p q,
    TypeParaProductCovar p q))

public export
typeDiProdIntroPos : {p, q, r : TypeProAr} ->
  TypeDiNTar p q -> TypeDiNTar p r ->
  TypeDiNTpos p (TypeParaProduct q r)
typeDiProdIntroPos {p} {q} {r} pq pr i asn =
  (typeDiNTpos pq i asn, typeDiNTpos pr i asn)

public export
typeDiProdIntroContra : {p, q, r : TypeProAr} ->
  (pq : TypeDiNTar p q) -> (pr : TypeDiNTar p r) ->
  TypeDiNTcontra p (TypeParaProduct q r) (typeDiProdIntroPos {p} {q} {r} pq pr)
typeDiProdIntroContra {p} {q} {r} pq pr i asn d =
  (typeDiNTcontra pq i asn d, typeDiNTcontra pr i asn d)

public export
typeDiProdIntroCovar : {p, q, r : TypeProAr} ->
  (pq : TypeDiNTar p q) -> (pr : TypeDiNTar p r) ->
  TypeDiNTcovar p (TypeParaProduct q r) (typeDiProdIntroPos {p} {q} {r} pq pr)
typeDiProdIntroCovar {p} {q} {r} pq pr i asn d with (d)
  typeDiProdIntroCovar {p} {q} {r} pq pr i asn d | Left pd =
    typeDiNTcovar pq i asn pd
  typeDiProdIntroCovar {p} {q} {r} pq pr i asn d | Right qd =
    typeDiNTcovar pr i asn qd

public export
typeDiProdIntro : {p, q, r : TypeProAr} ->
  TypeDiNTar p q -> TypeDiNTar p r -> TypeDiNTar p (TypeParaProduct q r)
typeDiProdIntro {p} {q} {r} pq pr =
  (typeDiProdIntroPos pq pr **
   (typeDiProdIntroContra pq pr,
    typeDiProdIntroCovar pq pr))

public export
typeParaProj1pos : (p, q : TypeProAr) -> TypeDiNTpos (TypeParaProduct p q) p
typeParaProj1pos p q i asn = fst i

public export
typeParaProj1contra : (p, q : TypeProAr) ->
  TypeDiNTcontra (TypeParaProduct p q) p (typeParaProj1pos p q)
typeParaProj1contra p q i asn d = fst d

public export
typeParaProj1covar : (p, q : TypeProAr) ->
  TypeDiNTcovar (TypeParaProduct p q) p (typeParaProj1pos p q)
typeParaProj1covar p q i asn d = Left d

public export
typeParaProj1 : (p, q : TypeProAr) ->
  TypeDiNTar (TypeParaProduct p q) p
typeParaProj1 p q =
  (typeParaProj1pos p q **
   (typeParaProj1contra p q,
    typeParaProj1covar p q))

public export
typeParaProj2pos : (p, q : TypeProAr) -> TypeDiNTpos (TypeParaProduct p q) q
typeParaProj2pos p q i asn = snd i

public export
typeParaProj2contra : (p, q : TypeProAr) ->
  TypeDiNTcontra (TypeParaProduct p q) q (typeParaProj2pos p q)
typeParaProj2contra p q i asn d = snd d

public export
typeParaProj2covar : (p, q : TypeProAr) ->
  TypeDiNTcovar (TypeParaProduct p q) q (typeParaProj2pos p q)
typeParaProj2covar p q i asn d = Right d

public export
typeParaProj2 : (p, q : TypeProAr) ->
  TypeDiNTar (TypeParaProduct p q) q
typeParaProj2 p q =
  (typeParaProj2pos p q **
   (typeParaProj2contra p q,
    typeParaProj2covar p q))

----------------------------------------------------
---- Distributivity of products over coproducts ----
----------------------------------------------------

public export
typeParaDistribPos : (p, q, r : TypeProAr) ->
  TypeDiNTpos
    (TypeParaProduct p (TypeParaCoproduct q r))
    (TypeParaCoproduct (TypeParaProduct p q) (TypeParaProduct p r))
typeParaDistribPos p q r i asn with (i)
  typeParaDistribPos p q r i asn | (pi, Left qi) = Left (pi, qi)
  typeParaDistribPos p q r i asn | (pi, Right ri) = Right (pi, ri)

public export
typeParaDistribContra : (p, q, r : TypeProAr) ->
  TypeDiNTcontra
    (TypeParaProduct p (TypeParaCoproduct q r))
    (TypeParaCoproduct (TypeParaProduct p q) (TypeParaProduct p r))
    (typeParaDistribPos p q r)
typeParaDistribContra p q r i asn d with (i)
  typeParaDistribContra p q r i asn d | (pi, Left qi) = d
  typeParaDistribContra p q r i asn d | (pi, Right ri) = d

public export
typeParaDistribCovar : (p, q, r : TypeProAr) ->
  TypeDiNTcovar
    (TypeParaProduct p (TypeParaCoproduct q r))
    (TypeParaCoproduct (TypeParaProduct p q) (TypeParaProduct p r))
    (typeParaDistribPos p q r)
typeParaDistribCovar p q r i asn d with (i)
  typeParaDistribCovar p q r i asn d | (pi, Left qi) = d
  typeParaDistribCovar p q r i asn d | (pi, Right ri) = d

public export
typeParaDistrib : (p, q, r : TypeProAr) ->
  TypeDiNTar
    (TypeParaProduct p (TypeParaCoproduct q r))
    (TypeParaCoproduct (TypeParaProduct p q) (TypeParaProduct p r))
typeParaDistrib p q r =
  (typeParaDistribPos p q r **
   (typeParaDistribContra p q r,
    typeParaDistribCovar p q r))

---------------------
---- Hom-objects ----
---------------------

-- We compute hom-objects in steps, beginning with representable domains.

-- First we consider hom-objects whose domains are covariant representables --
-- that is, they ignore their contravariant arguments (in other words, they
-- are representables represened by pairs with contravariant component `Unit`).

public export
TypeParaCovarRepHomObjPos : Type -> TypeProAr -> Type
TypeParaCovarRepHomObjPos p q = (qi : ipaPos q ** ipaCovar q qi -> Either () p)

public export
TypeParaCovarRepHomObjContra : (p : Type) -> (q : TypeProAr) ->
  (i : TypeParaCovarRepHomObjPos p q) -> Type
TypeParaCovarRepHomObjContra p q i = ipaContra q $ fst i

public export
TypeParaCovarRepHomObjCovarSnd : (p : Type) -> (q : TypeProAr) ->
  (i : TypeParaCovarRepHomObjPos p q) -> ipaCovar q (fst i) -> Type
TypeParaCovarRepHomObjCovarSnd p q i qcov with (snd i qcov)
  TypeParaCovarRepHomObjCovarSnd p q i qcov | Left () = Unit
  TypeParaCovarRepHomObjCovarSnd p q i qcov | Right ep = Void

public export
TypeParaCovarRepHomObjCovar : (p : Type) -> (q : TypeProAr) ->
  (i : TypeParaCovarRepHomObjPos p q) -> Type
TypeParaCovarRepHomObjCovar p q i =
  DPair (ipaCovar q $ fst i) (TypeParaCovarRepHomObjCovarSnd p q i)

public export
TypeParaCovarRepHomObj : Type -> TypeProAr -> TypeProAr
TypeParaCovarRepHomObj p q =
  (TypeParaCovarRepHomObjPos p q **
   (TypeParaCovarRepHomObjContra p q,
    TypeParaCovarRepHomObjCovar p q))

public export
typeParaCovarRepEvalPos : (p : Type) -> (q : TypeProAr) ->
  TypeProNTpos
    (TypeParaProduct (TypeParaCovarRepHomObj p q) (TypeParaCovarRep p))
    q
typeParaCovarRepEvalPos p q i = fst $ fst i

public export
typeParaCovarRepEvalContra : (p : Type) -> (q : TypeProAr) ->
  TypeProNTcontra
    (TypeParaProduct (TypeParaCovarRepHomObj p q) (TypeParaCovarRep p))
    q
    (typeParaCovarRepEvalPos p q)
typeParaCovarRepEvalContra p q i d = fst d

public export
typeParaCovarRepEvalCovar : (p : Type) -> (q : TypeProAr) ->
  TypeProNTcovar
    (TypeParaProduct (TypeParaCovarRepHomObj p q) (TypeParaCovarRep p))
    q
    (typeParaCovarRepEvalPos p q)
typeParaCovarRepEvalCovar p q i d with (snd (fst i) d) proof eq
  typeParaCovarRepEvalCovar p q i d | Left () = Left (d ** rewrite eq in ())
  typeParaCovarRepEvalCovar p q i d | Right ep = Right ep

public export
typeParaCovarRepEval : (p : Type) -> (q : TypeProAr) ->
  TypeProNTar
    (TypeParaProduct (TypeParaCovarRepHomObj p q) (TypeParaCovarRep p))
    q
typeParaCovarRepEval p q =
  (typeParaCovarRepEvalPos p q **
   (typeParaCovarRepEvalContra p q,
    typeParaCovarRepEvalCovar p q))

public export
typeParaCovarRepCurryPos : {q : Type} -> {p, r : TypeProAr} ->
  TypeProNTar (TypeParaProduct p (TypeParaCovarRep q)) r ->
  TypeProNTpos p (TypeParaCovarRepHomObj q r)
typeParaCovarRepCurryPos {q} {p} {r} (onpos ** (oncontra, oncovar)) i =
  (onpos (i, ()) **
   \rcov => case oncovar (i, ()) rcov of
    Left pcov => Left ()
    Right elq => Right elq)

public export
typeParaCovarRepCurryContra : {q : Type} -> {p, r : TypeProAr} ->
  (ar : TypeProNTar (TypeParaProduct p (TypeParaCovarRep q)) r) ->
  TypeProNTcontra
    p
    (TypeParaCovarRepHomObj q r)
    (typeParaCovarRepCurryPos {q} {p} {r} ar)
typeParaCovarRepCurryContra (onpos ** (oncontra, oncovar)) pi pcont =
  oncontra (pi, ()) (pcont, ())

public export
typeParaCovarRepCurryCovar : {q : Type} -> {p, r : TypeProAr} ->
  (ar : TypeProNTar (TypeParaProduct p (TypeParaCovarRep q)) r) ->
  TypeProNTcovar
    p
    (TypeParaCovarRepHomObj q r)
    (typeParaCovarRepCurryPos {q} {p} {r} ar)
typeParaCovarRepCurryCovar (onpos ** (oncontra, oncovar)) pi (rcov1 ** rcov2)
    with (oncovar (pi, ()) rcov1) proof eq
  typeParaCovarRepCurryCovar (onpos ** (oncontra, oncovar)) pi (rcov1 ** rcov2)
    | Left pcov = pcov
  typeParaCovarRepCurryCovar (onpos ** (oncontra, oncovar)) pi (rcov1 ** rcov2)
    | Right elq = void rcov2

public export
typeParaCovarRepCurry : {q : Type} -> {p, r : TypeProAr} ->
  TypeProNTar (TypeParaProduct p (TypeParaCovarRep q)) r ->
  TypeProNTar p (TypeParaCovarRepHomObj q r)
typeParaCovarRepCurry {q} {p} {r} ar =
  (typeParaCovarRepCurryPos {q} {p} {r} ar **
   (typeParaCovarRepCurryContra {q} {p} {r} ar,
    typeParaCovarRepCurryCovar {q} {p} {r} ar))

-- Next we consider hom-objects whose domains are contravariant
-- representables that is, they ignore their covariant arguments (in other
-- words, they are representables represened by pairs with covariant component
-- `Void`).

public export
TypeParaContraRepHomObjPos : Type -> TypeProAr -> Type
TypeParaContraRepHomObjPos p q = ipaPos q

public export
TypeParaContraRepHomObjContra : (p : Type) -> (q : TypeProAr) ->
  (i : TypeParaContraRepHomObjPos p q) -> Type
TypeParaContraRepHomObjContra p q i = p -> ipaContra q i

public export
TypeParaContraRepHomObjCovar : (p : Type) -> (q : TypeProAr) ->
  (i : TypeParaContraRepHomObjPos p q) -> Type
TypeParaContraRepHomObjCovar p q i = ipaCovar q i

public export
TypeParaContraRepHomObj : Type -> TypeProAr -> TypeProAr
TypeParaContraRepHomObj p q =
  (TypeParaContraRepHomObjPos p q **
   (TypeParaContraRepHomObjContra p q,
    TypeParaContraRepHomObjCovar p q))

public export
typeParaContraRepEvalPos : (p : Type) -> (q : TypeProAr) ->
  TypeProNTpos
    (TypeParaProduct (TypeParaContraRepHomObj p q) (TypeParaContraRep p))
    q
typeParaContraRepEvalPos p q i = fst i

public export
typeParaContraRepEvalContra : (p : Type) -> (q : TypeProAr) ->
  TypeProNTcontra
    (TypeParaProduct (TypeParaContraRepHomObj p q) (TypeParaContraRep p))
    q
    (typeParaContraRepEvalPos p q)
typeParaContraRepEvalContra p q i d = fst d (snd d)

public export
typeParaContraRepEvalCovar : (p : Type) -> (q : TypeProAr) ->
  TypeProNTcovar
    (TypeParaProduct (TypeParaContraRepHomObj p q) (TypeParaContraRep p))
    q
    (typeParaContraRepEvalPos p q)
typeParaContraRepEvalCovar p q i d = Left d

public export
typeParaContraRepEval : (p : Type) -> (q : TypeProAr) ->
  TypeProNTar
    (TypeParaProduct (TypeParaContraRepHomObj p q) (TypeParaContraRep p))
    q
typeParaContraRepEval p q =
  (typeParaContraRepEvalPos p q **
   (typeParaContraRepEvalContra p q,
    typeParaContraRepEvalCovar p q))

public export
typeParaContraRepCurryPos : {q : Type} -> {p, r : TypeProAr} ->
  TypeProNTar (TypeParaProduct p (TypeParaContraRep q)) r ->
  TypeProNTpos p (TypeParaContraRepHomObj q r)
typeParaContraRepCurryPos {q} {p} {r} (onpos ** (oncontra, oncovar)) i =
  onpos (i, ())

public export
typeParaContraRepCurryContra : {q : Type} -> {p, r : TypeProAr} ->
  (ar : TypeProNTar (TypeParaProduct p (TypeParaContraRep q)) r) ->
  TypeProNTcontra
    p
    (TypeParaContraRepHomObj q r)
    (typeParaContraRepCurryPos {q} {p} {r} ar)
typeParaContraRepCurryContra (onpos ** (oncontra, oncovar)) pi pcont elq =
  oncontra (pi, ()) (pcont, elq)

public export
typeParaContraRepCurryCovar : {q : Type} -> {p, r : TypeProAr} ->
  (ar : TypeProNTar (TypeParaProduct p (TypeParaContraRep q)) r) ->
  TypeProNTcovar
    p
    (TypeParaContraRepHomObj q r)
    (typeParaContraRepCurryPos {q} {p} {r} ar)
typeParaContraRepCurryCovar (onpos ** (oncontra, oncovar)) pi rcov =
  case oncovar (pi, ()) rcov of
    Left pcov => pcov
    Right v => void v

public export
typeParaContraRepCurry : {q : Type} -> {p, r : TypeProAr} ->
  TypeProNTar (TypeParaProduct p (TypeParaContraRep q)) r ->
  TypeProNTar p (TypeParaContraRepHomObj q r)
typeParaContraRepCurry {q} {p} {r} ar =
  (typeParaContraRepCurryPos {q} {p} {r} ar **
   (typeParaContraRepCurryContra {q} {p} {r} ar,
    typeParaContraRepCurryCovar {q} {p} {r} ar))

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---- Category of pi types, viewed as a subcategory of the category of monos ----
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

public export
PiMonCatObj : Type
PiMonCatObj = (dom : Type ** cod : SliceObj dom ** Pi {a=dom} cod)

public export
PiMonCatMor : IntMorSig PiMonCatObj
PiMonCatMor (d ** c ** m) (d' ** c' ** m') =
  (l : d' -> d **
   r1 : (ed' : d') -> c' ed' -> d **
   comm1 : (ed' : d') -> r1 ed' (m' ed') = l ed' **
   r2 : (ed' : d') -> (ec' : c' ed') -> c (r1 ed' ec') **
   (ed' : d') -> m (l ed') = replace {p=c} (comm1 ed') (r2 ed' (m' ed')))

-------------------------------------------
-------------------------------------------
---- Polydifunctors as enriched arenas ----
-------------------------------------------
-------------------------------------------

-------------------------------
---- Polydifunctor objects ----
-------------------------------

{-
 - We might view a polydifunctor as a functor from
 - `Type` to `[op(Type), Type`]`.  As such, we could define it as a parametric
 - right adjoint from the category of presheaves (into `Type`) over the
 - terminal category -- which is equivalent to `Type` itself -- to the
 - category of presheaves over `Type`.  Examining the formula for PRA
 - functors between presheaf categories at
 - https://ncatlab.org/nlab/show/parametric+right+adjoint#generic_morphisms ,
 - we set `I := 1` and `J := Type`, and thus determine that the PRA functor
 - is determined by the following data:
 -
 -  - An object `T1` in `[op(J), Type]`, i.e. a presheaf over `Type`,
 -    which, because we are trying to define a polynomial _difunctor_,
 -    we treat as a Dirichlet functor
 -  - A functor `el_op(T1) -> [op(I), Type]`; since `I` is the terminal
 -    category, this reduces to a functor in `[el_op(T1), Type]`.
 -    And because that is a presheaf on a category of elements, it is
 -    equivalently a slice over `T1`.
 -}
public export
record PDiData where
  constructor PDiD
  pdiT1 : MLDirichCatObj
  pdiF : MlDirichSlObj pdiT1

public export
PDiPos1 : PDiData -> Type
PDiPos1 = dfPos . pdiT1

public export
PDiPos2 : (pdid : PDiData) -> PDiPos1 pdid -> Type
PDiPos2 pdid = mdsOnPos (pdiF pdid)

public export
PDiDir1 : (pdid : PDiData) -> PDiPos1 pdid -> Type
PDiDir1 pdid = dfDir (pdiT1 pdid)

public export
PDiDir2 : (pdid : PDiData) ->
  (i : PDiPos1 pdid) -> PDiPos2 pdid i -> PDiDir1 pdid i -> Type
PDiDir2 pdid = mdsDir (pdiF pdid)

public export
PDiTot1 : (pdid : PDiData) -> Type
PDiTot1 = dfTot . pdiT1

public export
PDiTot2 : (pdid : PDiData) -> Type
PDiTot2 pdid = mlDirichSlObjTotTot {ar=(pdiT1 pdid)} $ pdiF pdid

-----------------------------------------------------------------
---- Polydifunctors as families of slice polynomial functors ----
-----------------------------------------------------------------

public export
PDiToSPFdepData : (pdid : PDiData) ->
  SPFdepData {b=(PDiPos1 pdid)} (PDiDir1 pdid) (const Unit)
PDiToSPFdepData pdid = MlDirichSlToSPFDD {ar=(pdiT1 pdid)} $ pdiF pdid

-- For each position of `T1`, we have a dependent polynomial functor from
-- the slice category of that position's direction to `Type` (which is
-- equivalent to the slice category of `Type` over `Unit`).
public export
PDiToSPFData : (pdid : PDiData) ->
  (i : PDiPos1 pdid) -> SPFData (PDiDir1 pdid i) Unit
PDiToSPFData pdid = SPFDataFamFromDep (PDiToSPFdepData pdid)

------------------------------------------
---- Interpretation of polydifunctors ----
------------------------------------------

-- From the formula in the "Proposition 2.10" section of the ncat
-- page on parametric right adjoints.  `z` here is the covariant
-- argument -- a presheaf from the terminal category to `Type`,
-- which is simply a type.  `j` is the contravariant argument,
-- an object of `op(Type)`.
public export
InterpPDiE : (pdid : PDiData) ->
  (j : Type) -> InterpDirichFunc (pdiT1 pdid) j -> Type
InterpPDiE pdid = InterpMlDirichSlObj {ar=(pdiT1 pdid)} (pdiF pdid)

public export
InterpPDiEform : (pdid : PDiData) ->
  (j : Type) -> (i1 : PDiPos1 pdid) -> (d1 : j -> PDiDir1 pdid i1) -> Type
InterpPDiEform pdid j i1 d1 =
  (i2 : mdsOnPos (pdiF pdid) i1 **
   Pi {a=j} (mdsDir (pdiF pdid) i1 i2 . d1))

public export
InterpPDiEtoForm : (pdid : PDiData) ->
  (j : Type) -> (i1 : PDiPos1 pdid) -> (d1 : j -> PDiDir1 pdid i1) ->
  InterpPDiE pdid j (i1 ** d1) -> InterpPDiEform pdid j i1 d1
InterpPDiEtoForm pdid j i1 d1 = dpMapSnd $ \i2, pid, ej => pid ej ()

public export
InterpPDiEfromForm : (pdid : PDiData) ->
  (j : Type) -> (i1 : PDiPos1 pdid) -> (d1 : j -> PDiDir1 pdid i1) ->
  InterpPDiEform pdid j i1 d1 -> InterpPDiE pdid j (i1 ** d1)
InterpPDiEfromForm pdid j i1 d1 = dpMapSnd $ \i2, pid, ej, () => pid ej

public export
InterpPolyDi : (pdid : PDiData) -> (j, z : Type) -> Type
InterpPolyDi pdid j z =
  (x : InterpDirichFunc (pdiT1 pdid) j ** InterpPDiE pdid j x -> z)

public export
InterpPolyDiForm : (pdid : PDiData) -> (j, z : Type) -> Type
InterpPolyDiForm pdid j z =
  (i1: PDiPos1 pdid **
   d1 : j -> PDiDir1 pdid i1 **
   (i2 : mdsOnPos (pdiF pdid) i1) ->
     Pi {a=j} (mdsDir (pdiF pdid) i1 i2 . d1) -> z)

public export
InterpPolyDiToForm : (pdid : PDiData) -> (j, z : Type) ->
  InterpPolyDi pdid j z -> InterpPolyDiForm pdid j z
InterpPolyDiToForm pdid j z ((i1 ** d1) ** d2) =
  (i1 ** d1 ** \i2, pid => d2 (i2 ** \ej, () => pid ej))

public export
InterpPolyDiFromForm : (pdid : PDiData) -> (j, z : Type) ->
  InterpPolyDiForm pdid j z -> InterpPolyDi pdid j z
InterpPolyDiFromForm pdid j z (i1 ** (d1 ** d2)) =
  ((i1 ** d1) ** \(i2 ** pid) => d2 i2 $ \ej => pid ej ())

-- This is the interpretation of the above family of `SPFData`s.
public export
InterpPDiSPF : (pdid : PDiData) ->
  (i : PDiPos1 pdid) -> SliceObj (PDiDir1 pdid i) -> Type
InterpPDiSPF pdid i sl = InterpSPFdepDataEl (PDiToSPFdepData pdid) i sl ()

-- The interpretation of the application to the first parameter of the
-- curried form of the dependent profunctor (AKA presheaf on the
-- twisted-arrow category) specified by a `PDiData`, returning a
-- slice polynomial functor over the selected direction.
public export
InterpPDi1SPF : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  SPFData (idfDir {p=(pdiT1 pdid)} idf) Unit
InterpPDi1SPF pdid x idf = PDiToSPFData pdid (idfPos {p=(pdiT1 pdid)} idf)

public export
InterpPDi1 : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  idfDirSl {p=(pdiT1 pdid)} idf -> Type
InterpPDi1 pdid x idf = InterpPDiSPF pdid (idfPos {p=(pdiT1 pdid)} idf)

public export
InterpPDi2SPF : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  SPFData x Unit
InterpPDi2SPF pdid x idf = spfdPrecompSigma (snd idf) (InterpPDi1SPF pdid x idf)

public export
InterpPDi2u : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  SliceFunctor x Unit
InterpPDi2u pdid x idf = InterpSPFData $ InterpPDi2SPF pdid x idf

public export
InterpPDi2SPFmap : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  SliceFMap (InterpPDi2u pdid x idf)
InterpPDi2SPFmap pdid x idf = InterpSPFDataMap $ InterpPDi2SPF pdid x idf

public export
InterpPDi2 : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  SliceObj x -> Type
InterpPDi2 pdid x idf y = InterpPDi2u pdid x idf y ()

public export
InterpPDi2map : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  (y, y' : SliceObj x) ->
  SliceMorphism {a=x} y y' ->
  InterpPDi2 pdid x idf y -> InterpPDi2 pdid x idf y'
InterpPDi2map pdid x idf y y' m = InterpPDi2SPFmap pdid x idf y y' m ()

public export
InterpPDi : (pdid : PDiData) -> (x : Type) -> (y : SliceObj x) -> Type
InterpPDi pdid x =
  Sigma {a=(InterpDirichFunc (pdiT1 pdid) x)} . flip (InterpPDi2 pdid x)

public export
InterpPDiu : (pdid : PDiData) -> (x : Type) -> SliceFunctor x Unit
InterpPDiu pdid x y () = InterpPDi pdid x y

---------------------------------------------------
---- Morphism-map components of polydifunctors ----
---------------------------------------------------

public export
PDiLmapu : (pdid : PDiData) -> (x, x' : Type) -> (m : x' -> x) ->
  SliceNatTrans {x=x'} {y=Unit}
    (InterpPDiu pdid x . SliceFibSigmaF m)
    (InterpPDiu pdid x')
PDiLmapu pdid x x' m y' () =
  dpBimap (InterpDFMap (pdiT1 pdid) m)
  $ \(i1 ** i2), ((ep ** dm1) ** dm2) =>
    ((ep **
     \ex, d1 =>
        let sfs = dm2 (sfsFst $ dm1 ex d1) ((ex ** d1) ** Refl) in
        rewrite sym (sfsEq $ dm1 ex d1) in
        rewrite sym (sfsEq sfs) in
        SFS (sfsFst sfs) ()) **
     \ex', ((ex ** d1) ** xeq) =>
      rewrite sym xeq in
      sfsSnd $ dm2 (sfsFst $ dm1 ex d1) ((ex ** d1) ** Refl))

public export
PDiLmap : (pdid : PDiData) -> (x, x' : Type) -> (m : x' -> x) ->
  (y' : SliceObj x') ->
  InterpPDi pdid x (SliceFibSigmaF m y') -> InterpPDi pdid x' y'
PDiLmap pdid x x' m y' = PDiLmapu pdid x x' m y' ()

public export
PDiRmap : (pdid : PDiData) -> (x : Type) -> (y, y' : SliceObj x) ->
  SliceMorphism {a=x} y y' ->
  InterpPDi pdid x y -> InterpPDi pdid x y'
PDiRmap pdid x y y' m =
  dpMapSnd $ \i1 => dpMapSnd $ \p2, i2, d1, d2 => m d1 $ i2 d1 d2

public export
PDiDimap : (pdid : PDiData) ->
  (x, x' : Type) -> (y : SliceObj x) -> (y' : SliceObj x') ->
  (mx : x' -> x) -> (my : SliceMorphism {a=x} y (SliceFibSigmaF mx y')) ->
  InterpPDi pdid x y -> InterpPDi pdid x' y'
PDiDimap pdid x x' y y' mx my =
  PDiLmap pdid x x' mx y' . PDiRmap pdid x y (SliceFibSigmaF mx y') my

public export
PDiDimapDP : (pdid : PDiData) ->
  (x : Type) -> (y, x' : SliceObj x) ->
  (y' : SliceObj $ Sigma {a=x} x') ->
  (lm : (ex : x) -> y ex -> x' ex) ->
  (rm : (ex : x) -> (ey : y ex) -> y' (ex ** lm ex ey)) ->
  InterpPDi pdid x y -> InterpPDi pdid (Sigma {a=x} x') y'
PDiDimapDP pdid x y x' y' lm rm =
  PDiDimap pdid x (Sigma x') y y' DPair.fst $
    \ex, ey => SFS (ex ** lm ex ey) (rm ex ey)

-----------------------------------------------------------
---- Categories of diagonal elements of polydifunctors ----
-----------------------------------------------------------

-- Suppose we want to write a restricted version of `dimap` that is only
-- required to operate on diagonal elements.  Diagonal elements are those
-- where `x ~=~ y` and `x' ~=~ y'`, which may be represented either by
-- the `y`s being slices whose values are `const Unit` (the terminal objects
-- of the slice category over `x`, which is the `id` morphism on `x` in
-- categorial style), or, if we take a twisted-arrow viewpoint, the morphism
-- being the identity.
--
-- Note that the parameters `x`, `x'`, and `m` constitute a monomorphism
-- from `x` to `Sigma {a=x} x'`, where the proof that it is a monomorphism
-- is the exhibition of a left inverse, namely the projection from
-- `Sigma {a=x} x'` to `x`.
--
-- Note also that `Pi {a=x} x'` may equivalently be viewed as
-- `SliceMorphism {a=x} (SliceObjTerminal x) x'` -- that is, it is
-- a section, or global element (or "point"), of `x'`.  See
-- https://ncatlab.org/nlab/show/generalized+element#in_toposes.

public export
InterpPDiDiag : (pdid : PDiData) -> (x : Type) -> Type
InterpPDiDiag pdid x = InterpPDi pdid x (SliceObjTerminal x)

public export
PDiDiagMap : (pdid : PDiData) ->
  (x : Type) -> (x' : SliceObj x) -> Pi {a=x} x' ->
  InterpPDiDiag pdid x -> InterpPDiDiag pdid (Sigma {a=x} x')
PDiDiagMap pdid x x' m =
  PDiDimapDP pdid
    x (SliceObjTerminal x) x' (SliceObjTerminal $ Sigma {a=x} x')
    (\ex, u => m ex)
    (\_, _ => ())

public export
PDiDiagElemObj : PDiData -> Type
PDiDiagElemObj = Sigma {a=Type} . InterpPDiDiag

public export
data PDiDiagElemMor : (pdid : PDiData) -> IntMorSig (PDiDiagElemObj pdid) where
  PDEM : {pdid : PDiData} -> {x : Type} -> {x' : SliceObj x} ->
    (el : InterpPDiDiag pdid x) -> (m : Pi {a=x} x') ->
    PDiDiagElemMor pdid
      (x ** el)
      (Sigma {a=x} x' ** PDiDiagMap pdid x x' m el)

---------------------------------------------------
---------------------------------------------------
---- Self-representation of Dirichlet functors ----
---------------------------------------------------
---------------------------------------------------

-- We can define a functor from `Type` to the category of Dirichlet
-- functors by defining a slice functor between the Dirichlet-functor
-- slice categories over `dfRepVoid` and `dfRepUnit`, because, as explained
-- in the comments to their definitions, those functors' categories of
-- elements are (equivalent to) `Type` and the category of Dirichlet functors
-- on `Type`, respectively.
public export
TypeDirichData : Type
TypeDirichData = PRAData MLDirichCat.dfRepVoid MLDirichCat.dfRepUnit

public export
InterpPRAdataOmapFromPDi : TypeDirichData ->
  MlDirichSlFunc MLDirichCat.dfRepVoid MLDirichCat.dfRepUnit
InterpPRAdataOmapFromPDi = InterpPRAdataOmap

public export
InterpPDiPRAdataOmap : (tdd : TypeDirichData) -> Type -> MLDirichCatObj
InterpPDiPRAdataOmap tdd =
  dfSlRepUnitToDirich . InterpPRAdataOmapFromPDi tdd . dfTypeToSlRepVoid

public export
InterpPDiDataOmap : (tdd : TypeDirichData) -> Type -> Type -> Type
InterpPDiDataOmap tdd x y = InterpDirichFunc (InterpPDiPRAdataOmap tdd y) x

public export
InterpPDiDataDimap : (tdd : TypeDirichData) ->
  IntEndoDimapSig TypeObj TypeMor (InterpPDiDataOmap tdd)
InterpPDiDataDimap (PRAD (MDSobj x slx) (MDSobj slsx _)) s t a b mas mtb
  ((ex ** mxt) ** msx) =
    ((ex ** \(() ** eslx) => mtb $ mxt (() ** eslx)) **
     \ea => (fst (msx $ mas ea) ** \_, _, v => void v))

----------------------------------------------
----------------------------------------------
---- Universal families as twisted arrows ----
----------------------------------------------
----------------------------------------------

public export
TwistArrArType : Type
TwistArrArType = TwistArrAr TypeCat

public export
TwistArrMorType : IntMorSig TwistArrArType
TwistArrMorType = TwistArrMor TypeCat

public export
twarDomType : TwistArrArType -> Type
twarDomType = twarDom {cat=TypeCat}

public export
twarCodType : (twar : TwistArrArType) -> SliceObj (twarDomType twar)
twarCodType = twarCod {cat=TypeCat}

public export
TwistPolyFuncType : Type
TwistPolyFuncType = TwistPolyFunc TypeCat

public export
tpfPosType : TwistPolyFuncType -> Type
tpfPosType = tpfPos {cat=TypeCat}

public export
tpfArType : (tpf : TwistPolyFuncType) -> tpfPosType tpf -> TwistArrArType
tpfArType = tpfAr {cat=TypeCat}

public export
tpfDomType : (tpf : TwistPolyFuncType) -> SliceObj (tpfPosType tpf)
tpfDomType = tpfDom {cat=TypeCat}

public export
tpfCodType : (tpf : TwistPolyFuncType) ->
  (i : tpfPosType tpf) -> SliceObj (tpfDomType tpf i)
tpfCodType = tpfCod {cat=TypeCat}

public export
TwistNTType : IntMorSig TwistPolyFuncType
TwistNTType = TwistNT TypeCat

public export
InterpTPFType : TwistPolyFuncType -> TwistArrArType -> Type
InterpTPFType = InterpTPF {cat=TypeCat}

public export
itpfOnCod : {tpf : TwistPolyFuncType} -> {twar : TwistArrArType} ->
  (itpf : InterpTPFType tpf twar) ->
  SliceMorphism {a=(twarDomType twar)}
    (BaseChangeF
      (itpfOnDom {cat=TypeCat} {tpf} {twar} itpf)
      (tpfCodType tpf $ itpfPos {cat=TypeCat} {tpf} {twar} itpf))
    (twarCodType twar)
itpfOnCod {tpf} {twar} itpf = DPair.snd (itpfDir {cat=TypeCat} itpf)

public export
twntOnCovar : {p, q : TwistPolyFuncType} ->
  (twnt : TwistNTType p q) ->
  (i : tpfPosType p) ->
    SliceMorphism {a=(tpfDomType p i)}
      (BaseChangeF
        (twntOnContra {cat=TypeCat} {p} {q} twnt i)
          (tpfCodType q $ twntOnPos {cat=TypeCat} {p} {q} twnt i))
      (tpfCodType p i)
twntOnCovar {p} {q} twnt i = DPair.snd (twntOnDir {cat=TypeCat} twnt i)

--------------------------------------------------------------------------
--------------------------------------------------------------------------
---- Metalanguage twisted-arrow ("di") arenas and polynomial functors ----
--------------------------------------------------------------------------
--------------------------------------------------------------------------

public export
record MLDiArena where
  constructor MLDiAr
  mdaAr : MLArena
  mdaPred :
    Pi {a=(pfPos mdaAr)} (SliceObj . pfDir {p=mdaAr})

public export
mdaPos : MLDiArena -> Type
mdaPos = pfPos . mdaAr

public export
mdaStruct : (mda : MLDiArena) -> SliceObj (mdaPos mda)
mdaStruct mda = pfDir {p=(mdaAr mda)}

public export
MDAterm : (mda : MLDiArena) -> SliceObj (mdaPos mda)
MDAterm mda i = Sigma {a=(mdaStruct mda i)} (mdaPred mda i)

public export
record MLDiNatTrans (dom, cod : MLDiArena) where
  constructor MLDiNT
  mdntOnPos :
    mdaPos dom -> mdaPos cod
  mdntOnTerm :
    SliceMorphism {a=(mdaPos dom)} (MDAterm cod . mdntOnPos) (MDAterm dom)

public export
record InterpMDA (mda : MLDiArena) (struct : Type) (pred : SliceObj struct)
    where
  constructor IMDA
  imdaPos : mdaPos mda
  imdaAssign : MDAterm mda imdaPos -> Sigma {a=struct} pred

-----------------------------------------------------------------
-----------------------------------------------------------------
---- Polydifunctors subject to polydinatural transformations ----
-----------------------------------------------------------------
-----------------------------------------------------------------

-------------------------------------
---- Arena form of polydifunctor ----
-------------------------------------

-- The positions of a polydifunctor map not to directions which are not
-- objects of `Type`, but morphisms (of `Type`).  In light of the
-- interpretation below, we can view these morphisms as the heteromorphisms
-- of a difunctor on `Type`, and also as the objects of the twisted-arrow
-- category on `Type`.  (Thus far they could also be objects of the arrow
-- category, but the interpretation below uses twisted-arrow morphisms,
-- not arrow morphisms.)
public export
record PolyDifunc where
  constructor PDF
  pdfPos : Type
  pdfCobase : SliceObj pdfPos
  pdfBase : SliceObj pdfPos
  pdfProj : SliceMorphism {a=pdfPos} pdfCobase pdfBase

-- The interpretation of a polydifunctor takes an object of the
-- twisted arrow category (of `Type`) and, as with polynomial
-- functors on other categories, comprises a choice of one of the
-- directions of the difunctor together with a (twisted-arrow)
-- morphism from that direction to the (twisted-arrow) object
-- that the functor is being applied to.
--
-- The difference between this and a general difunctor is the twisted-arrow
-- morphism:  without that, this would just determine a general profunctor
-- by its collage.  The twisted-arrow morphism constrains the profunctor
-- so that it only contains elements that can be "diagonalized" by the
-- morphism.
--
-- Note that when `y` is `x` and `m` is `id`, then this amounts to
-- a factorization of the identity on `x` through `pdfCobase` and
-- `pdfBase` via three morphisms.  If furthermore we choose a position
-- where `pdfCobase` is `pdfBase` and `pdfProj` is `id`, then this
-- interpretation becomes a factorization of the identity on `x` through
-- `pdfBase`, the type of directions at that position.  Such a factorization
-- is an epi (surjective) assignment of directions to `x`, together with
-- a mono (injective) assignment from `x` to the directions which effectively
-- constitutes a proof that `x` -- the type of variables -- contains no
-- "unused variables".
public export
record InterpPDF (pdf : PolyDifunc) (x, y : Type) (m : x -> y) where
  constructor IPDF
  ipdfPos : pdfPos pdf
  ipdfContraMor : x -> pdfCobase pdf ipdfPos
  ipdfCovarMor : pdfBase pdf ipdfPos -> y
  0 ipdfComm :
    FunExtEq (ipdfCovarMor . pdfProj pdf ipdfPos . ipdfContraMor) m

public export
InterpPDFdiag : (pdf : PolyDifunc) -> Type -> Type
InterpPDFdiag pdf x = InterpPDF pdf x x (Prelude.id {a=x})

public export
IPDFc : {pdf : PolyDifunc} -> {x, y : Type} ->
  (i : pdfPos pdf) ->
  (cnm : x -> pdfCobase pdf i) -> (cvm : pdfBase pdf i -> y) ->
  InterpPDF pdf x y (cvm . pdfProj pdf i . cnm)
IPDFc {pdf} {x} {y} i cnm cvm = IPDF i cnm cvm $ \fext => Refl

export
0 ipdfEqPos : {0 p, q : PolyDifunc} -> {0 x, y : Type} -> {0 m : x -> y} ->
  {ip : InterpPDF p x y m} -> {iq : InterpPDF q x y m} ->
  ip ~=~ iq -> ipdfPos ip ~=~ ipdfPos iq
ipdfEqPos {p} {q} {x} {y} {m}
  {ip=(IPDF pi mxpd mpcy pcomm)} {iq=(IPDF qi mxqd mqcy qcomm)} eq =
    case eq of Refl => Refl

export
0 ipdfEqDom : {0 p, q : PolyDifunc} -> {0 x, y : Type} -> {0 m : x -> y} ->
  {ip : InterpPDF p x y m} -> {iq : InterpPDF q x y m} ->
  ip ~=~ iq -> ipdfContraMor ip ~=~ ipdfContraMor iq
ipdfEqDom {p} {q} {x} {y} {m}
  {ip=(IPDF pi mxpd mpcy pcomm)} {iq=(IPDF qi mxqd mqcy qcomm)} eq =
    case eq of Refl => Refl

export
0 ipdfEqCod : {0 p, q : PolyDifunc} -> {0 x, y : Type} -> {0 m : x -> y} ->
  {ip : InterpPDF p x y m} -> {iq : InterpPDF q x y m} ->
  ip ~=~ iq -> ipdfCovarMor ip ~=~ ipdfCovarMor iq
ipdfEqCod {p} {q} {x} {y} {m}
  {ip=(IPDF pi mxpd mpcy pcomm)} {iq=(IPDF qi mxqd mqcy qcomm)} eq =
    case eq of Refl => Refl

export
0 ipdfEqComm : {0 p, q : PolyDifunc} -> {0 x, y : Type} -> {0 m : x -> y} ->
  {ip : InterpPDF p x y m} -> {iq : InterpPDF q x y m} ->
  ip ~=~ iq -> ipdfComm ip ~=~ ipdfComm iq
ipdfEqComm {p} {q} {x} {y} {m}
  {ip=(IPDF pi mxpd mpcy pcomm)} {iq=(IPDF qi mxqd mqcy qcomm)} eq =
    case eq of Refl => Refl

export
0 ipdfUip : FunExt ->
  {0 p : PolyDifunc} ->
  {0 x, y : Type} -> {0 m : x -> y} ->
  {ip, iq : InterpPDF p x y m} ->
  ipdfPos ip ~=~ ipdfPos iq ->
  ipdfContraMor ip ~=~ ipdfContraMor iq ->
  ipdfCovarMor ip ~=~ ipdfCovarMor iq ->
  ip = iq
ipdfUip fext {p=(PDF pp pd pc pm)} {x} {y} {m}
  {ip=(IPDF pi mxpd mpcy pcomm)} {iq=(IPDF _ _ _ qcomm)}
    Refl Refl Refl =
      let eqComm : (pcomm = qcomm) = (funExt $ \fext' => uip) in
      case eqComm of Refl => Refl

public export
InterpPDFlmap : (pdf : PolyDifunc) ->
  (0 s, t, a : Type) -> (mst : s -> t) -> (mas : a -> s) ->
  InterpPDF pdf s t mst -> InterpPDF pdf a t (mst . mas)
InterpPDFlmap (PDF pos dom cod proj) s t a mst mas (IPDF i msi mit comm) =
  IPDF i (msi . mas) mit
    $ \fext => funExt $ \ea => fcong {x=(mas ea)} (comm fext)

public export
InterpPDFrmap : (pdf : PolyDifunc) ->
  (0 s, t, b : Type) -> (mst : s -> t) -> (mtb : t -> b) ->
  InterpPDF pdf s t mst -> InterpPDF pdf s b (mtb . mst)
InterpPDFrmap (PDF pos dom cod proj) s t b mst mtb (IPDF i msi mit comm) =
  IPDF i msi (mtb . mit)
    $ \fext => funExt $ \es => cong mtb $ fcong {x=es} (comm fext)

public export
InterpPDFdimap : (pdf : PolyDifunc) ->
  (0 s, t, a, b : Type) -> (mst : s -> t) -> (mas : a -> s) -> (mtb : t -> b) ->
  InterpPDF pdf s t mst -> InterpPDF pdf a b (mtb . mst . mas)
InterpPDFdimap pdf s t a b mst mas mtb =
  InterpPDFlmap pdf s b a (mtb . mst) mas . InterpPDFrmap pdf s t b mst mtb

--------------------------------------------------
---- Categories of elements of polydifunctors ----
--------------------------------------------------

public export
record PDFelemCatObj (pdf : PolyDifunc) where
  constructor PDFElObj
  pdfElPos : pdfPos pdf
  pdfElPred : SliceObj (pdfCobase pdf pdfElPos)
  pdfElStruct : Type
  pdfElAssign : pdfBase pdf pdfElPos -> pdfElStruct

public export
pdfElProj : {pdf : PolyDifunc} -> (el : PDFelemCatObj pdf) ->
  Sigma {a=(pdfCobase pdf $ pdfElPos el)} (pdfElPred el) -> pdfElStruct el
pdfElProj {pdf} el = pdfElAssign el . pdfProj pdf (pdfElPos el) . DPair.fst

public export
data PDFelemCatMor : {pdf : PolyDifunc} -> (dom, cod : PDFelemCatObj pdf) ->
    Type where
  PDFElMor : {0 pdf : PolyDifunc} ->
    {i : pdfPos pdf} ->
    {dpred, cpred : SliceObj $ pdfCobase pdf i} ->
    {dstruct, cstruct : Type} ->
    {dassign : pdfBase pdf i -> dstruct} ->
    (contra : SliceMorphism {a=(pdfCobase pdf i)} dpred cpred) ->
    (covar : dstruct -> cstruct) ->
    PDFelemCatMor {pdf}
      (PDFElObj i dpred dstruct dassign)
      (PDFElObj i cpred cstruct (covar . dassign))

----------------------------------
---- Monoid of polydifunctors ----
----------------------------------

-- Polydifunctors form a monoid -- a one-object category, with
-- the polydifunctors as morphisms -- whose identity is the hom-profunctor,
-- and whose composition resembles that of profunctors, but with the
-- additional morphism (since the objects are twisted arrows rather than
-- just objects of `op(Type) x Type`) to compose.

-- We represent the hom-profunctor, which is the identity of the monoid of
-- polydifunctors, with one position per morphism of `Type`.

public export
PdfHomProfId : PolyDifunc
PdfHomProfId =
  PDF
    (dom : Type ** cod : Type ** dom -> cod)
    (\i => fst i)
    (\i => fst $ snd i)
    (\i => snd $ snd i)

export
InterpToIdPDF : (x, y : Type) -> (m : x -> y) -> InterpPDF PdfHomProfId x y m
InterpToIdPDF x y m = IPDF (x ** y ** m) id id $ \fext => Refl

export
InterpFromIdPDF : (x, y : Type) -> (m : x -> y) ->
  InterpPDF PdfHomProfId x y m -> x -> y
InterpFromIdPDF x y mxy (IPDF (i ** j ** mij) mxi mjy comm) =
  -- There are two ways of getting from `x` to `y` -- `mxy` and
  -- `mjy . mij . mxi`. But `comm` shows them to be equal.
  -- We make that explicit here to make sure, and to document, that
  -- `mjy`, `mij`, and `mxi` are not "unused", but rather are an
  -- alternative to the `mxy` which we do use.
  let 0 eqm : (FunExtEq (mjy . mij . mxi) mxy) = comm in
  mxy

-- The arena form of polydifunctors is closed under composition.
public export
pdfComp : PolyDifunc -> PolyDifunc -> PolyDifunc
pdfComp (PDF qp qd qc qm) (PDF pp pd pc pm) =
  PDF
    (qi : qp ** pi : pp ** qc qi -> pd pi)
    (\(qi ** pi ** qcpd) => qd qi)
    (\(qi ** pi ** qcpd) => pc pi)
    (\(qi ** pi ** qcpd), qdi => pm pi $ qcpd $ qm qi qdi)

export
PDFcomposeInterpToInterpCompose :
  (q, p : PolyDifunc) -> (x, z : Type) -> (mxz : x -> z) ->
  TwArrCoprCompose (InterpPDF q) (InterpPDF p) x z mxz ->
  InterpPDF (pdfComp q p) x z mxz
PDFcomposeInterpToInterpCompose (PDF qp qd qc qm) (PDF pp pd pc pm) x z mxz
  (y **
   (mxy, myz) **
   (comm, IPDF qi mxqd mqcy qcomm, IPDF pi mypd mpcz pcomm)) =
    IPDF
      (qi ** pi ** mypd . mqcy)
      mxqd
      mpcz
      (\fext => funExt $ \ex =>
        trans
          (rewrite fcong {x=ex} (qcomm fext) in fcong {x=(mxy ex)} (pcomm fext))
          (fcong {x=ex} (comm fext)))

0 PDFinterpComposeToComposeInterp :
  (q, p : PolyDifunc) -> (x, z : Type) -> (mxz : x -> z) ->
  InterpPDF (pdfComp q p) x z mxz ->
  TwArrCoprCompose (InterpPDF q) (InterpPDF p) x z mxz
PDFinterpComposeToComposeInterp (PDF qp qd qc qm) (PDF pp pd pc pm) x z mxz
  (IPDF (qi ** pi ** mqcpd) mxqd mpcz comm) =
    (pd pi **
     (mqcpd . qm qi . mxqd, mpcz . pm pi) **
     (comm,
      IPDF qi mxqd mqcpd (\fext => Refl),
      IPDF pi Prelude.id mpcz (\fext => Refl)))

public export
PDiMonoidCat : IntCatSig
PDiMonoidCat =
  ICat
    Unit
  $ MICS
    (\_, _ => PolyDifunc)
  $ ICS
    (\_ => PdfHomProfId)
    (\_, _, _ => pdfComp)

-----------------------------------------------------------------------
---- Polydinatural transformations between metalanguage difunctors ----
-----------------------------------------------------------------------

-- A polydinatural transformation comprises an on-positions function from
-- the positions (collage objects) of the domain polydifunctor to those of
-- the codomain polydifunctor, and for each position, a twisted-arrow
-- morphism between the collage objects from the one at the output of the
-- on-positions function in the codomain polydifunctor to the one at the
-- input of the on-positions in the domain polydifunctor.
public export
record PolyDiNT (p, q : PolyDifunc) where
  constructor PDNT
  pdntOnPos : pdfPos p -> pdfPos q
  -- Per position, this is a twisted-arrow morphism from `q` to `p`.
  pdntOnBase :
    (i : pdfPos p) -> pdfBase q (pdntOnPos i) -> pdfBase p i
  pdntOnCobase :
    (i : pdfPos p) -> pdfCobase p i -> pdfCobase q (pdntOnPos i)
  pdntComm :
    (i : pdfPos p) ->
      FunExtEq
        (pdntOnBase i . pdfProj q (pdntOnPos i) . pdntOnCobase i)
        (pdfProj p i)

export
InterpPDNTnat : {0 p, q : PolyDifunc} -> PolyDiNT p q ->
  (x, y : Type) -> (m : x -> y) -> InterpPDF p x y m -> InterpPDF q x y m
InterpPDNTnat {p=(PDF pp pd pc pm)} {q=(PDF qp qd qc qm)}
  (PDNT oni onb onc ntcomm) x y m (IPDF pi mxpd mpcx pcomm) =
    IPDF
      (oni pi)
      (onc pi . mxpd)
      (mpcx . onb pi)
      (\fext => funExt $ \ex =>
        rewrite fcong {x=(mxpd ex)} $ ntcomm pi fext in
        fcong {x=ex} $ pcomm fext)

export
InterpPDNT : {0 p, q : PolyDifunc} -> PolyDiNT p q ->
  (x : Type) -> InterpPDFdiag p x -> InterpPDFdiag q x
InterpPDNT {p} {q} pdnt x = InterpPDNTnat {p} {q} pdnt x x Prelude.id

export
0 InterpPDFisPara : FunExt ->
  {0 p, q : PolyDifunc} -> (pdnt : PolyDiNT p q) ->
  (i0, i1 : Type) -> (i2 : i0 -> i1) ->
  (d0 : InterpPDFdiag p i0) -> (d1 : InterpPDFdiag p i1) ->
  (InterpPDFlmap p i1 i1 i0 Prelude.id i2 d1 ~=~
   InterpPDFrmap p i0 i0 i1 Prelude.id i2 d0) ->
  (InterpPDFlmap q i1 i1 i0 Prelude.id i2 (InterpPDNT {p} {q} pdnt i1 d1) ~=~
   InterpPDFrmap q i0 i0 i1 Prelude.id i2 (InterpPDNT {p} {q} pdnt i0 d0))
InterpPDFisPara fext {p=p@(PDF pp pd pc pm)} {q=q@(PDF qp qd qc qm)}
  pdnt@(PDNT onidx onb onc ntcomm) i0 i1 i2
  ip@(IPDF pi0 mi0pd mpci0 pcomm) iq@(IPDF pi1 mi1pd mpci1 qcomm) cond =
    case ipdfEqPos cond of
      Refl => case ipdfEqDom cond of
        Refl => case ipdfEqCod cond of
          Refl =>
            ipdfUip fext Refl Refl Refl

--------------------------------------------------------------------------------
---- Category of metalanguage difunctors with paranatural transformations ----
--------------------------------------------------------------------------------

export
pdNTid : (pdf : PolyDifunc) -> PolyDiNT pdf pdf
pdNTid pdf =
  PDNT id (\_ => id) (\i => id) $ \i, fext => Refl

export
pdNTvcomp : {0 r, q, p : PolyDifunc} -> PolyDiNT q r -> PolyDiNT p q ->
  PolyDiNT p r
pdNTvcomp {r=(PDF rp rd rc rm)} {q=(PDF qp qd qc qm)} {p=(PDF pp pd pc pm)}
  (PDNT oniqr onbqr oncqr qrcomm) (PDNT onipq onbpq oncpq pqcomm) =
    PDNT
      (oniqr . onipq)
      (\pi => onbpq pi . onbqr (onipq pi))
      (\pi => (oncqr $ onipq pi) . oncpq pi)
      $ \pi, fext => funExt $ \pd =>
        trans
          (rewrite (fcong {x=(oncpq pi pd)} $ qrcomm (onipq pi) fext) in Refl)
          (fcong {x=pd} $ pqcomm pi fext)

public export
PolyDiMICS : MorIdCompSig PolyDifunc
PolyDiMICS =
  MICS
    PolyDiNT
  $ ICS
    pdNTid
    (\p, q, r => pdNTvcomp {r} {q} {p})

public export
PolyDiCat : IntCatSig
PolyDiCat = ICat PolyDifunc PolyDiMICS

--------------------------------------------------------------------
---- Two-categorical structure of polydinatural transformations ----
--------------------------------------------------------------------

-- The polydinatural transformations of difunctors form a two-category:
-- polydinatural transformations have horizontal composition and whiskering.

export
pdNTwhiskerL : {0 q, r : PolyDifunc} -> PolyDiNT q r -> (p : PolyDifunc) ->
  PolyDiNT (pdfComp q p) (pdfComp r p)
pdNTwhiskerL {q=(PDF qp qd qc qm)} {r=(PDF rp rd rc rm)}
  (PDNT oni onb onc ntcomm) (PDF pp pd pc pm) =
    PDNT
      (\(qi ** pi ** qcpd) => (oni qi ** pi ** qcpd . onb qi))
      (\(qi ** pi ** qcpd) => id)
      (\(qi ** pi ** qcpd) => onc qi)
      (\(qi ** pi ** qcpd), fext =>
        funExt $ \qd => rewrite fcong {x=qd} (ntcomm qi fext) in Refl)

export
pdNTwhiskerR : {0 p, q : PolyDifunc} -> PolyDiNT p q -> (r : PolyDifunc) ->
  PolyDiNT (pdfComp r p) (pdfComp r q)
pdNTwhiskerR {p=(PDF pp pd pc pm)} {q=(PDF qp qd qc qm)}
  (PDNT oni onb onc ntcomm) (PDF rp rd rc rm) =
    PDNT
      (\(ri ** pi ** rcpd) => (ri ** oni pi ** onc pi . rcpd))
      (\(ri ** pi ** rcpd) => onb pi)
      (\(ri ** pi ** rcpd) => id)
      (\(ri ** pi ** rcpd), fext =>
        funExt $ \rd => fcong $ ntcomm pi fext)

export
pdNThcomp : {0 p, q' : PolyDifunc} -> {p', q : PolyDifunc} ->
  PolyDiNT q q' -> PolyDiNT p p' -> PolyDiNT (pdfComp q p) (pdfComp q' p')
pdNThcomp {p} {p'} {q} {q'} beta alpha =
  pdNTvcomp (pdNTwhiskerL {q} {r=q'} beta p') (pdNTwhiskerR {p} {q=p'} alpha q)

public export
PolyDiGHS : GlobalHomStruct PDiMonoidCat
PolyDiGHS () () = PolyDiMICS

public export
PolyDiLWS : GlobalLeftWhiskerHomStruct PDiMonoidCat PolyDiGHS
PolyDiLWS () () () f g g' alpha = pdNTwhiskerL {q=g} {r=g'} alpha f

public export
PolyDiRWS : GlobalRightWhiskerHomStruct PDiMonoidCat PolyDiGHS
PolyDiRWS () () () g f f' alpha = pdNTwhiskerR {p=f} {q=f'} alpha g

public export
PolyDi2CatS : Int2CatStruct PDiMonoidCat
PolyDi2CatS =
  I2CS
    PolyDiGHS
    PolyDiLWS
    PolyDiRWS

public export
PolyDi2Cat : Int2CatSig
PolyDi2Cat = I2Cat PDiMonoidCat PolyDi2CatS

---------------------------------------
---- Polynomial/Dirichlet functors ----
---------------------------------------

-- Twisted polynomials subsume both polynomial and Dirichlet functors.

export
PdfFromPoly : PolyFunc -> PolyDifunc
PdfFromPoly p = PDF (pfPos p) (\_ => Void) (pfDir {p}) (\i, v => void v)

export
PdfFromPolyNT : (p, q : PolyFunc) ->
  PolyNatTrans p q -> PolyDiNT (PdfFromPoly p) (PdfFromPoly q)
PdfFromPolyNT (ppos ** pdir) (qpos ** qdir) (onpos ** ondir) =
  PDNT
    onpos
    ondir
    (\_ => Prelude.id {a=Void})
    (\pi, fext => funExt $ \v => void v)

export
PdfToPolyNT : (p, q : PolyFunc) ->
  PolyDiNT (PdfFromPoly p) (PdfFromPoly q) -> PolyNatTrans p q
PdfToPolyNT (ppos ** pdir) (qpos ** qdir) (PDNT onpos onbase oncobase comm) =
  (onpos ** onbase)

export
InterpPdfFromPoly : (p : PolyFunc) -> (y : Type) ->
  InterpPolyFunc p y -> InterpPDF (PdfFromPoly p) Void y (\v => void v)
InterpPdfFromPoly (pos ** dir) y (i ** dm) =
  IPDF i (\v => void v) dm $ \fext => funExt $ \v => void v

export
InterpPdfToPoly : (p : PolyFunc) -> (y : Type) ->
  InterpPDF (PdfFromPoly p) Void y (\v => void v) -> InterpPolyFunc p y
InterpPdfToPoly (pos ** dir) y (IPDF i mx my comm) = (i ** my)

export
PdfFromDirich : PolyFunc -> PolyDifunc
PdfFromDirich p = PDF (pfPos p) (pfDir {p}) (\_ => Unit) (\_, _ => ())

export
PdfFromDirichNT : (p, q : MLDirichCatObj) ->
  DirichNatTrans p q -> PolyDiNT (PdfFromDirich p) (PdfFromDirich q)
PdfFromDirichNT (ppos ** pdir) (qpos ** qdir) (onpos ** ondir) =
  PDNT
    onpos
    (\_ => Prelude.id {a=Unit})
    ondir
    (\_, _ => Refl)

export
PdfToDirichNT : (p, q : MLDirichCatObj) ->
  PolyDiNT (PdfFromDirich p) (PdfFromDirich q) -> DirichNatTrans p q
PdfToDirichNT (ppos ** pdir) (qpos ** qdir) (PDNT onpos onbase oncobase comm) =
  (onpos ** oncobase)

export
InterpPdfFromDirich : (p : PolyFunc) -> (x : Type) ->
  InterpDirichFunc p x -> InterpPDF (PdfFromDirich p) x Unit (\_ => ())
InterpPdfFromDirich (pos ** dir) x (i ** dm) =
  IPDF i dm (\_ => ()) $ \fext => funExt $ \_ => Refl

export
InterpPdfToDirich : (p : PolyFunc) -> (x : Type) ->
  InterpPDF (PdfFromDirich p) x Unit (\_ => ()) -> InterpDirichFunc p x
InterpPdfToDirich (pos ** dir) x (IPDF i mx my comm) = (i ** mx)

----------------------------------------------
----------------------------------------------
---- Embedding of PolyDifunc into PolyFunc ---
----------------------------------------------
----------------------------------------------

public export
PDiToPoly : PolyDifunc -> PolyFunc
PDiToPoly (PDF pos cobase base proj) =
  (Sigma {a=pos} cobase ** base . DPair.fst)

public export
PDiToPolyNT : (p, q : PolyDifunc) ->
  PolyDiNT p q -> PolyNatTrans (PDiToPoly p) (PDiToPoly q)
PDiToPolyNT (PDF ppos pcobase pbase pproj) (PDF qpos qcobase qbase qproj)
  (PDNT onpos onbase oncobase ntcomm) =
    (dpBimap onpos oncobase ** \(pi ** pcb), qb => onbase pi qb)

---------------------------------------------
---------------------------------------------
---- Universal morphisms in `PolyDifunc` ----
---------------------------------------------
---------------------------------------------

------------------------
---- Initial object ----
------------------------

public export
PDIinitial : PolyDifunc
PDIinitial = PDF Void (\v => void v) (\v => void v) (\v => void v)

public export
pdiFromInitial : (p : PolyDifunc) -> PolyDiNT PDIinitial p
pdiFromInitial p =
  PDNT
    (\v => void v)
    (\v => void v)
    (\v => void v)
    (\v => void v)

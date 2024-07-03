module LanguageDef.MLDirichCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import LanguageDef.QType
import public LanguageDef.InternalCat
import public LanguageDef.IntEFamCat
import public LanguageDef.IntArena

----------------------------------------------
----------------------------------------------
---- Interpretation of Dirichlet functors ----
----------------------------------------------
----------------------------------------------

-- Interpret the same data as determine a polynomial functor --
-- namely, a dependent set, AKA arena -- as a Dirichlet functor
-- (rather than a polynomial functor).  While a polynomial
-- functor is a sum of covariant representables, a Dirichlet
-- functor is a sum of contravariant representables.
public export
InterpDirichFunc : MLDirichCatObj -> Type -> Type
InterpDirichFunc = InterpIDFobj TypeObj TypeMor

public export
dfPos : MLDirichCatObj -> Type
dfPos = ifeoIdx

public export
dfDir : (p : MLDirichCatObj) -> dfPos p -> Type
dfDir = ifeoObj

public export
InterpDFMap : (p : MLDirichCatObj) -> {0 a, b : Type} ->
  (a -> b) -> InterpDirichFunc p b -> InterpDirichFunc p a
InterpDFMap p m = dpMapSnd (\i => (|>) m)

public export
(p : MLDirichCatObj) => Contravariant (InterpDirichFunc p) where
  contramap {p} = InterpDFMap p

-------------------------------------------------------
-------------------------------------------------------
---- Natural transformations on Dirichlet functors ----
-------------------------------------------------------
-------------------------------------------------------

public export
DirichNatTrans : MLDirichCatObj -> MLDirichCatObj -> Type
DirichNatTrans = MLDirichCatMor

public export
dntOnPos : {0 p, q : MLDirichCatObj} -> DirichNatTrans p q ->
  dfPos p -> dfPos q
dntOnPos = DPair.fst

public export
dntOnDir : {0 p, q : MLDirichCatObj} -> (alpha : DirichNatTrans p q) ->
  (i : dfPos p) -> dfDir p i -> dfDir q (dntOnPos {p} {q} alpha i)
dntOnDir = DPair.snd

-- A natural transformation between Dirichlet functors may be viewed as a
-- morphism in the slice category of `Type` over `Type`.
public export
InterpDirichNT : {0 p, q : MLDirichCatObj} -> DirichNatTrans p q ->
  SliceMorphism {a=Type} (InterpDirichFunc p) (InterpDirichFunc q)
InterpDirichNT {p} {q} alpha a =
  dpBimap (dntOnPos alpha) (\i => (.) $ dntOnDir alpha i)

----------------------------------------------------------
---- Composition of Dirichlet natural transformations ----
----------------------------------------------------------

public export
dntId : (p : MLDirichCatObj) -> DirichNatTrans p p
dntId = ifemId TypeMor typeId

-- Vertical composition of natural transformations, which is the categorial
-- composition in the category of Dirichlet functors.
public export
dntVCatComp : {p, q, r : MLDirichCatObj} ->
  DirichNatTrans q r -> DirichNatTrans p q -> DirichNatTrans p r
dntVCatComp = ifemComp TypeMor typeComp

---------------------------------------------------------------------------
---- Vertical-Cartesian factoring of Dirichlet natural transformations ----
---------------------------------------------------------------------------

public export
arBaseChangePos : (p : MLArena) -> {a : Type} -> (a -> dfPos p) -> Type
arBaseChangePos p {a} f = a

public export
arBaseChangeDir : (p : MLArena) -> {a : Type} -> (f : a -> dfPos p) ->
  arBaseChangePos p {a} f -> Type
arBaseChangeDir p {a} f i = dfDir p $ f i

public export
arBaseChangeArena : (p : MLArena) -> {a : Type} -> (a -> dfPos p) -> MLArena
arBaseChangeArena p {a} f = (arBaseChangePos p {a} f ** arBaseChangeDir p {a} f)

-- The intermediate Dirichlet functor in the vertical-Cartesian
-- factoring of a natural transformation between Dirichlet functors.
public export
DirichVertCartFactFunc : {p, q : MLDirichCatObj} ->
  DirichNatTrans p q -> MLDirichCatObj
DirichVertCartFactFunc {p} {q} alpha =
  arBaseChangeArena q {a=(dfPos p)} (dntOnPos alpha)

public export
DirichVertCartFactPos : {p, q : MLDirichCatObj} -> DirichNatTrans p q -> Type
DirichVertCartFactPos {p} {q} alpha =
  dfPos (DirichVertCartFactFunc {p} {q} alpha)

public export
DirichVertCartFactDir : {p, q : MLDirichCatObj} ->
  (alpha : DirichNatTrans p q) -> DirichVertCartFactPos {p} {q} alpha -> Type
DirichVertCartFactDir {p} {q} alpha =
  dfDir (DirichVertCartFactFunc {p} {q} alpha)

public export
DirichVertFactOnPos : {0 p, q : MLDirichCatObj} ->
  (alpha : DirichNatTrans p q) ->
  dfPos p -> DirichVertCartFactPos {p} {q} alpha
DirichVertFactOnPos alpha = id

public export
DirichVertFactOnDir :
  {0 p, q : MLDirichCatObj} -> (alpha : DirichNatTrans p q) ->
  (i : dfPos p) -> dfDir p i ->
  DirichVertCartFactDir {p} {q} alpha (DirichVertFactOnPos {p} {q} alpha i)
DirichVertFactOnDir = dntOnDir

public export
DirichVertFactNatTrans : {0 p, q : MLDirichCatObj} ->
  (alpha : DirichNatTrans p q) ->
  DirichNatTrans p (DirichVertCartFactFunc {p} {q} alpha)
DirichVertFactNatTrans {p} {q} alpha =
  (DirichVertFactOnPos {p} {q} alpha ** DirichVertFactOnDir {p} {q} alpha)

public export
DirichCartFactOnPos : {0 p, q : MLDirichCatObj} ->
  (alpha : DirichNatTrans p q) ->
  DirichVertCartFactPos {p} {q} alpha -> dfPos q
DirichCartFactOnPos = dntOnPos

public export
DirichCartFactOnDir :
  {0 p, q : MLDirichCatObj} -> (alpha : DirichNatTrans p q) ->
  (i : DirichVertCartFactPos {p} {q} alpha) ->
  DirichVertCartFactDir {p} {q} alpha i ->
  dfDir q (DirichCartFactOnPos {p} {q} alpha i)
DirichCartFactOnDir alpha i = id

public export
DirichCartFactNatTrans : {0 p, q : MLDirichCatObj} ->
  (alpha : DirichNatTrans p q) ->
  DirichNatTrans (DirichVertCartFactFunc {p} {q} alpha) q
DirichCartFactNatTrans {p} {q} alpha =
  (DirichCartFactOnPos {p} {q} alpha ** DirichCartFactOnDir {p} {q} alpha)

public export
0 DirichVertCartFactIsCorrect : {0 p, q : MLDirichCatObj} ->
  (alpha : DirichNatTrans p q) ->
  (dntVCatComp {p} {q=(DirichVertCartFactFunc {p} {q} alpha)} {r=q}
    (DirichCartFactNatTrans {p} {q} alpha)
    (DirichVertFactNatTrans {p} {q} alpha))
  = alpha
DirichVertCartFactIsCorrect {p=(_ ** _)} {q=(_ ** _)} (_ ** _) = Refl

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
---- Universal morphisms in the category of Dirichlet functors on `Type` ----
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

----------------------------
---- (Parallel) product ----
----------------------------

public export
dfParProductPos : MLDirichCatObj -> MLDirichCatObj -> Type
dfParProductPos (ppos ** pdir) (qpos ** qdir) = Pair ppos qpos

public export
dfParProductDir : (p, q : MLDirichCatObj) -> dfParProductPos p q -> Type
dfParProductDir (ppos ** pdir) (qpos ** qdir) = uncurry Pair . bimap pdir qdir

public export
dfParProductArena : MLDirichCatObj -> MLDirichCatObj -> MLDirichCatObj
dfParProductArena p q = (dfParProductPos p q ** dfParProductDir p q)

public export
dirichParProj1OnPos : (p, q : MLDirichCatObj) ->
  dfPos (dfParProductArena p q) -> dfPos p
dirichParProj1OnPos (ppos ** pdir) (qpos ** qdir) (pi, qi) = pi

public export
dirichParProj1OnDir : (p, q : MLDirichCatObj) ->
  (i : dfPos (dfParProductArena p q)) ->
  dfDir (dfParProductArena p q) i ->
  dfDir p (dirichParProj1OnPos p q i)
dirichParProj1OnDir (ppos ** pdir) (qpos ** qdir) (pi, qi) (pd, qd) = pd

public export
dirichParProj1 : (p, q : MLDirichCatObj) ->
  DirichNatTrans (dfParProductArena p q) p
dirichParProj1 p@(ppos ** pdir) q@(qpos ** qdir) =
  (dirichParProj1OnPos p q ** dirichParProj1OnDir p q)

public export
dirichParProj2OnPos : (p, q : MLDirichCatObj) ->
  dfPos (dfParProductArena p q) -> dfPos q
dirichParProj2OnPos (ppos ** pdir) (qpos ** qdir) (pi, qi) = qi

public export
dirichParProj2OnDir : (p, q : MLDirichCatObj) ->
  (i : dfPos (dfParProductArena p q)) ->
  dfDir (dfParProductArena p q) i ->
  dfDir q (dirichParProj2OnPos p q i)
dirichParProj2OnDir (ppos ** pdir) (qpos ** qdir) (pi, qi) (pd, qd) = qd

public export
dirichParProj2 : (p, q : MLDirichCatObj) ->
  DirichNatTrans (dfParProductArena p q) q
dirichParProj2 p@(ppos ** pdir) q@(qpos ** qdir) =
  (dirichParProj2OnPos p q ** dirichParProj2OnDir p q)

public export
dirichParPairOnPos : (p, q, r : MLDirichCatObj) ->
  DirichNatTrans p q -> DirichNatTrans p r ->
  dfPos p ->
  dfPos (dfParProductArena q r)
dirichParPairOnPos (ppos ** pdir) (qpos ** qdir) (rpos ** rdir)
  (pqonpos ** pqondir) (pronpos ** prondir) pi =
    (pqonpos pi, pronpos pi)

public export
dirichParPairOnDir : (p, q, r : MLDirichCatObj) ->
  (f : DirichNatTrans p q) -> (g : DirichNatTrans p r) ->
  (pi : dfPos p) ->
  dfDir p pi ->
  dfDir (dfParProductArena q r) (dirichParPairOnPos p q r f g pi)
dirichParPairOnDir (ppos ** pdir) (qpos ** qdir) (rpos ** rdir)
  (pqonpos ** pqondir) (pronpos ** prondir) pi pd =
    (pqondir pi pd, prondir pi pd)

public export
dirichParPair : {p, q, r : MLDirichCatObj} ->
  DirichNatTrans p q -> DirichNatTrans p r ->
  DirichNatTrans p (dfParProductArena q r)
dirichParPair {p=p@(ppos ** pdir)} {q=q@(qpos ** qdir)} {r=r@(rpos ** rdir)}
  f g =
    (dirichParPairOnPos p q r f g ** dirichParPairOnDir p q r f g)

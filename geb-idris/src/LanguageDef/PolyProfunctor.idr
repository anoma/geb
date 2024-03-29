module LanguageDef.PolyProfunctor

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.PolyCat

%default total

--------------------------------------------------
--------------------------------------------------
---- Slices over signatures (symmetric pairs) ----
--------------------------------------------------
--------------------------------------------------

public export
SigSliceObj : Type -> Type
SigSliceObj a = a -> a -> Type

public export
SigSliceMorph : {a : Type} -> SigSliceObj a -> SigSliceObj a -> Type
SigSliceMorph {a} s s' = (x, y : a) -> s x y -> s' x y

public export
SigSliceFunctor : Type -> Type -> Type
SigSliceFunctor a b = SigSliceObj a -> SigSliceObj b

--------------------------------------------------------------
--------------------------------------------------------------
---- Polynomial functors in categories of dependent pairs ----
--------------------------------------------------------------
--------------------------------------------------------------

public export
DProdSlice : {a : Type} -> (b : a -> Type) -> Type
DProdSlice {a} b = SliceObj (Sigma {a} b)

public export
DProdSPF : {a : Type} -> (b : a -> Type) -> Type
DProdSPF {a} b = SlicePolyEndoFunc (Sigma {a} b)

------------------------------------------------------------------------
------------------------------------------------------------------------
---- Trying to work out polynomial profunctor definition by example ----
------------------------------------------------------------------------
------------------------------------------------------------------------

public export
data SubstObjMuPosPos : Type where
  SOMId : SubstObjMuPosPos
  SOMComp : SubstObjMuPosPos
  SOMFromInit : SubstObjMuPosPos
  SOMToTerminal : SubstObjMuPosPos
  SOMInjLeft : SubstObjMuPosPos
  SOMInjRight : SubstObjMuPosPos
  SOMCase : SubstObjMuPosPos
  SOMPair : SubstObjMuPosPos
  SOMProjLeft : SubstObjMuPosPos
  SOMProjRight : SubstObjMuPosPos
  SOMPDistrib : SubstObjMuPosPos

public export
data SubstObjMuPosDir : SubstObjMuPosPos -> Type where
  SOMPDIdObj : SubstObjMuPosDir SOMId
  SOMPDCompDom : SubstObjMuPosDir SOMComp
  SOMPDCompMid : SubstObjMuPosDir SOMComp
  SOMPDCompCod : SubstObjMuPosDir SOMComp
  SOMPDFromInitCod : SubstObjMuPosDir SOMFromInit
  SOMPDToTerminalDom : SubstObjMuPosDir SOMToTerminal
  SOMPDInjLeftDom : SubstObjMuPosDir SOMInjLeft
  SOMPDInjLeftCodR : SubstObjMuPosDir SOMInjLeft
  SOMPDInjRightDom : SubstObjMuPosDir SOMInjRight
  SOMPDInjRightCodL : SubstObjMuPosDir SOMInjRight
  SOMPDCaseDomL : SubstObjMuPosDir SOMCase
  SOMPDCaseDomR : SubstObjMuPosDir SOMCase
  SOMPDCaseCod : SubstObjMuPosDir SOMCase
  SOMPDPairDom : SubstObjMuPosDir SOMPair
  SOMPDPairCodL : SubstObjMuPosDir SOMPair
  SOMPDPairCodR : SubstObjMuPosDir SOMPair
  SOMPDProjLeftDomR : SubstObjMuPosDir SOMProjLeft
  SOMPDProjLeftCod : SubstObjMuPosDir SOMProjLeft
  SOMPDProjRightDomL : SubstObjMuPosDir SOMProjRight
  SOMPDProjRightCod : SubstObjMuPosDir SOMProjRight
  SOMPDDistribLeft : SubstObjMuPosDir SOMPDistrib
  SOMPDDistribMid : SubstObjMuPosDir SOMPDistrib
  SOMPDDistribRight : SubstObjMuPosDir SOMPDistrib

public export
SubstObjMuPosPF : PolyFunc
SubstObjMuPosPF = (SubstObjMuPosPos ** SubstObjMuPosDir)

public export
SubstObjMuAssignDomAlg : PFAlg SubstObjMuPosPF SubstObjMu
SubstObjMuAssignDomAlg SOMId d = d SOMPDIdObj
SubstObjMuAssignDomAlg SOMComp d = d SOMPDCompDom
SubstObjMuAssignDomAlg SOMFromInit d = Subst0
SubstObjMuAssignDomAlg SOMToTerminal d = d SOMPDToTerminalDom
SubstObjMuAssignDomAlg SOMInjLeft d = d SOMPDInjLeftDom
SubstObjMuAssignDomAlg SOMInjRight d = d SOMPDInjRightDom
SubstObjMuAssignDomAlg SOMCase d = d SOMPDCaseDomL !+ d SOMPDCaseDomR
SubstObjMuAssignDomAlg SOMPair d = d SOMPDPairDom
SubstObjMuAssignDomAlg SOMProjLeft d =
  d SOMPDProjLeftCod !* d SOMPDProjLeftDomR
SubstObjMuAssignDomAlg SOMProjRight d =
  d SOMPDProjRightDomL !* d SOMPDProjRightCod
SubstObjMuAssignDomAlg SOMPDistrib d =
   d SOMPDDistribLeft !* (d SOMPDDistribMid !+ d SOMPDDistribRight)

public export
SubstObjMuAssignCodAlg : PFAlg SubstObjMuPosPF SubstObjMu
SubstObjMuAssignCodAlg SOMId d = d SOMPDIdObj
SubstObjMuAssignCodAlg SOMComp d = d SOMPDCompCod
SubstObjMuAssignCodAlg SOMFromInit d = d SOMPDFromInitCod
SubstObjMuAssignCodAlg SOMToTerminal d = Subst1
SubstObjMuAssignCodAlg SOMInjLeft d = d SOMPDInjLeftDom !+ d SOMPDInjLeftCodR
SubstObjMuAssignCodAlg SOMInjRight d = d SOMPDInjRightCodL !+ d SOMPDInjRightDom
SubstObjMuAssignCodAlg SOMCase d = d SOMPDCaseCod
SubstObjMuAssignCodAlg SOMPair d = d SOMPDPairCodL !* d SOMPDPairCodR
SubstObjMuAssignCodAlg SOMProjLeft d = d SOMPDProjLeftCod
SubstObjMuAssignCodAlg SOMProjRight d = d SOMPDProjRightCod
SubstObjMuAssignCodAlg SOMPDistrib d =
   (d SOMPDDistribLeft !* d SOMPDDistribMid) !+
   (d SOMPDDistribLeft !* d SOMPDDistribRight)

public export
SubstObjMuAssignDom : Algebra (InterpPolyFunc SubstObjMuPosPF) SubstObjMu
SubstObjMuAssignDom = InterpPFAlg {p=SubstObjMuPosPF} SubstObjMuAssignDomAlg

public export
SubstObjMuAssignCod : Algebra (InterpPolyFunc SubstObjMuPosPF) SubstObjMu
SubstObjMuAssignCod = InterpPFAlg {p=SubstObjMuPosPF} SubstObjMuAssignCodAlg

public export
SubstObjMuAssignSig :
  InterpPolyFunc SubstObjMuPosPF SubstObjMu -> (SubstObjMu, SubstObjMu)
SubstObjMuAssignSig = MkPairF SubstObjMuAssignDom SubstObjMuAssignCod

public export
data SubstObjMuDir : SubstObjMuPosPos -> Type where
  SOMDCompDirAnt : SubstObjMuDir SOMComp
  SOMDCompDirPrec : SubstObjMuDir SOMComp
  SOMDCaseL : SubstObjMuDir SOMCase
  SOMDCaseR : SubstObjMuDir SOMCase
  SOMDPairL : SubstObjMuDir SOMPair
  SOMDPairR : SubstObjMuDir SOMPair

public export
SubstMorphShapeF : PolyFunc
SubstMorphShapeF = (SubstObjMuPosPos ** SubstObjMuDir)

public export
SubstMorphShape : Type
SubstMorphShape = PolyFuncMu SubstMorphShapeF

public export
SubstMorphAnnotatedDir : SliceObj SubstObjMuPosPos
SubstMorphAnnotatedDir = SliceProduct SubstObjMuDir SubstObjMuPosDir

public export
SubstMorphAnnotated : PolyFunc
SubstMorphAnnotated = (SubstObjMuPosPos ** SubstMorphAnnotatedDir)

public export
SubstMorphFromShape : (SubstObjMu, SubstObjMu) -> Type
SubstMorphFromShape = ?SubstMorphFromShape_hole

-----------------------------------------------------------------
-----------------------------------------------------------------
---- Polynomial functors from arbitrary categories to `Type` ----
-----------------------------------------------------------------
-----------------------------------------------------------------

-----------------------------------------------------------------
---- `Type`-object-dependent objects of arbitrary categories ----
-----------------------------------------------------------------

-- An object of an arbitrary category dependent on a type in `Type`.
-- This may be seen as the directions-map of an arena where the directions
-- may be drawn from an arbitrary category, not just `Type` (the positions
-- are drawn from `Type`).
public export
DirMap : CatSig -> Type -> Type
DirMap dom pos = pos -> catObj dom

public export
TypeArena : CatSig -> Type
TypeArena = DPair Type . DirMap

public export
taPos : {cat : CatSig} -> TypeArena cat -> Type
taPos = DPair.fst

public export
taDir : {cat : CatSig} -> (ar : TypeArena cat) -> taPos {cat} ar -> cat.catObj
taDir = DPair.snd

public export
TypeArenaId : (c : CatSig) -> c.catObj -> TypeArena c
TypeArenaId c cTerminal = (() ** \() => cTerminal)

-- Interpret a dependent object as a covariant polynomial functor.
public export
PolyMap : (cat : CatSig) -> {pos : Type} ->
  DirMap cat pos -> cat.catObj -> Type
PolyMap cat {pos} dir a = (i : pos ** cat.catMorph (dir i) a)

public export
PolyFMap : {cat : CatSig} -> {pos : Type} ->
  (dir : DirMap cat pos) -> {a, b : cat.catObj} ->
  cat.catMorph a b -> PolyMap cat dir a -> PolyMap cat dir b
PolyFMap {cat} {pos} dir {a} {b} f (i ** d) = (i ** cat.catComp f d)

-- Interpret a dependent object as a contravariant polynomial functor --
-- AKA a "Dirichlet functor".  (This means a functor from the opposite
-- category of `cat` to `Type`.)
public export
DirichMap : (cat : CatSig) -> {pos : Type} ->
  DirMap cat pos -> cat.catObj -> Type
DirichMap cat {pos} dir a = (i : pos ** cat.catMorph a (dir i))

public export
DirichFMap : {cat : CatSig} -> {pos : Type} ->
  (dir : DirMap cat pos) -> {a, b : cat.catObj} ->
  cat.catMorph b a -> DirichMap cat dir a -> DirichMap cat dir b
DirichFMap {cat} {pos} dir {a} {b} f (i ** d) = (i ** cat.catComp d f)

---------------------------------------------------------------------------
---- Natural transformations between `Type`-valued polynomial functors ----
---------------------------------------------------------------------------

public export
TAPolyNT : {cat : CatSig} -> (p, q : TypeArena cat) -> Type
TAPolyNT {cat} p q =
  (onPos : taPos p -> taPos q **
   Pi {a=(taPos p)} $ \i => cat.catMorph ((taDir q . onPos) i) ((taDir p) i))

public export
taPntOnPos : {cat : CatSig} -> {p, q : TypeArena cat} -> TAPolyNT {cat} p q ->
  taPos {cat} p -> taPos {cat} q
taPntOnPos = DPair.fst

public export
taPntOnDir : {cat : CatSig} -> {p, q : TypeArena cat} ->
  (alpha : TAPolyNT {cat} p q) ->
  (i : taPos {cat} p) ->
  cat.catMorph
    (taDir {cat} q (taPntOnPos {cat} {p} {q} alpha i))
    (taDir {cat} p i)
taPntOnDir = DPair.snd

public export
TADirichNT : {cat : CatSig} -> (p, q : TypeArena cat) -> Type
TADirichNT {cat} p q =
  (onPos : taPos p -> taPos q **
   Pi {a=(taPos p)} $ \i => cat.catMorph ((taDir p) i) ((taDir q . onPos) i))

public export
taDntOnPos : {cat : CatSig} -> {p, q : TypeArena cat} -> TADirichNT {cat} p q ->
  taPos {cat} p -> taPos {cat} q
taDntOnPos = DPair.fst

public export
taDntOnDir : {cat : CatSig} -> {p, q : TypeArena cat} ->
  (alpha : TADirichNT {cat} p q) ->
  (i : taPos {cat} p) ->
  cat.catMorph
    (taDir {cat} p i)
    (taDir {cat} q (taDntOnPos {cat} {p} {q} alpha i))
taDntOnDir = DPair.snd

public export
PolyNTApp : {cat : CatSig} -> {p, q : TypeArena cat} ->
   TAPolyNT {cat} p q -> (a : cat.catObj) ->
  PolyMap cat {pos=(taPos {cat} p)} (taDir {cat} p) a ->
  PolyMap cat {pos=(taPos {cat} q)} (taDir {cat} q) a
PolyNTApp {cat} {p} {q} alpha a (i ** d) =
  (taPntOnPos alpha i ** cat.catComp d (taPntOnDir alpha i))

public export
DirichNTApp : {cat : CatSig} -> {p, q : TypeArena cat} ->
  TADirichNT {cat} p q -> (a : cat.catObj) ->
  DirichMap cat {pos=(taPos {cat} p)} (taDir {cat} p) a ->
  DirichMap cat {pos=(taPos {cat} q)} (taDir {cat} q) a
DirichNTApp {cat} {p} {q} alpha a (i ** d) =
  (taDntOnPos alpha i ** cat.catComp (taDntOnDir alpha i) d)

----------------------------------------------------------------
---- Inferences of hom-sets from parameterized hom-functors ----
----------------------------------------------------------------

public export
ParamCovarToNT : {cat : CatSig} ->
  (p : cat.catObj -> TypeArena cat) -> (a, b : cat.catObj) -> Type
ParamCovarToNT {cat} p a b = TAPolyNT {cat} (p b) (p a)

public export
ParamContravarToNT : {cat : CatSig} ->
  (p : cat.catObj -> TypeArena cat) -> (a, b : cat.catObj) -> Type
ParamContravarToNT {cat} p a b = TADirichNT {cat} (p a) (p b)

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---- `Type`-valued polynomial profunctors between arbitrary categories ----
---------------------------------------------------------------------------
---------------------------------------------------------------------------

-----------------------------------------------------------------
---- Definition and interpretation of polynomial profunctors ----
-----------------------------------------------------------------

-- An arena representing a (polynomial) functor from the product category of
-- the opposite category of `dOp` with `c` to `Type`.
--
-- There are categories with in which the objects themselves are categories
-- and the profunctors are morphisms in both directions -- where the profunctors
-- are treated as morphisms from `c` to `dOp`, and where the profunctors are
-- treated as morphisms from `dOp` to `c`.  The latter is sometimes called a
-- "correspondence" (according to Wikipedia).
public export
DirMapPair : CatSig -> CatSig -> Type -> Type -> Type
DirMapPair dOp c contravarpos covarpos =
  (DirMap dOp contravarpos, DirMap c covarpos)

public export
dmpCovar : {dOp, c : CatSig} -> {contravarpos, covarpos : Type} ->
  DirMapPair dOp c contravarpos covarpos -> DirMap c covarpos
dmpCovar {dOp} {c} {contravarpos} {covarpos} = snd

public export
dmpContravar : {dOp, c : CatSig} -> {contravarpos, covarpos : Type} ->
  DirMapPair dOp c contravarpos covarpos -> DirMap dOp contravarpos
dmpContravar {dOp} {c} {contravarpos} {covarpos} = fst

public export
ProfArena : CatSig -> CatSig -> Type
ProfArena dOp c = (pos : (Type, Type) ** DirMapPair dOp c (fst pos) (snd pos))

public export
paPos : {dOp, c : CatSig} -> ProfArena dOp c -> (Type, Type)
paPos = DPair.fst

public export
paCovarPos : {dOp, c : CatSig} -> ProfArena dOp c -> Type
paCovarPos = snd . paPos

public export
paContravarPos : {dOp, c : CatSig} -> ProfArena dOp c -> Type
paContravarPos = fst . paPos

public export
paDir : {dOp, c : CatSig} ->
  (ar : ProfArena dOp c) ->
  DirMapPair dOp c (paContravarPos {dOp} {c} ar) (paCovarPos {dOp} {c} ar)
paDir = DPair.snd

public export
paCovarDir : {dOp, c : CatSig} -> (ar : ProfArena dOp c) ->
  paCovarPos {dOp} {c} ar -> c.catObj
paCovarDir ar = dmpCovar (paDir ar)

public export
paContravarDir : {dOp, c : CatSig} -> (ar : ProfArena dOp c) ->
  paContravarPos {dOp} {c} ar -> dOp.catObj
paContravarDir ar = dmpContravar (paDir ar)

-- Interpret a dependent object as a (polynomial) profunctor.
public export
ProfMap : (dOp, c : CatSig) -> {contravarpos : Type} -> {covarpos : Type} ->
  DirMapPair dOp c contravarpos covarpos -> dOp.catObj -> c.catObj -> Type
ProfMap dOp c {contravarpos} {covarpos} dir objdOp objc =
  ((i : contravarpos ** dOp.catMorph objdOp (dmpContravar dir i)),
   (j : covarpos ** c.catMorph (dmpCovar dir j) objc))

public export
ProfFDimap : {dOp, c : CatSig} -> {contravarpos : Type} -> {covarpos : Type} ->
  (dir : DirMapPair dOp c contravarpos covarpos) ->
  {da, db : dOp.catObj} -> {ca, cb : c.catObj} ->
  dOp.catMorph db da -> c.catMorph ca cb ->
  ProfMap dOp c dir da ca -> ProfMap dOp c dir db cb
ProfFDimap {dOp} {c} dir {da} {db} {ca} {cb} f g ((i ** ddir), (j ** cdir)) =
  ((i ** dOp.catComp ddir f), (j ** c.catComp g cdir))

{-
-------------------------------------------------------
---- Polynomial-profunctor natural transformations ----
-------------------------------------------------------

public export
ProfNT : {dOp, c : CatSig} -> (p, q : ProfArena dOp c) -> Type
ProfNT {dOp} {c} p q =
  (onPos : paPos p -> paPos q **
   Pi {a=(paPos p)} $ \i =>
    (dOp.catMorph (paContravarDir p i) (paContravarDir q (onPos i)),
     c.catMorph (paCovarDir q (onPos i)) (paCovarDir p i)))

public export
paOnPos : {dOp, c : CatSig} -> {p, q : ProfArena dOp c} ->
  ProfNT {dOp} {c} p q -> paPos {dOp} {c} p -> paPos {dOp} {c} q
paOnPos = DPair.fst

public export
paCovarOnDir : {dOp, c : CatSig} -> {p, q : ProfArena dOp c} ->
  (alpha : ProfNT {dOp} {c} p q) ->
  (i : paPos {dOp} {c} p) ->
  c.catMorph
    (paCovarDir {dOp} {c} q (paOnPos {dOp} {c} {p} {q} alpha i))
    (paCovarDir {dOp} {c} p i)
paCovarOnDir alpha i = snd (DPair.snd alpha i)

public export
paContravarOnDir : {dOp, c : CatSig} -> {p, q : ProfArena dOp c} ->
  (alpha : ProfNT {dOp} {c} p q) ->
  (i : paPos {dOp} {c} p) ->
  dOp.catMorph
    (paContravarDir {dOp} {c} p i)
    (paContravarDir {dOp} {c} q (paOnPos {dOp} {c} {p} {q} alpha i))
paContravarOnDir alpha i = fst (DPair.snd alpha i)

public export
ProfNTApp : {dOp, c : CatSig} -> {p, q : ProfArena dOp c} ->
  ProfNT {dOp} {c} p q -> (a : dOp.catObj) -> (b : c.catObj) ->
  ProfMap dOp c {pos=(paPos {dOp} {c} p)} (paDir {dOp} {c} p) a b ->
  ProfMap dOp c {pos=(paPos {dOp} {c} q)} (paDir {dOp} {c} q) a b
ProfNTApp {dOp} {c} {p} {q} alpha a b (i ** (ddir, cdir)) =
  (paOnPos alpha i **
   (dOp.catComp (paContravarOnDir alpha i) ddir,
    c.catComp cdir (paCovarOnDir alpha i)))

------------------------------
---- Derived hom-functors ----
------------------------------

-- If all the contravariant directions are terminal objects, then this is
-- effectively just a (covariant) polynomial functor from `c` to `Type`
-- (whose outputs are independent of `a`).
public export
ProfToCovar : {dOp, c : CatSig} -> (p : ProfArena dOp c) ->
  (a : dOp.catObj) -> TypeArena c
ProfToCovar {dOp} {c} p a =
  ((i : paPos p ** dOp.catMorph a (paContravarDir p i)) **
   \(i ** f) => paCovarDir p i)

-- Define a profunctor purely by covariant directions.
public export
CovarToProf : {dOp, c : CatSig} ->
  dOp.catObj -> TypeArena c -> ProfArena dOp c
CovarToProf {dOp} {c} dOpTerminal (cpos ** cdir) =
  (cpos ** (const dOpTerminal, cdir))

-- If all the covariant directions are initial objects, then this is
-- effectively just a Dirichlet (contravariant polynomial) functor from
-- `dOp` to `Type` (whose outputs are independent of `a`).
public export
ProfToContravar : {dOp, c : CatSig} -> (p : ProfArena dOp c) ->
  (a : c.catObj) -> TypeArena dOp
ProfToContravar {dOp} {c} p a =
  ((i : paPos p ** c.catMorph (paCovarDir p i) a) **
   \(i ** f) => paContravarDir p i)

-- Define a profunctor purely by contravariant directions.
public export
ContravarToProf : {dOp, c : CatSig} ->
  c.catObj -> TypeArena dOp -> ProfArena dOp c
ContravarToProf {dOp} {c} cInitial (dOpPos ** dOpDir) =
  (dOpPos ** (dOpDir, const cInitial))

-- Another special case is where there are both contravariant and covariant
-- directions, but they do not overlap -- that is, any one position either has
-- only contravariant or only covariant directions.
public export
IndependentDirsToProf : {dOp, c : CatSig} ->
  dOp.catObj -> c.catObj -> TypeArena dOp -> TypeArena c -> ProfArena dOp c
IndependentDirsToProf {dOp} {c}
  dOpTerminal cInitial (dOpPos ** dOpDir) (cpos ** cdir) =
    (Either dOpPos cpos **
     (eitherElim dOpDir (const dOpTerminal),
      eitherElim (const cInitial) cdir))

public export
EndoProfArena : CatSig -> Type
EndoProfArena cat = ProfArena cat cat

public export
ProfNTFromCovar : {cat : CatSig} ->
  (p : EndoProfArena cat) -> (a, b : cat.catObj) -> Type
ProfNTFromCovar {cat} p =
  ParamCovarToNT {cat} (ProfToCovar p)

public export
ProfNTFromContravar : {cat : CatSig} ->
  (p : EndoProfArena cat) -> (a, b : cat.catObj) -> Type
ProfNTFromContravar {cat} p =
  ParamContravarToNT {cat} (ProfToContravar p)

--------------------------------
---- Profunctor composition ----
--------------------------------

-- Here we take the view of a profunctor as a correspondence -- i.e., as a
-- morphism from `dOp` to `c`.

public export
ProfId : (c : CatSig) -> EndoProfArena c
ProfId c = (c.catObj ** (id, id))

public export
ProfCompose : {c, d, e : CatSig} ->
  ProfArena d c -> ProfArena e d -> ProfArena e c
ProfCompose {c} {d} {e} (dcPos ** (dOpDir, cDir)) (edPos ** (eOpDir, dDir)) =
  ((i : (edPos, dcPos) ** d.catMorph (dDir (fst i)) (dOpDir (snd i))) **
   (\((edi, dci) ** dm) => eOpDir edi,
    \((edi, dci) ** dm) => cDir dci))

-}

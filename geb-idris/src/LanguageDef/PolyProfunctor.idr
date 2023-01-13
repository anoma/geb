module LanguageDef.PolyProfunctor

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.PolyCat

%default total

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
  SOMDistrib : SubstObjMuPosPos

public export
data SubstObjMuPosDir : SubstObjMuPosPos -> Type where
  SOMDIdObj : SubstObjMuPosDir SOMId
  SOMDCompDom : SubstObjMuPosDir SOMComp
  SOMDCompMid : SubstObjMuPosDir SOMComp
  SOMDCompCod : SubstObjMuPosDir SOMComp
  SOMDFromInitDom : SubstObjMuPosDir SOMFromInit
  SOMDDistribLeft : SubstObjMuPosDir SOMDistrib
  SOMDDistribMid : SubstObjMuPosDir SOMDistrib
  SOMDDistribRight : SubstObjMuPosDir SOMDistrib

public export
SubstObjMuPosPF : PolyFunc
SubstObjMuPosPF = (SubstObjMuPosPos ** SubstObjMuPosDir)

public export
SubstObjMuAssignDom :
  InterpPolyFunc SubstObjMuPosPF SubstObjMu -> SubstObjMu
SubstObjMuAssignDom (SOMId ** d) = d SOMDIdObj
SubstObjMuAssignDom (SOMComp ** d) = d SOMDCompDom
SubstObjMuAssignDom (SOMFromInit ** d) = d SOMDFromInitDom
SubstObjMuAssignDom (SOMDistrib ** d) =
   d SOMDDistribLeft !* (d SOMDDistribMid !+ d SOMDDistribRight)

public export
SubstObjMuAssignCod :
  InterpPolyFunc SubstObjMuPosPF SubstObjMu -> SubstObjMu
SubstObjMuAssignCod (SOMId ** d) = d SOMDIdObj
SubstObjMuAssignCod (SOMComp ** d) = d SOMDCompCod
SubstObjMuAssignCod (SOMFromInit ** d) = Subst0
SubstObjMuAssignCod (SOMDistrib ** d) =
   (d SOMDDistribLeft !* d SOMDDistribMid) !+
   (d SOMDDistribLeft !* d SOMDDistribRight)

public export
SubstObjMuAssignSig :
  InterpPolyFunc SubstObjMuPosPF SubstObjMu -> (SubstObjMu, SubstObjMu)
SubstObjMuAssignSig = MkPairF SubstObjMuAssignDom SubstObjMuAssignCod

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
DirMapPair : CatSig -> CatSig -> Type -> Type
DirMapPair dOp c pos = (DirMap dOp pos, DirMap c pos)

public export
dmpCovar : {dOp, c : CatSig} -> {pos : Type} ->
  DirMapPair dOp c pos -> DirMap c pos
dmpCovar {dOp} {c} {pos} = snd

public export
dmpContravar : {dOp, c : CatSig} -> {pos : Type} ->
  DirMapPair dOp c pos -> DirMap dOp pos
dmpContravar {dOp} {c} {pos} = fst

public export
ProfArena : CatSig -> CatSig -> Type
ProfArena dOp c = DPair Type (DirMapPair dOp c)

public export
paPos : {dOp, c : CatSig} -> ProfArena dOp c -> Type
paPos = DPair.fst

public export
paDir : {dOp, c : CatSig} ->
  (ar : ProfArena dOp c) -> DirMapPair dOp c (paPos {dOp} {c} ar)
paDir = DPair.snd

public export
paCovarDir : {dOp, c : CatSig} -> (ar : ProfArena dOp c) ->
  paPos {dOp} {c} ar -> c.catObj
paCovarDir ar = dmpCovar (paDir ar)

public export
paContravarDir : {dOp, c : CatSig} -> (ar : ProfArena dOp c) ->
  paPos {dOp} {c} ar -> dOp.catObj
paContravarDir ar = dmpContravar (paDir ar)

-- Interpret a dependent object as a (polynomial) profunctor.
public export
ProfMap : (dOp, c : CatSig) -> {pos : Type} ->
  DirMapPair dOp c pos -> dOp.catObj -> c.catObj -> Type
ProfMap dOp c {pos} dir objdOp objc =
  (i : pos **
   (dOp.catMorph objdOp (dmpContravar dir i), c.catMorph (dmpCovar dir i) objc))

public export
ProfFDimap : {dOp, c : CatSig} -> {pos : Type} ->
  (dir : DirMapPair dOp c pos) ->
  {da, db : dOp.catObj} -> {ca, cb : c.catObj} ->
  dOp.catMorph db da -> c.catMorph ca cb ->
  ProfMap dOp c dir da ca -> ProfMap dOp c dir db cb
ProfFDimap {dOp} {c} {pos} dir {da} {db} {ca} {cb} f g (i ** (ddir, cdir)) =
  (i ** (dOp.catComp ddir f, c.catComp g cdir))

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

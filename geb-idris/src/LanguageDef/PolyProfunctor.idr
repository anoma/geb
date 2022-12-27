module LanguageDef.PolyProfunctor

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.PolyCat

%default total

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
   (i : taPos p) -> cat.catMorph (taDir q (onPos i)) (taDir p i))

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
   (i : taPos p) -> cat.catMorph (taDir p i) (taDir q (onPos i)))

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
HomSetFromParamCovarHom : {cat : CatSig} ->
  (p : cat.catObj -> TypeArena cat) -> (a, b : cat.catObj) -> Type
HomSetFromParamCovarHom {cat} p a b = TAPolyNT {cat} (p b) (p a)

public export
HomSetFromParamContravarHom : {cat : CatSig} ->
  (p : cat.catObj -> TypeArena cat) -> (a, b : cat.catObj) -> Type
HomSetFromParamContravarHom {cat} p a b = TADirichNT {cat} (p a) (p b)

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
public export
DirMapPair : CatSig -> CatSig -> Type -> Type
DirMapPair dOp c pos = (DirMap dOp pos, DirMap c pos)

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
  paPos {dOp} {c} ar -> dOp.catObj
paCovarDir ar = fst (DPair.snd ar)

public export
paContravarDir : {dOp, c : CatSig} -> (ar : ProfArena dOp c) ->
  paPos {dOp} {c} ar -> c.catObj
paContravarDir ar = snd (DPair.snd ar)

-- Interpret a dependent object as a (polynomial) profunctor.
public export
ProfMap : (dOp, c : CatSig) -> {pos : Type} ->
  DirMapPair dOp c pos -> dOp.catObj -> c.catObj -> Type
ProfMap dOp c {pos} dir objdOp objc =
  (i : pos **
   (dOp.catMorph (fst dir i) objdOp, c.catMorph objc (snd dir i)))

public export
ProfFDimap : {dOp, c : CatSig} -> {pos : Type} ->
  (dir : DirMapPair dOp c pos) ->
  {da, db : dOp.catObj} -> {ca, cb : c.catObj} ->
  dOp.catMorph da db -> c.catMorph cb ca ->
  ProfMap dOp c dir da ca -> ProfMap dOp c dir db cb
ProfFDimap {dOp} {c} {pos} dir {da} {db} {ca} {cb} f g (i ** (ddir, cdir)) =
  (i ** (dOp.catComp f ddir, c.catComp cdir g))

-------------------------------------------------------
---- Polynomial-profunctor natural transformations ----
-------------------------------------------------------

public export
ProfNT : {dOp, c : CatSig} -> (p, q : ProfArena dOp c) -> Type
ProfNT {dOp} {c} p q =
  (onPos : paPos p -> paPos q **
   (i : paPos p) ->
    (dOp.catMorph (paCovarDir q (onPos i)) (paCovarDir p i),
     c.catMorph (paContravarDir p i) (paContravarDir q (onPos i))))

public export
paOnPos : {dOp, c : CatSig} -> {p, q : ProfArena dOp c} ->
  ProfNT {dOp} {c} p q -> paPos {dOp} {c} p -> paPos {dOp} {c} q
paOnPos = DPair.fst

public export
paCovarOnDir : {dOp, c : CatSig} -> {p, q : ProfArena dOp c} ->
  (alpha : ProfNT {dOp} {c} p q) ->
  (i : paPos {dOp} {c} p) ->
  dOp.catMorph
    (paCovarDir {dOp} {c} q (paOnPos {dOp} {c} {p} {q} alpha i))
    (paCovarDir {dOp} {c} p i)
paCovarOnDir alpha i = fst (DPair.snd alpha i)

public export
paContravarOnDir : {dOp, c : CatSig} -> {p, q : ProfArena dOp c} ->
  (alpha : ProfNT {dOp} {c} p q) ->
  (i : paPos {dOp} {c} p) ->
  c.catMorph
    (paContravarDir {dOp} {c} p i)
    (paContravarDir {dOp} {c} q (paOnPos {dOp} {c} {p} {q} alpha i))
paContravarOnDir alpha i = snd (DPair.snd alpha i)

public export
ProfNTApp : {dOp, c : CatSig} -> {p, q : ProfArena dOp c} ->
  ProfNT {dOp} {c} p q -> (a : dOp.catObj) -> (b : c.catObj) ->
  ProfMap dOp c {pos=(paPos {dOp} {c} p)} (paDir {dOp} {c} p) a b ->
  ProfMap dOp c {pos=(paPos {dOp} {c} q)} (paDir {dOp} {c} q) a b
ProfNTApp {dOp} {c} {p} {q} alpha a b (i ** (ddir, cdir)) =
  (paOnPos alpha i **
   (dOp.catComp ddir (paCovarOnDir alpha i),
    c.catComp (paContravarOnDir alpha i) cdir))

------------------------------
---- Derived hom-functors ----
------------------------------

public export
ProfToCovarHom : {dOp, c : CatSig} -> (p : ProfArena dOp c) ->
  (a : c.catObj) -> TypeArena dOp
ProfToCovarHom {dOp} {c} p a =
  ((i : paPos p ** c.catMorph a (paContravarDir p i)) **
   \(i ** f) => paCovarDir p i)

public export
ProfToContravarHom : {dOp, c : CatSig} -> (p : ProfArena dOp c) ->
  (a : dOp.catObj) -> TypeArena c
ProfToContravarHom {dOp} {c} p a =
  ((i : paPos p ** dOp.catMorph (paCovarDir p i) a) **
   \(i ** f) => paContravarDir p i)

public export
ProfHomSetFromCovarHom : {cat : CatSig} ->
  (p : ProfArena cat cat) -> (a, b : cat.catObj) -> Type
ProfHomSetFromCovarHom {cat} p =
  HomSetFromParamCovarHom {cat} (ProfToCovarHom p)

public export
ProfHomSetFromContravarHom : {cat : CatSig} ->
  (p : ProfArena cat cat) -> (a, b : cat.catObj) -> Type
ProfHomSetFromContravarHom {cat} p =
  HomSetFromParamContravarHom {cat} (ProfToContravarHom p)

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

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---- `Type`-valued polynomial profunctors between arbitrary categories ----
---------------------------------------------------------------------------
---------------------------------------------------------------------------

-----------------------------------------------------------------
---- Definition and interpretation of polynomial profunctors ----
-----------------------------------------------------------------

-- An arena representing a (polynomial) functor from the product category of
-- the opposite category of `cod` with `dom` to `Type`, which is also viewed
-- as a profunctor from `dom` to `cod` (not the opposite category of `cod`).
public export
DirMapPair : CatSig -> CatSig -> Type -> Type
DirMapPair dom cod pos = (DirMap dom pos, DirMap cod pos)

public export
ProfArena : CatSig -> CatSig -> Type
ProfArena dom cod = DPair Type (DirMapPair dom cod)

public export
paPos : {dom, cod : CatSig} -> ProfArena dom cod -> Type
paPos = DPair.fst

public export
paDir : {dom, cod : CatSig} ->
  (ar : ProfArena dom cod) -> DirMapPair dom cod (paPos {dom} {cod} ar)
paDir = DPair.snd

public export
paCovarDir : {dom, cod : CatSig} -> (ar : ProfArena dom cod) ->
  paPos {dom} {cod} ar -> dom.catObj
paCovarDir ar = fst (DPair.snd ar)

public export
paContravarDir : {dom, cod : CatSig} -> (ar : ProfArena dom cod) ->
  paPos {dom} {cod} ar -> cod.catObj
paContravarDir ar = snd (DPair.snd ar)

-- Interpret a dependent object as a (polynomial) profunctor.
public export
ProfMap : (dom, cod : CatSig) -> {pos : Type} ->
  DirMapPair dom cod pos -> dom.catObj -> cod.catObj -> Type
ProfMap dom cod {pos} dir objdom objcod =
  (i : pos **
   (dom.catMorph (fst dir i) objdom, cod.catMorph objcod (snd dir i)))

public export
ProfFDimap : {dom, cod : CatSig} -> {pos : Type} ->
  (dir : DirMapPair dom cod pos) ->
  {da, db : dom.catObj} -> {ca, cb : cod.catObj} ->
  dom.catMorph da db -> cod.catMorph cb ca ->
  ProfMap dom cod dir da ca -> ProfMap dom cod dir db cb
ProfFDimap {dom} {cod} {pos} dir {da} {db} {ca} {cb} f g (i ** (ddir, cdir)) =
  (i ** (dom.catComp f ddir, cod.catComp cdir g))

-------------------------------------------------------
---- Polynomial-profunctor natural transformations ----
-------------------------------------------------------

public export
ProfNT : {dom, cod : CatSig} -> (p, q : ProfArena dom cod) -> Type
ProfNT {dom} {cod} p q =
  (onPos : paPos p -> paPos q **
   (i : paPos p) ->
    (dom.catMorph (paCovarDir q (onPos i)) (paCovarDir p i),
     cod.catMorph (paContravarDir p i) (paContravarDir q (onPos i))))

public export
paOnPos : {dom, cod : CatSig} -> {p, q : ProfArena dom cod} ->
  ProfNT {dom} {cod} p q -> paPos {dom} {cod} p -> paPos {dom} {cod} q
paOnPos = DPair.fst

public export
paCovarOnDir : {dom, cod : CatSig} -> {p, q : ProfArena dom cod} ->
  (alpha : ProfNT {dom} {cod} p q) ->
  (i : paPos {dom} {cod} p) ->
  dom.catMorph
    (paCovarDir {dom} {cod} q (paOnPos {dom} {cod} {p} {q} alpha i))
    (paCovarDir {dom} {cod} p i)
paCovarOnDir alpha i = fst (DPair.snd alpha i)

public export
paContravarOnDir : {dom, cod : CatSig} -> {p, q : ProfArena dom cod} ->
  (alpha : ProfNT {dom} {cod} p q) ->
  (i : paPos {dom} {cod} p) ->
  cod.catMorph
    (paContravarDir {dom} {cod} p i)
    (paContravarDir {dom} {cod} q (paOnPos {dom} {cod} {p} {q} alpha i))
paContravarOnDir alpha i = snd (DPair.snd alpha i)

public export
ProfNTApp : {dom, cod : CatSig} -> {p, q : ProfArena dom cod} ->
  ProfNT {dom} {cod} p q -> (a : dom.catObj) -> (b : cod.catObj) ->
  ProfMap dom cod {pos=(paPos {dom} {cod} p)} (paDir {dom} {cod} p) a b ->
  ProfMap dom cod {pos=(paPos {dom} {cod} q)} (paDir {dom} {cod} q) a b
ProfNTApp {dom} {cod} {p} {q} alpha a b (i ** (ddir, cdir)) =
  (paOnPos alpha i **
   (dom.catComp ddir (paCovarOnDir alpha i),
    cod.catComp (paContravarOnDir alpha i) cdir))

------------------------------
---- Derived hom-functors ----
------------------------------

public export
ProfToCovarHom : {dom, cod : CatSig} -> (p : ProfArena dom cod) ->
  (a : cod.catObj) -> TypeArena dom
ProfToCovarHom {dom} {cod} p a =
  ((i : paPos p ** cod.catMorph a (paContravarDir p i)) **
   \(i ** f) => paCovarDir p i)

public export
ProfToContravarHom : {dom, cod : CatSig} -> (p : ProfArena dom cod) ->
  (a : dom.catObj) -> TypeArena cod
ProfToContravarHom {dom} {cod} p a =
  ((i : paPos p ** dom.catMorph (paCovarDir p i) a) **
   \(i ** f) => paContravarDir p i)

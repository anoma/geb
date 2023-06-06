module LanguageDef.Figures

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.RefinedADT
import public LanguageDef.PolyCat

%default total

------------------------------------------------------------
------------------------------------------------------------
---- Presheaf/figure-style diagram/category definitions ----
------------------------------------------------------------
------------------------------------------------------------

------------------
---- Diagrams ----
------------------

-- The vertices of the diagram, which, when interpreted as an index
-- category for presheaves or copreasheaves (depending on the directions
-- of the edges), defines the category of diagrams.
public export
data DiagDiagVert : Type where
  DDVvert : DiagDiagVert
  DDVedge : DiagDiagVert

-- The edges of the diagram which, when interpreted as an index category
-- for (co)presheaves, defines the category of diagrams.
public export
data DiagDiagEdge : Type where
  DDEsrc : DiagDiagEdge
  DDEtgt : DiagDiagEdge

-- The sources of the edges of the diagram which, when interpreted as an
-- index category for copresheaves, defines the category of diagrams.
public export
CoprshfDiagSrc : DiagDiagEdge -> DiagDiagVert
CoprshfDiagSrc = const DDVedge

public export
CDSbc : CSliceObj DiagDiagVert -> CSliceObj DiagDiagEdge
CDSbc = CSBaseChange CoprshfDiagSrc

-- The targets of the edges of the diagram which, when interpreted as an
-- index category for copresheaves, defines the category of diagrams.
public export
CoprshfDiagTgt : DiagDiagEdge -> DiagDiagVert
CoprshfDiagTgt = const DDVvert

public export
CDTbc : CSliceObj DiagDiagVert -> CSliceObj DiagDiagEdge
CDTbc = CSBaseChange CoprshfDiagTgt

-- The sources of the edges of the diagram which, when interpreted as an
-- index category for presheaves, defines the category of diagrams.
-- (Such an index category is sometimes called a "generic figure").
public export
PrshfDiagSrc : DiagDiagEdge -> DiagDiagVert
PrshfDiagSrc = CoprshfDiagTgt

public export
PDSbc : CSliceObj DiagDiagVert -> CSliceObj DiagDiagEdge
PDSbc = CSBaseChange PrshfDiagSrc

-- The targets of the edges of the diagram which, when interpreted as an
-- index category for presheaves, defines the category of diagrams.
public export
PrshfDiagTgt : DiagDiagEdge -> DiagDiagVert
PrshfDiagTgt = CoprshfDiagSrc

public export
PDTbc : CSliceObj DiagDiagVert -> CSliceObj DiagDiagEdge
PDTbc = CSBaseChange PrshfDiagTgt

------------------------
---- (Co)presheaves ----
------------------------

-- The objects of the category of diagrams, when that category is defined
-- as the copresheaf category on the diagram (interpreted as an index
-- category) of diagrams themselves (DiagDiagVert/DiagDiagEdge).
--
-- A copresheaf is a (covariant) functor, so the _objects_ are
-- (covariant) functors from the `DiagDiag` index category to `Type`.
public export
record DiagCoprshfObj where
  constructor DCObj
  -- If we wrote it in dependent-type-with-universes style rather than
  -- category-theoretic style, DCObj would have type `DiagDiagVert -> Type` --
  -- although there are only two objects, so this is also equivalent to
  -- simply two `Type`s.
  DCObj : CSliceObj DiagDiagVert

  -- If we wrote it in dependent-type-with-universes style rather than
  -- category-theoretic style, DCMorph would look something like this:
  --  DCMorph : (e : DiagDiagEdge) ->
  --    DCObj (coprshfDiagSrc e) -> DCObj (coprshfDiagTgt e)
  -- (There are only two edges, so this is equivalent to simply two functions,
  -- both from the `Type` to which we map `DDVedge` to the type to which
  -- we map `DDVvert`, representing the source and target maps.)
  DCMorph : CSliceMorphism {c=DiagDiagEdge} (CDSbc DCObj) (CDTbc DCObj)

-- The objects of the category of diagrams, when that category is defined
-- as the presheaf category on the diagram (interpreted as an index
-- category) of diagrams themselves (DiagDiagVert/DiagDiagEdge).
--
-- A presheaf is a (contravariant) functor, so the _objects_ are
-- (contravariant) functors from the `DiagDiag` index category to `Type`.
public export
record DiagPrshfObj where
  constructor DPObj
  -- If we wrote it in dependent-type-with-universes style rather than
  -- category-theoretic style, DPObj would have type `DiagDiagVert -> Type`.
  -- That's the same type as `DCObj`, but when we interpret diagrams as
  -- presheaves rather than copresheaves, we interpret the edge type
  -- differently; see `DPMorph`.
  DPObj : CSliceObj DiagDiagVert

  -- This is `DPMorph`'s signature backwards, reflecting that we are
  -- now interpreting the diagram as a "generic figure", meaning as a
  -- presheaf (contravariant functor), rather than the usual interpretation
  -- of "diagram" as "(covariant) functor", AKA copresheaf.
  --
  -- That's the same signature as `DPMorph`, but when we interpret diagrams
  -- as presheaves rather than copresheaves, we interpret the source and
  -- target mappings differently (as we must, since they point in opposite
  -- directions).  In this interpretation, rather than mapping each edge
  -- to its source or target respectively, the source mapping maps each
  -- vertex to the set of edges with that vertex as source, and the target
  -- mapping maps each vertex to the set of edges with that vertex as target.
  --
  -- This also means that, while we interpret the vertex type the same way
  -- in both the copresheaf and presheaf interpretations, we interpret the
  -- edge type differently.  In the copresheaf interpretation, it was just
  -- the type of edges.  In the presheaf interpretation, however, because the
  -- source and target mappings produce _sets_ of edges, the edge type in
  -- the presheaf interpretation must be a collection of subobjects of some
  -- type of edges.
  DPMorph : CSliceMorphism {c=DiagDiagEdge} (PDSbc DPObj) (PDTbc DPObj)

---------------------
---------------------
---- Prafunctors ----
---------------------
---------------------

public export
IndexCat : Type
IndexCat = DiagCoprshfObj

-- A copresheaf on `j`, a category (which in this formulation is defined via a
-- diagram in `Type`), is a covariant functor from `j` to `Type`.  As such it
-- is a choice of a type for each vertex and a function for each edge (with
-- domain and codomain matching source and target, respectively).
--
-- (The copresheaves on a given index category `j` themselves form the objects
-- of a functor category, whose morphisms are natural transformations).
public export
record Copresheaf (j : IndexCat) where
  constructor CoPrshf

---------------------------------
---------------------------------
---- Computational substrate ----
---------------------------------
---------------------------------

public export
data CompCatObj : Type where
  CC1 : CompCatObj
  CCB : CompCatObj
  CCP : CompCatObj -> CompCatObj -> CompCatObj

public export
data CompCatMorph : CompCatObj -> CompCatObj -> Type where
  CCid : (a : CompCatObj) -> CompCatMorph a a
  CCconst : (a : CompCatObj) -> {0 b : CompCatObj} ->
    CompCatMorph CC1 b -> CompCatMorph a b
  CCif : {0 a, b : CompCatObj} ->
    CompCatMorph a CCB -> CompCatMorph a b -> CompCatMorph a b ->
    CompCatMorph a b
  CCt : CompCatMorph CC1 CCB
  CCf : CompCatMorph CC1 CCB
  CCp : {0 a, b, c : CompCatObj} ->
    CompCatMorph a b -> CompCatMorph a c -> CompCatMorph a (CCP b c)
  CCp1 : {a, b, c : CompCatObj} ->
    CompCatMorph a (CCP b c) -> CompCatMorph a b
  CCp2 : {a, b, c : CompCatObj} ->
    CompCatMorph a (CCP b c) -> CompCatMorph a c

public export
ccComp : {a, b, c : CompCatObj} ->
  CompCatMorph b c -> CompCatMorph a b -> CompCatMorph a c
ccComp {a} {b} {c=b} (CCid b) f = f
ccComp {a} {b=a} {c=b} g (CCid a) = g
ccComp {a} {b} {c} g (CCconst a {b} f) = CCconst a {b=c} $ ccComp g f
ccComp {a} {b} {c} (CCconst b {b=c} g) f = CCconst a {b=c} g
ccComp {a} {b} {c} (CCif {a=b} {b=c} cond g g') f =
  CCif {a} {b=c} (ccComp cond f) (ccComp g f) (ccComp g' f)
ccComp {a} {b} {c} g (CCif {a} {b} cond f f') =
  CCif {a} {b=c} cond (ccComp g f) (ccComp g f')
ccComp {a} {b=CC1} {c=CCB} CCt f = CCconst a {b=CCB} CCt
ccComp {a} {b=CC1} {c=CCB} CCf f = CCconst a {b=CCB} CCf
ccComp {a=CC1} {b=CCB} {c=c} (CCif {a=CCB} {b=c} cond f g) CCt = ccComp f CCt
ccComp {a=CC1} {b=CCB} {c=c} (CCif {a=CCB} {b=c} cond f g) CCf = ccComp f CCf
ccComp {a=CC1} {b=CCB} {c=(CCP b c)} (CCp f g) CCt =
  CCp {a=CC1} {b} {c} (ccComp f CCt) (ccComp g CCt)
ccComp {a=CC1} {b=CCB} {c=(CCP b c)} (CCp f g) CCf =
  CCp {a=CC1} {b} {c} (ccComp f CCf) (ccComp g CCf)
ccComp {a=CC1} {b=CCB} {c=c} (CCp1 {a=CCB} {b=c} {c=d} f) CCt =
  CCp1 {a=CC1} {b=c} {c=d} $ ccComp {a=CC1} {b=CCB} {c=(CCP c d)} f CCt
ccComp {a=CC1} {b=CCB} {c=c} (CCp1 {a=CCB} {b=c} {c=d} f) CCf =
  CCp1 {a=CC1} {b=c} {c=d} $ ccComp {a=CC1} {b=CCB} {c=(CCP c d)} f CCf
ccComp {a=CC1} {b=CCB} {c} (CCp2 {a=CCB} {b} {c} f) CCt =
  CCp2 {a=CC1} {b} {c} $ ccComp {a=CC1} {b=CCB} {c=(CCP b c)} f CCt
ccComp {a=CC1} {b=CCB} {c} (CCp2 {a=CCB} {b} {c} f) CCf =
  CCp2 {a=CC1} {b} {c} $ ccComp {a=CC1} {b=CCB} {c=(CCP b c)} f CCf
ccComp {a} {b} {c} g f = ?ccComp_hole

---------------------------------
---------------------------------
---- Minimal topos interface ----
---------------------------------
---------------------------------

{-
mutual
  public export
  data MinToposCat : Type where
    MTCb : MinToposCat
    MTCs : (cat : MinToposCat) -> MinToposObj cat -> MinToposCat

  public export
  data MinToposObj : MinToposCat -> Type where
    MT1 : (cat : MinToposCat) -> MinToposObj cat
    MTB : (cat : MinToposCat) -> MinToposObj cat
    MTP : {0 cat : MinToposCat} -> {0 x, y, z : MinToposObj cat} ->
      MinToposMorph {cat} x z -> MinToposMorph {cat} y z -> MinToposObj cat
    MTS : {0 cat : MinToposCat} -> {0 x : MinToposObj cat} ->
      MinToposMorph {cat} x z -> MinToposMorph {cat} y z -> MinToposObj cat
    MTT : {0 cat : MinToposCat} -> MinToposObj cat -> MinToposObj cat

  public export
  data MinToposMorph : {0 cat : MinToposCat} ->
      MinToposObj cat -> MinToposObj cat -> Type where
  public export
  data MinToposObj : Type where
    MTP : MinToposObj -> MinToposObj -> MinToposObj
    MTE : {0 a, b : MinToposObj} ->
      MinToposMorph a b -> MinToposMorph a b -> MinToposObj
    MTT : MinToposObj -> MinToposObj

  public export
  data MinToposMorph : MinToposObj -> MinToposObj -> Type where
    MTid : (a : MinToposObj) -> MinToposMorph a a
    MTcomp : {0 a, b, c : MinToposObj} ->
      MinToposMorph b c -> MinToposMorph a b -> MinToposMorph a c
    MTterm : (a : MinToposObj) -> MinToposMorph a MT1
    Mtif : {0 a : MinToposObj} ->
      MinToposMorph MT1 a -> MinToposMorph MT1 a -> MinToposMorph MTB a
    Mtbt : {0 a : MinToposObj} -> MinToposMorph MTB a -> MinToposMorph MT1 a
    Mtbf : {0 a : MinToposObj} -> MinToposMorph MTB a -> MinToposMorph MT1 a

  public export
  data MinToposEq : {0 a, b : MinToposObj} ->
      MinToposMorph a b -> MinToposMorph a b -> Type where

mutual
  public export
  interpMinToposObj : MinToposObj -> Type
  interpMinToposObj x = ?interpMinToposObj_hole

  public export
  interpMinToposMorph : {0 a, b : MinToposObj} ->
    MinToposMorph a b -> interpMinToposObj a -> interpMinToposObj b
  interpMinToposMorph f = ?interpMinToposMorph_hole

  public export
  interpMinToposEq : {0 a, b : MinToposObj} -> {0 f, g : MinToposMorph a b} ->
    MinToposEq {a} {b} f g ->
    ExtEq (interpMinToposMorph {a} {b} f) (interpMinToposMorph {a} {b} g)
  interpMinToposEq {a} {b} {f} {g} eq = ?interpMinToposEq_hole
    -}

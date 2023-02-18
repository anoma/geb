module LanguageDef.DiagramCat

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.ProgFinSet
import public LanguageDef.PolyCat
import public LanguageDef.Syntax

%default total

----------------------------------------
----------------------------------------
---- Category-signature definitions ----
----------------------------------------
----------------------------------------

public export
SignatureT : Type -> Type
SignatureT = ProductMonad

public export
HomSlice : Type -> Type
HomSlice = SliceObj . SignatureT

public export
SigRelObj : {obj : Type} -> SliceObj (HomSlice obj)
SigRelObj {obj} hom = DepRelObj {a=(SignatureT obj)} (hom, hom)

public export
SigRelT : {obj : Type} -> SliceObj (HomSlice obj)
SigRelT {obj} hom = DepRelOn {a=(SignatureT obj)} (hom, hom)

public export
HomEndofunctor : Type -> Type
HomEndofunctor = SliceEndofunctor . SignatureT

public export
InternalCopresheaf : Type -> Type
InternalCopresheaf = SliceObj

public export
InternalCopresheafNT : {obj : Type} -> SliceObj obj -> SliceObj obj -> Type
InternalCopresheafNT {obj} = SliceMorphism {a=obj}

public export
CopresheafNTExtEq : {obj : Type} -> {f, g : InternalCopresheaf obj} ->
  (alpha, beta : InternalCopresheafNT f g) -> Type
CopresheafNTExtEq {obj} {f} {g} = SliceExtEq {a=obj} {s=f} {s'=g}

public export
InternalCovarHom : HomSlice obj -> obj -> SliceObj obj
InternalCovarHom hom = hom .* MkPair

public export
InternalContravarHom : HomSlice obj -> obj -> SliceObj obj
InternalContravarHom = flip . InternalCovarHom

public export
HomUncurry : (obj -> obj -> Type) -> HomSlice obj
HomUncurry hom (x, y) = hom x y

public export
InternalNTFromCovarHom : {obj : Type} ->
  (hom : HomSlice obj) -> obj -> SliceObj obj -> Type
InternalNTFromCovarHom {obj} hom =
  SliceMorphism {a=obj} . InternalCovarHom hom

public export
InternalNTFromContravarHom : {obj : Type} ->
  (hom : HomSlice obj) -> obj -> SliceObj obj -> Type
InternalNTFromContravarHom {obj} hom =
  SliceMorphism {a=obj} . InternalContravarHom hom

---------------------------------------------------------------
---------------------------------------------------------------
---- Standard (Mac Lane / Eilenberg) internal categories ----
---------------------------------------------------------------
---------------------------------------------------------------

public export
record SCat where
  constructor SC
  scObj : Type
  scHom : HomSlice scObj
  scId : (a : scObj) -> scHom (a, a)
  scComp : {a, b, c : scObj} -> scHom (b, c) -> scHom (a, b) -> scHom (a, c)
  scEq : (sig : SignatureT scObj) -> EqRel (scHom sig)
  0 scIdL : {0 a, b : scObj} -> (f : scHom (a, b)) ->
    (scEq (a, b)).eqRel f (scComp {a} {b} {c=b} (scId b) f)
  0 scIdR : {0 a, b : scObj} -> (f : scHom (a, b)) ->
    (scEq (a, b)).eqRel f (scComp {a} {b=a} {c=b} f (scId a))
  0 scIdAssoc : {0 a, b, c, d : scObj} ->
    (f : scHom (a, b)) -> (g : scHom (b, c)) -> (h : scHom (c, d)) ->
    (scEq (a, d)).eqRel
      (scComp {a} {b=c} {c=d} h (scComp {a} {b} {c} g f))
      (scComp {a} {b} {c=d} (scComp {a=b} {b=c} {c=d} h g) f)

----------------------------------------
---- Standard-category Yoneda lemma ----
----------------------------------------

public export
SCCovarHomYonedaR :
  (sc : SCat) -> (a : sc.scObj) -> (f : SliceObj sc.scObj) ->
  InternalNTFromCovarHom {obj=sc.scObj} sc.scHom a f -> f a
SCCovarHomYonedaR sc a f alpha = alpha a $ sc.scId a

public export
SCCovarHomYonedaL : (sc : SCat) -> (a : sc.scObj) -> (f : SliceObj sc.scObj) ->
  (fmap : (a, b : sc.scObj) -> sc.scHom (a, b) -> f a -> f b) ->
  f a -> InternalNTFromCovarHom {obj=sc.scObj} sc.scHom a f
SCCovarHomYonedaL sc a f fmap fa b mab = fmap a b mab fa

public export
SCContravarHomYonedaR :
  (sc : SCat) -> (a : sc.scObj) -> (f : SliceObj sc.scObj) ->
  InternalNTFromContravarHom {obj=sc.scObj} sc.scHom a f -> f a
SCContravarHomYonedaR sc a f alpha = alpha a $ sc.scId a

public export
SCContravarHomYonedaL :
  (sc : SCat) -> (a : sc.scObj) -> (f : SliceObj sc.scObj) ->
  -- f is contravariant
  (fmap : (a, b : sc.scObj) -> sc.scHom (a, b) -> f b -> f a) ->
  f a -> InternalNTFromContravarHom {obj=sc.scObj} sc.scHom a f
SCContravarHomYonedaL sc a f fmap fa b mba = fmap b a mba fa

-------------------------
-------------------------
---- Free categories ----
-------------------------
-------------------------

-- The (free-forgetful) adjunction which can be used to define a category
-- has the following data:
--
--  - Left category C: two-category of categories
--  - Right category D: category of diagrams
--  - Left functor L: free functor which adds identities (loop edges) for
--    each vertex and paths to represent compositions, and equalities for
--    left identity, right identity, and associativity
--  - Right functor R: forgetful functor which drops identity, composition,
--    and equalities, leaving just vertices and edges
--  - R . L (D -> D): Functor which closes a diagram with loops labeled
--    as identities and paths labeled as compositions
--  - L . R (C -> C): Identity functor
--  - Unit (id -> R . L): injection of diagram into its closure
--  - Counit (L . R -> id): identity natural transformation
--  - Adjuncts: (Hom(L A, B) == Hom(A, R B), for A : D and B : C):
--    functors from a free category generated from a diagram A to an arbitrary
--    category B are in bijection with graph homomorphisms from A to the
--    diagram underlying B (i.e. the diagram whose vertices are objects of B
--    and whose edges are morphisms of B)
--  - Left triangle identity: (counit . L) . (L . unit) = id(L):
--    expanded, for all A : D, counit(L(A)) . L(unit(A)) = id(L(A))
--    (which goes from L(A) to L(A) in C via L(R(L(A)))):
--      id(L(A)) . L(inj(A)) = id(L(A))
--    -- this reflects preservation of identities by functors
--  - Right triangle identity: (R . counit) . (unit . R) = id(R):
--    expanded, for all B : C, R(counit(B)) . unit(R(B)) = id(R(B))
--    (which goes from R(B) to R(B) in D via R(L(R(B)))):
--      id(forget(B)) . inj(forget(B)) = id(forget(B))
--    -- this reflects the definition of the injection

public export
data CatHomF : {0 obj : Type} -> HomEndofunctor obj where
  CHId :
    {0 obj : Type} -> {0 hom : HomSlice obj} ->
    (x : obj) -> CatHomF {obj} hom (x, x)
  CHComp :
    {0 obj : Type} -> {0 hom : HomSlice obj} -> {x, y, z : obj} ->
    hom (y, z) -> hom (x, y) -> CatHomF {obj} hom (x, z)

public export
HomTranslateF : (obj : Type) -> HomSlice obj -> HomEndofunctor obj
HomTranslateF obj = SliceTranslateF {a=(SignatureT obj)} (CatHomF {obj})

public export
CatEitherF : {obj : Type} -> HomEndofunctor obj
CatEitherF {obj} = SliceTrEitherF {a=(SignatureT obj)} (CatHomF {obj})

public export
CEid : {obj : Type} -> {0 hom : HomSlice obj} ->
  (x : obj) -> CatEitherF {obj} hom (x, x)
CEid x = InSlC $ CHId x

public export
CEcomp : {obj : Type} -> {0 hom : HomSlice obj} ->
  {x, y, z: obj} -> hom (y, z) -> hom (x, y) -> CatEitherF {obj} hom (x, z)
CEcomp f g = InSlC $ CHComp f g

public export
FreeHomM : (obj : Type) -> HomEndofunctor obj
FreeHomM obj = SliceFreeM {a=(SignatureT obj)} (CatHomF {obj})

public export
chId : {obj : Type} ->
  (hom : HomSlice obj) -> (a : obj) -> FreeHomM obj hom (a, a)
chId {obj} hom a = InSlFc $ CHId a

public export
chComp : {obj : Type} -> {a, b, c : obj} -> {hom : HomSlice obj} ->
  FreeHomM obj hom (b, c) -> FreeHomM obj hom (a, b) -> FreeHomM obj hom (a, c)
chComp {obj} {a} {b} {c} {hom} g f = InSlFc $ CHComp g f

public export
HomSliceCata : Type -> Type
HomSliceCata obj = SliceFreeCata {a=(SignatureT obj)} (CatHomF {obj})

public export
homSliceCata : {obj : Type} -> HomSliceCata obj
homSliceCata {obj} sv sa subst alg (a, b) (InSlF (a, b) (InSlV v)) =
  subst (a, b) v
homSliceCata {obj} sv sa subst alg (a, b) (InSlF (a, b) (InSlC m)) =
  alg (a, b) $ case m of
    CHId c => CHId c
    CHComp {x} {y} {z} g f =>
      CHComp {x} {y} {z}
        (homSliceCata {obj} sv sa subst alg (y, z) g)
        (homSliceCata {obj} sv sa subst alg (x, y) f)

public export
chFreeFMap : {obj : Type} -> {hom : HomSlice obj} -> {f : SliceObj obj} ->
  ((a, b : obj) -> hom (a, b) -> f a -> f b) ->
  ((a, b : obj) -> FreeHomM obj hom (a, b) -> f a -> f b)
chFreeFMap {obj} {hom} {f} fmap a b =
  homSliceCata hom (\(x, y) => f x -> f y)
    (\(x, y) => fmap x y)
    (\(x, z), m => case m of CHId z => id ; CHComp g f => g . f)
    (a, b)

public export
chFreeFContramap : {obj : Type} -> {hom : HomSlice obj} -> {f : SliceObj obj} ->
  ((a, b : obj) -> hom (a, b) -> f b -> f a) ->
  ((a, b : obj) -> FreeHomM obj hom (a, b) -> f b -> f a)
chFreeFContramap {obj} {hom} {f} fmap a b =
  homSliceCata hom (\(x, y) => f y -> f x)
    (\(x, y) => fmap x y)
    (\(x, z), m => case m of CHId z => id ; CHComp g f => f . g)
    (a, b)

public export
FreeHomRel : {obj : Type} -> SliceObj (HomSlice obj)
FreeHomRel {obj} hom =
  DepRelOn {a=(SignatureT obj)} (FreeHomM obj hom, FreeHomM obj hom)

public export
FreeHomEqF : {obj : Type} -> (hom : HomSlice obj) ->
  FreeHomRel {obj} hom -> FreeHomRel {obj} hom
FreeHomEqF {obj} hom = DepFreeEqF {a=(SignatureT obj)} {sl=(FreeHomM obj hom)}

public export
CatRelObj : {obj : Type} -> SliceObj (HomSlice obj)
CatRelObj {obj} hom = SigRelObj {obj} (FreeHomM obj hom)

public export
CatRelT : {obj : Type} -> SliceObj (HomSlice obj)
CatRelT {obj} hom = SigRelT {obj} (FreeHomM obj hom)

public export
data SigToCatRel : {obj : Type} -> {hom : HomSlice obj} ->
    SigRelT {obj} hom -> CatRelT {obj} hom where
  StoCR : {0 obj : Type} -> {0 hom : HomSlice obj} ->
    {0 rv : SigRelT hom} ->
    {0 a, b : obj} -> {0 f, g : hom (a, b)} ->
    rv ((a, b) ** (f, g)) ->
    SigToCatRel {obj} {hom} rv ((a, b) ** (InSlFv f, InSlFv g))

public export
data CatEqAx : {obj : Type} -> {hom : HomSlice obj} -> CatRelT hom where
  CEidL :
    {0 obj : Type} -> {0 hom : HomSlice obj} ->
    {0 a, b : obj} -> (0 f : FreeHomM obj hom (a, b)) ->
    CatEqAx {obj} {hom} ((a, b) ** (f, chComp (chId hom b) f))
  CEidR :
    {0 obj : Type} -> {0 hom : HomSlice obj} ->
    {0 a, b : obj} -> (0 f : FreeHomM obj hom (a, b)) ->
    CatEqAx {obj} {hom} ((a, b) ** (f, chComp f (chId hom a)))
  CEassoc :
    {0 obj : Type} -> {0 hom : HomSlice obj} ->
    {0 a, b, c, d : obj} ->
    (0 f : FreeHomM obj hom (a, b)) ->
    (0 g : FreeHomM obj hom (b, c)) ->
    (0 h : FreeHomM obj hom (c, d)) ->
    CatEqAx {obj} {hom}
      ((a, d) ** (chComp h (chComp g f), chComp (chComp h g) f))

public export
data CatFreeEqF : {obj : Type} -> {hom : HomSlice obj} ->
    CatRelT hom -> CatRelT hom where
  CEax : {0 obj : Type} -> {0 hom : HomSlice obj} ->
    {0 ra : CatRelT hom} ->
    {0 a, b : obj} -> {0 f, g : FreeHomM obj hom (a, b)} ->
    CatEqAx {obj} {hom} ((a, b) ** (f, g)) ->
    CatFreeEqF {obj} {hom} ra ((a, b) ** (f, g))
  CEeq : {0 obj : Type} -> {0 hom : HomSlice obj} ->
    {0 ra : CatRelT hom} ->
    {0 a, b : obj} -> {0 f, g : FreeHomM obj hom (a, b)} ->
    FreeHomEqF {obj} hom ra ((a, b) ** (f, g)) ->
    CatFreeEqF {obj} {hom} ra ((a, b) ** (f, g))

public export
CatFreeEq : {obj : Type} -> {hom : HomSlice obj} -> (rel : SigRelT hom) ->
  CatRelT hom
CatFreeEq {obj} {hom} rel =
  SliceFreeM
    {a=(CatRelObj {obj} hom)}
    (CatFreeEqF {obj} {hom})
    (SigToCatRel rel)

public export
record Diagram where
  constructor MkDiagram
  dVert : Type
  dEdge : HomSlice dVert
  -- `dRel` is a relation which, when we freely generate a category from
  -- the diagram, will freely generate an equivalence relation, but `dRel`
  -- itself does not promise to be an equivalence relation.
  dRel : SigRelT dEdge

public export
diagToCatForget : SCat -> Diagram
diagToCatForget sc =
  MkDiagram sc.scObj sc.scHom (\(sig ** (f, g)) => eqRel (sc.scEq sig) f g)

public export
DiagFreeObj : Diagram -> Type
DiagFreeObj diag = diag.dVert

public export
DiagFreeSig : Diagram -> Type
DiagFreeSig = SignatureT . DiagFreeObj

public export
DiagFreeHom : (diag : Diagram) -> HomSlice (DiagFreeObj diag)
DiagFreeHom diag = FreeHomM diag.dVert diag.dEdge

public export
diagFreeId :
  (diag : Diagram) -> (a : DiagFreeObj diag) -> DiagFreeHom diag (a, a)
diagFreeId diag a = chId diag.dEdge a

public export
diagFreeComp : {diag : Diagram} -> {a, b, c : DiagFreeObj diag} ->
  DiagFreeHom diag (b, c) -> DiagFreeHom diag (a, b) -> DiagFreeHom diag (a, c)
diagFreeComp {diag} g f = chComp {hom=diag.dEdge} g f

public export
DiagFreeSigRel : (diag : Diagram) -> SigRelT (DiagFreeHom diag)
DiagFreeSigRel diag = CatFreeEq {obj=diag.dVert} {hom=diag.dEdge} diag.dRel

public export
DiagFreeRel : (diag : Diagram) -> (sig : DiagFreeSig diag) ->
  RelationOn (DiagFreeHom diag sig)
DiagFreeRel diag sig f g = DiagFreeSigRel diag (sig ** (f, g))

public export
DiagFreeRelIsRefl : (diag : Diagram) -> (a, b : DiagFreeObj diag) ->
  IsReflexive (DiagFreeRel diag (a, b))
DiagFreeRelIsRefl diag a b f =
  InSlF ((a, b) ** (f, f)) $ InSlC $ CEeq $ DFErefl f

public export
DiagFreeRelIsSym : (diag : Diagram) -> (a, b : DiagFreeObj diag) ->
  IsSymmetric (DiagFreeRel diag (a, b))
DiagFreeRelIsSym diag a b {x=f} {y=g} eq =
  InSlF ((a, b) ** (g, f)) $ InSlC $ CEeq $ DFEsym eq

public export
DiagFreeRelIsTrans : (diag : Diagram) -> (a, b : DiagFreeObj diag) ->
  IsTransitive (DiagFreeRel diag (a, b))
DiagFreeRelIsTrans diag a b {x=f} {y=g} {z=h} eqfg eqgh =
  InSlF ((a, b) ** (f, h)) $ InSlC $ CEeq $ DFEtrans eqgh eqfg

public export
DiagFreeRelIsEquiv : (diag : Diagram) -> (a, b : DiagFreeObj diag) ->
  IsEquivalence (DiagFreeRel diag (a, b))
DiagFreeRelIsEquiv diag a b =
  MkEquivalence
    (DiagFreeRelIsRefl diag a b)
    (DiagFreeRelIsSym diag a b)
    (DiagFreeRelIsTrans diag a b)

public export
DiagFreeEqRel : (diag : Diagram) -> (sig : DiagFreeSig diag) ->
  EqRel (DiagFreeHom diag sig)
DiagFreeEqRel diag (a, b) =
  MkEq (DiagFreeRel diag (a, b)) (DiagFreeRelIsEquiv diag a b)

public export
DiagFreeIdL : (diag : Diagram) -> {a, b : DiagFreeObj diag} ->
  (f : DiagFreeHom diag (a, b)) ->
  DiagFreeRel diag (a, b) f (diagFreeComp {diag} (diagFreeId diag b) f)
DiagFreeIdL diag {a} {b} f =
  InSlF ((a, b) ** (f, diagFreeComp (diagFreeId diag b) f)) $
    InSlC $ CEax $ CEidL f

public export
DiagFreeIdR : (diag : Diagram) -> {a, b : DiagFreeObj diag} ->
  (f : DiagFreeHom diag (a, b)) ->
  DiagFreeRel diag (a, b) f (diagFreeComp {diag} f (diagFreeId diag a))
DiagFreeIdR diag {a} {b} f =
  InSlF ((a, b) ** (f, diagFreeComp f (diagFreeId diag a))) $
    InSlC $ CEax $ CEidR f

public export
DiagFreeAssoc : (diag : Diagram) -> {a, b, c, d : DiagFreeObj diag} ->
  (f : DiagFreeHom diag (a, b)) ->
  (g : DiagFreeHom diag (b, c)) ->
  (h : DiagFreeHom diag (c, d)) ->
  DiagFreeRel diag (a, d)
    (diagFreeComp {diag} h (diagFreeComp {diag} g f))
    (diagFreeComp {diag} (diagFreeComp {diag} h g) f)
DiagFreeAssoc diag {a} {b} {c} {d} f g h =
  InSlF
    ((a, d) **
     (diagFreeComp {diag} h (diagFreeComp {diag} g f),
      diagFreeComp {diag} (diagFreeComp {diag} h g) f)) $
    InSlC $ CEax $ CEassoc f g h

public export
DiagToFreeCat : Diagram -> SCat
DiagToFreeCat diag =
  SC
    (DiagFreeObj diag)
    (DiagFreeHom diag)
    (diagFreeId diag)
    (diagFreeComp {diag})
    (DiagFreeEqRel diag)
    (DiagFreeIdL diag)
    (DiagFreeIdR diag)
    (DiagFreeAssoc diag)

-----------------------------------------
-----------------------------------------
---- Polynomial functors on diagrams ----
-----------------------------------------
-----------------------------------------

public export
sigMap : (obj -> obj') -> SignatureT obj -> SignatureT obj'
sigMap m (a, b) = (m a, m b)

public export
HomMap : {obj, obj' : Type} ->
  (m : obj -> obj') -> HomSlice obj -> HomSlice obj' -> Type
HomMap {obj} m sl sl' = SliceMorphism {a=(SignatureT obj)} sl (sl' . sigMap m)

public export
sigObjMap : {obj, obj' : Type} ->
  {m : obj -> obj'} -> {sl : HomSlice obj} -> {sl' : HomSlice obj'} ->
  HomMap {obj} {obj'} m sl sl' ->
  SigRelObj sl -> SigRelObj sl'
sigObjMap {obj} {obj'} {m} {sl} {sl'} hm ((a, b) ** (f, g)) =
  ((m a, m b) ** (hm (a, b) f, hm (a, b) g))

public export
HomRelMap : {obj, obj' : Type} ->
  {m : obj -> obj'} -> {sl : HomSlice obj} -> {sl' : HomSlice obj'} ->
  HomMap {obj} {obj'} m sl sl' ->
  SigRelT sl -> SigRelT sl' ->
  Type
HomRelMap {obj} {obj'} {m} {sl} {sl'} hm rel rel' =
  SliceMorphism {a=(SigRelObj sl)} rel (rel' . sigObjMap hm)

public export
record DiagFunctor (dom, cod : Diagram) where
  constructor MkDiagF
  dfVmap : dom.dVert -> cod.dVert
  dfEmap : HomMap {obj=dom.dVert} dfVmap dom.dEdge cod.dEdge
  0 dfRmap : HomRelMap {m=dfVmap} dfEmap dom.dRel cod.dRel

public export
record PolyDOF where
  constructor PDOF
  pdfPos : Type
  pdfDir : pdfPos -> Diagram

public export
pdofInterp : PolyDOF -> Diagram -> Type
pdofInterp pdof diag =
  (i : pdof.pdfPos ** DiagFunctor (pdof.pdfDir i) diag)

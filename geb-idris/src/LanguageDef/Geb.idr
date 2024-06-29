module LanguageDef.Geb

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import LanguageDef.BinTree
import LanguageDef.PolyCat
import LanguageDef.DiagramCat
import LanguageDef.NatPrefixCat
import LanguageDef.PolyIndTypes
import LanguageDef.FinCat
import LanguageDef.InternalCat
import LanguageDef.SlicePolyCat
import LanguageDef.QType
import LanguageDef.MLBundleCat
import LanguageDef.PolySliceCat
import LanguageDef.GenPolyFunc

%default total
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)

---------------------------------
---------------------------------
---- `QType` as `DiagramCat` ----
---------------------------------
---------------------------------

public export
0 QTDCat : Diagram
QTDCat = catToDiagForget QTSCat

--------------------------------------
--------------------------------------
---- Reachability through W-types ----
--------------------------------------
--------------------------------------

------------------------------
---- Dependent-arena form ----
------------------------------

public export
data ReachableBasePos :
    {0 a : Type} -> SliceObj a where
  RPos : {0 a : Type} -> (0 ea : a) -> ReachableBasePos {a} ea

public export
data ReachableBaseDir :
    {0 a : Type} -> SliceObj (Sigma {a} $ ReachableBasePos {a}) where
  RDir : {0 a : Type} -> (0 ea : a) -> ReachableBaseDir {a} (ea ** RPos ea)

public export
ReachableBaseAssign :
  {0 a : Type} -> (a -> a) ->
  Sigma {a=(Sigma {a} $ ReachableBasePos {a})} (ReachableBaseDir {a}) -> a
ReachableBaseAssign {a} f ((ea ** RPos ea) ** RDir ea) = f ea

public export
ReachableBase : {0 a : Type} -> (a -> a) -> SlicePolyEndoFunc a
ReachableBase {a} f =
  (ReachableBasePos {a} ** ReachableBaseDir {a} ** ReachableBaseAssign {a} f)

-- If `F : SliceObj a` and `f : a -> a`, and for any `ea : a` we interpret
-- `F(ea)` as a type of proofs of reachability of `ea`, then
-- `ReachableBaseF {a} f F (f ea)` is the type of proofs of reachability of
-- `f ea` via single applications of `f` to elements of `a` which can be
-- proven reachable by `F {a} f`.  `ReachableBaseF {a} f` is polynomial --
-- it is the interpretation of `ReachableBase {a} f`, which is a W-type
-- (expressed in dependent-type form, `SlicePolyEndoFunc`).
public export
ReachableBaseF : {a : Type} -> (a -> a) -> SliceEndofunctor a
ReachableBaseF {a} f = InterpSPFunc {a} (ReachableBase {a} f)

public export
ReachableBaseFMap : {a : Type} -> (f : a -> a) ->
  {sa, sa' : SliceObj a} ->
  SliceMorphism sa sa' ->
  SliceMorphism (ReachableBaseF {a} f sa) (ReachableBaseF {a} f sa')
ReachableBaseFMap {a} f {sa} {sa'} =
  InterpSPFMap {a} {b=a} (ReachableBase {a} f)

public export
ReachableFreeM : {a : Type} -> (a -> a) -> SlicePolyEndoFunc a
ReachableFreeM {a} f = SPFFreeM {a} (ReachableBase {a} f)

-- Under the same interpretation as `ReachableBaseF`,
-- `ReachableFreeF {a} f F ea` is the type of proofs of reachability of
-- elements of `a` via any finite number of applications of `f`.  Like
-- `ReachableBaseF`, it is polynomial -- it is the free monad of
-- `ReachableBaseF`.
public export
ReachableFreeF : {a : Type} -> (a -> a) -> SliceEndofunctor a
ReachableFreeF {a} f = SlicePolyFree {a} (ReachableBase {a} f)

-- The universal `eval` morphism of a free monad (in this case,
-- `ReachableFreeF`).
public export
ReachableEval : {a : Type} -> (f : a -> a) -> SPFMeval (ReachableBase {a} f)
ReachableEval {a} f = spfmEval {a} (ReachableBase {a} f)

-- `ReachableSl` {a} f init` is the subset of `a` which is reachable from
-- the subset `Subset0 a init` of `a` by any finite number of applications of
-- `f`.
public export
ReachableSl : {a : Type} -> (a -> a) -> SliceObj (SliceObj a)
ReachableSl {a} f init = Subset0 a (ReachableFreeF {a} f init)

public export
ReachableF : {a : Type} -> (a -> a) -> SliceFunctor a Unit
ReachableF {a} f init () = ReachableSl {a} f init

public export
ReachableFid : {a : Type} -> SliceFunctor a Unit
ReachableFid {a} = ReachableF {a} (id {a})

public export
ReachableMu : {a : Type} -> SliceFunctor a (a -> a)
ReachableMu {a} = flip (ReachableSl {a})

---------------------
---- W-type form ----
---------------------

-- `ReachableBase` is just a specification of `BaseChangeF`.
0 ReachableBaseW : {a : Type} -> (a -> a) -> WTypeFunc a a
ReachableBaseW {a} = BCasWTF {c=a} {d=a}

0 ReachableBaseToW : {a : Type} -> (f : a -> a) -> {sl : SliceObj a} ->
  SliceMorphism {a}
    (ReachableBaseF {a} f sl)
    (InterpWTF (ReachableBaseW {a} f) sl)
ReachableBaseToW {a} f {sl} ea (RPos ea ** d) =
  (Element0 ea Refl ** \(Element0 ea Refl) => d (RDir ea))

0 ReachableBaseFromW : {a : Type} -> (f : a -> a) -> {sl : SliceObj a} ->
  SliceMorphism {a}
    (InterpWTF (ReachableBaseW {a} f) sl)
    (ReachableBaseF {a} f sl)
ReachableBaseFromW {a} f {sl} ea (Element0 ea Refl ** d) =
  (RPos ea ** \(RDir ea) => d $ Element0 ea Refl)

---------------------
---------------------
---- Free arenas ----
---------------------
---------------------

public export
ArenaArena : Type
ArenaArena = PolyFunc -> PolyFunc

PolyFreeRelPos : PolyFunc -> Type
PolyFreeRelPos = ReachableBasePos {a=PolyFunc}

PolyFreeRelDir : Sigma {a=PolyFunc} PolyFreeRelPos -> Type
PolyFreeRelDir = ReachableBaseDir {a=PolyFunc}

PolyFreeRelAssign : ArenaArena ->
  Sigma {a=(Sigma {a=PolyFunc} PolyFreeRelPos)} PolyFreeRelDir -> PolyFunc
PolyFreeRelAssign = ReachableBaseAssign {a=PolyFunc}

PolyRelSPF : ArenaArena -> SlicePolyEndoFunc PolyFunc
PolyRelSPF = ReachableBase {a=PolyFunc}

PolyFreeRelSPF : ArenaArena -> SlicePolyEndoFunc PolyFunc
PolyFreeRelSPF = ReachableFreeM {a=PolyFunc}

public export
PolyFreeRel : ArenaArena -> SliceEndofunctor PolyFunc
PolyFreeRel = ReachableFreeF {a=PolyFunc}

public export
data PolyInitRel : PolyFunc -> Type where
  PFRi : PolyInitRel PFInitialArena

public export
PolyRelMu : ArenaArena -> PolyFunc -> Type
PolyRelMu ar = PolyFreeRel ar PolyInitRel

public export
PolyFuncMu : ArenaArena -> Type
PolyFuncMu = ReachableMu {a=PolyFunc} PolyInitRel

-- A term of `PolyFuncMuFst` is a term of any type `pos` such that
-- `(pos ** dir) : PolyFunc` is reachable from `PFInitialArena` via
-- a finite number of applications of `ar`.
public export
PolyFuncMuFst : ArenaArena -> Type
PolyFuncMuFst ar = (p : PolyFuncMu ar ** fst $ fst0 p)

-- A term of `PolyFuncMuSnd` is a term of any type `dir i` such that
-- `(pos ** dir) : PolyFunc` is reachable from `PFInitialArena` via
-- a finite number of applications of `ar` and `i` is a term of `pos`.
public export
PolyFuncMuSnd : (ar : ArenaArena) -> PolyFuncMuFst ar -> Type
PolyFuncMuSnd ar (Element0 (pos ** dir) rel ** i) = dir i

-- A term of `PolyFuncMuSigma` is a dependent pair of a term `i : pos` and
-- a term of `dir i` where `(pos ** dir) : PolyFunc` is reachable from
-- `PFInitialArena` via a finite number of applications of `ar` and `i` is a
-- term of `pos`.
public export
PolyFuncMuSigma : ArenaArena -> Type
PolyFuncMuSigma ar = DPair (PolyFuncMuFst ar) (PolyFuncMuSnd ar)

-- A term of `PolyFuncMuPF` is itself a polynomial functor, whose position-set
-- is the set of reachable positions, and whose direction-set is the dependent
-- set of reachable directions corresponding to those positions.
public export
PolyFuncMuPF : ArenaArena -> PolyFunc
PolyFuncMuPF ar = MkDPair (PolyFuncMuFst ar) (PolyFuncMuSnd ar)

------------------------------------------
------------------------------------------
---- Internal polynomial endofunctors ----
------------------------------------------
------------------------------------------

-----------------------------------------------------------
---- Representable endofunctors internal to `PolyFunc` ----
-----------------------------------------------------------

PFIntArena : Type
PFIntArena = (pos : Type ** pos -> PolyFunc)

InterpPFIntPolyPos : PFIntArena -> PolyFunc -> Type
InterpPFIntPolyPos (pos ** dir) q =
  pfSetCoproductPos {a=pos} $ \i => pfHomObj (dir i) q

InterpPFIntPolyDir : (ar : PFIntArena) -> (p : PolyFunc) ->
  InterpPFIntPolyPos ar p -> Type
InterpPFIntPolyDir (pos ** dir) q =
  pfSetCoproductDir {a=pos} $ \i => pfHomObj (dir i) q

PFIntPolyMuF : (p : PFIntArena) -> ArenaArena
PFIntPolyMuF ar p = (InterpPFIntPolyPos ar p ** InterpPFIntPolyDir ar p)

PFIntPolyRel : PFIntArena -> PolyFunc -> Type
PFIntPolyRel ar = PolyRelMu (PFIntPolyMuF ar)

PFIntPolyMuFPF : PFIntArena -> Type
PFIntPolyMuFPF ar = PolyFuncMu (PFIntPolyMuF ar)

PFIntPolyMuFPos : (ar : PFIntArena) -> Type
PFIntPolyMuFPos ar = PolyFuncMuFst (PFIntPolyMuF ar)

PFIntPolyMuFDir : (ar : PFIntArena) -> PFIntPolyMuFPos ar -> Type
PFIntPolyMuFDir ar = PolyFuncMuSnd (PFIntPolyMuF ar)

PFIntPolyMuPF : PFIntArena -> PolyFunc
PFIntPolyMuPF ar = PolyFuncMuPF (PFIntPolyMuF ar)

PFIntPolyMuSigma : PFIntArena -> Type
PFIntPolyMuSigma ar = PolyFuncMuSigma (PFIntPolyMuF ar)

InterpPFIntDirich : PFIntArena -> PolyFunc -> PolyFunc
InterpPFIntDirich (pos ** dir) q =
  pfSetCoproductArena {a=pos} $ \i => pfHomObj q (dir i)

-------------------------------------
-------------------------------------
---- Language architecture notes ----
-------------------------------------
-------------------------------------

-------------------
---- Dualities ----
-------------------

-- We summarize the what we gain from each dualization or other form of
-- generalization from the simple `Poly` subcategory of `Type -> Type`:
--
--  1) Extending from programming in a "base" category such as `Type` to
--     programming in `Poly` itself gives us inductive data types a la carte,
--     with a much wider variety of combinators on inductive types.  Polynomial
--     functors also give us a notion of input interfaces (via algebras) and
--     output interfaces (via coalgebras).
--  2) Dirichlet endofunctors should emerge as a special case, like
--     `Poly`, of extending to profunctors (`op(Type) -> Type -> Type`) --
--     polynomial di/pro-functors will be "mixed" polynomial and Dirichlet
--     (endo-)functors ("di/endo" is an important special case because we
--     can make free ones and use the diYoneda embedding).
--  3) Extending from polynomial endofunctors to polynomial _di_functors
--     (endo-profunctors) allows us to use the _di-_(co-)Yoneda embedding
--     rather than just the (contra-)Yoneda embedding, which is crucial to
--     enabling categories a la carte because we need to specify universal
--     properties both from the right and the left simultaneously.
--     Polynomial difunctors also give us a notion of _combined_ interfaces
--     which specify both inputs and outputs at the same time.
--  4) Extending from polynomial functors on `Type` to those on slice
--     categories (`Type/c` for `c : Type`) gives us dependent data types;
--     when we are also extending from polynomial functors to polynomial
--     _pro_functors, the analogue is _splice_ categories, so for categories
--     a la carte with dependent types, we use polynomial profunctors on
--     splice categories.  Specifically, because this makes objects and
--     morphisms dependent on objects of `Type`, it allows us to define
--     _families_ of categories with mutual dependencies -- which is also
--     in effect an absolute requirement of categories a la carte, because
--     the adjunctions which define universal properties are not (necessarily,
--     or even usually) between endofunctors, but between functors between
--     different categories (for example, initial and terminal objects come
--     from adjunctions between the categories which have them and the
--     terminal category; products and coproducts come from adjunctions between
--     the categories which have them and their product categories -- note
--     that in that case, the other category _depends_ on the category we're
--     defining).  In fact, even defining a single category without reference
--     to other categories is at least more convenient when we use slice/splice
--     categories because we can slice over `2` to define objects and morphisms
--     using (potentially mutual) recursion, and indeed separate classes of
--     _universal_ objects/morphisms with dependencies between them -- the
--     object of morphisms will certainly depend on the object of objects, and
--     the other way around can also happen, for example in the case of freely-
--     generated (co)equalizers.  We might also slice over `Fin 3` to include
--     functors, or `Fin 4` to include natural transformations as well, or
--     `Fin 5` to add adjunctions.  We may therefore define categories a la
--     carte by using (polynomial pro-)functors, (polynomial para-)natural
--     transformations, and adjunctions by slicing over (internally-dependent)
--     pairs of `Fin 5` with (internal) parameters -- categories of natural
--     transformations might be indexed as `2 x (functor, functor)`, where
--     `functor` in turn is indexed by `(category, category)`, and the two
--     `category` parameters of the two `functor` parameters to `natural
--     transformation` must match.  Thus categories a la carte require at least
--     polynomial profunctors on splice categories.
--
--     Extending polynomial (di-)functors to s(p)lice categories also extends
--     our notion of polynomial-functors-as-interfaces to _multi-sorted_
--     interfaces.
--  5) Extending from polynomial profunctors on slice categories to polynomial
--     profunctors on presheaf categories allows us to specify internal
--     morphisms, which we need in order to express the relationships among
--     the internal parameters within the slice, which we need in order to
--     express the coherence described above between parameters which ensure
--     properties such as how natural transformations occur only between
--     functors whose domains and codomains match.  This use of presheaf
--     rather than just slice categories means that we end up using (structural)
--     (co)ends rather than just sigma and pi types to construct polynomial
--     (pro)functors inductively.
--
--     When combined with the "ANF transformation" enabled by the definition
--     of polynomial (di-)functors, the extension to (co/pro-)sheaf categories
--     as domains (prosheaves are just profunctors, just as (co)presheaves are
--     just functors to `Type`, but we may use the term "prosheaf" to
--     distinguish profunctors as _(co)domains_ of (pro)functors) also gives
--     us inductive-inductive types (from presheaves, or the contravariant
--     component of a prosheaf) and inductive-recursive types (from
--     copresheaves, or the covariant component of a prosheaf).
--
--     Also, from the interface perspective, extending from (co)s(p)lices to
--     (co/pro/pre)sheaves allows us to define _operations_, not just sorts,
--     of generalized algebraic theories.
--  6) Extending from polynomial (pro-)functors on presheaf categories to
--     polynomial (pro-)functors on _profunctor_ categories allows us to
--     combine the slice-to-splice extension with the slice-to-presheaf
--     extension.  The splice extension is the one which allows us to the
--     the _di_Yoneda embedding and paranatural transformations, thus using
--     covariance and contravariance simultaneously, and the slice-to-presheaf
--     extension is the one which allows us to ensure coherence among internal
--     parameters, both of which are necessary for categories a la carte, so
--     we do require profunctors on profunctor categories.  Thus we are
--     forced into that form of reflection:  profunctors on profunctor
--     categories are themselves objects of profunctor categories.  This is
--     a category-theoretic, universal, formally-verifiable form of
--     metacircularity.
--  7) Drawing objects and morphisms in our definition of categories internal
--     to Geb allows us to do enriched category theory.
--  8) The universal factorization of a functor allows us to define
--     polynomial functors across _arbitrary_ categories (not even just
--     profunctor categories).  It has both covariant and contravariant forms,
--     so it too can be dualized to a comprehensive factorization of a
--     _profunctor_, using the category of _diagonal_ elements (I think).
--     Taking a (structural) (co)end of a difunctor on _any_ category
--     takes us back to an object of `Type` (or any enriching category)
--     (together with a universal paranatural transformation between that
--     object and the difunctor), by analogue with how taking a sigma or
--     pi (using the unique morphism to the terminal object of `Type`)
--     on a slice category brins us back to `Type`:  a sigma of a slice
--     category gives us the generalized analogue from type theory of a choice
--     of a particular type from a type family (where the slice category is the
--     type family) together with a term of that type, while the coend
--     further generalizes that to a "term" of an object of an arbitrary
--     category (it's using the category of diagonal elements to produce the
--     analogue of a term); a pi of a slice category gives us the generalized
--     analogue from type theory of a choice of terms from each type of a
--     type family, while the end further generalizes that to a "type"
--     dependent upon an object of an arbitrary category.
--  9) Drawing _theories_ -- polynomial profunctors in profunctors themselves --
--     from arbitrary categories by using dependencies on objects of arbitrary
--     categories (using structural (co)ends as described above) allows us to
--     define categories internal to categories internal to Geb, which is
--     metacircular _metalogic_ (we identify a metalogic with a higher
--     category, such as Geb itself).
-- 10) Higher categories of higher categories give us double categories,
--     `n`-fold categories via iteration, and infinity-categories via
--     fixed points of that iteration.
-- 11) Extending from dialgebras to algebras of profunctors, in particular
--     when combined with the internal "ANF transformation" allowed by the
--     definition of a _polynomial_ profunctor (which can be viewed as an
--     extension specifically of dialgebras between _polynomial_ functors),
--     allows us to generate free formally-verifiable-and-executable
--     specifications from all generalized algebraic theores -- even those
--     for which we have no real implementation, and even those which depend
--     on oracles which provably can _have_ no interpretation, because the
--     "execution" need not reduce fully, but is expressed in terms of
--     metalanguage continuations.  This allows us to inspect and execute
--     "what would happen if we had an oracle for".  (It also allows us to
--     perform implementation of a theory in terms of others, by substituting
--     real implementations in for oracles, when such implementations exist.)
-- 12) I think that the interface perspective combined with the ANF
--     transformation, which leads to free implementations in terms of
--     continuations and natural transformations (all using Yoneda!), might
--     also give us coequalizers (as polynomial natural transformations and
--     adjunctions with the two-object/two-parallel-morphisms category),
--     and thus the ability to implement quotient types, _without_
--     client-visible explicit equality, and _within_ a category (such as
--     Idris's `Type`) which does not itself have (explicit, at least)
--     coequalizers or quotient types.
-- 13) Initial algebras (of polynomial profunctors) within this context give
--     us categories/theories a la carte; terminal coalgebras give us
--     (potentially non-terminating) execution traces.
-- 14) Including in the language definition a standard library written
--     in Geb itself allows Geb to self-host, and allows programs written
--     in Geb to reason using the axioms of Geb, including about Geb itself,
--     and to define languages as extensions of, or using components of, Geb
--     itself.

-- The direction-map of a polynomial functor, which we may view as a slice
-- object of `pos`, may equivalently be viewed as a (co)presheaf (into `Type`)
-- from the discrete category whose objects are terms of `pos`.  (Because
-- the domain category `pos` is discrete, there is no difference between viewing
-- the functor `dir` as covariant or as contravariant, because it has no
-- non-identity morphisms to map into functions of `Type`.)
--
-- As a functor into `Type`, it has a category of elements, which we
-- now define.  Note that this is not the category of elements of the
-- `PolyFunc` itself -- it is the category of elements of its `dir` component
-- viewed as a functor.
PFDirCatElemObj : PolyFunc -> Type
PFDirCatElemObj (pos ** dir) = Sigma {a=pos} dir

-- A morphism in the category of elements consists of a morphism of the
-- domain category -- of which there is always exactly one, the identity,
-- since the domain category is the discrete category with objects from
-- `pos` such that the `fmap` component takes the element of one output
-- set to the other.  Since that morphism must be the identity, that means
-- that the position components of the two objects of the category of
-- elements must be the same.  `fmap` is also the identity (in `Type`) by the
-- identity-to-identity functor law, so in this discrete case, the `fmap`
-- output requirement for a morphism in the category of elements means that
-- the elements of the output sets must also be equal.  Hence, the whole
-- objects of the category of elements must be equal.
--
-- In other words, there is precisely one morphism in the category of elements
-- between equal elements, and there are none between non-equal elements.
-- So, that one morphism when it exists is also the identity.
--
-- That is all to say:  the category of elements of a (co)presheaf on a
-- discrete category is also discrete.
PFDirCatElemMor : {p : PolyFunc} ->
  PFDirCatElemObj p -> PFDirCatElemObj p -> Type
PFDirCatElemMor {p=(pos ** dir)} x y = x = y

--------------------
---- Dialgebras ----
--------------------

-- An object of the category of elements of a polynomial functor
-- which is the exponential object of two polynomial functors is
-- a dialgebra for those two functors.  (Furthermore, the object part
-- of the dialgebra is the same object of `Type` as the object
-- underlying the given object of the category of elements.)
export
PolyExpToDialgFst : (p, q : PolyFunc) ->
  (a : Type) ->
  InterpPolyFunc (pfHomObj p q) a ->
  InterpPolyFunc p a ->
  pfPos q
PolyExpToDialgFst p q x (i ** d) (pi ** pd) =
  fst (i pi)

export
PolyExpToDialgSnd : (p, q : PolyFunc) ->
  (a : Type) ->
  (dialg : InterpPolyFunc (pfHomObj p q) a) ->
  (pa : InterpPolyFunc p a) ->
  pfDir {p=q} (PolyExpToDialgFst p q a dialg pa) ->
  a
PolyExpToDialgSnd p q x (i ** d) (pi ** pd) qdi with
    (snd (i pi) qdi) proof eq
  PolyExpToDialgSnd p q x (i ** d) (pi ** pd) qdi
    | Left () =
      d (pi ** (qdi ** rewrite eq in ()))
  PolyExpToDialgSnd p q x (i ** d) (pi ** pd) qdi
    | Right pdi =
      pd pdi

export
PolyExpToDialg : (p, q : PolyFunc) ->
  NaturalTransformation
    (InterpPolyFunc (pfHomObj p q))
    (Dialgebra (InterpPolyFunc p) (InterpPolyFunc q))
PolyExpToDialg p q x dialg px =
  (PolyExpToDialgFst p q x dialg px ** PolyExpToDialgSnd p q x dialg px)

export
PolyExpElemToDialg : (p, q : PolyFunc) ->
  MLPolyCatElemObj (pfHomObj p q) ->
  (x : Type ** Dialgebra (InterpPolyFunc p) (InterpPolyFunc q) x)
PolyExpElemToDialg p q (x ** pqx) = (x ** PolyExpToDialg p q x pqx)

public export
IsDialgMorph : (f, g : Type -> Type) -> Functor f -> Functor g ->
  (a, b : Type) -> Dialgebra f g a -> Dialgebra f g b -> (a -> b) -> Type
IsDialgMorph f g fm gm a b da db m =
  ExtEq {a=(f a)} {b=(g b)} (map {f=g} m . da) (db . map {f} m)

export
PolyExpMorToDialgDirEq : (p, q : PolyFunc) ->
  (a, b : Type) -> (m : a -> b) ->
  (dialgpos : pfPos (pfHomObj p q)) ->
  (dialgdir : pfDir {p=(pfHomObj p q)} dialgpos -> a) ->
  (i : pfPos p) -> (d : pfDir {p} i -> a) ->
  (qdi : pfDir {p=q} $ fst $ dialgpos i) ->
    m (PolyExpToDialgSnd p q a (dialgpos ** dialgdir) (i ** d) qdi) =
    PolyExpToDialgSnd p q b
      (InterpPFMap (pfHomObj p q) m (dialgpos ** dialgdir)) (i ** m . d) qdi
PolyExpMorToDialgDirEq (ppos ** dir) (qpos ** qdir) a b m di dd i d qdi
    with (snd (di i) qdi)
  PolyExpMorToDialgDirEq (ppos ** dir) (qpos ** qdir) a b m di dd i d qdi |
    Left () =
      Refl
  PolyExpMorToDialgDirEq (ppos ** dir) (qpos ** qdir) a b m di dd i d qdi |
    Right pdi =
      Refl

export
PolyExpMorToDialg : FunExt -> (p, q : PolyFunc) ->
  (a, b : Type) -> (m : a -> b) ->
  (dialg : InterpPolyFunc (pfHomObj p q) a) ->
  IsDialgMorph (InterpPolyFunc p) (InterpPolyFunc q)
    (MkFunctor $ InterpPFMap p) (MkFunctor $ InterpPFMap q)
    a b
    (PolyExpToDialg p q a dialg)
    (PolyExpToDialg p q b $ InterpPFMap (pfHomObj p q) m dialg)
    m
PolyExpMorToDialg fext (ppos ** dir) (qpos ** qdir) a b m (di ** dd) (i ** d) =
  dpEq12 Refl $ funExt $ \qdi =>
    PolyExpMorToDialgDirEq (ppos ** dir) (qpos ** qdir) a b m di dd i d qdi

public export
PolyHomIdToSection : (p : PolyFunc) ->
  (x : Type) -> InterpPolyFunc (pfHomObj p PFIdentityArena) x ->
  PFSection (pfProductArena (PFHomArena x) p)
PolyHomIdToSection (ppos ** pdir) x (i ** d) ((), pi)
    with (snd (i pi) ()) proof eq
  PolyHomIdToSection (ppos ** pdir) x (i ** d) ((), pi) | Left () =
    Left $ d (pi ** () ** rewrite eq in ())
  PolyHomIdToSection (ppos ** pdir) x (i ** d) ((), pi) | Right pd =
    Right pd

public export
PolyNTtoCEfuncElem : {p, q : PolyFunc} ->
  PolyNatTrans p q -> (e : MLPolyCatElemObj p) -> InterpPolyFunc q (fst e)
PolyNTtoCEfuncElem {p=p@(ppos ** pdir)} {q=q@(qpos ** qdir)} alpha (x ** e) =
  InterpPolyNT {p} {q} alpha x e

public export
PolyNTtoCEfunc : {p, q : PolyFunc} ->
  PolyNatTrans p q -> MLPolyCatElemObj p -> MLPolyCatElemObj q
PolyNTtoCEfunc {p=p@(ppos ** pdir)} {q=q@(qpos ** qdir)} alpha (x ** e) =
  (x ** PolyNTtoCEfuncElem {p} {q} alpha (x ** e))

public export
MLToPolyTerminalCatElem : Type -> MLPolyCatElemObj PFTerminalArena
MLToPolyTerminalCatElem x = (x ** () ** \v => void v)

public export
MLFromPolyTerminalCatElem : MLPolyCatElemObj PFTerminalArena -> Type
MLFromPolyTerminalCatElem (x ** () ** v) = x

public export
PolyPiElem : (p : PolyFunc) ->
  PolyNatTrans PFTerminalArena p -> Pi {a=Type} (InterpPolyFunc p)
PolyPiElem p@(pos ** dir) alpha x =
  PolyNTtoCEfuncElem {p=PFTerminalArena} {q=p} alpha $ MLToPolyTerminalCatElem x

--------------------------------------------------------------------
--------------------------------------------------------------------
---- Dirichlet presheaves enriched over polynomial copresheaves ----
--------------------------------------------------------------------
--------------------------------------------------------------------

public export
IntDirichPolyCatObj : (d, c : Type) -> (cmor : IntDifunctorSig c) -> Type
IntDirichPolyCatObj d c cmor =
  (pos : IntArena c ** PolyCatElemObj c cmor pos -> d)

public export
InterpIDPFobj : (d, c : Type) ->
  (dmor : IntDifunctorSig d) ->
  (cmor : IntDifunctorSig c) ->
  IntDirichPolyCatObj d c cmor -> IntProfunctorSig d c
InterpIDPFobj d c dmor cmor (pos ** dir) ed ec =
  (i : InterpIPFobj c cmor pos ec ** dmor ed (dir (ec ** i)))

public export
IntPolyDirichCatObj : (d, c : Type) -> (dmor : IntDifunctorSig d) -> Type
IntPolyDirichCatObj d c dmor =
  (pos : IntArena d ** DirichCatElemObj d dmor pos -> c)

public export
InterpIPDFobj : (d, c : Type) ->
  (dmor : IntDifunctorSig d) ->
  (cmor : IntDifunctorSig c) ->
  IntPolyDirichCatObj d c dmor -> IntProfunctorSig d c
InterpIPDFobj d c dmor cmor (pos ** dir) ed ec =
  (i : InterpIDFobj d dmor pos ed ** cmor ec (dir (ed ** i)))

-----------------------------------------
-----------------------------------------
---- Internal polynomial profunctors ----
-----------------------------------------
-----------------------------------------

---------------------------
---- Profunctor arenas ----
---------------------------

public export
IntProAr : (d, c : Type) -> Type
IntProAr d c = (pos : Type ** (pos -> d, pos -> c))

public export
IntEndoProAr : (c : Type) -> Type
IntEndoProAr c = IntProAr c c

-----------------------------------------
---- Profunctor arena interpretation ----
-----------------------------------------

public export
InterpIPPobj : (d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  IntProAr d c -> d -> c -> Type
InterpIPPobj d c dmor cmor (pos ** (contra, covar)) a b =
   (i : pos ** (dmor a (contra i), cmor (covar i) b))

public export
InterpIEPPobj : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntEndoProAr c -> c -> c -> Type
InterpIEPPobj c mor = InterpIPPobj c c mor mor

public export
InterpIPPdimap : (d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  (dcomp : IntCompSig d dmor) -> (ccomp : IntCompSig c cmor) ->
  (ar : IntProAr d c) ->
  IntDimapSig d c dmor cmor (InterpIPPobj d c dmor cmor ar)
InterpIPPdimap d c dmor cmor dcomp ccomp (pos ** (contra, covar)) s t a b
  dmas cmtb (i ** (dmsx, cmyt)) =
    (i ** (dcomp a s (contra i) dmsx dmas, ccomp (covar i) t b cmtb cmyt))

public export
InterpIEPPdimap : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (ar : IntEndoProAr c) ->
  IntEndoDimapSig c mor (InterpIEPPobj c mor ar)
InterpIEPPdimap c mor comp = InterpIPPdimap c c mor mor comp comp

--------------------------------------------
---- Profunctor natural transformations ----
--------------------------------------------

public export
IntPPNTar : (d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  IntProAr d c -> IntProAr d c -> Type
IntPPNTar d c dmor cmor
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar)) =
    (onpos : ppos -> qpos **
     ((i : ppos) -> dmor (pcontra i) (qcontra $ onpos i),
      (i : ppos) -> cmor (qcovar $ onpos i) (pcovar i)))

public export
InterpIPPnt : (d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  (dcomp : IntCompSig d dmor) -> (ccomp : IntCompSig c cmor) ->
  (p, q : IntProAr d c) -> IntPPNTar d c dmor cmor p q ->
  IntProfNTSig d c (InterpIPPobj d c dmor cmor p) (InterpIPPobj d c dmor cmor q)
InterpIPPnt d c dmor cmor dcomp ccomp
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar))
  (onpos ** (dcontra, dcovar)) a b (i ** (dmax, cmyb)) =
    (onpos i **
     (dcomp a (pcontra i) (qcontra (onpos i)) (dcontra i) dmax,
      ccomp (qcovar (onpos i)) (pcovar i) b cmyb (dcovar i)))

public export
0 InterpIPPntNatural : (d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  (dcomp : IntCompSig d dmor) -> (ccomp : IntCompSig c cmor) ->
  (dassoc : IntAssocSig d dmor dcomp) ->
  (cassoc : IntAssocSig c cmor ccomp) ->
  (p, q : IntProAr d c) -> (ar : IntPPNTar d c dmor cmor p q) ->
  IntProfNTNaturality d c dmor cmor
    (InterpIPPobj d c dmor cmor p)
    (InterpIPPobj d c dmor cmor q)
    (InterpIPPdimap d c dmor cmor dcomp ccomp p)
    (InterpIPPdimap d c dmor cmor dcomp ccomp q)
    (InterpIPPnt d c dmor cmor dcomp ccomp p q ar)
InterpIPPntNatural d c dmor cmor dcomp ccomp dassoc cassoc
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar))
  (onpos ** (dcontra, dcovar)) s t a b dmas cmtb (i ** (dmsp, cmpt)) =
    dpEq12
      Refl
      $ pairEqCong
        (dassoc a s (pcontra i) (qcontra (onpos i)) (dcontra i) dmsp dmas)
        (sym $ cassoc (qcovar $ onpos i) (pcovar i) t b cmtb cmpt (dcovar i))

public export
IntEPPNTar : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntEndoProAr c -> IntEndoProAr c -> Type
IntEPPNTar c mor = IntPPNTar c c mor mor

public export
InterpIEPPnt : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (p, q : IntEndoProAr c) -> IntEPPNTar c mor p q ->
  IntEndoProfNTSig c (InterpIEPPobj c mor p) (InterpIEPPobj c mor q)
InterpIEPPnt c mor comp = InterpIPPnt c c mor mor comp comp

public export
intPPNTvcomp : (d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  (dcomp : IntCompSig d dmor) -> (ccomp : IntCompSig c cmor) ->
  (p, q, r : IntProAr d c) ->
  IntPPNTar d c dmor cmor q r ->
  IntPPNTar d c dmor cmor p q ->
  IntPPNTar d c dmor cmor p r
intPPNTvcomp d c dmor cmor dcomp ccomp
  (ppos ** (pcontra, pcovar))
  (qpos ** (qcontra, qcovar))
  (rpos ** (rcontra, rcovar))
  (bonpos ** (bcontra, bcovar))
  (aonpos ** (acontra, acovar)) =
    (bonpos . aonpos **
     (\i =>
        dcomp (pcontra i) (qcontra (aonpos i)) (rcontra (bonpos (aonpos i)))
          (bcontra (aonpos i))
          (acontra i),
      \i =>
        ccomp (rcovar (bonpos (aonpos i))) (qcovar (aonpos i)) (pcovar i)
          (acovar i)
          (bcovar (aonpos i))))

----------------------------------------------------
---- Profunctor di/para-natural transformations ----
----------------------------------------------------

public export
record CatFromPrshf where
  constructor CFP
  cfpObj : Type
  cfpMor : cfpObj -> cfpObj -> Type
  cfpRepObj : cfpObj -> cfpObj -> Type
  cfpRepMor : (a : cfpObj) -> (x, y : cfpObj) ->
    cfpMor y x -> cfpRepObj a x -> cfpRepObj a y

public export
record PolyDiAr where
  constructor PDA
  pdaContra : PolyFunc
  pdaCovar : PolyFunc

public export
InterpPDA : PolyDiAr -> Type -> Type -> Type
InterpPDA (PDA contra covar) x y =
  InterpPolyFunc contra x -> InterpPolyFunc covar y

public export
interpPDAlmap : (pda : PolyDiAr) -> (0 s, t, a : Type) ->
  (a -> s) -> InterpPDA pda s t -> InterpPDA pda a t
interpPDAlmap (PDA contra covar) s t a mas = (|>) $ InterpPFMap contra mas

public export
interpPDArmap : (pda : PolyDiAr) -> (0 s, t, b : Type) ->
  (t -> b) -> InterpPDA pda s t -> InterpPDA pda s b
interpPDArmap (PDA contra covar) s t b mtb = (.) $ InterpPFMap covar mtb

public export
interpPDAdimap : (pda : PolyDiAr) -> (0 s, t, b : Type) ->
  (a -> s) -> (t -> b) -> InterpPDA pda s t -> InterpPDA pda a b
interpPDAdimap pda s t b mas mtb =
  interpPDAlmap pda s b a mas . interpPDArmap pda s t b mtb

public export
PDAend : PolyDiAr -> Type
PDAend (PDA contra covar) = PolyNatTrans contra covar

public export
record PDAcoend (ar : PolyDiAr) where
  constructor PDAc
  pdacObj : Type
  pdacElem : InterpPDA ar pdacObj pdacObj

public export
IntPDiNTar : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntEndoProAr c -> IntEndoProAr c -> Type
IntPDiNTar c mor (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar)) =
  (onpos : ppos -> qpos **
   ((i : ppos) -> mor (pcontra i) (qcontra $ onpos i),
    (i : ppos) -> mor (qcovar $ onpos i) (pcovar i)))

public export
InterpIEPPdint : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (p, q : IntEndoProAr c) -> IntPDiNTar c mor p q ->
  IntDiNTSig c (InterpIEPPobj c mor p) (InterpIEPPobj c mor q)
InterpIEPPdint c mor comp
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar))
  (onpos ** (dcontra, dcovar)) a (i ** (cmax, cmya)) =
    let
      passign : mor (pcovar i) (pcontra i) =
        comp (pcovar i) a (pcontra i) cmax cmya
    in
    (onpos i **
     (comp a (pcontra i) (qcontra $ onpos i) (dcontra i) cmax,
      comp (qcovar $ onpos i) (pcovar i) a cmya (dcovar i)))

public export
IntPDiNTPara : (c : Type) -> (mor : IntDifunctorSig c) ->
  (cid : IntIdSig c mor) -> (comp : IntCompSig c mor) ->
  (idl : IntIdLSig c mor comp cid) ->
  (idr : IntIdRSig c mor comp cid) ->
  (assoc : IntAssocSig c mor comp) ->
  (p, q : IntEndoProAr c) -> (ar : IntPDiNTar c mor p q) ->
  IntParaNTCond c mor
    (InterpIEPPobj c mor p)
    (InterpIEPPobj c mor q)
    (IntEndoLmapFromDimap c mor cid
      (InterpIEPPobj c mor p) (InterpIEPPdimap c mor comp p))
    (IntEndoRmapFromDimap c mor cid
      (InterpIEPPobj c mor p) (InterpIEPPdimap c mor comp p))
    (IntEndoLmapFromDimap c mor cid
      (InterpIEPPobj c mor q) (InterpIEPPdimap c mor comp q))
    (IntEndoRmapFromDimap c mor cid
      (InterpIEPPobj c mor q) (InterpIEPPdimap c mor comp q))
  (InterpIEPPdint c mor comp p q ar)
IntPDiNTPara c mor cid comp idl idr assoc
  (ppos ** (pcovar, pcontra)) (qpos ** (qcovar, qcontra))
  (onpos ** (dcontra, dcovar)) c0 c1 mc0c1
  (i0 ** (mcp0, mpc0)) (i1 ** (mcp1, mpc1)) cond =
    case mkDPairInjectiveFstHet cond of
      Refl =>
        let
          eq2 = mkDPairInjectiveSndHet cond
          eq21 = trans (fstEq eq2) $ idl c0 (pcovar i1) mcp0
          eq22 = trans (sym $ idr (pcontra i1) c1 mpc1) $ sndEq eq2
          a1 = assoc c0 c1 (pcovar i1) (qcovar $ onpos i1)
            (dcontra i1) mcp1 mc0c1
          a2 = sym $ assoc c0 c0 (pcovar i1) (qcovar $ onpos i1)
            (dcontra i1) mcp0 (cid c0)
          il1 = idl c0 (pcovar i1) mcp0
          ir1 = idr (qcontra $ onpos i1) c1
            (comp (qcontra (onpos i1)) (pcontra i1) c1 mpc1 (dcovar i1))
          a3 = assoc (qcontra (onpos i1)) (pcontra i1) c0 c1
            mc0c1 mpc0 (dcovar i1)
        in
        dpEq12
          Refl
          $ pairEqCong
            (trans a1 $ trans (rewrite il1 in rewrite eq21 in Refl) a2)
            (trans ir1 $ trans (rewrite eq22 in Refl) a3)

public export
intPDiNTvcomp :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (p, q, r : IntEndoProAr c) ->
  IntPDiNTar c mor q r -> IntPDiNTar c mor p q -> IntPDiNTar c mor p r
intPDiNTvcomp c mor comp
  (ppos ** (pcontra, pcovar))
  (qpos ** (qcontra, qcovar))
  (rpos ** (rcontra, rcovar))
  (bonpos ** (bcontra, bcovar))
  (aonpos ** (acontra, acovar)) =
    (bonpos . aonpos **
      (\i =>
        comp (pcontra i) (qcontra (aonpos i)) (rcontra (bonpos (aonpos i)))
          (bcontra (aonpos i))
          (acontra i),
       \i =>
        comp (rcovar (bonpos (aonpos i))) (qcovar (aonpos i)) (pcovar i)
          (acovar i)
          (bcovar (aonpos i))))

public export
IntHetArena : (c : Type) -> (mor : IntDifunctorSig c) -> IntEndoProAr c -> Type
IntHetArena c mor (pos ** (contra, covar)) =
  (i : pos) -> mor (covar i) (contra i)

public export
IntDiArena : (c : Type) -> (mor : IntDifunctorSig c) -> Type
IntDiArena c mor = DPair (IntEndoProAr c) (IntHetArena c mor)

public export
InterpDiArBase : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) -> IntDiArena c mor -> c -> Type
InterpDiArBase c mor comp (ar ** het) x = InterpIEPPobj c mor ar x x

public export
InterpDiArCond : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) -> (ar : IntDiArena c mor) -> (x : c) ->
  InterpDiArBase c mor comp ar x -> Type
InterpDiArCond c mor comp
  ((pos ** (contra, covar)) ** het) x (i ** (mxi, mjx)) =
    comp (covar i) x (contra i) mxi mjx = het i

public export
InterpDiAr : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) -> IntDiArena c mor -> c -> Type
InterpDiAr c mor comp ar x =
  Subset0
    (InterpDiArBase c mor comp ar x)
    (InterpDiArCond c mor comp ar x)

------------------------------------------------------
---- Profunctor categories of (diagonal) elements ----
------------------------------------------------------

PProfCatElemObj : (d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  IntProAr d c -> Type
PProfCatElemObj d c dmor cmor p =
  (x : d ** y : c ** InterpIPPobj d c dmor cmor p x y)

public export
data PProfCatElemMor :
    (d, c : Type) ->
    (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
    (dcomp : IntCompSig d dmor) -> (ccomp : IntCompSig c cmor) ->
    (p : IntProAr d c) ->
    PProfCatElemObj d c dmor cmor p -> PProfCatElemObj d c dmor cmor p -> Type
    where
  PPCEM :
    {d, c : Type} ->
    {dmor : IntDifunctorSig d} -> {cmor : IntDifunctorSig c} ->
    {dcomp : IntCompSig d dmor} -> {ccomp : IntCompSig c cmor} ->
    -- `pos`, `contra`, and `covar` together form an `IntProAr d c`.
    (pos : Type) -> (contra : pos -> d) -> (covar : pos -> c) ->
    -- `i`, `ddm`, and `cdm` together comprise a term of
    -- `InterpIPPobj d c dmor cmor (pos ** (contra, covar)) x y`;
    -- `x` and `ddm` together comprise an object of the slice category
    -- of `contra i`; `y` and `cdm` together comprise an object of
    -- the coslice category of `covar i`.  `x`, `y`, `i`, `ddm`, and `cdm`
    -- all together comprise an object of the category of elements of
    -- `(pos ** (contra, covar))`.
    (x : d) -> (y : c) ->
    (i : pos) -> (ddm : dmor x (contra i)) -> (cdm : cmor (covar i) y) ->
    -- `a` and `dmax` together form an object of the slice category of `x`.
    (a : d) -> (dmax : dmor a x) ->
    -- `b` and `cmyb` together form an object of the coslice category of `y`.
    (b : c) -> (cmyb : cmor y b) ->
    PProfCatElemMor d c dmor cmor dcomp ccomp (pos ** (contra, covar))
      (x ** y ** i ** (ddm, cdm))
      (a ** b ** i **
       (dcomp a x (contra i) ddm dmax, ccomp (covar i) y b cmyb cdm))

public export
PProfCatDiagElemObj : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntEndoProAr c -> Type
PProfCatDiagElemObj c mor p = (x : c ** InterpIEPPobj c mor p x x)

public export
data PProfCatDiagElemMor :
    (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
    (p : IntEndoProAr c) ->
    PProfCatDiagElemObj c mor p -> PProfCatDiagElemObj c mor p -> Type where
  PPCDEM :
    {c : Type} -> {mor : IntDifunctorSig c} -> {comp : IntCompSig c mor} ->
    -- `pos`, `contra`, and `covar` together form an `IntEndoProAr c`.
    (pos : Type) -> (contra : pos -> c) -> (covar : pos -> c) ->
    -- `mxy` is the morphism of the underlying category (`c`) which
    -- underlies the morphism of the category of elements.
    (x, y : c) -> (mxy : mor x y) ->
    -- `i`, `mcontra`, and `mcovar` together comprise a term of
    -- `InterpIEPPobj c mor (pos ** (contra, covar)) y x`; `y` and
    -- `mcontra` together comprise an object of the slice category of
    -- `contra i`; `x` and `mcovar` together comprise an object of the coslice
    -- category of `covar i`.
    (i : pos) -> (mcontra : mor y (contra i)) -> (mcovar : mor (covar i) x) ->
    PProfCatDiagElemMor c mor comp (pos ** (contra, covar))
      (x ** i ** (comp x y (contra i) mcontra mxy, mcovar))
      (y ** i ** (mcontra, comp (covar i) x y mxy mcovar))

------------------------------------------
------------------------------------------
---- Metalanguage polynomial functors ----
------------------------------------------
------------------------------------------

0 MLDifunctorSig : Type
MLDifunctorSig = IntDifunctorSig Type

MLPolyFObj : Type
MLPolyFObj = PolyFunc

0 MLPolyDifunctorSig : Type
MLPolyDifunctorSig = IntDifunctorSig MLPolyFObj

MLPolyFMor : MLPolyDifunctorSig
MLPolyFMor = PolyNatTrans

0 PFCopreshfSig : Type
PFCopreshfSig = IntCopreshfSig PolyFunc

0 PFCopreshfMapSig : PFCopreshfSig -> Type
PFCopreshfMapSig = IntCopreshfMapSig PolyFunc MLPolyFMor

0 PFCopreshfNTSig : (alpha, beta : PFCopreshfSig) -> Type
PFCopreshfNTSig = IntCopreshfNTSig PolyFunc

-----------------------
-----------------------
---- Apply functor ----
-----------------------
-----------------------

pfApplyArena : Type -> PolyFunc -> PolyFunc
pfApplyArena x p = pfCompositionArena p (PFConstArena x)

PFApplyType : Type -> PFCopreshfSig
PFApplyType x p = pfPos (pfApplyArena x p)

pfApplyIsConst : (x : Type) -> (p : PolyFunc) ->
  (i : PFApplyType x p) -> pfDir {p=(pfApplyArena x p)} i -> Void
pfApplyIsConst x p i (qd ** v) = void v

pfApplyToInterp : (x : Type) -> (p : PolyFunc) ->
  PFApplyType x p -> InterpPolyFunc p x
pfApplyToInterp x p = id

pfApplyFromInterp : (x : Type) -> (p : PolyFunc) ->
  InterpPolyFunc p x -> PFApplyType x p
pfApplyFromInterp x p = id

--------------------------------
--------------------------------
---- Polynomial (co-)Yoneda ----
--------------------------------
--------------------------------

--------------------------------------------
---- Polynomial double-Yoneda embedding ----
--------------------------------------------

PolyCopreshfYoEmbedObjObjMap : Type -> PFCopreshfSig
PolyCopreshfYoEmbedObjObjMap = PFApplyType

PolyCopreshfYoEmbedObjFMap :
  (x : Type) -> PFCopreshfMapSig (PolyCopreshfYoEmbedObjObjMap x)
PolyCopreshfYoEmbedObjFMap x p q alpha = InterpPolyNT {p} {q} alpha x

0 PolyCopreshfYoEmbedMor :
  (a, b : Type) -> (a -> b) ->
  PFCopreshfNTSig
    (PolyCopreshfYoEmbedObjObjMap a)
    (PolyCopreshfYoEmbedObjObjMap b)
PolyCopreshfYoEmbedMor x y f p = InterpPFMap {a=x} {b=y} p f

------------------------------------------------------
------------------------------------------------------
---- Polynomial functors over polynomial functors ----
------------------------------------------------------
------------------------------------------------------

-----------------------------------------
-----------------------------------------
---- Polynomial difunctors on `Type` ----
-----------------------------------------
-----------------------------------------

public export
SliceProfunctorSig : Type -> Type -> Type
SliceProfunctorSig x y = SliceObj x -> SliceObj y -> Type

public export
SliceEndoProfSig : Type -> Type
SliceEndoProfSig x = SliceProfunctorSig x x

public export
record DepPFpair (lpos, rpos : Type) where
  constructor DPFP
  dpfL : SlicePolyEndoFunc lpos
  dpfR : SlicePolyEndoFunc rpos

-- We may view the two components of a `DepPFpair` as a single
-- dependent polynomial functor.
public export
DepPFtoSPF : (lpos, rpos : Type) ->
  DepPFpair lpos rpos -> SlicePolyEndoFunc (Either lpos rpos)
DepPFtoSPF lpos rpos (DPFP (lpd ** ldd ** lasn) (rpd ** rdd ** rasn)) =
  (eitherElim lpd rpd **
   \(i ** id) => case i of
    Left il => ldd (il ** id)
    Right ir => rdd (ir ** id) **
   \((i ** id) ** d) => case i of
    Left il => Left $ lasn ((il ** id) ** d)
    Right ir => Right $ rasn ((ir ** id) ** d))

-- Note that the single-dependent-polynomial-functor form is more
-- general than the `DepPFpair` form, specifically because the assignment
-- morphism is not obliged to always take `Left` to `Left` and
-- `Right` to `Right`.  However, `DepPFfromSPF . DepPFtoSPF` is the identity,
-- so `DepPFtoSPF` is an (injective) embedding of `DepPFpair` into
-- `SlicePolyEndoFunc lpos rpos`.  In particular, it is a full and faithful
-- embedding into the subcategory of `SlicePolyEndoFunc lpos rpos` whose
-- assignment morphisms _do_ always take `Left` to `Left` and
-- `Right` to `Right`.
public export
DepPFfromSPF : (lpos, rpos : Type) ->
  SlicePolyEndoFunc (Either lpos rpos) -> DepPFpair lpos rpos
DepPFfromSPF lpos rpos (pd ** dd ** asn) =
  DPFP
    (pd . Left **
     \(il ** id) => dd (Left il ** id) **
     \((il ** id) ** d) => case asn ((Left il ** id) ** d) of
      Left al => al
      Right _ => il)
    (pd . Right **
     \(ir ** id) => dd (Right ir ** id) **
     \((ir ** id) ** d) => case asn ((Right ir ** id) ** d) of
      Left _ => ir
      Right ar => ar)

public export
PProAr : Type
PProAr = CoendBase DepPFpair

public export
ppaPos : PProAr -> Type
ppaPos = DPair.fst

public export
ppaDir : (p : PProAr) -> DepPFpair (ppaPos p) (ppaPos p)
ppaDir = DPair.snd

public export
ppaDirL : (p : PProAr) -> SlicePolyEndoFunc (ppaPos p)
ppaDirL p = dpfL (ppaDir p)

public export
ppaDirR : (p : PProAr) -> SlicePolyEndoFunc (ppaPos p)
ppaDirR p = dpfR (ppaDir p)

public export
InterpPPAenr : (p : PProAr) ->
  SliceObj (ppaPos p) -> SliceObj (ppaPos p) -> SliceObj (ppaPos p)
InterpPPAenr (pos ** DPFP lpoly rpoly) x y =
  SliceHom {a=pos} (InterpSPFunc lpoly x) (InterpSPFunc rpoly y)

public export
InterpPPA : (p : PProAr) -> SliceEndoProfSig (ppaPos p)
InterpPPA p x y = Pi {a=(ppaPos p)} (InterpPPAenr p x y)

public export
InterpPPAlmap : (p : PProAr) -> {a, b, c : SliceObj (ppaPos p)} ->
  SliceMorphism {a=(ppaPos p)} c a -> InterpPPA p a b -> InterpPPA p c b
InterpPPAlmap p@(pos ** DPFP lpoly rpoly) {a} {b} {c} mca pab =
  sliceComp {a=pos}
    {x=(InterpSPFunc lpoly c)}
    {y=(InterpSPFunc lpoly a)}
    {z=(InterpSPFunc rpoly b)}
    pab
    (InterpSPFMap {a=pos} {b=pos} {sa=c} {sa'=a} lpoly mca)

public export
InterpPPArmap : (p : PProAr) -> {a, b, d : SliceObj (ppaPos p)} ->
  SliceMorphism {a=(ppaPos p)} b d -> InterpPPA p a b -> InterpPPA p a d
InterpPPArmap (pos ** DPFP lpoly rpoly) {a} {b} {d} mbd pab =
  sliceComp {a=pos}
    {x=(InterpSPFunc lpoly a)}
    {y=(InterpSPFunc rpoly b)}
    {z=(InterpSPFunc rpoly d)}
    (InterpSPFMap {a=pos} {b=pos} {sa=b} {sa'=d} rpoly mbd)
    pab

public export
InterpPPAdimap : (p : PProAr) -> {a, b, c, d : SliceObj (ppaPos p)} ->
  SliceMorphism {a=(ppaPos p)} c a -> SliceMorphism {a=(ppaPos p)} b d ->
  InterpPPA p a b -> InterpPPA p c d
InterpPPAdimap p {a} {b} {c} {d} mca mbd =
  InterpPPAlmap {a} {b=d} {c} p mca . InterpPPArmap {a} {b} {d} p mbd

----------------------------------------
----------------------------------------
---- Internal polynomial difunctors ----
----------------------------------------
----------------------------------------

public export
record GenPolyRep (c : Type) where
  constructor MkGPR
  gprObj : c

public export
InterpGPRcontra : (c : Type) -> (mor : IntDifunctorSig c) ->
  GenPolyRep c -> c -> Type
InterpGPRcontra c mor (MkGPR obj) = flip mor obj

public export
InterpGPRcontramap :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (gpr : GenPolyRep c) -> IntPreshfMapSig c mor (InterpGPRcontra c mor gpr)
InterpGPRcontramap c mor comp (MkGPR obj) x y = flip $ comp y x obj

public export
GPRcontraNT : (c : Type) -> (mor : IntDifunctorSig c) ->
  GenPolyRep c -> GenPolyRep c -> Type
GPRcontraNT c mor (MkGPR obj) (MkGPR obj') = mor obj obj'

public export
InterpGPRcontraNT : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (p, q : GenPolyRep c) -> GPRcontraNT c mor p q ->
  IntPreshfNTSig c (InterpGPRcontra c mor p) (InterpGPRcontra c mor q)
InterpGPRcontraNT c mor comp (MkGPR obj) (MkGPR obj') alpha x =
  comp x obj obj' alpha

public export
InterpGPRcovar : (c : Type) -> (mor : IntDifunctorSig c) ->
  GenPolyRep c -> c -> Type
InterpGPRcovar c mor (MkGPR obj) = mor obj

public export
InterpGPRcovarmap :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (gpr : GenPolyRep c) -> IntCopreshfMapSig c mor (InterpGPRcovar c mor gpr)
InterpGPRcovarmap c mor comp (MkGPR obj) x y = comp obj x y

public export
GPRcovarNT : (c : Type) -> (mor : IntDifunctorSig c) ->
  GenPolyRep c -> GenPolyRep c -> Type
GPRcovarNT c mor (MkGPR obj) (MkGPR obj') = mor obj' obj

public export
InterpGPRcovarNT : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (p, q : GenPolyRep c) -> GPRcovarNT c mor p q ->
  IntPreshfNTSig c (InterpGPRcovar c mor p) (InterpGPRcovar c mor q)
InterpGPRcovarNT c mor comp (MkGPR obj) (MkGPR obj') alpha x =
  flip (comp obj' obj x) alpha

public export
record GenPolyRepProf (c : Type) where
  constructor MkGPRP
  gprContravar : GenPolyRep c
  gprCovar : GenPolyRep c

public export
InterpGPRPobj : (c : Type) -> (mor : IntDifunctorSig c) ->
  GenPolyRepProf c -> IntDifunctorSig c
InterpGPRPobj c mor (MkGPRP contravar covar) x y =
  (InterpGPRcontra c mor contravar x, InterpGPRcovar c mor covar y)

public export
InterpGPRPdimap :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (gprp : GenPolyRepProf c) -> IntEndoDimapSig c mor (InterpGPRPobj c mor gprp)
InterpGPRPdimap c mor comp (MkGPRP contravar covar) x y a b max myb (px, py) =
  (InterpGPRcontramap c mor comp contravar x a max px,
   InterpGPRcovarmap c mor comp covar y b myb py)

public export
GPRPnt : (c : Type) -> (mor : IntDifunctorSig c) ->
  GenPolyRepProf c -> GenPolyRepProf c -> Type
GPRPnt c mor (MkGPRP s t) (MkGPRP a b) =
  -- A generalized `Iso s t a b`.
  (GPRcontraNT c mor s a, GPRcovarNT c mor t b)

public export
InterpGPRPnt : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (p, q : GenPolyRepProf c) -> GPRPnt c mor p q ->
  IntEndoProfNTSig c (InterpGPRPobj c mor p) (InterpGPRPobj c mor q)
InterpGPRPnt c mor comp (MkGPRP s t) (MkGPRP a b) (msa, mtb) x y (msx, mty) =
  (InterpGPRcontraNT c mor comp s a msa x msx,
   InterpGPRcovarNT c mor comp t b mtb y mty)

public export
record GenPolyProf (c : Type) where
  constructor MkGPP
  gppPos : Type
  gppDir : gppPos -> GenPolyRepProf c

public export
InterpGPPobj : (c : Type) -> (mor : IntDifunctorSig c) ->
  GenPolyProf c -> IntDifunctorSig c
InterpGPPobj c mor (MkGPP pos dir) x y =
  (i : pos ** InterpGPRPobj c mor (dir i) x y)

public export
InterpGPPdimap :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (gprp : GenPolyProf c) -> IntEndoDimapSig c mor (InterpGPPobj c mor gprp)
InterpGPPdimap c mor comp (MkGPP pos dir) x y a b max myb (i ** obj) =
  (i ** InterpGPRPdimap c mor comp (dir i) x y a b max myb obj)

public export
GPPnt : (c : Type) -> (mor : IntDifunctorSig c) ->
  GenPolyProf c -> GenPolyProf c -> Type
GPPnt c mor (MkGPP pos dir) (MkGPP pos' dir') =
  (onpos : pos -> pos' ** (i : pos) -> GPRPnt c mor (dir i) (dir' $ onpos i))

public export
InterpGPPnt : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (p, q : GenPolyProf c) -> GPPnt c mor p q ->
  IntEndoProfNTSig c (InterpGPPobj c mor p) (InterpGPPobj c mor q)
InterpGPPnt c mor comp (MkGPP pos dir) (MkGPP pos' dir') (onpos ** ondir) x y
  (i ** z) =
    (onpos i **
     InterpGPRPnt c mor comp (dir i) (dir' $ onpos i) (ondir i) x y z)

------------------------------------------------------------------------
------------------------------------------------------------------------
---- Internal Pro-Yoneda (simultaneous covariant and contravariant) ----
------------------------------------------------------------------------
------------------------------------------------------------------------

-- This is the internal generalization (it is a generalization because
-- `Type` is internal to `Type`) of`PrePostPair`.  As such, it is the
-- (covariant) Yoneda embedding of `(op(d), c)` into the category of
-- `Type`-internal profunctors ("prosheaves") `op(d) -> c -> Type`.
-- That is, `IntProfYonedaEmbed d c dmor cmor s t` is `Hom((s, t), (-, _))`.
public export
IntProfYonedaEmbed : (0 d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  d -> c -> IntProfunctorSig d c
IntProfYonedaEmbed d c dmor cmor s t a b = (dmor a s, cmor t b)

public export
IntProfYonedaEmbedDimap : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  (dcomp : IntCompSig d dmor) -> (ccomp : IntCompSig c cmor) ->
  (s : d) -> (t : c) ->
  IntDimapSig d c dmor cmor (IntProfYonedaEmbed d c dmor cmor s t)
IntProfYonedaEmbedDimap d c dmor cmor dcomp ccomp s t a b i j
  dmia cmbj (dmas, cmtb) = (dcomp i a s dmas dmia, ccomp t b j cmbj cmtb)

-------------------------------------------------------------------------
-------------------------------------------------------------------------
---- Pro-Yoneda (simultaneous covariant and contravariant) on `Type` ----
-------------------------------------------------------------------------
-------------------------------------------------------------------------

-- `ProfYonedaEmbed` embeds the object `(i0, i1)` of `(op(Type), Type)` into
-- the category whose objects are profunctors `(op(Type), Type) -> Type)` and
-- whose morphisms are natural transformations.
--
-- Note that `ProfYonedaEmbed Unit b` is the profunctor which ignores its
-- first argument and acts as `CovarHomFunc b` on its second argument, whereas
-- `ProfYonedaEmbed a Void` is the profunctor which ignores its second argument
-- and acts as `ContravarHomFunc a` on its first argument.
public export
ProfYonedaEmbed : Type -> Type -> ProfunctorSig
ProfYonedaEmbed = IntProfYonedaEmbed Type Type HomProf HomProf

public export
ProfYonedaEmbedProf : Profunctor (PrePostPair s t)
ProfYonedaEmbedProf = PrePostPairProf

-- The Yoneda lemma asserts a natural isomorphism between two objects
-- of the enriching category, one of which is an object of natural
-- transformations.  This type is an explicit name for that object on
-- the category `(op(Type), Type)`.  An analogous type is called
-- `Yoneda/runYoneda` in some Haskell libraries, where it is referred
-- to as "the cofree profunctor".
public export
ProfYonedaLemmaNT : ProfunctorSig -> ProfunctorSig
ProfYonedaLemmaNT p c d = ProfNT (ProfYonedaEmbed c d) p

public export
Profunctor (ProfYonedaLemmaNT p) where
  dimap {a} {b} {c} {d} mca mbd alpha (mac, mdb) = alpha (mca . mac, mdb . mbd)

-- One direction of the natural isomorphism asserted by the Yoneda lemma
-- on `(op(Type), Type)`.  This is called `toProYo` in another context.
public export
ProfYonedaLemmaL : (0 p : ProfunctorSig) -> {auto isP : Profunctor p} ->
  ProfNT p (ProfYonedaLemmaNT p)
ProfYonedaLemmaL p {isP} {a=i} {b=j} pij {a} {b} (mai, mjb) =
  dimap {f=p} {a=i} {b=j} {c=a} {d=b} mai mjb pij

-- The other direction of the natural isomorphism asserted by the Yoneda lemma
-- on `(op(Type), Type)`.  This is called `fromProYo` in another context.
public export
ProfYonedaLemmaR : (0 p : ProfunctorSig) ->
  ProfNT (ProfYonedaLemmaNT p) p
ProfYonedaLemmaR p dyembed {a=i} {b=j} = dyembed (id {a=i}, id {a=j})

-- The co-Yoneda lemma asserts a natural isomorphism between two objects
-- of the enriching category, one of which is a coend (existential type).
-- This type is an explicit name for that object on the category
-- `(op(Type), Type)`.  An analogous type is called `CoYoneda` in some
-- Haskell libraries.  It is the existential dual of `ProfYonedaLemmaNT`
-- (the "cofree profunctor").
public export
ProfCoYonedaLemmaCoend : ProfunctorSig -> ProfunctorSig
ProfCoYonedaLemmaCoend p c d =
  Exists {type=(Type, Type)} $
    \ab => (ProfYonedaEmbed d c (snd ab) (fst ab), p (fst ab) (snd ab))

public export
Profunctor (ProfCoYonedaLemmaCoend p) where
  dimap {a} {b} {c} {d} mca mbd (Evidence ij ((mjb, mai), pij)) =
    Evidence ij ((mbd . mjb, mai . mca), pij)

-- One direction of the natural isomorphism asserted by the co-Yoneda lemma
-- on `(op(Type), Type)`.  This is called `toCoProYo` in another context.
public export
ProfCoYonedaLemmaL : (0 p : ProfunctorSig) ->
  ProfNT p (ProfCoYonedaLemmaCoend p)
ProfCoYonedaLemmaL p {a} {b} pab = Evidence (a, b) ((id {a=b}, id {a}), pab)

-- One direction of the natural isomorphism asserted by the co-Yoneda lemma
-- on `(op(Type), Type)`.  This is called `fromCoProYo` in another context.
public export
ProfCoYonedaLemmaR : (0 p : ProfunctorSig) -> {auto isP : Profunctor p} ->
  ProfNT (ProfCoYonedaLemmaCoend p) p
ProfCoYonedaLemmaR p {isP} {a=c} {b=d} (Evidence ab ((mbd, mca), pab)) =
  dimap {f=p} mca mbd pab

---------------------------------------------
---------------------------------------------
---- Exponentials in presheaf categories ----
---------------------------------------------
---------------------------------------------

-- See for example
-- https://math.stackexchange.com/questions/2402394/exponential-of-presheaves.

public export
0 IntPreshfHomObjOmap : (c : Type) -> (mor : IntDifunctorSig c) ->
  (xomap, yomap : c -> Type) ->
  (xfmap : IntPreshfMapSig c mor xomap) ->
  (yfmap : IntPreshfMapSig c mor yomap) ->
  c -> Type
IntPreshfHomObjOmap c mor xomap yomap xfmap yfmap a =
  ?IntPreshfHomObjOmap_hole

public export
0 IntPreshfHomObjFmap : (c : Type) -> (mor : IntDifunctorSig c) ->
  (xomap, yomap : c -> Type) ->
  (xfmap : IntPreshfMapSig c mor xomap) ->
  (yfmap : IntPreshfMapSig c mor yomap) ->
  IntPreshfMapSig c mor (IntPreshfHomObjOmap c mor xomap yomap xfmap yfmap)
IntPreshfHomObjFmap c mor xomap yomap xfmap yfmap a b mba =
  ?IntPreshfHomObjFmap_hole

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
---- Yoneda embedding of twisted-arrow category into profunctor category ----
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

public export
ArrEmbedObjDom : ArrObj -> Type
ArrEmbedObjDom ((a, b) ** mab) = a

public export
ArrEmbedObjCod : ArrObj -> Type
ArrEmbedObjCod ((a, b) ** mab) = b

public export
ArrEmbedObjObj : ArrObj -> (Type, Type)
ArrEmbedObjObj arr = (ArrEmbedObjDom arr, ArrEmbedObjCod arr)

public export
ArrEmbedObjProf : ArrObj -> ProfunctorSig
ArrEmbedObjProf arr = PrePostPair (ArrEmbedObjDom arr) (ArrEmbedObjCod arr)

public export
ArrDiEmbedObjProf : ArrObj -> ProfunctorSig
ArrDiEmbedObjProf arr = DiYonedaEmbed (ArrEmbedObjDom arr) (ArrEmbedObjCod arr)

public export
ArrEmbedObjProfNT : ArrObj -> Type
ArrEmbedObjProfNT arr = ProfNT (ArrEmbedObjProf arr) HomProf

public export
ArrDiEmbedObjProfNT : ArrObj -> Type
ArrDiEmbedObjProfNT arr = ProfDiNT (ArrDiEmbedObjProf arr) HomProf

public export
ArrEmbedObjMorph : (arr : ArrObj) -> ArrEmbedObjProfNT arr
ArrEmbedObjMorph ((a, b) ** mab) {a=s} {b=t} (msa, mbt) = mbt . mab . msa

public export
ArrDiEmbedObjMorph : (arr : ArrObj) -> ArrDiEmbedObjProfNT arr
ArrDiEmbedObjMorph ((a, b) ** mab) x (msa, mbt) = id {a=x}

public export
TwistArrEmbedObjDom : TwistArrObj -> Type
TwistArrEmbedObjDom = ArrEmbedObjDom

public export
TwistArrEmbedObjCod : TwistArrObj -> Type
TwistArrEmbedObjCod = ArrEmbedObjCod

public export
TwistArrEmbedObjObj : TwistArrObj -> (Type, Type)
TwistArrEmbedObjObj = ArrEmbedObjObj

public export
TwistArrEmbedObjProf : TwistArrObj -> ProfunctorSig
TwistArrEmbedObjProf = ArrEmbedObjProf

public export
TwistArrDiEmbedObjProf : TwistArrObj -> ProfunctorSig
TwistArrDiEmbedObjProf = ArrDiEmbedObjProf

public export
TwistArrEmbedObjProfNT : TwistArrObj -> Type
TwistArrEmbedObjProfNT = ArrEmbedObjProfNT

public export
TwistArrDiEmbedObjProfNT : TwistArrObj -> Type
TwistArrDiEmbedObjProfNT = ArrDiEmbedObjProfNT

public export
TwistArrEmbedObjMorph : (arr : TwistArrObj) -> TwistArrEmbedObjProfNT arr
TwistArrEmbedObjMorph = ArrEmbedObjMorph

public export
TwistArrDiEmbedObjMorph : (arr : TwistArrObj) -> TwistArrDiEmbedObjProfNT arr
TwistArrDiEmbedObjMorph = ArrDiEmbedObjMorph

public export
ProfNTMorph : (p, q, r : ProfunctorSig) ->
  ProfNT p r -> ProfNT q r -> Type
ProfNTMorph p q r pnt qnt =
  (x : Type ** y : Type ** pxy : p x y ** qxy : q x y **
   FunExt -> pnt pxy = qnt qxy)

public export
ProfDiNTMorph : (p, q, r : ProfunctorSig) ->
  ProfDiNT p r -> ProfDiNT q r -> Type
ProfDiNTMorph p q r pnt qnt =
  (x : Type ** pxx : p x x ** qxx : q x x ** pnt x pxx = qnt x qxx)

public export
TwistArrEmbedMorph : (arr, arr' : TwistArrObj) ->
  TwistArrMorph arr arr' ->
  ProfNTMorph
    (TwistArrEmbedObjProf arr)
    (TwistArrEmbedObjProf arr')
    HomProf
    (TwistArrEmbedObjMorph arr)
    (TwistArrEmbedObjMorph arr')
TwistArrEmbedMorph
  ((a, b) ** mab) ((a', b') ** ma'b') (Element0 (ma'a, mbb') comm) =
    -- This doesn't look right -- neither `mab` nor `ma'b'` are used.
    (a' ** b' ** (ma'a, mbb') ** (id {a=a'}, id {a=b'}) **
     \funext => funExt $ \ea' => sym $ comm ea')

public export
0 TwistArrEmbedMorphInv : (arr, arr' : TwistArrObj) ->
  ProfNTMorph
    (TwistArrEmbedObjProf arr)
    (TwistArrEmbedObjProf arr')
    HomProf
    (TwistArrEmbedObjMorph arr)
    (TwistArrEmbedObjMorph arr') ->
  TwistArrMorph arr arr'
TwistArrEmbedMorphInv
  ((a, b) ** mab) ((a', b') ** ma'b')
  (x ** y ** (mxa, mby) ** (mxa', mb'y) ** comm) =
    ?TwistArrEmbedMorphInv_hole

public export
TwistArrDiEmbedMorph : (arr, arr' : TwistArrObj) ->
  TwistArrMorph arr arr' ->
  ProfDiNTMorph
    (TwistArrDiEmbedObjProf arr)
    (TwistArrDiEmbedObjProf arr')
    HomProf
    (TwistArrDiEmbedObjMorph arr)
    (TwistArrDiEmbedObjMorph arr')
TwistArrDiEmbedMorph
  ((a, b) ** mab) ((a', b') ** ma'b') (Element0 (ma'a, mbb') comm) =
    -- `ma'b'` isn't used, but that's because "comm" tells us that
    -- it's redundant -- it's determined by the other three morphisms.
    (a ** (mab, id {a}) ** (mbb' . mab, ma'a) ** Refl)

public export
0 TwistArrDiEmbedMorphInv : (arr, arr' : TwistArrObj) ->
  ProfDiNTMorph
    (TwistArrDiEmbedObjProf arr)
    (TwistArrDiEmbedObjProf arr')
    HomProf
    (TwistArrDiEmbedObjMorph arr)
    (TwistArrDiEmbedObjMorph arr') ->
  TwistArrMorph arr arr'
TwistArrDiEmbedMorphInv
  ((a, b) ** mab) ((a', b') ** ma'b')
  (x ** (mxb, max) ** (mxb', ma'x) ** comm) =
    Element0 (?ma'a_hole, ?mbb'_hole) $ ?TwistArrDiEmbedMorphInv_hole

--------------------------------------------------------
---- Double-Yoneda on `Type` (functor polymorphism) ----
--------------------------------------------------------

-- The signature of the object-map component of a (co)presheaf on the category
-- of endofunctors on `Type`.
public export
0 FuncCopreshfObj : Type
FuncCopreshfObj = (Type -> Type) -> Type

-- The signature of the morphism-map component of a `FuncCopreshfObj` (since
-- such an object is itself a functor).
public export
0 FuncCopreshfObjFMapSig : FuncCopreshfObj -> Type
FuncCopreshfObjFMapSig fp =
  (0 f, g : Type -> Type) -> NaturalTransformation f g -> fp f -> fp g

-- The identity-preserving condition on the morphism-map component of a
-- `FuncCopreshfObj` (since such an object is itself a functor).
public export
0 FuncCopreshfObjFMapIdCond :
  (fp : FuncCopreshfObj) -> FuncCopreshfObjFMapSig fp -> Type
FuncCopreshfObjFMapIdCond fp fpm =
  (0 f : Type -> Type) -> ExtEq (fpm f f (IdNT f)) (id {a=(fp f)})

public export
0 TypeFMapSig : (Type -> Type) -> Type
TypeFMapSig = IntCopreshfMapSig Type HomProf

public export
0 TypeFMapIdCond : (0 f : Type -> Type) -> TypeFMapSig f -> Type
TypeFMapIdCond f fm = (0 x : Type) -> ExtEq (fm x x (id {a=x})) (id {a=(f x)})

public export
0 TypeNaturality : (0 f, g : Type -> Type) ->
  (0 fm : TypeFMapSig f) -> (0 gm : TypeFMapSig g) ->
  NaturalTransformation f g -> Type
TypeNaturality f g fm gm nu = (0 a, b : Type) -> (0 m : a -> b) ->
  ExtEq {a=(f a)} {b=(g b)} (gm a b m . nu a) (nu b . fm a b m)

-- A morphism in the category of (co)presheaves on the category of
-- endofunctors on `Type` is a natural transformation, because the
-- objects of that category are functors (whose domain is the category
-- of endofunctors on `Type`, and whose codomain is `Type`).
public export
0 FuncCopreshfMorphBase : FuncCopreshfObj -> FuncCopreshfObj -> Type
FuncCopreshfMorphBase fp gp =
  (0 f : Type -> Type) -> (fm : TypeFMapSig f) -> fp f -> gp f

public export
0 FuncCopreshfMorphBaseEq : (0 fp, gp : FuncCopreshfObj) ->
  (m, m' : FuncCopreshfMorphBase fp gp) -> Type
FuncCopreshfMorphBaseEq fp gp m m' =
  (0 f : Type -> Type) -> (0 fm : TypeFMapSig f) ->
  TypeFMapIdCond f fm ->
  ExtEq {a=(fp f)} {b=(gp f)} (m f fm) (m' f fm)

public export
0 FuncCopreshfMorphNaturality :
  (0 fp, gp : FuncCopreshfObj) ->
  (0 fpm : FuncCopreshfObjFMapSig fp) ->
  (0 gpm : FuncCopreshfObjFMapSig gp) ->
  FuncCopreshfMorphBase fp gp -> Type
FuncCopreshfMorphNaturality fp gp fpm gpm alpha =
  (0 f, g : Type -> Type) ->
  (0 fm : TypeFMapSig f) -> (0 gm : TypeFMapSig g) ->
  (0 nu : NaturalTransformation f g) ->
  TypeNaturality f g fm gm nu ->
  ExtEq {a=(fp f)} {b=(gp g)}
    (alpha g gm . fpm f g nu)
    (gpm f g nu . alpha f fm)

public export
0 FuncCopreshfMorph :
  (0 fp, gp : FuncCopreshfObj) ->
  (0 fpm : FuncCopreshfObjFMapSig fp) ->
  (0 gpm : FuncCopreshfObjFMapSig gp) ->
  Type
FuncCopreshfMorph fp gp fpm gpm =
  Subset0
    (FuncCopreshfMorphBase fp gp)
    (FuncCopreshfMorphNaturality fp gp fpm gpm)

public export
0 FuncCopreshfMorphEq :
  (0 fp, gp : FuncCopreshfObj) ->
  (0 fpm : FuncCopreshfObjFMapSig fp) ->
  (0 gpm : FuncCopreshfObjFMapSig gp) ->
  (0 nu, nu' : FuncCopreshfMorph fp gp fpm gpm) ->
  Type
FuncCopreshfMorphEq fp gp fpm gpm nu nu' =
  FuncCopreshfMorphBaseEq fp gp (Subset0.fst0 nu) (Subset0.fst0 nu')

-- `fapply x` is the object-map component of a functor on functors that
-- applies a functor to `x`.
public export
fapply : Type -> FuncCopreshfObj
fapply x f = f x

-- `fapply x` is the morphism-map component of a functor on functors that
-- applies a functor to `x`.
public export
fapplym : (x : Type) -> FuncCopreshfObjFMapSig (fapply x)
fapplym x f g alpha fx = alpha x fx

public export
fapplymIdCond : (x : Type) -> FuncCopreshfObjFMapIdCond (fapply x) (fapplym x)
fapplymIdCond x f elfx = Refl

-- `fapply` and `fapplym` together form the object-map component of
-- an embedding of `Type` into the category of (co)presheaves on the
-- category of endofunctors on `Type` (such an embedding is a functor
-- from `Type` to `FuncCopreshfObj/FuncCopreshfObjFMapSig`).  We now define
-- the morphism-map component of that embedding (`fapplyNT`).
public export
fapplyNTBase : (x, y : Type) -> (x -> y) ->
  FuncCopreshfMorphBase (fapply x) (fapply y)
fapplyNTBase x y m f fm = fm x y m

public export
0 fapplyNTnaturality : (x, y : Type) -> (m : x -> y) ->
  FuncCopreshfMorphNaturality
    (fapply x) (fapply y) (fapplym x) (fapplym y) (fapplyNTBase x y m)
fapplyNTnaturality x y m f g fm gm nu nunat = nunat x y m

public export
fapplyNT : (x, y : Type) -> (x -> y) ->
  FuncCopreshfMorph (fapply x) (fapply y) (fapplym x) (fapplym y)
fapplyNT x y m = Element0 (fapplyNTBase x y m) (fapplyNTnaturality x y m)

-- `fapply(m)/fapplyNT` form an embedding of `Type` into
-- `FuncCopreshf(Obj/Morph)`.  We now show as much as we can within Idris
-- of a proof that `fapplyNT` has an inverse, hence is bijective, which
-- means that that embedding is full and faithful.
public export
fapplyNTinv : (x, y : Type) ->
  FuncCopreshfMorph (fapply x) (fapply y) (fapplym x) (fapplym y) ->
  (x -> y)
fapplyNTinv x y (Element0 nu nat) =
  nu (id {a=Type}) $ \a, b => id {a=(a -> b)}

public export
0 fapplyNTinvRthenL : (x, y : Type) -> (m : x -> y) ->
  ExtEq (fapplyNTinv x y (fapplyNT x y m)) m
fapplyNTinvRthenL x y m elx = Refl

-- We can not actually prove this theorem in Idris, because Idris doesn't
-- know the rules of its own type system.  Proving this would amount to
-- proving the double-Yoneda lemma on Idris's type system.
public export
0 FapplyNTinvLthenRcond : Type
FapplyNTinvLthenRcond =
  (x, y : Type) ->
  (m : FuncCopreshfMorph (fapply x) (fapply y) (fapplym x) (fapplym y)) ->
  FuncCopreshfMorphEq (fapply x) (fapply y) (fapplym x) (fapplym y)
    (fapplyNT x y (fapplyNTinv x y m)) m

-------------------------------------------------------------------------------
---- Double-pro-/di-Yoneda on `Type` (profunctor paranatural polymorphism) ----
-------------------------------------------------------------------------------

-- The signature of a (co)presheaf on the category of endoprofunctors
-- on `Type`.
public export
0 ProfCopreshfObj : Type
ProfCopreshfObj = ProfunctorSig -> Type

-- The signature of the morphism-map component of a `ProfCopreshfObj` (since
-- such an object is itself a functor), when the copresheaf's domain is the
-- category of endoprofunctors with natural transformations.
public export
0 ProfCopreshfObjFMapSig : ProfCopreshfObj -> Type
ProfCopreshfObjFMapSig pp =
  (0 p, q : ProfunctorSig) -> ProfNT p q -> pp p -> pp q

-- The signature of the morphism-map component of a `ProfCopreshfObj` (since
-- such an object is itself a functor), when the copresheaf's domain is the
-- category of endoprofunctors with _paranatural_ transformations.
public export
0 ParaCopreshfObjFMapSig : ProfCopreshfObj -> Type
ParaCopreshfObjFMapSig pp =
  (0 p, q : ProfunctorSig) -> ProfDiNT p q -> pp p -> pp q

public export
0 TypeDimapSig : (0 _ : Type -> Type -> Type) -> Type
TypeDimapSig p = IntEndoDimapSig Type HomProf p

public export
0 TypeLmapSig : (0 _ : Type -> Type -> Type) -> Type
TypeLmapSig p = IntEndoLmapSig Type HomProf p

public export
0 TypeRmapSig : (0 _ : Type -> Type -> Type) -> Type
TypeRmapSig p = IntEndoRmapSig Type HomProf p

public export
0 TypeDimapFromLR : (p : ProfunctorSig) ->
  TypeLmapSig p -> TypeRmapSig p -> TypeDimapSig p
TypeDimapFromLR p = IntEndoDimapFromLRmaps Type HomProf p

public export
0 ProfNaturality : (0 p, q : ProfunctorSig) ->
  (0 pdm : TypeDimapSig p) -> (0 qdm : TypeDimapSig q) ->
  ProfNT p q -> Type
ProfNaturality p q pdm qdm alpha =
  IntProfNTNaturality Type Type HomProf HomProf p q pdm qdm $ \_, _ => alpha

public export
0 ProfParanaturality : (0 p, q : ProfunctorSig) ->
  (0 plm : TypeLmapSig p) -> (0 prm : TypeRmapSig p) ->
  (0 qlm : TypeLmapSig q) -> (0 qrm : TypeRmapSig q) ->
  ProfDiNT p q -> Type
ProfParanaturality p q plm prm qlm qrm =
  IntParaNTCond Type HomProf p q plm prm qlm qrm

-- A morphism in the category of (co)presheaves on the category of
-- difunctors on `Type` is a natural transformation, because the
-- objects of that category are functors (whose domain is the category
-- of difunctors on `Type`, and whose codomain is `Type`).
public export
0 ProfCopreshfMorphBase : ProfCopreshfObj -> ProfCopreshfObj -> Type
ProfCopreshfMorphBase pp qp =
  (0 p : ProfunctorSig) -> (dm : TypeDimapSig p) -> pp p -> qp p

public export
0 ProfCopreshfMorphNaturality :
  (0 pp, qp : ProfCopreshfObj) ->
  (0 pdm : ProfCopreshfObjFMapSig pp) ->
  (0 qdm : ProfCopreshfObjFMapSig qp) ->
  ProfCopreshfMorphBase pp qp -> Type
ProfCopreshfMorphNaturality pp qp ppdm qpdm alpha =
  (0 p, q : ProfunctorSig) ->
  (0 pdm : TypeDimapSig p) -> (0 qdm : TypeDimapSig q) ->
  (0 nu : ProfNT p q) ->
  ProfNaturality p q pdm qdm nu ->
  ExtEq {a=(pp p)} {b=(qp q)}
    (alpha q qdm . ppdm p q nu)
    (qpdm p q nu . alpha p pdm)

public export
0 ParaCopreshfMorphNaturality :
  (0 pp, qp : ProfCopreshfObj) ->
  (0 pdm : ParaCopreshfObjFMapSig pp) ->
  (0 qdm : ParaCopreshfObjFMapSig qp) ->
  ProfCopreshfMorphBase pp qp -> Type
ParaCopreshfMorphNaturality pp qp ppdm qpdm alpha =
  (0 p, q : ProfunctorSig) ->
  (0 plm : TypeLmapSig p) -> (0 prm : TypeRmapSig p) ->
  (0 qlm : TypeLmapSig q) -> (0 qrm : TypeRmapSig q) ->
  (0 nu : ProfDiNT p q) ->
  ProfParanaturality p q plm prm qlm qrm nu ->
  ExtEq {a=(pp p)} {b=(qp q)}
    (alpha q (TypeDimapFromLR q qlm qrm) . ppdm p q nu)
    (qpdm p q nu . alpha p (TypeDimapFromLR p plm prm))

public export
0 ProfCopreshfMorph :
  (0 pp, qp : ProfCopreshfObj) ->
  (0 pdm : ProfCopreshfObjFMapSig pp) ->
  (0 qdm : ProfCopreshfObjFMapSig qp) ->
  Type
ProfCopreshfMorph pp qp pdm qdm =
  Subset0
    (ProfCopreshfMorphBase pp qp)
    (ProfCopreshfMorphNaturality pp qp pdm qdm)

public export
0 ParaCopreshfMorph :
  (0 pp, qp : ProfCopreshfObj) ->
  (0 pdm : ParaCopreshfObjFMapSig pp) ->
  (0 qdm : ParaCopreshfObjFMapSig qp) ->
  Type
ParaCopreshfMorph pp qp pdm qdm =
  Subset0
    (ProfCopreshfMorphBase pp qp)
    (ParaCopreshfMorphNaturality pp qp pdm qdm)

-- `profapply x y` is the object-map component of a functor on difunctors that
-- applies a difunctor to `x` and `y`.
public export
profapply : Type -> Type -> ProfCopreshfObj
profapply x y p = p x y

-- `profapplym x y` is the morphism-map component of a functor on difunctors
-- that applies a difunctor to `x` and `y`.
public export
profapplym : (x, y : Type) -> ProfCopreshfObjFMapSig (profapply x y)
profapplym x y p q alpha pxy = alpha pxy

-- `diapply x` is the object-map component of a functor on difunctors that
-- applies a difunctor to `x` and `x`.
public export
diapply : Type -> ProfCopreshfObj
diapply x = profapply x x

-- `diapplym x` is the morphism-map component of a functor on difunctors
-- that applies a difunctor to `x` and `x`.
public export
diapplym : (x : Type) -> ParaCopreshfObjFMapSig (diapply x)
diapplym x p q alpha pxx = alpha x pxx

-- `profapply` and `profapplym` together form the object-map component of
-- an embedding of `(op(Type), Type)` into the category of (co)presheaves on the
-- category of difunctors on `Type` with natural transformations (such an
-- embedding is a functor from `(op(Type), Type)` to
-- `ProfCopreshfObj/ProfCopreshfObjFMapSig`).  We now define the morphism-map
-- component of that embedding (`profapplyNT`).
public export
profapplyNTBase : (s, t, a, b : Type) -> (a -> s) -> (t -> b) ->
  ProfCopreshfMorphBase (profapply s t) (profapply a b)
profapplyNTBase s t a b mas mtb p pdm pst = pdm s t a b mas mtb pst

-- `diapply` and `diapplym` together form the object-map component of
-- an embedding of `Type` into the category of (co)presheaves on the
-- category of difunctors on `Type` with paranatural transformations (such
-- an embedding is a functor from `Type` to
-- `ProfCopreshfObj/ParaCopreshfObjFMapSig`).  We now define the morphism-map
-- component of that embedding (`diapplyNT`).
public export
0 diapplyNTBase : (x, y : Type) -> (x -> y) ->
  ProfCopreshfMorphBase (diapply x) (diapply y)
diapplyNTBase x y m p pdm pxx = let pdmxy = pdm x x y y in ?diapplyNTBase_hole

-- The signature of an endprofunctor/difunctor/prosheaf (we'll use any
-- one of those names to mean the same thing, depending on the context) on
-- the category of endoprofunctors on `Type`.
public export
0 ProfProshfObj : Type
ProfProshfObj = ProfunctorSig -> ProfunctorSig -> Type

public export
0 ProfProshfMorph : ProfProshfObj -> ProfProshfObj -> Type
ProfProshfMorph pp pp' = (0 p, q : ProfunctorSig) -> pp p q -> pp' p q

public export
profappnt : Type -> Type -> ProfProshfObj
profappnt x y p q = profapply x y p -> profapply x y q

public export
diappnt : Type -> ProfProshfObj
diappnt x = profappnt x x

--------------------------------
--------------------------------
---- Categories of elements ----
--------------------------------
--------------------------------

---------------------------------------------------------------------
---- Categories of structures / diagonal elements of profunctors ----
---------------------------------------------------------------------

-- The category of diagonal elements of `p` is also called the category of
-- `p`-structures.  See https://arxiv.org/abs/2307.09289.
--
-- Note that if `p : ProfunctorSig` is `DiYonedaEmbed i j` for
-- some `i, j : Type`, then `ProfCatDiagElemObj p` is
-- `(a : Type ** (i -> a, a -> j))`, which is precisely the definition of
-- a splice object between `i` and `j` (i.e. an object of the category
-- `i/Type/j`).
--
-- If `p` is `DiYonedaEmbed Void j` for some `j : Type`, then
-- `p` is naturally isomorphic to `ContravarHomFunc j`, and
-- `ProfCatDiagElemObj p` is isomorphic to `SliceObj j`.
--
-- If `p` is `DiYonedaEmbed i Unit` for some `i : Type`, then
-- `p` is naturally isomorphic to `CovarHomFunc i`, and
-- `ProfCatDiagElemObj p` is isomorphic to `CosliceObj i`.
public export
ProfCatDiagElemObj : ProfunctorSig -> Type
ProfCatDiagElemObj = CoendBase -- (a : Type ** p a a)

-- Note that if `p : ProfunctorSig` is `DiYonedaEmbed i j` for
-- some `i, j : Type`, and `spl` and `spl'` are morphisms of the
-- splice category `i/Type/j`, then `ProfCatDiagElemDomMorph {p} spl spl'` is
-- the signature of the morphism underlying a splice morphism from
-- `spl` to `spl'` (without the commutativity condition).
public export
ProfCatDiagElemDomMorph : {0 p : ProfunctorSig} ->
  ProfCatDiagElemObj p -> ProfCatDiagElemObj p -> Type
ProfCatDiagElemDomMorph {p} paa pbb = fst paa -> fst pbb

-- Note that if `p : ProfunctorSig` is `DiYonedaEmbed i j` for
-- some `i, j : Type`, and `spl` and `spl'` are morphisms of the
-- splice category `i/Type/j`, and `m` has the signature of a morphism
-- underlying a splice morphism from `spl` to `spl'` in `i/Type/j`,
-- then `ProfCatDiagElemDomMorph {p} spl spl' m` is
-- precisely the commutativity condition for `m` to constitute a
-- splice morphism (from `spl` to `spl'`):  it asserts the equality of
-- a pair of pairs of morphisms, and hence, equivalently, a pair of
-- equalities of morphisms, where each equality is the commutativity
-- condition for one of the two triangles in the splice-morphism diagram.
public export
0 ProfCatDiagElemCommutes : {0 p : ProfunctorSig} -> {0 isP : Profunctor p} ->
  {paa, pbb : ProfCatDiagElemObj p} ->
  ProfCatDiagElemDomMorph {p} paa pbb -> Type
ProfCatDiagElemCommutes {p} {isP} {paa} {pbb} mab =
  rmap {f=p} mab (snd paa) = lmap {f=p} mab (snd pbb)

-- As a consequence of the previous notes,
-- `ProfCatDiagElemMorph {p=(DiYonedaEmbed i j)} spl spl'`
-- is precisely the type of splice morphisms from `spl` to `spl'`.
-- Hence the category of diagonal elements of `DiYonedaEmbed i j` is
-- equivalent to the splice category `i/Type/j`.
public export
ProfCatDiagElemMorph : {0 p : ProfunctorSig} -> {0 isP : Profunctor p} ->
  ProfCatDiagElemObj p -> ProfCatDiagElemObj p -> Type
ProfCatDiagElemMorph {p} {isP} paa pbb =
  Subset0
    (ProfCatDiagElemDomMorph {p} paa pbb)
    (ProfCatDiagElemCommutes {p} {isP} {paa} {pbb})

-----------------------------------------------
---- Categories of elements of profunctors ----
-----------------------------------------------

-- A profunctor `Type -> Type` is a functor `op(Type) -> Type -> Type`,
-- so its category of elements consists of objects of `(op(Type), Type)`
-- together with elements of the profunctor applied to them.
--
-- Note that a covariant functor `Type -> Type` is a special case of a
-- profunctor which ignores its first argument, and a contravariant functor
-- `op(Type) -> Type` is a special case of a profunctor which ignores its
-- second argument.  In particular, a covariant representable
-- `p _ x = CovarHom i x` has the coslice category
-- `i/Type` as its category of elements, and a contravariant representable
-- `p x _ = ContravarHom j x` has the slice category `Type/j` as its
-- category of elements.  The hom-profunctor has the twisted-arrow category as
-- its category of elements.
--
-- The contravariant profunctor `SliceObj` has as its category of elements
-- the category of polynomial endofunctors on `Type`.  Dually, the covariant
-- profunctor `CosliceObj` has as its category of elements the category of
-- Dirichlet endofunctors on `Type`.  Those categories have the same objects,
-- which correspond to the "arenas" of such endofunctors (that is why the
-- same data determine polynomial endofunctors and Dirichlet endofunctors),
-- but different morphisms (meaning that polynomial endofunctors and Dirichlet
-- endofunctors have different natural transformations for the same arenas).
public export
ProfCatElemObj : ProfunctorSig -> Type
ProfCatElemObj p = (ab : (Type, Type) ** p (fst ab) (snd ab))

-- Because the domain of an endo-profunctor on `Type` is `(op(Type), Type)`,
-- the morphism component of a morphism in its category of elements is a
-- morphism in `(op(Type), Type)`, which is a `PrePostPair`.
--
-- (Besides a morphism in the functor's domain, a morphism in the category of
-- elements also has an equality/commutativity component.)
public export
ProfCatElemDomMorph : {0 p : ProfunctorSig} ->
  ProfCatElemObj p -> ProfCatElemObj p -> Type
ProfCatElemDomMorph {p} pab pcd =
  PrePostPair (fst (fst pab)) (snd (fst pab)) (fst (fst pcd)) (snd (fst pcd))

public export
0 ProfCatElemCommutes : {0 p : ProfunctorSig} -> {0 isP : Profunctor p} ->
  (pab, pcd : ProfCatElemObj p) -> ProfCatElemDomMorph {p} pab pcd -> Type
ProfCatElemCommutes {p} {isP} pab pcd mcabd =
  dimap {f=p} (fst mcabd) (snd mcabd) (snd pab) = snd pcd

public export
ProfCatElemMorph : {0 p : ProfunctorSig} -> {0 isP : Profunctor p} ->
  ProfCatElemObj p -> ProfCatElemObj p -> Type
ProfCatElemMorph {p} {isP} pab pcd =
  Subset0
    (ProfCatElemDomMorph {p} pab pcd)
    (ProfCatElemCommutes {p} {isP} pab pcd)

-------------------------------
-------------------------------
---- Algebraic interfaces -----
-------------------------------
-------------------------------

---------------------------------
---- Empty/uninhabited types ----
---------------------------------

-- This is effectively just a name for the constant functor which
-- returns Void.  It is not representable.
--
-- It is an initial object both in the category of polynomial endofunctors
-- on `Type` and the category of Dirichlet endofunctors on `Type`.
public export
data EmptyF : Type -> Type where

public export
EmptyAlg : Type -> Type
EmptyAlg = Algebra EmptyF

public export
EmptyCoalg : Type -> Type
EmptyCoalg = Coalgebra EmptyF

-- The deduction rule of `ex falso quodlibet` is an algebra of `EmptyF`.
public export
ExF : {0 a : Type} -> EmptyAlg a
ExF {a} _ impossible

-- A proof that a type is uninhabited -- in other words, a derivation of
-- a contradiction from an arbitrary term of the type -- is a coalgebra
-- of `EmptyF`.
public export
IsEmpty : {0 a : Type} -> (a -> Void) -> EmptyCoalg a
IsEmpty {a} coalg x = case (coalg x) of _ impossible

public export
EmptyFM : Type -> Type
EmptyFM = FreeMonad EmptyF

public export
EmptyFreeAlg : (a : Type) -> EmptyAlg (EmptyFM a)
EmptyFreeAlg a = inFC {a}

public export
EmptyCFCM : Type -> Type
EmptyCFCM = CofreeComonad EmptyF

public export
EmptyCofreeCoalg : (a : Type) -> EmptyCoalg (EmptyCFCM a)
EmptyCofreeCoalg a = outCFC {a}

---------------------------
---- Unital structures ----
---------------------------

-- This is effectively just a name for the constant functor which
-- returns Unit, which is a covariant representable represented by Void,
-- and also a contravariant representable represented by Unit.
--
-- It is a terminal object both in the category of polynomial endofunctors
-- on `Type` and the category of Dirichlet endofunctors on `Type`.
public export
data UnitalF : Type -> Type where
  UOu : UnitalF a

public export
UnitalAlg : Type -> Type
UnitalAlg = Algebra UnitalF

public export
UnitalCoalg : Type -> Type
UnitalCoalg = Coalgebra UnitalF

-- Since `Type` is well-pointed, an algebra of a `UnitalF` is effectively
-- a type together with a term of that type.
public export
MkU : {0 a : Type} -> a -> UnitalAlg a
MkU x UOu = x

public export
Uu : {0 a : Type} -> UnitalAlg a -> a
Uu alg = alg UOu

-- Since `UnitalF` returns the terminal object for any input object, a
-- coalgebra of `UnitalF` is effectively just a type, as any type has
-- a morphism to the terminal object.
public export
MatchU : {0 a : Type} -> UnitalCoalg a
MatchU {a} _ = UOu

public export
UnitalFM : Type -> Type
UnitalFM = FreeMonad UnitalF

public export
UnitalFreeAlg : (a : Type) -> UnitalAlg (UnitalFM a)
UnitalFreeAlg a = inFC {a}

public export
UnitalCFCM : Type -> Type
UnitalCFCM = CofreeComonad UnitalF

public export
UnitalCofreeCoalg : (a : Type) -> UnitalCoalg (UnitalCFCM a)
UnitalCofreeCoalg a = outCFC {a}

---------------
---- Unars ----
---------------

-- Effectively the identity functor, which is a covariant representable
-- represented by `Unit`.
public export
data UnarF : Type -> Type where
  UOun : a -> UnarF a

public export
UnarAlg : Type -> Type
UnarAlg = Algebra UnarF

public export
UnarCoalg : Type -> Type
UnarCoalg = Coalgebra UnarF

-- Since `UnarF a` is just `a`, an algebra or coalgebra of `UnarF` is
-- effectively an endormorphism on `a`.
public export
MkUn : {0 a : Type} -> (a -> a) -> UnarAlg a
MkUn f (UOun x) = f x

public export
Uun : {0 a : Type} -> UnarAlg a -> a -> a
Uun alg = alg . UOun

public export
MatchUn : {0 a : Type} -> (a -> a) -> UnarCoalg a
MatchUn f x = UOun $ f x

public export
TypeUn : {0 a : Type} -> UnarCoalg a -> a -> a
TypeUn coalg x = case (coalg x) of UOun x' => x

public export
UnarFM : Type -> Type
UnarFM = FreeMonad UnarF

public export
UnarFreeAlg : (a : Type) -> UnarAlg (UnarFM a)
UnarFreeAlg a = inFC {a}

public export
UnarCFCM : Type -> Type
UnarCFCM = CofreeComonad UnarF

public export
UnarCofreeCoalg : (a : Type) -> UnarCoalg (UnarCFCM a)
UnarCofreeCoalg a = outCFC {a}

-------------------------------------------------
-------------------------------------------------
---- Representable functors and hom-functors ----
-------------------------------------------------
-------------------------------------------------

-- If the terms of `a` and `b` are the objects of two categories,
-- `h` is a profunctor `a |-> b` internal to a monoidal category with objects
-- from `c`, and `u` is a monoidal unit in `d`, then this produces the
-- covariant hom-functor represented by an initial object in `a` (if
-- there is one).
public export
CovarInit : {0 a, b, c, d : Type} ->
  (u : UnitalAlg d) -> (h : a -> b -> c) -> b -> d
CovarInit {a} {b} {c} {d} u h _ = Uu u

-- If the terms of `a` and `b` are the objects of two categories,
-- `h` is a profunctor `a |-> b` internal to a monoidal category with objects
-- from `c`, and `u` is the monoidal unit in `c`, then this produces the
-- contravariant hom-functor represented by a terminal object in `b` (if
-- there is one).
public export
ContravarTerm : {0 a, b, c, d : Type} ->
  (u : UnitalAlg d) -> (h : a -> b -> c) -> a -> d
ContravarTerm {a} {b} {c} {d} u h _ = Uu u

-- If `a` is a type of objects which we assume to have a terminal object,
-- and `h x` is the covariant hom-functor represented by `x` for any `x : a`
-- (where the hom-functor itself is internal to a category with objects in
-- `b`), then this returns the covariant hom-functor represented by a terminal
-- object.
--
-- In particular:
--
-- - If `b` is `a`, then the hom-functor is internal to the category `a` itself,
-- so this returns the hom-object out of a terminal object; since this makes
-- sense only if the category has products and hom-objects, that means that
-- the category is cartesian closed, and in particular this function is the
-- identity, since `hom(1, x) === x` for any `x : a`.
--
-- - If `b` is `Type`, then the (covariant) hom-functor is internal to `Type`.
-- In this case, that `CovarTerm h` is the identity functor reflects that
-- `Type` is well-pointed (its objects are characterized entirely by its
-- functions from `Unit`, AKA its terms).
public export
CovarTerm : {0 a, b, c : Type} -> (h : a -> b -> c) -> b -> b
CovarTerm {a} {b} {c} h x = x

-- If the terms of `a` and `b` are the objects of two categories,
-- `h` is a profunctor `a |-> b` internal to a monoidal category with objects
-- from `c`, and `p` is the monoidal product in `c`, then for each pair of
-- objects in `a`, this produces the covariant functor resulting from
-- taking the tensor product of the pair of covariant functors represented
-- by each of the pair of objects in `a`.
--
-- In particular, if `b` is `a` and `d` is `c` and `p` is a product, then this
-- is the covariant hom-functor internal to `c` represented by a pairwise
-- coproduct in `a`.
public export
PCCovarHom : {0 a, b, c, d : Type} -> (p : c -> c -> d) ->
  (h : a -> b -> c) -> (a, a) -> b -> d
PCCovarHom {a} {b} {c} p h (x, y) z = p (h x z) (h y z)

-- If the terms of `a` and `b` are the objects of two categories,
-- `h` is a profunctor `a |-> b` internal to a monoidal category with objects
-- from `c`, and `p` is the monoidal product in `c`, then for each pair of
-- objects in `b`, this produces the contravariant functor resulting from
-- taking the tensor product of the pair of contravariant functors represented
-- by each of the pair of objects in `b`.
--
-- In particular, if `b` is `a` and `d` is `c` and `p` is a product, then this
-- is the contravariant hom-functor internal to `c` represented by a pairwise
-- product in `a`.
public export
PPContraHom : {0 a, b, c, d : Type} -> (p : c -> c -> d) ->
  (h : a -> b -> c) -> (b, b) -> a -> d
PPContraHom {a} {b} {c} p h (y, z) x = p (h x y) (h x z)

-- If `a` is a type of objects which we assume to have pairwise products,
-- and `h x` is the covariant hom-functor represented by `x` for any `x : a`
-- (where the hom-functor itself is internal to a category with objects in
-- `b`), then this returns the covariant hom-functor represented by a pairwise
-- product.
--
-- In particular:
--
-- - If `b` is `a`, then the hom-functor is internal to the category `a` itself,
-- so this returns the hom-object out of a product; since this makes
-- sense only if the category has products and hom-objects, that means that
-- the category is cartesian closed, and in particular this function is the
-- object-map component of the currying functor.
--
-- - If `b` is `Type`, then the (covariant) hom-functor is internal to `Type`;
-- one application of this case is that if `h` produces types of `a`-indexed
-- families of terms of a given type, then the output of this function produces
-- families indexed by the product of a pair of objects of `a`.
public export
PPCovarHom : {0 a, b : Type} -> (h : a -> b -> b) -> (a, a) -> b -> b
PPCovarHom {a} {b} h (x, y) z = h x (h y z)

-----------------------------------------------
-----------------------------------------------
---- Categories defined via slice algebras ----
-----------------------------------------------
-----------------------------------------------

-----------------
---- Quivers ----
-----------------

public export
Quiver : Type
Quiver = PreDiagram

public export
qVert : SliceObj Quiver
qVert = pdVert

public export
qSig : SliceObj Quiver
qSig = SignatureT . qVert

public export
QHomSlice : SliceObj Quiver
QHomSlice = HomSlice . qVert

public export
qEdge : Pi {a=Quiver} QHomSlice
qEdge = pdEdge

-- A notion of identity and composition on a quiver.
public export
QuiverIC : SliceObj Quiver
QuiverIC q = SliceAlg CatHomF (qEdge q)

-- A notion of a relation on the edges of a quiver.
public export
QuivEdgeRel : SliceObj Quiver
QuivEdgeRel q = Pi {a=(qSig q)} (PrERel . qEdge q)

--------------------
---- Categories ----
--------------------

-- A quiver with notions of identity, composition, and congruence --
-- which suffice to form the data of a category, but does not contain
-- proofs of the category laws.
public export
record CatData where
  constructor CatD
  cdQuiv : Quiver
  cdIdComp : QuiverIC cdQuiv
  cdCong : QuivEdgeRel cdQuiv

public export
cdObj : SliceObj CatData
cdObj = qVert . cdQuiv

public export
cdSig : SliceObj CatData
cdSig = qSig . cdQuiv

public export
CDHomSlice : SliceObj CatData
CDHomSlice = QHomSlice . cdQuiv

public export
cdHom : Pi {a=CatData} CDHomSlice
cdHom cd = qEdge $ cdQuiv cd

public export
CDIC : SliceObj CatData
CDIC = QuiverIC . cdQuiv

public export
cdIdSig : SliceObj CatData
cdIdSig cd = (x : cdObj cd) -> cdHom cd (x, x)

public export
cdId : (cd : CatData) -> cdIdSig cd
cdId cd x = cdIdComp cd (x, x) $ CHId {hom=(cdHom cd)} x

public export
cdCompSig : SliceObj CatData
cdCompSig cd = (x, y, z : cdObj cd) ->
  cdHom cd (y, z) -> cdHom cd (x, y) -> cdHom cd (x, z)

public export
cdComp : (cd : CatData) -> cdCompSig cd
cdComp cd x y z g f = cdIdComp cd (x, z) $ CHComp {hom=(cdHom cd)} g f

public export
cdPipeSig : SliceObj CatData
cdPipeSig cd = (x, y, z : cdObj cd) ->
  cdHom cd (x, y) -> cdHom cd (y, z) -> cdHom cd (x, z)

public export
cdPipe : (cd : CatData) -> cdPipeSig cd
cdPipe cd x y z = flip (cdComp cd x y z)

export infixr 1 <#
public export
(<#) : {cd : CatData} -> {x, y, z : cdObj cd} ->
  cdHom cd (y, z) -> cdHom cd (x, y) -> cdHom cd (x, z)
(<#) {cd} {x} {y} {z} = cdComp cd x y z

export infixr 1 |>
public export
(#>) : {cd : CatData} -> {x, y, z : cdObj cd} ->
  cdHom cd (x, y) -> cdHom cd (y, z) -> cdHom cd (x, z)
(#>) {cd} {x} {y} {z} = cdPipe cd x y z

public export
0 CatEquivLaw : SliceObj CatData
CatEquivLaw cd = (xy : cdSig cd) -> PrEquivRelI (cdHom cd xy) (cdCong cd xy)

public export
0 CatLeftIdLaw : SliceObj CatData
CatLeftIdLaw cd =
  (x, y : cdObj cd) -> (f : cdHom cd (x, y)) ->
  cdCong cd (x, y) (cdComp cd x y y (cdId cd y) f, f)

public export
0 CatRightIdLaw : SliceObj CatData
CatRightIdLaw cd =
  (x, y : cdObj cd) -> (f : cdHom cd (x, y)) ->
  cdCong cd (x, y) (cdComp cd x x y f (cdId cd x), f)

public export
0 CatAssocLaw : SliceObj CatData
CatAssocLaw cd =
  (w, x, y, z : cdObj cd) ->
  (f : cdHom cd (w, x)) -> (g : cdHom cd (x, y)) -> (h : cdHom cd (y, z)) ->
  cdCong cd (w, z)
    (cdComp cd w x z (cdComp cd x y z h g) f,
     cdComp cd w y z h (cdComp cd w x y g f))

-- A type representing that a given `CatData` obeys the laws of a category.
-- This could be viewed as stating that the relation on the edges is a
-- congruence.
public export
record CatDataLawful (cd : CatData) where
  constructor CatLaws
  0 catLawEquiv : CatEquivLaw cd
  0 catLawIdL : CatLeftIdLaw cd
  0 catLawIdR : CatRightIdLaw cd
  0 catLawIdAssoc : CatAssocLaw cd

-- A proven category, with underlying data and proofs of the laws.
public export
record LawfulCat where
  constructor LCat
  lcData : CatData
  0 lcLawful : CatDataLawful lcData

public export
lcObj : SliceObj LawfulCat
lcObj = cdObj . lcData

public export
lcSig : SliceObj LawfulCat
lcSig = cdSig . lcData

public export
LCHomSlice : SliceObj LawfulCat
LCHomSlice = CDHomSlice . lcData

public export
lcHom : Pi {a=LawfulCat} LCHomSlice
lcHom lc = cdHom $ lcData lc

public export
LCIC : SliceObj LawfulCat
LCIC = CDIC . lcData

public export
lcIdSig : SliceObj LawfulCat
lcIdSig = cdIdSig . lcData

public export
lcId : (lc : LawfulCat) -> lcIdSig lc
lcId lc = cdId (lcData lc)

public export
lcCompSig : SliceObj LawfulCat
lcCompSig = cdCompSig . lcData

public export
lcComp : (lc : LawfulCat) -> lcCompSig lc
lcComp lc = cdComp (lcData lc)

public export
lcPipeSig : SliceObj LawfulCat
lcPipeSig = cdPipeSig . lcData

public export
lcPipe : (lc : LawfulCat) -> lcPipeSig lc
lcPipe lc x y z = flip (lcComp lc x y z)

export infixr 1 <!
public export
(<!) : {lc : LawfulCat} -> {x, y, z : lcObj lc} ->
  lcHom lc (y, z) -> lcHom lc (x, y) -> lcHom lc (x, z)
(<!) {lc} {x} {y} {z} = lcComp lc x y z

export infixr 1 !>
public export
(!>) : {lc : LawfulCat} -> {x, y, z : lcObj lc} ->
  lcHom lc (x, y) -> lcHom lc (y, z) -> lcHom lc (x, z)
(!>) {lc} {x} {y} {z} = lcPipe lc x y z

------------------
---- Functors ----
------------------

public export
FunctorSig : Type
FunctorSig = SignatureT CatData

public export
ObjMap : SliceObj FunctorSig
ObjMap sig = cdObj (fst sig) -> cdObj (snd sig)

public export
MorphMap : (sig : FunctorSig) -> SliceObj (ObjMap sig)
MorphMap sig fo = (x, y : cdObj $ fst sig) ->
  cdHom (fst sig) (x, y) -> cdHom (snd sig) (fo x, fo y)

public export
record FunctorData (sig : FunctorSig) where
  constructor FunctorD
  fdOmap : ObjMap sig
  fdMmap : MorphMap sig fdOmap

public export
0 FunctorIdLaw : (sig : FunctorSig) -> SliceObj (FunctorData sig)
FunctorIdLaw sig fd =
  (x : cdObj $ fst sig) ->
  cdCong (snd sig) (fdOmap fd x, fdOmap fd x)
    (cdId (snd sig) (fdOmap fd x), fdMmap fd x x (cdId (fst sig) x))

public export
0 FunctorCompLaw : (sig : FunctorSig) -> SliceObj (FunctorData sig)
FunctorCompLaw sig fd = (x, y, z : cdObj $ fst sig) ->
  (g : cdHom (fst sig) (y, z)) -> (f : cdHom (fst sig) (x, y)) ->
  cdCong (snd sig) (fdOmap fd x, fdOmap fd z)
    (fdMmap fd x z (g <# f), fdMmap fd y z g <# fdMmap fd x y f)

public export
record FunctorDataLawful {sig : FunctorSig} (fd : FunctorData sig) where
  constructor FunctorLaws
  0 funcLawId : FunctorIdLaw sig fd
  0 funcLawComp : FunctorCompLaw sig fd

public export
record LawfulFunctor (sig : FunctorSig) where
  constructor LFunc
  lfData : FunctorData sig
  0 lfLawful : FunctorDataLawful lfData

---------------------------------------------------
---- Two-categories with functors as morphisms ----
---------------------------------------------------

---------------------------------
---- Natural transformations ----
---------------------------------

public export
NTSig : Type
NTSig = DPair FunctorSig (SignatureT . FunctorData)

public export
NTcdata : NTSig -> SignatureT CatData
NTcdata = fst

public export
NTcdom : NTSig -> CatData
NTcdom = fst . NTcdata

public export
NTccod : NTSig -> CatData
NTccod = snd . NTcdata

public export
NTfdom : (sig : NTSig) -> FunctorData $ NTcdata sig
NTfdom sig = fst $ snd sig

public export
NTfcod : (sig : NTSig) -> FunctorData $ NTcdata sig
NTfcod sig = snd $ snd sig

public export
NTComponentSig : SliceObj NTSig
NTComponentSig sig = (x : cdObj $ NTcdom sig) ->
  cdHom (NTccod sig) (fdOmap (NTfdom sig) x, fdOmap (NTfcod sig) x)

public export
record NTData (sig : NTSig) where
  constructor NTD
  ntdC : NTComponentSig sig

public export
0 NaturalityLaw : (sig : NTSig) -> SliceObj (NTData sig)
NaturalityLaw sig ntd =
  (x, y : cdObj $ NTcdom sig) -> (m : cdHom (NTcdom sig) (x, y)) ->
  cdCong (NTccod sig) (fdOmap (NTfdom sig) x, fdOmap (NTfcod sig) y)
    (fdMmap (NTfcod sig) x y m <# ntdC ntd x,
     ntdC ntd y <# fdMmap (NTfdom sig) x y m)

public export
record NTDataLawful {sig : NTSig} (ntd : NTData sig) where
  constructor NTLaws
  0 ntLawNatural : NaturalityLaw sig ntd

public export
record LawfulNT (sig : NTSig) where
  constructor LNT
  lntData : NTData sig
  0 lntLawful : NTDataLawful lntData

-----------------------------------------
-----------------------------------------
---- Internal representable functors ----
-----------------------------------------
-----------------------------------------

public export
algLift :
  (0 f : Type -> Type) -> (fm : (0 x, y : Type) -> (x -> y) -> f x -> f y) ->
  {0 a, b : Type} -> (m : Algebra f b) -> (h : a -> b) -> f a -> b
algLift f fm {a} {b} = (|>) (fm a b) . (.)

{-
  Suppose the following:

    - `f` is an endofunctor in `Type`
    - `c` and `m` form an algebra of `f` (`c` is the object; `m`
      is the morphism)
    - `a` and `b` are the types of objects of two categories (we shall also
      refer to the those categories themselves as `a` and `b`)
    - `h` is a profunctor `a |-> b` enriched over a third category, whose
      objects are of type `c` (we shall also refer to that category itself
      as `c`) -- that is, a functor from `(op(b), a)` to `c` (the `h` is meant
      to suggest `hom-(pro)functor`)

  Under those conditions, we can produce a hom-profunctor `a |-> f(b)` where
  `f(b)` is the image of `b` under `f`.

  In particular, for example, if `f` is `ProductMonad` and `b` is `a`, then
  this takes an endoprofunctor `h` on `a` and generates a hom-functor internal
  to `c` extended by a covariant hom-functor represented by a pairwise
  coproduct in `a`.
-}
public export
covarHomProfuncLift :
  (0 f : Type -> Type) -> (fm : (0 x, y : Type) -> (x -> y) -> f x -> f y) ->
  {0 a, b, c : Type} -> (m : Algebra f c) -> (h : b -> a -> c) -> f b -> a -> c
covarHomProfuncLift f fm {a} {b} {c} =
  (|>) ((|>) . flip) . (|>) . flip . algLift f fm {a=b} {b=c}

{-
  Dually to `covarHomLift`, this produces a hom-profunctor `f(a) |-> b`
  by extending the contravariant component.
-}
public export
contravarHomProfuncLift :
  (0 f : Type -> Type) -> (fm : (0 x, y : Type) -> (x -> y) -> f x -> f y) ->
  {0 a, b, c : Type} -> (m : Algebra f c) -> (h : b -> a -> c) -> b -> f a -> c
contravarHomProfuncLift f fm {a} {b} {c} =
  (.) . algLift f fm {a} {b=c}

-------------------------------------------------
-------------------------------------------------
---- Functors in `Cat` as internal to `Type` ----
-------------------------------------------------
-------------------------------------------------

-------------------------------------------------------------------------------
---- Product `Cat`-functor (the functor which produces a product category) ----
-------------------------------------------------------------------------------

-- A functor in the category of categories, which produces the product category.
-- This is the first component of the object map of a polynomial endofunctor in
-- the category of presheaves over the walking quiver.
public export
ProdCatOMap1 : (o : Type) -> (m : o -> o -> Type) -> Type
ProdCatOMap1 o m = (o, o)

-- This is the second component.
public export
ProdCatOMap2 : (o : Type) -> (m : o -> o -> Type) ->
  ProdCatOMap1 o m -> ProdCatOMap1 o m -> Type
ProdCatOMap2 o m x y = (m (fst x) (fst y), m (snd x) (snd y))

public export
ProdCatOMap : (o : Type) -> (m : o -> o -> Type) ->
  (o' : Type ** o' -> o' -> Type)
ProdCatOMap o m = (ProdCatOMap1 o m ** ProdCatOMap2 o m)

-- The morphism map of an endofunctor in the category of presheaves over the
-- walking quiver is a map from morphisms to morphisms of the category of
-- presheaves, and the morphisms of the category of presheaves are natural
-- transformations.  So the morphism map takes natural transformations to
-- natural transformations (in the presheaf category).  This is the morphism
-- map of the functor which produces the product category of the input category.
public export
ProdCatFMap :
  (o, o' : Type) -> (m : o -> o -> Type) -> (m' : o' -> o' -> Type) ->
  (ont : o -> o') -> (mnt : (x, y : o) -> m x y -> m' (ont x) (ont y)) ->
  (font : ProdCatOMap1 o m -> ProdCatOMap1 o' m' **
   (x, y :  ProdCatOMap1 o m) ->
    ProdCatOMap2 o m x y -> ProdCatOMap2 o' m' (font x) (font y))
ProdCatFMap o o' m m' ont mnt =
  (\xy => (ont (fst xy), ont (snd xy)) **
   \xx', yy', mm' =>
    (mnt (fst xx') (fst yy') (fst mm'), (mnt (snd xx') (snd yy') (snd mm'))))

-- The diagonal functor from a category to its product category.  This is
-- a natural transformation in the category of presheaves over the walking
-- quiver, from the identity functor to the `ProdCatOMap` functor.
-- That means that for each object of the category of presheaves over the
-- walking quiver, we specify a morphism from that object to its image under
-- `ProdCatOMap`.
--
-- An object in a category of presheaves is a functor from the index category
-- (in this case, the walking quiver) to `Type`, and a morphism in that
-- category is a natural transformation between those functors.
--
-- So, the diagonal functor in this formulation -- a polymorphic one in which
-- the input category could be any category -- consists of, for each presheaf
-- on the walking quiver, a natural transformation from the identity functor
-- to `ProdCatOMap`/`ProdCatFMap`.
public export
InternalDiagOMap : (o : Type) -> (m : o -> o -> Type) -> o -> ProdCatOMap1 o m
InternalDiagOMap o m x = (x, x)

public export
InternalDiagFMap : (o : Type) -> (m : o -> o -> Type) -> (x, y : o) ->
  m x y -> ProdCatOMap2 o m (InternalDiagOMap o m x) (InternalDiagOMap o m y)
InternalDiagFMap o m x y f = (f, f)

---------------------------------------------------------
---- Adjunction with the product category: coproduct ----
---------------------------------------------------------

public export
CopROMap : (o : Type) -> (m : o -> o -> Type) -> o -> ProdCatOMap1 o m
CopROMap = InternalDiagOMap

public export
CopRFMap : (o : Type) -> (m : o -> o -> Type) -> (x, y : o) ->
  m x y -> ProdCatOMap2 o m (CopROMap o m x) (CopROMap o m y)
CopRFMap = InternalDiagFMap

public export
CopFreeRAdj : (o : Type) -> (m : o -> o -> Type) ->
  (a : ProdCatOMap1 o m) -> (b : o) -> Type
CopFreeRAdj o m = flip $ (.) (uncurry Pair) . (mapHom {f=Pair} . flip m)

-------------------------------------------------------
---- Adjunction with the product category: product ----
-------------------------------------------------------

public export
ProdLOMap : (o : Type) -> (m : o -> o -> Type) -> o -> ProdCatOMap1 o m
ProdLOMap = InternalDiagOMap

public export
ProdLFMap : (o : Type) -> (m : o -> o -> Type) -> (x, y : o) ->
  m x y -> ProdCatOMap2 o m (ProdLOMap o m x) (ProdLOMap o m y)
ProdLFMap = InternalDiagFMap

public export
ProdFreeLAdj : (o : Type) -> (m : o -> o -> Type) ->
  (a : ProdCatOMap1 o m) -> (b : o) -> Type
ProdFreeLAdj o m = flip $ (.) (uncurry Pair) . (mapHom {f=Pair} . m)

---------------------------------------------------
---------------------------------------------------
---- Partial interpretations as `Maybe`-slices ----
---------------------------------------------------
---------------------------------------------------

-- For a given object `a`, a category-theory-style slice object over `Maybe a`
-- maybe viewed as an object together with an interpretation of that object
-- as a representation of `a`, which may be partial both in the sense that
-- the object may have more structure than is determined solely by its
-- representing `a` and in the sense that it might represent only part of the
-- structure of `a`.
--
-- One specific application of this is that if we imagine that `a` is a type
-- whose terms some interface knows how to interpret, then given a slice
-- `(b : Type ** f : b -> Maybe a)` over `Maybe a`, we could build an
-- interpretation of some type of structure containing terms of `b` which knows
-- how to interpret a given structure of that type whenever all the terms
-- of `b` contained in that structure have interpretations as `Just a` under
-- `f`.
public export
MaybeCS : Type -> Type
MaybeCS = CSliceObj . Maybe

----------------------------------------------
----------------------------------------------
---- Typechecked terms as `Either`-slices ----
----------------------------------------------
----------------------------------------------

-- For given objects `a` and `b`, a category-theory-style slice object over
-- `Either a b` maybe viewed as an object with a type `b` whose typechecking
-- might fail with an error from `a`.
--
-- `Either Void b` is isomorphic to `b`; `Either Unit b` is isomorphic to
-- `Maybe b`.
public export
EitherCS : Type -> Type -> Type
EitherCS = CSliceObj .* Either

-----------------------------------------
-----------------------------------------
---- Either algebras of binary trees ----
-----------------------------------------
-----------------------------------------

-- Simply an alias for `btCataByTuple` which specializes `btCataByTuple`'s
-- output type to a `HomEither`.
public export
binTreeHomEitherCataByTuple :
  {0 atom, a, e, b : Type} ->
  (aalg : atom -> HomEither a e b) ->
  (talg : BTTexp2 (HomEither a e b) -> HomEither a e b) ->
  BinTreeMu atom -> HomEither a e b
binTreeHomEitherCataByTuple {atom} {a} {e} {b} =
  btCataByTuple {atom} {x=(HomEither a e b)} .* MkPair

public export
BinTreeBindAlg :
  {0 m : Type -> Type} -> (fm : {0 a, b : Type} -> (a -> b) -> m a -> m b) ->
  (pu : {0 a : Type} -> a -> m a) ->
  (app : {0 a, b : Type} -> m (a -> b) -> m a -> m b) ->
  (bind : {0 a, b : Type} -> m a -> (a -> m b) -> m b) ->
  {0 atom, a, b : Type} ->
  (alg : atom -> a -> m b) -> (cons : a -> b -> a) ->
  BinTreeAlg atom (a -> m b)
BinTreeBindAlg {m} fm pu app bind alg cons (Left x) ea =
  alg x ea
BinTreeBindAlg {m} fm pu app bind alg cons (Right (bt, bt')) ea =
  bind (app {a=b} {b=a} (fm {a} {b=(b -> a)} cons (pu ea)) $ bt ea) bt'

public export
BinTreeMonadAlg :
  {0 m : Type -> Type} -> {auto isMonad : Monad m} ->
  {0 atom, a, b : Type} ->
  (alg : atom -> a -> m b) -> (cons : a -> b -> a) ->
  BinTreeAlg atom (a -> m b)
BinTreeMonadAlg {m} {isMonad} =
  BinTreeBindAlg {m} (map {f=m}) (pure {f=m}) ((<*>) {f=m}) ((>>=) {m})

public export
binTreeBindCata :
  {0 m : Type -> Type} -> (fm : {0 a, b : Type} -> (a -> b) -> m a -> m b) ->
  (pu : {0 a : Type} -> a -> m a) ->
  (app : {0 a, b : Type} -> m (a -> b) -> m a -> m b) ->
  (bind : {0 a, b : Type} -> m a -> (a -> m b) -> m b) ->
  {0 atom, a, b : Type} ->
  (alg : atom -> a -> m b) -> (cons : a -> b -> a) ->
  BinTreeMu atom -> a -> m b
binTreeBindCata {m} fm pu app bind {atom} {a} {b} alg cons =
  binTreeCata {atom} {a=(a -> m b)}
    (BinTreeBindAlg {m} fm pu app bind {atom} {a} {b} alg cons)

public export
binTreeMonadCata :
  {0 m : Type -> Type} -> {auto isMonad : Monad m} ->
  {0 atom, a, b : Type} ->
  (alg : atom -> a -> m b) -> (cons : a -> b -> a) ->
  BinTreeMu atom -> a -> m b
binTreeMonadCata {m} {isMonad} =
  binTreeBindCata {m} (map {f=m}) (pure {f=m}) ((<*>) {f=m}) ((>>=) {m})

public export
binTreeHomEitherCata :
  {0 atom, a, e, b : Type} ->
  (alg : atom -> HomEither a e b) -> (cons : a -> b -> a) ->
  BinTreeMu atom -> HomEither a e b
binTreeHomEitherCata {atom} {a} {e} {b} =
  binTreeMonadCata {m=(Either e)} {atom} {a} {b}

public export
binTreeMaybeCata :
  {0 atom, a, b : Type} ->
  (alg : atom -> a -> Maybe b) -> (cons : a -> b -> a) ->
  BinTreeMu atom -> a -> Maybe b
binTreeMaybeCata {atom} {a} {b} =
  binTreeMonadCata {m=Maybe} {atom} {a} {b}

public export
BinTreeAutoBindAlg :
  {0 m : Type -> Type} -> {0 atom, a : Type} ->
  (alg : atom -> a -> m a) -> (autob : m a -> (a -> m a) -> m a) ->
  BinTreeAlg atom (a -> m a)
BinTreeAutoBindAlg {m} alg autob (Left x) ea = alg x ea
BinTreeAutoBindAlg {m} alg autob (Right (bt, bt')) ea = autob (bt ea) bt'

public export
BinTreeMonadAutoAlg :
  {0 m : Type -> Type} -> {auto isMonad : Monad m} -> {0 atom, a : Type} ->
  (atom -> a -> m a) -> BinTreeAlg atom (a -> m a)
BinTreeMonadAutoAlg {m} {a} {isMonad} alg =
  BinTreeAutoBindAlg {m} alg ((>>=) {a} {b=a})

public export
AutoHomEither : Type -> Type -> Type
AutoHomEither a e = HomEither a e a

public export
aheMap : {0 a, e, e' : Type} ->
  (e -> e') -> AutoHomEither a e -> AutoHomEither a e'
aheMap = (.) . mapFst {f=Either} {a=e} {b=a} {c=e'}

public export
Functor (AutoHomEither a) where
  map = aheMap

public export
ahePure : {0 a, e : Type} -> e -> AutoHomEither a e
ahePure {a} {e} = const . Left

public export
EitherAutoHom : Type -> Type -> Type
EitherAutoHom = flip AutoHomEither

public export
ehaPure : {0 e, a : Type} -> a -> EitherAutoHom e a
ehaPure {a} {e} = const . Right

public export
eahBindHom : {0 e, a : Type} ->
  EitherAutoHom e a -> (a -> EitherAutoHom e a) -> EitherAutoHom e a
eahBindHom {e} {a} = flip $ biapp (eitherElim Left)

public export
BinTreeEitherAutoHomAlg : {0 atom, a, e : Type} ->
  (alg : atom -> a -> EitherAutoHom e a) ->
  BinTreeAlg atom (a -> EitherAutoHom e a)
BinTreeEitherAutoHomAlg {atom} {a} {e} =
  flip (BinTreeAutoBindAlg {m=(EitherAutoHom e)} {atom} {a}) eahBindHom

public export
binTreeEitherAutoHomCata : {0 atom, a, e : Type} ->
  (alg : atom -> a -> EitherAutoHom e a) ->
  BinTreeMu atom -> a -> EitherAutoHom e a
binTreeEitherAutoHomCata {atom} {a} {e} =
  binTreeCata {atom} {a=(a -> a -> Either e a)} . BinTreeEitherAutoHomAlg

-------------------------------------------------------------
-------------------------------------------------------------
---- Unrefined finitary polynomial types as binary trees ----
-------------------------------------------------------------
-------------------------------------------------------------

-- The simplest form of finitary polynomial types is just a finite
-- set of constructors each of which has a finite set of arguments (of
-- the type itself).  A finite type is a type whose argument sets are
-- all empty (zero-size).
public export
record FPFunctor where
  constructor FPF
  fpfNpos : Nat
  fpfNdir : Vect fpfNpos Nat

public export
FPFatom : FPFunctor -> Type
FPFatom = Fin . fpfNpos

public export
FPFbt : FPFunctor -> Type
FPFbt = BinTreeMu . FPFatom

public export
FPFpred : FPFunctor -> Type
FPFpred = DecPred . FPFbt

public export
data FPFCheck : Type where
  FPFconstr : Nat -> FPFCheck
  FPFterm : FPFCheck

public export
Show FPFCheck where
  show (FPFconstr n) = "(constr[" ++ show n ++ "])"
  show FPFterm = "(term)"

public export
data FPFErr : Type where
  FPFnonConstrHd : FPFErr
  FPFwrongNarg : Nat -> Nat -> FPFErr

public export
Show FPFErr where
  show FPFnonConstrHd = "(non-constructor head)"
  show (FPFwrongNarg n n') = "(wrong number of arguments: expected " ++
    show n ++ "; got " ++ show n' ++ ")"

public export
fpfCheckTermVec : {0 n : Nat} -> Vect n FPFCheck -> Either FPFErr ()
fpfCheckTermVec {n} =
  foldr {t=(Vect n)}
    (\x => eitherElim Left $ \() =>
      case x of
        FPFconstr n' => Left $ FPFwrongNarg 0 n'
        FPFterm => Right ())
    (Right ())

public export
fpfCheck : {fpf : FPFunctor} ->
  BinTreeMu (FPFatom fpf) -> Either FPFErr FPFCheck
fpfCheck {fpf} = btCataByTuple {atom=(FPFatom fpf)} {x=(Either FPFErr FPFCheck)}
  (\i =>
    let ndir = index i (fpfNdir fpf) in
    Right $ if ndir == 0 then FPFterm else FPFconstr ndir,
   \(n ** v) =>
    eitherElim
      Left
      (\v' => case index FZ v' of
        FPFconstr n' =>
          if n' == S n then
            eitherElim
              Left
              (const $ Right FPFterm)
              (fpfCheckTermVec $ tail v')
          else
            Left $ FPFwrongNarg n' (S n)
        FPFterm => Left FPFnonConstrHd)
      $ sequence v)

public export
fpfValid : {fpf : FPFunctor} -> DecPred $ BinTreeMu (FPFatom fpf)
fpfValid = isRight . fpfCheck

public export
FPFTerm : FPFunctor -> Type
FPFTerm fpf = Refinement {a=(BinTreeMu (FPFatom fpf))} (fpfValid {fpf})

public export
MkFPF : (fpf : FPFunctor) -> (bt : BinTreeMu (FPFatom fpf)) ->
  {auto 0 valid : IsTrue $ fpfValid {fpf} bt} -> FPFTerm fpf
MkFPF fpf bt {valid} = MkRefinement {p=(fpfValid {fpf})} bt

public export
checkFPFbounds : (fpf : FPFunctor) ->
  BinTreeMu Nat -> Maybe $ BinTreeMu $ FPFatom fpf
checkFPFbounds fpf =
  traverse {f=Maybe} {b=(FPFatom fpf)} $ \n => natToFin n (fpfNpos fpf)

public export
validFPFbounds : (fpf : FPFunctor) -> DecPred $ BinTreeMu Nat
validFPFbounds fpf = isJust . checkFPFbounds fpf

public export
MkFPFbounded : (fpf : FPFunctor) -> (bt : BinTreeMu Nat) ->
  {auto 0 bounded : IsTrue $ validFPFbounds fpf bt} ->
  BinTreeMu (FPFatom fpf)
MkFPFbounded fpf bt {bounded} with (checkFPFbounds fpf bt)
  MkFPFbounded fpf bt {bounded} | Just bt' = bt'
  MkFPFbounded fpf bt {bounded} | Nothing =
    void $ case bounded of Refl impossible

public export
checkFPFn : (fpf : FPFunctor) ->
  BinTreeMu Nat -> Maybe $ FPFTerm fpf
checkFPFn fpf bt with (checkFPFbounds fpf bt)
  checkFPFn fpf bt | Just bt' = case decEq (fpfValid {fpf} bt') True of
    Yes valid => Just $ Element0 bt' valid
    No _ => Nothing
  checkFPFn fpf bt | Nothing = Nothing

public export
validFPFn : (fpf : FPFunctor) -> DecPred $ BinTreeMu Nat
validFPFn fpf = isJust . checkFPFn fpf

public export
MkFPFn : (fpf : FPFunctor) -> (bt : BinTreeMu Nat) ->
  {auto 0 valid : IsTrue $ validFPFn fpf bt} ->
  FPFTerm fpf
MkFPFn fpf bt {valid} with (checkFPFn fpf bt)
  MkFPFn fpf bt {valid} | Just t = t
  MkFPFn fpf bt {valid} | Nothing = void $ case valid of Refl impossible

-------------------------------------------------------
-------------------------------------------------------
---- Experiments with generalized pattern matching ----
-------------------------------------------------------
-------------------------------------------------------

------------------------------------------------------------------
---- Using an explicit structure representing a pattern-match ----
------------------------------------------------------------------

public export
BinTreeGenAlgF : Type -> Type -> Type -> Type
BinTreeGenAlgF atom a x = (BinTreeAlg atom a, Maybe x, Maybe x)

public export
BinTreeGenAlgAlg : Type -> Type -> Type -> Type
BinTreeGenAlgAlg = Algebra .* BinTreeGenAlgF

public export
data BinTreeGenAlg : Type -> Type -> Type where
  InBTGA : {0 atom, a : Type} ->
    BinTreeGenAlgF atom a (BinTreeGenAlg atom a) -> BinTreeGenAlg atom a

public export
binTreeGenCata :
  {0 atom, a : Type} -> BinTreeMu atom -> BinTreeGenAlg atom a -> a
binTreeGenCata (InBTm (Left ea)) (InBTGA (alg, _, _)) =
  alg $ Left ea
binTreeGenCata (InBTm (Right (bt1, bt2))) galg@(InBTGA (alg, m1, m2)) =
  let
    (alg1, alg2) = case (m1, m2) of
      (Nothing, Nothing) => (galg, galg)
      (Nothing, Just mt2) => (galg, mt2)
      (Just mt1, Nothing) => (mt1, galg)
      (Just mt1, Just mt2) => (mt1, mt2)
  in
  alg $ Right (binTreeGenCata bt1 alg1, binTreeGenCata bt2 alg2)

------------------------------------------------
------------------------------------------------
---- Polynomial binary-tree-dependent types ----
------------------------------------------------
------------------------------------------------

public export
record BTMPolyDep (atom : Type) where
  constructor BTMPD
  btmPosCtor : Type
  btmPosParam : SliceObj btmPosCtor
  btmPosCod : Pi {a=btmPosCtor} $ BinTreeFM atom . btmPosParam
  btmDir : SliceObj btmPosCtor
  btmDirDom : SliceMorphism {a=btmPosCtor} btmDir (BinTreeFM atom . btmPosParam)

public export
btmpdPos : {atom : Type} -> BTMPolyDep atom -> SliceObj (BinTreeMu atom)
btmpdPos {atom} btmpd bt =
  (c : btmPosCtor btmpd **
   p : btmPosParam btmpd c -> BinTreeMu atom **
   Equal (btFullSubst p (btmPosCod btmpd c)) bt)

public export
btmpdDir : {atom : Type} -> (btmpd : BTMPolyDep atom) ->
  SliceObj (Sigma {a=(BinTreeMu atom)} $ btmpdPos {atom} btmpd)
btmpdDir {atom} btmpd pos = btmDir btmpd (fst (snd pos))

public export
btmpdAssign : {atom : Type} -> (btmpd : BTMPolyDep atom) ->
  (Sigma {a=(Sigma {a=(BinTreeMu atom)} $ btmpdPos {atom} btmpd)} $
    btmpdDir {atom} btmpd) ->
  BinTreeMu atom
btmpdAssign {atom} btmpd posdir =
  btFullSubst
    (fst $ snd $ snd $ fst posdir)
    (btmDirDom btmpd (fst $ snd $ fst posdir) $ snd posdir)

public export
btmpdToSPF : {atom : Type} ->
  BTMPolyDep atom -> SlicePolyFunc (BinTreeMu atom) (BinTreeMu atom)
btmpdToSPF {atom} btmpd =
  (btmpdPos {atom} btmpd **
   btmpdDir {atom} btmpd **
   btmpdAssign {atom} btmpd)

public export
InterpBTMPolyDep : {atom : Type} ->
  BTMPolyDep atom -> SliceEndofunctor (BinTreeMu atom)
InterpBTMPolyDep = InterpSPFunc . btmpdToSPF

public export
BinTreeDepFM : {atom : Type} ->
  BTMPolyDep atom -> SliceEndofunctor (BinTreeMu atom)
BinTreeDepFM = SlicePolyFree . btmpdToSPF

public export
BinTreeDepMu : {atom : Type} -> BTMPolyDep atom -> SliceObj (BinTreeMu atom)
BinTreeDepMu = SPFMu . btmpdToSPF

public export
binTreeDepEval : {atom : Type} -> (btmpd : BTMPolyDep atom) ->
  SPFMeval {a=(BinTreeMu atom)} (btmpdToSPF {atom} btmpd)
binTreeDepEval btmpd = spfmEval (btmpdToSPF btmpd)

-------------------------------------
---- Binary-tree-dependent types ----
-------------------------------------

public export
BinTreeF1 : Type -> IndIndF1
BinTreeF1 = (|>) pfPos . BinTreeF

public export
BinTreeIndIndAlg : Type -> IndIndF1
BinTreeIndIndAlg = IndIndAlg . BinTreeF1

public export
BinTreeF2 : Type -> Type
BinTreeF2 = IndIndF2 . BinTreeF1

public export
BinTreeIndInd : {atom : Type} -> BinTreeF2 atom -> IndInd
BinTreeIndInd {atom} f2 = (BinTreeF1 atom ** f2)

public export
BinTreeFreeM1 : Type -> PolyFunc -> Type
BinTreeFreeM1 = (|>) pfPos . BinTreeFM

public export
partial
data BinTreeFreeM2 : {0 atom : Type} -> (f2 : BinTreeF2 atom) ->
    (p : PolyFunc) -> BinTreeFreeM1 atom p -> Type where
  InBT2v : {0 atom : Type} -> {0 f2 : BinTreeF2 atom} -> {0 p : PolyFunc} ->
    (i : pfPos p) -> pfDir {p} i ->
    BinTreeFreeM2 {atom} f2 p (InBTv i)
  InBT2c : {0 atom : Type} -> {0 f2 : BinTreeF2 atom} -> {0 p : PolyFunc} ->
    (i1 : BinTreeF atom (BinTreeFreeM1 atom p)) ->
    f2 (BinTreeFreeM1 atom p ** BinTreeFreeM2 {atom} f2 p)
      InBTc i1 ->
    BinTreeFreeM2 {atom} f2 p (InBTc i1)

public export
BinTreeFreeIndIndM : {atom : Type} -> BinTreeF2 atom -> PolyFunc -> PolyFunc
BinTreeFreeIndIndM {atom} f2 p =
  (BinTreeFreeM1 atom p ** BinTreeFreeM2 {atom} f2 p)

public export
BinTreeF2' : Type -> Type
BinTreeF2' atom = (a : Type) -> (p : a -> Type) ->
  BinTreeAlg atom a -> BinTreeF atom a -> Type

public export
partial
data BinTreeFreeM2' : {0 atom : Type} -> (f2 : BinTreeF2' atom) ->
    {0 atom' : Type} -> (p : atom' -> Type) ->
    BinTreeFM atom atom' -> Type where
  InBT2v' : {0 atom, atom' : Type} ->
    {0 f2 : BinTreeF2' atom} -> {0 p : atom' -> Type} ->
    (i : atom') -> p i ->
    BinTreeFreeM2' {atom} {atom'} f2 p (InBTv i)
  InBT2c' : {0 atom, atom' : Type} ->
    {0 f2 : BinTreeF2' atom} -> {0 p : atom' -> Type} ->
    (i1 : BinTreeF atom (BinTreeFM atom atom')) ->
    f2 (BinTreeFM atom atom') (BinTreeFreeM2' {atom} f2 {atom'} p)
      InBTc i1 ->
    BinTreeFreeM2' {atom} {atom'} f2 p (InBTc i1)

public export
record PolyBTDep (atom : Type) where
  constructor PBTD
  pbtdPos : Type
  pbtdDir1 : pbtdPos -> Type
  pbtdDir2 : pbtdPos -> Type
  pbtdAssign : SliceMorphism {a=pbtdPos} pbtdDir2 (BinTreeFM atom . pbtdDir1)
  pbtdCod : Pi {a=pbtdPos} $ BinTreeFM atom . pbtdDir1

public export
data BinTreeFreeM2'' : {0 atom : Type} -> (f2 : PolyBTDep atom) ->
    {0 atom' : Type} -> (p : atom' -> Type) ->
    SliceObj (BinTreeFM atom atom') where
  InBTF2v : {0 atom : Type} -> {0 f2 : PolyBTDep atom} ->
    {0 atom' : Type} -> {0 p : atom' -> Type} ->
    (i : atom') -> p i ->
    BinTreeFreeM2'' {atom} f2 {atom'} p (InBTv i)
  InBTF2c : {0 atom : Type} -> {0 f2 : PolyBTDep atom} ->
    {0 atom' : Type} -> {0 p : atom' -> Type} ->
    (i : pbtdPos f2) ->
    (d1 : pbtdDir1 f2 i -> BinTreeFM atom atom') ->
    ((d2 : pbtdDir2 f2 i) -> BinTreeFreeM2'' {atom} f2 {atom'} p $
      binTreeFMBind d1 $ pbtdAssign f2 i d2) ->
    BinTreeFreeM2'' {atom} f2 {atom'} p $ binTreeFMBind d1 $ pbtdCod f2 i

--------------------------------------
---- Correctness of equality test ----
--------------------------------------

public export
0 binTreeEqCorrect : {0 atom : Type} -> (deq : DecEqPred atom) ->
  (x, x' : BinTreeMu atom) -> IsTrue (binTreeEq deq x x') -> x = x'
binTreeEqCorrect deq x x' eq = ?binTreeEqCorrect_hole

public export
0 binTreeNeqCorrect : {0 atom : Type} -> (deq : DecEqPred atom) ->
  (x, x' : BinTreeMu atom) -> IsFalse (binTreeEq deq x x') -> Not (x = x')
binTreeNeqCorrect deq x x' neq = ?binTreeNeqCorrect_hole

public export
0 binTreeDecEq : {0 atom : Type} -> DecEqPred atom -> DecEqPred (BinTreeMu atom)
binTreeDecEq deq x x' with (binTreeEq deq x x') proof prf
  binTreeDecEq deq x x' | True = Yes $ binTreeEqCorrect deq x x' prf
  binTreeDecEq deq x x' | False = No $ binTreeNeqCorrect deq x x' prf

------------------------------------------------
------------------------------------------------
---- Finitary dependent polynomial functors ----
------------------------------------------------
------------------------------------------------

FinSliceProdS : Type
FinSliceProdS = List Nat

0 FinProdBounded : Nat -> SliceObj FinSliceProdS
FinProdBounded n = All (GT n)

0 IsFinProdBounded :
  (n : Nat) -> DecSlice {a=FinSliceProdS} (FinProdBounded n)
IsFinProdBounded n = all (isGT n)

0 isFinProdBounded : (n : Nat) -> DecPred FinSliceProdS
isFinProdBounded n = SliceDecPred $ IsFinProdBounded n

FinSliceProd : Nat -> Type
FinSliceProd n = Refinement {a=FinSliceProdS} (isFinProdBounded n)

InterpFSPP : {n : Nat} -> (p : FinSliceProdS) -> (0 _ : FinProdBounded n p) ->
  SliceObj (Fin n) -> Type
InterpFSPP {n} [] i sl = Unit
InterpFSPP {n=Z} (_ :: _) (gt :: _) sl = void $ succNotLTEzero gt
InterpFSPP {n=(S n)} (k :: ks) (_ :: gt) sl =
  (sl $ natToFinLT k, InterpFSPP {n=(S n)} ks gt sl)

InterpFSP : {n : Nat} -> FinSliceProd n -> SliceObj (Fin n) -> Type
InterpFSP {n} p = InterpFSPP {n} (fst0 p) (fromIsYes $ snd0 p)

FinMatrixS : Type
FinMatrixS = List FinSliceProdS

0 FinMatrixBounded : Nat -> SliceObj FinMatrixS
FinMatrixBounded n = All (FinProdBounded n)

0 IsFinMatrixBounded :
  (n : Nat) -> DecSlice {a=FinMatrixS} (FinMatrixBounded n)
IsFinMatrixBounded n = all (IsFinProdBounded n)

0 isFinMatrixBounded : (n : Nat) -> DecPred FinMatrixS
isFinMatrixBounded n = SliceDecPred $ IsFinMatrixBounded n

FinMatrix : Nat -> Type
FinMatrix n = Refinement {a=FinMatrixS} (isFinMatrixBounded n)

0 InterpFSMP : {n : Nat} -> (p : FinMatrixS) -> (0 _ : FinMatrixBounded n p) ->
  SliceObj (Fin n) -> Type
InterpFSMP {n} ps bounded sl =
  Subset0 (Nat, List Nat) $
    \(i, p) =>
      (b : LT i (length ps) **
       InterpFSP {n} (Element0 (index' ps $ natToFinLT i) $
        ?InterpFSMP_hole_pred $ indexAll ?InterpFSMP_hole_elem bounded) sl)

0 InterpFSM : {n : Nat} ->
  (sl : FinMatrix n) -> SliceObj (Fin n) -> Type
InterpFSM {n} sl = InterpFSMP {n} (fst0 sl) (fromIsYes $ snd0 sl)

----------------------------------------
----------------------------------------
---- Finite directed acyclic graphs ----
----------------------------------------
----------------------------------------

public export
FinTopoSort : SliceObj FSObj
FinTopoSort n = Vect n FSObj

public export
record TopoSortedFin where
  constructor TSFin
  tsfVert : FSObj
  tsfSort : FinTopoSort tsfVert

public export
TSFVert : TopoSortedFin -> Type
TSFVert = FSElem . tsfVert

public export
0 tsfOrd : (0 tsf : TopoSortedFin) -> (0 _ : TSFVert tsf) -> FSObj
tsfOrd tsf v = Vect.index v (tsfSort tsf)

public export
0 TSFlt : (0 tsf : TopoSortedFin) -> (0 _, _ : TSFVert tsf) -> Type
TSFlt tsf v v' = LT (tsfOrd tsf v) (tsfOrd tsf v')

-- An edge incoming to the given vertex of a topologically sorted finite graph.
public export
record DAGincE (tsf : TopoSortedFin) (tgt : TSFVert tsf) where
  constructor DAGie
  diSrc : TSFVert tsf
  0 diLT : TSFlt tsf diSrc tgt

public export
record DAGedge (tsf : TopoSortedFin) where
  constructor DAGe
  deTgt : TSFVert tsf
  deEdge : DAGincE tsf deTgt

-- A set of edges incoming to the given vertex of a topologically sorted
-- finite graph.
public export
record DAGincSet (tsf : TopoSortedFin) (tgt : TSFVert tsf) where
  constructor DAGis
  disE : List $ DAGincE tsf tgt

public export
DAGieTV : (tsf : TopoSortedFin) -> Vect (tsfVert tsf) Type
DAGieTV tsf = finFToVect $ DAGincSet tsf

public export
DAGedgeSet : TopoSortedFin -> Type
DAGedgeSet tsf = HVect {n=(tsfVert tsf)} (DAGieTV tsf)

public export
record FinDAG where
  constructor FDAG
  fdagVert : TopoSortedFin
  fdagEdge : DAGedgeSet fdagVert

-----------------------------------
-----------------------------------
---- Parameterizations of DAGs ----
-----------------------------------
-----------------------------------

mutual
  public export
  record TSFParam (tssf : TopoSortedFin) where
    constructor TSFP
    -- tsfpV : HVect {k=(tsfVert tsf)} TFSParam_hole

  public export
  data TSFVertParam : (tsf : TopoSortedFin) -> TSFParam tsf -> Type where

------------------------------
------------------------------
---- List-dependent types ----
------------------------------
------------------------------

public export
partial
data ListIndInd2 : {atom : Type} -> ListF2 atom ->
    (pos : Type) -> (pos -> Type) -> FreeList atom pos -> Type where
  LI2v : {0 atom : Type} -> {0 f2 : ListF2 atom} ->
    {0 pos : Type} -> {0 dir : pos -> Type} ->
    (i : pos) -> dir i ->
    ListIndInd2 {atom} f2 pos dir (IdrisCategories.inFV i)
  LI2c : {0 atom : Type} -> {0 f2 : ListF2 atom} ->
    {0 pos : Type} -> {0 dir : pos -> Type} ->
    (i1 : ListF1 atom $ FreeList atom pos) ->
    f2 (FreeList atom pos) (ListIndInd2 f2 pos dir) IdrisCategories.inFC i1 ->
    ListIndInd2 {atom} f2 pos dir (IdrisCategories.inFC i1)

public export
AListF : Type -> Type -> Type
AListF = Either () .* Pair

public export
AListAlg : Type -> Type -> Type
AListAlg atom x = AListF atom x -> x

public export
AListTypeAlg : Type -> Type
AListTypeAlg atom = AListAlg atom Type

public export
MuAList : Type -> Type
MuAList = Mu . AListF

public export
cataAListF : {0 atom : Type} -> FreeFEval $ AListF atom
cataAListF v a subst alg (InFree x) = case x of
  TFV var => subst var
  TFC l => alg $ case l of
    Left () => Left ()
    Right (MkPair x l') => Right $ MkPair x $ cataAListF v a subst alg l'

public export
AListMuSlice : Type -> Type
AListMuSlice = SliceObj . MuAList

public export
AListTypeMuSlice : {0 atom : Type} -> AListTypeAlg atom -> AListMuSlice atom
AListTypeMuSlice {atom} = cataAListF {atom} Void Type (voidF Type)

public export
0 AListMuPiAlg : {atom : Type} -> AListTypeAlg atom -> Type
AListMuPiAlg = ?AListMuPiAlg_hole

public export
alistMuPi' : {atom : Type} -> (tyalg : AListTypeAlg atom) ->
  (() -> tyalg (Left ())) ->
  ((x : atom) -> (ty : Type) -> ty -> tyalg (Right $ MkPair x ty)) ->
  Pi {a=(MuAList atom)} $ AListTypeMuSlice {atom} tyalg
alistMuPi' {atom} tyalg nalg calg (InFree (TFV v)) = void v
alistMuPi' {atom} tyalg nalg calg (InFree (TFC l)) = case l of
  Left () => nalg ()
  Right (MkPair x l') =>
    calg x (AListTypeMuSlice tyalg l') $ alistMuPi' tyalg nalg calg l'

public export
listMuPi' : {atom : Type} -> (tyalg : ListTypeAlg atom) ->
  tyalg NilF ->
  ((x : atom) -> (ty : Type) -> ty -> tyalg (ConsF x ty)) ->
  Pi {a=(MuList atom)} $ ListTypeMuSlice {atom} tyalg
listMuPi' {atom} tyalg nalg calg (InFree (TFV v)) = void v
listMuPi' {atom} tyalg nalg calg (InFree (TFC l)) = case l of
  NilF => nalg
  ConsF x l' =>
    calg x (ListTypeMuSlice tyalg l') $ listMuPi' tyalg nalg calg l'

public export
0 listMuSliceCata' : {atom : Type} -> (dom, cod : ListTypeAlg atom) ->
  SliceMorphism {a=(MuList atom)} (ListTypeMuSlice dom) (ListTypeMuSlice cod)
listMuSliceCata' {atom} dom cod = ?listMuSliceCata'_hole

--------------------------
--------------------------
---- Matrix interface ----
--------------------------
--------------------------

-- Bounded natural numbers used as list indexes.
public export
ListNI : {0 a : Type} -> List a -> Type
ListNI {a} = Fin . length {a}

-- For any type `a`, given a functor assigning types to terms of `a`,
-- produce a functor assigning types to terms of type `Coproduct (List a)`.
--
-- A functor assigning types to terms of a type `a` may be viewed as an
-- object of the slice category of `Type` over `a`.  Consequently, this
-- assignment itself may be viewed as a natural transformation between functors
-- from `Type` to the two-category of slice categories of `Type`.
public export
CoproductT : NaturalTransformation SliceObj (SliceObj . List)
CoproductT a ta l = Sigma {a=(ListNI l)} (ta . index' {a} l)

public export
showCoprod : {0 a : Type} -> {0 p : a -> Type} -> {l : List a} ->
  ((x : a) -> p x -> String) -> Show (CoproductT a p l)
showCoprod {a} {p} {l} sh = shfc where
  sfp : {x : a} -> Show (p x)
  sfp {x} = shfp where
    [shfp] Show (p x) where
      show = sh x

  sfpi : {i : ListNI l} -> Show (p (index' l i))
  sfpi {i} = sfp {x=(index' l i)}

  [shfc] Show (CoproductT a p l) where
    show = showDP show $ \i => let _ = sfpi {i} in show

-- For any type `a`, given a functor assigning types to terms of `a`,
-- produce a functor assigning types to terms of type `Product (List a)`.
--
-- A functor assigning types to terms of a type `a` may be viewed as an
-- object of the slice category of `Type` over `a`.  Consequently, this
-- assignment itself may be viewed as a natural transformation between functors
-- from `Type` to the two-category of slice categories of `Type`.
public export
ProductT : NaturalTransformation SliceObj (SliceObj . List)
ProductT a ta = All {a} ta

public export
showAll : {0 a : Type} -> {0 p : a -> Type} -> ((x : a) -> p x -> String) ->
  (l : List a) -> All (Show . p) l
showAll {a} {p} sh [] = Nil
showAll {a} {p} sh (x :: l') = shf :: showAll sh l' where
  [shf] Show (p x) where
    show = sh x

public export
showProd : {0 a : Type} -> {0 p : a -> Type} -> {l : List a} ->
  ((x : a) -> p x -> String) -> Show (ProductT a p l)
showProd {a} {p} {l} sh = shfp where
  sfp : All p l -> String
  sfp = let _ : All (Show . p) l = showAll {a} {p} sh l in show

  [shfp] Show (All p l) where
    show = sfp

-- Functor which takes a type to a (two-dimensional) matrix of terms of
-- that type.
public export
MatrixF : Type -> Type
MatrixF = List . List

-- For any type `a`, given a functor assigning types to terms of `a`, produce
-- a functor assigning types to terms of type `MatrixF a`.
--
-- A functor assigning types to terms of a type `a` may be viewed as an
-- object of the slice category of `Type` over `a`.  Consequently, this
-- functor itself may be viewed as a natural transformation between functors
-- from `Type` to the two-category of slice categories of `Type`.
public export
MatrixT : NaturalTransformation SliceObj (SliceObj . MatrixF)
MatrixT = vcompNT (whiskerLeft CoproductT List) ProductT

public export
showMatrixT : {0 a : Type} -> {0 p : a -> Type} -> {m : MatrixF a} ->
  ((x : a) -> p x -> String) -> MatrixT a p m -> String
showMatrixT {m} shp = shm where
  sh : {n : ListNI m} -> Show (All p (index' m n))
  sh {n} = showProd {a} {p} {l=(index' m n)} shp

  [shdp] Show (DPair (ListNI m) (All p . index' m)) where
    show = showDP show $ \n => let _ = sh {n} in show

  shm : MatrixT a p m -> String
  shm = let _ = shdp in show

public export
NatMatrix : Type
NatMatrix = MatrixF Nat

-- Given a matrix of natural numbers, produce a type whose terms are
-- coproducts-of-products-of-`Fin n` (where the matrix determines the `n`s).
public export
FinMatrixT : NatMatrix -> Type
FinMatrixT = MatrixT Nat Fin

public export
showFinMatrixT : {m : NatMatrix} -> FinMatrixT m -> String
showFinMatrixT {m} = showMatrixT {a=Nat} {p=Fin} {m} (\_ => show)

public export
(m : NatMatrix) => Show (FinMatrixT m) where
  show {m} = showFinMatrixT {m}

public export
MkMaybeAllFin : List Nat -> (l : List Nat) -> Maybe (All Fin l)
MkMaybeAllFin ns [] = Just Nil
MkMaybeAllFin [] (_ :: _) = Nothing
MkMaybeAllFin (n :: ns) (k :: ks) = case (natToFin n k, MkMaybeAllFin ns ks) of
  (Just i, Just ks') => Just (i :: ks')
  _ => Nothing

public export
MkMaybeFinMatrixT : (m : NatMatrix) -> Nat -> List Nat -> Maybe (FinMatrixT m)
MkMaybeFinMatrixT m n l = case natToFin n (length m) of
  Just i => case MkMaybeAllFin l (index' m i) of
    Just l' => Just (i ** l')
    Nothing => Nothing
  Nothing => Nothing

public export
MkFinMatrixT : (m : NatMatrix) -> (n : Nat) -> (l : List Nat) ->
  {auto ok : IsJustTrue (MkMaybeFinMatrixT m n l)} -> FinMatrixT m
MkFinMatrixT m n l {ok} = fromIsJust ok

----------------------------------------
----------------------------------------
---- Finite directed acyclic graphs ----
----------------------------------------
----------------------------------------

-- A representation of a finite topologically-sorted set -- a list of
-- equivalence classes, each represented by its cardinality.
public export
FinTSort : Type
FinTSort = List Nat

-- A level of the given topological sort.
public export
FinTSLevel : FinTSort -> Type
FinTSLevel = ListNI {a=Nat}

-- A level other than the lowest of the given topological sort.
public export
FinTSInnerLevel : FinTSort -> Type
FinTSInnerLevel = Fin . pred . length

-- An inner (non-lowest) level of a topological sort viewed as an
-- unconstrained level.
public export
FinTSWeaken : SliceMorphism {a=FinTSort} FinTSInnerLevel FinTSLevel
FinTSWeaken [] lev = absurd lev
FinTSWeaken (_ :: _) lev = weaken lev

-- A node of a DAG at the given level of a topological sort.
public export
FinSortNode : (ts : FinTSort) -> FinTSLevel ts -> Type
FinSortNode ts lev = Fin $ index' ts lev

-- A node of a DAG at the given level, which is not the lowest, of the given
-- topological sort.
public export
FinSortInnerNode : (ts : FinTSort) -> FinTSInnerLevel ts -> Type
FinSortInnerNode ts = FinSortNode ts . FinTSWeaken ts

-- A node of a DAG whose representation uses the above representation of
-- a topological sort.
public export
FinDAGNode : FinTSort -> Type
FinDAGNode ts = Sigma {a=(FinTSLevel ts)} $ FinSortNode ts

-- A representation of an edge of a DAG, pointing from a lower-numbered level
-- to a higher-numbered level in the given topological sort.  The parameter
-- is the lower-numbered level.
public export
0 FinDAGEdge : (ts : FinTSort) -> FinTSInnerLevel ts -> Type
FinDAGEdge ts lev = ?FinDAGEdge_hole

-- A representation of a finite directed acyclic (multi)graph (DAG) -- a list of
-- edges each of which points from a lower-numbered level to a higher-numbered
-- level in the given topological sort.
public export
0 FinDAG' : FinTSort -> Type
FinDAG' = ?FinDAG_hole

----------------------------------------------------
----------------------------------------------------
---- Coproduct-of-product types (finitary ADTs) ----
----------------------------------------------------
----------------------------------------------------

-- A family of `n` finite ADTs.
public export
FinPCTfam : FSObj -> Type
FinPCTfam Z = Unit
FinPCTfam (S n) = List $ List $ Either Nat $ Fin n

-- A family of `n` potentially-infinite ADTs.
public export
PCTfam : FSObj -> Type
PCTfam n = Vect n $ List $ Fin n

public export
FSSlicePF : FSObj -> FSObj -> Type
FSSlicePF dom cod = Vect cod (List $ List $ Fin dom)

---------------------------------
---------------------------------
---- Terms of core Geb logic ----
---------------------------------
---------------------------------

-------------------
---- Structure ----
-------------------

mutual
  public export
  data GebCatTerm : Type where

  public export
  data GebObjTerm : Type where

  public export
  data GebMorphTerm : Type where

-------------------
---- Utilities ----
-------------------

mutual
  public export
  Show GebCatTerm where
    show _ impossible

  public export
  Show GebObjTerm where
    show _ impossible

  public export
  Show GebMorphTerm where
    show _ impossible

---------------------
---- Typechecker ----
---------------------

mutual
  public export
  0 checkGebCatTerm :
    GebCatTerm -> Bool
  checkGebCatTerm _ impossible

  public export
  0 checkGebObjTerm :
    GebCatTerm -> GebObjTerm -> Bool
  checkGebObjTerm _ impossible

  public export
  0 checkGebMorphTerm :
    GebCatTerm -> GebObjTerm -> GebObjTerm -> GebMorphTerm -> Bool
  checkGebMorphTerm _ impossible

-------------------------------------------------------
-------------------------------------------------------
---- Idris denotational semantics and verification ----
-------------------------------------------------------
-------------------------------------------------------

--------------------------------------
---- Typechecker self-consistency ----
--------------------------------------

mutual
  public export
  0 goSigConsis : (c : GebCatTerm) -> (o : GebObjTerm) ->
    IsTrue (checkGebObjTerm c o) -> IsTrue (checkGebCatTerm c)
  goSigConsis _ _ _ impossible

  public export
  0 gmSigConsisCat :
    (c : GebCatTerm) -> (dom, cod : GebObjTerm) -> (m : GebMorphTerm) ->
    IsTrue (checkGebMorphTerm c dom cod m) -> IsTrue (checkGebCatTerm c)
  gmSigConsisCat _ _ _ impossible

  public export
  0 gmSigConsisDom :
    (c : GebCatTerm) -> (dom, cod : GebObjTerm) -> (m : GebMorphTerm) ->
    IsTrue (checkGebMorphTerm c dom cod m) -> IsTrue (checkGebObjTerm c dom)
  gmSigConsisDom _ _ _ impossible

  public export
  0 gmSigConsisCod :
    (c : GebCatTerm) -> (dom, cod : GebObjTerm) -> (m : GebMorphTerm) ->
    IsTrue (checkGebMorphTerm c dom cod m) -> IsTrue (checkGebObjTerm c cod)
  gmSigConsisCod _ _ _ impossible

  public export
  0 gmSigConsisDomCod :
    (c : GebCatTerm) -> (dom, cod : GebObjTerm) -> (m : GebMorphTerm) ->
    IsTrue (checkGebObjTerm c dom) -> IsTrue (checkGebObjTerm c cod)
  gmSigConsisDomCod _ _ _ impossible

  public export
  0 gmSigConsisCodDom :
    (c : GebCatTerm) -> (dom, cod : GebObjTerm) -> (m : GebMorphTerm) ->
    IsTrue (checkGebObjTerm c cod) -> IsTrue (checkGebObjTerm c dom)
  gmSigConsisCodDom _ _ _ impossible

---------------------------
---- Typechecked terms ----
---------------------------

public export
GebCat : Type
GebCat = Refinement {a=GebCatTerm} checkGebCatTerm

public export
gcTerm : GebCat -> GebCatTerm
gcTerm = shape

public export
GebObjSigTerm : Type
GebObjSigTerm = (GebCatTerm, GebObjTerm)

public export
0 checkGebObjSigTerm : GebObjSigTerm -> Bool
checkGebObjSigTerm = uncurry checkGebObjTerm

public export
GebObj : Type
GebObj = Refinement {a=GebObjSigTerm} checkGebObjSigTerm

public export
goSigTerm : GebObj -> GebObjSigTerm
goSigTerm = shape

public export
goObjTerm : GebObj -> GebObjTerm
goObjTerm = snd . goSigTerm

public export
goCatTerm : GebObj -> GebCatTerm
goCatTerm = fst . goSigTerm

public export
GebMorphSigTerm : Type
GebMorphSigTerm = (GebCatTerm, GebObjTerm, GebObjTerm, GebMorphTerm)

public export
0 checkGebMorphSigTerm : GebMorphSigTerm -> Bool
checkGebMorphSigTerm (c, dom, cod, m) = checkGebMorphTerm c dom cod m

public export
GebMorph : Type
GebMorph = Refinement {a=GebMorphSigTerm} checkGebMorphSigTerm

public export
goCat : GebObj -> GebCat
goCat (Element0 (c, o) p) = Element0 c $ goSigConsis c o p

public export
gmCat : GebMorph -> GebCat
gmCat (Element0 (c, dom, cod, m) p) = Element0 c $ gmSigConsisCat c dom cod m p

public export
gmDom : GebMorph -> GebObj
gmDom (Element0 (c, dom, cod, m) p) =
  Element0 (c, dom) $ gmSigConsisDom c dom cod m p

public export
gmCod : GebMorph -> GebObj
gmCod (Element0 (c, dom, cod, m) p) =
  Element0 (c, cod) $ gmSigConsisCod c dom cod m p

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
---- Idris evaluator (operational semantics) -- for some categories only ----
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

----------------------------------------------
----------------------------------------------
---- Dependent bifunctors and profunctors ----
----------------------------------------------
----------------------------------------------

public export
SliceBifunctor : Type -> Type -> Type -> Type
SliceBifunctor c d e = SliceObj c -> SliceObj d -> SliceObj e

public export
SliceEndoBifunctor : Type -> Type
SliceEndoBifunctor e = SliceBifunctor e e e

public export
SliceProfunctor : Type -> Type -> Type -> Type
SliceProfunctor = SliceBifunctor

public export
SliceEndoProfunctor : Type -> Type
SliceEndoProfunctor = SliceEndoBifunctor

---------------------------------------------------------
---------------------------------------------------------
---- Dependent polynomial bifunctors and profunctors ----
---------------------------------------------------------
---------------------------------------------------------

public export
SliceObjEither : {0 param : Type} ->
  (dom, cod : SliceObj param) -> SliceObj param
SliceObjEither {param} dom cod ep = SliceObj (Either (dom ep) (cod ep))

-- A dependent polynomial functor is defined between slice categories --
-- `Type/dom` -> `Type/cod`.  A dependent polynomial (non-enriched)
-- profunctor, therefore, should be from `Type/dom -> Type/cod -> Type`.
--
-- However, we can add further dependency by defining in effect a family
-- of profunctors indexed by a type `param`, where each of the domain, codomain,
-- and enriching categories depend on `param`.
public export
DepProfunctor : {param : Type} -> (dom, cod, enr : SliceObj param) -> Type
DepProfunctor {param} dom cod enr =
  SliceMorphism {a=param} (SliceObjEither {param} dom cod) enr

public export
record DepArena (0 dom, cod : Type) where
  constructor DepAr
  darPos : SliceObj cod
  darDir : (elcod : cod) -> darPos elcod -> SliceObj dom

public export
InterpDepArGen : {dom, cod : Type} ->
  SliceBifunctor dom dom cod ->
  DepArena dom cod -> SliceFunctor dom cod
InterpDepArGen {dom} {cod} bf dar domsl elcod =
  (pos : darPos dar elcod ** bf (darDir dar elcod pos) domsl elcod)

public export
InterpDepAr : {dom, cod : Type} ->
  (dom -> cod -> Type -> Type -> Type) ->
  DepArena dom cod -> SliceFunctor dom cod
InterpDepAr {dom} {cod} bf dar domsl elcod =
  (pos : darPos dar elcod **
  (eldom : dom) -> bf eldom elcod (darDir dar elcod pos eldom) (domsl eldom))

public export
InterpDepArPoly : {dom, cod : Type} ->
  DepArena dom cod -> SliceFunctor dom cod
InterpDepArPoly = InterpDepAr $ \_, _ => HomProf

public export
depArPolyMap : {dom, cod : Type} -> (dar : DepArena dom cod) ->
  {x, y : SliceObj dom} ->
  SliceMorphism {a=dom} x y ->
  SliceMorphism {a=cod}
    (InterpDepArPoly {dom} {cod} dar x) (InterpDepArPoly {dom} {cod} dar y)
depArPolyMap {dom} {cod} dar {x} {y} m elcod fx =
  (fst fx ** sliceComp m (snd fx))

public export
InterpDepArDirich : {dom, cod : Type} ->
  DepArena dom cod -> SliceFunctor dom cod
InterpDepArDirich = InterpDepAr $ \_, _ => OpHomProf

public export
depArDirichContramap : {dom, cod : Type} -> (dar : DepArena dom cod) ->
  {x, y : SliceObj dom} ->
  SliceMorphism {a=dom} y x ->
  SliceMorphism {a=cod}
    (InterpDepArDirich {dom} {cod} dar x) (InterpDepArDirich {dom} {cod} dar y)
depArDirichContramap {dom} {cod} dar {x} {y} m elcod fx =
  (fst fx ** sliceComp (snd fx) m)

public export
DepCopArena : (0 dom1, dom2, cod : Type) -> Type
DepCopArena dom1 dom2 cod = DepArena (Either dom1 dom2) cod

public export
InterpDepCopAr : {dom1, dom2, cod : Type} ->
  (dom1 -> cod -> Type -> Type -> Type) ->
  (dom2 -> cod -> Type -> Type -> Type) ->
  DepCopArena dom1 dom2 cod -> SliceBifunctor dom1 dom2 cod
InterpDepCopAr {dom1} {dom2} {cod} bf1 bf2 dbar dom1sl dom2sl =
  InterpDepAr {dom=(Either dom1 dom2)} {cod} (eitherElim bf1 bf2) dbar $
    eitherElim dom1sl dom2sl

public export
InterpDepCopArCovarPoly : {dom1, dom2, cod : Type} ->
  DepCopArena dom1 dom2 cod -> SliceBifunctor dom1 dom2 cod
InterpDepCopArCovarPoly {dom1} {dom2} {cod} =
  InterpDepCopAr (\_, _ => HomProf) (\_, _ => HomProf)

public export
depCopArCovarPolyMap : {dom1, dom2, cod : Type} ->
  (dar : DepCopArena dom1 dom2 cod) ->
  {x1, y1 : SliceObj dom1} ->
  {x2, y2 : SliceObj dom2} ->
  SliceMorphism {a=(Either dom1 dom2)} (eitherElim x1 x2) (eitherElim y1 y2) ->
  SliceMorphism {a=cod}
    (InterpDepCopArCovarPoly {dom1} {dom2} {cod} dar x1 x2)
    (InterpDepCopArCovarPoly {dom1} {dom2} {cod} dar y1 y2)
depCopArCovarPolyMap {dom1} {dom2} {cod} dar m elcod (pos ** dirmap) =
  (pos **
   \eldom => case eldom of
    Left ell => m (Left ell) . dirmap (Left ell)
    Right elr => m (Right elr) . dirmap (Right elr))

public export
InterpDepCopArPolyProf : {dom1, dom2, cod : Type} ->
  DepCopArena dom1 dom2 cod -> SliceProfunctor dom1 dom2 cod
InterpDepCopArPolyProf {dom1} {dom2} {cod} =
  InterpDepCopAr (\_, _ => OpHomProf) (\_, _ => HomProf)

public export
depCopArPolyProfDimap : {dom1, dom2, cod : Type} ->
  (dar : DepCopArena dom1 dom2 cod) ->
  {x1, y1 : SliceObj dom1} ->
  {x2, y2 : SliceObj dom2} ->
  SliceMorphism {a=(Either dom1 dom2)} (eitherElim y1 x2) (eitherElim x1 y2) ->
  SliceMorphism {a=cod}
    (InterpDepCopArPolyProf {dom1} {dom2} {cod} dar x1 x2)
    (InterpDepCopArPolyProf {dom1} {dom2} {cod} dar y1 y2)
depCopArPolyProfDimap {dom1} {dom2} {cod} dar m elcod (pos ** dirmap) =
  (pos **
   \eldom => case eldom of
    Left ell => dirmap (Left ell) . m (Left ell)
    Right elr => m (Right elr) . dirmap (Right elr))

public export
DepProdArena : (0 dom, cod1, cod2 : Type) -> Type
DepProdArena dom cod1 cod2 = DepArena dom (Pair cod1 cod2)

public export
InterpDepProdAr : {dom, cod1, cod2 : Type} ->
  (dom -> (cod1, cod2) -> Type -> Type -> Type) ->
  DepProdArena dom cod1 cod2 -> SliceFunctor dom (cod1, cod2)
InterpDepProdAr {dom} {cod1} {cod2} pf dbar =
  InterpDepAr {dom} {cod=(Pair cod1 cod2)} pf dbar

public export
InterpDepProdArPair : {dom, cod1, cod2 : Type} ->
  DepProdArena dom cod1 cod2 -> SliceFunctor dom (cod1, cod2)
InterpDepProdArPair {dom} {cod1} {cod2} =
  InterpDepProdAr (\_, (_, _) => Pair)

public export
depProdArPairMap : {dom, cod1, cod2 : Type} ->
  (dar : DepProdArena dom cod1 cod2) ->
  {x, y : SliceObj dom} ->
  SliceMorphism {a=dom} x y ->
  SliceMorphism {a=(cod1, cod2)}
    (InterpDepProdArPair {dom} {cod1} {cod2} dar x)
    (InterpDepProdArPair {dom} {cod1} {cod2} dar y)
depProdArPairMap {dom} {cod1} {cod2} dar m (elcod1, elcod2) fx =
  (fst fx ** \eldom => mapSnd (m eldom) (snd fx eldom))

public export
InterpDepProdArCovarHom : {dom, cod1, cod2 : Type} ->
  DepProdArena dom cod1 cod2 -> SliceFunctor dom (cod1, cod2)
InterpDepProdArCovarHom {dom} {cod1} {cod2} =
  InterpDepProdAr (\_, (_, _) => HomProf)

public export
depProdArHomMap : {dom, cod1, cod2 : Type} ->
  (dar : DepProdArena dom cod1 cod2) ->
  {x, y : SliceObj dom} ->
  SliceMorphism {a=dom} x y ->
  SliceMorphism {a=(cod1, cod2)}
    (InterpDepProdArCovarHom {dom} {cod1} {cod2} dar x)
    (InterpDepProdArCovarHom {dom} {cod1} {cod2} dar y)
depProdArHomMap {dom} {cod1} {cod2} dar m (elcod1, elcod2) fx =
  (fst fx ** \eldom, ely => m eldom $ snd fx eldom ely)

public export
InterpDepProdArContraHom : {dom, cod1, cod2 : Type} ->
  DepProdArena dom cod1 cod2 -> SliceFunctor dom (cod1, cod2)
InterpDepProdArContraHom {dom} {cod1} {cod2} =
  InterpDepProdAr (\_, (_, _) => OpHomProf)

public export
depProdArHomContramap : {dom, cod1, cod2 : Type} ->
  (dar : DepProdArena dom cod1 cod2) ->
  {x, y : SliceObj dom} ->
  SliceMorphism {a=dom} y x ->
  SliceMorphism {a=(cod1, cod2)}
    (InterpDepProdArContraHom {dom} {cod1} {cod2} dar x)
    (InterpDepProdArContraHom {dom} {cod1} {cod2} dar y)
depProdArHomContramap {dom} {cod1} {cod2} dar m (elcod1, elcod2) fx =
  (fst fx ** \eldom, ely => snd fx eldom $ m eldom ely)

-----------------------------------------------
-----------------------------------------------
---- Polynomial profunctors and categories ----
-----------------------------------------------
-----------------------------------------------

-----------------------------------------------
---- Polynomial endo-profunctors on `Type` ----
-----------------------------------------------

public export
PolyProfData : Type
PolyProfData = (pos : Type ** Either pos pos -> Type)

public export
InterpPolyProfData : PolyProfData -> ProfunctorSig
InterpPolyProfData ppd x y =
  (p : fst ppd ** PrePostPair (snd ppd $ Left p) (snd ppd $ Right p) x y)

public export
ppdDimap : (ppd : PolyProfData) -> DimapSig (InterpPolyProfData ppd)
ppdDimap ppd mca mbd pab =
  (fst pab ** (fst (snd pab) . mca, mbd . snd (snd pab)))

-- This position (together with the direction below) makes `HomProf` into a
-- polynomial by turning its interpretation into `CoProYo`.
--
-- These positions are, I believe, the objects of the category of elements
-- of `HomProf`.
public export
HomProfPolyPos : Type
HomProfPolyPos = (ab : (Type, Type) ** fst ab -> snd ab)

public export
HomProfPolyDir1 : HomProfPolyPos -> Type
HomProfPolyDir1 = fst . fst

public export
HomProfPolyDir2 : HomProfPolyPos -> Type
HomProfPolyDir2 = snd . fst

public export
HomProfPolyDir : Either HomProfPolyPos HomProfPolyPos -> Type
HomProfPolyDir = eitherElim HomProfPolyDir1 HomProfPolyDir2

public export
HomProfPolyData : PolyProfData
HomProfPolyData = (HomProfPolyPos ** HomProfPolyDir)

public export
HomProfToPoly : ProfNT HomProf (InterpPolyProfData HomProfPolyData)
HomProfToPoly {a} {b} mab = (((a, b) ** mab) ** (id, id))

public export
HomProfFromPoly : ProfNT (InterpPolyProfData HomProfPolyData) HomProf
HomProfFromPoly {a} {b} pab = snd (snd pab) . snd (fst pab) . fst (snd pab)

public export
HomProfToFromPolyId : {a, b : Type} ->
  (mab : HomProf a b) ->
  ProfNTcomp
     {p=HomProf}
     {q=(InterpPolyProfData HomProfPolyData)}
     {r=HomProf}
    HomProfFromPoly HomProfToPoly {a} {b}
    mab =
  mab
HomProfToFromPolyId {a} {b} mab = Refl

{- This dictates an equivalence relation that we could use in a logic
 - with quotient types.
public export
HomProfFromToPolyId : {a, b : Type} ->
  (mab : InterpPolyProfData HomProfPolyData a b) ->
  ProfNTcomp
     {p=(InterpPolyProfData HomProfPolyData)}
     {q=HomProf}
     {r=(InterpPolyProfData HomProfPolyData)}
    HomProfToPoly HomProfFromPoly {a} {b}
    mab =
  mab
HomProfFromToPolyId {a} {b} ((cd ** mcd) ** (mac, mdb)) =
  HomProfFromToPolyId_hole
-}

public export
CatToPolyProfPos : SCat -> Type
CatToPolyProfPos = scObj

public export
CatToPolyProfDir :
  (sc : SCat) -> Either (CatToPolyProfPos sc) (CatToPolyProfPos sc) -> Type
CatToPolyProfDir sc = eitherElim
  (Sigma {a=(scObj sc)} . curry (scHom sc))
  (Sigma {a=(scObj sc)} . flip (curry (scHom sc)))

public export
CatToPolyProf : SCat -> PolyProfData
CatToPolyProf sc = (CatToPolyProfPos sc ** CatToPolyProfDir sc)

-----------------------------------------------------
---- Category/polynomial-promonad correspondence ----
-----------------------------------------------------

public export
0 FMapSig : (Type -> Type) -> Type
FMapSig f = {0 a, b : Type} -> (a -> b) -> f a -> f b

public export
0 FContramapSig : (Type -> Type) -> Type
FContramapSig f = {0 a, b : Type} -> (b -> a) -> f a -> f b

-- See https://ncatlab.org/nlab/show/profunctor#definition

-- The representable profunctor from `Type^op x Type` to `Type` (also
-- written `Type -|-> Type`) induced by the given functor from `Type` to
-- `Type`.  Called `D(1, f)` on the above page.
public export
RepProf : (Type -> Type) -> ProfunctorSig
RepProf f d c = d -> f c

public export
repProfDimap : {0 f : Type -> Type} -> FMapSig f -> DimapSig (RepProf f)
repProfDimap {f} fm mca mbd mafb = fm mbd . mafb . mca

public export
Functor f => Profunctor (RepProf f) where
  dimap = repProfDimap {f} (map {f})

-- The (co-)representable profunctor from `Type x Type^op` to `Type`
-- (also written `Type^op -|-> Type^op`) induced by the given functor from
-- `Type` to `Type`.  Called `D(f, 1)` on the above page.
public export
CorepProf : (Type -> Type) -> ProfunctorSig
CorepProf f c d = f c -> d

public export
corepProfDimap : {0 f : Type -> Type} -> FMapSig f -> DimapSig (CorepProf f)
corepProfDimap {f} fm mca mbd mfab = mbd . mfab . fm mca

public export
Functor f => Profunctor (CorepProf f) where
  dimap = corepProfDimap {f} (map {f})

public export
FunctorFam : Type
FunctorFam = (pos : Type ** pos -> Type -> Type)

public export
FFPos : FunctorFam -> Type
FFPos = fst

public export
FFDir : (ff : FunctorFam) -> FFPos ff -> Type -> Type
FFDir = snd

public export
0 FFMapSig : FunctorFam -> Type
FFMapSig ff = (pos : FFPos ff) -> FMapSig (FFDir ff pos)

public export
SumRepProf : FunctorFam -> ProfunctorSig
SumRepProf ff d c = (pos : FFPos ff ** RepProf (FFDir ff pos) d c)

public export
sumRepProfDimap : {0 ff : FunctorFam} ->
  FFMapSig ff -> DimapSig (SumRepProf ff)
sumRepProfDimap {ff} ffm mca mbd (pos ** mafb) =
  (pos ** repProfDimap {f=(FFDir ff pos)} (ffm pos) mca mbd mafb)

public export
SumRepProfunctor : {0 ff : FunctorFam} -> (ffm : FFMapSig ff) ->
  Profunctor (SumRepProf ff)
SumRepProfunctor {ff} ffm = MkProfunctor $ sumRepProfDimap {ff} ffm

public export
SumCorepProf : FunctorFam -> ProfunctorSig
SumCorepProf ff c d = (pos : FFPos ff ** CorepProf (FFDir ff pos) c d)

public export
sumCorepProfDimap : {0 ff : FunctorFam} ->
  FFMapSig ff -> DimapSig (SumCorepProf ff)
sumCorepProfDimap {ff} ffm mca mbd (pos ** mfab) =
  (pos ** corepProfDimap {f=(FFDir ff pos)} (ffm pos) mca mbd mfab)

public export
SumCorepProfunctor : {0 ff : FunctorFam} -> (ffm : FFMapSig ff) ->
  Profunctor (SumCorepProf ff)
SumCorepProfunctor {ff} ffm = MkProfunctor $ sumCorepProfDimap {ff} ffm

public export
FunctorFamPair : Type
FunctorFamPair = (FunctorFam, FunctorFam)

public export
FFPcorep : FunctorFamPair -> FunctorFam
FFPcorep = fst

public export
FFPrep : FunctorFamPair -> FunctorFam
FFPrep = snd

public export
0 FFPMapSig : FunctorFamPair -> Type
FFPMapSig ffp = (FFMapSig $ FFPcorep ffp, FFMapSig $ FFPrep ffp)

public export
FFPMcorep : {0 ffp : FunctorFamPair} ->
  FFPMapSig ffp -> FFMapSig (FFPcorep ffp)
FFPMcorep = fst

public export
FFPMrep : {0 ffp : FunctorFamPair} ->
  FFPMapSig ffp -> FFMapSig (FFPrep ffp)
FFPMrep = snd

public export
SumRepCorepProf : FunctorFamPair -> ProfunctorSig
SumRepCorepProf ffp d c =
  Either (SumCorepProf (FFPcorep ffp) d c) (SumRepProf (FFPrep ffp) d c)

public export
sumRepCorepProfDimap : {0 ffp : FunctorFamPair} ->
  FFPMapSig ffp -> DimapSig (SumRepCorepProf ffp)
sumRepCorepProfDimap {ffp} ffpm mca mbd (Left (pos ** mfab)) =
  Left $
    sumCorepProfDimap {ff=(FFPcorep ffp)} (FFPMcorep ffpm) mca mbd (pos ** mfab)
sumRepCorepProfDimap {ffp} ffpm mca mbd (Right (pos ** mafb)) =
  Right $
    sumRepProfDimap {ff=(FFPrep ffp)} (FFPMrep ffpm) mca mbd (pos ** mafb)

public export
SumRepCorepProfunctor : {0 ffp : FunctorFamPair} -> (ffpm : FFPMapSig ffp) ->
  Profunctor (SumRepCorepProf ffp)
SumRepCorepProfunctor {ffp} ffpm =
  MkProfunctor $ sumRepCorepProfDimap {ffp} ffpm

-------------------------------
-------------------------------
---- Finitary copresheaves ----
-------------------------------
-------------------------------

------------------------
---- Finite quivers ----
------------------------

-- A quiver (directed multigraph) internal to FinSet.
record FSQuiv' where
  constructor FSQ'
  fsqVert : Nat
  fsqEdge : Nat
  fsqSrc : Vect fsqEdge (Fin fsqVert)
  fsqTgt : Vect fsqEdge (Fin fsqVert)

-- The signature of endpoints of an edge in or a path through a finite quiver.
record FSQSig (FSQ' : FSQuiv') where
  constructor FSQS
  fsqsDom : Fin (fsqVert FSQ')
  fsqsCod : Fin (fsqVert FSQ')

-- An edge in a finite quiver with the given endpoints.
record FSQEdge (sig : Sigma FSQSig) where
  constructor FSQE
  fsqeE : Fin (fsqEdge (fst sig))
  0 fsqeDom : index fsqeE (fsqSrc (fst sig)) = fsqsDom (snd sig)
  0 fsqeCod : index fsqeE (fsqTgt (fst sig)) = fsqsCod (snd sig)

-- A path through a finite quiver (ordered starting from the target)
-- with the given endpoints.
data FSQPath : SliceObj (Sigma FSQSig) where
  FSQPid : (0 FSQ' : FSQuiv') -> (0 v : Fin (fsqVert FSQ')) ->
    FSQPath (FSQ' ** FSQS v v)
  FSQPcomp : (0 FSQ' : FSQuiv') -> {0 s, v, t : Fin (fsqVert FSQ')} ->
    FSQEdge (FSQ' ** FSQS v t) -> FSQPath (FSQ' ** FSQS s v) ->
    FSQPath (FSQ' ** FSQS s t)

------------------------------------------------
------------------------------------------------
---- Discrete dependent polynomial functors ----
------------------------------------------------
------------------------------------------------

---------------------
---- Definitions ----
---------------------

public export
DiscBaseChange : {dom : Type} -> {0 cod : Type} ->
  (cod -> dom) -> SliceFunctor dom cod
DiscBaseChange {dom} {cod} = (|>)

-- In general, the left Kan extension of `SliceObj dom` (viewed as a functor
-- to `Type` from a discrete category formed from `dom`) along `f` (viewed
-- as a functor between discrete categories formed from `dom` and `cod`).
public export
DiscSigma : {dom : Type} -> {0 cod : Type} ->
  (dom -> cod) -> SliceFunctor dom cod
DiscSigma {dom} {cod} f sld elc = (eld : PreImage f elc ** sld $ fst0 eld)

-- In general, the right Kan extension of `SliceObj dom` (viewed as a functor
-- to `Type` from a discrete category formed from `dom`) along `f` (viewed
-- as a functor between discrete categories formed from `dom` and `cod`).
public export
GenPi : {dom : Type} -> {0 cod : Type} ->
  (dom -> cod) -> SliceFunctor dom cod
GenPi {dom} {cod} f sld elc = (eld : PreImage f elc) -> sld $ fst0 eld

-- We define a discrete dependent product as one which factors through
-- a type of (finite) dependent vectors.
public export
DiscPi : {pos : Type} -> (nfield : pos -> Nat) ->
  SliceFunctor (Sigma {a=pos} (Fin . nfield)) pos
DiscPi {pos} nfield sld i = HVect {n=(nfield i)} $ finFToVect $ sld . MkDPair i

public export
record DiscSlicePolyFunc (dom, cod : Type) where
  constructor MkDSPF
  dspfPos : SliceObj cod
  dspfNField : Sigma {a=cod} dspfPos -> Nat
  dspfFieldTypes : Sigma {a=(Sigma {a=cod} dspfPos)} (Fin . dspfNField) -> dom

public export
interpDSPF : {dom, cod : Type} ->
  DiscSlicePolyFunc dom cod -> SliceObj dom -> SliceObj cod
interpDSPF {dom} {cod} (MkDSPF pos nfield ftypes) =
  DiscBaseChange {dom} {cod=(Sigma {a=(Sigma {a=cod} pos)} (Fin . nfield))}
    ftypes
  |> DiscPi {pos=(Sigma {a=cod} pos)} nfield
  |> DiscSigma {dom=(Sigma {a=cod} pos)} {cod} DPair.fst

-----------------------------------------------------------
---- Relationships with other polynomial-functor forms ----
-----------------------------------------------------------

public export
dspfToWType : {dom, cod : Type} ->
  DiscSlicePolyFunc dom cod -> WTypeFunc dom cod
dspfToWType {dom} {cod} (MkDSPF pos nfield ftypes) =
  MkWTF
    (Sigma {a=cod} pos)
    (Sigma {a=(Sigma {a=cod} pos)} (Fin . nfield))
    ftypes
    DPair.fst
    DPair.fst

public export
dspfToSpf : {dom, cod : Type} ->
  DiscSlicePolyFunc dom cod -> SlicePolyFunc dom cod
dspfToSpf {dom} {cod} (MkDSPF pos nfield ftypes) =
  (pos ** (Fin . nfield) ** ftypes)

----------------------
---- Fixed points ----
----------------------

---------------------------------------
---------------------------------------
---- Polynomial functors on FinSet ----
---------------------------------------
---------------------------------------

-- A slice category is identified by a category together with one of its
-- objects.  In particular, a slice of `FinSet` is identified by an object
-- of `FinSet`, i.e. a natural number.  Similarly, the _opposite_ of a slice
-- category may be identified by the object whose slice category it is the
-- opposite of.  Note that the opposite of a slice category is not (necessarily)
-- equivalent to the coslice category, nor is it (necessarily) equivalent to
-- a slice of the opposite of the base category (although those latter two are
-- equivalent to _each other_) -- although it is equivalent to a coslice of the
-- opposite of the base category!
--
-- The equivalences of categories with the opposite of a slice category in
-- which we are most intereseted are:
--
--  - The subcategory of the polynomial endofunctors on `FinSet` whose
--    position-sets (when we view endofunctors as `FinSet`s dependent on
--    `FinSet`s) are the same as the object being sliced over
--  - The opposite of the subcategory of the Dirichlet endofunctors on `FinSet`
--    whose position-sets (when we view endofunctors as `FinSet`s dependent on
--    `FinSet`s) are the same as the object being sliced over
--  - The (contravariant) presheaf category into `FinSet` resulting from
--    treating the object being sliced over as a discrete category (presheaves
--    in general are sometimes called "generic figures" or "C-sets")
public export
record FinOpSlCat where
  constructor FinOSC
  finOSbase : FSObj

-- A dependent product between opposites of slices of `FinSet` is determined
-- by a morphism from the codomain to the domain.
public export
record FSOpPi (dom, cod : FinOpSlCat) where
  constructor MkFSPi
  fspiMorph : FSMorph (finOSbase cod) (finOSbase dom)

public export
DiscOpFactorization : {pos : Type} -> (nfield : pos -> Nat) -> Type
DiscOpFactorization {pos} = Sigma {a=pos} . (.) Fin

-- We define a discrete dependent product as one which factors through
-- a type of (finite) dependent vectors.  So we insert a discrete-factorization
-- functor into the polynomial-functor "pipeline".
public export
DiscOpFactorize : {pos : Type} -> (nfield : pos -> Nat) ->
  SliceFunctor (DiscOpFactorization {pos} nfield) pos
DiscOpFactorize {pos} nfield sld i =
  HVect {n=(nfield i)} $ finFToVect $ sld . MkDPair i

---------------------------
---------------------------
---- Splices of `Type` ----
---------------------------
---------------------------

-------------------------------
---- Objects and morphisms ----
-------------------------------

public export
data SpliceObj : (j, i : Type) -> Type where
  SplO : {0 j : Type} -> {cobase : SliceObj j} ->
    (sl : SliceObj j) -> (inj : SliceMorphism {a=j} cobase sl) ->
    SpliceObj j (Sigma {a=j} cobase)

SplCosl : {j, i : Type} -> SpliceObj j i -> SliceObj j
SplCosl (SplO {j} {cobase} _ _) = cobase

SplCoTot : {j, i : Type} -> SpliceObj j i -> Type
SplCoTot (SplO {j} {cobase} _ _) = Sigma {a=j} cobase

SplSl : {j, i : Type} -> SpliceObj j i -> SliceObj j
SplSl (SplO {j} sl _) = sl

SplTot : {j, i : Type} -> SpliceObj j i -> Type
SplTot (SplO {j} sl _) = Sigma {a=j} sl

splCoproj : {0 j, i : Type} -> (spl : SpliceObj j i) -> SplCoTot spl -> j
splCoproj (SplO {j} {cobase} _ _) = DPair.fst

splProj : {0 j, i : Type} -> (spl : SpliceObj j i) -> SplTot spl -> j
splProj (SplO {j} sl _) = DPair.fst

splInj : {0 j, i : Type} -> (spl : SpliceObj j i) ->
  SliceMorphism {a=j} (SplCosl spl) (SplSl spl)
splInj (SplO {j} _ inj) = inj

data SpliceMorph : {0 j, i : Type} ->
    SpliceObj j i -> SpliceObj j i -> Type where
  SplM : {0 j : Type} -> {0 slx, sly, cobase : SliceObj j} ->
    (xinj : SliceMorphism {a=j} cobase slx) ->
    (yinj : SliceMorphism {a=j} cobase sly) ->
    (mxy : SliceMorphism {a=j} slx sly) ->
    {auto 0 eq :
      (ej : j) -> (ec : cobase ej) -> mxy ej (xinj ej ec) = yinj ej ec} ->
    SpliceMorph {j} {i=(Sigma {a=j} cobase)}
      (SplO {j} {cobase} slx xinj)
      (SplO {j} {cobase} sly yinj)

spliceMorphDomInj : {0 j, i : Type} -> {splx, sply : SpliceObj j i} ->
  SpliceMorph {j} {i} splx sply ->
  SliceMorphism {a=j} (SplCosl splx) (SplSl splx)
spliceMorphDomInj (SplM xinj _ _) = xinj

spliceMorphCodInj :
  {j : Type} -> {0 i : Type} -> {splx, sply : SpliceObj j i} ->
  SpliceMorph {j} {i} splx sply ->
  SliceMorphism {a=j} (SplCosl sply) (SplSl sply)
spliceMorphCodInj (SplM _ yinj _) = yinj

spliceMorphTot : {0 j, i : Type} -> {splx, sply : SpliceObj j i} ->
  SpliceMorph {j} {i} splx sply ->
  SliceMorphism {a=j} (SplSl splx) (SplSl sply)
spliceMorphTot (SplM _ _ mxy) = mxy

splId : {j : Type} -> {0 i : Type} ->
  (spl : SpliceObj j i) -> SpliceMorph {j} {i} spl spl
splId (SplO {j} {cobase} sl inj) = SplM inj inj (sliceId {a=j} sl)

splComp : {j : Type} -> {0 i : Type} -> {splx, sply, splz : SpliceObj j i} ->
  SpliceMorph {j} {i} sply splz ->
  SpliceMorph {j} {i} splx sply ->
  SpliceMorph {j} {i} splx splz
splComp
  (SplM {slx=sly} {sly=slz} {cobase} yinj zinj myz {eq})
  (SplM {slx} {sly} {cobase} xinj _ mxy {eq=eq'}) =
    SplM xinj zinj (sliceComp {a=j} myz mxy)
      {eq=(\ej, ec => rewrite eq' ej ec in eq ej ec)}

-- Substitute the second parameter into the first.
splObjSubst :
  {0 k : Type} -> {0 j : SliceObj k} -> {i : SliceObj (Sigma {a=k} j)} ->
  SpliceObj (Sigma {a=k} j) (Sigma {a=(Sigma {a=k} j)} i) ->
  SpliceObj k (Sigma {a=k} j) ->
  SpliceObj (Sigma {a=k} j) (Sigma {a=(Sigma {a=k} j)} i)
splObjSubst (SplO slx xinj) (SplO sly yinj) =
  SplO
    (\(ek ** ejk) => (slx (ek ** ejk), sly ek))
    (\(ek ** ejk), ei => (xinj (ek ** ejk) ei, yinj ek ejk))

{-

-------------------------
---- Splice functors ----
-------------------------

public export
SpliceSigma : {i, j, j' : Type} -> (m : j -> j') ->
  SpliceObj j i -> SpliceObj j' i
SpliceSigma {i} {j} {j'} m (SplO x proj inj) = SplO x (m . proj) inj

public export
SpliceCosigma : {i, i', j  : Type} -> (m : i' -> i) ->
  SpliceObj j i -> SpliceObj j i'
SpliceCosigma {i} {i'} {j} m (SplO x proj inj) = SplO x proj (inj . m)

public export
SpliceDibaseChange : {i, i', j, j' : Type} ->
  (mj : j' -> j) ->
  (spl : SpliceObj j i) ->
  (mi : i' -> Pullback {a=j'} {b=i} {c=j} mj (projInj spl)) ->
  SpliceObj j' i'
SpliceDibaseChange {i} {i'} {j} {j'} mj (SplO x proj inj) mi =
  SplO
    (Pullback {a=j'} {b=x} {c=j} mj proj)
    (fst . fst0)
    (\ei' => case mi ei' of Element0 (ej', ei) eq => Element0 (ej', inj ei) eq)

    -}

--------------------------------------------------
--------------------------------------------------
---- Lawvere-style Geb program representation ----
--------------------------------------------------
--------------------------------------------------

--------------------------------
---- Lawvere-style `FinSet` ----
--------------------------------

-- `FinSet`, so far without explicit equalizers or coequalizers, presented
-- in the style of a Lawvere theory.
public export
data FinSetLawObj : Type where
  FSLprod : List FinSetLawObj -> FinSetLawObj
  FSLcoprod : List FinSetLawObj -> FinSetLawObj

public export
FSLinitial : FinSetLawObj
FSLinitial = FSLcoprod []

public export
FSLterminal : FinSetLawObj
FSLterminal = FSLprod []

public export
FSLn : Nat -> FinSetLawObj
FSLn n = FSLcoprod (replicate n FSLterminal)

------------------
---- Ordinals ----
------------------

public export
record FinOrd where
  constructor FO
  FOn : Nat

public export
record OrdW where
  constructor OW

public export
record OrdM where
  constructor OM

public export
data PolyOrdWF : Type where
  POrdWFn : FinOrd -> PolyOrdWF
  POrdWFw : OrdW -> PolyOrdWF

public export
data PolyOrd : Type where
  POrdWF : PolyOrdWF -> PolyOrd
  POrdM : OrdM -> PolyOrd

--------------------------------------------------------------
---- Lawvere-style finitary dependent polynomial functors ----
--------------------------------------------------------------

-- The double category of finitary dependent polynomial functors, presented
-- in the style of a Lawvere theory.

public export
data FinPolyLawVertMorph : FinSetLawObj -> FinSetLawObj -> Type where

public export
data FinPolyLawHorizMorph : FinSetLawObj -> FinSetLawObj -> Type where

public export
data FinPolyLawCell : {0 w, w', z, z' : FinSetLawObj} ->
    FinPolyLawVertMorph w w' -> FinPolyLawVertMorph z z' ->
    FinPolyLawHorizMorph w z -> FinPolyLawHorizMorph w' z' -> Type where

public export
data FPLawEdge : Type where
  FPLEvert : FPLawEdge
  FPLEhoriz : FPLawEdge
  FPLEcell : FPLawEdge

public export
FPLMDom : FPLawEdge -> Type
FPLMDom FPLEvert = (FinSetLawObj, FinSetLawObj)
FPLMDom FPLEhoriz = (FinSetLawObj, FinSetLawObj)
FPLMDom FPLEcell = (FinSetLawObj, FinSetLawObj, FinSetLawObj, FinSetLawObj)

public export
data FinPolyLawMorph : (0 e : FPLawEdge) -> FPLMDom e -> Type where
  FLPMe : {0 w, z : FinSetLawObj} ->
    FinPolyLawVertMorph w z -> FinPolyLawMorph FPLEvert (w, z)
  FLPMh : {0 w, z : FinSetLawObj} ->
    FinPolyLawHorizMorph w z -> FinPolyLawMorph FPLEhoriz (w, z)
  FLPMc : {0 w, w', z, z' : FinSetLawObj} ->
    {0 mvw : FinPolyLawVertMorph w w'} -> {0 mvz : FinPolyLawVertMorph z z'} ->
    {0 mh : FinPolyLawHorizMorph w z} -> {0 mh' : FinPolyLawHorizMorph w' z'} ->
    FinPolyLawCell {w} {w'} {z} {z'} mvw mvz mh mh' ->
    FinPolyLawMorph FPLEcell (w, w', z, z')

------------------------
---- Raw operations ----
------------------------

-- We will interpret a raw operation as a functor from a finite-product
-- category of the raw core category to the raw core category.  The number of
-- products is the number of sorts referenced in the operation.  (The
-- operation itself need not specify a sort -- it might be used by any
-- number of definitions of sorts in the theory as a whole.)
--
-- We bootstrap the implementation by first assuming an interpretation of
-- the raw core category into the metalanguage's `Type`, so our initial
-- interpretation of a raw operation will be as a functor of the form
-- `RawCore^N -> RawCore`.
--
-- Because we're modeling a multi-sorted theory, the arity is not just a
-- number; rather, it's a list of sorts.  So the first parameter here is
-- the number of sorts, and the second is the _length_ of the arity.
public export
RawOp : Nat -> Nat -> Type
RawOp s a = Vect a (Fin s)

-- A convenience for writing raw operations without having to
-- use `Fin` explicitly.
public export
rawOpFromListMaybe : {s, a : Nat} -> List Nat -> Maybe (RawOp s a)
rawOpFromListMaybe {s} {a} ns =
  fromListMaybe {a=Nat} {n=a} ns >>=
  (traverse {a=Nat} {b=(Fin s)} {f=Maybe} {t=(Vect a)} $ \n => natToFin n s)

public export
rawOpFromList : {s, a : Nat} ->
  (ns : List Nat) -> {auto 0 _ : ReturnsJust (rawOpFromListMaybe {s} {a}) ns} ->
  RawOp s a
rawOpFromList = MkMaybe rawOpFromListMaybe

-- A mapping of sorts to concrete types.  This is the interpretation (into
-- the metalanguage) of the domain of the interpretation of the raw operation.
public export
SortInterpretation : Nat -> Type
SortInterpretation = flip Vect Type

public export
SortInterpretationSl : Nat -> Type
SortInterpretationSl = SliceObj . Fin

public export
SortInterpretationToSl :
  {n : Nat} -> SortInterpretation n -> SortInterpretationSl n
SortInterpretationToSl {n} = flip $ index {len=n} {elem=Type}

public export
SortInterpretationFromSl :
  {n : Nat} -> SortInterpretationSl n -> SortInterpretation n
SortInterpretationFromSl {n} = finFToVect {n} {a=Type}

public export
SortMorphism : {s : Nat} ->
  SortInterpretation s -> SortInterpretation s -> Type
SortMorphism {s} sl sl' = HVect {n=s} $ map (uncurry HomProf) $ zip sl sl'

public export
SortMorphismToSl : {s : Nat} -> {sl, sl' : SortInterpretation s} ->
  SortMorphism {s} sl sl' ->
  SliceMorphism {a=(Fin s)}
    (SortInterpretationToSl sl) (SortInterpretationToSl sl')
SortMorphismToSl {s=(S s)} {sl=(ty :: tys)} {sl'=(ty' :: tys')}
  (m :: ms) FZ i =
    m i
SortMorphismToSl {s=(S s)} {sl=(ty :: tys)} {sl'=(ty' :: tys')}
  (m :: ms) (FS k) i =
    SortMorphismToSl {s} {sl=tys} {sl'=tys'} ms k i

public export
SortMorphismFromSl : {s : Nat} -> {sl, sl' : SortInterpretation s} ->
  SliceMorphism {a=(Fin s)}
    (SortInterpretationToSl sl) (SortInterpretationToSl sl') ->
  SortMorphism {s} sl sl'
SortMorphismFromSl {s=Z} {sl=[]} {sl'=[]} m = []
SortMorphismFromSl {s=(S s)} {sl=(ty :: tys)} {sl'=(ty' :: tys')} m =
  m FZ :: SortMorphismFromSl {s} {sl=tys} {sl'=tys'} (\i => m $ FS i)

-- Given a mapping of sorts to concrete types, compute the direction-set
-- of the operation.  This is a discrete representation of it, using a
-- vector of types and a vector of types dependent upon them, as opposed
-- to an explicit pi type.
public export
RawOpDir : {s, a : Nat} ->
  (op : RawOp s a) -> SortInterpretation s -> Vect a Type
RawOpDir {s} {a} op sorts = map (flip index sorts) op

-- Given a mapping of sorts to concrete types, compute an interpretation
-- of the raw operation:  that is, the result of applying the functor
-- to an object of the finite product category -- i.e., to a finite list
-- of types -- to obtain an object of `Type`.
--
-- This interpretation is a discrete 'pi' operation.
public export
InterpRawOpProd : {s, a : Nat} ->
  (op : RawOp s a) -> SortInterpretation s -> Type
InterpRawOpProd {s} {a} op sorts =
  HVect {n=a} $ RawOpDir {s} {a} op sorts

public export
InterpRawOpProdSl : {s, a : Nat} ->
  (op : RawOp s a) -> SortInterpretationSl s -> Type
InterpRawOpProdSl {s} {a} op sorts = Pi {a=(Fin a)} (sorts . flip index op)

public export
InterpRawOpProdToSl : {s, a : Nat} ->
  (op : RawOp s a) -> (sorts : SortInterpretation s) ->
  InterpRawOpProd {s} {a} op sorts ->
  InterpRawOpProdSl {s} {a} op (SortInterpretationToSl sorts)
InterpRawOpProdToSl {s} {a} op sorts v i =
  replace {p=id} (mapIndex {f=(flip index sorts)} op i) $ index i v

public export
InterpRawOpProdFromSl : {s, a : Nat} ->
  (op : RawOp s a) -> (sorts : SortInterpretation s) ->
  InterpRawOpProdSl {s} {a} op (SortInterpretationToSl sorts) ->
  InterpRawOpProd {s} {a} op sorts
InterpRawOpProdFromSl {s} {a=Z} [] sorts sl = []
InterpRawOpProdFromSl {s} {a=(S a)} (i :: v) sorts sl =
  sl FZ :: InterpRawOpProdFromSl {s} {a} v sorts (\ty => sl $ FS ty)

-- This interpretation, dual to `InterpRawOpProd`,  is a discrete
-- 'sigma' operation.
public export
InterpRawOpCop : {s, a : Nat} ->
  (op : RawOp s a) -> SortInterpretation s -> Type
InterpRawOpCop {s} {a} op sorts =
  (i : Fin a ** index i $ RawOpDir {s} {a} op sorts)

public export
InterpRawOpCopSl : {s, a : Nat} ->
  (op : RawOp s a) -> SortInterpretationSl s -> Type
InterpRawOpCopSl {s} {a} op sorts = Sigma {a=(Fin a)} (sorts . flip index op)

public export
InterpRawOpCopToSl : {s, a : Nat} ->
  (op : RawOp s a) -> (sorts : SortInterpretation s) ->
  InterpRawOpCop {s} {a} op sorts ->
  InterpRawOpCopSl {s} {a} op (SortInterpretationToSl sorts)
InterpRawOpCopToSl {s} {a} op sorts (i ** ty) =
  (i ** replace {p=id} (mapIndex {f=(flip index sorts)} op i) ty)

public export
InterpRawOpCopFromSl : {s, a : Nat} ->
  (op : RawOp s a) -> (sorts : SortInterpretation s) ->
  InterpRawOpCopSl {s} {a} op (SortInterpretationToSl sorts) ->
  InterpRawOpCop {s} {a} op sorts
InterpRawOpCopFromSl {s} {a} op sorts (i ** ty) =
  (i ** replace {p=id} (sym (mapIndex {f=(flip index sorts)} op i)) ty)

---------------------------
---- Tagged operations ----
---------------------------

public export
data OpTag : Type where
  OP_PI : OpTag
  OP_SIGMA : OpTag

public export
TaggedRawOp : Nat -> Nat -> Type
TaggedRawOp s a = (OpTag, RawOp s a)

public export
InterpTaggedRawOp : {s, a : Nat} ->
  (op : TaggedRawOp s a) -> SortInterpretation s -> Type
InterpTaggedRawOp {s} {a} (OP_PI, op) = InterpRawOpProd {s} {a} op
InterpTaggedRawOp {s} {a} (OP_SIGMA, op) = InterpRawOpCop {s} {a} op

public export
taggedRawOpFromListMaybe : {s, a : Nat} ->
  OpTag -> List Nat -> Maybe (TaggedRawOp s a)
taggedRawOpFromListMaybe {s} {a} tag ns =
  rawOpFromListMaybe {s} {a} ns >>= pure . MkPair tag

public export
taggedRawOpFromList : {s, a : Nat} ->
  (tag : OpTag) -> (ns : List Nat) ->
  {auto 0 j :
    ReturnsJust (uncurry $ taggedRawOpFromListMaybe {s} {a}) (tag, ns)} ->
  TaggedRawOp s a
taggedRawOpFromList {s} {a} tag ns =
  MkMaybe (uncurry $ taggedRawOpFromListMaybe {s} {a}) (tag, ns)

public export
InterpTaggedRawOpSl : {s, a : Nat} ->
  (op : TaggedRawOp s a) -> SortInterpretationSl s -> Type
InterpTaggedRawOpSl {s} {a} (OP_PI, op) = InterpRawOpProdSl {s} {a} op
InterpTaggedRawOpSl {s} {a} (OP_SIGMA, op) = InterpRawOpCopSl {s} {a} op

public export
InterpTaggedRawOpToSl : {s, a : Nat} ->
  (op : TaggedRawOp s a) -> (sorts : SortInterpretation s) ->
  InterpTaggedRawOp {s} {a} op sorts ->
  InterpTaggedRawOpSl {s} {a} op (SortInterpretationToSl sorts)
InterpTaggedRawOpToSl {s} {a} (OP_PI, v) sorts t =
  InterpRawOpProdToSl {s} {a} v sorts t
InterpTaggedRawOpToSl {s} {a} (OP_SIGMA, v) sorts t =
  InterpRawOpCopToSl {s} {a} v sorts t

public export
InterpTaggedRawOpFromSl : {s, a : Nat} ->
  (op : TaggedRawOp s a) -> (sorts : SortInterpretation s) ->
  InterpTaggedRawOpSl {s} {a} op (SortInterpretationToSl sorts) ->
  InterpTaggedRawOp {s} {a} op sorts
InterpTaggedRawOpFromSl {s} {a} (OP_PI, v) sorts t =
  InterpRawOpProdFromSl {s} {a} v sorts t
InterpTaggedRawOpFromSl {s} {a} (OP_SIGMA, v) sorts t =
  InterpRawOpCopFromSl {s} {a} v sorts t

-------------------------
---- Operation lists ----
-------------------------

public export
TaggedRawOpDP : Nat -> Type
TaggedRawOpDP = DPair Nat . TaggedRawOp

public export
taggedRawOpDPFromListMaybe : {s : Nat} ->
  OpTag -> List Nat -> Maybe (TaggedRawOpDP s)
taggedRawOpDPFromListMaybe {s} tag ns =
  map {f=Maybe} (MkDPair (length ns)) $
  taggedRawOpFromListMaybe {s} {a=(length ns)} tag ns

public export
taggedRawOpDPFromList : {s : Nat} ->
  (tag : OpTag) -> (ns : List Nat) ->
  {auto 0 j :
    ReturnsJust (uncurry $ taggedRawOpDPFromListMaybe {s}) (tag, ns)} ->
  TaggedRawOpDP s
taggedRawOpDPFromList {s} tag ns {j} =
  MkMaybe (uncurry $ taggedRawOpDPFromListMaybe {s}) (tag, ns) {j}

public export
InterpTaggedRawOpDP : {s : Nat} ->
  (op : TaggedRawOpDP s) -> SortInterpretation s -> Type
InterpTaggedRawOpDP {s} op = InterpTaggedRawOp {s} {a=(fst op)} (snd op)

public export
InterpTaggedRawOpDPSl : {s : Nat} ->
  (op : TaggedRawOpDP s) -> SortInterpretationSl s -> Type
InterpTaggedRawOpDPSl {s} op = InterpTaggedRawOpSl {s} {a=(fst op)} (snd op)

public export
InterpTaggedRawOpDPToSl : {s : Nat} ->
  (op : TaggedRawOpDP s) -> (sorts : SortInterpretation s) ->
  InterpTaggedRawOpDP op sorts ->
  InterpTaggedRawOpDPSl op (SortInterpretationToSl sorts)
InterpTaggedRawOpDPToSl {s} (ar ** op) sorts t =
  InterpTaggedRawOpToSl {a=ar} op sorts t

public export
InterpTaggedRawOpDPFromSl : {s : Nat} ->
  (op : TaggedRawOpDP s) -> (sorts : SortInterpretation s) ->
  InterpTaggedRawOpDPSl op (SortInterpretationToSl sorts) ->
  InterpTaggedRawOpDP op sorts
InterpTaggedRawOpDPFromSl {s} (ar ** op) sorts t =
  InterpTaggedRawOpFromSl {a=ar} op sorts t

-- `n` tagged operations with sorts drawn from `Fin s`.
public export
RawOpList : Nat -> Nat -> Type
RawOpList s n = Vect n (TaggedRawOpDP s)

public export
rawOpListFromListMaybe : {s, n : Nat} ->
  List (OpTag, List Nat) -> Maybe (RawOpList s n)
rawOpListFromListMaybe {s} {n} ops =
  fromListMaybe {a=(OpTag, List Nat)} {n} ops >>=
  (traverse {a=(OpTag, List Nat)} {b=(TaggedRawOpDP s)} {f=Maybe} {t=(Vect n)} $
   uncurry $ taggedRawOpDPFromListMaybe {s})

public export
rawOpListFromList : {s, n : Nat} ->
  (ops : List (OpTag, List Nat)) ->
  {auto 0 _ : ReturnsJust (rawOpListFromListMaybe {s} {n}) ops} ->
  RawOpList s n
rawOpListFromList = MkMaybe rawOpListFromListMaybe

public export
InterpRawOpListSl : {s, n : Nat} -> RawOpList s n ->
  SliceFunctor (Fin s) (Fin n)
InterpRawOpListSl {s} {n} ops sorts i =
  InterpTaggedRawOpDPSl {s} (index i ops) sorts

public export
RawEndoOpList : Nat -> Type
RawEndoOpList s = RawOpList s s

public export
InterpRawEndoOpListSl : {s : Nat} -> RawEndoOpList s ->
  SliceFunctor (Fin s) (Fin s)
InterpRawEndoOpListSl {s} = InterpRawOpListSl {s} {n=s}

public export
InterpRawOpList : {s, n : Nat} -> RawOpList s n ->
  SortInterpretation s -> SortInterpretation n
InterpRawOpList {s} {n} ops sorts =
  SortInterpretationFromSl
  $ InterpRawOpListSl {s} {n} ops
  $ SortInterpretationToSl sorts

public export
InterpRawOpListToSl : {s, n : Nat} -> (ops : RawOpList s n) ->
  (sorts : SortInterpretation s) ->
  SliceMorphism {a=(Fin n)}
    (SortInterpretationToSl (InterpRawOpList {s} {n} ops sorts))
    (InterpRawOpListSl {s} {n} ops (SortInterpretationToSl sorts))
InterpRawOpListToSl {s} {n} ops sorts i op =
  rewrite sym
    (finFToVectIdx
      (InterpRawOpListSl {s} {n} ops $ SortInterpretationToSl sorts) i) in
  op

public export
InterpRawOpListFromSl : {s, n : Nat} -> (ops : RawOpList s n) ->
  (sorts : SortInterpretation s) ->
  SliceMorphism {a=(Fin n)}
    (InterpRawOpListSl {s} {n} ops (SortInterpretationToSl sorts))
    (SortInterpretationToSl (InterpRawOpList {s} {n} ops sorts))
InterpRawOpListFromSl {s} {n} ops sorts i op =
  rewrite
    (finFToVectIdx
      (InterpRawOpListSl {s} {n} ops $ SortInterpretationToSl sorts) i) in
  op

public export
InterpRawEndoOpList : {s : Nat} -> RawEndoOpList s ->
  SortInterpretation s -> SortInterpretation s
InterpRawEndoOpList {s} = InterpRawOpList {s} {n=s}

public export
FreeTheorySl : {s : Nat} -> (ops : RawEndoOpList s) ->
  SliceFunctor (Fin s) (Fin s)
FreeTheorySl {s} = SliceFreeM . InterpRawEndoOpListSl {s}

public export
FreeTheory : {s : Nat} -> (ops : RawEndoOpList s) ->
  SortInterpretation s -> SortInterpretation s
FreeTheory {s} ops sorts =
  SortInterpretationFromSl
  $ FreeTheorySl {s} ops
  $ SortInterpretationToSl sorts

public export
FreeTheorySlEq : {s : Nat} -> (ops : RawEndoOpList s) ->
  (sl : SortInterpretation s) -> (i : Fin s) ->
  index i (FreeTheory {s} ops sl) =
    FreeTheorySl ops (SortInterpretationToSl sl) i
FreeTheorySlEq {s} ops sl i =
  finFToVectIdx (FreeTheorySl {s} ops $ SortInterpretationToSl sl) i

public export
InitialTheorySl : {s : Nat} -> (ops : RawEndoOpList s) -> SliceObj (Fin s)
InitialTheorySl {s} = SliceMu . InterpRawEndoOpListSl {s}

public export
CofreeTheorySl : {s : Nat} -> (ops : RawEndoOpList s) ->
  SliceFunctor (Fin s) (Fin s)
CofreeTheorySl {s} = SliceCofreeCM . InterpRawEndoOpListSl {s}

public export
CofreeTheory : {s : Nat} -> (ops : RawEndoOpList s) ->
  SortInterpretation s -> SortInterpretation s
CofreeTheory {s} ops sorts =
  SortInterpretationFromSl
  $ CofreeTheorySl {s} ops
  $ SortInterpretationToSl sorts

public export
CofreeTheorySlEq : {s : Nat} -> (ops : RawEndoOpList s) ->
  (sl : SortInterpretation s) -> (i : Fin s) ->
  index i (CofreeTheory {s} ops sl) =
    CofreeTheorySl ops (SortInterpretationToSl sl) i
CofreeTheorySlEq {s} ops sl i =
  finFToVectIdx (CofreeTheorySl {s} ops $ SortInterpretationToSl sl) i

public export
TerminalTheorySl : {s : Nat} -> (ops : RawEndoOpList s) -> SliceObj (Fin s)
TerminalTheorySl {s} = SliceNu . InterpRawEndoOpListSl {s}

mutual
  public export
  evalTheorySl : {s : Nat} -> (ops : RawEndoOpList s) ->
    SliceFreeFEval (InterpRawEndoOpListSl {s} ops)
  evalTheorySl {s} ops sv sa subst alg i (InSlF i t) =
    case t of
      InSlV vt => subst i vt
      InSlC ct => evalTheoryFSl {s} ops sv sa subst alg i ct

  public export
  evalTheoryFSl : {s : Nat} -> (ops : RawEndoOpList s) ->
    SliceFreeFEvalF (InterpRawEndoOpListSl {s} ops)
  evalTheoryFSl {s} ops sv sa subst alg i ct with (index i ops) proof opeq
    evalTheoryFSl {s} ops sv sa subst alg i ct | (ar ** (OP_PI, op)) =
      alg i $ rewrite opeq in
      \ty => evalTheorySl {s} ops sv sa subst alg (index ty op) (ct ty)
    evalTheoryFSl {s} ops sv sa subst alg i (ty ** t) | (ar ** (OP_SIGMA, op)) =
      alg i $ rewrite opeq in
      (ty ** evalTheorySl {s} ops sv sa subst alg (index ty op) t)

public export
evalTheory : {s : Nat} -> (ops : RawEndoOpList s) ->
  (sv, sa : SortInterpretation s) ->
  SortMorphism {s} sv sa ->
  SliceAlg (InterpRawEndoOpListSl {s} ops) (SortInterpretationToSl sa) ->
  SortMorphism {s} (FreeTheory ops sv) sa
evalTheory {s} ops sv sa subst alg =
  SortMorphismFromSl {s} {sl=(FreeTheory ops sv)} {sl'=sa} $
  \i, x =>
    evalTheorySl {s} ops
      (SortInterpretationToSl sv)
      (SortInterpretationToSl sa)
      (SortMorphismToSl subst)
      alg
      i
      (rewrite sym (FreeTheorySlEq {s} ops sv i) in x)

mutual
  public export
  traceTheorySl : {s : Nat} -> (ops : RawEndoOpList s) ->
    SliceCofreeFTrace (InterpRawEndoOpListSl {s} ops)
  traceTheorySl {s} ops sl sa label coalg i esa =
    InSlCF i $ InSlS (label i esa) $
      traceTheoryFSl {s} ops sl sa label coalg i esa

  public export
  traceTheoryFSl : {s : Nat} -> (ops : RawEndoOpList s) ->
    SliceCofreeFTraceF (InterpRawEndoOpListSl {s} ops)
  traceTheoryFSl {s} ops sl sa label coalg i esa =
    traceOpSl {s} ops sl sa label coalg i (coalg i esa)

  public export
  traceOpSl : {s : Nat} -> (ops : RawEndoOpList s) ->
    (sl, sa : SliceObj (Fin s)) -> SliceMorphism {a=(Fin s)} sa sl ->
    SliceCoalg (InterpRawEndoOpListSl {s} ops) sa ->
    (i : Fin s) -> InterpTaggedRawOpSl (snd (index i ops)) sa ->
    InterpTaggedRawOpSl (snd (index i ops)) (CofreeTheorySl {s} ops sl)
  traceOpSl {s} ops sl sa label coalg i t with (index i ops)
    traceOpSl {s} ops sl sa label coalg i t | (ar ** (OP_PI, op)) =
      \ty => traceTheorySl {s} ops sl sa label coalg (index ty op) $ t ty
    traceOpSl {s} ops sl sa label coalg i (ty ** t) | (ar ** (OP_SIGMA, op)) =
      (ty ** traceTheorySl {s} ops sl sa label coalg (index ty op) t)

public export
traceTheory : {s : Nat} -> (ops : RawEndoOpList s) ->
  (sl, sa : SortInterpretation s) -> SortMorphism {s} sa sl ->
  SliceCoalg (InterpRawEndoOpListSl {s} ops) (SortInterpretationToSl sa) ->
  SortMorphism {s} sa (CofreeTheory {s} ops sl)
traceTheory {s} ops sl sa label coalg =
  SortMorphismFromSl {s} {sl=sa} {sl'=(CofreeTheory ops sl)} $
  \i, x =>
    rewrite CofreeTheorySlEq {s} ops sl i in
    traceTheorySl {s} ops
      (SortInterpretationToSl sl)
      (SortInterpretationToSl sa)
      (SortMorphismToSl label)
      coalg
      i
      x

-------------------------------------------------
-------------------------------------------------
---- Inductive representation of finite DAGs ----
-------------------------------------------------
-------------------------------------------------

-- See https://arxiv.org/abs/1303.0376 .

public export
data FinIdag : SliceObj (Nat, Nat) where
  DAG0 : FinIdag (0, 0)
  DAG1 : FinIdag (1, 1)
  -- This is incomplete.

-----------------------------------------------
-----------------------------------------------
---- Finite directed acyclic graphs (DAGs) ----
-----------------------------------------------
-----------------------------------------------

-- Impose a partial order on a finite set by slicing it into levels.
-- `l` is the number of levels; `k` is the size of the set being ordered.
public export
FSPOrd : Nat -> Nat -> Type
FSPOrd l k = Fin k -> Fin l

public export
0 FSPordMap : {0 l, k : Nat} -> {0 a : Type} ->
  (Fin l -> Fin l -> a) -> FSPOrd l k -> Fin k -> Fin k -> a
FSPordMap {l} {k} cmp ord m n = cmp (ord m) (ord n)

public export
0 FSPltDec : {0 l, k : Nat} -> FSPOrd l k -> Fin k -> Fin k -> Bool
FSPltDec {l} {k} = FSPordMap {l} {k} {a=Bool} (<)

public export
0 FSPgtDec : {0 l, k : Nat} -> FSPOrd l k -> Fin k -> Fin k -> Bool
FSPgtDec {l} {k} = FSPordMap {l} {k} {a=Bool} (>)

public export
0 FSPordDec : {0 l, k : Nat} ->
  (Fin l -> Fin l -> Bool) -> FSPOrd l k -> PrERel (Fin k)
FSPordDec {l} {k} ord cmp mn =
  IsTrue $ FSPordMap {l} {k} {a=Bool} ord cmp (fst mn) (snd mn)

public export
0 FSPlt : {0 l, k : Nat} -> FSPOrd l k -> PrERel (Fin k)
FSPlt {l} {k} = FSPordDec {l} {k} (<)

public export
0 FSPgt : {0 l, k : Nat} -> FSPOrd l k -> PrERel (Fin k)
FSPgt {l} {k} = FSPordDec {l} {k} (>)

public export
FinSig : Nat -> Type
FinSig k = SignatureT (Fin k)

public export
FinDAGsig : {l, k : Nat} -> FSPOrd l k -> Type
FinDAGsig {l} {k} ord = Subset0 (FinSig k) (FSPgt {l} {k} ord)

public export
FinDAGopSig : {l, k : Nat} -> FSPOrd l k -> Type
FinDAGopSig {l} {k} ord = Subset0 (FinSig k) (FSPlt {l} {k} ord)

public export
FinDAGedgeSet : {l, k : Nat} -> (ord : FSPOrd l k) -> Type
FinDAGedgeSet {l} {k} ord = FinDAGsig {l} {k} ord -> Nat

public export
FinDAGopEdgeSet : {l, k : Nat} -> (ord : FSPOrd l k) -> Type
FinDAGopEdgeSet {l} {k} ord = FinDAGopSig {l} {k} ord -> Nat

---------------------------------------------
---------------------------------------------
---- Programmer's FinSet via profunctors ----
---------------------------------------------
---------------------------------------------

public export
coprodHomLift : (Type -> Type -> Type) -> (Type, Type) -> Type -> Type
coprodHomLift =
  covarHomProfuncLift ProductMonad (\x, y => map {f=ProductMonad})
    {a=Type} {b=Type} {c=Type} (\(x, y) => Either x y)

public export
prodHomLift : (Type -> Type -> Type) -> Type -> (Type, Type) -> Type
prodHomLift =
  contravarHomProfuncLift ProductMonad (\x, y => map {f=ProductMonad})
    {a=Type} {b=Type} {c=Type} (\(x, y) => Pair x y)

public export
prodHomLiftCurry : (Type -> Type -> Type) -> (Type, Type) -> Type -> Type
prodHomLiftCurry h (x, y) z = h x (h y z)

------------------------
------------------------
---- Free promonads ----
------------------------
------------------------

public export
data FreePromonad : ProfunctorSig -> ProfunctorSig where
  InFPv : {0 p : ProfunctorSig} -> {0 a, b : Type} ->
    p a b -> FreePromonad p a b
  InFPM : {0 p : ProfunctorSig} -> {0 a, b : Type} ->
    EndoProfCompose p (FreePromonad p) a b -> FreePromonad p a b

public export
Profunctor p => Profunctor (FreePromonad p) where
  dimap {a} {b} {c} {d} mca mbd (InFPv pab) =
    InFPv {p} {a=c} {b=d} $ dimap {f=p} mca mbd pab
  dimap {a} {b} {c} {d} mca mbd (InFPM (i ** (pai, fpib))) =
    InFPM {p} {a=c} {b=d}
      (i ** (dimap {f=p} mca id pai, dimap {f=(FreePromonad p)} id mbd fpib))

public export
data CofreeProcomonad : ProfunctorSig -> ProfunctorSig where
  InFPCM : {0 p : ProfunctorSig} -> {0 a, b : Type} ->
    p a b -> EndoProfCompose p (CofreeProcomonad p) a b ->
    CofreeProcomonad p a b

public export
Profunctor p => Profunctor (CofreeProcomonad p) where
  dimap {a} {b} {c} {d} mca mbd (InFPCM pab (i ** (pai, fpib))) =
    InFPCM {p} {a=c} {b=d}
      (dimap mca mbd pab)
      (i ** (dimap {f=p} mca id pai,
       dimap {f=(CofreeProcomonad p)} id mbd fpib))

----------------------------
----------------------------
---- Coslice categories ----
----------------------------
----------------------------

public export
CCosliceObj : Type -> Type
CCosliceObj c = DPair Type (HomProf c)

public export
CCosliceObjCodomain : {0 c : Type} -> CCosliceObj c -> Type
CCosliceObjCodomain = fst

public export
CCosliceObjMap : {0 c : Type} ->
  (x : CCosliceObj c) -> (c -> CCosliceObjCodomain {c} x)
CCosliceObjMap = snd

public export
CCosliceMorphism : {0 c : Type} -> CCosliceObj c -> CCosliceObj c -> Type
CCosliceMorphism x y =
  Subset0
    (CCosliceObjCodomain x -> CCosliceObjCodomain y)
    (ExtEq (CCosliceObjMap y) . (|>) (CCosliceObjMap x))

public export
CCosliceMorphismMap : {0 c : Type} -> {0 x, y : CCosliceObj c} ->
  CCosliceMorphism {c} x y ->
  CCosliceObjCodomain {c} x -> CCosliceObjCodomain {c} y
CCosliceMorphismMap = fst0

public export
0 CCosliceMorphismEq : {0 c : Type} -> {0 x, y : CCosliceObj c} ->
  (f : CCosliceMorphism {c} x y) ->
  ExtEq
    (CCosliceObjMap {c} y)
    (CCosliceObjMap {c} x |> CCosliceMorphismMap {c} {x} {y} f)
CCosliceMorphismEq = snd0

public export
record ProYoProshf
    (pp : ProfunctorSig -> ProfunctorSig) (p : ProfunctorSig) where
  constructor MkProYoPro
  ProYoProEmbed : (q : ProfunctorSig) ->
    {auto 0 _ : Profunctor q} -> ProfNT p (pp q)

------------------------------
------------------------------
---- Embeddings of `Type` ----
------------------------------
------------------------------

0 MLProfSig : Type
MLProfSig = IntDifunctorSig Type

0 MLDimapSig : MLProfSig -> Type
MLDimapSig = IntEndoDimapSig Type HomProf

MLSliceCatObj : Type -> Type
MLSliceCatObj = CSliceObj

MLSliceCatMor : (c : Type) -> IntDifunctorSig (MLSliceCatObj c)
MLSliceCatMor c = CSliceMorphism {c}

mlSliceCatComp : (c : Type) -> IntCompSig (MLSliceCatObj c) (MLSliceCatMor c)
mlSliceCatComp c x y z = CSliceCompose {c} {u=x} {v=y} {w=z}

MLSliceToTypeAr : Type -> Type
MLSliceToTypeAr = IntArena . MLSliceCatObj

InterpMLSliceToType : (c : Type) -> MLSliceToTypeAr c -> CSliceObj c -> Type
InterpMLSliceToType c = InterpIPFobj (MLSliceCatObj c) (MLSliceCatMor c)

-- We interpret the notion of a polynomial profunctor as a polynomial
-- functor into the category of Dirichlet functors on `Type`.  Thus
-- the positions are drawn from the category of Dirichlet functors.
record MLPolyProfAr where
  constructor MLPProf
  mlppPos : Type
  mlppContraDir : mlppPos -> Type
  mlppCovarDir : (i : mlppPos) -> CSliceObj (mlppContraDir i)

InterpMLPP : MLPolyProfAr -> MLProfSig
InterpMLPP (MLPProf pos contra covar) x y =
  (i : pos ** slx : x -> contra i ** sly : y -> contra i **
   CSliceMorphism {c=(contra i)} (covar i) (y ** sly))

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
---- Experiments with polynomial "difunctors" translated to exponentials ----
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

NAlgF : Type -> Type
NAlgF x = (x, x -> x)

NAlg : Type
NAlg = (x : Type ** NAlgF x)

NAlgPF : MLPolyCatObj
NAlgPF =
  pfProductArena PFIdentityArena (pfHomObj PFIdentityArena PFIdentityArena)

NAlgP : Type
NAlgP = MLPolyCatElemObj NAlgPF

public export
nAlgToP : NAlg -> NAlgP
nAlgToP (x ** (base, ind)) =
  (x ** (((), \() => (() ** \() => Left ())) **
   \y => case y of Left () => base ; Right (() ** (() ** ())) => ind base))

public export
0 nAlgFromP : NAlgP -> NAlg
nAlgFromP (x ** (((), base) ** ind)) with (snd (base ()) ()) proof eq
  nAlgFromP (x ** (((), base) ** ind)) | Left () =
    (x **
     (ind $ Left (), \ex => ind $ Right $ (() ** (() ** rewrite eq in ()))))
  nAlgFromP (x ** (((), base) ** ind)) | Right () =
    ?nAlgFromP_hole

------------------------------------------
------------------------------------------
---- Alternative PolyFunc experiments ----
------------------------------------------
------------------------------------------

PiBC : {w, y : Type} -> (y -> w -> Type) -> SliceFunctor w y
PiBC {w} {y} dir slw ely = SliceMorphism {a=w} (dir ely) slw

PolyProAr' : Type -> Type -> Type
PolyProAr' d c = d -> IntArena c

record PolyProAr (d, c : Type) where
  constructor PPA
  ppaPos : d -> Type
  ppaDir : Sigma {a=d} ppaPos -> c

-- The category of elements of a functor from `Type` to `Type` (or of a
-- functor from `op(Type)` to `Type`).
record MLCatElemObj (f : Type -> Type) where
  constructor MLElObj
  mlcObj : Type
  mlcEl : f mlcObj

-- The data which determine morphisms of the category of elements of a
-- (covariant) endofunctor on `Type`.
record MLCovarCatElemMorData (f : Type -> Type) where
  constructor MLElMor
  mlcDom : MLCatElemObj f
  mlcCodObj : Type
  mlcMor : mlcObj mlcDom -> mlcCodObj

-- The morphisms of the category of elements of a (covariant) endofunctor on
-- `Type`.
data MLCovarCatElemMor : {0 f : Type -> Type} ->
    (fm : {0 a, b : Type} -> (a -> b) -> f a -> f b) ->
    MLCatElemObj f -> MLCatElemObj f -> Type where
  MLCovCEM :
    {0 f : Type -> Type} -> (fm : {0 a, b : Type} -> (a -> b) -> f a -> f b) ->
    (mdata : MLCovarCatElemMorData f) ->
    MLCovarCatElemMor {f} fm
      (mlcDom mdata)
      (MLElObj
        (mlcCodObj mdata)
        (fm {a=(mlcObj (mlcDom mdata))} {b=(mlcCodObj mdata)}
          (mlcMor mdata) (mlcEl (mlcDom mdata))))

-- The data which determine morphisms of the dual category of elements of a
-- (contravariant) endofunctor on `Type`.
record MLContravarCatElemMorData (f : Type -> Type) where
  constructor MLdElMor
  mldcDomObj : Type
  mldcCod : MLCatElemObj f
  mldcMor : mldcDomObj -> mlcObj mldcCod

-- The morphisms of the dual category of elements of a (contravariant)
-- endofunctor on `Type`.
data MLContravarCatElemMor : {0 f : Type -> Type} ->
    (fcm : {0 a, b : Type} -> (b -> a) -> f a -> f b) ->
    MLCatElemObj f -> MLCatElemObj f -> Type where
  MLContraCEM :
    {0 f : Type -> Type} -> (fcm : {0 a, b : Type} -> (b -> a) -> f a -> f b) ->
    (mdata : MLContravarCatElemMorData f) ->
    MLContravarCatElemMor {f} fcm
      (MLElObj
        (mldcDomObj mdata)
        (fcm {a=(mlcObj (mldcCod mdata))} {b=(mldcDomObj mdata)}
          (mldcMor mdata) (mlcEl (mldcCod mdata))))
      (mldcCod mdata)

----------------------------------------
----------------------------------------
---- Covariant slice representables ----
----------------------------------------
----------------------------------------

--------------------
---- Definition ----
--------------------

-- The slice functor from `c` to `Type` which is covariantly represented
-- by the given `SliceObj c`.  (`Type` is isomorphic to `SliceObj Unit`.)
public export
SliceCovarRepF : {c : Type} -> (sc : SliceObj c) -> SliceFunctor c Unit
SliceCovarRepF sa sb () = SliceMorphism sa sb

--------------------------------------------
----- Covariant representable as W-type ----
--------------------------------------------

0 SCovRasWTF : {c : Type} -> (sc : SliceObj c) -> WTypeFunc c Unit
SCovRasWTF {c} sc =
  MkWTF {dom=c} {cod=Unit}
    Unit
    (Sigma {a=c} sc)
    fst
    (const ())
    (id {a=Unit})

scovrToWTF : {c, d : Type} -> (sa : SliceObj c) ->
  SliceNatTrans (SliceCovarRepF {c} sa) (InterpWTF $ SCovRasWTF sa)
scovrToWTF {c} {d} sa sb () mfsa =
  (Element0 () Refl ** \(Element0 (ec ** sea) eq) => mfsa ec sea)

scovrFromWTF : {c, d : Type} -> (sa : SliceObj c) ->
  SliceNatTrans (InterpWTF $ SCovRasWTF sa) (SliceCovarRepF {c} sa)
scovrFromWTF {c} {d} sa sb () (Element0 () eq ** sbd) =
  \ec, sea => sbd $ Element0 (ec ** sea) Refl

---------------------------
---------------------------
---- Dependent product ----
---------------------------
---------------------------

---------------------------------------------
---- Dependent product from slice object ----
---------------------------------------------

-- The slice functor from `c` to `d` which consists of a product of `d`
-- representable functors from `SliceObj c`.  Products of representables
-- are themselves representable (products of covariant representables are
-- represented by sums, and products of contravariant representables are
-- represented by products).
public export
SliceDepPiF : {c : Type} -> (d -> c -> Type) -> SliceFunctor c d
SliceDepPiF sdc sc ed = SliceCovarRepF (sdc ed) {c} sc ()

--------------------------------------
----- Dependent product as W-type ----
--------------------------------------

0 SDPasWTF : {c, d : Type} -> (p : d -> c -> Type) -> WTypeFunc c d
SDPasWTF {c} {d} p =
  MkWTF {dom=c} {cod=d}
    d
    (Sigma {a=(d, c)} (uncurry p))
    (snd . fst)
    (fst . fst)
    (id {a=d})

spdToWTF : {c, d : Type} -> (0 p : d -> c -> Type)->
  SliceNatTrans (SliceDepPiF {c} {d} p) (InterpWTF $ SDPasWTF p)
spdToWTF {c} {d} p sc ed mpsc =
  (Element0 ed Refl **
   \(Element0 ((ed', ec') ** pdc) eq) =>
    mpsc ec' $ replace {p=(flip p ec')} eq pdc)

spdFromWTF : {c, d : Type} -> (0 p : d -> c -> Type)->
  SliceNatTrans (InterpWTF $ SDPasWTF p) (SliceDepPiF {c} {d} p)
spdFromWTF {c} {d} p sc ed (Element0 ed' eq ** mpsc) =
  \ec, pdc => mpsc (Element0 ((ed, ec) ** pdc) $ sym eq)

---------------------------------------------------------------------
---------------------------------------------------------------------
---- Slice objects in terms of parameterized polynomial functors ----
---------------------------------------------------------------------
---------------------------------------------------------------------

-- The dependent-type view of slices in the category of polynomial functors,
-- which turns the arrows backwards (an object of a slice category "depends"
-- on the functor being sliced over, rather than being a functor with a
-- natural transformation to the functor being sliced over), induces a mapping
-- of positions of the functor being sliced over to polynomial functors.
-- Furthermore, for each such position, it induces a mapping of the directions
-- of the functor being sliced over at that position to directions of the
-- dependent polynomial functors for _each_ position of those functors.
--
-- Thus, the dependent polynomial functors may be viewed as pointed -- each
-- of them, at each of its own positions, must have directions available to
-- which to map the directions of the functor being sliced over (unless that
-- functor has no directions at the corresponding position).

-- To summarize, one way of viewing a polynomial-functor slice object is as a
-- family of polynomial functors parameterized over the positions of the functor
-- being sliced over, together with a section of each functor in the family
-- for each direction of the corresponding position of the functor being
-- sliced over.

public export
PosParamPolyFunc : PolyFunc -> Type
PosParamPolyFunc = ParamPolyFunc . pfPos

public export
mlDirichSlObjToPPF : {ar : MLArena} -> MlDirichSlObj ar -> PosParamPolyFunc ar
mlDirichSlObjToPPF {ar=(bpos ** bdir)} (MDSobj slpos sldir) i =
  ((bdir i, slpos i) ** \(bd, j) => sldir i j bd)

public export
mlDirichSlObjFromPPF : {ar : MLArena} -> PosParamPolyFunc ar -> MlDirichSlObj ar
mlDirichSlObjFromPPF {ar=(bpos ** bdir)} ppf =
  MDSobj (\i => bdir i -> fst $ ppf i) (\i, sld, bd => snd (ppf i) $ sld bd)

public export
mlPolySlObjToPPF : {ar : MLArena} -> MlPolySlObj ar -> PosParamPolyFunc ar
mlPolySlObjToPPF {ar} sl i = (mpsOnPos sl i ** mpsDir sl i)

public export
ParamPFSection : (p : PolyFunc) -> PosParamPolyFunc p -> Type
ParamPFSection p spf = SliceMorphism {a=(pfPos p)} (pfDir {p}) (PFSection . spf)

public export
mlPolySlObjToPPFsect : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  ParamPFSection ar (mlPolySlObjToPPF {ar} sl)
mlPolySlObjToPPFsect {ar} sl i bd j = mpsOnDir sl i j bd

public export
mlPolySlObjFromPPFandSections : {ar : MLArena} ->
  (ppf : PosParamPolyFunc ar) -> ParamPFSection ar ppf -> MlPolySlObj ar
mlPolySlObjFromPPFandSections {ar=(bpos ** bdir)} ppf sect =
  MPSobj (fst . ppf) (\i => snd $ ppf i) (\i, j, bd => sect i bd j)

-- Using this formulation, we can characterize a polynomial-functor slice
-- object as represented by the directions of a particular polynomial functor.

PFSliceObjPF : PolyFunc -> PolyFunc
PFSliceObjPF p = (PosParamPolyFunc p ** ParamPFSection p)

PFSliceObj : PolyFunc -> Type
PFSliceObj p = pfPDir $ PFSliceObjPF p

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---- Slice categories of polynomial functors (in dependent-type style) ----
---------------------------------------------------------------------------
---------------------------------------------------------------------------

-------------------------------------------------------------
---- Polynomial-functor slice category utility functions ----
-------------------------------------------------------------

-- A slice object over a constant functor is effectively a polynomial
-- functor parameterized over terms of the output type of the constant functor.
mlPolySliceOverConst : {x : Type} -> MlPolySlObj (PFConstArena x) ->
  ParamPolyFunc x
mlPolySliceOverConst {x} (MPSobj onpos dir ondir) ex =
  -- The arguments of `ondir` include a term of type `Void`, so
  -- it is impossible to apply (unless we find such a term, and
  -- hence a contradiction in our metalanguage).  Thus we can and
  -- must ignore it.
  --
  -- Put another way, `ondir` gives us no information, because its type
  -- restricts it to being effectively just the unique morphism out
  -- of the initial object.
  (onpos ex ** \i => dir ex i)

-- A slice object over the terminal polynomial functor is effectively
-- just a polynomial functor, just as a slice of `Type` over `Unit` is
-- effectively just a type.
mlPolySliceOver1 : MlPolySlObj PFTerminalArena -> PolyFunc
mlPolySliceOver1 psl = mlPolySliceOverConst {x=Unit} psl ()

mlPolyAppI : {p : PolyFunc} ->
  {- these two parameters form an object of the category of elements of `p`
   - interpreted as a Dirichlet functor -}
  (ty : Type) -> (el : InterpDirichFunc p ty) ->
  MlPolySlObj p -> MlPolySlObj (PFHomArena ty)
mlPolyAppI {p=p@(_ ** _)} ty (i ** d) =
  mlPolySlBaseChange {p} {q=(PFHomArena ty)} (\() => i ** \() => d)

-- By analogy with the application of a `SliceObj x` in `Type` to a term
-- of `x`, `PFApp` is a base change from the slice category over `p` to
-- the slice category over the terminal polynomial functor, which is
-- effectively just the category of polynomial endofunctors on `Type`.
-- Such a base change requires a Dirichlet (not polynomial!) natural
-- transformation from the terminal polynomial functor (which is just
-- a single position with no directions) to the functor being sliced over.
-- That in turn amounts to simply a choice of position of the functor
-- being sliced over, which dictates which dependent polynomial functor
-- to select as the result.
mlPolyApp1 : {p : PolyFunc} -> pfPos p -> MlPolySlObj p -> PolyFunc
mlPolyApp1 {p=p@(pos ** dir)} i slp =
  mlPolySliceOver1 $ mlPolyAppI {p} Void (i ** \v => void v) slp

----------------------------
----------------------------
---- Generalized arenas ----
----------------------------
----------------------------

--------------------
---- Telescopes ----
--------------------

data MLTelFPos : (tl : Type) -> Type where
  MLUnitPos : {0 tl : Type} -> MLTelFPos tl
  MLDPairPos : {0 tl : Type} -> SliceObj tl -> MLTelFPos tl

MLTelFDir : Sigma {a=Type} MLTelFPos -> Type
MLTelFDir (tl ** MLUnitPos) = Void
MLTelFDir (tl ** (MLDPairPos {tl} sl)) = Unit

MLTelFAssign : Sigma {a=(Sigma {a=Type} MLTelFPos)} MLTelFDir -> Type
MLTelFAssign ((tl ** MLUnitPos) ** v) = void v
MLTelFAssign ((tl ** (MLDPairPos {tl} sl)) ** ()) = Sigma {a=tl} sl

MLTelF : SlicePolyEndoFunc Type
MLTelF = (MLTelFPos ** MLTelFDir ** MLTelFAssign)

MLTel : Type -> Type
MLTel = SPFMu MLTelF

MLFreeTel : SliceEndofunctor Type
MLFreeTel = SlicePolyFree MLTelF

----------------------------------------------
----------------------------------------------
---- Factorized slice polynomial functors ----
----------------------------------------------
----------------------------------------------

-- Because `Cat` has a factorization system -- all functors can be factored
-- into two, via a category of elements of a functor out of the codomain --
-- we could also choose to _define_ a functor as a composite of two functors
-- of that specific form.

-- So we begin with a definition of a polynomial (co)presheaf on a slice
-- category.
public export
SlPolyAr : Type -> Type
SlPolyAr c = IntArena (SliceObj c)

public export
SlIntComp : (c : Type) -> IntCompSig (SliceObj c) (SliceMorphism {a=c})
SlIntComp c x y z g f = \ela, elx => g ela $ f ela elx

public export
SlArInterp : {c : Type} -> SlPolyAr c -> SliceObj c -> Type
SlArInterp {c} = InterpIPFobj (SliceObj c) (SliceMorphism {a=c})

public export
0 SlPolyArMapSig : {c : Type} -> SlPolyAr c -> Type
SlPolyArMapSig {c} ar =
  IntCopreshfMapSig (SliceObj c) (SliceMorphism {a=c}) (SlArInterp {c} ar)

public export
SlArFMap : {c : Type} -> (ar : SlPolyAr c) -> SlPolyArMapSig {c} ar
SlArFMap {c} = InterpIPFmap (SliceObj c) (SliceMorphism {a=c}) (SlIntComp c)

--------------------------------------------------
--------------------------------------------------
---- Experiments with impredicative encodings ----
--------------------------------------------------
--------------------------------------------------

-------------------------------------------------
---- Coproducts through universal properties ----
-------------------------------------------------

ImpredCoprodDom : Type -> Type -> PolyFunc
ImpredCoprodDom x y = pfProductArena (PFHomArena x) (PFHomArena y)

ImpredCoprodCodom : Type -> Type -> PolyFunc
ImpredCoprodCodom _ _ = PFIdentityArena

-- Compare `IntIsCoprodCovar`.
ImpredCoprod : Type -> Type -> Type
ImpredCoprod x y = PolyNatTrans (ImpredCoprodDom x y) (ImpredCoprodCodom x y)

impredInjL : {x, y : Type} -> x -> ImpredCoprod x y
impredInjL {x} {y} ex = (\_ => () ** \((), ()), () => Left ex)

impredInjR : {x, y : Type} -> y -> ImpredCoprod x y
impredInjR {x} {y} ey = (\_ => () ** \((), ()), () => Right ey)

CoprodFromImpred : (x, y : Type) -> ImpredCoprod x y -> Either x y
CoprodFromImpred x y (onpos ** ondir) = ondir ((), ()) ()

CoprodToImpred : (x, y : Type) -> Either x y -> ImpredCoprod x y
CoprodToImpred x y = eitherElim (impredInjL {x} {y}) (impredInjR {x} {y})

impredCase : {x, y, z : Type} -> (x -> z, y -> z) -> (ImpredCoprod x y -> z)
impredCase {x} {y} {z} (f, g) ic = eitherElim f g $ CoprodFromImpred x y ic

impredCopLAdj : {x, y, z : Type} -> (ImpredCoprod x y -> z) -> (x -> z, y -> z)
impredCopLAdj {x} {y} {z} f = (f . impredInjL {x} {y}, f . impredInjR {x} {y})

CoprodToFromImpredId : (x, y : Type) -> (exy : Either x y) ->
  CoprodFromImpred x y (CoprodToImpred x y exy) = exy
CoprodToFromImpredId x y (Left ex) = Refl
CoprodToFromImpredId x y (Right ey) = Refl

CoprodFromToImpredId : (x, y : Type) -> (ic : ImpredCoprod x y) ->
  CPFNatTransEq (ImpredCoprodDom x y) (ImpredCoprodCodom x y)
    (CoprodToImpred x y (CoprodFromImpred x y ic))
    ic
CoprodFromToImpredId x y (onpos ** ondir) with
    (onpos ((), ()), ondir ((), ()) ()) proof eq
  CoprodFromToImpredId x y (onpos ** ondir) | ((), Left ex) =
    rewrite sndEq eq in
    Evidence0
      (\((), ()) => rewrite fstEq eq in Refl)
      (\((), ()), () => sndEq eq)
  CoprodFromToImpredId x y (onpos ** ondir) | ((), Right ey) =
    rewrite sndEq eq in
    Evidence0
      (\((), ()) => rewrite fstEq eq in Refl)
      (\((), ()), () => sndEq eq)

ImpredCoprod' : Type -> Type -> Type
ImpredCoprod' x y =
  InterpPolyFunc
    (pfParProdClosure (ImpredCoprodDom x y) (ImpredCoprodCodom x y))
    Unit

ImpredCoprodFromPrime : (x, y : Type) -> ImpredCoprod' x y -> ImpredCoprod x y
ImpredCoprodFromPrime x y (pos ** dir) =
  (\_ => () ** \((), ()), () => snd $ snd (pos ((), ())) ())

ImpredCoprodToPrime : (x, y : Type) -> ImpredCoprod x y -> ImpredCoprod' x y
ImpredCoprodToPrime x y (onpos ** ondir) =
  (\((), ()) => (() ** \() => ((), ondir ((), ()) ())) ** \_ => ())

-----------------------------------------------
---- Products through universal properties ----
-----------------------------------------------

ImpredProdDom : Type -> Type -> PolyFunc
ImpredProdDom x y = pfCoproductArena (PFHomArena x) (PFHomArena y)

ImpredProdCodom : Type -> Type -> PolyFunc
ImpredProdCodom _ _ = PFIdentityArena

ImpredProd : Type -> Type -> Type
ImpredProd x y = PolyNatTrans (ImpredProdDom x y) (ImpredProdCodom x y)

impredProj1 : {x, y : Type} -> ImpredProd x y -> x
impredProj1 {x} {y} (onpos ** ondir) = ondir (Left ()) ()

impredProj2 : {x, y : Type} -> ImpredProd x y -> y
impredProj2 {x} {y} (onpos ** ondir) = ondir (Right ()) ()

ProdFromImpred : (x, y : Type) -> ImpredProd x y -> Pair x y
ProdFromImpred x y alpha = (impredProj1 alpha, impredProj2 alpha)

ProdToImpred : (x, y : Type) -> Pair x y -> ImpredProd x y
ProdToImpred x y (ex, ey) =
  (\_ => () ** \i, () => case i of Left () => ex ; Right () => ey)

impredBi : {x, y, z : Type} -> (x -> y, x -> z) -> (x -> ImpredProd y z)
impredBi {x} {y} {z} (f, g) ic =
  (\_ => () ** \d, () => case d of Left () => f ic ; Right () => g ic)

impredProdRAdj : {x, y, z : Type} -> (x -> ImpredProd y z) -> (x -> y, x -> z)
impredProdRAdj {x} {y} {z} ic =
  (\ex => snd (ic ex) (Left ()) (), \ex => snd (ic ex) (Right ()) ())

ImpredProdDomPar : Type -> Type -> PolyFunc
ImpredProdDomPar x y = pfParProductArena (PFHomArena x) (PFHomArena y)

ImpredProdCodomPar : Type -> Type -> PolyFunc
ImpredProdCodomPar _ _ = PFIdentityArena

-- Compare `IntIsProdContra`, as well as `ImpredProd` and `ImpredCoprod`.
ImpredProdPar : Type -> Type -> Type
ImpredProdPar x y = PolyNatTrans (ImpredProdDomPar x y) (ImpredProdCodomPar x y)

ImpredProdToPar : (x, y : Type) -> ImpredProd x y -> ImpredProdPar x y
ImpredProdToPar x y (pos ** dir) =
  (\_ => () ** \((), ()), () => (dir (Left()) (), dir (Right ()) ()))

ImpredProdFromPar : (x, y : Type) -> ImpredProdPar x y -> ImpredProd x y
ImpredProdFromPar x y (onpos ** ondir) =
  (\_ => () ** \eu, () =>
    case eu of
      Left () => fst $ ondir ((), ()) ()
      Right () => snd $ ondir ((), ()) ())

-------------------------------------------------------
---- Initial algebras through universal properties ----
-------------------------------------------------------

public export
ImpredInitAlg : (Type -> Type) -> Type
ImpredInitAlg f = NaturalTransformation (Algebra f) Prelude.id

public export
PolyImpredToMu : (p : PolyFunc) ->
  ImpredInitAlg (InterpPolyFunc p) -> PolyFuncMu p
PolyImpredToMu p alg = alg (PolyFuncMu p) $ \(i ** d) => InPFM i d

public export
PolyImpredFromMu : (p : PolyFunc) ->
  PolyFuncMu p -> ImpredInitAlg (InterpPolyFunc p)
PolyImpredFromMu p x a alg = pfCata (\i, d => alg (i ** d)) x

public export
ImpredAlgDom : PolyFunc -> PolyFunc
ImpredAlgDom p = pfHomObj p PFIdentityArena

public export
ImpredAlgCodom : PolyFunc -> PolyFunc
ImpredAlgCodom _ = PFIdentityArena

public export
PolyImpredInitAlg : PolyFunc -> Type
PolyImpredInitAlg p = PolyNatTrans (ImpredAlgDom p) (ImpredAlgCodom p)

public export
PolyImpredInitAlgToFreeM : (p : PolyFunc) ->
  PolyImpredInitAlg p -> PolyNatTrans (ImpredAlgDom p) (PolyFuncFreeM p)
PolyImpredInitAlgToFreeM p =
  pntVCatComp {p=(ImpredAlgDom p)} {q=PFIdentityArena} {r=(PolyFuncFreeM p)}
    (PolyNTvar p)

public export
0 PolyFreeMtoImpredInitAlgM : (p : PolyFunc) ->
  PolyNatTrans (ImpredAlgDom p) (PolyFuncFreeM p) -> PolyImpredInitAlg p
PolyFreeMtoImpredInitAlgM p alpha = ?PolyFreeMtoImpredInitAlgM_hole

public export
0 ImpredInitAlgFromPoly : (p : PolyFunc) ->
  PolyImpredInitAlg p -> ImpredInitAlg (InterpPolyFunc p)
ImpredInitAlgFromPoly p (onpos ** ondir) a alg = ?ImpredAlgInitFromPoly_hole

public export
0 PolyImpredNTtoMu : (p : PolyFunc) -> PolyImpredInitAlg p -> PolyFuncMu p
PolyImpredNTtoMu p (onpos ** ondir) = ?PolyImpredNTtoMu_hole

public export
PolyElemCatFunc : PolyFunc -> PolyFunc
PolyElemCatFunc p = pfHomObj PFTerminalArena p

public export
PolyElemFromFunc : (p : PolyFunc) ->
  MLPolyCatElemObj (PolyElemCatFunc p) -> PolyNatTrans PFIdentityArena p
PolyElemFromFunc (pos ** dir) (x ** i ** d) =
  (\() => fst (i ()) ** \(), di => ())

public export
PolyElemToFunc : (p : PolyFunc) ->
  PolyNatTrans PFIdentityArena p -> MLPolyCatElemObj (PolyElemCatFunc p)
PolyElemToFunc (pos ** dir) (onpos ** ondir) =
  (dir (onpos ()) ** \() => (onpos () ** \d => Left ()) **
   \(() ** qd ** ()) => qd)

public export
PolyElemToFromFuncId : (p : PolyFunc) ->
  (alpha : PolyNatTrans PFIdentityArena p) ->
  CPFNatTransEq PFIdentityArena p
    (PolyElemFromFunc p (PolyElemToFunc p alpha)) alpha
PolyElemToFromFuncId (pos ** dir) (onpos ** ondir) =
  Evidence0 (\() => Refl) $ \(), d => unitUnique (ondir () d) ()

-------------------------------------------
---- Impredicative terminal coalgebras ----
-------------------------------------------

public export
SeededCoalgF : (Type -> Type) -> Type -> Type
SeededCoalgF f = ProductF (Coalgebra f) Prelude.id

public export
SeededCoalgElim : (Type -> Type) -> Type -> Type
SeededCoalgElim f z = NaturalTransformation (SeededCoalgF f) (const z)

-- An object of the category of elements of `SeededCoalgF`.
-- We shall show that this is ismorphic to `Nu`.
public export
ImpredTerminalCoalgExist : (Type -> Type) -> Type
ImpredTerminalCoalgExist f = (a : Type ** SeededCoalgF f a)

public export
ImpredTCExToNu : (f : Type -> Type) -> Anamorphism f ->
  ImpredTerminalCoalgExist f -> Nu f
ImpredTCExToNu f af (a ** (coalg, ea)) = af a coalg ea

public export
ImpredTCExFromNu : (f : Type -> Type) -> Nu f -> ImpredTerminalCoalgExist f
ImpredTCExFromNu f x = (Nu f ** (treeSubtree . outCofree, x))

-- Simply the Yoneda embedding of `ImpredTerminalCoalgExist f`.
public export
ImpredTerminalCoalg : (Type -> Type) -> Type
ImpredTerminalCoalg f = NaturalTransformation (SeededCoalgElim f) Prelude.id

public export
ImpredTCToNu : (f : Type -> Type) -> Anamorphism f ->
  ImpredTerminalCoalg f -> Nu f
ImpredTCToNu f af alpha = alpha (Nu f) $ DPair.curry $ ImpredTCExToNu f af

public export
ImpredTCFromNu : (f : Type -> Type) -> Nu f -> ImpredTerminalCoalg f
ImpredTCFromNu f x z alpha = DPair.uncurry alpha (ImpredTCExFromNu f x)

--------------------------------------------------------
--------------------------------------------------------
---- (Co)slice categories as categories of elements ----
--------------------------------------------------------
--------------------------------------------------------

----------------------------
---- Coslice categories ----
----------------------------

public export
InterpCovarHomCoslice : (c : Type) ->
  MLPolyCatElemObj (PFHomArena c) ->
  (b : Type ** c -> b)
InterpCovarHomCoslice c (a ** () ** d) = (a ** d)

------------------------------------------
---- Two-category of slice categories ----
------------------------------------------

public export
ParamCovarHom : ParamPolyFunc Type
ParamCovarHom = PFHomArena

public export
PFSliceObj' : PolyFunc
PFSliceObj' = ParamPolyFuncToPolyFunc ParamCovarHom

public export
InterpPFSliceObj : (a : Type) -> InterpPolyFunc PFSliceObj' a -> CSliceObj a
InterpPFSliceObj a ((b ** ()) ** m) = (b ** m)

public export
InterpPFSliceElemObj : (e : MLPolyCatElemObj PFSliceObj') -> CSliceObj (fst e)
InterpPFSliceElemObj (a ** ea) = InterpPFSliceObj a ea

public export
InterpPFSliceMor : (a, a' : Type) -> InterpPolyFunc PFSliceObj' a ->
  (a -> a') -> InterpPolyFunc PFSliceObj' a'
InterpPFSliceMor a a' = flip $ InterpPFMap {a} {b=a'} PFSliceObj'

public export
0 InterpPFSliceElemSigma : (a, a' : MLPolyCatElemObj PFSliceObj') ->
  MLPolyCatElemMor PFSliceObj' a a' ->
  CSliceFunctor (fst a) (fst a')
InterpPFSliceElemSigma (a ** (i ** ()) ** d) (a' ** (i' ** ()) ** d') m =
  CSSigma $ pcemMor _ _ _ _ _ _ m

public export
0 InterpPFSliceElemPi : (a, a' : MLPolyCatElemObj PFSliceObj') ->
  MLPolyCatElemMor PFSliceObj' a a' ->
  CSliceFunctor (fst a) (fst a')
InterpPFSliceElemPi (a ** (i ** ()) ** d) (a' ** (i' ** ()) ** d') m =
  CSPi $ pcemMor _ _ _ _ _ _ m

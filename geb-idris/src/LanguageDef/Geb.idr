module LanguageDef.Geb

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import LanguageDef.BinTree
import LanguageDef.PolyCat
import LanguageDef.DiagramCat
import LanguageDef.NatPrefixCat
import LanguageDef.PolyIndTypes

%default total

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

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Internal pro-/di-functors and (para-)natural transformations ----
----------------------------------------------------------------------
----------------------------------------------------------------------

-- The convention we use is that the first parameter (here, `d`) is the
-- contravariant parameter, and the second parameter (`here, `c`) is
-- the covariant parameter.  This is sometimes written as `c -/-> d`,
-- and sometimes called a "correspondence from" `d` to `c`.
-- Since `Cat` is cartesian closed, it may be viewed as a functor
-- `c -> presheaves(d)`, or equivalently as a functor
-- `op(d) -> copresheaves(c)`.  See
-- https://en.wikipedia.org/wiki/Profunctor#Definition and
-- https://ncatlab.org/nlab/show/profunctor#definition.
public export
IntProfunctorSig : (d, c : Type) -> Type
IntProfunctorSig d c = d -> c -> Type

public export
IntDifunctorSig : (c : Type) -> Type
IntDifunctorSig c = IntProfunctorSig c c

public export
IntProfNTSig : (d, c : Type) ->
  (p, q : IntProfunctorSig d c) -> Type
IntProfNTSig d c p q = (a : d) -> (b : c) -> p a b -> q a b

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

-- Merge two profunctors going in opposite directions (between `d` and `c`)
-- into an embedding of `(op(d), c)` into its category of prosheaves.
public export
IntBidirProfEmbed : (0 d, c : Type) ->
  (relop : IntProfunctorSig c d) -> (rel : IntProfunctorSig d c) ->
  d -> c -> IntProfunctorSig d c
IntBidirProfEmbed d c relop rel i0 i1 j0 j1 = (relop i1 j0, rel i0 j1)

-- Suppose that `c` is a type of objects of a category internal to `Type`,
-- and `mor` is a type dependent on pairs of terms of `c` (we could also
-- express it dually as a `Type` together with morphisms `dom` and `cod` to
-- `c`), which we interpret as _some_ morphisms of the category but not
-- necessarily all.  Then `IntDiYonedaEmbed c mor` is the diYoneda embedding
-- of the product of the opposite of the internal category and the internal
-- category itself (`op(Type) x Type`) into the category whose objects are
-- profunctors on the internal category -- that is, functors
-- `op(c) -> c -> Type` -- and whose morphisms are paranatural
-- transformations.
public export
IntDiYonedaEmbed : (0 c : Type) ->
  (mor : IntDifunctorSig c) -> c -> c -> IntDifunctorSig c
IntDiYonedaEmbed c mor = IntBidirProfEmbed c c (flip mor) mor

-----------------------------------------------
-----------------------------------------------
---- Paranatural transformations on `Type` ----
-----------------------------------------------
-----------------------------------------------

-- The following categories are equivalent:
--
--  1) the splice category of `Type` over `(i, j)`
--  2) the category of profunctors `j -> i`, AKA functors `(op(i), j) -> Type`,
--    where `i` and `j` are viewed as discrete categories, and the morphisms
--    are paranatural transformations
--  3) the category of diagonal elements of the profunctor di-represented by
--    `(i, j)`, i.e. `DiYoneda i j`
--  4) the category of polynomial difunctors (endo-profunctors) on
--     `(op(Type), Type)` with position-set `(i, j)` (i.e. contravariant
--     position-set `i` and covariant position-set `j`), with paranatural
--     transformations as morphisms
--
-- (I expect, but have not proven, that the category of profunctors `j -> i`
-- (AKA functors `(op(i), j) -> Type` where `i` and `j` are viewed as
-- discrete categories) with _natural_ transformations, as opposed to the
-- more general _paranatural_ transformations, as morphisms is equivalent to
-- the category of _elements_, as opposed to the category of _diagonal_
-- elements, of the profunctor _represented_, as opposed to _direpresented_, by
-- `(i, j)`, i.e. `PrePostPair i j` (the (contravariant x covariant) Yoneda
-- embedding of `(i, j)`) or `Iso i j` (the (covariant x contravariant) Yoneda
-- embedding of `(i, j`)).  I further expect that it is probably equivalent to
-- the slice category of `Type` over `(i, j)`, and to the category
-- of polynomial difunctors (endo-profunctors) on `Type` with position-set
-- `(i, j)` with _natural_ (not just paranatural) transformations as morphisms.)
--
-- This is analogous to how the following are equivalent:
--
--  1) the slice category of `Type` over `j`
--  2) the category of presheaves over `j`, AKA functors `op(j) -> Type`,
--    where `j` is viewed as a discrete category, and the morphisms
--    are natural transformations
--  3) the category of elements of the presheaf represented by `j`,
--    i.e. the contravariant Yoneda embedding of `j`
--  4) the category of Dirichlet endofunctors on `Type` with position-set `j`
--  5) the opposite of the category of polynomial endofunctors on `Type` with
--     position-set `j`
--
-- And dually:
--
--  1) the coslice category of `Type` over `i`
--  2) the category of copresheaves over `i`, AKA functors `i -> Type`,
--    where `i` is viewed as a discrete category, and the morphisms
--    are natural transformations
--  3) the category of elements of the copresheaf represented by `i`,
--    i.e. the covariant Yoneda embedding of `i`
--  4) the category of Dirichlet endofunctors on `op(Type)` with
--     position-set `i`
--  5) the opposite of the category of polynomial endofunctors on `op(Type)`
--     with position-set `i`
--
-- The splice version unifies the two duals.
--
-- Given an object in a splice category over `(i, j)`, with intermediate
-- object `k`, injection `into : i -> k`, and projection `from : k -> j`,
-- where we shall refer to the composition `from . into : i -> j` as `comp`,
-- we can form objects of other splice categories in the following ways (which
-- are functorial, so we are saying that there are the following functors
-- between splice categories):
--
--  1) Given morphisms `f : x -> i` and `g : j -> y`, we can form an object
--     of the splice category over `(x, y)` with intermediate object `k` by
--     composing `f` before `into` and `g` after `from`.  Note that
--     `(f, g)` is a morphism from `(i, j)` to `(x, y)` in `(op(Type), Type)`.
--     This is the sigma functor between splice categories.  Note that `(f, g)`
--     may equivalently be seen as `DiYoneda x y j i`, or `PrePostPair i j x y`,
--     or `Iso x y i j`.  The intermediate object is still `k`.

-- See https://arxiv.org/abs/2307.09289 .

-- `DiYonedaEmbed` is sometimes written `yy(i0, i1)` .  It embeds
-- the object `(i0, i1)` of `(op(Type), Type)` into the category
-- whose objects are profunctors `(op(Type), Type) -> Type)` and whose
-- morphisms are _paranatural_ transformations (compare to `DualYonedaEmbed`,
-- where the codomain category's objects are the same, but the morphisms are
-- the more strict _natural_ transformations).
--
-- Note that `DiYonedaEmbed Void i1` is the profunctor which ignores its
-- second argument and acts as `ContravarHomFunc i1` on its first argument,
-- whereas `DiYonedaEmbed i0 Unit` is the profunctor which ignores its first
-- argument and acts as `CovarHomFunc i0` on its second argument.  So
-- `DiYonedaEmbed Void` is effectively the contravariant Yoneda embedding
-- on `Type`, while `flip DiYonedaEmbed Unit` is effectively the covariant
-- Yoneda embedding on `Type`.

-- `Type` itself is a category internal to `Type`, so we may define the
-- diYoneda embedding of `Type` as a specialization of the internal diYoneda
-- embedding with `Type` as `obj` and `HomProf` as `mor`.
public export
DiYonedaEmbed : Type -> Type -> ProfunctorSig
DiYonedaEmbed = IntDiYonedaEmbed Type HomProf

public export
[DiYonedaEmbedProf] Profunctor (DiYonedaEmbed i j) where
  dimap mca mbd (maj, mib) = (maj . mca, mbd . mib)

-- The diYoneda lemma asserts a paranatural isomorphism between two objects
-- of the enriching category, one of which is an object of paranatural
-- transformations.  This type is an explicit name for that object on
-- the category `(op(Type), Type)`.
public export
DiYonedaLemmaNT : ProfunctorSig -> ProfunctorSig
DiYonedaLemmaNT p c d = ProfDiNT (flip DiYonedaEmbed c d) p

public export
DiYonedaLemmaNTPro : Profunctor (DiYonedaLemmaNT p)
DiYonedaLemmaNTPro = MkProfunctor $
  \mca, mbd, alpha, i, (mic, mdi) => alpha i (mca . mic, mdi . mbd)

-- One direction of the paranatural isomorphism asserted by the
-- diYoneda lemma on `(op(Type), Type)`.
public export
DiYonedaLemmaL : (0 p : ProfunctorSig) -> {auto isP : Profunctor p} ->
  ProfDiNT p (DiYonedaLemmaNT p)
DiYonedaLemmaL p {isP} i pii j (mji, mij) = dimap {f=p} mji mij pii

-- The other direction of the paranatural isomorphism asserted by the
-- diYoneda lemma on `(op(Type), Type)`.
public export
DiYonedaLemmaR : (0 p : ProfunctorSig) -> {auto isP : Profunctor p} ->
  ProfDiNT (DiYonedaLemmaNT p) p
DiYonedaLemmaR p {isP} i dye = dye i (id {a=i}, id {a=i})

-- The di-co-Yoneda lemma asserts a paranatural isomorphism between two objects
-- of the enriching category, one of which is a coend (existential type).
-- This type is an explicit name for that object on the category
-- `(op(Type), Type)`.
public export
DiCoYonedaLemmaCoend : ProfunctorSig -> ProfunctorSig
DiCoYonedaLemmaCoend p i0 i1 =
  Exists {type=(Type, Type)} $
    \j => (DiYonedaEmbed i0 i1 (fst j) (snd j), p (snd j) (fst j))

public export
Profunctor (DiCoYonedaLemmaCoend p) where
  dimap {a} {b} {c} {d} mca mbd (Evidence ij ((mib, maj), pji)) =
    Evidence ij ((mbd . mib, maj . mca), pji)

-- One direction of the paranatural isomorphism asserted by the
-- di-co-Yoneda lemma on `(op(Type), Type)`.
public export
DiCoYonedaLemmaL : (0 p : ProfunctorSig) ->
  ProfDiNT p (DiCoYonedaLemmaCoend p)
DiCoYonedaLemmaL p i pii = Evidence (i, i) ((id {a=i}, id {a=i}), pii)

-- The other direction of the paranatural isomorphism asserted by the
-- di-co-Yoneda lemma on `(op(Type), Type)`.
public export
DiCoYonedaLemmaR : (0 p : ProfunctorSig) -> {auto isP : Profunctor p} ->
  ProfDiNT (DiCoYonedaLemmaCoend p) p
DiCoYonedaLemmaR p {isP} i (Evidence j ((mj0i, mij1), pj1j0)) =
  dimap {f=p} mij1 mj0i pj1j0

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
-- `Yoneda/runYoneda` in some Haskell libraries.
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
-- Haskell libraries.
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

infixr 1 <#
public export
(<#) : {cd : CatData} -> {x, y, z : cdObj cd} ->
  cdHom cd (y, z) -> cdHom cd (x, y) -> cdHom cd (x, z)
(<#) {cd} {x} {y} {z} = cdComp cd x y z

infixr 1 |>
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

infixr 1 <!
public export
(<!) : {lc : LawfulCat} -> {x, y, z : lcObj lc} ->
  lcHom lc (y, z) -> lcHom lc (x, y) -> lcHom lc (x, z)
(<!) {lc} {x} {y} {z} = lcComp lc x y z

infixr 1 !>
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
  (alg : atom -> a -> m a) -> (autobind : m a -> (a -> m a) -> m a) ->
  BinTreeAlg atom (a -> m a)
BinTreeAutoBindAlg {m} alg autobind (Left x) ea = alg x ea
BinTreeAutoBindAlg {m} alg autobind (Right (bt, bt')) ea = autobind (bt ea) bt'

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
binTreeEqCorrect : {0 atom : Type} -> (deq : DecEqPred atom) ->
  (x, x' : BinTreeMu atom) -> IsTrue (binTreeEq deq x x') -> x = x'
binTreeEqCorrect deq x x' eq = ?binTreeEqCorrect_hole

public export
binTreeNeqCorrect : {0 atom : Type} -> (deq : DecEqPred atom) ->
  (x, x' : BinTreeMu atom) -> IsFalse (binTreeEq deq x x') -> Not (x = x')
binTreeNeqCorrect deq x x' neq = ?binTreeNeqCorrect_hole

public export
binTreeDecEq : {0 atom : Type} -> DecEqPred atom -> DecEqPred (BinTreeMu atom)
binTreeDecEq deq x x' with (binTreeEq deq x x') proof prf
  binTreeDecEq deq x x' | True = Yes $ binTreeEqCorrect deq x x' prf
  binTreeDecEq deq x x' | False = No $ binTreeNeqCorrect deq x x' prf

public export
DecEq atom => DecEq (BinTreeMu atom) where
  decEq = binTreeDecEq decEq

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

InterpFSMP : {n : Nat} -> (p : FinMatrixS) -> (0 _ : FinMatrixBounded n p) ->
  SliceObj (Fin n) -> Type
InterpFSMP {n} ps bounded sl =
  Subset0 (Nat, List Nat) $
    \(i, p) =>
      (b : LT i (length ps) **
       InterpFSP {n} (Element0 (index' ps $ natToFinLT i) $
        ?InterpFSMP_hole_pred $ indexAll ?InterpFSMP_hole_elem bounded) sl)

InterpFSM : {n : Nat} ->
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
DAGedgeSet tsf = HVect {k=(tsfVert tsf)} (DAGieTV tsf)

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
AListMuPiAlg : {atom : Type} -> AListTypeAlg atom -> Type
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
listMuSliceCata' : {atom : Type} -> (dom, cod : ListTypeAlg atom) ->
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
FinDAGEdge : (ts : FinTSort) -> FinTSInnerLevel ts -> Type
FinDAGEdge ts lev = ?FinDAGEdge_hole

-- A representation of a finite directed acyclic (multi)graph (DAG) -- a list of
-- edges each of which points from a lower-numbered level to a higher-numbered
-- level in the given topological sort.
public export
FinDAG' : FinTSort -> Type
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

------------------------
------------------------
---- Quotient types ----
------------------------
------------------------

---------------------
---- Definitions ----
---------------------

-- A quotient type is a type together with an equivalence relation.
public export
QType : Type
QType = Subset0 Type PrEquivRel

public export
QBase : QType -> Type
QBase = fst0

public export
0 QRel : (0 x : QType) -> PrEquivRel (QBase x)
QRel x = snd0 x

public export
0 QBaseRel : (0 x : QType) -> PrERel (QBase x)
QBaseRel x = fst (QRel x)

public export
0 QRelEquivI : (0 x : QType) -> PrEquivRelI (QBase x) (QBaseRel x)
QRelEquivI x = snd (QRel x)

public export
QFunc : QType -> QType -> Type
QFunc x y = QBase x -> QBase y

public export
0 QPres : (0 x, y : QType) -> SliceObj (QFunc x y)
QPres x y f = PrERelPres {a=(QBase x)} {b=(QBase y)} f (QBaseRel x) (QBaseRel y)

public export
QMorph : QType -> QType -> Type
QMorph x y = Subset0 (QFunc x y) (QPres x y)

public export
QMorphBase : {0 x, y : QType} -> QMorph x y -> QBase x -> QBase y
QMorphBase = fst0

public export
0 QMorphPres : {0 x, y : QType} ->
  (f : QMorph x y) -> QPres x y (QMorphBase {x} {y} f)
QMorphPres = snd0


-----------------------------------------
---- Self-internalization of `QType` ----
-----------------------------------------

-- We can form an equivalence relation on `QType` itself which states that
-- two `QType`s are equivalent if they have the same underlying type and
-- their equivalence relations are equivalent.  This equivalence relation is
-- therefore using the notion of equivalence relation to "hide" the witnesses
-- of equivalence relations themselves.  (It is introducing a proof-irrelevant
-- layer on top of proof-relevant relations.)
public export
data QTEquiv : PrERel QType where
  QTE : {0 x : Type} -> {0 r, r' : PrEquivRel x} ->
    (0 _ : PrRelBiImp (fst r) (fst r')) -> QTEquiv (Element0 x r, Element0 x r')

-- `QTEquiv` is an equivalence relation.
public export
QTEquivEquivI : PrEquivRelI QType QTEquiv
QTEquivEquivI
  (Element0 x r, Element0 x r) (PrErefl _) =
    QTE $ PrEquivRefl (BiImpEquivERel x) (fst r)
QTEquivEquivI
  (Element0 x r, Element0 x r') (PrEsym _ _ (QTE eq)) =
    QTE $ PrEquivSym {ea=(fst r')} {ea'=(fst r)} (BiImpEquivERel x) eq
QTEquivEquivI
  (Element0 x r, Element0 x r')
  (PrEtrans (Element0 x r) (Element0 x r'') (Element0 x r')
    (QTE eq) (QTE eq')) =
      QTE $ PrEquivTrans {ea=(fst r)} {ea'=(fst r'')} {ea''=(fst r')}
        (BiImpEquivERel x) eq eq'

public export
QTEquivEquiv : PrEquivRel QType
QTEquivEquiv = (QTEquiv ** QTEquivEquivI)

-- Between any two `QTEquiv`-equivalent types, there is an isomorphism
-- whose underlying function is the identity.
public export
QTEqIso : {0 x, y : QType} -> QTEquiv (x, y) -> QMorph x y
QTEqIso (QTE imp) = Element0 id $ fst imp

-- Using `QTEquiv`, we can make `QType` itself a `QType`.
public export
QTypeQT : QType
QTypeQT = Element0 QType QTEquivEquiv

-- We can also define an extensional equality on morphisms of `QType`.
public export
0 QMExtEq : {0 x, y : QType} -> PrERel (QMorph x y)
QMExtEq {x} {y} (f, g) =
  PrERelBiPres {a=(QBase x)} {b=(QBase y)}
    (QMorphBase f) (QMorphBase g) (QBaseRel x) (QBaseRel y)

-- `QMExtEq` is an equivalence relation.
public export
0 QMExtEqEquivI : {0 x, y : QType} -> PrEquivRelI (QMorph x y) (QMExtEq {x} {y})
QMExtEqEquivI {x=(Element0 x (rx ** eqx))} {y=(Element0 y (ry ** eqy))}
  (Element0 f fpres, Element0 f fpres) (PrErefl _) =
    fpres
QMExtEqEquivI {x=(Element0 x (rx ** eqx))} {y=(Element0 y (ry ** eqy))}
  (Element0 f fpres, Element0 g gpres) (PrEsym _ _ r) =
    \ex, ex', rex =>
      eqy (f ex, g ex') $ PrEtrans (f ex) (g ex) (g ex') (gpres ex ex' rex)
      $ eqy (f ex, g ex) $ PrEtrans (f ex) (f ex') (g ex)
      (eqy (f ex', g ex) $ PrEsym (g ex) (f ex') $ r ex ex' rex)
      $ fpres ex ex' rex
QMExtEqEquivI {x=(Element0 x (rx ** eqx))} {y=(Element0 y (ry ** eqy))}
  (Element0 f fpres, Element0 g gpres) (PrEtrans _ (Element0 h hpres) _ r r') =
    \ex, ex', rex =>
      eqy (f ex, g ex') $ PrEtrans (f ex) (g ex) (g ex') (gpres ex ex' rex)
      $ eqy (f ex, g ex) $ PrEtrans (f ex) (h ex') (g ex)
      (eqy (h ex', g ex) $ PrEtrans (h ex') (g ex') (g ex)
        (eqy (g ex', g ex) $ PrEsym (g ex) (g ex') $ gpres ex ex' rex)
        (eqy (h ex', g ex') $ PrEtrans (h ex') (h ex) (g ex')
          (r ex ex' rex)
          $ eqy (h ex', h ex) $ PrEsym (h ex) (h ex') $ hpres ex ex' rex))
      $ r' ex ex' rex

public export
0 QMExtEqEquiv : (0 x, y : QType) -> PrEquivRel (QMorph x y)
QMExtEqEquiv x y = (QMExtEq {x} {y} ** QMExtEqEquivI {x} {y})

-- This type represents that two `QType` morphisms agree (up to codomain
-- equivalence) on intensionally equal elements of the domain.
public export
0 QMIntExt : {0 x, y : QType} -> PrERel (QMorph x y)
QMIntExt {x} {y} (f, g) = PrERelIntExt {a=(QBase x)} {b=(QBase y)}
  (QMorphBase f) (QMorphBase g) (QBaseRel y)

-- To show that `QType` morphisms are extensionally equal, we only need to
-- show that they agree (up to codomain equivalence) on _intensionally_
-- equal elements of the domain.
public export
0 MkQMExtEq : {0 x, y : QType} -> {f, g : QMorph x y} ->
  QMIntExt {x} {y} (f, g) -> QMExtEq {x} {y} (f, g)
MkQMExtEq {x} {y} {f} {g} intext =
  PresEqRel
    {a=(QBase x)} {b=(QBase y)}
    {f=(QMorphBase f)} {g=(QMorphBase g)}
    {ra=(QBaseRel x)} {rb=(QRel y)}
    (QMorphPres g) intext

-- In particular, if two `QType` morphisms' base morphisms are extensionally
-- equal, then the `QType` morphisms are equivalent under `QMExtEq`.
public export
0 QMEqFromExt : {0 x, y : QType} -> {f, g : QMorph x y} ->
  ExtEq {a=(QBase x)} {b=(QBase y)}
    (QMorphBase {x} {y} f) (QMorphBase {x} {y} g) ->
  QMExtEq {x} {y} (f, g)
QMEqFromExt {x} {y} {f} {g} eq = MkQMExtEq {x} {y} {f} {g} $
  \_, ea, Refl => rewrite eq ea in PrEquivRefl (snd0 y) $ fst0 g ea

public export
qmId : (a : QType) -> QMorph a a
qmId a = Element0 (id {a=(QBase a)}) $ \_, _ => id

public export
qmComp : {a, b, c : QType} -> QMorph b c -> QMorph a b -> QMorph a c
qmComp {a} {b} {c} g f =
  Element0 (QMorphBase g . QMorphBase f) $ \ea, ea', aeq =>
    QMorphPres g (QMorphBase f ea) (QMorphBase f ea') $ QMorphPres f ea ea' aeq

public export
qmPipe : {a, b, c : QType} -> QMorph a b -> QMorph b c -> QMorph a c
qmPipe {a} {b} {c} = flip $ qmComp {a} {b} {c}

----------------------------------------------------------------------------
---- `QType` as category (with explicit equivalence) internal to `Type` ----
----------------------------------------------------------------------------

public export
0 QTFreeEqRel : (sig : SignatureT QType) -> EqRel (uncurry QMorph sig)
QTFreeEqRel (_, _) =
  MkEq (curry QMExtEq) $ EquivItoIsEquiv QMExtEq QMExtEqEquivI

public export
0 QTidL : {0 a, b : QType} -> (f : QMorph a b) ->
  eqRel (QTFreeEqRel (a, b)) f (qmComp {a} {b} {c=b} (qmId b) f)
QTidL = snd0

public export
0 QTidR : {0 a, b : QType} -> (f : QMorph a b) ->
  eqRel (QTFreeEqRel (a, b)) f (qmComp {a} {b=a} {c=b} f (qmId a))
QTidR = snd0

public export
0 QTassoc : {0 a, b, c, d : QType} ->
  (f : QMorph a b) -> (g : QMorph b c) -> (h : QMorph c d) ->
  eqRel (QTFreeEqRel (a, d))
    (qmComp {a} {b=c} {c=d} h $ qmComp {a} {b} {c} g f)
    (qmComp {a} {b} {c=d} (qmComp {a=b} {b=c} {c=d} h g) f)
QTassoc (Element0 f fpres) (Element0 g gpres) (Element0 h hpres) ea ea' =
  hpres (g $ f ea) (g $ f ea') . gpres (f ea) (f ea') . fpres ea ea'

-- This definition shows that the objects of `QType` with the morphisms
-- of `QMorph` quotiented by `QMExtEq` form a category, with identity and
-- composition given by `qmId` and `qmComp`.

public export
0 QTSCat : SCat
QTSCat = SC
  QType
  (uncurry QMorph)
  qmId
  qmComp
  QTFreeEqRel
  QTidL
  QTidR
  QTassoc

public export
0 QTDCat : Diagram
QTDCat = catToDiagForget QTSCat

----------------------------------------------------
----------------------------------------------------
---- Universal objects and morphisms in `QType` ----
----------------------------------------------------
----------------------------------------------------

-----------------
---- Initial ----
-----------------

public export
QInitBase : Type
QInitBase = Void

public export
0 QInitBaseRel : PrERel QInitBase
QInitBaseRel (v, v') = void v

public export
0 QInitBaseRelEquivI : PrEquivRelI QInitBase QInitBaseRel
QInitBaseRelEquivI (v, v') _ = void v

public export
0 QInitRel : PrEquivRel QInitBase
QInitRel = (QInitBaseRel ** QInitBaseRelEquivI)

public export
QInit : QType
QInit = Element0 QInitBase QInitRel

public export
qInitBase : (x : QType) -> QInitBase -> QBase x
qInitBase x v = void v

public export
QInitPres : (x : QType) -> QPres QInit x (qInitBase x)
QInitPres x v = void v

public export
qInit : (x : QType) -> QMorph QInit x
qInit x = Element0 (qInitBase x) (QInitPres x)

------------------
---- Terminal ----
------------------

public export
QTermBase : Type
QTermBase = Unit

public export
0 QTermBaseRel : PrERel QTermBase
QTermBaseRel ((), ()) = Unit

public export
0 QTermBaseRelEquivI : PrEquivRelI QTermBase QTermBaseRel
QTermBaseRelEquivI ((), ()) eq = ()

public export
0 QTermRel : PrEquivRel QTermBase
QTermRel = (QTermBaseRel ** QTermBaseRelEquivI)

public export
QTerm : QType
QTerm = Element0 QTermBase QTermRel

public export
qTermBase : (x : QType) -> QBase x -> QTermBase
qTermBase x ex = ()

public export
0 QTermPres : (x : QType) -> QPres x QTerm (qTermBase x)
QTermPres x ex ex' eqx = ()

public export
qTerm : (x : QType) -> QMorph x QTerm
qTerm x = Element0 (qTermBase x) (QTermPres x)

-------------------
---- Coproduct ----
-------------------

public export
QCoproductBase : (x, y : QType) -> Type
QCoproductBase x y = Either (QBase x) (QBase y)

public export
0 QCoproductBaseRel : (x, y : QType) -> PrERel (QCoproductBase x y)
QCoproductBaseRel x y exy =
  case exy of
    (Left ex, Left ex') => QBaseRel x (ex, ex')
    (Right ey, Right ey') => QBaseRel y (ey, ey')
    _ => Void

public export
0 QCoproductBaseRelEquivI : (x, y : QType) ->
  PrEquivRelI (QCoproductBase x y) (QCoproductBaseRel x y)
QCoproductBaseRelEquivI (Element0 x xeq) (Element0 y yeq) exyp exypeq =
  case exyp of
    (Left ex, Left ex') => case exypeq of
      PrErefl _ => PrEquivRefl xeq ex
      PrEsym _ _ r => PrEquivSym xeq r
      PrEtrans _ (Left ex'') _ r r' => PrEquivTrans xeq r r'
      PrEtrans _ (Right ey) _ r r' => void r
    (Left ex, Right ey) => case exypeq of
      PrErefl _ impossible
      PrEsym _ _ r => void r
      PrEtrans _ (Left ex'') _ r r' => void r
      PrEtrans _ (Right ey) _ r r' => void r'
    (Right ey, Left ex) => case exypeq of
      PrErefl _ impossible
      PrEsym _ _ r => void r
      PrEtrans _ (Left ex'') _ r r' => void r'
      PrEtrans _ (Right ey) _ r r' => void r
    (Right ey, Right ey') => case exypeq of
      PrErefl _ => PrEquivRefl yeq ey
      PrEsym _ _ r => PrEquivSym yeq r
      PrEtrans _ (Left ex'') _ r r' => void r'
      PrEtrans _ (Right ey) _ r r' => PrEquivTrans yeq r r'

public export
0 QCoproductRel : (x, y : QType) -> PrEquivRel (QCoproductBase x y)
QCoproductRel x y = (QCoproductBaseRel x y ** QCoproductBaseRelEquivI x y)

public export
QCoproduct : QType -> QType -> QType
QCoproduct x y = Element0 (QCoproductBase x y) (QCoproductRel x y)

public export
qInjLBase : (0 x, y : QType) -> QBase x -> QCoproductBase x y
qInjLBase x y = Left

public export
0 QInjLPres : (0 x, y : QType) -> QPres x (QCoproduct x y) (qInjLBase x y)
QInjLPres x y _ _ = id

public export
qInjL : (0 x, y : QType) -> QMorph x (QCoproduct x y)
qInjL x y = Element0 (qInjLBase x y) (QInjLPres x y)

public export
qInjRBase : (0 x, y : QType) -> QBase y -> QCoproductBase x y
qInjRBase x y = Right

public export
0 QInjRPres : (0 x, y : QType) -> QPres y (QCoproduct x y) (qInjRBase x y)
QInjRPres x y _ _ = id

public export
qInjR : (0 x, y : QType) -> QMorph y (QCoproduct x y)
qInjR x y = Element0 (qInjRBase x y) (QInjRPres x y)

public export
qCaseBase : {0 x, y, z : QType} ->
   QMorph x z -> QMorph y z -> QCoproductBase x y -> QBase z
qCaseBase f g = eitherElim (QMorphBase f) (QMorphBase g)

public export
0 QCasePres : {0 x, y, z : QType} ->
   (f : QMorph x z) -> (g : QMorph y z) ->
   QPres (QCoproduct x y) z (qCaseBase {x} {y} {z} f g)
QCasePres f g (Left ex) (Left ex') = QMorphPres f ex ex'
QCasePres f g (Left ex) (Right ey) = \v => void v
QCasePres f g (Right ey) (Left ex) = \v => void v
QCasePres f g (Right ey) (Right ey') = QMorphPres g ey ey'

public export
qCase : {0 x, y, z : QType} ->
  QMorph x z -> QMorph y z -> QMorph (QCoproduct x y) z
qCase f g = Element0 (qCaseBase f g) (QCasePres f g)

public export
qCoproductBimap : {w, x, y, z : QType} ->
  QMorph w y -> QMorph x z -> QMorph (QCoproduct w x) (QCoproduct y z)
qCoproductBimap {w} {x} {y} {z} f g =
  qCase {x=w} {y=x} {z=(QCoproduct y z)}
    (qmComp (qInjL y z) f) (qmComp (qInjR y z) g)

public export
qCoproductMapFst : {w, x, y : QType} ->
  QMorph w y -> QMorph (QCoproduct w x) (QCoproduct y x)
qCoproductMapFst {w} {x} {y} = flip (qCoproductBimap {w} {x} {y} {z=x}) (qmId x)

public export
qCoproductMapSnd : {w, x, y : QType} ->
  QMorph w x -> QMorph (QCoproduct y w) (QCoproduct y x)
qCoproductMapSnd {w} {x} {y} = qCoproductBimap {w=y} {x=w} {y} {z=x} (qmId y)

-----------------
---- Product ----
-----------------

public export
QProductBase : (x, y : QType) -> Type
QProductBase x y = (QBase x, QBase y)

public export
0 QProductBaseRel : (x, y : QType) -> PrERel (QProductBase x y)
QProductBaseRel x y (pxy, pxy') =
  (QBaseRel x (fst pxy, fst pxy'), QBaseRel y (snd pxy, snd pxy'))

public export
0 QProductBaseRelEquivI : (x, y : QType) ->
  PrEquivRelI (QProductBase x y) (QProductBaseRel x y)
QProductBaseRelEquivI (Element0 x xeq) (Element0 y yeq) ((ex, ey), (ex, ey))
  (PrErefl _) =
    (PrEquivRefl xeq ex, PrEquivRefl yeq ey)
QProductBaseRelEquivI (Element0 x xeq) (Element0 y yeq) ((ex, ey), (ex', ey'))
  (PrEsym _ _ (rx, ry)) =
    (PrEquivSym xeq rx, PrEquivSym yeq ry)
QProductBaseRelEquivI (Element0 x xeq) (Element0 y yeq) ((ex, ey), (ex', ey'))
  (PrEtrans _ (ex'', ey'') _ (rx, ry) (rx', ry')) =
    (PrEquivTrans xeq rx rx', PrEquivTrans yeq ry ry')

public export
0 QProductRel : (x, y : QType) -> PrEquivRel (QProductBase x y)
QProductRel x y = (QProductBaseRel x y ** QProductBaseRelEquivI x y)

public export
QProduct : QType -> QType -> QType
QProduct x y = Element0 (QBase x, QBase y) (QProductRel x y)

public export
qProdIntroBase : {0 x, y, z : QType} ->
  QMorph x y -> QMorph x z -> QBase x -> QProductBase y z
qProdIntroBase {x} {y} {z} f g ex = (QMorphBase f ex, QMorphBase g ex)

public export
0 QProductIntroPres : {0 x, y, z : QType} ->
   (f : QMorph x y) -> (g : QMorph x z) ->
   QPres x (QProduct y z) (qProdIntroBase {x} {y} {z} f g)
QProductIntroPres {x} {y} {z} f g ea ea' rx =
  (snd0 f ea ea' rx, snd0 g ea ea' rx)

public export
qProdIntro : {0 x, y, z : QType} ->
  QMorph x y -> QMorph x z -> QMorph x (QProduct y z)
qProdIntro {x} {y} {z} f g =
  Element0 (qProdIntroBase f g) (QProductIntroPres f g)

public export
qProj1Base : (0 x, y : QType) -> QProductBase x y -> QBase x
qProj1Base x y = fst

public export
0 QProj1Pres : (0 x, y : QType) -> QPres (QProduct x y) x (qProj1Base x y)
QProj1Pres x y _ _ = fst

public export
qProj1 : (0 x, y : QType) -> QMorph (QProduct x y) x
qProj1 x y = Element0 (qProj1Base x y) (QProj1Pres x y)

public export
qProj2Base : (0 x, y : QType) -> QProductBase x y -> QBase y
qProj2Base x y = snd

public export
0 QProj2Pres : (0 x, y : QType) -> QPres (QProduct x y) y (qProj2Base x y)
QProj2Pres x y _ _ = snd

public export
qProj2 : (0 x, y : QType) -> QMorph (QProduct x y) y
qProj2 x y = Element0 (qProj2Base x y) (QProj2Pres x y)

public export
qProductBimap : {w, x, y, z : QType} ->
  QMorph w y -> QMorph x z -> QMorph (QProduct w x) (QProduct y z)
qProductBimap {w} {x} {y} {z} f g =
  qProdIntro (qmComp f (qProj1 w x)) (qmComp g (qProj2 w x))

public export
qProductMapFst : {w, x, y : QType} ->
  QMorph w y -> QMorph (QProduct w x) (QProduct y x)
qProductMapFst {w} {x} {y} = flip (qProductBimap {w} {x} {y} {z=x}) (qmId x)

public export
qProductMapSnd : {w, x, y : QType} ->
  QMorph w x -> QMorph (QProduct y w) (QProduct y x)
qProductMapSnd {w} {x} {y} = qProductBimap {w=y} {x=w} {y} {z=x} (qmId y)

------------------------------------
---- Hom-objects (exponentials) ----
------------------------------------

-- Using the notion of extensional equality on QType morphisms (up to the
-- equivalences embedded within the types), we can define the hom-set of
-- of any two `QType`s within `QType` itself, thus making `QType` Cartesian
-- closed.
public export
QHomBase : (x, y : QType) -> Type
QHomBase = QMorph

public export
0 QHomBaseRel : (x, y : QType) -> PrERel (QHomBase x y)
QHomBaseRel x y = QMExtEq {x} {y}

public export
0 QHomBaseRelEquivI : (x, y : QType) ->
  PrEquivRelI (QHomBase x y) (QHomBaseRel x y)
QHomBaseRelEquivI x y = QMExtEqEquivI {x} {y}

public export
0 QHomRel : (x, y : QType) -> PrEquivRel (QHomBase x y)
QHomRel x y = (QHomBaseRel x y ** QHomBaseRelEquivI x y)

public export
QHom : QType -> QType -> QType
QHom x y = Element0 (QHomBase x y) (QHomRel x y)

public export
QExp : QType -> QType -> QType
QExp = flip QHom

public export
qHomEvalBase : (x, y : QType) -> QBase (QProduct (QHom x y) x) -> QBase y
qHomEvalBase x y (Element0 f fpres, ex) = f ex

public export
0 QHomEvalPres : (x, y : QType) ->
  QPres (QProduct (QHom x y) x) y (qHomEvalBase x y)
QHomEvalPres (Element0 x xeq) (Element0 y yeq)
  (Element0 f fpres, ex) (Element0 g gpres, ex') (fgpres, rx) =
    fgpres ex ex' rx

public export
qHomEval : (x, y : QType) -> QMorph (QProduct (QHom x y) x) y
qHomEval x y = Element0 (qHomEvalBase x y) (QHomEvalPres x y)

public export
qHomCurryBase : {0 x, y, z : QType} ->
  QMorph (QProduct x y) z -> QBase x -> QBase (QHom y z)
qHomCurryBase {x=(Element0 x xeq)} {y=(Element0 y yeq)} {z=(Element0 z zeq)}
  (Element0 f fpres) ex =
    Element0
      (curry f ex)
      $ \ey, ey', ry => fpres (ex, ey) (ex, ey') (PrEquivRefl xeq ex, ry)

public export
0 QHomCurryPres : {0 x, y, z : QType} ->
  (f : QMorph (QProduct x y) z) ->
  QPres x (QHom y z) (qHomCurryBase {x} {y} {z} f)
QHomCurryPres {x=(Element0 x xeq)} {y=(Element0 y yeq)} {z=(Element0 z zeq)}
  (Element0 f fpres) ex ex' rx ey ey' ry =
    fpres (ex, ey) (ex', ey') (rx, ry)

public export
qHomCurry : {0 x, y, z : QType} ->
  QMorph (QProduct x y) z -> QMorph x (QHom y z)
qHomCurry {x} {y} {z} f = Element0 (qHomCurryBase f) (QHomCurryPres f)

public export
qHomUncurry : {x, y, z : QType} ->
  QMorph x (QHom y z) -> QMorph (QProduct x y) z
qHomUncurry {x} {y} {z} f = qmComp (qHomEval y z) (qProductMapFst f)

----------------------------------------------
---- Quotation (derived from hom-objects) ----
----------------------------------------------

-- A global element of a `QType` is a morphism from the terminal object.
public export
QGElem : QType -> Type
QGElem = QMorph QTerm

-- We shall refer to a global element of a hom-object as a "quotation".
public export
QQuotation : QType -> QType -> Type
QQuotation = QGElem .* QHom

public export
qQuote : {x, y : QType} -> QMorph x y -> QQuotation x y
qQuote {x} {y} = qHomCurry {x=QTerm} . flip qmComp (qProj2 QTerm x)

public export
qUnquote : {x, y : QType} -> QQuotation x y -> QMorph x y
qUnquote {x} {y} =
  qmPipe {b=(QProduct QTerm x)} (qProdIntro (qTerm x) (qmId x))
  .  qHomUncurry {x=QTerm}

--------------------
---- Equalizers ----
--------------------

public export
QEqualizerBase : {x : QType} -> {0 y : QType} ->
  QMorph x y -> QMorph x y -> Type
QEqualizerBase {x} {y} f g =
  Subset0 (QBase x) $ \ex => QBaseRel y (QMorphBase f ex, QMorphBase g ex)

public export
0 QEqualizerBaseRel : {0 x, y : QType} ->
  (f, g : QMorph x y) -> PrERel (QEqualizerBase {x} {y} f g)
QEqualizerBaseRel {x} {y} f g (Element0 ex fgeq, Element0 ex' fgeq') =
  QBaseRel x (ex, ex')

public export
0 QEqualizerBaseRelEquivI : {0 x, y : QType} ->
  (f, g : QMorph x y) ->
  PrEquivRelI (QEqualizerBase {x} {y} f g) (QEqualizerBaseRel {x} {y} f g)
QEqualizerBaseRelEquivI {x} {y} f g (Element0 ex fgeq, Element0 ex' fgeq') xeq =
  case xeq of
    PrErefl _ => PrEquivRefl (QRel x) ex
    PrEsym _ _ r => PrEquivSym (QRel x) r
    PrEtrans _ (Element0 ex'' rfg) _ r r' => PrEquivTrans (QRel x) r r'

public export
0 QEqualizerRel : {0 x, y : QType} ->
  (f, g : QMorph x y) -> PrEquivRel (QEqualizerBase {x} {y} f g)
QEqualizerRel {x} {y} f g =
  (QEqualizerBaseRel {x} {y} f g ** QEqualizerBaseRelEquivI {x} {y} f g)

public export
QEqualizer : {x : QType} -> {0 y : QType} ->
  QMorph x y -> QMorph x y -> QType
QEqualizer {x} {y} f g =
  Element0 (QEqualizerBase {x} {y} f g) (QEqualizerRel {x} {y} f g)

public export
qEqIntroBase : {0 w, x, y : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph w x) ->
  QMExtEq {x=w} {y}
    (qmComp {a=w} {b=x} {c=y} f h, qmComp {a=w} {b=x} {c=y} g h) ->
  QBase w -> QEqualizerBase {x} {y} f g
qEqIntroBase {w} {x} {y} {f} {g} h eq ew =
  Element0 (fst0 h ew) $ eq ew ew $ PrEquivRefl (QRel w) ew

public export
0 QEqIntroPres : {0 w, x, y : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph w x) ->
  (eq : QMExtEq {x=w} {y}
    (qmComp {a=w} {b=x} {c=y} f h, qmComp {a=w} {b=x} {c=y} g h)) ->
  QPres w (QEqualizer {x} {y} f g) (qEqIntroBase {w} {x} {y} {f} {g} h eq)
QEqIntroPres {w} {x} {y} {f} {g} h eq ew ew' rw = snd0 h ew ew' rw

public export
qEqIntro : {0 w, x, y : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph w x) ->
  QMExtEq {x=w} {y}
    (qmComp {a=w} {b=x} {c=y} f h, qmComp {a=w} {b=x} {c=y} g h) ->
  QMorph w (QEqualizer {x} {y} f g)
qEqIntro {f} {g} h eq =
  Element0 (qEqIntroBase {f} {g} h eq) (QEqIntroPres {f} {g} h eq)

public export
qEqElimBase : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QEqualizerBase {x} {y} f g -> QBase x
qEqElimBase {x} {y} f g = fst0

public export
0 QEqElimPres : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QPres (QEqualizer {x} {y} f g) x (qEqElimBase {x} {y} f g)
QEqElimPres f g (Element0 ex fgeq) (Element0 ex' fgeq') = id

public export
qEqElim : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QMorph (QEqualizer {x} {y} f g) x
qEqElim f g = Element0 (qEqElimBase f g) (QEqElimPres f g)

public export
0 QEqElimEq : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QMExtEq {x=(QEqualizer {x} {y} f g)} {y}
    (qmComp {a=(QEqualizer {x} {y} f g)} {b=x} {c=y} f (qEqElim {x} {y} f g),
     qmComp {a=(QEqualizer {x} {y} f g)} {b=x} {c=y} g (qEqElim {x} {y} f g))
QEqElimEq {x} {y} f g (Element0 ex fgeq) (Element0 ex' fgeq') rx =
  PrEquivTrans (snd0 y) fgeq' $ snd0 f ex ex' rx

----------------------
---- Coequalizers ----
----------------------

public export
QCoequalizerBase : {0 x : QType} -> {y : QType} ->
  QMorph x y -> QMorph x y -> Type
QCoequalizerBase {x} {y} f g = QBase y

public export
0 QCoequalizerBaseRel : {0 x, y : QType} ->
  (f, g : QMorph x y) -> PrERel (QCoequalizerBase {x} {y} f g)
QCoequalizerBaseRel {x} {y} f g =
  CoeqFreeEquivRelF {x=(QBase x)} {y=(QBase y)}
    (QMorphBase f) (QMorphBase g) (QBaseRel x) (QBaseRel y)

public export
0 QCoequalizerBaseRelEquivI : {0 x, y : QType} ->
  (f, g : QMorph x y) ->
  PrEquivRelI (QCoequalizerBase {x} {y} f g) (QCoequalizerBaseRel {x} {y} f g)
QCoequalizerBaseRelEquivI {x} {y} f g =
  CoeqFreeEquivRelI {x=(QBase x)} {y=(QBase y)}
    (QMorphBase f) (QMorphBase g) (QBaseRel x) (QBaseRel y)

public export
0 QCoequalizerRel : {0 x, y : QType} ->
  (f, g : QMorph x y) -> PrEquivRel (QCoequalizerBase {x} {y} f g)
QCoequalizerRel {x} {y} f g =
  (QCoequalizerBaseRel {x} {y} f g ** QCoequalizerBaseRelEquivI {x} {y} f g)

public export
QCoequalizer : {0 x : QType} -> {y : QType} ->
  QMorph x y -> QMorph x y -> QType
QCoequalizer {x} {y} f g =
  Element0 (QCoequalizerBase {x} {y} f g) (QCoequalizerRel {x} {y} f g)

public export
qCoeqIntroBase : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QBase y -> QCoequalizerBase {x} {y} f g
qCoeqIntroBase {x} {y} f g = id

public export
0 QCoeqIntroPres : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QPres y (QCoequalizer {x} {y} f g) (qCoeqIntroBase {x} {y} f g)
QCoeqIntroPres {x} {y} f g ew ew' = InSlFv . Right

public export
qCoeqIntro : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QMorph y (QCoequalizer {x} {y} f g)
qCoeqIntro f g = Element0 (qCoeqIntroBase f g) (QCoeqIntroPres f g)

public export
qCoeqElimBase : {0 x, y, z : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph y z) ->
  QMExtEq {x} {y=z}
    (qmComp {a=x} {b=y} {c=z} h f, qmComp {a=x} {b=y} {c=z} h g) ->
  QCoequalizerBase {x} {y} f g -> QBase z
qCoeqElimBase {x} {y} {z} {f} {g} h eq ey = fst0 h ey

public export
0 QCoeqElimPresSubst : {0 x, y, z : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph y z) ->
  (eq : QMExtEq {x} {y=z}
    (qmComp {a=x} {b=y} {c=z} h f, qmComp {a=x} {b=y} {c=z} h g)) ->
  SliceMorphism {a=(ProductMonad $ QBase y)}
    (CoeqRelF
      (QMorphBase {x} {y} f) (QMorphBase {x} {y} g) (QBaseRel x) (QBaseRel y))
    (QBaseRel z . mapHom (QMorphBase {x=y} {y=z} h))
QCoeqElimPresSubst {x} {y} {z} {f} {g} h hcoeq (ey, ey')
  (Left (Evidence0 (ex, ex') (rx, feq, geq))) =
    rewrite sym feq in rewrite sym geq in
    hcoeq ex ex' rx
QCoeqElimPresSubst {x} {y} {z} {f} {g} h hcoeq (ey, ey')
  (Right yeq) =
    QMorphPres h ey ey' yeq

public export
0 QCoeqElimPresAlg : {0 x, y, z : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph y z) ->
  (eq : QMExtEq {x} {y=z}
    (qmComp {a=x} {b=y} {c=z} h f, qmComp {a=x} {b=y} {c=z} h g)) ->
  SliceAlg {a=(ProductMonad $ QBase y)} (PrEquivF {a=(QBase y)})
    (QBaseRel z . mapHom (QMorphBase {x=y} {y=z} h))
QCoeqElimPresAlg {x} {y} {z} {f} {g} h hcoeq (ey, ey') eqy =
  QRelEquivI z (mapHom (QMorphBase {x=y} {y=z} h) (ey, ey')) $
    prEquivMapHom {r=(QBaseRel z)} {f=(QMorphBase h)} (ey, ey') eqy

public export
0 QCoeqElimPres : {0 x, y, z : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph y z) ->
  (eq : QMExtEq {x} {y=z}
    (qmComp {a=x} {b=y} {c=z} h f, qmComp {a=x} {b=y} {c=z} h g)) ->
  QPres (QCoequalizer {x} {y} f g) z (qCoeqElimBase {x} {y} {z} {f} {g} h eq)
QCoeqElimPres {x} {y} {z} {f} {g} h hcoeq ey ey' =
  freePrEquivEval {a=(QBase y)}
    (CoeqRelF (QMorphBase f) (QMorphBase g) (QBaseRel x) (QBaseRel y))
    (QBaseRel z . mapHom (QMorphBase h))
    (QCoeqElimPresSubst h hcoeq)
    (QCoeqElimPresAlg h hcoeq)
    (ey, ey')

public export
qCoeqElim : {0 x, y, z : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph y z) ->
  QMExtEq {x} {y=z}
    (qmComp {a=x} {b=y} {c=z} h f, qmComp {a=x} {b=y} {c=z} h g) ->
  QMorph (QCoequalizer {x} {y} f g) z
qCoeqElim {x} {y} {z} {f} {g} h eq =
  Element0 (qCoeqElimBase {f} {g} h eq) (QCoeqElimPres {f} {g} h eq)

---------------------------------------------
---------------------------------------------
---- Predicates on and slices of `QType` ----
---------------------------------------------
---------------------------------------------

-----------------------------
---- In categorial style ----
-----------------------------

public export
QSliceObjBase : QType -> Type
QSliceObjBase a = Subset0 QType (flip QMorph a)

public export
0 QSliceTotRel : {a : QType} -> PrERel (QSliceObjBase a)
QSliceTotRel (sl, sl') = QTEquiv (fst0 sl, fst0 sl')

public export
0 QSliceProjRel : {a : QType} -> (sl, sl' : QSliceObjBase a) ->
  (0 _ : QSliceTotRel {a} (sl, sl')) -> Type
QSliceProjRel sl sl' qte = QMExtEq (snd0 sl, qmComp (snd0 sl') $ QTEqIso qte)

public export
0 QSliceObjRel : {a : QType} -> PrERel (QSliceObjBase a)
QSliceObjRel (sl, sl') = Exists0 (QSliceTotRel (sl, sl')) (QSliceProjRel sl sl')

public export
0 QSliceObjRelEquivI : {a : QType} ->
  PrEquivRelI (QSliceObjBase a) (QSliceObjRel {a})
QSliceObjRelEquivI {a=(Element0 a (aeq ** aequiv))}
  (Element0 (Element0 x (xeq ** xequiv)) (Element0 f fpres),
   Element0 (Element0 x' (xeq' ** xequiv')) (Element0 f' fpres'))
  eq =
    case eq of
      PrErefl _ =>
        Evidence0
          (QTE (\_, _ => id, \_, _ => id))
          fpres
      PrEsym _ _ (Evidence0 (QTE (impl, impr)) gpres) =>
        Evidence0
          (QTE (impr, impl))
          $ \ea, ea', eaeq =>
            aequiv (f ea, f' ea') $
              PrEtrans (f ea) (f' ea) (f' ea')
                (fpres' ea ea' $ impr ea ea' eaeq)
                $ aequiv (f ea, f' ea) $
                  PrEtrans (f ea) (f ea') (f' ea)
                    (aequiv (f ea', f' ea) $ PrEsym (f' ea) (f ea') $
                      gpres ea ea' $ impr ea ea' eaeq)
                    (fpres ea ea' eaeq)
      PrEtrans _ (Element0 (Element0 z (zeq ** zequiv)) (Element0 g gpres)) _
        (Evidence0 (QTE (impl, impr)) gfpres)
        (Evidence0 (QTE (impl', impr')) fgpres) =>
          Evidence0
            (QTE
              (\ea, ea' => impl ea ea' . impl' ea ea',
               \ea, ea' => impr' ea ea' . impr ea ea'))
            $ \ea, ea', eaeq =>
              aequiv (f ea, f' ea') $
                PrEtrans (f ea) (g ea) (f' ea')
                  (gfpres ea ea' $ impl' ea ea' eaeq)
                  $ aequiv (f ea, g ea) $
                    PrEtrans (f ea) (g ea') (g ea)
                      (aequiv (g ea', g ea) $ PrEsym (g ea) (g ea') $
                        gpres ea ea' $ impl' ea ea' eaeq)
                      $ fgpres ea ea' eaeq

public export
0 QSliceObjRelEquiv : {a : QType} -> PrEquivRel (QSliceObjBase a)
QSliceObjRelEquiv {a} = (QSliceObjRel {a} ** QSliceObjRelEquivI {a})

public export
QSliceObj : QType -> QType
QSliceObj a = Element0 (QSliceObjBase a) (QSliceObjRelEquiv {a})

---------------------------------
---- In dependent-type style ----
---------------------------------

-- A predicate is a dependent type in the type-theoretic view.  In the
-- categorial view, it is a discrete presheaf, which is the opposite category
-- of a discrete copresheaf, which is equivalent to a slice category.
-- So the category of predicates on a `QType` is equivalent to the opposite
-- of the slice category of `QType` over that `QType`.
public export
QPred : QType -> QType
QPred a = QHom a QTypeQT

----------------------------
----------------------------
---- Quivers in `QType` ----
----------------------------
----------------------------

-- A quiver in `QType` is a functor from the walking quiver -- a generic
-- figure with two objects and two parallel non-identity morphisms -- to
-- `QType`.  Such a functor is determined by a choice of two `QType`s and
-- two parallel `QMorph`s between them.
--
-- However, there is another way of looking at this:  when we view the
-- functor as contravariant, so that it is a presheaf rather than a
-- copresheaf -- a functor from the _opposite_ category of the walking quiver
-- to `QType` -- it is equivalent to a `QType` together with a `QType`
-- dependent on pairs of the first `QType`, or, to put it another way, a
-- `QType` together with a slice over its product.
public export
QQuivEdge : QType -> QType
QQuivEdge vert = QPred $ QProduct vert vert

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
DiscPi {pos} nfield sld i = HVect {k=(nfield i)} $ finFToVect $ sld . MkDPair i

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
  HVect {k=(nfield i)} $ finFToVect $ sld . MkDPair i

---------------------------
---------------------------
---- Splices of `Type` ----
---------------------------
---------------------------

-------------------------------
---- Objects and morphisms ----
-------------------------------

public export
SpliceCat : Type
SpliceCat = (Type, Type)

public export
SpliceBase : SpliceCat -> Type
SpliceBase = snd

public export
SpliceCobase : SpliceCat -> Type
SpliceCobase = fst

public export
SpliceBasePair : SpliceCat -> Type
SpliceBasePair = ProductMonad . SpliceBase

public export
SpliceCobasePair : SpliceCat -> Type
SpliceCobasePair = ProductMonad . SpliceCobase

public export
SpliceDualPair : SpliceCat -> Type
SpliceDualPair cat = (SpliceCobase cat, SpliceBase cat)

public export
SpliceDualPairBase : {cat : SpliceCat} ->
  SpliceDualPair cat -> SpliceBase cat
SpliceDualPairBase {cat} = snd

public export
SpliceDualPairCobase : {cat : SpliceCat} ->
  SpliceDualPair cat -> SpliceCobase cat
SpliceDualPairCobase {cat} = fst

public export
SpliceBaseObj : SpliceCat -> Type
SpliceBaseObj = SliceObj . SpliceBase

public export
SpliceBaseTot : (cat : SpliceCat) -> SpliceBaseObj cat -> Type
SpliceBaseTot cat = Sigma {a=(SpliceBase cat)}

public export
SpliceBaseFst : {cat : SpliceCat} -> {base : SpliceBaseObj cat} ->
  SpliceBaseTot cat base -> SpliceBase cat
SpliceBaseFst {cat} {base} = fst

public export
SpliceBaseSnd : {cat : SpliceCat} -> {base : SpliceBaseObj cat} ->
  (spl : SpliceBaseTot cat base) -> base (SpliceBaseFst {cat} spl)
SpliceBaseSnd {cat} {base} = snd

public export
SpliceCobaseObj : (cat : SpliceCat) -> SpliceBaseObj cat -> Type
SpliceCobaseObj cat b = SpliceCobase cat -> SpliceBaseTot cat b

public export
SpliceObj : SpliceCat -> Type
SpliceObj cat = Subset0 (SpliceBaseObj cat) (SpliceCobaseObj cat)

public export
SpliceObjBase : {cat : SpliceCat} -> SpliceObj cat -> SpliceBaseObj cat
SpliceObjBase {cat} = fst0

public export
0 SpliceObjCobase : {cat : SpliceCat} -> (spl : SpliceObj cat) ->
  SpliceCobaseObj cat (SpliceObjBase {cat} spl)
SpliceObjCobase {cat} = snd0

public export
SpliceObjTot : {cat : SpliceCat} -> SpliceObj cat -> Type
SpliceObjTot {cat} spl = SpliceBaseTot cat $ SpliceObjBase {cat} spl

public export
SpliceObjBaseFst : {cat : SpliceCat} -> (spl : SpliceObj cat) ->
  SpliceObjTot {cat} spl -> SpliceBase cat
SpliceObjBaseFst {cat} spl =
  SpliceBaseFst {cat} {base=(SpliceObjBase {cat} spl)}

public export
SpliceObjBaseSnd : {cat : SpliceCat} -> (spl : SpliceObj cat) ->
  (e : SpliceObjTot {cat} spl) ->
  SpliceObjBase {cat} spl (SpliceObjBaseFst {cat} spl e)
SpliceObjBaseSnd {cat} spl =
  SpliceBaseSnd {cat} {base=(SpliceObjBase {cat} spl)}

public export
SpliceCobaseTotSlice : {cat : SpliceCat} -> (spl : SpliceObj cat) ->
  (i : SpliceBase cat) -> SliceObj (SpliceObjBase {cat} spl i)
SpliceCobaseTotSlice {cat} spl i j = PreImage (SpliceObjCobase spl) (i ** j)

public export
0 SpliceObjCobaseBaseProj : {cat : SpliceCat} ->
  SpliceObj cat -> SpliceCobase cat -> SpliceBase cat
SpliceObjCobaseBaseProj {cat} spl e =
  SpliceObjBaseFst {cat} spl $ SpliceObjCobase spl e

public export
SpliceCobaseBaseSlice : {cat : SpliceCat} ->
  (spl : SpliceObj cat) -> SliceObj (SpliceBase cat)
SpliceCobaseBaseSlice {cat} spl e = PreImage (SpliceObjCobaseBaseProj spl) e

SpliceSig : SpliceCat -> Type
SpliceSig = SignatureT . SpliceObj

public export
SpliceDom : {cat : SpliceCat} -> SpliceSig cat -> SpliceObj cat
SpliceDom = fst

public export
SpliceCod : {cat : SpliceCat} -> SpliceSig cat -> SpliceObj cat
SpliceCod = snd

public export
SpliceDomTot : {cat : SpliceCat} -> SpliceSig cat -> Type
SpliceDomTot {cat} sig = SpliceObjTot $ SpliceDom {cat} sig

public export
SpliceCodTot : {cat : SpliceCat} -> SpliceSig cat -> Type
SpliceCodTot {cat} sig = SpliceObjTot $ SpliceCod {cat} sig

public export
SpliceDomBase : {cat : SpliceCat} -> SpliceSig cat -> SpliceBaseObj cat
SpliceDomBase {cat} sig = SpliceObjBase $ SpliceDom {cat} sig

public export
SpliceCodBase : {cat : SpliceCat} -> SpliceSig cat -> SpliceBaseObj cat
SpliceCodBase {cat} sig = SpliceObjBase $ SpliceCod {cat} sig

public export
0 SpliceDomCobase : {cat : SpliceCat} ->
  (sig : SpliceSig cat) -> SpliceCobaseObj cat (SpliceDomBase {cat} sig)
SpliceDomCobase {cat} sig = SpliceObjCobase $ SpliceDom {cat} sig

public export
0 SpliceCodCobase : {cat : SpliceCat} ->
  (sig : SpliceSig cat) -> SpliceCobaseObj cat (SpliceCodBase {cat} sig)
SpliceCodCobase {cat} sig = SpliceObjCobase $ SpliceCod {cat} sig

public export
SpliceDomCobaseTotSlice : {cat : SpliceCat} -> (sig : SpliceSig cat) ->
  (i : SpliceBase cat) -> SliceObj (SpliceDomBase {cat} sig i)
SpliceDomCobaseTotSlice {cat} sig =
  SpliceCobaseTotSlice {cat} (SpliceDom {cat} sig)

public export
SpliceCodCobaseTotSlice : {cat : SpliceCat} -> (sig : SpliceSig cat) ->
  (i : SpliceBase cat) -> SliceObj (SpliceCodBase {cat} sig i)
SpliceCodCobaseTotSlice {cat} sig =
  SpliceCobaseTotSlice {cat} (SpliceCod {cat} sig)

public export
SpliceDomCobaseBaseSlice : {cat : SpliceCat} ->
  (sig : SpliceSig cat) -> SliceObj (SpliceBase cat)
SpliceDomCobaseBaseSlice {cat} sig =
  SpliceCobaseBaseSlice {cat} (SpliceDom {cat} sig)

public export
SpliceCodCobaseBaseSlice : {cat : SpliceCat} ->
  (sig : SpliceSig cat) -> SliceObj (SpliceBase cat)
SpliceCodCobaseBaseSlice {cat} sig =
  SpliceCobaseBaseSlice {cat} (SpliceCod {cat} sig)

public export
SpliceBaseMorph : {cat : SpliceCat} -> SpliceSig cat -> Type
SpliceBaseMorph {cat} sig =
  SliceMorphism {a=(SpliceBase cat)}
    (SpliceDomBase {cat} sig)
    (SpliceCodBase {cat} sig)

public export
0 SpliceCobaseMorph : {cat : SpliceCat} -> (sig : SpliceSig cat) ->
  SpliceBaseMorph {cat} sig -> Type
SpliceCobaseMorph {cat} sig m =
  (i : SpliceBase cat) ->
  SliceMorphism {a=(SpliceDomBase {cat} sig i)}
    (BaseChangeF (m i) $ SpliceCodCobaseTotSlice {cat} sig i)
    (SpliceDomCobaseTotSlice {cat} sig i)

public export
SpliceMorph : {cat : SpliceCat} -> SpliceSig cat -> Type
SpliceMorph {cat} sig =
  Subset0 (SpliceBaseMorph {cat} sig) (SpliceCobaseMorph {cat} {sig})

public export
SpliceMorphBase : {cat : SpliceCat} -> {sig : SpliceSig cat} ->
  SpliceMorph {cat} sig -> SpliceBaseMorph {cat} sig
SpliceMorphBase = fst0

public export
0 SpliceMorphCobase : {cat : SpliceCat} -> {sig : SpliceSig cat} ->
  (m : SpliceMorph {cat} sig) ->
  SpliceCobaseMorph {cat} sig (SpliceMorphBase {cat} {sig} m)
SpliceMorphCobase = snd0

-----------------------------
---- Polynomial functors ----
-----------------------------

public export
SpliceBaseChangeBase : {cat : SpliceCat} -> {d : Type} ->
  (d -> SpliceBase cat) -> SpliceObj cat -> SpliceBaseObj (SpliceCobase cat, d)
SpliceBaseChangeBase {cat} {d} f spl = ?SpliceBaseChangeBase_hole

public export
0 SpliceBaseChangeCobase : {cat : SpliceCat} -> {d : Type} ->
  (f : d -> SpliceBase cat) -> (spl : SpliceObj cat) ->
  SpliceCobaseObj (SpliceCobase cat, d) (SpliceBaseChangeBase {cat} {d} f spl)
SpliceBaseChangeCobase {cat} {d} f spl = ?SpliceBaseChangeCobase_hole

{-
public export
SpliceBaseChange : {cat : SpliceCat} -> {d : Type} ->
  (d -> SpliceBase cat) -> SpliceObj cat -> SpliceObj (SpliceCobase cat, d)
SpliceBaseChange {cat} {d} f spl =
  Element0
    (SpliceBaseChangeBase {cat} {d} f spl)
    (SpliceBaseChangeCobase {cat} {d} f spl)
    -}

public export
SpliceSigmaBase : {cat : SpliceCat} -> {d : Type} ->
  (SpliceBase cat -> d) -> SpliceObj cat -> SpliceBaseObj (SpliceCobase cat, d)
SpliceSigmaBase {cat} {d} f spl = ?SpliceSigmaBase_hole

public export
0 SpliceSigmaCobase : {cat : SpliceCat} -> {d : Type} ->
  (f : SpliceBase cat -> d) -> (spl : SpliceObj cat) ->
  SpliceCobaseObj (SpliceCobase cat, d) (SpliceSigmaBase {cat} {d} f spl)
SpliceSigmaCobase {cat} {d} f spl = ?SpliceSigmaCobase_hole

{-
public export
SpliceSigma : {cat : SpliceCat} -> {d : Type} ->
  (SpliceBase cat -> d) -> SpliceObj cat -> SpliceObj (SpliceCobase cat, d)
SpliceSigma {cat} {d} f spl =
  Element0
    (SpliceSigmaBase {cat} {d} f spl)
    (SpliceSigmaCobase {cat} {d} f spl)
    -}

public export
0 SpliceCosigmaBase : {cat : SpliceCat} -> {b : Type} ->
  (b -> SpliceCobase cat) -> SpliceObj cat -> SpliceBaseObj (b, SpliceBase cat)
SpliceCosigmaBase {cat} {b} f spl = SpliceObjBase {cat} spl

public export
0 SpliceCosigmaCobase : {cat : SpliceCat} -> {b : Type} ->
  (f : b -> SpliceCobase cat) -> (spl : SpliceObj cat) ->
  SpliceCobaseObj (b, SpliceBase cat) (SpliceCosigmaBase {cat} {b} f spl)
SpliceCosigmaCobase {cat} {b} f spl = SpliceObjCobase spl . f

public export
0 SpliceCosigma : {cat : SpliceCat} -> {b : Type} ->
  (f : b -> SpliceCobase cat) -> SpliceObj cat -> SpliceObj (b, SpliceBase cat)
SpliceCosigma {cat} {b} f spl =
  Element0
    (SpliceCosigmaBase {cat} {b} f spl)
    (SpliceCosigmaCobase {cat} {b} f spl)

----------------------------------------------
---- Double category of splices of `Type` ----
----------------------------------------------

public export
spliceId : {cat : SpliceCat} ->
  (spl : SpliceObj cat) -> SpliceMorph {cat} (spl, spl)
spliceId {cat} spl = ?spliceId_hole

public export
spliceComp : {cat : SpliceCat} ->
  {spl, spl', spl'' : SpliceObj cat} ->
  SpliceMorph {cat} (spl', spl'') ->
  SpliceMorph {cat} (spl, spl') ->
  SpliceMorph {cat} (spl, spl'')
spliceComp {cat} spl = ?spliceComp_hole

public export
SpliceObjComp : {0 x, y, z : Type} ->
  SpliceObj (y, z) -> SpliceObj (x, z) -> SpliceObj (x, y)
SpliceObjComp {x} {y} {z} spl' spl = ?SpliceObjComp_hole

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
SortMorphism {s} sl sl' = HVect {k=s} $ map (uncurry HomProf) $ zip sl sl'

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
  HVect {k=a} $ RawOpDir {s} {a} op sorts

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

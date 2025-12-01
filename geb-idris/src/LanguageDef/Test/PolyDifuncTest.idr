module LanguageDef.Test.PolyDifuncTest

import Test.TestLibrary
import Library.IdrisAlgebra
import LanguageDef.PolyDifunc
import LanguageDef.PolyCat

%default total

public export
NegPosMaybe : Type -> Type
NegPosMaybe r = Either Unit (r -> r, r)

public export
NegPosMaybeP : ProfunctorSig
NegPosMaybeP x y = Either Unit (x -> y, y)

public export
NegPosMaybePdimap : TypeDimapSig NegPosMaybeP
NegPosMaybePdimap s t a b mas mtb (Left ()) =
  Left ()
NegPosMaybePdimap s t a b mas mtb (Right (mst, et)) =
  Right (mtb . mst . mas, mtb et)

public export
NegPosMaybeMendlerExt : Type -> Type
NegPosMaybeMendlerExt = ProfMendlerExt NegPosMaybeP

public export
NegPosMaybeMendlerUniv : Type -> Type
NegPosMaybeMendlerUniv = ProfMendlerUniv NegPosMaybeP

public export
NegPosMaybeMendlerExtFormula : (c : Type) ->
  NegPosMaybeMendlerExt c = (x : Type ** (x -> c, Either () (x -> x, x)))
NegPosMaybeMendlerExtFormula c = Refl

public export
NegPosMaybeMendlerUnivFormula : (c : Type) ->
  NegPosMaybeMendlerUniv c =
  NaturalTransformation
    (\y : Type => (x : Type) -> (x -> c) -> Either () (x -> x, x) -> y)
    (Prelude.id {a=Type})
NegPosMaybeMendlerUnivFormula c = Refl

public export
NegPosMaybeMendlerExtPos : Type
NegPosMaybeMendlerExtPos = (x : Type ** Either () (x -> x, x))

public export
NegPosMaybeMendlerExtDir : NegPosMaybeMendlerExtPos -> Type
NegPosMaybeMendlerExtDir = DPair.fst

public export
NegPosMaybeMendlerExtPoly : PolyFunc
NegPosMaybeMendlerExtPoly =
  (NegPosMaybeMendlerExtPos ** NegPosMaybeMendlerExtDir)

public export
InterpNegPosMaybeMendlerExtPoly : Type -> Type
InterpNegPosMaybeMendlerExtPoly = InterpPolyFunc NegPosMaybeMendlerExtPoly

public export
NegPosMaybeMendlerExtFromPoly :
  NaturalTransformation InterpNegPosMaybeMendlerExtPoly NegPosMaybeMendlerExt
NegPosMaybeMendlerExtFromPoly c ((x ** dd) ** mxc) = (x ** (mxc, dd))

public export
NegPosMaybeMendlerExtToPoly :
  NaturalTransformation NegPosMaybeMendlerExt InterpNegPosMaybeMendlerExtPoly
NegPosMaybeMendlerExtToPoly c (x ** (mxc, dd)) = ((x ** dd) ** mxc)

public export
NegPosMaybePPpos : Type
NegPosMaybePPpos = Fin 2

public export
NegPosMaybePPposF : Type -> Type
NegPosMaybePPposF = const NegPosMaybePPpos

-- This polynomial functor describes the directions of the polynomial
-- profunctor at the given position.  The meaning of the directions being
-- a functor rather than a type is that there may be negative occurrences
-- in the datatype:  the constant component determines positive directions,
-- while the directions of the direction functor are negative directions of
-- the overall profunctor.
public export
NegPosMaybePPdirPF : NegPosMaybePPpos -> PolyFunc
NegPosMaybePPdirPF FZ = PFInitialArena
NegPosMaybePPdirPF (FS FZ) = pfCoproductArena PFIdentityArena PFTerminalArena

public export
NegPosMaybePPdirF : NegPosMaybePPpos -> Type -> Type
NegPosMaybePPdirF = InterpPolyFunc . NegPosMaybePPdirPF

public export
NegPosMaybePPdir : (x : Type) -> SliceObj (NegPosMaybePPposF x)
NegPosMaybePPdir = flip NegPosMaybePPdirF

-- `NegPosMaybePP` is a parameterized polynomial functor whose value
-- at each type `x` is a functor with only positive occurrences -- that is,
-- a (polynomial) functor on `Type` -- resulting from substituting `x` in
-- for the negative occurrences in the original profunctor `NegPosMaybeP`.
-- Because we're substituting the type parameter into negative occurrences,
-- `NegPosMaybePP` is contravariant -- that is, it is a functor from
-- `op(Type)` to `Poly(Type)`.  As we shall see in the next lemma, only
-- its directions, not its positions, depend on the type parameter, although
-- that need not necessarily be the case for all polynomial profunctors.
--
-- The way we can view this functor is as follows:
--
-- - The _positions_ of this functor are the fields of the (dual-variance)
--   recursive data structure which it generates.  In other words, they play
--   the role of the _directions_ of a (purely) covariant polynomial functor.
-- - The _directions_ of this functor at a given position are the negative
--   occurences of the data type in that particular field.  For example, a
--   position with three directions represents a field which requires three
--   negative occurrences of the data type -- to fill in that field requires
--   a function from a product of three occurrences of the data type to
--   the data type.  Thus in particular if there are no directions, then their
--   product is the terminal object, and a function from that is equivalent
--   to simply a term of the codomain, so the field can be filled in simply
--   by a term of the data type -- in other words, the same way as a field of
--   a (purely) covariant polynomial functor.
public export
NegPosMaybePP : PolyPolyFunc
NegPosMaybePP x = (NegPosMaybePPposF x ** NegPosMaybePPdir x)

public export
0 NegPosMaybePPposConst :
  (x : Type) -> NegPosMaybePP x = (NegPosMaybePPpos ** NegPosMaybePPdir x)
NegPosMaybePPposConst x = Refl

public export
InterpNegPosMaybePP : ProfunctorSig
InterpNegPosMaybePP = PolyPolyProf NegPosMaybePP

public export
InterpNegPosMaybePPfromPolyPoly : TypeProfNT InterpNegPosMaybePP NegPosMaybeP
InterpNegPosMaybePPfromPolyPoly x y (FZ ** dm) =
  Left ()
InterpNegPosMaybePPfromPolyPoly x y ((FS FZ) ** dm) =
  Right (\ex => dm (Left () ** const ex), dm (Right () ** voidF x))

public export
InterpNegPosMaybePPtoPolyPoly : TypeProfNT NegPosMaybeP InterpNegPosMaybePP
InterpNegPosMaybePPtoPolyPoly x y (Left ()) =
  (FZ ** \(i ** mvx) => void i)
InterpNegPosMaybePPtoPolyPoly x y (Right (mxy, ey)) =
  (FS FZ ** \(i ** mux) => case i of Left () => mxy $ mux () ; Right () => ey)

-- The contramap of `NegPosMaybePP` leaves both the overall positions
-- and the per-field positions alone, and post-composes the given morphism
-- with the per-field directions to produce the on-directions function of
-- a vertical natural transformation (i.e. a natural transformation whose
-- on-positions function is the identity).
--
-- Thus, given a morphism `x' -> x`, it assigns negative occurrences
-- of the datatype-generating polynomial functor at `x'` to negative
-- occurrences of the datatype-generating polynomial functor at `x`.
--
-- Thus in turn it defines the 'lmap' of the profunctor which it generates
-- by turning morphisms `(d -> x) -> y` into morphisms `(d -> x') -> y`
-- by _pre_-composing the morphism from `(d -> x')` to `(d -> x)` which itself
-- is defined by _post_-composing the morphism `x' -> x`.
--
-- The net effect is that if we have a function from `d` occurrences of
-- `x` to `y`, we can turn it into a function from `d` occurrences of
-- `x'` to `y` by, for each collection of `d` occurrences of `x'`,
-- converting all `d` occurrences of `x'` to `x` using the given morphism
-- and then applying the given function to the collection to get a `y`.
-- We could view the contramap as defining how to transform the datatype
-- as a whole given a transformation between representations of itself
-- as used in its negative occurrences.
public export
npnpContramap : PolyPolyFuncContramap NegPosMaybePP
npnpContramap a b mba = (id ** \i => InterpPFMap (NegPosMaybePPdirPF i) mba)

public export
NegPosMaybePPdirMu : NegPosMaybePPpos -> Type
NegPosMaybePPdirMu = PolyFuncMu . NegPosMaybePPdirPF

public export
NegPosNat : Type
NegPosNat = Mu NegPosMaybe

public export
NegPosNatOP : Type
NegPosNatOP = ProfOpMu NegPosMaybeP

public export
NegPosNatP : Type
NegPosNatP = ProfMu NegPosMaybeP

public export
NegPosNatPMu : Type
NegPosNatPMu = PolyPolyFuncFix NegPosMaybePP

public export
NegPosFM : Type -> Type
NegPosFM = FreeMonad NegPosMaybe

public export
NegPosOPFM : ProfunctorSig
NegPosOPFM = ProfOpFreeM NegPosMaybeP

public export
NegPosPFM : ProfunctorSig
NegPosPFM = ProfFreeM NegPosMaybeP

public export
npnZ : NegPosNat
npnZ = inFC $ Left ()

public export
npnpZ : NegPosNatP
npnpZ = inPFC $ Left ()

public export
npnS : (NegPosNat -> NegPosNat) -> NegPosNat -> NegPosNat
npnS f n = inFC $ Right (f, n)

public export
npnpS : (NegPosNatOP -> NegPosNatP) -> NegPosNatP -> NegPosNatP
npnpS f n = inPFC $ Right (f, n)

public export
NPNAlg : Type -> Type
NPNAlg a = Either Unit (NegPosNat -> NegPosNat, NegPosNat, Nat -> a) -> a

mutual
  public export
  npnPara : {a : Type} -> NPNAlg a -> NegPosNat -> a
  npnPara {a} alg (InFree (TFV ev)) =
    void ev
  npnPara {a} alg (InFree (TFC (Left ()))) =
    alg $ Left ()
  npnPara {a} alg (InFree (TFC (Right (f, n)))) =
    alg $ Right (f, n, npnIterPara {a} alg n f)

  public export
  npnIterPara : {a : Type} ->
    NPNAlg a -> NegPosNat -> (NegPosNat -> NegPosNat) -> Nat -> a
  npnIterPara {a} alg n f Z = npnPara {a} alg n
  npnIterPara {a} alg n f (S k) = npnIterPara {a} alg (f n) f k

public export
NPNPAlg : Type -> Type
NPNPAlg a = Either Unit (NegPosNatP -> NegPosNatP, NegPosNatP, Nat -> a) -> a

public export
npnToNatAlg : NPNAlg Nat
npnToNatAlg (Left ()) = Z
npnToNatAlg (Right (f, n, fkn)) = S $ fkn $ S Z

public export
npnToNat : NegPosNat -> Nat
npnToNat = npnPara {a=Nat} npnToNatAlg

public export
NPNPPAlg : Type -> Type
NPNPPAlg a =
  Either Unit (NegPosNatPMu -> NegPosNatPMu, NegPosNatPMu, Nat -> a) -> a

public export
NegPosNatMendlerMu : Type
NegPosNatMendlerMu = Mu NegPosMaybeMendlerExt

public export
NPNMAlg : Type -> Type
NPNMAlg a =
  Either
    Unit
    (NegPosNatMendlerMu -> NegPosNatMendlerMu, NegPosNatMendlerMu, Nat -> a) ->
  a

-- See https://www.schoolofhaskell.com/user/edwardk/phoas#phoas-is-free.

-- A parameterized polynomial free monad, whose value at some contravariant
-- type parameter `x` is the free monad of the polynomial functor which
-- from comes from evaluating `NegPosMaybePP` at `x`.
--
-- In this specific case, evaluating `NegPosMaybePP` at `x` yields
-- a polynomial functor with one position with no directions and one
-- position with `x + 1` directions.  That means that evaluating it
-- at `Void` produces a type whose closed terms are unlabeled lists,
-- which is equivalent to `Nat`; evaluating it at `Unit` produces a type
-- whoose closed terms are unlabeled binary trees, evaluating it at `Fin 2`
-- produces a type whose closed terms are unlabaled ternary trees, and so
-- forth.  In all cases, the type of the free monad at `x` when evaluated
-- at `y` is the corresponding type of open terms with variables drawn from `y`.
public export
NegPosNatRec : PolyPolyFunc
NegPosNatRec = ProfToParamFreeM NegPosMaybePP

public export
NegPosNatRecPF : ProfunctorSig
NegPosNatRecPF = PolyPolyProf NegPosNatRec

-- The contramap of `NegPosNatRec` lifts the contramap of `NegPosMaybePP`
-- to the free monad generated by it.  It may be seen as applying a
-- translation between representations (used for negative occurrences)
-- of the datatype to the recursive datatype with open terms generated by
-- the free monad.
public export
NegPosNatRecContramap : (a, b : Type) -> (b -> a) ->
  PolyNatTrans (NegPosNatRec a) (NegPosNatRec b)
NegPosNatRecContramap = PTPFMcontramap NegPosMaybePP npnpContramap

-- The `lmap` part of the `dimap` of `NegPosNatRecPF` comes from
-- `NegPosNatRecContramap`; the `rmap` part comes from the `map` of
-- the (pointwise) free monads, which maps the variables of the open
-- terms.  So the `lmap` translates term representations in negative
-- positions, while the `rmap` translates term representations in positive
-- positions.
public export
NegPosNatRecPFdimap : TypeDimapSig NegPosNatRecPF
NegPosNatRecPFdimap = polyPolyProfDimap NegPosNatRec NegPosNatRecContramap

public export
NegPosNatRecPFlmap : TypeLmapSig NegPosNatRecPF
NegPosNatRecPFlmap = polyPolyProfLmap NegPosNatRec NegPosNatRecContramap

public export
NegPosNatRecPFrmap : TypeRmapSig NegPosNatRecPF
NegPosNatRecPFrmap = polyPolyProfRmap NegPosNatRec NegPosNatRecContramap

public export
0 NegPosNatRecPFdimap0 : TypeDimapSig NegPosNatRecPF
NegPosNatRecPFdimap0 = NegPosNatRecPFdimap

public export
NegPosNatPFFormula : (x, y : Type) ->
  NegPosNatRecPF x y = InterpPolyFuncFreeM (NegPosMaybePP x) y
NegPosNatPFFormula x y = Refl

-- Below we spell out a more verbose description of `NegPosNatRecPF`.
-- It is a parameterized free monad which, given types `x` and `y`,
-- represents a recursive type of open terms whose negative occurrences are
-- functions from `x` and whose positive occurrences include variables
-- drawn from `y` along with (recursively) terms of shape `NegPosMaybePP x`.
-- Its `lmap` translates the negative occurrences by precomposition, while
-- its `rmap` translates the variables by postcomposition.
public export
NegPosNatEndPos : Type -> Type
NegPosNatEndPos x = PolyFuncFreeMPos (NegPosMaybePP x)

-- As a polynomial functor, the interpretation of `NegPosNatRecPF(x)`
-- consists of a choice of position and a choice of directions at that position.
-- The positions are those of a free monad, which constitute unlabeled trees
-- of the shape of the generating functor.
public export
NegPosNatEndFst : Type -> Type
NegPosNatEndFst = NegPosNatEndPos

public export
negPosNatEndFstLmap : (a, b : Type) ->
  (b -> a) -> NegPosNatEndFst a -> NegPosNatEndFst b
negPosNatEndFstLmap a b mba =
  pntOnPos
    {p=(PolyFuncFreeM $ NegPosMaybePP a)}
    {q=(PolyFuncFreeM $ NegPosMaybePP b)}
    (NegPosNatRecContramap a b mba)

-- The directions at a given position of the free monad are the
-- variable terms -- the leaves drawn from the type of variables,
-- rather than from positions of the generating functor, which
-- may be seen as representing trees, or places that trees can
-- be substituted into.  A term of the free-monad type therefore
-- comprises a choice of functor-shaped tree and a choice of variable for
-- each variable term within that tree.
public export
NegPosNatEndDir : (x : Type) -> NegPosNatEndFst x -> Type
NegPosNatEndDir x = PolyFuncFreeMDir (NegPosMaybePP x)

public export
NegPosNatEndSnd : (x : Type) -> NegPosNatEndFst x -> Type -> Type
NegPosNatEndSnd x i y = NegPosNatEndDir x i -> y

public export
NegPosNatPFFormulaLong : (x, y : Type) ->
  NegPosNatRecPF x y = (i : NegPosNatEndFst x ** NegPosNatEndSnd x i y)
NegPosNatPFFormulaLong x y = Refl

-- The first component of the `dimap` of a `NegPosNatRecPF` is determined
-- by the `lmap` of the first component of the `NegPosNatRecPF`.  In other
-- words, the position of the output of a `dimap` is independent of the
-- input's assignment to directions - it depends only on the input's choice
-- of position.  Again considering it's a free monad, that means that it
-- depends on the choice of a _shape_ of a tree.
public export
0 NPNdimapFstIsLmap : (s, t, a, b : Type) -> (mas : a -> s) -> (mtb : t -> b) ->
  (i : NegPosNatEndFst s) -> (d, d' : NegPosNatEndSnd s i t) ->
  fst (NegPosNatRecPFdimap s t a b mas mtb (i ** d)) =
  fst (NegPosNatRecPFlmap s t a mas (i ** d'))
NPNdimapFstIsLmap s t a b mas mtb i d d' = Refl

-- The end of a `NegPosNatRecPF` is a polymorphic term -- a selection for
-- each type of a term which uses that type for _both_ the negative and
-- the positive occurrences.
public export
NegPosNatEnd : Type
NegPosNatEnd = EndBase NegPosNatRecPF

-- The end's selection of terms is subject to a coherence condition,
-- which we specify in a series of definitions below, and separate
-- into first and second components (since the wedge condition specifies
-- an equality, which is equivalent to component-wise equality of the
-- two components of a term of `NegPosNatRecPF`).  The left side of the
-- equality in the coherence condition is an `lmap`, and the right side
-- is an `rmap`.

public export
0 npnWedgeLeft :
  NegPosNatEnd -> (a, b : Type) -> (a -> b) -> NegPosNatRecPF a b
npnWedgeLeft =
  wedgeLeft
    {p=NegPosNatRecPF}
    {isP=(MkProfunctor $ NegPosNatRecPFdimap0 _ _ _ _)}

public export
0 npnWedgeLeftFst :
  NegPosNatEnd -> (a, b : Type) -> (a -> b) -> NegPosNatEndFst a
npnWedgeLeftFst el a b mab = fst $ npnWedgeLeft el a b mab

public export
0 npnWedgeLeftSnd :
  (el : NegPosNatEnd) -> (a, b : Type) -> (mab : a -> b) ->
  NegPosNatEndSnd a (npnWedgeLeftFst el a b mab) b
npnWedgeLeftSnd el a b mab = snd $ npnWedgeLeft el a b mab

public export
0 npnWedgeRight :
  NegPosNatEnd -> (a, b : Type) -> (a -> b) -> NegPosNatRecPF a b
npnWedgeRight =
  wedgeRight
    {p=NegPosNatRecPF}
    {isP=(MkProfunctor $ NegPosNatRecPFdimap0 _ _ _ _)}

public export
0 npnWedgeRightFst :
  NegPosNatEnd -> (a, b : Type) -> (a -> b) -> NegPosNatEndFst a
npnWedgeRightFst el a b mab = fst $ npnWedgeRight el a b mab

public export
0 npnWedgeRightSnd :
  (el : NegPosNatEnd) -> (a, b : Type) -> (mab : a -> b) ->
  NegPosNatEndSnd a (npnWedgeRightFst el a b mab) b
npnWedgeRightSnd el a b mab = snd $ npnWedgeRight el a b mab

public export
0 NPNWedgeCondFst : NegPosNatEnd -> (a, b : Type) -> (a -> b) -> Type
NPNWedgeCondFst el a b mab =
  (npnWedgeLeftFst el a b mab = npnWedgeRightFst el a b mab)

public export
0 NPNWedgeCondSnd : (el : NegPosNatEnd) -> (a, b : Type) -> (mab : a -> b) ->
  NPNWedgeCondFst el a b mab -> Type
NPNWedgeCondSnd el a b mab cond1 =
  (i : NegPosNatEndDir a (npnWedgeRightFst el a b mab)) ->
  (npnWedgeRightSnd el a b mab i =
   npnWedgeLeftSnd el a b mab (rewrite cond1 in i))

public export
0 NPNEndCondFst : NegPosNatEnd -> Type
NPNEndCondFst el = (a, b : Type) -> (mab : a -> b) -> NPNWedgeCondFst el a b mab

public export
0 NPNEndCondSnd : (el : NegPosNatEnd) -> NPNEndCondFst el -> Type
NPNEndCondSnd el cond =
  (a, b : Type) -> (mab : a -> b) -> NPNWedgeCondSnd el a b mab (cond a b mab)

public export
0 NPNEndCond : NegPosNatEnd -> Type
NPNEndCond el = DPair (NPNEndCondFst el) (NPNEndCondSnd el)

-- The first component of a term of `NegPosNatRecPF` depends only on the
-- contravariant parameter (`x`), not the covariant parameter (`y`) --
-- it is a choice of a position of a free monad, which depends only on the
-- shape of the tree, not the type of variables.  Indeed, it is specifically
-- the type of terms when the type of variables is `Unit`.
--
-- Since `y` does not appear in the first component of the end, the `rmap`
-- does nothing -- it is the identity.
public export
0 npnWedgeRightFstId : FunExt ->
  (el : NegPosNatEnd) -> (a, b : Type) -> (mab : a -> b) ->
  npnWedgeRightFst el a b mab = fst (el a)
npnWedgeRightFstId fext el a b mab =
  pfCataInIdRefl fext _ _
    (funExt $ \i => funExt $ \d => case i of
      PFVar ev => cong (InPFM (PFVar ev)) $ funExt $ \ev' => void ev'
      PFCom ec => cong (InPFM (PFCom ec)) $ funExt $ \(j ** dm) => Refl)
    (fst $ el a)

-- Given a position of the free monad evaluated with `Unit` as the type
-- of negative occurrences, we can generate a position of the free monad
-- evaluated at _any_ type via an `lmap` of the unique morphism to the
-- terminal object.
--
-- In light of the description of `npnpContramap`, we can describe the
-- action of this mapping as follows:  a position of the free monad evaluated
-- at `Unit` turns every negative occurrence into a function of `d` copies
-- of `Unit` into `y`; but `d` copies of `Unit` is `Unit` for any `d`, so
-- every negative direction simply becomes a _term_ of `y`.  We can thus
-- generate a field of the free monad evaluated at any _other_ type by
-- using the constant function which returns that term on any input.  (The
-- possible inputs comprise `d` occurrences of `x'`.)
public export
npnePosFromUnitFst : NegPosNatEndFst Unit -> (a : Type) -> NegPosNatEndFst a
npnePosFromUnitFst i x = negPosNatEndFstLmap Unit x (const ()) i

public export
npnePosFromUnit : NegPosNatEnd -> (a : Type) -> NegPosNatEndFst a
npnePosFromUnit el a = npnePosFromUnitFst (fst $ el ()) a

-- Now that we have shown that a _potential_ first component of an end evaluated
-- at _any_ type can be computed from a first component of an end evaluated at
-- `Unit`, we here furthermore show that to satisfy the wedge condition, the
-- first components of the end must _all_ be _determined_ purely by the
-- evaluation of the end at `Unit`.  And since we have already shown that the
-- first component of the `lmap` which generates the evaluation at an arbitrary
-- type from the evaluation at `Unit` is determined purely by the first
-- component of the end (independent of the second component), we can conclude
-- more specifically that the first component of the end at an arbitrary type
-- is determined by the first component of the evaluation of the end at `Unit`.
public export
0 npnWedgeCondFstEq : FunExt ->
  (el : NegPosNatEnd) -> NPNEndCondFst el ->
  (a : Type) -> (fst (el a) = npnePosFromUnitFst (fst $ el ()) a)
npnWedgeCondFstEq fext el cond a =
  trans
    (sym $ npnWedgeRightFstId fext el a Unit (const ()))
    (sym $ cond a Unit (const ()))

public export
NegPosNatEndFormula :
  NegPosNatEnd = ((x : Type) -> InterpPolyFuncFreeM (NegPosMaybePP x) x)
NegPosNatEndFormula = Refl

public export
NegPosNatEndFormulaDP :
  NegPosNatEnd =
  ((x : Type) -> (i : NegPosNatEndFst x ** NegPosNatEndSnd x i x))
NegPosNatEndFormulaDP = Refl

-- Because the end condition requires that the first component of the end at
-- any type is determined by the first component of the evaluation of the end
-- at `Unit`, we can pull the first component of the end out of the dependency
-- on the type at which the end is evaluated.  We begin by refining the type
-- of the second component so that it depends only on the type of the first
-- component _at_ `Unit`, since we know that that instance of the first
-- component determines every instance of the first component.
--
-- As it turns out, we can represent that second component as a natural
-- transformation from a polynomial functor to the identity (which of course
-- is also polynomial).  Here we define that polynomial functor.

public export
NegPosNatEndDirUnitPF : NegPosNatEndFst Unit -> PolyFunc
NegPosNatEndDirUnitPF (InPFM (PFVar ()) dm) =
  -- A variable term (which, as a position of the free monad, represents
  -- a hole into which any tree might be substituted) always has exactly
  -- one direction.
  PFTerminalArena
NegPosNatEndDirUnitPF (InPFM (PFCom FZ) dm) =
  -- A left-type term is just an unlabeled leaf, so it contains no variables.
  PFInitialArena
NegPosNatEndDirUnitPF (InPFM (PFCom (FS FZ)) dm) =
  -- We combine the directions of both subtrees to obtain the directions
  -- of the whole tree.
  pfCoproductArena
    -- The left side is a collection of `x` subtrees.  Because
    -- `npnePosFromUnitFst` simply generates constant functions
    -- from `x` to subtrees (with the constant value provided by the
    -- subtree with `x == Unit` given by the position of the free monad),
    -- the total free-monad directions from the function from `x` to
    -- subtrees (i.e. an `x`-way collection of subtrees) comprises simply
    -- `x` copies of the recursive computation.
    (pfProductArena
      PFIdentityArena
      (NegPosNatEndDirUnitPF (dm (Left () ** \eu_ => ()))))
    -- The right side is a "collection" of `Unit` subtrees, i.e.
    -- a single subtree, on which we therefore simply perform the
    -- recursive computation.
    (NegPosNatEndDirUnitPF (dm (Right () ** \ev => void ev)))

public export
NegPosNatEndDirUnit : NegPosNatEndFst Unit -> Type -> Type
NegPosNatEndDirUnit i = InterpPolyFunc (NegPosNatEndDirUnitPF i)

-- For each choice of position, the type of directions is functorial
-- on the type of negative occurrences.
public export
npneduMap : (i : NegPosNatEndFst Unit) -> (a, b : Type) -> (a -> b) ->
  NegPosNatEndDirUnit i a -> NegPosNatEndDirUnit i b
npneduMap i a b = InterpPFMap (NegPosNatEndDirUnitPF i) {a} {b}

-- Since we have determined that we can pull the first component out of
-- the polymorphic part of the end, we can define another profunctor,
-- dependent on the first component and whose polymorphism is constrained
-- to the second component, whose pointwise ends (i.e. end for each choice of
-- first component) will give us the end of `NegPosNatRecPF`.

public export
NegPosNatDepEnd : NegPosNatEndFst Unit -> ProfunctorSig
NegPosNatDepEnd i x y = NegPosNatEndDirUnit i x -> y

public export
npndeDimap : (i : NegPosNatEndFst Unit) -> TypeDimapSig (NegPosNatDepEnd i)
npndeDimap i s t a b mas mtb = (.) mtb . (|>) (npneduMap i a s mas)

public export
NegPosNatEndDirNT : NegPosNatEndFst Unit -> Type
NegPosNatEndDirNT i =
  NaturalTransformation (NegPosNatEndDirUnit i) (id {a=Type})

public export
NegPosNatEndUnit : Type
NegPosNatEndUnit = DPair (NegPosNatEndFst Unit) NegPosNatEndDirNT

-------------------------------------------------------------------
-------------------------------------------------------------------
---- Path characterization of natural transformations to `id` ----
-------------------------------------------------------------------
-------------------------------------------------------------------

-- The direction type at FZ position for NegPosMaybePP Unit (isomorphic to Void)
public export
NPNPPdirFZ : Type
NPNPPdirFZ = NegPosMaybePPdir Unit FZ

-- The direction type at FS FZ position for NegPosMaybePP Unit
public export
NPNPPdirFSFZ : Type
NPNPPdirFSFZ = NegPosMaybePPdir Unit (FS FZ)

-- The two canonical elements of the direction type at FS FZ
public export
NpnppDirLeft : NPNPPdirFSFZ
NpnppDirLeft = (Left () ** \_ => ())

public export
NpnppDirRight : NPNPPdirFSFZ
NpnppDirRight = (Right () ** voidF Unit)

-- Type aliases for the recursive polynomial functors at FS FZ nodes
public export
NpnppRecLeftPF : (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) -> PolyFunc
NpnppRecLeftPF dm = NegPosNatEndDirUnitPF (dm NpnppDirLeft)

public export
NpnppRecRightPF : (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) -> PolyFunc
NpnppRecRightPF dm = NegPosNatEndDirUnitPF (dm NpnppDirRight)

-- The full polynomial for the FS FZ case
public export
NpnppNodePF : (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) -> PolyFunc
NpnppNodePF dm = pfCoproductArena
  (pfProductArena PFIdentityArena (NpnppRecLeftPF dm))
  (NpnppRecRightPF dm)

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Combinator library for polynomial functor interpretation ----
----------------------------------------------------------------------
----------------------------------------------------------------------

-- Instead of pattern matching on complex dependent types, we build
-- eliminators that encapsulate the case analysis and provide properly-typed
-- components to handlers. This is the "point-free" or combinator style.

-- Eliminator for InterpPolyFunc of a coproduct arena.
-- Given handlers for the left and right cases, dispatches appropriately.
public export
elimInterpPfCoproduct :
  (p, q : PolyFunc) -> (x : Type) -> (r : Type) ->
  (leftCase : (i : pfPos p) -> (pfDir {p} i -> x) -> r) ->
  (rightCase : (j : pfPos q) -> (pfDir {p=q} j -> x) -> r) ->
  InterpPolyFunc (pfCoproductArena p q) x -> r
elimInterpPfCoproduct (ppos ** pdir) (qpos ** qdir) x r leftCase rightCase
  (Left i ** dirFn) = leftCase i dirFn
elimInterpPfCoproduct (ppos ** pdir) (qpos ** qdir) x r leftCase rightCase
  (Right j ** dirFn) = rightCase j dirFn

-- Eliminator for InterpPolyFunc of a product arena.
-- The direction type is Either (pdir i) (qdir j), so we need handlers for
-- when the caller provides a left direction vs a right direction.
public export
elimInterpPfProduct :
  (p, q : PolyFunc) -> (x : Type) -> (r : Type) ->
  (handler :
    (i : pfPos p) -> (j : pfPos q) ->
    (Either (pfDir {p} i) (pfDir {p=q} j) -> x) -> r) ->
  InterpPolyFunc (pfProductArena p q) x -> r
elimInterpPfProduct (ppos ** pdir) (qpos ** qdir) x r handler
  ((i, j) ** dirFn) = handler i j dirFn

-- Specialized eliminator for InterpPolyFunc of (pfProductArena PFIdentityArena q).
-- The left position is Unit, so we ignore it. The left direction is also Unit,
-- so `dirFn (Left ())` gives us an x directly.
public export
elimInterpPfProductId :
  (q : PolyFunc) -> (x : Type) -> (r : Type) ->
  (handler :
    (j : pfPos q) ->
    (getX : x) ->                        -- dirFn (Left ())
    (recurse : pfDir {p=q} j -> x) ->    -- \d => dirFn (Right d)
    r) ->
  InterpPolyFunc (pfProductArena PFIdentityArena q) x -> r
elimInterpPfProductId (qpos ** qdir) x r handler (((), j) ** dirFn) =
  handler j (dirFn (Left ())) (\d => dirFn (Right d))

-- Eliminator for the node polynomial functor interpretation.
-- Combines the coproduct and product eliminators for our specific case.
public export
elimNpnppNodeInterp :
  (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) ->
  (x : Type) -> (r : Type) ->
  -- Handler for Left case: we get the recursive position, a direct x,
  -- and a way to recurse into the left subtree
  (leftCase :
    (recLeftPos : pfPos (NpnppRecLeftPF dm)) ->
    (getX : x) ->
    (recurseLeft : pfDir {p=NpnppRecLeftPF dm} recLeftPos -> x) ->
    r) ->
  -- Handler for Right case: we get the recursive position and direction fn
  (rightCase :
    (recRightPos : pfPos (NpnppRecRightPF dm)) ->
    (recurseRight : pfDir {p=NpnppRecRightPF dm} recRightPos -> x) ->
    r) ->
  InterpPolyFunc (NpnppNodePF dm) x -> r
elimNpnppNodeInterp dm x r leftCase rightCase =
  elimInterpPfCoproduct
    (pfProductArena PFIdentityArena (NpnppRecLeftPF dm))
    (NpnppRecRightPF dm)
    x r
    (\leftPos, dirFn =>
      elimInterpPfProductId (NpnppRecLeftPF dm) x r
        (\recLeftPos, getX, recurseLeft => leftCase recLeftPos getX recurseLeft)
        (leftPos ** dirFn))
    rightCase

-- Introduction forms (constructors) for polynomial functor interpretations.
-- These are the duals of the eliminators.

-- Introduce a Left element in a coproduct arena interpretation.
public export
introInterpPfCoproductLeft :
  (p, q : PolyFunc) -> (x : Type) ->
  (i : pfPos p) -> (pfDir {p} i -> x) ->
  InterpPolyFunc (pfCoproductArena p q) x
introInterpPfCoproductLeft (ppos ** pdir) (qpos ** qdir) x i dirFn =
  (Left i ** dirFn)

-- Introduce a Right element in a coproduct arena interpretation.
public export
introInterpPfCoproductRight :
  (p, q : PolyFunc) -> (x : Type) ->
  (j : pfPos q) -> (pfDir {p=q} j -> x) ->
  InterpPolyFunc (pfCoproductArena p q) x
introInterpPfCoproductRight (ppos ** pdir) (qpos ** qdir) x j dirFn =
  (Right j ** dirFn)

-- Introduce an element in (pfProductArena PFIdentityArena q).
-- Given a position in q, a direct x value, and a function for recursive dirs.
public export
introInterpPfProductId :
  (q : PolyFunc) -> (x : Type) ->
  (j : pfPos q) ->
  (getX : x) ->
  (recurse : pfDir {p=q} j -> x) ->
  InterpPolyFunc (pfProductArena PFIdentityArena q) x
introInterpPfProductId (qpos ** qdir) x j getX recurse =
  (((), j) ** \d => case d of Left () => getX; Right rd => recurse rd)

-- Introduction forms for the node polynomial functor.
public export
introNpnppNodeLeft :
  (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) ->
  (x : Type) ->
  (recLeftPos : pfPos (NpnppRecLeftPF dm)) ->
  (getX : x) ->
  (recurseLeft : pfDir {p=NpnppRecLeftPF dm} recLeftPos -> x) ->
  InterpPolyFunc (NpnppNodePF dm) x
introNpnppNodeLeft dm x recLeftPos getX recurseLeft =
  introInterpPfCoproductLeft
    (pfProductArena PFIdentityArena (NpnppRecLeftPF dm))
    (NpnppRecRightPF dm)
    x
    ((), recLeftPos)
    (\d => case d of Left () => getX; Right rd => recurseLeft rd)

public export
introNpnppNodeRight :
  (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) ->
  (x : Type) ->
  (recRightPos : pfPos (NpnppRecRightPF dm)) ->
  (recurseRight : pfDir {p=NpnppRecRightPF dm} recRightPos -> x) ->
  InterpPolyFunc (NpnppNodePF dm) x
introNpnppNodeRight dm x recRightPos recurseRight =
  introInterpPfCoproductRight
    (pfProductArena PFIdentityArena (NpnppRecLeftPF dm))
    (NpnppRecRightPF dm)
    x
    recRightPos
    recurseRight

-- A predicate asserting that a position has no PFVar nodes anywhere.
-- A closed term is one where all leaves are PFCom FZ (closed leaves), not
-- PFVar (open variable leaves).
--
-- Structure:
-- - PFVar: No constructor - open terms are not closed
-- - PFCom FZ: Closed (leaf with no variables)
-- - PFCom (FS FZ): Closed if both children are closed
public export
data NpnpIsClosed : NegPosNatEndFst Unit -> Type where
  IsClosedLeaf :
    (dm : NPNPPdirFZ -> NegPosNatEndFst Unit) ->
    NpnpIsClosed (InPFM (PFCom FZ) dm)
  IsClosedNode :
    (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) ->
    (leftClosed : NpnpIsClosed (dm NpnppDirLeft)) ->
    (rightClosed : NpnpIsClosed (dm NpnppDirRight)) ->
    NpnpIsClosed (InPFM (PFCom (FS FZ)) dm)

-- A path through a term tree to a variable occurrence.  This is an
-- inductive characterization of natural transformations from
-- `NegPosNatEndDirUnit i` to the identity functor.
--
-- The structure mirrors `NegPosNatEndDirUnitPF`:
-- - At a variable leaf (PFVar): there is exactly one path (PathVar)
-- - At an FZ node: there is exactly one path (PathLeaf) - the trivial one
-- - At an FS FZ node: we need a choice for the left branch and a path for
--   the right branch
--
-- Note: Natural transformations from a coproduct to `id` require handling
-- BOTH branches, so at each node we need:
-- 1. For the left branch: either stop and extract `x`, or recurse
-- 2. For the right branch: always recurse
public export
data NegPosNatEndDirPath : NegPosNatEndFst Unit -> Type where
  -- At a variable leaf, there is exactly one path: extract the variable.
  PathVar :
    (dm : Void -> NegPosNatEndFst Unit) ->
    NegPosNatEndDirPath (InPFM (PFVar ()) dm)
  -- At an FZ node (zero/leaf), there is exactly one path: the trivial one.
  -- (A nat trans from `const Void` to `id` is the absurd function.)
  PathLeaf :
    (dm : NPNPPdirFZ -> NegPosNatEndFst Unit) ->
    NegPosNatEndDirPath (InPFM (PFCom FZ) dm)
  -- At an FS FZ node, we need both a choice for left and a path for right.
  PathNode :
    (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) ->
    (leftChoice : Either () (NegPosNatEndDirPath (dm NpnppDirLeft))) ->
    (rightPath : NegPosNatEndDirPath (dm NpnppDirRight)) ->
    NegPosNatEndDirPath (InPFM (PFCom (FS FZ)) dm)

-- Convert a path to the corresponding natural transformation.
-- This is the forward direction of the isomorphism.
--
-- For each case, we need to understand the structure of
-- `NegPosNatEndDirUnit i x`:
-- - PFVar: No constructor in NpnpIsClosed, so this case is impossible
-- - PFCom FZ: `InterpPolyFunc PFInitialArena x = Void`
-- - PFCom (FS FZ): `InterpPolyFunc (pfCoproductArena ... recR) x`
--                = (i : Either ((), posL) posR ** dirFn i -> x)
--   where for Left ((), posL): dirFn = Either Unit (dirL posL) -> x
--         for Right posR: dirFn = dirR posR -> x
--
-- We use the combinator-style eliminators to handle the complex dependent
-- types without pattern matching.
--
-- Note: We require an NpnpIsClosed proof to ensure the term is closed.
-- The PFVar case (open variable) is impossible for closed terms.
public export
closedPathToNatTrans : (i : NegPosNatEndFst Unit) ->
  NpnpIsClosed i -> NegPosNatEndDirPath i -> NegPosNatEndDirNT i
-- PFVar case is impossible - no NpnpIsClosed constructor for it
closedPathToNatTrans (InPFM (PFVar ()) dm) closed (PathVar _) x _ impossible
-- For leaf (FZ): the direction type is Void, so we use absurd.
closedPathToNatTrans (InPFM (PFCom FZ) dm) (IsClosedLeaf _) (PathLeaf _) x
    (ev ** _) =
  void ev
-- For node (FS FZ): use the combinator-style eliminator.
closedPathToNatTrans (InPFM (PFCom (FS FZ)) dm)
    (IsClosedNode _ leftCl rightCl) (PathNode _ lc rp) x dir =
  elimNpnppNodeInterp dm x x
    (\recLeftPos, getX, recurseLeft =>
      case lc of
        Left () => getX
        Right leftPath =>
          closedPathToNatTrans (dm NpnppDirLeft) leftCl leftPath x
            (recLeftPos ** recurseLeft))
    (\recRightPos, recurseRight =>
      closedPathToNatTrans (dm NpnppDirRight) rightCl rp x
        (recRightPos ** recurseRight))
    dir

-- The position type for the FS FZ case polynomial functor.
-- This is an explicit type alias to help with unification.
public export
NpnppNodePos : (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) -> Type
NpnppNodePos dm = pfPos (NpnppNodePF dm)

-- The left and right component polynomials of NpnppNodePF
public export
NpnppNodeLeftPF : (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) -> PolyFunc
NpnppNodeLeftPF dm = pfProductArena PFIdentityArena (NpnppRecLeftPF dm)

-- Convert a right position to the node position type.
-- Uses the polyInjR API which pattern-matches on both polynomials,
-- forcing the type reduction that makes Left/Right work.
public export
npnppPosFromRight :
  (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) ->
  pfPos (NpnppRecRightPF dm) ->
  pfPos (NegPosNatEndDirUnitPF (InPFM (PFCom (FS FZ)) dm))
npnppPosFromRight dm posR =
  polyInjROnPos (NpnppNodeLeftPF dm) (NpnppRecRightPF dm) posR

-- Convert a left position to the node position type.
-- The left component is (Unit, pfPos (NpnppRecLeftPF dm)).
public export
npnppPosFromLeft :
  (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) ->
  pfPos (NpnppRecLeftPF dm) ->
  pfPos (NegPosNatEndDirUnitPF (InPFM (PFCom (FS FZ)) dm))
npnppPosFromLeft dm posL =
  polyInjLOnPos (NpnppNodeLeftPF dm) (NpnppRecRightPF dm) ((), posL)

-- Try to extract an arbitrary position from a polynomial functor.
-- Returns Nothing if the position type is Void.
public export
anyPositionNPNE : (i : NegPosNatEndFst Unit) ->
  Maybe (pfPos (NegPosNatEndDirUnitPF i))
anyPositionNPNE (InPFM (PFVar ()) dm) = Just ()
anyPositionNPNE (InPFM (PFCom FZ) dm) = Nothing
anyPositionNPNE (InPFM (PFCom (FS FZ)) dm) =
  case anyPositionNPNE (dm NpnppDirRight) of
    Just posR => Just (npnppPosFromRight dm posR)
    Nothing => case anyPositionNPNE (dm NpnppDirLeft) of
      Just posL => Just (npnppPosFromLeft dm posL)
      Nothing => Nothing

-- Helper: extract a nat trans for the right subtree from a node nat trans.
-- This is straightforward because the right case doesn't need a "dummy" value.
public export
extractRightNatTrans :
  (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) ->
  NegPosNatEndDirNT (InPFM (PFCom (FS FZ)) dm) ->
  NegPosNatEndDirNT (dm NpnppDirRight)
extractRightNatTrans dm eta x rightDir =
  eta x (introNpnppNodeRight dm x (DPair.fst rightDir) (DPair.snd rightDir))

-- Probe whether a nat trans uses the direct value or recurses.
-- Returns True if it uses direct value, False if it recurses.
-- Requires a position to construct a test element.
public export
probeUsesDirectValue :
  (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) ->
  (pos : pfPos (NpnppRecLeftPF dm)) ->
  NegPosNatEndDirNT (InPFM (PFCom (FS FZ)) dm) ->
  Bool
probeUsesDirectValue dm pos eta =
  -- Apply eta at type Bool with getX=True and recurseLeft=const False
  -- If eta uses direct value, returns True; if it recurses, returns False
  eta Bool (introNpnppNodeLeft dm Bool pos True (const False))

-- A "prober" knows how to probe whether a nat trans uses direct value.
-- This abstracts the probing mechanism so we can pass it through recursion.
public export
Prober : NegPosNatEndFst Unit -> Type
Prober i = (pos : pfPos (NegPosNatEndDirUnitPF i)) -> Bool

mutual
  -- Compute path using a prober instead of a nat trans directly.
  -- This allows us to work with the recursive structure without needing
  -- to extract nat trans values.
  public export
  natTransToPathViaProber :
    (i : NegPosNatEndFst Unit) ->
    Prober i ->
    NegPosNatEndDirPath i
  natTransToPathViaProber (InPFM (PFVar ()) dm) _ = PathVar dm
  natTransToPathViaProber (InPFM (PFCom FZ) dm) _ = PathLeaf dm
  natTransToPathViaProber (InPFM (PFCom (FS FZ)) dm) prober =
    PathNode dm
      (determineLeftChoiceViaProber dm prober)
      (natTransToPathViaProber (dm NpnppDirRight) (rightProber dm prober))

  -- Determine left choice using a prober.
  public export
  determineLeftChoiceViaProber :
    (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) ->
    Prober (InPFM (PFCom (FS FZ)) dm) ->
    Either () (NegPosNatEndDirPath (dm NpnppDirLeft))
  determineLeftChoiceViaProber dm prober =
    case anyPositionNPNE (dm NpnppDirLeft) of
      Nothing => Left ()
      Just pos =>
        -- Probe using a left position
        if prober (npnppPosFromLeft dm pos)
          then Left ()
          else Right (natTransToPathViaProber (dm NpnppDirLeft)
                       (leftProber dm prober))

  -- Create a prober for the left subtree from a node prober.
  -- The left prober embeds positions in the left subtree into the outer
  -- node structure and probes there.
  public export
  leftProber :
    (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) ->
    Prober (InPFM (PFCom (FS FZ)) dm) ->
    Prober (dm NpnppDirLeft)
  leftProber dm prober pos = prober (npnppPosFromLeft dm pos)

  -- Create a prober for the right subtree from a node prober.
  public export
  rightProber :
    (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) ->
    Prober (InPFM (PFCom (FS FZ)) dm) ->
    Prober (dm NpnppDirRight)
  rightProber dm prober pos = prober (npnppPosFromRight dm pos)

-- Eliminator for positions in the node polynomial functor.
-- This dispatches on whether the position is Left or Right.
public export
elimNpnppNodePos :
  (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) ->
  (r : Type) ->
  (leftCase : pfPos (NpnppRecLeftPF dm) -> r) ->
  (rightCase : pfPos (NpnppRecRightPF dm) -> r) ->
  pfPos (NpnppNodePF dm) -> r
elimNpnppNodePos dm r leftCase rightCase =
  elimInterpPfCoproduct
    (pfProductArena PFIdentityArena (NpnppRecLeftPF dm))
    (NpnppRecRightPF dm)
    Unit r
    (\prodPos, _ => leftCase (snd prodPos))
    (\rightPos, _ => rightCase rightPos)
    . (\pos => (pos ** const ()))

-- Convert a nat trans to a prober.
-- The prober checks whether applying the nat trans at Bool returns True
-- (direct value) or False (recurse).
--
-- For a given position `pos`, we construct a test element where:
-- - At the position we're probing, getX = True and recurse = const False
-- - This way, if eta returns True, it used the direct value
-- - If eta returns False, it recursed
public export
natTransToProber :
  (i : NegPosNatEndFst Unit) ->
  NegPosNatEndDirNT i ->
  Prober i
natTransToProber (InPFM (PFVar ()) dm) eta pos = True  -- No recursion possible
natTransToProber (InPFM (PFCom FZ) dm) eta pos = void pos
natTransToProber (InPFM (PFCom (FS FZ)) dm) eta pos =
  -- Dispatch on whether pos is a left or right position
  elimNpnppNodePos dm Bool
    -- Left case: construct test with getX=True, recurse=const False
    (\recLeftPos =>
      eta Bool (introNpnppNodeLeft dm Bool recLeftPos True (const False)))
    -- Right case: right always recurses (no direct value), return False
    (\recRightPos =>
      eta Bool (introNpnppNodeRight dm Bool recRightPos (const False)))
    pos

-- Determine the left choice for natTransToPath.
-- Returns Left () if the nat trans uses direct value, Right path otherwise.
-- NOTE: This function is now superseded by determineLeftChoiceViaProber
-- but kept for reference/backwards compatibility.
public export
determineLeftChoice :
  (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) ->
  NegPosNatEndDirNT (InPFM (PFCom (FS FZ)) dm) ->
  Either () (NegPosNatEndDirPath (dm NpnppDirLeft))
determineLeftChoice dm eta =
  let prober = natTransToProber (InPFM (PFCom (FS FZ)) dm) eta
  in case anyPositionNPNE (dm NpnppDirLeft) of
       -- No position in left recursive polynomial => must use direct value
       Nothing => Left ()
       -- Have a position => probe to determine
       Just pos =>
         if prober (npnppPosFromLeft dm pos)
           then Left ()
           else Right (natTransToPathViaProber (dm NpnppDirLeft)
                        (leftProber dm prober))

-- Convert a natural transformation to the corresponding path.
-- This is the inverse direction of closedPathToNatTrans.
--
-- The key insight is that we convert the nat trans to a prober, then
-- use the prober-based path computation. This avoids needing to extract
-- sub-nat-trans values which would require dummy values.
public export
natTransToPath : (i : NegPosNatEndFst Unit) ->
  NegPosNatEndDirNT i -> NegPosNatEndDirPath i
natTransToPath i eta = natTransToPathViaProber i (natTransToProber i eta)

public export
NPNEAlgProf : Type -> ProfunctorSig
NPNEAlgProf a b c = InterpNegPosMaybePP a b -> c

public export
NPNEAlgProfDimap : (a : Type) -> TypeDimapSig (NPNEAlgProf a)
NPNEAlgProfDimap a s t b c mbs mtc ipf = mtc . ipf . dpMapSnd (\j => (.) mbs)

public export
NPNEAlg : Type -> Type -> Type
NPNEAlg a b = NPNEAlgProf a b b

public export
NPNEAlgAlt : Type -> Type -> Type
NPNEAlgAlt a b = (Unit -> b, (a -> b, b) -> b)

public export
NPNEAlgToAlt : (a, b : Type) -> NPNEAlg a b -> NPNEAlgAlt a b
NPNEAlgToAlt a b alg =
  (\() => alg (FZ ** \(ev ** _) => void ev),
   \el => alg (FS FZ ** \(i ** ea) => case i of
    Left () => fst el $ ea ()
    Right () => snd el))

public export
NPNEAlgFromAlt : (a, b : Type) -> NPNEAlgAlt a b -> NPNEAlg a b
NPNEAlgFromAlt a b (alg1, alg2) (FZ ** _) =
  alg1 ()
NPNEAlgFromAlt a b (alg1, alg2) (FS FZ ** alt) =
  alg2 (\ea => alt (Left () ** \() => ea), alt (Right () ** voidF a))

public export
npneEval : {a, b, c : Type} ->
  (b -> c) -> NPNEAlg a c -> NegPosNatRecPF a b -> c
npneEval {a} {b} {c} subst alg =
  pfSubstCata {p=(NegPosMaybePP a)} {a=b} {b=c} subst (DPair.curry alg)

public export
npneCata : {a, b : Type} -> NPNEAlg a b -> NegPosNatRecPF a b -> b
npneCata {a} {b} = npneEval {a} {b} {c=b} Prelude.id

public export
npneEndCata : {a : Type} -> NPNEAlg a a -> NegPosNatEnd -> a
npneEndCata {a} alg el = npneCata {a} {b=a} alg (el a)

-- See
-- https://www.schoolofhaskell.com/user/edwardk/phoas#boxes-go-bananas-for-less.

public export
NegPosNatImpredPF : ProfunctorSig
NegPosNatImpredPF a b = (r : Type) -> (b -> r) -> NPNEAlg a r -> r

public export
NegPosNatImpredPFdimap : TypeDimapSig NegPosNatImpredPF
NegPosNatImpredPFdimap s t a b mas mtb ipf r mbr alga =
  ipf r (mbr . mtb) (alga . dpMapSnd (\i => (|>) (dpMapSnd (\j => (.) mas))))

----------------------------
---- Polynomial version ----
----------------------------

public export
NPNPbasePos : Type
NPNPbasePos = Fin 2

public export
NPNPbaseDir : NPNPbasePos -> Type
NPNPbaseDir FZ = Unit
NPNPbaseDir (FS FZ) = Nat

public export
NPNPbasePF : PolyFunc
NPNPbasePF = (NPNPbasePos ** NPNPbaseDir)

public export
NPNPbaseMu : Type
NPNPbaseMu = PolyFuncMu NPNPbasePF

public export
NPNPpfExtPos : NPNPbasePos -> Type
NPNPpfExtPos FZ = Unit
NPNPpfExtPos (FS FZ) = (NPNPbaseMu -> NPNPbaseMu, NPNPbaseMu)

public export
NPNPpfPos : Type
NPNPpfPos = DPair NPNPbasePos NPNPpfExtPos

public export
NPNPpfDir : NPNPpfPos -> Type
NPNPpfDir = NPNPbaseDir . DPair.fst

public export
NPNPpf : PolyFunc
NPNPpf = (NPNPpfPos ** NPNPpfDir)

public export
NPNPmu : Type
NPNPmu = PolyFuncMu NPNPpf

public export
NPNpfAlg : Type -> Type
NPNpfAlg a = Either Unit (NPNPmu -> NPNPmu, NPNPmu, Nat -> a) -> a

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
polyDifuncTest : IO ()
polyDifuncTest = do
  putStrLn ""
  putStrLn "======================"
  putStrLn "Begin PolyDifuncTest:"
  putStrLn "----------------------"
  putStrLn ""
  putStrLn "--------------------"
  putStrLn "End PolyDifuncTest."
  putStrLn "===================="
  pure ()

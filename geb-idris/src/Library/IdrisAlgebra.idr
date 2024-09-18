module Library.IdrisAlgebra

import Library.IdrisUtils
import Library.IdrisCategories

%default total

----------------------------------
----------------------------------
---- Categories of F-algebras ----
----------------------------------
----------------------------------

public export
FunctorIdP :
  (f : Type -> Type) -> (fm : {0 a, b : Type} -> (a -> b) -> f a -> f b) -> Type
FunctorIdP f fm = (a : Type) -> ExtEq (fm $ id {a}) (id {a=(f a)})

public export
FunctorCompP :
  (f : Type -> Type) -> (fm : {0 a, b : Type} -> (a -> b) -> f a -> f b) -> Type
FunctorCompP f fm = {a, b, c : Type} ->
  (h : b -> c) -> (g : a -> b) -> ExtEq (fm (h . g)) (fm h . fm g)

public export
FunctorP :
  (f : Type -> Type) -> (fm : {0 a, b : Type} -> (a -> b) -> f a -> f b) -> Type
FunctorP f fm = (FunctorIdP f fm, FunctorCompP f fm)

public export
fAlgId :
  {f : Type -> Type} -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  FunctorIdP f fm ->
  (alg : FAlgObj f) -> FAlgMorph {f} {fm} alg alg
fAlgId {f} {fm} idp (a ** m) = Element0 id $ \el => cong m $ sym $ idp a el

public export
fAlgComp :
  {f : Type -> Type} -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  FunctorCompP f fm -> {a, b, c : FAlgObj f} ->
  FAlgMorph {f} {fm} b c -> FAlgMorph {f} {fm} a b -> FAlgMorph {f} {fm} a c
fAlgComp {f} {fm} compp {a=(a ** ma)} {b=(b ** mb)} {c=(c ** mc)}
  (Element0 h heq) (Element0 g geq) =
    Element0 (h . g) $
      \el =>
        trans
          (trans
            (cong h $ geq el)
            (heq $ fm g el))
          (cong mc $ sym $ compp h g el)

----------------------------------------
----------------------------------------
---- F-algebra universal properties ----
----------------------------------------
----------------------------------------

------------------------------
---- Initiality in `Type` ----
------------------------------

public export
FAlgEq : {f : Type -> Type} -> {a : Type} -> Algebra f a -> Algebra f a -> Type
FAlgEq {f} a b = ExtEq a b

public export
FAlgIso :
  {f : Type -> Type} -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  FAlgObj f -> FAlgObj f -> Type
FAlgIso {f} {fm} a b =
  Subset0 (FAlgMorph {fm} a b, FAlgMorph {fm} b a) $
    \(m, m') => ExtInverse (fst0 m) (fst0 m')

public export
IsCandidateInitialFAlg :
  {f : Type -> Type} -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  FAlgObj f -> Type
IsCandidateInitialFAlg {f} {fm} a = (b : FAlgObj f) -> FAlgMorph {fm} a b

public export
IsUniqueInitialFAlg :
  {f : Type -> Type} -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  FAlgObj f -> Type
IsUniqueInitialFAlg {f} {fm} a =
  (b : FAlgObj f) -> IsCandidateInitialFAlg {f} {fm} b -> FAlgIso {fm} a b

public export
IsInitialFAlg :
  {f : Type -> Type} -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  FAlgObj f -> Type
IsInitialFAlg {f} {fm} a =
  (IsCandidateInitialFAlg {f} {fm} a, IsUniqueInitialFAlg {f} {fm} a)

public export
InitialFAlg :
  (f : Type -> Type) -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  Type
InitialFAlg f {fm} = Subset0 (FAlgObj f) (IsInitialFAlg {f} {fm})

-------------------------------
-------------------------------
---- `Fin` with equalizers ----
-------------------------------
-------------------------------

-------------------------------
---- Algebras of `BinNatF` ----
-------------------------------

-- The effect of an equalizer on morphisms between objects of `FinSet`
-- may be viewed as erasing some terms from the domain, so we can represent
-- objects of `FinSet` as lists of booleans, where the length is the
-- cardinality of the underlying set without any equalizers, and the booleans
-- indicate which terms have been erased.

-- Rather than the concrete type `List Bool`, we use algebras of `BinNatF`,
-- thereby requiring only that the type implement the interface of `List Bool`,
-- not that it be `List Bool` precisely.
public export
BinNatAlgObj : Type
BinNatAlgObj = FAlgObj BinNatF

public export
freeBinNatMap : {a, b : Type} -> (a -> b) -> FreeBinNat a -> FreeBinNat b
freeBinNatMap = freeMap evalBinNatF

public export
freeBinNatJoin : {a : Type} -> FreeBinNat (FreeBinNat a) -> FreeBinNat a
freeBinNatJoin = freeFJoin evalBinNatF

public export
bnAlgFromFreeObj : (alg : FAlgObj FreeBinNat) -> Algebra BinNatF (fst alg)
bnAlgFromFreeObj = FAlgFromFreeObj {f=BinNatF} {fm=(map @{BifunctorToFunctor})}

public export
bnAlgObjFromFree : FAlgObj FreeBinNat -> FAlgObj BinNatF
bnAlgObjFromFree = FAlgObjFromFree {f=BinNatF} {fm=(map @{BifunctorToFunctor})}

public export
bnAlgObjToFree : (alg : FAlgObj BinNatF) -> FreeMAlgSig BinNatF (fst alg)
bnAlgObjToFree = FAlgObjToFree {f=BinNatF} evalBinNatF

public export
bnAlgObjToFreeObj : FAlgObj BinNatF -> FAlgObj FreeBinNat
bnAlgObjToFreeObj = FAlgObjToFreeObj {f=BinNatF} evalBinNatF

public export
bnAlgObjToFreeIso : (a : FAlgObj BinNatF) ->
  FAlgIso {f=BinNatF} {fm=(Prelude.map @{BifunctorToFunctor})}
    (bnAlgObjFromFree (bnAlgObjToFreeObj a)) a
bnAlgObjToFreeIso (a ** m) =
  Element0
    (Element0 id $ \el => case el of NilF => Refl ; ConsF b x => Refl,
     Element0 id $ \el => case el of NilF => Refl ; ConsF b x => Refl)
    (\el => Refl, \el => Refl)

-- The unit property of an algebra over a monad.
public export
bnAlgObjToFreeUnit : (a : FAlgObj BinNatF) ->
  FreeMonadAlgUnitP IdrisCategories.evalBinNatF (bnAlgObjToFreeObj a)
bnAlgObjToFreeUnit (a ** m) el = Refl

-- The action property of an algebra over a monad.
-- Together with the unit property above, this shows that `bnAlgObjToFree a`
-- _is_ an algebra over a monad (not only over the underlying endofunctor).
public export
bnAlgObjToFreeAct : (a : FAlgObj BinNatF) ->
  FreeMonadAlgActP IdrisCategories.evalBinNatF (bnAlgObjToFreeObj a)
bnAlgObjToFreeAct (a ** m) (InFree (TFV var)) = Refl
bnAlgObjToFreeAct (a ** m) (InFree (TFC x)) = case x of
  NilF => Refl
  ConsF b x' => rewrite bnAlgObjToFreeAct (a ** m) x' in Refl

public export
bnFreeAlgCommutesLemma :
  (a : Type) -> (m : FreeMAlgSig BinNatF a) ->
  FreeMonadAlgActP IdrisCategories.evalBinNatF (a ** m) ->
  (b : Bool) -> (x : FreeBinNat a) ->
  m (InFree (TFC (ConsF b (InFree (TFV (m x)))))) = m (InFree (TFC (ConsF b x)))
bnFreeAlgCommutesLemma a m eqact b x =
  eqact $ inFC $ ConsF b $ inFV x

public export
bnFreeAlgCommutes :
  (a : Type) -> (m : FreeMAlgSig BinNatF a) ->
  FreeMonadAlgP IdrisCategories.evalBinNatF (a ** m) ->
  (el : FreeBinNat a) ->
  cataBinNatF
    (m . InFree . TFC . mapSnd Library.IdrisCategories.inFV) el =
  m (evalBinNatF a (FreeBinNat a) IdrisCategories.inFV IdrisCategories.inFC el)
bnFreeAlgCommutes a m (equ, eqact) (InFree (TFV var)) = sym $ equ var
bnFreeAlgCommutes a m (equ, eqact) (InFree (TFC x)) =
  case x of
    NilF => Refl
    ConsF b x' =>
      rewrite bnFreeAlgCommutes a m (equ, eqact) x' in
      bnFreeAlgCommutesLemma a m eqact b _

public export
bnFreeAlgCommutes' :
  (a : Type) -> (m : FreeMAlgSig BinNatF a) ->
  FreeMonadAlgP IdrisCategories.evalBinNatF (a ** m) ->
  (el : FreeBinNat a) ->
  m el =
  cataBinNatF
    (m . InFree . TFC . mapSnd Library.IdrisCategories.inFV)
    (evalBinNatF a (FreeBinNat a) IdrisCategories.inFV IdrisCategories.inFC el)
bnFreeAlgCommutes' a m (equ, eqact) (InFree (TFV var)) = equ var
bnFreeAlgCommutes' a m (equ, eqact) (InFree (TFC x)) =
  case x of
    NilF => Refl
    ConsF b x' =>
      rewrite sym (bnFreeAlgCommutes' a m (equ, eqact) x') in
      sym $ bnFreeAlgCommutesLemma a m eqact b x'

-- This (together with `bnAlgObjToFreeIso` above) completes the demonstration
-- that the category of algebras over the monad `FreeBinNat` (the
-- "Eilenberg-Moore category') is equivalent to the category of algebras over
-- the underlying endofunctor `BinNatF`, with the equivalence being witnessed
-- by `bnAlgObjToFreeObj` and `bnAlgObjFromFree`.
-- (See proposition 3.1 from
-- https://ncatlab.org/nlab/show/algebra+for+an+endofunctor#relation_to_algebras_over_a_monad .)
public export
bnAlgObjFromFreeIso : (a : FAlgObj FreeBinNat) ->
  FreeMonadAlgP IdrisCategories.evalBinNatF a ->
  FAlgIso {f=FreeBinNat} {fm=IdrisAlgebra.freeBinNatMap}
    (bnAlgObjToFreeObj (bnAlgObjFromFree a)) a
bnAlgObjFromFreeIso (a ** m) algp =
  Element0
    (Element0 id $ bnFreeAlgCommutes a m algp,
     Element0 id $ bnFreeAlgCommutes' a m algp)
    (\el => Refl, \el => Refl)

-- From _Toposes, Triples, and Theories_ (section 3.6) by Michael Barr and
-- Charles Wells, morphisms in the category of monads (a monad is known in
-- that book as a "triple") correspond bijectively with (contravariant) functors
-- between Eilenberg-Moore categories which commute with the functors underlying
-- the monads.
--
-- This is the definition of a morphism in the category of free monads.
public export
FreeMonadCatMorph : {f, g : Type -> Type} ->
  (feval : FreeFEval f) -> (geval : FreeFEval g) -> Type
FreeMonadCatMorph {f} {g} feval geval =
  Subset0 (NaturalTransformation (FreeMonad f) (FreeMonad g)) $
    \alpha =>
      (ExtEqNT
        (vcompNT
          {f=(Prelude.id)} {g=(FreeMonad f)} {h=(FreeMonad g)}
          alpha (freeMunit f))
        (freeMunit g),
       ExtEqNT
        (vcompNT
          {f=(FreeMonad f . FreeMonad f)} {g=(FreeMonad f)} {h=(FreeMonad g)}
          alpha
          (freeMmult {f} feval))
        (vcompNT
          {f=(FreeMonad f . FreeMonad f)}
          {g=(FreeMonad g . FreeMonad g)}
          {h=(FreeMonad g)}
          (freeMmult {f=g} geval)
          (hcompNT
            {f=(FreeMonad f)} {g=(FreeMonad f)}
            {f'=(FreeMonad g)} {g'=(FreeMonad g)}
            (freeMap {f} feval) alpha alpha)))

-- Derive (the object-map component of) a (contravariant) functor between the
-- Eilenberg-Moore categories of a pair of monads from a morphism between the
-- monads.
public export
FreeMonadMorphToMonadFunctor : {f, g : Type -> Type} ->
  {feval : FreeFEval f} -> {geval : FreeFEval g} ->
  FreeMonadCatMorph {f} {g} feval geval ->
  (a : Type ** FreeMAlgSig g a) -> (b : Type ** FreeMAlgSig f b)
FreeMonadMorphToMonadFunctor {f} {g} {feval} {geval}
  (Element0 alpha comm) (a ** m) = (a ** m . alpha a)

public export
FreeMonadMorphToFunctorFunctor : {f, g : Type -> Type} ->
  {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  {feval : FreeFEval f} -> {geval : FreeFEval g} ->
  FreeMonadCatMorph {f} {g} feval geval ->
  (a : Type ** Algebra g a) -> (b : Type ** Algebra f b)
FreeMonadMorphToFunctorFunctor {f} {fm} {g} {feval} {geval}
  (Element0 alpha comm) (a ** m) =
    (a ** FAlgFromFree {f} {fm} $ FAlgToFree geval m . alpha a)

----------------------------------------
----------------------------------------
---- Universal properties in `Type` ----
----------------------------------------
----------------------------------------

-------------------------------------------
---- Objects of categories of elements ----
-------------------------------------------

public export
ElemCatObj : (Type -> Type) -> Type
ElemCatObj f = Sigma {a=Type} f

-------------------------------------------------------
---- Morphisms of covariant categories of elements ----
-------------------------------------------------------

public export
CovarElemCatMor : {f : Type -> Type} -> Functor f ->
  ElemCatObj f -> ElemCatObj f -> Type
CovarElemCatMor {f} fm (a ** efa) (b ** efb) =
  Subset0 (a -> b) (\m => map {f} m efa = efb)

-------------------------------------------------------------
---- Initial objects of covariant categories of elements ----
-------------------------------------------------------------

public export
HasAllOutgoing : {f : Type -> Type} -> Functor f -> ElemCatObj f -> Type
HasAllOutgoing {f} fm (a ** efa) =
  (eb : ElemCatObj f) -> CovarElemCatMor fm (a ** efa) eb

public export
0 AllOutgoingUnique : {f : Type -> Type} ->
  (fm : Functor f) -> (e : ElemCatObj f) ->
  (0 _ : HasAllOutgoing {f} fm e) -> Type
AllOutgoingUnique {f} fm (a ** efa) m =
  (b : Type) -> (efb : f b) ->
  (m' : CovarElemCatMor {f} fm (a ** efa) (b ** efb)) ->
  FunExtEq (Subset0.fst0 $ m (b ** efb)) (Subset0.fst0 $ m')

public export
IsInitialCovarElemCatObj : {f : Type -> Type} ->
  Functor f -> ElemCatObj f -> Type
IsInitialCovarElemCatObj {f} fm e =
  Exists0 (HasAllOutgoing {f} fm e) (AllOutgoingUnique {f} fm e)

public export
InitCovarElemCatObj : {f : Type -> Type} -> Functor f -> Type
InitCovarElemCatObj {f} fm =
  Subset0 (ElemCatObj f) (IsInitialCovarElemCatObj {f} fm)

-----------------------------------------------------------
---- Morphisms of contravariant categories of elements ----
-----------------------------------------------------------

public export
ContravarElemCatMor : {f : Type -> Type} -> Contravariant f ->
  ElemCatObj f -> ElemCatObj f -> Type
ContravarElemCatMor {f} fm (a ** efa) (b ** efb) =
  Subset0 (a -> b) (\m => contramap {f} m efb = efa)

------------------------------------------------------------------
---- Terminal objects of contravariant categories of elements ----
------------------------------------------------------------------

public export
HasAllIncoming : {f : Type -> Type} -> Contravariant f -> ElemCatObj f -> Type
HasAllIncoming {f} fm (a ** efa) =
  (eb : ElemCatObj f) -> ContravarElemCatMor fm eb (a ** efa)

public export
0 AllIncomingUnique : {f : Type -> Type} ->
  (fm : Contravariant f) -> (e : ElemCatObj f) ->
  (0 _ : HasAllIncoming {f} fm e) -> Type
AllIncomingUnique {f} fm (a ** efa) m =
  (b : Type) -> (efb : f b) ->
  (m' : ContravarElemCatMor {f} fm (b ** efb) (a ** efa)) ->
  FunExtEq (Subset0.fst0 $ m (b ** efb)) (Subset0.fst0 $ m')

public export
IsTerminalContravarElemCatObj : {f : Type -> Type} ->
  Contravariant f -> ElemCatObj f -> Type
IsTerminalContravarElemCatObj {f} fm e =
  Exists0 (HasAllIncoming {f} fm e) (AllIncomingUnique {f} fm e)

public export
TerminalContravarElemCatObj : {f : Type -> Type} -> Contravariant f -> Type
TerminalContravarElemCatObj {f} fm =
  Subset0 (ElemCatObj f) (IsTerminalContravarElemCatObj {f} fm)

----------------------------------------------------
---- Objects of categories of diagonal elements ----
----------------------------------------------------

public export
DiagElemCatObj : (Type -> Type -> Type) -> Type
DiagElemCatObj = CoendBase

------------------------------------------------------
---- Morphisms of categories of diagonal elements ----
------------------------------------------------------

public export
DiagElemCatMor : {f : Type -> Type -> Type} -> Profunctor f ->
  DiagElemCatObj f -> DiagElemCatObj f -> Type
DiagElemCatMor {f} dm (a ** efa) (b ** efb) =
  Subset0 (a -> b) (\m => dimap {f} id m efa = dimap {f} m id efb)

------------------------------
------------------------------
---- Dialgebra profunctor ----
------------------------------
------------------------------

public export
DialgebraProf : (Type -> Type) -> (Type -> Type) -> ProfunctorSig
DialgebraProf f g x y = f x -> g y

public export
DialgebraDimap : (f, g : Type -> Type) -> Functor f -> Functor g ->
  DimapSig (DialgebraProf f g)
DialgebraDimap f g fm gm mca mbd dialg = map {f=g} mbd . dialg . map {f} mca

--------------------------------------------
--------------------------------------------
---- Dialgebra twisted-arrow copresheaf ----
--------------------------------------------
--------------------------------------------

public export
DialgebraTwF : (Type -> Type) -> (Type -> Type) -> TwArrCoprSig
DialgebraTwF f g x y mxy = DialgebraProf f g x y

public export
DialgebraTwMap : (f, g : Type -> Type) -> Functor f -> Functor g ->
  TwArrCoprDimapSig (DialgebraTwF f g)
DialgebraTwMap f g fm gm s t a b mst = DialgebraDimap f g fm gm

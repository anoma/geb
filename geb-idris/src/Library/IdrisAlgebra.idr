module Library.IdrisAlgebra

import Library.IdrisUtils
import Library.IdrisCategories

%default total

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

-- The effect of an equalizer on morphisms between objects of `FinSet`
-- may be viewed as erasing some terms from the domain, so we can represent
-- objects of `FinSet` as lists of booleans, where the length is the
-- cardinality of the underlying set without any equalizers, and the booleans
-- indicate which terms have been erased.

-- Rather than the concrete type `List Bool`, we use algebras of `BinNatF`,
-- thereby requiring only that the type implement the interface of `List Bool`,
-- not that it be `List Bool` precisely.
public export
FSEqObj : Type
FSEqObj = FAlgObj FreeBinNat

public export
freeBinNatMap : {a, b : Type} -> (a -> b) -> FreeBinNat a -> FreeBinNat b
freeBinNatMap = freeMap evalBinNatF

public export
freeBinNatJoin : {a : Type} -> FreeBinNat (FreeBinNat a) -> FreeBinNat a
freeBinNatJoin = freeFJoin evalBinNatF

public export
bnAlgFromFreeObj : (alg : FAlgObj FreeBinNat) -> Algebra BinNatF (fst alg)
bnAlgFromFreeObj = FAlgFromFreeObj {f=BinNatF} {fm=map}

public export
bnAlgObjFromFree : FAlgObj FreeBinNat -> FAlgObj BinNatF
bnAlgObjFromFree = FAlgObjFromFree {f=BinNatF} {fm=map}

public export
bnAlgObjToFree : (alg : FAlgObj BinNatF) -> FreeMAlgSig BinNatF (fst alg)
bnAlgObjToFree = FAlgObjToFree {f=BinNatF} evalBinNatF

public export
bnAlgObjToFreeObj : FAlgObj BinNatF -> FAlgObj FreeBinNat
bnAlgObjToFreeObj = FAlgObjToFreeObj {f=BinNatF} evalBinNatF

public export
bnAlgObjToFreeIso : (a : FAlgObj BinNatF) ->
  FAlgIso {f=BinNatF} {fm=Prelude.map}
    (bnAlgObjFromFree (bnAlgObjToFreeObj a)) a
bnAlgObjToFreeIso (a ** m) =
  Element0
    (Element0 id $ \el => case el of NilF => Refl ; ConsF b x => Refl,
     Element0 id $ \el => case el of NilF => Refl ; ConsF b x => Refl)
    (\el => Refl, \el => Refl)

-- The unit property of an algebra over a free monad.
public export
FreeMonadAlgUnitP : {f : Type -> Type} ->
  FreeFEval f -> FAlgObj (FreeMonad f) -> Type
FreeMonadAlgUnitP {f} eval alg =
  ExtEq (snd alg . IdrisCategories.inFV) Prelude.id

-- The action property of an algebra over a free monad.
public export
FreeMonadAlgActP : {f : Type -> Type} ->
  FreeFEval f -> FAlgObj (FreeMonad f) -> Type
FreeMonadAlgActP {f} eval alg =
  ExtEq (snd alg . (freeMap eval $ snd alg)) (snd alg . freeFJoin eval)

-- The properties required to make an algebra over the underlying endofunctor
-- of a monad into an algebra over a monad.
public export
FreeMonadAlgP : {f : Type -> Type} ->
  FreeFEval f -> FAlgObj (FreeMonad f) -> Type
FreeMonadAlgP {f} eval alg =
  (FreeMonadAlgUnitP {f} eval alg, FreeMonadAlgActP {f} eval alg)

-- The signature of an algebra not only over the underlying endofunctor of
-- a free monad, but over the free monad _as_ a monad in the sense of "algebra
-- over a monad", which is an algebra over the underlying endofunctor together
-- with conditions that represent compatibility between that algebra and the
-- unit and multiplication of the monad.
public export
FreeMonadAlg : {f : Type -> Type} -> FreeFEval f -> Type
FreeMonadAlg {f} eval = (a : FAlgObj (FreeMonad f) ** FreeMonadAlgP {f} eval a)

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
-- that the category of algebras over the monad `FreeBinNat` is equivalent to
-- the category of algebras over the underlying endofunctor `BinNatF`, with
-- the equivalence being witnessed by `bnAlgObjToFreeObj` and
-- `bnAlgObjFromFree`.
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

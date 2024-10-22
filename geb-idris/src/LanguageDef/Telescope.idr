module LanguageDef.Telescope

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.InternalCat
import public LanguageDef.PolyCat
import public LanguageDef.SlicePolyCat
import public LanguageDef.PolySliceCat
import public LanguageDef.SlicePolyUMorph

%hide Library.IdrisCategories.BaseChangeF

public export
PNfi : (n : Nat) -> Vect n Nat -> Fin n -> Type -> Type
PNfi n v i = Vect (index i v)

public export
PNf : (n : Nat) -> Vect n Nat -> Type -> Type
PNf n v x = Sigma {a=(Fin n)} (flip (PNfi n v) x)

public export
data PNmu : (n : Nat) -> Vect n Nat -> Type where
  InPN : {n : Nat} -> {v : Vect n Nat} -> PNf n v (PNmu n v) -> PNmu n v

------------------------------------------
------------------------------------------
---- PRA functors on `MLDirichCatObj` ----
------------------------------------------
------------------------------------------

public export
PFpra1 : Type
PFpra1 = (pos : Type ** ParamDirichObj pos)

public export
InterpPFpra1pos : (pra1 : PFpra1) -> fst pra1 -> MLDirichCatObj -> Type
InterpPFpra1pos (pos ** dir) = MLDirichCatMor . dir

public export
InterpPFpra1posMap : (pra1 : PFpra1) -> (ep1 : fst pra1) ->
  (f, g : MLDirichCatObj) ->
  MLDirichCatMor f g -> InterpPFpra1pos pra1 ep1 f -> InterpPFpra1pos pra1 ep1 g
InterpPFpra1posMap (pos ** dir) ep1
  (fpos ** fdir) (gpos ** gdir) (onpos ** ondir) (fpm ** fdm) =
    (onpos . fpm ** sliceComp (\d1 => ondir (fpm d1)) fdm)

public export
InterpPFpra1posSl : (pra1 : PFpra1) -> MLDirichCatObj -> SliceObj (fst pra1)
InterpPFpra1posSl pra1 = flip (InterpPFpra1pos pra1)

public export
InterpPFpra1Sigma : PFpra1 -> MLDirichCatObj -> Type
InterpPFpra1Sigma pra1 = Sigma {a=(fst pra1)} . InterpPFpra1posSl pra1

public export
InterpPFpra1 : (pra1 : PFpra1) -> MLDirichCatObj ->
  SliceObj (Either Unit (fst pra1))
InterpPFpra1 pra1 p (Left ()) = InterpPFpra1Sigma pra1 p
InterpPFpra1 pra1 p (Right ep) = InterpPFpra1posSl pra1 p ep

public export
PFpra2 : PFpra1 -> Type
PFpra2 pra1 =
  (pos2 : fst pra1 -> Type **
   (i1 : fst pra1) -> pos2 i1 -> Type)

-- Suppose we have a slice object over `T1` in `PolyFunc`.  This
-- applies the dependent sum from `PolyFunc/T1` to `PolyFunc`
-- (where the latter is equivalent to `PolyFunc/PFTerminalArena`)
-- with the unique terminal morphism from `T1` to `PFTerminalArena`.
public export
PFSigmaPos : (t1 : PolyFunc) -> MlPolySlObj t1 -> Type
PFSigmaPos (t1pos ** t1dir) (MPSobj slpos sldir ondir) =
  (t1p : t1pos ** slpos t1p)

public export
PFSigmaDir : (t1 : PolyFunc) -> (sl : MlPolySlObj t1) ->
  SliceObj (PFSigmaPos t1 sl)
PFSigmaDir (t1pos ** t1dir) (MPSobj slpos sldir ondir) (t1p ** lp) =
  sldir t1p lp

public export
PFSigma : (t1 : PolyFunc) -> MlPolySlObj t1 -> PolyFunc
PFSigma t1 sl = (PFSigmaPos t1 sl ** PFSigmaDir t1 sl)

public export
PFET : PolyFunc -> Type
PFET = MlPolySlObj

-----------------
-----------------
---- Indexes ----
-----------------
-----------------

-- The position-type of `VectZ` viewed as an endofunctor on `PolyFunc`
-- is `const Unit` (the terminal object of `PolyFunc`), which in turn
-- is the `PolyFunc` whose position-type is `Unit` and whose direction-type
-- is `Void`.  (We obtain this by applying `VectZ` to the terminal object,
-- i.e. `const Unit`.  `VectZ` is constant so it returns `const Unit`
-- upon _any_ input.)
public export
VectZ : (Type -> Type) -> Type -> Type
VectZ = const $ const Unit

public export
VectZPF : PolyFunc -> PolyFunc
VectZPF _ = PFTerminalArena

public export
vectZpos : PolyFunc
vectZpos = PFTerminalArena

-- The position-type of `VectS` viewed as an endofunctor on `PolyFunc`
-- is `ProductF id (const Unit)`, which in turn is simply `id` (the
-- `PolyFunc` whose position-type is `Unit` and whose direction-type is `Unit`).
public export
VectS : (Type -> Type) -> Type -> Type
VectS = ProductF id

public export
VectSPF : PolyFunc -> PolyFunc
VectSPF (pos ** dir) = (pos ** Either Unit . dir)

public export
vectSpos : PolyFunc
vectSpos = PFIdentityArena

public export
VectF : (Type -> Type) -> Type -> Type
VectF f = CoproductF (VectZ f) (VectS f)

public export
VectFPFpos : PolyFunc -> Type
VectFPFpos (pos ** dir) = Either Unit pos

public export
VectFPFdir : (p : PolyFunc) -> SliceObj (VectFPFpos p)
VectFPFdir (pos ** dir) (Left ()) = Void
VectFPFdir (pos ** dir) (Right ep) = Either Unit (dir ep)

public export
VectFPF : PolyFunc -> PolyFunc
VectFPF p = (VectFPFpos p ** VectFPFdir p)

public export
vectFpos : PolyFunc
vectFpos = pfCoproductArena vectZpos vectSpos

public export
VectM : Nat -> Type -> Type
VectM Z = VectZ (const Unit)
VectM (S n') = VectS (VectM n')

public export
TelIdxN : Nat -> Type
TelIdxN = flip VectM Nat

public export
TelIdx : Type
TelIdx = Sigma {a=Nat} TelIdxN

-----------------
-----------------
---- Objects ----
-----------------
-----------------

module LanguageDef.Test.PolyIndTypesTest

import Test.TestLibrary
import LanguageDef.PolyIndTypes
import LanguageDef.SlicePolyCat
import LanguageDef.SlicePolyUMorph
import LanguageDef.GenPolyFunc

%default total

-----------------------------------------
-----------------------------------------
---- Simple dependent-pair induction ----
-----------------------------------------
-----------------------------------------

mutual
  public export
  data ST0 : Type where
    ST0u : ST0
    ST0p : ST0 -> ST0 -> ST0
    ST0d : (a, b, c : ST0) -> ST1 a -> ST1 b -> ST1 c -> ST0

  public export
  data ST1 : ST0 -> Type where
    ST1u :
      (a : ST0) -> ST1 a
    ST1p :
      (a, b : ST0) -> ST1 a -> ST1 b -> ST1 (ST0p a b)
    ST1d : (a, b, c : ST0) ->
      (da : ST1 a) -> (db : ST1 b) -> (dc : ST1 c) -> ST1 (ST0d a b c da db dc)
    ST1d' : (a, b : ST0) ->
      (da : ST1 a) -> (db : ST1 b) ->
      ST1 (ST0d a a b da da db)

public export
data ST0f : (x : Type) -> SliceObj x -> Type where
  ST0fu : {x : Type} -> {f : SliceObj x} ->
    ST0f x f
  ST0fp : {x : Type} -> {f : SliceObj x} ->
    x -> x -> ST0f x f
  ST0fd : {x : Type} -> {f : SliceObj x} ->
    (a, b, c : x) -> f a -> f b -> f c -> ST0f x f

public export
ST0F_T1 : MLDirichF1_T1
ST0F_T1 = Fin 3 -- fu, fp, fd

public export
ST0F_ET1pos : SliceObj ST0F_T1
ST0F_ET1pos FZ = Void -- `fu` has no parameters
ST0F_ET1pos (FS FZ) = Fin 2 -- `fp` has 2 parameters of non-dependent type
ST0F_ET1pos (FS (FS FZ)) = Fin 3 -- `fd` has 3 parameters of non-dependent type

public export
ST0F_ET1dir : (i : ST0F_T1) -> SliceObj (ST0F_ET1pos i)
ST0F_ET1dir FZ ie1 = void ie1
ST0F_ET1dir (FS FZ) FZ = Void -- `fp` has no parameters dependent on the first
                              -- non-dependent parameter
ST0F_ET1dir (FS FZ) (FS FZ) = Void -- `fp` has no parameters dependent on the
                                   -- second non-dependent parameter
ST0F_ET1dir (FS (FS FZ)) FZ = Unit -- `fd` has one parameter dependent on the
                                   -- first non-dependent parameter
ST0F_ET1dir (FS (FS FZ)) (FS FZ) = Unit -- ditto the second parameter
ST0F_ET1dir (FS (FS FZ)) (FS (FS FZ)) = Unit -- ditto the second parameter

public export
ST0F_ET1 : MLDirichF1_ET ST0F_T1
ST0F_ET1 = (ST0F_ET1pos ** ST0F_ET1dir)

public export
ST0F_F1 : MLDirichF1
ST0F_F1 = (ST0F_T1 ** ST0F_ET1)

-- Here we show that `ST0F_F1` has an equivalent interpretation to
-- `ST0f`.

public export
ST0f_to_ET1 : (x : Type) -> (sx : SliceObj x) ->
  ST0f x sx -> InterpMLDirichF1 ST0F_F1 (x ** sx)
ST0f_to_ET1 x sx ST0fu =
  (FZ ** \v => void v ** \v => void v)
ST0f_to_ET1 x sx (ST0fp a b) =
  (FS FZ **
   flip index [a, b] **
   \i, d => case i of FZ => void d ; FS FZ => void d)
ST0f_to_ET1 x sx (ST0fd a b c da db dc) =
  (FS (FS FZ) **
   flip index [a, b, c] **
   \i, d => case i of FZ => da ; FS FZ => db ; FS (FS FZ) => dc)

public export
ST0f_from_ET1 : (x : Type) -> (sx : SliceObj x) ->
  InterpMLDirichF1 ST0F_F1 (x ** sx) -> ST0f x sx
ST0f_from_ET1 x sx (FZ ** dm1 ** dm2) =
  ST0fu
ST0f_from_ET1 x sx (FS FZ ** dm1 ** dm2) =
  ST0fp (dm1 FZ) (dm1 $ FS FZ)
ST0f_from_ET1 x sx (FS $ FS FZ ** dm1 ** dm2) =
  ST0fd
    (dm1 FZ) (dm1 $ FS FZ) (dm1 $ FS $ FS FZ)
    (dm2 FZ ()) (dm2 (FS FZ) ()) (dm2 (FS $ FS FZ) ())

public export
data ST1f : (x : Type) -> (f : SliceObj x) -> Type where
  ST1fu : {x : Type} -> {f : SliceObj x} ->
    ST1f x f
  ST1fp : {x : Type} -> {f : SliceObj x} ->
    {a, b : x} -> f a -> f b ->
    ST1f x f
  ST1fd : {x : Type} -> {f : SliceObj x} ->
    {a, b, c : x} -> f a -> f b -> f c ->
    ST1f x f
  ST1fd' : {x : Type} -> {f : SliceObj x} ->
    {a, b : x} -> f a -> f b ->
    ST1f x f

public export
ST1F_T1 : MLDirichF1_T1
ST1F_T1 = Fin 4 -- fu, fp, fd, fd'

public export
ST1F_ET1pos : SliceObj ST1F_T1
ST1F_ET1pos FZ = Void
ST1F_ET1pos (FS FZ) = Fin 2
ST1F_ET1pos (FS (FS FZ)) = Fin 3
ST1F_ET1pos (FS (FS (FS FZ))) = Fin 2

public export
ST1F_ET1dir : (i : ST1F_T1) -> SliceObj (ST1F_ET1pos i)
ST1F_ET1dir FZ ie1 = void ie1
ST1F_ET1dir (FS FZ) FZ = Unit
ST1F_ET1dir (FS FZ) (FS FZ) = Unit
ST1F_ET1dir (FS (FS FZ)) FZ = Unit
ST1F_ET1dir (FS (FS FZ)) (FS FZ) = Unit
ST1F_ET1dir (FS (FS FZ)) (FS (FS FZ)) = Unit
ST1F_ET1dir (FS (FS (FS FZ))) FZ = Unit
ST1F_ET1dir (FS (FS (FS FZ))) (FS FZ) = Unit

public export
ST1F_ET1 : MLDirichF1_ET ST1F_T1
ST1F_ET1 = (ST1F_ET1pos ** ST1F_ET1dir)

public export
ST1F_F1 : MLDirichF1
ST1F_F1 = (ST1F_T1 ** ST1F_ET1)

public export
ST1f_to_ET1 : (x : Type) -> (sx : SliceObj x) ->
  ST1f x sx -> InterpMLDirichF1 ST1F_F1 (x ** sx)
ST1f_to_ET1 x sx ST1fu =
  (FZ ** \v => void v ** \v => void v)
ST1f_to_ET1 x sx (ST1fp {a} {b} da db) =
  (FS FZ **
   flip index [a, b] **
   \i, d => case i of FZ => da; FS FZ => db)
ST1f_to_ET1 x sx (ST1fd {a} {b} {c} da db dc) =
  (FS (FS FZ) **
   flip index [a, b, c] **
   \i, d => case i of FZ => da ; FS FZ => db ; FS (FS FZ) => dc)
ST1f_to_ET1 x sx (ST1fd' {a} {b} da db) =
  (FS (FS FZ) **
   flip index [a, a, b] **
   \i, d => case i of FZ => da ; FS FZ => da ; FS (FS FZ) => db)

public export
ST1f_from_ET1 : (x : Type) -> (sx : SliceObj x) ->
  InterpMLDirichF1 ST1F_F1 (x ** sx) -> ST1f x sx
ST1f_from_ET1 x sx (FZ ** dm1 ** dm2) =
  ST1fu
ST1f_from_ET1 x sx (FS FZ ** dm1 ** dm2) =
  ST1fp {a=(dm1 FZ)} {b=(dm1 $ FS FZ)} (dm2 FZ ()) (dm2 (FS FZ) ())
ST1f_from_ET1 x sx (FS $ FS FZ ** dm1 ** dm2) =
  ST1fd (dm2 FZ ()) (dm2 (FS FZ) ()) (dm2 (FS $ FS FZ) ())
ST1f_from_ET1 x sx (FS $ FS $ FS FZ ** dm1 ** dm2) =
  ST1fd' (dm2 FZ ()) (dm2 (FS FZ) ())

public export
ST1fnt : (x : Type) -> (f : SliceObj x) -> ST1f x f -> ST0f x f
ST1fnt x f ST1fu = ST0fu {x} {f}
ST1fnt x f (ST1fp {a} {b} da db) = ST0fp {x} {f} a b
ST1fnt x f (ST1fd {a} {b} {c} da db dc) = ST0fd {x} {f} a b c da db dc
ST1fnt x f (ST1fd' {a} {b} da db) = ST0fd {x} {f} a a b da da db

public export
STntOnPos1 : ST1F_T1 -> ST0F_T1
STntOnPos1 FZ = FZ
STntOnPos1 (FS FZ) = FS FZ
STntOnPos1 (FS (FS FZ)) = FS $ FS FZ
STntOnPos1 (FS (FS (FS FZ))) = FS $ FS FZ

public export
STntOnPos2 : (i : ST1F_T1) -> ST0F_ET1pos (STntOnPos1 i) -> ST1F_ET1pos i
STntOnPos2 FZ i2 = void i2
STntOnPos2 (FS FZ) FZ = FZ
STntOnPos2 (FS FZ) (FS FZ) = FS FZ
STntOnPos2 (FS (FS FZ)) FZ = FZ
STntOnPos2 (FS (FS FZ)) (FS FZ) = FS FZ
STntOnPos2 (FS (FS FZ)) (FS (FS FZ)) = FS $ FS FZ
STntOnPos2 (FS (FS (FS FZ))) FZ = FZ
STntOnPos2 (FS (FS (FS FZ))) (FS FZ) = FZ
STntOnPos2 (FS (FS (FS FZ))) (FS (FS FZ)) = FS FZ

public export
STntOnDir : (i1 : ST1F_T1) -> (i2 : ST0F_ET1pos (STntOnPos1 i1)) ->
  ST0F_ET1dir (STntOnPos1 i1) i2 -> ST1F_ET1dir i1 (STntOnPos2 i1 i2)
STntOnDir FZ i2 d = void i2
STntOnDir (FS FZ) FZ d = void d
STntOnDir (FS FZ) (FS FZ) d = void d
STntOnDir (FS (FS FZ)) FZ () = ()
STntOnDir (FS (FS FZ)) (FS FZ) () = ()
STntOnDir (FS (FS FZ)) (FS (FS FZ)) () = ()
STntOnDir (FS (FS (FS FZ))) FZ () = ()
STntOnDir (FS (FS (FS FZ))) (FS FZ) () = ()
STntOnDir (FS (FS (FS FZ))) (FS (FS FZ)) () = ()

public export
STnt : MLDirichF1NT ST1F_F1 ST0F_F1
STnt = (STntOnPos1 ** STntOnPos2 ** STntOnDir)

public export
STf1Sl : MLDirichF1Sl ST0F_F1
STf1Sl = (ST1F_F1 ** STnt)

public export
STmlf : MLDirichF
STmlf = (ST0F_F1 ** STf1Sl)

public export
ST1ft : (x : Type) -> (f : SliceObj x) -> ST0f x f -> Type
ST1ft x f f0 = (f1 : ST1f x f ** ST1fnt x f f1 = f0)

----------------------------------
----------------------------------
---- Dependent-pair induction ----
----------------------------------
----------------------------------

T0Starter' : Type
T0Starter' = ()

T0Maker' : Type -> Type
T0Maker' = ProductMonad

T0DepMaker' : (Type, Type) -> Type
T0DepMaker' (a, b) = (a, b, b)

Test0' : (Type, Type) -> Type
Test0' (a, b) = Either T0Starter' (Either (T0Maker' a) (T0DepMaker' (a, b)))

T0DepMakerF : {t0 : Type} -> SliceObj t0 -> Type
T0DepMakerF {t0} t1 = (a : t0 ** Fin 2 -> t1 a)

T0DepMakerSPFam : SPFDataFam {b=Type} Prelude.id (const Unit)
T0DepMakerSPFam t0 = SPFD (const t0) (\u_, et0, et0' => (et0 = et0', Fin 2))

T0DepMakerFtoSPFam : {t0 : Type} -> (t1 : SliceObj t0) ->
  T0DepMakerF {t0} t1 ->
  InterpSPFData {dom=t0} {cod=Unit} (T0DepMakerSPFam t0) t1 ()
T0DepMakerFtoSPFam {t0} t1 (et0 ** t1dm) = (et0 ** \et0, (Refl, i) => t1dm i)

T0DepMakerSPFamtoF : {t0 : Type} -> (t1 : SliceObj t0) ->
  InterpSPFData {dom=t0} {cod=Unit} (T0DepMakerSPFam t0) t1 () ->
  T0DepMakerF {t0} t1
T0DepMakerSPFamtoF {t0} t1 (et0 ** t1dm) = (et0 ** \i => t1dm et0 (Refl, i))

T0FF : {t0 : Type} -> SliceObj t0 -> Type
T0FF {t0} t1 = Either Unit (Either (t0, t0) (T0DepMakerF {t0} t1))

T0SPFamPos : (t0 : Type) -> SliceObj Unit
T0SPFamPos t0 () =
  Either
    -- T0Starter
    Unit
  $ Either
    -- T0Maker
    (t0, t0)
    -- T0DepMaker
    t0

T0SPFamDir : (t0 : Type) -> SPFdirType t0 Unit (T0SPFamPos t0)
T0SPFamDir t0 () (Left ()) et0 =
  -- T0Starter
  Void
T0SPFamDir t0 () (Right (Left (et0, et1))) et2 =
  -- T0Maker
  Void
T0SPFamDir t0 () (Right (Right et0)) et0' =
  -- T0DepMaker
  (et0 = et0', Fin 2)

T0SPFam : SPFDataFam {b=Type} Prelude.id (const Unit)
T0SPFam t0 = SPFD (T0SPFamPos t0) (T0SPFamDir t0)

T0FtoSPFam : {t0 : Type} -> (t1 : SliceObj t0) ->
  T0FF {t0} t1 ->
  InterpSPFData {dom=t0} {cod=Unit} (T0SPFam t0) t1 ()
T0FtoSPFam {t0} t1 (Left ()) =
  (Left () ** \_ => voidF _)
T0FtoSPFam {t0} t1 (Right $ Left (et0, et1)) =
  (Right (Left (et0, et1)) ** \_ => voidF _)
T0FtoSPFam {t0} t1 (Right $ Right el) =
  let (el1 ** el2) = T0DepMakerFtoSPFam {t0} t1 el in
  (Right (Right el1) ** el2)

T0SPFamToF : {t0 : Type} -> (t1 : SliceObj t0) ->
  InterpSPFData {dom=t0} {cod=Unit} (T0SPFam t0) t1 () ->
  T0FF {t0} t1
T0SPFamToF {t0} t1 (Left () ** dm) =
  Left ()
T0SPFamToF {t0} t1 (Right $ Left (et0, et0') ** dm) =
  Right $ Left (et0, et0')
T0SPFamToF {t0} t1 (Right $ Right el ** dm) =
  Right $ Right (el ** \i => dm el (Refl, i))

T0NonDepSPFpos : SliceObj Unit
T0NonDepSPFpos () = Either Unit (Either Unit Unit)

T0NonDepSPFdir : SPFdirType Unit Unit T0NonDepSPFpos
T0NonDepSPFdir () (Left ()) () = Void
T0NonDepSPFdir () (Right $ Left ()) () = Fin 2
T0NonDepSPFdir () (Right $ Right ()) () = Unit

T0NonDepSPF : SPFData Unit Unit
T0NonDepSPF = SPFD T0NonDepSPFpos T0NonDepSPFdir

T0DepSPFdir : (t0 : Type) ->
  -- SPFdirType t0 Unit (InterpSPFData T0NonDepSPF (const t0))
  (ec : Unit) -> (ep : InterpSPFData T0NonDepSPF (const t0) ec) -> SliceObj t0
T0DepSPFdir t0 () (Left () ** dm) et0 = Void
T0DepSPFdir t0 () (Right $ Left () ** dm) et0 = Void
T0DepSPFdir t0 () (Right $ Right () ** dm) et0 = (dm () () = et0, Fin 2)

T0DepSPF : (t0 : Type) -> SPFData t0 Unit
T0DepSPF t0 = SPFD (InterpSPFData T0NonDepSPF (const t0)) (T0DepSPFdir t0)

DFT1 : Type
DFT1 = (pos : Type ** dir : SliceObj pos ** (ep : pos) -> SliceObj (dir ep))

InterpDFT1 : DFT1 -> (a : Type) -> SliceObj a -> Type
InterpDFT1 (pos ** dir ** depdir) a sa =
  (ep : pos **
   dm : dir ep -> a **
   SliceMorphism {a=(dir ep)} (depdir ep) (sa . dm))

DFET : DFT1 -> Type
DFET (pos ** dir ** depdir) =
  (pos2 : Type **
   dir2 : SliceObj pos2 **
   (ep2 : pos2) -> dir2 ep2 -> ?DFET_hole)

InterpDFET : (t1 : DFT1) -> DFET t1 -> (a : Type) -> (sa : SliceObj a) ->
  SliceObj (InterpDFT1 t1 a sa)
InterpDFET (pos ** dir ** depdir) (pos2 ** dir2 ** dfet)
  a sa (ep ** dm ** ddm) =
    (esp : pos2 ** ?InterpDFET_hole)

TestPRAT1pos : Unit -> Type
TestPRAT1pos _ = Fin 3 -- T0Starter, T0Maker, T0DepMaker

TestPRAT1dir : (u : Unit) -> TestPRAT1pos u -> Unit -> Type
TestPRAT1dir () FZ () = Fin 2 -- T1Starter, T1Id
TestPRAT1dir () (FS FZ) () = Fin 4 -- T1Maker, T1Id, T1Composer, T1Distrib
TestPRAT1dir () (FS (FS FZ)) () = Fin 3 -- T1Id, T1DepComposer, T1Telescope

TestPRAT1 : MlDirichSlObj MLDirichCatObjTerminal
TestPRAT1 = MDSobj TestPRAT1pos TestPRAT1dir

TestPRAdirPos : SliceObj (Unit, Sigma {a=Unit} TestPRAT1pos)
TestPRAdirPos ((), (() ** FZ)) = ?TestPRAdirPos_hole_0
TestPRAdirPos ((), (() ** (FS FZ))) = ?TestPRAdirPos_hole_1
TestPRAdirPos ((), (() ** (FS (FS FZ)))) = ?TestPRAdirPos_hole_2

TestPRAdirDir :
  (i : (Unit, Sigma {a=Unit} TestPRAT1pos)) ->
  TestPRAdirPos i ->
  SliceObj (Unit, (u : Unit ** TestPRAT1dir (fst $ snd i) (snd $ snd i) u))
-- TestPRAdirDir ((), (() ** i)) j k = ?TestPRAdirDir_hole

TestPRAdir : PRAdirType MLDirichCatObjTerminal MLDirichCatObjTerminal TestPRAT1
TestPRAdir = MDSobj TestPRAdirPos TestPRAdirDir

TestPRA : PRAData MLDirichCatObjTerminal MLDirichCatObjTerminal
TestPRA = PRAD TestPRAT1 TestPRAdir

mutual
  public export
  T0StarterT : Type
  T0StarterT = Unit

  public export
  data T0MakerT : Type where
    T0Mk : Test0 -> Test0 -> T0MakerT

  public export
  data T0DepMakerT : Type where
    T0DepMk : (a : Test0) -> Test1 a -> Test1 a -> T0DepMakerT

  public export
  data Test0 : Type where
    T0Starter : T0StarterT -> Test0
    T0Maker : T0MakerT -> Test0
    T0DepMaker : T0DepMakerT -> Test0

  public export
  data T1StarterT : T0StarterT -> Type where
    T1Start : T1StarterT ()

  public export
  T1IdT : Test0 -> Type
  T1IdT _ = Unit

  public export
  data Test1 : Test0 -> Type where
    T1Starter : (t0s : T0StarterT) -> T1StarterT t0s -> Test1 (T0Starter t0s)
    T1Id : (a : Test0) -> T1IdT a -> Test1 a
    T1Maker :
      (a, b : Test0) -> Test1 a -> Test1 b -> Test1 (T0Maker $ T0Mk a b)
    T1Composer : (a, b, c : Test0) ->
      Test1 (T0Maker $ T0Mk b c) -> Test1 (T0Maker $ T0Mk a b) ->
      Test1 (T0Maker $ T0Mk a c)
    T1Distrib : (a, b, c : Test0) ->
      Test1 (T0Maker $ T0Mk a (T0Maker $ T0Mk b c)) ->
      Test1 (T0Maker $ T0Mk (T0Maker $ T0Mk a b) (T0Maker $ T0Mk a c))
    T1DepComposer :
      (a : Test0) -> (f, g, h : Test1 a) ->
      Test1 (T0DepMaker $ T0DepMk a g h) ->
      Test1 (T0DepMaker $ T0DepMk a f g) ->
      Test1 (T0DepMaker $ T0DepMk a f h)
    T1Telescope : (a : Test0) -> (f, g : Test1 a) ->
      (t, t' : Test1 (T0DepMaker $ T0DepMk a f g)) ->
      (dt, dt' :
        Test1 (T0DepMaker $ T0DepMk (T0DepMaker $ T0DepMk a f g) t t')) ->
      Test1
        (T0DepMaker $
          T0DepMk
            (T0DepMaker $ T0DepMk (T0DepMaker $ T0DepMk a f g) t t') dt dt')

--------------------------------------------
--------------------------------------------
---- Finitary inductive-inductive types ----
--------------------------------------------
--------------------------------------------

t0Starter : FinIndIndF1Constr
t0Starter = FII1c 0 0 []

t0Maker : FinIndIndF1Constr
t0Maker = FII1c 2 0 []

t0DepMaker : FinIndIndF1Constr
t0DepMaker = FII1c 1 2 [ FZ, FZ ]

T0F : FinIndIndF1
T0F = FII1 [ t0Starter, t0Maker, t0DepMaker ]

t1Starter : FinIndIndF2Constr T0F
t1Starter = FII2c 0 0 FF2AZ $ FF2t1a (FZ ** [] ** [])

t1Id : FinIndIndF2Constr T0F
t1Id = FII2c 1 0 FF2AZ $ FF2t1p FZ

t1Maker : FinIndIndF2Constr T0F
t1Maker = FII2c 2 2 (FF2AS (FF2AS FF2AZ $ FF2t1p FZ) $ FF2t1p $ FS FZ) $
  FF2t1a (FS FZ ** [FF2t1p FZ, FF2t1p $ FS FZ] ** [])

t1Telescope : FinIndIndF2Constr T0F
t1Telescope = FII2c 1 6
  (FF2AS (FF2AS (FF2AS (FF2AS (FF2AS (FF2AS FF2AZ
    $ FF2t1p FZ)
    $ FF2t1p FZ)
    $ FF2t1a ((FS (FS FZ)) **
      [FF2t1p FZ] **
      [?t1Telescope_FF2t2hd_hole, ?t1Telescope_FF2t2tl_hole]))
    $ ?t1Telescope_hole_tel_4)
    $ ?t1Telescope_hole_tel_5)
    $ ?t1Telescope_hole_tel_6) $
  ?t1Telescope_hole_param

T1F : FinIndIndF2 T0F
T1F = FII2 [ t1Starter, t1Id, t1Maker, t1Telescope ]

T01F : FinIndInd
T01F = (T0F ** T1F)

T0 : Type
T0 = FinIndIndMu1 T01F

T1 : T0 -> Type
T1 = FinIndIndMu2 T01F

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
polyIndTypesTest : IO ()
polyIndTypesTest = do
  putStrLn ""
  putStrLn "======================="
  putStrLn "Begin PolyIndTypesTest:"
  putStrLn "-----------------------"
  putStrLn ""
  putStrLn "---------------------"
  putStrLn "End PolyIndTypesTest."
  putStrLn "====================="
  pure ()

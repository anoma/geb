module LanguageDef.Theories

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.RefinedADT

%default total

---------------------------------------
---------------------------------------
---- Bool as (one-object) category ----
---------------------------------------
---------------------------------------

-------------------------------
---- Objects and morphisms ----
-------------------------------

public export
data BoolObj : Type where
  BOBool : BoolObj

public export
DecEq BoolObj where
  decEq BOBool BOBool = Yes Refl

public export
Eq BoolObj where
  b == b' = isYes (decEq b b')

public export
Show BoolObj where
  show BOBool = "Bool"

public export
data BoolMorph : Type where
  BMid : BoolMorph
  BMnot : BoolMorph
  BMtrue : BoolMorph
  BMfalse : BoolMorph

public export
DecEq BoolMorph where
  decEq BMid BMid = Yes Refl
  decEq BMid BMnot = No $ \eq => case eq of Refl impossible
  decEq BMid BMtrue = No $ \eq => case eq of Refl impossible
  decEq BMid BMfalse = No $ \eq => case eq of Refl impossible
  decEq BMnot BMid = No $ \eq => case eq of Refl impossible
  decEq BMnot BMnot = Yes Refl
  decEq BMnot BMtrue = No $ \eq => case eq of Refl impossible
  decEq BMnot BMfalse = No $ \eq => case eq of Refl impossible
  decEq BMtrue BMid = No $ \eq => case eq of Refl impossible
  decEq BMtrue BMnot = No $ \eq => case eq of Refl impossible
  decEq BMtrue BMtrue = Yes Refl
  decEq BMtrue BMfalse = No $ \eq => case eq of Refl impossible
  decEq BMfalse BMid = No $ \eq => case eq of Refl impossible
  decEq BMfalse BMnot = No $ \eq => case eq of Refl impossible
  decEq BMfalse BMtrue = No $ \eq => case eq of Refl impossible
  decEq BMfalse BMfalse = Yes Refl

public export
Eq BoolMorph where
  bm == bm' = isYes (decEq bm bm')

public export
Show BoolMorph where
  show BMid = "id"
  show BMnot = "not"
  show BMtrue = "t"
  show BMfalse = "f"

public export
bmDom : BoolMorph -> BoolObj
bmDom _ = BOBool

public export
bmCod : BoolMorph -> BoolObj
bmCod _ = BOBool

public export
bmId : (a : BoolObj) -> BoolMorph
bmId BOBool = BMid

public export
0 bmIdDom : (0 a : BoolObj) -> bmDom (bmId a) = a
bmIdDom BOBool = Refl

public export
0 bmIdCod : (0 a : BoolObj) -> bmCod (bmId a) = a
bmIdCod BOBool = Refl

public export
bmComp : (g, f : BoolMorph) -> bmCod f = bmDom g -> BoolMorph
bmComp BMid f Refl = f
bmComp BMnot BMid Refl = BMnot
bmComp BMnot BMnot Refl = BMid
bmComp BMnot BMtrue Refl = BMfalse
bmComp BMnot BMfalse Refl = BMtrue
bmComp BMtrue _ Refl = BMtrue
bmComp BMfalse _ Refl = BMfalse

public export
0 bmCompDom :
  (0 g, f : BoolMorph) -> {0 eq : bmCod f = bmDom g} ->
  bmDom (bmComp g f eq) = bmDom f
bmCompDom g f {eq} = Refl

public export
0 bmCompCod :
  (0 g, f : BoolMorph) -> {0 eq : bmCod f = bmDom g} ->
  bmCod (bmComp g f eq) = bmCod g
bmCompCod g f {eq} = Refl

------------------------------------
---- Interpretation into `Type` ----
------------------------------------

public export
interpBoolObj : BoolObj -> Type
interpBoolObj BOBool = Bool

public export
RefinedBoolMorph : BoolObj -> BoolObj -> Type
RefinedBoolMorph b b' =
  Refinement {a=BoolMorph} $ (\m => bmDom m == b && bmCod m == b')

public export
interpBoolMorph : {0 b, b' : BoolObj} -> RefinedBoolMorph b b' ->
  interpBoolObj b -> interpBoolObj b'
interpBoolMorph {b=BOBool} {b'=BOBool} (Element0 BMid eq) = id
interpBoolMorph {b=BOBool} {b'=BOBool} (Element0 BMnot eq) = not
interpBoolMorph {b=BOBool} {b'=BOBool} (Element0 BMtrue eq) = const True
interpBoolMorph {b=BOBool} {b'=BOBool} (Element0 BMfalse eq) = const False

------------------------------------------------------------------------
------------------------------------------------------------------------
---- Boolean circuits (such as modeled by BITC) as a Lawvere theory ----
------------------------------------------------------------------------
------------------------------------------------------------------------

--------------------
---- Definition ----
--------------------

-- Every object of this category is some natural number of bits.
public export
data BCLawObj : Type where
  BCLOnbits : Nat -> BCLawObj

public export
DecEq BCLawObj where
  decEq (BCLOnbits m) (BCLOnbits n) = case decEq m n of
    Yes Refl => Yes Refl
    No neq => case neq of Refl impossible

public export
Eq BCLawObj where
  x == y = isYes $ decEq x y

public export
Show BCLawObj where
  show (BCLOnbits n) = "2^" ++ show n

public export
BCLawSig : Type
BCLawSig = (BCLawObj, BCLawObj)

-- The total space of morphisms in the boolean-Lawvere category.
-- Slices of this provide the morphisms indexed by signature
-- (domain and codomain).  These should compile very directly to BITC.
public export
data BCLawMorph : Type where
  -- The identity which is present in all categories.  Composition
  -- is not explicit here, but derived.
  BCLMid : BCLawObj -> BCLawMorph

  -- Every object of of the BCLaw category is a finite product (of Bool).
  --
  -- This is the left adjunct, which provides the product introduction rule.
  BCLMprodAdjL : List BCLawMorph -> BCLawMorph

public export
DecEq BCLawMorph where
  decEq = decEqOne where
    mutual
      public export
      decEqOne : DecEqPred BCLawMorph
      decEqOne (BCLMid m) (BCLMid n) = case decEq m n of
        Yes Refl => Yes Refl
        No neq => case neq of Refl impossible
      decEqOne (BCLMid _) (BCLMprodAdjL _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjL _) (BCLMid _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjL fs) (BCLMprodAdjL gs) = case decEqList fs gs of
        Yes Refl => Yes Refl
        No neq => case neq of Refl impossible

      public export
      decEqList : DecEqPred (List BCLawMorph)
      decEqList [] [] = Yes Refl
      decEqList [] (_ :: _) = No $ \eq => case eq of Refl impossible
      decEqList (_ :: _) [] = No $ \eq => case eq of Refl impossible
      decEqList (f :: fs) (g :: gs) = case (decEqOne f g, decEqList fs gs) of
        (Yes Refl, Yes Refl) => Yes Refl
        (No neq, _) => No $ \eq => case eq of Refl => neq Refl
        (_, No neq) => No $ \eq => case eq of Refl => neq Refl

public export
Eq BCLawMorph where
  f == g = isYes $ decEq f g

public export
Show BCLawMorph where
  show = showOne where
    mutual
      public export
      showOne : BCLawMorph -> String
      showOne (BCLMid n) = "id[" ++ show n ++ "]"
      showOne (BCLMprodAdjL fs) = "prodAdjL[" ++ showList fs ++ "]"

      public export
      showList : List BCLawMorph -> String
      showList fs = "[" ++ showListRec fs ++ "]"

      public export
      showListRec : List BCLawMorph -> String
      showListRec [] = ""
      showListRec (f :: []) = showOne f
      showListRec (f :: fs@(g :: gs)) = showOne f ++ ", " ++ showListRec fs

public export
checkBCLMCurried : BCLawObj -> BCLawObj -> BCLawMorph -> Bool
checkBCLMCurried = checkBCLMOne where
  mutual
    public export
    checkBCLMOne : BCLawObj -> BCLawObj -> BCLawMorph -> Bool
    checkBCLMOne m n (BCLMid k) =
      m == k && n == k
    checkBCLMOne m (BCLOnbits n) (BCLMprodAdjL fs) =
      length fs == n && checkBCLMList m (BCLOnbits 1) fs

    public export
    checkBCLMList : BCLawObj -> BCLawObj -> List BCLawMorph -> Bool
    checkBCLMList m n [] = True
    checkBCLMList m n (f :: fs) = checkBCLMOne m n f && checkBCLMList m n fs

public export
checkBCLM : BCLawSig -> BCLawMorph -> Bool
checkBCLM = uncurry checkBCLMCurried

public export
checkSignedBCLM : (BCLawSig, BCLawMorph) -> Bool
checkSignedBCLM = uncurry checkBCLM

public export
SignedBCLM : Type
SignedBCLM = PullbackDec {a=BCLawSig} {b=BCLawMorph} checkSignedBCLM

{- XXX compute this
  -- This is the right adjunct, which provides the product elimination rule
  -- (via the counit, which comes from applying the right adjunct to `id`).
  BCLMprodAdjR : BCLawMorph -> List BCLawMorph
  -}

--------------------------------------
--------------------------------------
---- Single-sorted Lawvere theory ----
--------------------------------------
--------------------------------------

-----------------------------------------------------------------
-----------------------------------------------------------------
---- Single-sorted Lawvere theory with generic object `Bool` ----
-----------------------------------------------------------------
-----------------------------------------------------------------

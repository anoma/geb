module LanguageDef.ADTCat

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.PolyCat

%default total

------------------------------------------------
------------------------------------------------
---- Type of terms of arbitrary finite size ----
------------------------------------------------
------------------------------------------------

----------------------------------
---- Positions and directions ----
----------------------------------

-- A position of the product term functor is the number of sub-terms.
public export
ProdTermPos : Type
ProdTermPos = Nat

-- A product term's position, which is a natural number, has that number
-- of sub-terms, so its type of directions at that position is (isomorphic to)
-- the type of natural numbers strictly less than the position.
public export
ProdTermDir : ProdTermPos -> Type
ProdTermDir = Fin

public export
ProdTermPF : PolyFunc
ProdTermPF = (ProdTermPos ** ProdTermDir)

-- A position of the coproduct term functor is the index of the sub-term.
public export
CoprodTermPos : Type
CoprodTermPos = Nat

-- Any coproduct term position has exactly one direction, which corresponds
-- to the term being injected into a coproduct term at the index given by
-- the position.
public export
CoprodTermDir : CoprodTermPos -> Type
CoprodTermDir n = Unit

public export
CoprodTermPF : PolyFunc
CoprodTermPF = (CoprodTermPos ** CoprodTermDir)

-- An ADT term is either a product term or a coproduct term.
public export
ADTTermPF : PolyFunc
ADTTermPF = pfCoproductArena ProdTermPF CoprodTermPF

public export
ADTTermPos : Type
ADTTermPos = pfPos ADTTermPF

public export
ADTTermDir : ADTTermPos -> Type
ADTTermDir = pfDir {p=ADTTermPF}

---------------------------------------------
---- Least fixed point (initial algebra) ----
---------------------------------------------

public export
TermMu : Type
TermMu = PolyFuncMu ADTTermPF

---------------------------------
---- Algebras, catamorphisms ----
---------------------------------

public export
TermAlg : Type -> Type
TermAlg = PFAlg ADTTermPF

public export
termCata : {0 a : Type} -> TermAlg a -> TermMu -> a
termCata = pfCata {p=ADTTermPF}

public export
record TermAlgRec (a : Type) where
  constructor MkTermAlg
  talgProd : List a -> a
  talgCoprod : Nat -> a -> a

public export
talgFromRec : {0 a : Type} -> TermAlgRec a -> TermAlg a
talgFromRec alg (Left len) ts = alg.talgProd $ toList $ finFToVect ts
talgFromRec alg (Right idx) t = alg.talgCoprod idx $ t ()

public export
termCataRec : {0 a : Type} -> TermAlgRec a -> TermMu -> a
termCataRec = termCata . talgFromRec

-------------------
---- Utilities ----
-------------------

public export
InProd : List TermMu -> TermMu
InProd ts = InPFM (Left $ length ts) $ index' ts

public export
InCoprod : Nat -> TermMu -> TermMu
InCoprod n t = InPFM (Right n) $ \() => t

--------------------------------------------------------------------------------
---- Explicitly recursive ADT equivalent to generalized polynomial ADT term ----
--------------------------------------------------------------------------------

public export
data RATerm : Type where
  RARecordTerm : List RATerm -> RATerm
  RASumTerm : Nat -> RATerm -> RATerm

mutual
  public export
  raTermToADTTerm : RATerm -> TermMu
  raTermToADTTerm (RARecordTerm ts) = InProd $ raTermListToADTTermList ts
  raTermToADTTerm (RASumTerm n t) = InCoprod n $ raTermToADTTerm t

  public export
  raTermListToADTTermList : List RATerm -> List TermMu
  raTermListToADTTermList [] =
    []
  raTermListToADTTermList (t :: ts) =
    raTermToADTTerm t :: raTermListToADTTermList ts

public export
termToRATermAlg : TermAlgRec RATerm
termToRATermAlg = MkTermAlg RARecordTerm RASumTerm

public export
termToRATerm : TermMu -> RATerm
termToRATerm = termCataRec termToRATermAlg

------------------------
---- More utilities ----
------------------------

public export
TermSizeAlg : TermAlgRec Nat
TermSizeAlg = MkTermAlg (foldl (+) 1) (const $ (+) 1)

public export
termSize : TermMu -> Nat
termSize = termCataRec TermSizeAlg

public export
TermDepthAlg : TermAlgRec Nat
TermDepthAlg = MkTermAlg (S . foldl max 0) (const $ (+) 1)

public export
termDepth : TermMu -> Nat
termDepth = termCataRec TermDepthAlg

public export
termShowList : List String -> String
termShowList [] = ""
termShowList [t] = t
termShowList (t :: ts@(_ :: _)) = show t ++ "," ++ termShowList ts

public export
termShowProduct : List String -> String
termShowProduct ts = "(" ++ termShowList ts ++ ")"

public export
termShowCoproduct : Nat -> String -> String
termShowCoproduct n t = "[" ++ show n ++ ":" ++ t ++ "]"

public export
TermShowAlg : TermAlgRec String
TermShowAlg = MkTermAlg termShowProduct termShowCoproduct

public export
Show TermMu where
  show = termCataRec TermShowAlg

-------------------------------------------
-------------------------------------------
---- Inductive definition of term type ----
-------------------------------------------
-------------------------------------------

----------------------------------
---- Positions and directions ----
----------------------------------

public export
data SubstTermPos : Type where
  STPosLeaf : SubstTermPos
  STPosLeft : SubstTermPos
  STPosRight : SubstTermPos
  STPosPair : SubstTermPos

public export
data SubstTermDir : SubstTermPos -> Type where
  STDirL : SubstTermDir STPosLeft
  STDirR : SubstTermDir STPosRight
  STDirFst : SubstTermDir STPosPair
  STDirSnd : SubstTermDir STPosPair

public export
SubstTermPF : PolyFunc
SubstTermPF = (SubstTermPos ** SubstTermDir)

---------------------------------------------
---- Least fixed point (initial algebra) ----
---------------------------------------------

public export
STMu : Type
STMu = PolyFuncMu SubstTermPF

---------------------------------
---- Algebras, catamorphisms ----
---------------------------------

public export
STAlg : Type -> Type
STAlg = PFAlg SubstTermPF

public export
stCata : {0 a : Type} -> STAlg a -> STMu -> a
stCata = pfCata {p=SubstTermPF}

-------------------
---- Utilities ----
-------------------

public export
InSTUnit : STMu
InSTUnit = InPFM STPosLeaf $ \d => case d of _ impossible

public export
InSTLeft : STMu -> STMu
InSTLeft x = InPFM STPosLeft $ \d => case d of STDirL => x

public export
InSTRight : STMu -> STMu
InSTRight y = InPFM STPosRight $ \d => case d of STDirR => y

public export
InSTPair : STMu -> STMu -> STMu
InSTPair x y = InPFM STPosPair $ \d => case d of
  STDirFst => x
  STDirSnd => y

public export
STSizeAlg : STAlg Nat
STSizeAlg STPosLeaf dir = 0
STSizeAlg STPosLeft dir = 1 + dir STDirL
STSizeAlg STPosRight dir = 1 + dir STDirR
STSizeAlg STPosPair dir = 1 + dir STDirFst + dir STDirSnd

public export
stSize : STMu -> Nat
stSize = stCata STSizeAlg

public export
STDepthAlg : STAlg Nat
STDepthAlg STPosLeaf dir = 0
STDepthAlg STPosLeft dir = 1 + dir STDirL
STDepthAlg STPosRight dir = 1 + dir STDirR
STDepthAlg STPosPair dir = smax (dir STDirFst) (dir STDirSnd)

public export
stDepth : STMu -> Nat
stDepth = stCata STDepthAlg

public export
STShowAlg : STAlg String
STShowAlg STPosLeaf dir = "!"
STShowAlg STPosLeft dir = "< [" ++ dir STDirL ++ "]"
STShowAlg STPosRight dir = "> [" ++ dir STDirR ++ "]"
STShowAlg STPosPair dir = "(" ++ dir STDirFst ++ ", " ++ dir STDirSnd ++ ")"

public export
Show STMu where
  show = stCata STShowAlg

---------------------
---- Refinements ----
---------------------

public export
STEitherAlg : Type -> Type -> Type
STEitherAlg = STAlg .* Either

public export
STRefinementAlg : Type
STRefinementAlg = STEitherAlg Unit Unit

public export
RefinedST : (0 _ : DecPred STMu) -> Type
RefinedST = Refinement {a=STMu}

public export
AlgRefinedST : STRefinementAlg -> Type
AlgRefinedST alg = RefinedST (isRight . stCata alg)

------------------------
---- Dependent fold ----
------------------------

-----------------------------------------------------------------
-----------------------------------------------------------------
---- Inductive definition of substitutive polynomial objects ----
-----------------------------------------------------------------
-----------------------------------------------------------------

----------------------------------
---- Positions and directions ----
----------------------------------

public export
data SubstObjPos : Type where
  SOPos0 : SubstObjPos -- Initial object
  SOPos1 : SubstObjPos -- Terminal object
  SOPosC : SubstObjPos -- Coproduct
  SOPosP : SubstObjPos -- Product

public export
data SubstObjDir : SubstObjPos -> Type where
  SODirL : SubstObjDir SOPosC -- left object of coproduct
  SODirR : SubstObjDir SOPosC -- right object of coproduct
  SODir1 : SubstObjDir SOPosP -- first object of product
  SODir2 : SubstObjDir SOPosP -- second object of product

public export
SubstObjPF : PolyFunc
SubstObjPF = (SubstObjPos ** SubstObjDir)

----------------------------------------------------
---- Least fixed point, algebras, catamorphisms ----
----------------------------------------------------

public export
SOMu : Type
SOMu = PolyFuncMu SubstObjPF

public export
SOAlg : Type -> Type
SOAlg = PFAlg SubstObjPF

public export
soCata : {0 a : Type} -> SOAlg a -> SOMu -> a
soCata = pfCata {p=SubstObjPF}

-------------------
---- Utilities ----
-------------------

public export
InSO0 : SOMu
InSO0 = InPFM SOPos0 $ \d => case d of _ impossible

public export
InSO1 : SOMu
InSO1 = InPFM SOPos1 $ \d => case d of _ impossible

public export
InSOC : SOMu -> SOMu -> SOMu
InSOC x y = InPFM SOPosC $ \d => case d of
  SODirL => x
  SODirR => y

public export
InSOP : SOMu -> SOMu -> SOMu
InSOP x y = InPFM SOPosP $ \d => case d of
  SODir1 => x
  SODir2 => y

public export
SOSizeAlg : SOAlg Nat
SOSizeAlg SOPos0 dir = 1
SOSizeAlg SOPos1 dir = 1
SOSizeAlg SOPosC dir = 1 + dir SODirL + dir SODirR
SOSizeAlg SOPosP dir = 1 + dir SODir1 + dir SODir2

public export
soSize : SOMu -> Nat
soSize = soCata SOSizeAlg

public export
SODepthAlg : SOAlg Nat
SODepthAlg SOPos0 dir = 0
SODepthAlg SOPos1 dir = 0
SODepthAlg SOPosC dir = smax (dir SODirL) (dir SODirR)
SODepthAlg SOPosP dir = smax (dir SODir1) (dir SODir2)

public export
soDepth : SOMu -> Nat
soDepth = soCata SODepthAlg

public export
SOShowAlg : SOAlg String
SOShowAlg SOPos0 dir = "0"
SOShowAlg SOPos1 dir = "1"
SOShowAlg SOPosC dir = "[" ++ dir SODirL ++ "|" ++ dir SODirR ++ "]"
SOShowAlg SOPosP dir = "(" ++ dir SODir1 ++ "," ++ dir SODir2 ++ ")"

public export
Show SOMu where
  show = soCata SOShowAlg

-----------------------------------------------------
---- Term representation of substitutive objects ----
-----------------------------------------------------

public export
AsSubstObjAlg :
  PFParamAlg SubstTermPF (SubstObjPos, SOMu -> Maybe SOMu) (Maybe SOMu)
AsSubstObjAlg STPosLeaf dir (i, cont) = ?IsSubstObj_alg_hole_0
AsSubstObjAlg STPosLeft dir (i, cont) = ?IsSubstObj_alg_hole_1
AsSubstObjAlg STPosRight dir (i, cont) = ?IsSubstObj_alg_hole_2
AsSubstObjAlg STPosPair dir (i, cont) = ?IsSubstObj_alg_hole_3

public export
asSubstObj : STMu -> Maybe SOMu
asSubstObj = pfParamCata AsSubstObjAlg (SOPos0, const Nothing)

public export
isSubstObj : STMu -> Bool
isSubstObj = isJust . asSubstObj

public export
SubstObjTerm : Type
SubstObjTerm = RefinedST isSubstObj

-------------------------------------------------------------------
-------------------------------------------------------------------
---- Inductive definition of substitutive polynomial morphisms ----
-------------------------------------------------------------------
-------------------------------------------------------------------

-----------------------------------------------------
---- Positions and directions of unrefined terms ----
-----------------------------------------------------

public export
data SubstMorphPos : Type where
  SMPosId : SOMu -> SubstMorphPos
  SMPosInit : SOMu -> SubstMorphPos -- from initial
  SMPosTerm : SOMu -> SubstMorphPos -- to terminal
  SMPosL : SOMu -> SubstMorphPos -- left injection
  SMPosR : SOMu -> SubstMorphPos -- right injection
  SMPosCase : SubstMorphPos
  SMPosPair : SubstMorphPos
  SMPos1 : SOMu -> SubstMorphPos -- first projection
  SMPos2 : SOMu -> SubstMorphPos -- second projection
  SMPosDistrib : SubstMorphPos

public export
Zero : Type
Zero = Void

public export
One : Type
One = Unit

public export
Two : Type
Two = Either Unit Unit

-- The directions of a `SubstMorphPos` indicate the number of input
-- morphisms required to construct a morphism of the type corresponding
-- to the position.
public export
SubstMorphDir : SubstMorphPos -> Type
SubstMorphDir (SMPosId x) = Zero
SubstMorphDir (SMPosInit x) = Zero
SubstMorphDir (SMPosTerm x) = Zero
SubstMorphDir (SMPosL x) = One
SubstMorphDir (SMPosR x) = One
SubstMorphDir SMPosCase = Two
SubstMorphDir SMPosPair = Two
SubstMorphDir (SMPos1 x) = One
SubstMorphDir (SMPos2 x) = One
SubstMorphDir SMPosDistrib = One

public export
SubstMorphF : PolyFunc
SubstMorphF = (SubstMorphPos ** SubstMorphDir)

public export
SubstMorphFree : PolyFunc
SubstMorphFree = PolyFuncFreeM SubstMorphF

-------------------------
---- Typed morphisms ----
-------------------------

public export
SubstMorphSig : Type
SubstMorphSig = (SOMu, SOMu)

public export
SubstMorphPosDep : SubstMorphSig -> SubstMorphPos -> Type
SubstMorphPosDep sig pos = ?SubstMorphPosDep_hole

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Inductive definition of substitutive polynomial endofunctors ----
----------------------------------------------------------------------
----------------------------------------------------------------------

----------------------------------
---- Positions and directions ----
----------------------------------

-- Extensions to the positions of endofunctors beyond those of objects,
-- all of which it shares (since the category of endofunctors also has
-- all the universal properties of the the `STMu` category).
public export
data SubstEFPosExt : Type where
  SEFPosExtI : SubstEFPosExt -- identity endofunctor
  SEFPosExtPar : SubstEFPosExt -- parallel product

public export
data SubstEFDirExt : SubstEFPosExt -> Type where
  -- Although the identity endofunctor has one position, the position
  -- corresponding to the identity of the endofunctor which _generates_
  -- endofunctors has no positions, because there is just one identity
  -- functor -- the constructor which generates the identity endofunctor does
  -- not take any endofunctors as parameters
  SEFDirExtPar1 : SubstEFDirExt SEFPosExtPar
    -- first component of parallel product
  SEFDirExtPar2 : SubstEFDirExt SEFPosExtPar
    -- second component of parallel product

public export
SubstEFExt : PolyFunc
SubstEFExt = (SubstEFPosExt ** SubstEFDirExt)

public export
SubstEFPF : PolyFunc
SubstEFPF = pfCoproductArena SubstObjPF SubstEFExt

public export
SubstEFPos : Type
SubstEFPos = pfPos SubstEFPF

public export
SubstEFDir : SubstEFPos -> Type
SubstEFDir = pfDir {p=SubstEFPF}

public export
SEFPos0 : SubstEFPos
SEFPos0 = Left SOPos0

public export
SEFPos1 : SubstEFPos
SEFPos1 = Left SOPos1

public export
SEFPosC : SubstEFPos
SEFPosC = Left SOPosC

public export
SEFPosP : SubstEFPos
SEFPosP = Left SOPosP

public export
SEFPosI : SubstEFPos
SEFPosI = Right SEFPosExtI

public export
SEFPosPar : SubstEFPos
SEFPosPar = Right SEFPosExtPar

----------------------------------------------------
---- Least fixed point, algebras, catamorphisms ----
----------------------------------------------------

public export
SEFMuExt : Type
SEFMuExt = PolyFuncMu SubstEFExt

public export
SEFMu : Type
SEFMu = PolyFuncMu SubstEFPF

public export
SEFAlg : Type -> Type
SEFAlg = PFAlg SubstEFPF

public export
SEFAlgExt : Type -> Type
SEFAlgExt = PFAlg SubstEFExt

public export
sefCataExt : {0 a : Type} -> SEFAlgExt a -> SEFMuExt -> a
sefCataExt = pfCata {p=SubstEFExt}

public export
sefCata : {0 a : Type} -> SEFAlg a -> SEFMu -> a
sefCata = pfCata {p=SubstEFPF}

-------------------
---- Utilities ----
-------------------

public export
InSEFL : (i : SubstObjPos) -> (SubstObjDir i -> SEFMu) -> SEFMu
InSEFL i = InPFM (Left i)

public export
InSEFR : (i : SubstEFPosExt) -> (SubstEFDirExt i -> SEFMu) -> SEFMu
InSEFR i = InPFM (Right i)

public export
InSEFO : SOMu -> SEFMu
InSEFO = soCata InSEFL

public export
InSEFExt : SEFMuExt -> SEFMu
InSEFExt = sefCataExt InSEFR

public export
InSEF0 : SEFMu
InSEF0 = InSEFO InSO0

public export
InSEF1 : SEFMu
InSEF1 = InSEFO InSO1

public export
InSEFC : SOMu -> SOMu -> SEFMu
InSEFC = InSEFO .* InSOC

public export
InSEFP : SOMu -> SOMu -> SEFMu
InSEFP = InSEFO .* InSOP

public export
InSEFI : SEFMu
InSEFI = InPFM SEFPosI $ \d => case d of _ impossible

public export
InSEFPar : SEFMu -> SEFMu -> SEFMu
InSEFPar x y = InPFM SEFPosPar $ \d => case d of
  SEFDirExtPar1 => x
  SEFDirExtPar2 => y

public export
SEFSizeAlgExt : SEFAlgExt Nat
SEFSizeAlgExt SEFPosExtI dir = 1
SEFSizeAlgExt SEFPosExtPar dir = 1 + dir SEFDirExtPar1 + dir SEFDirExtPar2

public export
SEFSizeAlg : SEFAlg Nat
SEFSizeAlg = PFCoprodAlg {p=SubstObjPF} {q=SubstEFExt} SOSizeAlg SEFSizeAlgExt

public export
sefSize : SEFMu -> Nat
sefSize = sefCata SEFSizeAlg

public export
SEFDepthAlgExt : SEFAlgExt Nat
SEFDepthAlgExt SEFPosExtI dir = 0
SEFDepthAlgExt SEFPosExtPar dir = smax (dir SEFDirExtPar1) (dir SEFDirExtPar2)

public export
SEFDepthAlg : SEFAlg Nat
SEFDepthAlg =
  PFCoprodAlg {p=SubstObjPF} {q=SubstEFExt} SODepthAlg SEFDepthAlgExt

public export
sefDepth : SEFMu -> Nat
sefDepth = sefCata SEFDepthAlg

public export
SEFShowAlgObj : SOAlg String
SEFShowAlgObj pos dir = "!" ++ SOShowAlg pos dir

public export
SEFShowAlgExt : SEFAlgExt String
SEFShowAlgExt SEFPosExtI dir = "{id}"
SEFShowAlgExt SEFPosExtPar dir =
  "<" ++ dir SEFDirExtPar1 ++ "x" ++ dir SEFDirExtPar2 ++ ">"

public export
SEFShowAlg : SEFAlg String
SEFShowAlg = PFCoprodAlg {p=SubstObjPF} {q=SubstEFExt} SOShowAlg SEFShowAlgExt

public export
Show SEFMu where
  show = sefCata SEFShowAlg

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Inductive definition of substitutive polynomial endofunctors ----
----                 (Not using PolyFunc)                         ----
----------------------------------------------------------------------
----------------------------------------------------------------------

--------------------------------------------------------------------------
---- Functor which generates polynomial functors (not using PolyFunc) ----
--------------------------------------------------------------------------

infixr 8 $$+
infixr 9 $$*

public export
data PolyF : Type -> Type where
  -- Identity
  PFI : PolyF carrier

  -- Initial
  PF0 : PolyF carrier

  -- Terminal
  PF1 : PolyF carrier

  -- Coproduct
  ($$+) : carrier -> carrier -> PolyF carrier

  -- Product
  ($$*) : carrier -> carrier -> PolyF carrier

public export
Functor PolyF where
  map m PFI = PFI
  map m PF0 = PF0
  map m PF1 = PF1
  map m (p $$+ q) = m p $$+ m q
  map m (p $$* q) = m p $$* m q

-----------------------------------------------------------------------
---- Polynomial functors as least fixed point of generator functor ----
-----------------------------------------------------------------------

public export
data PolyMu : Type where
  InPCom : PolyF PolyMu -> PolyMu

public export
data PolyNu : Type where
  InPLabel : Inf (PolyF PolyNu) -> PolyNu

infixr 8 $+
infixr 9 $*

public export
PolyI : PolyMu
PolyI = InPCom PFI

public export
Poly0 : PolyMu
Poly0 = InPCom PF0

public export
Poly1 : PolyMu
Poly1 = InPCom PF1

public export
($+) : PolyMu -> PolyMu -> PolyMu
($+) = InPCom .* ($$+)

public export
($*) : PolyMu -> PolyMu -> PolyMu
($*) = InPCom .* ($$*)

----------------------------------
---- Algebra and catamorphism ----
----------------------------------

public export
MetaPolyAlg : Type -> Type
MetaPolyAlg x = PolyF x -> x

public export
metaPolyCata : MetaPolyAlg x -> PolyMu -> x
metaPolyCata alg (InPCom p) = alg $ case p of
  PFI => PFI
  PF0 => PF0
  PF1 => PF1
  p $$+ q => metaPolyCata alg p $$+ metaPolyCata alg q
  p $$* q => metaPolyCata alg p $$* metaPolyCata alg q

public export
metaPolyCataCPS : MetaPolyAlg x -> PolyMu -> x
metaPolyCataCPS alg = metaPolyFold id where
  mutual
    metaPolyCataCont : (x -> x -> PolyF x) ->
      (x -> x) -> PolyMu -> PolyMu -> x
    metaPolyCataCont op cont p q =
      metaPolyFold
        (\p' => metaPolyFold (\q' => cont $ alg $ op p' q') q) p

    metaPolyFold : (x -> x) -> PolyMu -> x
    metaPolyFold cont (InPCom p) = case p of
      PFI => cont (alg PFI)
      PF0 => cont (alg PF0)
      PF1 => cont (alg PF1)
      p $$+ q => metaPolyCataCont ($$+) cont p q
      p $$* q => metaPolyCataCont ($$*) cont p q

-----------------------------------
---- Coalgebra and anamorphism ----
-----------------------------------

public export
MetaPolyCoalg : Type -> Type
MetaPolyCoalg x = x -> PolyF x

public export
metaPolyAna : MetaPolyCoalg x -> x -> Inf PolyNu
metaPolyAna coalg t = case coalg t of
  PFI => InPLabel PFI
  PF0 => InPLabel PF0
  PF1 => InPLabel PF1
  p $$+ q => InPLabel $ metaPolyAna coalg p $$+ metaPolyAna coalg q
  p $$* q => InPLabel $ metaPolyAna coalg p $$* metaPolyAna coalg q

public export
metaPolyAnaCPS : MetaPolyCoalg x -> x -> Inf PolyNu
metaPolyAnaCPS coalg = metaPolyUnfold id where
  mutual
    metaPolyAnaCont : (PolyNu -> PolyNu -> PolyF PolyNu) ->
      (PolyNu -> PolyNu) -> x -> x -> PolyNu
    metaPolyAnaCont op cont x y =
      metaPolyUnfold
        (\x' => metaPolyUnfold (\y' => cont $ InPLabel $ op x' y') y) x

    metaPolyUnfold : (PolyNu -> PolyNu) -> x -> Inf PolyNu
    metaPolyUnfold cont t = case coalg t of
      PFI => cont (InPLabel PFI)
      PF0 => cont (InPLabel PF0)
      PF1 => cont (InPLabel PF1)
      p $$+ q => metaPolyAnaCont ($$+) cont p q
      p $$* q => metaPolyAnaCont ($$*) cont p q

------------------------------------------
---- Derived variants of catamorphism ----
------------------------------------------

-- Catamorphism which passes not only the output of the previous
-- induction steps but also the original `PolyMu` to the algebra.
public export
MetaPolyArgAlg : Type -> Type
MetaPolyArgAlg x = PolyF (PolyMu, x) -> x

public export
MetaPolyAlgFromArg : {0 x : Type} -> MetaPolyArgAlg x -> MetaPolyAlg (PolyMu, x)
MetaPolyAlgFromArg alg t = (InPCom $ map fst t, alg t)

public export
metaPolyArgCata : MetaPolyArgAlg x -> PolyMu -> x
metaPolyArgCata alg t = snd $ metaPolyCata (MetaPolyAlgFromArg alg) t

-- Catamorphism on a pair of `PolyMu`s using the product-hom adjunction.
public export
MetaPolyPairAdjAlg : Type -> Type
MetaPolyPairAdjAlg x = MetaPolyAlg (PolyMu -> x)

public export
metaPolyPairAdjCata : MetaPolyPairAdjAlg x -> PolyMu -> PolyMu -> x
metaPolyPairAdjCata = metaPolyCata

-- Catamorphism on a pair of `PolyMu`s using the product-hom adjunction,
-- where the original first `PolyMu` is also available to the algebra.
public export
MetaPolyPairAdjArgAlg : Type -> Type
MetaPolyPairAdjArgAlg x = PolyF (PolyMu, PolyMu -> x) -> PolyMu -> x

public export
metaPolyPairAdjArgCata : MetaPolyPairAdjArgAlg x -> PolyMu -> PolyMu -> x
metaPolyPairAdjArgCata = metaPolyArgCata

-- Catamorphism on a pair of `PolyMu`s using all combinations of cases.
public export
MetaPolyPairAlg : Type -> Type
MetaPolyPairAlg x = PolyF (PolyMu -> x) -> PolyF PolyMu -> x

public export
MetaPolyPairAlgToAdj : {0 x : Type} -> MetaPolyPairAlg x -> MetaPolyPairAdjAlg x
MetaPolyPairAlgToAdj alg f (InPCom p) = alg f p

public export
metaPolyPairCata : MetaPolyPairAlg x -> PolyMu -> PolyMu -> x
metaPolyPairCata alg = metaPolyPairAdjCata (MetaPolyPairAlgToAdj alg)

-------------------
---- Utilities ----
-------------------

public export
PolySizeAlg : MetaPolyAlg Nat
PolySizeAlg PFI = 1
PolySizeAlg PF0 = 1
PolySizeAlg PF1 = 1
PolySizeAlg (p $$+ q) = p + q
PolySizeAlg (p $$* q) = p + q

public export
polySize : PolyMu -> Nat
polySize = metaPolyCata PolySizeAlg

public export
PolyDepthAlg : MetaPolyAlg Nat
PolyDepthAlg PFI = 0
PolyDepthAlg PF0 = 0
PolyDepthAlg PF1 = 0
PolyDepthAlg (p $$+ q) = smax p q
PolyDepthAlg (p $$* q) = smax p q

public export
polyDepth : PolyMu -> Nat
polyDepth = metaPolyCata PolyDepthAlg

-- The cardinality of the type that would result from applying
-- the given polynomial to a type of the given cardinality.
public export
PolyCardAlg : Nat -> MetaPolyAlg Nat
PolyCardAlg n PFI = n
PolyCardAlg n PF0 = 0
PolyCardAlg n PF1 = 1
PolyCardAlg n (p $$+ q) = p + q
PolyCardAlg n (p $$* q) = p * q

public export
polyCard : Nat -> PolyMu -> Nat
polyCard = metaPolyCata . PolyCardAlg

public export
polyTCard : PolyMu -> Nat
polyTCard = polyCard 0

--------------------------------------------
---- Displaying polynomial endofunctors ----
--------------------------------------------

public export
PolyShowAlg : MetaPolyAlg String
PolyShowAlg PFI = "id"
PolyShowAlg PF0 = "0"
PolyShowAlg PF1 = "1"
PolyShowAlg (x $$+ y) = "(" ++ x ++ " + " ++ y ++ ")"
PolyShowAlg (x $$* y) = "[" ++ x ++ " * " ++ y ++ "]"

public export
Show PolyMu where
  show = metaPolyCata PolyShowAlg

---------------------------------------------
---- Equality on polynomial endofunctors ----
---------------------------------------------

public export
PolyMuEqAlg : MetaPolyPairAlg Bool
PolyMuEqAlg PFI PFI = True
PolyMuEqAlg PFI _ = False
PolyMuEqAlg PF0 PF0 = True
PolyMuEqAlg PF0 _ = False
PolyMuEqAlg PF1 PF1 = True
PolyMuEqAlg PF1 _ = False
PolyMuEqAlg (p $$+ q) (r $$+ s) = p r && q s
PolyMuEqAlg (p $$+ q) _ = False
PolyMuEqAlg (p $$* q) (r $$* s) = p r && q s
PolyMuEqAlg (p $$* q) _ = False

public export
Eq PolyMu where
  (==) = metaPolyPairCata PolyMuEqAlg

--------------------------------------------------
---- Normalization of polynomial endofunctors ----
--------------------------------------------------

public export
PolyRemoveZeroAlg : MetaPolyAlg PolyMu
PolyRemoveZeroAlg PFI = PolyI
PolyRemoveZeroAlg PF0 = Poly0
PolyRemoveZeroAlg PF1 = Poly1
PolyRemoveZeroAlg (p $$+ q) = case p of
  InPCom p' => case p' of
    PF0 => q
    _ => case q of
      InPCom q' => case q' of
        PF0 => p
        _ => p $+ q
PolyRemoveZeroAlg (p $$* q) = case p of
  InPCom p' => case p' of
    PF0 => Poly0
    _ => case q of
      InPCom q' => case q' of
        PF0 => Poly0
        _ => p $* q

public export
polyRemoveZero : PolyMu -> PolyMu
polyRemoveZero = metaPolyCata PolyRemoveZeroAlg

public export
PolyRemoveOneAlg : MetaPolyAlg PolyMu
PolyRemoveOneAlg PFI = PolyI
PolyRemoveOneAlg PF0 = Poly0
PolyRemoveOneAlg PF1 = Poly1
PolyRemoveOneAlg (p $$+ q) = p $+ q
PolyRemoveOneAlg (p $$* q) = case p of
  InPCom p' => case p' of
    PF1 => q
    _ => case q of
      InPCom q' => case q' of
        PF1 => p
        _ => p $* q

public export
polyRemoveOne : PolyMu -> PolyMu
polyRemoveOne = metaPolyCata PolyRemoveOneAlg

---------------------------------------------------------------
---- Composition of polynomial endofunctors (substitution) ----
---------------------------------------------------------------

public export
PolyComposeAlg : MetaPolyPairAdjAlg PolyMu
PolyComposeAlg PFI q = q
PolyComposeAlg PF0 _ = Poly0
PolyComposeAlg PF1 _ = Poly1
PolyComposeAlg (p $$+ q) r = p r $+ q r
PolyComposeAlg (p $$* q) r = p r $* q r

infixr 2 $.
public export
($.) : PolyMu -> PolyMu -> PolyMu
($.) = metaPolyPairAdjCata PolyComposeAlg

-----------------------------------------------------
---- Multiplication by a constant (via addition) ----
-----------------------------------------------------

infix 10 $:*
public export
($:*) : Nat -> PolyMu -> PolyMu
n $:* p = foldrNatNoUnit (($+) p) Poly0 p n

---------------------------------------
---- Multiplicative exponentiation ----
---------------------------------------

infix 10 $*^
public export
($*^) : PolyMu -> Nat -> PolyMu
p $*^ n = foldrNatNoUnit (($*) p) Poly1 p n

--------------------------------------------------
---- Compositional exponentiation (iteration) ----
--------------------------------------------------

infix 10 $.^
public export
($.^) : PolyMu -> Nat -> PolyMu
p $.^ n = foldrNatNoUnit (($.) p) PolyI p n

---------------------------------------
---- Composition with zero and one ----
---------------------------------------

public export
polyAppZero : PolyMu -> PolyMu
polyAppZero p = polyRemoveZero (p $. Poly0)

public export
polyAppOne : PolyMu -> PolyMu
polyAppOne p = polyRemoveOne (p $. Poly1)

-------------------------------------------------
---- Conversion to and from algebraic format ----
-------------------------------------------------

public export
CountOnesAlg : MetaPolyAlg Nat
CountOnesAlg PFI = 0
CountOnesAlg PF0 = 0
CountOnesAlg PF1 = 1
CountOnesAlg (p $$+ q) = p + q
CountOnesAlg (p $$* q) = p + q

public export
countOnes : PolyMu -> Nat
countOnes = metaPolyCata CountOnesAlg

public export
CountIdsAlg : MetaPolyAlg Nat
CountIdsAlg PFI = 1
CountIdsAlg PF0 = 0
CountIdsAlg PF1 = 0
CountIdsAlg (p $$+ q) = p + q
CountIdsAlg (p $$* q) = p + q

public export
countIds : PolyMu -> Nat
countIds = metaPolyCata CountIdsAlg

public export
ToPolyShapeAlg : MetaPolyAlg PolyShape
ToPolyShapeAlg PFI = idPolyShape
ToPolyShapeAlg PF0 = initialPolyShape
ToPolyShapeAlg PF1 = terminalPolyShape
ToPolyShapeAlg (p $$+ q) = addPolyShape p q
ToPolyShapeAlg (p $$* q) = mulPolyShape p q

public export
toPolyShape : PolyMu -> PolyShape
toPolyShape = metaPolyCata ToPolyShapeAlg

public export
showPolyShape : PolyMu -> String
showPolyShape = show . toPolyShape

public export
polyPosShow : PolyMu -> String
polyPosShow = psPosShow . toPolyShape

public export
polyNPos : PolyMu -> Nat
polyNPos = sumPTCoeff . toPolyShape

-- Create a polynomial from a list of (power, coefficient) pairs.
public export
fromPolyShapeAcc : PolyShape -> PolyMu -> PolyMu
fromPolyShapeAcc [] q = q
fromPolyShapeAcc ((p, c) :: l) q =
  fromPolyShapeAcc l (c $:* (PolyI $*^ p) $+ q)

public export
fromPolyShape : PolyShape -> PolyMu
fromPolyShape l = fromPolyShapeAcc l Poly0

public export
polyDistrib : PolyMu -> PolyMu
polyDistrib = fromPolyShape . toPolyShape

-----------------------------------------------------------------------------
---- Interpretation of polynomial functors as natural-number polymomials ----
-----------------------------------------------------------------------------

public export
MetaPolyFNatAlg : MetaPolyAlg (Nat -> Nat)
MetaPolyFNatAlg PFI = id
MetaPolyFNatAlg PF0 = const 0
MetaPolyFNatAlg PF1 = const 1
MetaPolyFNatAlg (p $$+ q) = \n => p n + q n
MetaPolyFNatAlg (p $$* q) = \n => p n * q n

public export
MetaPolyFNat : PolyMu -> Nat -> Nat
MetaPolyFNat = metaPolyCata MetaPolyFNatAlg

----------------------------------------------------------
---- Exponentiation (hom-objects) of polynomial types ----
----------------------------------------------------------

public export
PolyHomObjAlg : MetaPolyPairAdjAlg PolyMu
-- id -> r == r . (id + 1) (see formula 4.27 in _Polynomial Functors: A General
-- Theory of Interaction_)
PolyHomObjAlg PFI r = r $. (PolyI $+ Poly1)
-- 0 -> x == 1
PolyHomObjAlg PF0 _ = Poly1
-- 1 -> x == x
PolyHomObjAlg PF1 q = q
-- (p + q) -> r == (p -> r) * (q -> r)
PolyHomObjAlg (p $$+ q) r = p r $* q r
-- (p * q) -> r == p -> q -> r
PolyHomObjAlg (p $$* q) r = p $ q r

public export
PolyHomObj : PolyMu -> PolyMu -> PolyMu
PolyHomObj = metaPolyPairAdjCata PolyHomObjAlg

public export
PolyExp : PolyMu -> PolyMu -> PolyMu
PolyExp = flip PolyHomObj

--------------------------------------------------------
---- Position/direction view of polynomial functors ----
--------------------------------------------------------

-- An alternate name since `PolyFunc` is close to `PolyMu`.
public export
PFArena : Type
PFArena = PolyFunc

-- The arena of an endofunctor.
public export
PolyArenaAlg : MetaPolyAlg PFArena
PolyArenaAlg PFI = PFIdentityArena
PolyArenaAlg PF0 = PFInitialArena
PolyArenaAlg PF1 = PFTerminalArena
PolyArenaAlg (p $$+ q) = pfCoproductArena p q
PolyArenaAlg (p $$* q) = pfProductArena p q

public export
PolyArena : PolyMu -> PFArena
PolyArena = metaPolyCata PolyArenaAlg

-- The "positions" of an endofunctor, in the arena viewpoint.
public export
PolyPos : PolyMu -> Type
PolyPos = pfPos . PolyArena

-- The "directions" of a given position, in the arena viewpoint.
public export
PolyPosDir : (p : PolyMu) -> PolyPos p -> Type
PolyPosDir p = pfDir {p=(PolyArena p)}

-- Any direction of an endofunctor.
public export
PolyDir : PolyMu -> Type
PolyDir p = DPair (PolyPos p) (PolyPosDir p)

-- The zero-power positions -- that is, the ones with no directions.
public export
PolyZeroPosAlg : MetaPolyAlg Type
PolyZeroPosAlg PFI = Void
PolyZeroPosAlg PF0 = Void
PolyZeroPosAlg PF1 = Unit
PolyZeroPosAlg (p $$+ q) = Either p q
PolyZeroPosAlg (p $$* q) = Pair p q

public export
PolyZeroPos : PolyMu -> Type
PolyZeroPos = metaPolyCata PolyZeroPosAlg

---------------------------------
---- Natural transformations ----
---------------------------------

public export
PolyMuNTAlg : MetaPolyPairAdjArgAlg Type
PolyMuNTAlg PFI q = PolyPos q
PolyMuNTAlg PF0 _ = ()
PolyMuNTAlg PF1 q = PolyZeroPos q
PolyMuNTAlg ((_, p) $$+ (_, q)) r = Pair (p r) (q r)
PolyMuNTAlg ((_, p) $$* (q, _)) r = ?PolyMuNTAlg_product_domain_hole

public export
PolyMuNT : PolyMu -> PolyMu -> Type
PolyMuNT = metaPolyPairAdjArgCata PolyMuNTAlg

----------------------------------------
---- Polynomial monads and comonads ----
----------------------------------------

public export
record PolyMonad where
  constructor MkPolyMonad
  pmFunctor : PolyMu
  pmUnit : PolyMuNT PolyI pmFunctor
  pmMul : PolyMuNT (pmFunctor $.^ 2) pmFunctor

public export
record PolyComonad where
  constructor MkPolyComonad
  pmFunctor : PolyMu
  pmEraser : PolyMuNT pmFunctor PolyI
  pmDuplicator : PolyMuNT pmFunctor (pmFunctor $.^ 2)

------------------------------------------------------------------------
---- Interpretation of polynomial functors as metalanguage functors ----
------------------------------------------------------------------------

public export
MetaPolyMetaFAlg : MetaPolyAlg (Type -> Type)
MetaPolyMetaFAlg PFI = id
MetaPolyMetaFAlg PF0 = const Void
MetaPolyMetaFAlg PF1 = const Unit
MetaPolyMetaFAlg (p $$+ q) = CoproductF p q
MetaPolyMetaFAlg (p $$* q) = ProductF p q

public export
MetaPolyFMetaF : PolyMu -> Type -> Type
MetaPolyFMetaF = metaPolyCata MetaPolyMetaFAlg

public export
ConstComponent : PolyMu -> Type
ConstComponent p = MetaPolyFMetaF (polyAppZero p) Void

public export
PositionType : PolyMu -> Type
PositionType p = MetaPolyFMetaF (polyAppOne p) Unit

---------------------------------------------------
---- The free monad in the polynomial category ----
---------------------------------------------------

public export
MetaPolyFreeM : PolyMu -> (0 _ : Type) -> Type
MetaPolyFreeM (InPCom p) = FreeM (MetaPolyFMetaF $ InPCom p)

public export
MetaPolyMu : PolyMu -> Type
MetaPolyMu p = MetaPolyFreeM p Void

-----------------------------------
-----------------------------------
---- Geb terms (S-expressions) ----
-----------------------------------
-----------------------------------

-----------------------------
---- Nameless definition ----
-----------------------------

public export
MaybeSqNPos : Nat
MaybeSqNPos = 4

public export
MaybeSqPos : Type
MaybeSqPos = Fin MaybeSqNPos

public export
MaybeSqUnit : MaybeSqPos
MaybeSqUnit = FZ

public export
MaybeSqLeft : MaybeSqPos
MaybeSqLeft = finS MaybeSqUnit

public export
MaybeSqRight : MaybeSqPos
MaybeSqRight = finS MaybeSqLeft

public export
MaybeSqPair : MaybeSqPos
MaybeSqPair = finS MaybeSqRight

public export
MaybeSqPosPred : Type -> Type
MaybeSqPosPred = Vect MaybeSqNPos

public export
maybeSqPosFunc : {0 a : Type} -> MaybeSqPosPred a -> MaybeSqPos -> a
maybeSqPosFunc = flip index

public export
MaybeSqNDir : MaybeSqPos -> Nat
MaybeSqNDir = maybeSqPosFunc [0, 1, 1, 2]

public export
MaybeSqDir : MaybeSqPos -> Type
MaybeSqDir = Fin . MaybeSqNDir

public export
MaybeSqArena : PFArena
MaybeSqArena = (MaybeSqPos ** MaybeSqDir)

public export
MaybeSq : Type -> Type
MaybeSq = InterpPolyFunc MaybeSqArena

public export
0 FreeMaybeSqPos : Type
FreeMaybeSqPos = PolyFuncFreeMPos MaybeSqArena

public export
0 FreeMaybeSqDir : FreeMaybeSqPos -> Type
FreeMaybeSqDir = PolyFuncFreeMDir MaybeSqArena

public export
0 FreeMaybeSqArena : PFArena
FreeMaybeSqArena = PolyFuncFreeM MaybeSqArena

public export
FreeMaybeSq : Type -> Type
FreeMaybeSq = InterpPolyFuncFreeM MaybeSqArena

public export
MuMaybeSq : Type
MuMaybeSq = PolyFuncMu MaybeSqArena

public export
CofreeMaybeSq : Type -> Type
CofreeMaybeSq = PolyFuncCofreeCMFromNuScale MaybeSqArena

public export
NuMaybeSq : Type
NuMaybeSq = PolyFuncNu MaybeSqArena

-------------------------------------
---- Definition and constructors ----
-------------------------------------

-- A functor which generates, through its initial algebra, a
-- category-theoretic analogue of an S-expression, or generic
-- term of any ADT.
--
-- This functor may be written anonymously as `1 + 2 * I + I ^ 2`.
-- That is isomorphic to `(1 + I) ^ 2`, which provides another way
-- of looking at it:  as a tree node with up to two children.

public export
data ADTTermF : Type -> Type where
  ADTUnit : {0 carrier : Type} -> ADTTermF carrier
  ADTLeft : {0 carrier : Type} -> carrier -> ADTTermF carrier
  ADTRight : {0 carrier : Type} -> carrier -> ADTTermF carrier
  ADTPair : {0 carrier : Type} -> carrier -> carrier -> ADTTermF carrier

public export
Functor ADTTermF where
  map f ADTUnit = ADTUnit
  map f (ADTLeft x) = ADTLeft (f x)
  map f (ADTRight x) = ADTRight (f x)
  map f (ADTPair x y) = ADTPair (f x) (f y)

-- The initial algebra of ADTTermF, a type whose terms are
-- category-theoretic S-expressions.  This is the only recursive
-- type definition in the core logic of Geb.
public export
data ADTTerm : Type where
  InADTT : ADTTermF ADTTerm -> ADTTerm

-- Convenience constructors for `ADTTerm`.

public export
($!) : ADTTerm
($!) = InADTT ADTUnit

prefix 10 $<
public export
($<) : ADTTerm -> ADTTerm
($<) t = InADTT (ADTLeft t)

prefix 10 $>
public export
($>) : ADTTerm -> ADTTerm
($>) t = InADTT (ADTRight t)

infixr 12 $$
public export
($$) : ADTTerm -> ADTTerm -> ADTTerm
t $$ t' = InADTT (ADTPair t t')

----------------------
---- Term algebra ----
----------------------

public export
TermAlg' : Type -> Type
TermAlg' a = ADTTermF a -> a

public export
TermEndoAlg : Type
TermEndoAlg = TermAlg' ADTTerm

----------------------------------------------------------
---- Zero-usage (compile-time-only) term catamorphism ----
----------------------------------------------------------

public export
0 termCataZeroUsage : {0 a : Type} -> (0 _ : TermAlg' a) -> (0 _ : ADTTerm) -> a
termCataZeroUsage alg (InADTT t) = alg $ case t of
  ADTUnit => ADTUnit
  ADTLeft t => ADTLeft (termCataZeroUsage alg t)
  ADTRight t => ADTRight (termCataZeroUsage alg t)
  ADTPair t t' => ADTPair (termCataZeroUsage alg t) (termCataZeroUsage alg t')

--------------------------------------
---- Compile-time term properties ----
--------------------------------------

public export
TermSizeAlg' : TermAlg' Nat
TermSizeAlg' ADTUnit = 1
TermSizeAlg' (ADTLeft t) = S t
TermSizeAlg' (ADTRight t) = S t
TermSizeAlg' (ADTPair t t') = S (t + t')

public export
0 termSize' : (0 _ : ADTTerm) -> Nat
termSize' = termCataZeroUsage TermSizeAlg'

public export
TermDepthAlg' : TermAlg' Nat
TermDepthAlg' ADTUnit = 1
TermDepthAlg' (ADTLeft t) = S t
TermDepthAlg' (ADTRight t) = S t
TermDepthAlg' (ADTPair t t') = smax t t'

public export
0 termDepth' : (0 _ : ADTTerm) -> Nat
termDepth' = termCataZeroUsage TermDepthAlg'

----------------------------------------------
---- Continuation-passing-style term fold ----
----------------------------------------------

mutual
  public export
  termFold : {0 a : Type} -> TermAlg' a -> (a -> a) -> ADTTerm -> a
  termFold alg cont (InADTT t) = case t of
    ADTUnit => cont (alg ADTUnit)
    ADTLeft l => termFold alg (cont . alg . ADTLeft) l
    ADTRight r => termFold alg (cont . alg . ADTRight) r
    ADTPair l r => termFold alg (termFoldPair alg cont r) l

  public export
  termFoldPair : {0 a : Type} -> TermAlg' a -> (a -> a) -> ADTTerm -> a -> a
  termFoldPair alg cont r l = termFold alg (cont . alg . ADTPair l) r

---------------------------------------
---- Term-processing stack machine ----
---------------------------------------

-- `TermStack` is a concrete data-structure representation of the continuation
-- function `a -> a` in `termFold`/`termFoldPair`.

public export
data TermStackElem : (0 _ : Type) -> Type where
  TSELeft : {0 a : Type} -> TermStackElem a
  TSERight : {0 a : Type} -> TermStackElem a
  TSEPairWithRightTerm : {0 a : Type} -> ADTTerm -> TermStackElem a
  TSEPairWithLeftResult : {0 a : Type} -> a -> TermStackElem a

public export
TermStack : (0 _ : Type) -> Type
TermStack a = List (TermStackElem a)

mutual
  public export
  partial
  termStackRun : {0 a : Type} ->
    TermAlg' a -> TermStack a -> ADTTerm -> a
  termStackRun alg stack (InADTT t) = case t of
    ADTUnit => termContRun alg stack (alg ADTUnit)
    ADTLeft l => termStackRun alg (TSELeft :: stack) l
    ADTRight r => termStackRun alg (TSERight :: stack) r
    ADTPair l r => termStackRun alg (TSEPairWithRightTerm r :: stack) l

  public export
  partial
  termContRun : {0 a : Type} -> TermAlg' a -> TermStack a -> a -> a
  termContRun {a} alg [] result = result
  termContRun {a} alg (elem :: stack) result = case elem of
    TSELeft => termContRun alg stack (alg $ ADTLeft result)
    TSERight => termContRun alg stack (alg $ ADTRight result)
    TSEPairWithRightTerm r =>
      termStackRun alg (TSEPairWithLeftResult result :: stack) r
    TSEPairWithLeftResult l => termContRun alg stack (alg $ ADTPair l result)

------------------------------------------
---- Tail-recursive term catamorphism ----
------------------------------------------

public export
termCata' : {0 a : Type} -> TermAlg' a -> ADTTerm -> a
termCata' alg = termFold alg id

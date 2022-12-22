module LanguageDef.ADTCat

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.PolyCat

%default total

----------------------------------------------------------------
----------------------------------------------------------------
---- Explicitly-recursive Idris ADT definition of term type ----
----------------------------------------------------------------
----------------------------------------------------------------

public export
data SubstTermRec : Type where
  STRLeaf : SubstTermRec
  STRLeft : SubstTermRec -> SubstTermRec
  STRRight : SubstTermRec -> SubstTermRec
  STRPair : SubstTermRec -> SubstTermRec -> SubstTermRec

------------------------------------------
------------------------------------------
---- PolyFunc definition of term type ----
------------------------------------------
------------------------------------------

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

public export
STFreeM : PolyFunc
STFreeM = PolyFuncFreeM SubstTermPF

---------------------------------
---- Algebras, catamorphisms ----
---------------------------------

public export
STAlg : Type -> Type
STAlg = PFAlg SubstTermPF

public export
stCata : {0 a : Type} -> STAlg a -> STMu -> a
stCata = pfCata {p=SubstTermPF}

public export
STProdAlg : Type -> Type
STProdAlg = PFProductAlg SubstTermPF SubstTermPF

public export
stProdCata : {0 a : Type} -> STProdAlg a -> STMu -> STMu -> a
stProdCata {a} = pfProductCata {a} {p=SubstTermPF} {q=SubstTermPF}

public export
STNatTrans : Type
STNatTrans = PolyNatTrans SubstTermPF SubstTermPF

public export
STFreeNatTrans : Type
STFreeNatTrans = PolyNatTrans STFreeM STFreeM

public export
STNatTransMN : Nat -> Nat -> Type
STNatTransMN = pfNatTransMN SubstTermPF SubstTermPF

public export
stPolyCata : STNatTrans -> STMu -> STMu
stPolyCata = pfPolyCata {p=SubstTermPF} {q=SubstTermPF}

public export
stFreePolyCata : STNatTrans -> STFreeNatTrans
stFreePolyCata = pfFreePolyCata {p=SubstTermPF} {q=SubstTermPF}

public export
STProductHomAlgNT : Type
STProductHomAlgNT = PFProductHomAlgNT SubstTermPF SubstTermPF SubstTermPF

public export
stProductHomCataNT : STProductHomAlgNT -> STMu -> STMu -> STMu
stProductHomCataNT =
  pfProductHomCataNT {p=SubstTermPF} {q=SubstTermPF} {r=SubstTermPF}

public export
STProductHomAlg : Type -> Type
STProductHomAlg = PFProductHomAlg SubstTermPF SubstTermPF

public export
stProductHomCata : {a : Type} -> STProductHomAlg a -> STMu -> STMu -> a
stProductHomCata = pfProductHomCata {p=SubstTermPF} {q=SubstTermPF}

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
STNumLeavesAlg : STAlg Nat
STNumLeavesAlg STPosLeaf dir = 1
STNumLeavesAlg STPosLeft dir = dir STDirL
STNumLeavesAlg STPosRight dir = dir STDirR
STNumLeavesAlg STPosPair dir = dir STDirFst + dir STDirSnd

public export
stNumLeaves : STMu -> Nat
stNumLeaves = stCata STNumLeavesAlg

public export
STNumInternalNodesAlg : STAlg Nat
STNumInternalNodesAlg STPosLeaf dir = 0
STNumInternalNodesAlg STPosLeft dir = 1 + dir STDirL
STNumInternalNodesAlg STPosRight dir = 1 + dir STDirR
STNumInternalNodesAlg STPosPair dir = 1 + dir STDirFst + dir STDirSnd

public export
stNumInternalNodes : STMu -> Nat
stNumInternalNodes = stCata STNumInternalNodesAlg

public export
STSizeAlg : STAlg Nat
STSizeAlg STPosLeaf dir = 1
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
STShowAlg STPosLeaf dir = "_"
STShowAlg STPosLeft dir = "l[" ++ dir STDirL ++ "]"
STShowAlg STPosRight dir = "r[" ++ dir STDirR ++ "]"
STShowAlg STPosPair dir = "(" ++ dir STDirFst ++ ", " ++ dir STDirSnd ++ ")"

public export
Show STMu where
  show = stCata STShowAlg

public export
STEqAlg : STProdAlg Bool
STEqAlg (STPosLeaf, STPosLeaf) d = True
STEqAlg (STPosLeaf, STPosLeft) d = False
STEqAlg (STPosLeaf, STPosRight) d = False
STEqAlg (STPosLeaf, STPosPair) d = False
STEqAlg (STPosLeft, STPosLeaf) d = False
STEqAlg (STPosLeft, STPosLeft) d = d (STDirL, STDirL)
STEqAlg (STPosLeft, STPosRight) d = False
STEqAlg (STPosLeft, STPosPair) d = False
STEqAlg (STPosRight, STPosLeaf) d = False
STEqAlg (STPosRight, STPosLeft) d = False
STEqAlg (STPosRight, STPosRight) d = d (STDirR, STDirR)
STEqAlg (STPosRight, STPosPair) d = False
STEqAlg (STPosPair, STPosLeaf) d = False
STEqAlg (STPosPair, STPosLeft) d = False
STEqAlg (STPosPair, STPosRight) d = False
STEqAlg (STPosPair, STPosPair) d =
  d (STDirFst, STDirFst) && d (STDirSnd, STDirSnd)

public export
stEq : STMu -> STMu -> Bool
stEq = stProdCata STEqAlg

public export
Eq STMu where
  (==) = stEq

------------------------------------
---- Translation with Idris ADT ----
------------------------------------

public export
STMuToRecAlg : STAlg SubstTermRec
STMuToRecAlg STPosLeaf d = STRLeaf
STMuToRecAlg STPosLeft d = STRLeft $ d STDirL
STMuToRecAlg STPosRight d = STRRight $ d STDirR
STMuToRecAlg STPosPair d = STRPair (d STDirFst) (d STDirSnd)

public export
stMuToRec : STMu -> SubstTermRec
stMuToRec = stCata STMuToRecAlg

public export
stMuFromRec : SubstTermRec -> STMu
stMuFromRec STRLeaf = InSTUnit
stMuFromRec (STRLeft t) = InSTLeft $ stMuFromRec t
stMuFromRec (STRRight t) = InSTRight $ stMuFromRec t
stMuFromRec (STRPair t t') = InSTPair (stMuFromRec t) (stMuFromRec t')

---------------------
---- Refinements ----
---------------------

public export
STEqualizerPred : {0 a : Type} -> DecEqPred a -> STAlg a -> a -> STMu -> Bool
STEqualizerPred {a} eq alg elema obj = isYes $ eq elema $ stCata alg obj

public export
STEqualizer : {0 a : Type} -> DecEqPred a -> STAlg a -> SliceObj a
STEqualizer {a} eq alg elema =
  Refinement {a=STMu} $ STEqualizerPred eq alg elema

public export
STRefineAlg : Type
STRefineAlg = STAlg Bool

public export
STRefinement : SliceObj STRefineAlg
STRefinement alg = Refinement {a=STMu} $ stCata alg

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

public export
SOProductAlg : Type -> Type
SOProductAlg = PFProductAlg SubstObjPF SubstObjPF

public export
soProductCata : {0 a : Type} -> SOProductAlg a -> SOMu -> SOMu -> a
soProductCata {a} = pfProductCata {a} {p=SubstObjPF} {q=SubstObjPF}

public export
SOProductHomAlgNT : Type
SOProductHomAlgNT = PFProductHomAlgNT SubstObjPF SubstObjPF SubstObjPF

public export
soProductHomCataNT : SOProductHomAlgNT -> SOMu -> SOMu -> SOMu
soProductHomCataNT =
  pfProductHomCataNT {p=SubstObjPF} {q=SubstObjPF} {r=SubstObjPF}

public export
SOProductHomAlg : Type -> Type
SOProductHomAlg = PFProductHomAlg SubstObjPF SubstObjPF

public export
soProductHomCata : {a : Type} -> SOProductHomAlg a -> SOMu -> SOMu -> a
soProductHomCata = pfProductHomCata {p=SubstObjPF} {q=SubstObjPF}

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
SOCardAlg : SOAlg Nat
SOCardAlg SOPos0 dir = 0
SOCardAlg SOPos1 dir = 1
SOCardAlg SOPosC dir = dir SODirL + dir SODirR
SOCardAlg SOPosP dir = dir SODir1 * dir SODir2

public export
soCard : SOMu -> Nat
soCard = soCata SOCardAlg

public export
SOShowAlg : SOAlg String
SOShowAlg SOPos0 dir = "0"
SOShowAlg SOPos1 dir = "1"
SOShowAlg SOPosC dir = "[" ++ dir SODirL ++ "|" ++ dir SODirR ++ "]"
SOShowAlg SOPosP dir = "(" ++ dir SODir1 ++ "," ++ dir SODir2 ++ ")"

public export
Show SOMu where
  show = soCata SOShowAlg

public export
SOEqAlg : SOProductAlg Bool
SOEqAlg (SOPos0, SOPos0) d = True
SOEqAlg (SOPos0, SOPos1) d = False
SOEqAlg (SOPos0, SOPosC) d = False
SOEqAlg (SOPos0, SOPosP) d = False
SOEqAlg (SOPos1, SOPos0) d = False
SOEqAlg (SOPos1, SOPos1) d = True
SOEqAlg (SOPos1, SOPosC) d = False
SOEqAlg (SOPos1, SOPosP) d = False
SOEqAlg (SOPosC, SOPos0) d = False
SOEqAlg (SOPosC, SOPos1) d = False
SOEqAlg (SOPosC, SOPosC) d = d (SODirL, SODirL) && d (SODirR, SODirR)
SOEqAlg (SOPosC, SOPosP) d = False
SOEqAlg (SOPosP, SOPos0) d = False
SOEqAlg (SOPosP, SOPos1) d = False
SOEqAlg (SOPosP, SOPosC) d = False
SOEqAlg (SOPosP, SOPosP) d = d (SODir1, SODir1) && d (SODir2, SODir2)

public export
soEq : SOMu -> SOMu -> Bool
soEq = soProductCata SOEqAlg

public export
Eq SOMu where
  (==) = soEq

----------------------------------------
---- Interpretation into Idris Type ----
----------------------------------------

public export
SOInterpAlg : SOAlg Type
SOInterpAlg SOPos0 dir = Void
SOInterpAlg SOPos1 dir = Unit
SOInterpAlg SOPosC dir = Either (dir SODirL) (dir SODirR)
SOInterpAlg SOPosP dir = Pair (dir SODir1) (dir SODir2)

public export
soInterp : SOMu -> Type
soInterp = soCata SOInterpAlg

---------------------------------------------------------
---- Embedding into PolyFunc as constant endofunctor ----
---------------------------------------------------------

public export
SOConstEFAlg : SOAlg PolyFunc
SOConstEFAlg SOPos0 dir = PFInitialArena
SOConstEFAlg SOPos1 dir = PFTerminalArena
SOConstEFAlg SOPosC dir = pfCoproductArena (dir SODirL) (dir SODirR)
SOConstEFAlg SOPosP dir = pfProductArena (dir SODir1) (dir SODir2)

public export
soConstEF : SOMu -> PolyFunc
soConstEF = soCata SOConstEFAlg

--------------------------------------------------------------
---- Embedding into PolyFunc as representable endofunctor ----
--------------------------------------------------------------

public export
SORepEFAlg : SOAlg PolyFunc
SORepEFAlg SOPos0 dir = PFTerminalArena
SORepEFAlg SOPos1 dir = PFIdentityArena
SORepEFAlg SOPosC dir = pfProductArena (dir SODirL) (dir SODirR)
SORepEFAlg SOPosP dir = pfParProductArena (dir SODir1) (dir SODir2)

public export
soRepEF : SOMu -> PolyFunc
soRepEF = soCata SORepEFAlg

---------------------
---- Refinements ----
---------------------

-- Note:  this section implements refinements of the type of objects,
-- not the types of refinements of objects.  In other words, here we are
-- selecting classes of types, not selecting terms from individual types.

public export
SOEqualizerPred : {0 a : Type} -> DecEqPred a -> SOAlg a -> a -> SOMu -> Bool
SOEqualizerPred {a} eq alg elema obj = isYes $ eq elema $ soCata alg obj

public export
SOEqualizer : {0 a : Type} -> DecEqPred a -> SOAlg a -> SliceObj a
SOEqualizer {a} eq alg elema =
  Refinement {a=SOMu} $ SOEqualizerPred eq alg elema

public export
SORefineAlg : Type
SORefineAlg = SOAlg Bool

public export
SORefinement : SliceObj SORefineAlg
SORefinement alg = Refinement {a=SOMu} $ soCata alg

-----------------------------------------------
-----------------------------------------------
---- Relationships between terms and types ----
-----------------------------------------------
-----------------------------------------------

-- Test whether the given term is a valid term of the given type.
public export
SOTermCheckAlg : PFProductAlg SubstObjPF SubstTermPF Bool
-- No term has type `InSO0`.
SOTermCheckAlg (SOPos0, STPosLeaf) d = False
SOTermCheckAlg (SOPos0, STPosLeft) d = False
SOTermCheckAlg (SOPos0, STPosRight) d = False
SOTermCheckAlg (SOPos0, STPosPair) d = False
-- Only `InSTLeaf` has type `InSO1`.
SOTermCheckAlg (SOPos1, STPosLeaf) d = True
SOTermCheckAlg (SOPos1, STPosLeft) d = False
SOTermCheckAlg (SOPos1, STPosRight) d = False
SOTermCheckAlg (SOPos1, STPosPair) d = False
-- A coproduct term must be either a left injection or a right injection,
-- and its sub-term must match the corresponding sub-type.  The other
-- sub-type could be anything.
SOTermCheckAlg (SOPosC, STPosLeaf) d = False
SOTermCheckAlg (SOPosC, STPosLeft) d = d (SODirL, STDirL)
SOTermCheckAlg (SOPosC, STPosRight) d = d (SODirR, STDirR)
SOTermCheckAlg (SOPosC, STPosPair) d = False
-- A product term must be a pair, and each of its sub-terms must
-- match the corresponding sub-type.
SOTermCheckAlg (SOPosP, STPosLeaf) d = False
SOTermCheckAlg (SOPosP, STPosLeft) d = False
SOTermCheckAlg (SOPosP, STPosRight) d = False
SOTermCheckAlg (SOPosP, STPosPair) d =
  d (SODir1, STDirFst) && d (SODir2, STDirSnd)

public export
soTermCheck : SOMu -> DecPred STMu
soTermCheck = pfProductCata SOTermCheckAlg

public export
STTyped : SOMu -> Type
STTyped so = Refinement {a=STMu} $ soTermCheck so

public export
MkSTTyped : {0 so : SOMu} -> (t : STMu) ->
  {auto 0 ok : Satisfies (soTermCheck so) t} -> STTyped so
MkSTTyped {so} t {ok} = MkRefinement t

public export
SOTermArena : PolyFunc
SOTermArena = pfParProductArena SubstObjPF SubstTermPF

public export
SOTermPos : Type
SOTermPos = pfPos SOTermArena

public export
SOTermDir : SliceObj SOTermPos
SOTermDir = pfDir {p=SOTermArena}

public export
SOTermPosDep : SliceObj SOTermPos
SOTermPosDep = SliceObj . SOTermDir

data SOTermDirDep : PFProductAlg SubstObjPF SubstTermPF Type where
  SOTermDirDep1L :
    {d : (SubstObjDir SOPos1, SubstTermDir STPosLeaf) -> Type} ->
    SOTermDirDep (SOPos1, STPosLeaf) d
  SOTermDirDepCL :
    {d : (SubstObjDir SOPosC, SubstTermDir STPosLeft) -> Type} ->
    d (SODirL, STDirL) ->
    SOTermDirDep (SOPosC, STPosLeft) d
  SOTermDirDepCR :
    {d : (SubstObjDir SOPosC, SubstTermDir STPosRight) -> Type} ->
    d (SODirR, STDirR) ->
    SOTermDirDep (SOPosC, STPosRight) d
  SOTermDirDepPP :
    {d : (SubstObjDir SOPosP, SubstTermDir STPosPair) -> Type} ->
    d (SODir1, STDirFst) -> d (SODir2, STDirSnd) ->
    SOTermDirDep (SOPosP, STPosPair) d

public export
SOTermSPFEndoId : SlicePolyEndoFuncId SOTermPos
SOTermSPFEndoId = (SOTermPosDep ** \(i ** d) => SOTermDirDep i d)

public export
SOTermSPF : SlicePolyEndoFunc SOTermPos
SOTermSPF = SlicePolyEndoFuncFromId SOTermSPFEndoId

public export
SOCheckedTermDir : SliceObj SOTermPos
SOCheckedTermDir = SPFMu SOTermSPF

---------------------------
---------------------------
---- Morphisms in SOMu ----
---------------------------
---------------------------

public export
SOHomObjAlg : SOAlg (SOMu -> SOMu)
-- 0 -> x === 1
SOHomObjAlg SOPos0 d obj = InSO1
-- 1 -> x === x
SOHomObjAlg SOPos1 d obj = obj
-- (x + y) -> z === (x -> z) * (y -> z)
SOHomObjAlg SOPosC d obj = InSOP (d SODirL obj) (d SODirR obj)
-- (x * y) -> z === x -> (y -> z)
SOHomObjAlg SOPosP d obj = d SODir1 $ d SODir2 obj

public export
soHomObj : SOMu -> SOMu -> SOMu
soHomObj = soCata SOHomObjAlg

public export
soExpObj : SOMu -> SOMu -> SOMu
soExpObj = flip soHomObj

public export
SOHomTerm : SOMu -> SOMu -> Type
SOHomTerm = STTyped .* soHomObj

-----------------------------------
-----------------------------------
---- Simple types, anonymously ----
-----------------------------------
-----------------------------------

-------------------------------
---- Unary natural numbers ----
-------------------------------

public export
UNatF : PolyFunc
UNatF = pfMaybeArena

public export
UNatAlg : Type -> Type
UNatAlg a = (a, a -> a)

public export
UNatAlgToPF : {a : Type} -> UNatAlg a -> PFAlg UNatF a
UNatAlgToPF (z, s) (Right ()) d = z
UNatAlgToPF (z, s) (Left ()) d = s $ d ()

public export
UNatMu : Type
UNatMu = PolyFuncMu UNatF

public export
unatCata : {a : Type} -> UNatAlg a -> UNatMu -> a
unatCata = pfCata {p=UNatF} . UNatAlgToPF

public export
UNatFreePF : PolyFunc
UNatFreePF = PolyFuncFreeM UNatF

public export
UNatFreeM : Type -> Type
UNatFreeM = InterpPolyFuncFreeM UNatF

public export
unatSubstCata : {a, b : Type} -> (a -> b) -> UNatAlg b -> UNatFreeM a -> b
unatSubstCata subst = pfSubstCata {p=UNatF} subst . UNatAlgToPF

public export
UNatToNativeAlg : UNatAlg Nat
UNatToNativeAlg = (Z, S)

public export
unatToNative : UNatMu -> Nat
unatToNative = unatCata UNatToNativeAlg

public export
unatZ : UNatMu
unatZ = InPFM (Right ()) $ voidF _

public export
unatS : UNatMu -> UNatMu
unatS n = InPFM (Left ()) $ const n

public export
unatFromNative : Nat -> UNatMu
unatFromNative Z = unatZ
unatFromNative (S n) = unatS (unatFromNative n)

public export
Show UNatMu where
  show n = show (unatToNative n)

--------------------------------
---- Unlabeled binary trees ----
--------------------------------

public export
UBTreeF : PolyFunc
UBTreeF = pfCompositionArena pfMaybeArena pfIdSquaredArena

public export
UBTreeAlg : Type -> Type
UBTreeAlg a = (a, a -> a -> a)

public export
UBTreeAlgToPF : {a : Type} -> UBTreeAlg a -> PFAlg UBTreeF a
UBTreeAlgToPF {a} (u, p) (Right () ** i) d = u
UBTreeAlgToPF {a} (u, p) (Left () ** i) d with (i ()) proof ieq
  UBTreeAlgToPF {a} (u, p) (Left () ** i) d | ((), ()) =
    p (d (() ** rewrite ieq in Left ())) (d (() ** rewrite ieq in Right ()))

public export
UBTreeMu : Type
UBTreeMu = PolyFuncMu UBTreeF

public export
ubtreeCata : {a : Type} -> UBTreeAlg a -> UBTreeMu -> a
ubtreeCata = pfCata {p=UBTreeF} . UBTreeAlgToPF

public export
UBTreeFreePF : PolyFunc
UBTreeFreePF = PolyFuncFreeM UBTreeF

public export
UBTreeFreeM : Type -> Type
UBTreeFreeM = InterpPolyFuncFreeM UBTreeF

public export
ubtreeSubstCata : {a, b : Type} -> (a -> b) -> UBTreeAlg b -> UBTreeFreeM a -> b
ubtreeSubstCata subst = pfSubstCata {p=UBTreeF} subst . UBTreeAlgToPF

public export
UBTreeShowAlg : UBTreeAlg String
UBTreeShowAlg = ("!", \x, y => "(" ++ x ++ "," ++ y ++ ")")

public export
Show UBTreeMu where
  show = ubtreeCata UBTreeShowAlg

----------------------------------------------------
---- Finite-product-and-coproduct objects/types ----
----------------------------------------------------

public export
FinPCObjF : PolyFunc
FinPCObjF = pfDoubleArena UBTreeF

public export
FinPCObjAlg : Type -> Type
FinPCObjAlg a = (UBTreeAlg a, UBTreeAlg a)

-- `alg1` is the algebra for limits (the terminal object and products)
-- while `alg2` is the algebra for colimits (the initial object and coproducts).
public export
FinPCObjAlgToPF : {a : Type} -> FinPCObjAlg a -> PFAlg FinPCObjF a
FinPCObjAlgToPF (alg1, alg2) =
  PFCoprodAlg {p=UBTreeF} {q=UBTreeF} (UBTreeAlgToPF alg1) (UBTreeAlgToPF alg2)

public export
FinPCObjMu : Type
FinPCObjMu = PolyFuncMu FinPCObjF

public export
finPCObjCata : {a : Type} -> FinPCObjAlg a -> FinPCObjMu -> a
finPCObjCata = pfCata {p=FinPCObjF} . FinPCObjAlgToPF

public export
FinPCObjFreePF : PolyFunc
FinPCObjFreePF = PolyFuncFreeM FinPCObjF

public export
FinPCObjFreeM : Type -> Type
FinPCObjFreeM = InterpPolyFuncFreeM FinPCObjF

public export
finPCObjSubstCata : {a, b : Type} ->
  (a -> b) -> FinPCObjAlg b -> FinPCObjFreeM a -> b
finPCObjSubstCata subst = pfSubstCata {p=FinPCObjF} subst . FinPCObjAlgToPF

public export
FinPCObjShowAlg : FinPCObjAlg String
FinPCObjShowAlg =
  (("1", \x, y => "(" ++ x ++ "," ++ y ++ ")"),
   ("0", \x, y => "[" ++ x ++ "+" ++ y ++ "]"))

public export
Show FinPCObjMu where
  show = finPCObjCata FinPCObjShowAlg

--------------------------------------------
---- Finite-product-and-coproduct terms ----
--------------------------------------------

public export
FinPCTermF : PolyFunc
FinPCTermF = pfSquareArena pfMaybeArena

-- Components of the algebra:
--  - unit
--  - left
--  - right
--  - pair
public export
FinPCTermAlg : Type -> Type
FinPCTermAlg a = (a, a -> a, a -> a, a -> a -> a)

public export
FinPCTermAlgToPF : {a : Type} -> FinPCTermAlg a -> PFAlg FinPCTermF a
FinPCTermAlgToPF (u, l, r, p) (Right (), Right ()) d = u
FinPCTermAlgToPF (u, l, r, p) (Right (), Left ()) d = r $ d $ Right ()
FinPCTermAlgToPF (u, l, r, p) (Left (), Right ()) d = l $ d $ Left ()
FinPCTermAlgToPF (u, l, r, p) (Left (), Left ()) d =
  p (d $ Left ()) (d $ Right ())

public export
FinPCTermMu : Type
FinPCTermMu = PolyFuncMu FinPCTermF

public export
finPCTermCata : {a : Type} -> FinPCTermAlg a -> FinPCTermMu -> a
finPCTermCata = pfCata {p=FinPCTermF} . FinPCTermAlgToPF

public export
FinPCTermFreePF : PolyFunc
FinPCTermFreePF = PolyFuncFreeM FinPCTermF

public export
FinPCTermFreeM : Type -> Type
FinPCTermFreeM = InterpPolyFuncFreeM FinPCTermF

public export
finPCTermSubstCata : {a, b : Type} ->
  (a -> b) -> FinPCTermAlg b -> FinPCTermFreeM a -> b
finPCTermSubstCata subst = pfSubstCata subst . FinPCTermAlgToPF

public export
FinPCTermShowAlg : FinPCTermAlg String
FinPCTermShowAlg =
  ("!",
   \x => "l[" ++ x ++ "]",
   \x => "r[" ++ x ++ "]",
   \x, y => "(" ++ x ++ "," ++ y ++ ")")

public export
Show FinPCTermMu where
  show = finPCTermCata FinPCTermShowAlg

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---- Explicitly-recursive ADT equivalent to generalized polynomial ADT term ----
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

public export
record TermAtom where
  constructor TAtom
  tAtom : GebAtom
  tData : Nat

public export
data GebTerm : Type where
  GebRecordTerm : List GebTerm -> GebTerm
  GebSumTerm : TermAtom -> GebTerm -> GebTerm

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

public export
Show TermAtom where
  show (TAtom a n) = show a ++ ":" ++ show n

-- A position of the coproduct term functor is the index of the sub-term.
public export
CoprodTermPos : Type
CoprodTermPos = TermAtom

-- Any coproduct term position has exactly one direction, which corresponds
-- to the term being injected into a coproduct term at the index given by
-- the position.
public export
CoprodTermDir : CoprodTermPos -> Type
CoprodTermDir i = Unit

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

public export
ProdAlg : Type -> Type
ProdAlg a = List a -> a

public export
MkProdAlg : {0 a : Type} -> ProdAlg a -> PFAlg ProdTermPF a
MkProdAlg alg len = alg . toList . finFToVect {n=len}

public export
prodCata : {0 a : Type} -> ProdAlg a -> PolyFuncMu ProdTermPF -> a
prodCata = pfCata {p=ProdTermPF} . MkProdAlg

public export
CoprodAlg : Type -> Type
CoprodAlg a = TermAtom -> a -> a

public export
MkCoprodAlg : {0 a : Type} -> CoprodAlg a -> PFAlg CoprodTermPF a
MkCoprodAlg alg n x = alg n $ x ()

public export
coprodCata : {0 a : Type} -> CoprodAlg a -> PolyFuncMu CoprodTermPF -> a
coprodCata = pfCata {p=CoprodTermPF} . MkCoprodAlg

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
  talgProd : ProdAlg a
  talgCoprod : CoprodAlg a

public export
talgFromRec : {0 a : Type} -> TermAlgRec a -> TermAlg a
talgFromRec alg (Left len) ts = MkProdAlg alg.talgProd len ts
talgFromRec alg (Right idx) t = MkCoprodAlg alg.talgCoprod idx t

public export
termCataRec : {0 a : Type} -> TermAlgRec a -> TermMu -> a
termCataRec = termCata . talgFromRec

public export
termCataCtx : {0 ctx, a : Type} -> (ctx -> TermAlgRec a) -> ctx -> TermMu -> a
termCataCtx {ctx} {a} alg =
  pfParamCata {p=ADTTermPF} {x=ctx} {a} ?termCataCtx_hole

----------------------
---- Constructors ----
----------------------

public export
InProd : List TermMu -> TermMu
InProd ts = InPFM (Left $ length ts) $ index' ts

public export
InTermAtom : TermAtom -> TermMu -> TermMu
InTermAtom n t = InPFM (Right n) $ \() => t

public export
InAtom : GebAtom -> Nat -> TermMu -> TermMu
InAtom = InTermAtom .* TAtom

public export
InNat : Nat -> TermMu -> TermMu
InNat = InAtom NAT

-------------------
---- Utilities ----
-------------------

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
termShowList (t :: ts@(_ :: _)) = t ++ "," ++ termShowList ts

public export
termShowProduct : List String -> String
termShowProduct ts = "(" ++ termShowList ts ++ ")"

public export
termShowCoproduct : TermAtom -> String -> String
termShowCoproduct n t = "[" ++ show n ++ ":" ++ t ++ "]"

public export
TermShowAlg : TermAlgRec String
TermShowAlg = MkTermAlg termShowProduct termShowCoproduct

public export
Show TermMu where
  show = termCataRec TermShowAlg

----------------------------------------
----------------------------------------
---- Finite product/coproduct types ----
----------------------------------------
----------------------------------------

------------------------------
---- Structure definition ----
------------------------------

-- Types constructed from finite products and coproducts are generated by
-- either of two products -- that is, lists of types, of which we will
-- generate either its product or its coproduct.
--
-- Thus these are the objects of a free bicartesian category.
public export
FinBCObjPF : PolyFunc
FinBCObjPF = pfCoproductArena ProdTermPF ProdTermPF

public export
FinBCObjPos : Type
FinBCObjPos = pfPos FinBCObjPF

public export
FinBCObjDir : FinBCObjPos -> Type
FinBCObjDir = pfDir {p=FinBCObjPF}

public export
record FinBCObjAlgRec (a : Type) where
  constructor MkFinBCObjAlg
  fbcAlgProd : ProdAlg a
  fbcAlgCoprod : ProdAlg a

public export
fbcAlgFromRec : {0 a : Type} -> FinBCObjAlgRec a -> PFAlg FinBCObjPF a
fbcAlgFromRec alg (Left len) ts = MkProdAlg alg.fbcAlgProd len ts
fbcAlgFromRec alg (Right len) ts = MkProdAlg alg.fbcAlgCoprod len ts

public export
FinBCObjMu : Type
FinBCObjMu = PolyFuncMu FinBCObjPF

public export
fbcObjCataRec : {0 a : Type} -> FinBCObjAlgRec a -> FinBCObjMu -> a
fbcObjCataRec = pfCata {p=FinBCObjPF} . fbcAlgFromRec

--------------------------------------------------
---- Translation to and from generalized term ----
--------------------------------------------------

public export
FBCObjRepProdIdx : Nat
FBCObjRepProdIdx = 0

public export
FBCObjRepTermAtom : Nat
FBCObjRepTermAtom = 1

public export
FBCObjRepAlg : FinBCObjAlgRec TermMu
FBCObjRepAlg =
  MkFinBCObjAlg
    (InAtom PRODUCT 0 . InProd)
    (InAtom COPRODUCT 0 . InProd)

public export
fbcObjRep : FinBCObjMu -> TermMu
fbcObjRep = fbcObjCataRec FBCObjRepAlg

public export
FBCObjParseAlg : TermAlgRec (Maybe FinBCObjMu)
FBCObjParseAlg =
  MkTermAlg
    (\ts => let tra = sequence ts in map ?FBCObjParse_hole_prod tra)
    (\ts => ?FBCObjParse_hole_coprod)

public export
fbcObjParse : TermMu -> Maybe FinBCObjMu
fbcObjParse = termCataRec FBCObjParseAlg

-----------------------------------------------------
-----------------------------------------------------
---- Term representation of substitutive objects ----
-----------------------------------------------------
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

---------------------------------------------
---- Interpretation of SEFMu as PolyFunc ----
---------------------------------------------

public export
SOtoPFalg : SOAlg PolyFunc
SOtoPFalg SOPos0 d = PFInitialArena
SOtoPFalg SOPos1 d = PFTerminalArena
SOtoPFalg SOPosC d = pfCoproductArena (d SODirL) (d SODirR)
SOtoPFalg SOPosP d = pfProductArena (d SODir1) (d SODir2)

public export
SEFtoPFalgExt : SEFAlgExt PolyFunc
SEFtoPFalgExt SEFPosExtI d =
  PFIdentityArena
SEFtoPFalgExt SEFPosExtPar d =
  pfParProductArena (d SEFDirExtPar1) (d SEFDirExtPar2)

public export
SEFtoPFalg : SEFAlg PolyFunc
SEFtoPFalg = PFCoprodAlg {p=SubstObjPF} {q=SubstEFExt} SOtoPFalg SEFtoPFalgExt

public export
sefToPF : SEFMu -> PolyFunc
sefToPF = sefCata SEFtoPFalg

--------------------------------------------------------------------------
--------------------------------------------------------------------------
---- Reflection of object and endofunctor definitions as endofunctors ----
--------------------------------------------------------------------------
--------------------------------------------------------------------------

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

-------------------------------------------------------------
---- Conversion to and from explicitly-recursive version ----
-------------------------------------------------------------

mutual
  public export
  gebTermToADTTerm : GebTerm -> TermMu
  gebTermToADTTerm (GebRecordTerm ts) = InProd $ gebTermListToADTTermList ts
  gebTermToADTTerm (GebSumTerm n t) = InTermAtom n $ gebTermToADTTerm t

  public export
  gebTermListToADTTermList : List GebTerm -> List TermMu
  gebTermListToADTTermList [] =
    []
  gebTermListToADTTermList (t :: ts) =
    gebTermToADTTerm t :: gebTermListToADTTermList ts

public export
termToGebTermAlg : TermAlgRec GebTerm
termToGebTermAlg = MkTermAlg GebRecordTerm GebSumTerm

public export
termToGebTerm : TermMu -> GebTerm
termToGebTerm = termCataRec termToGebTermAlg

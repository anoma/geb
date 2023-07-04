module LanguageDef.PolyIndTypes

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.Atom
import public LanguageDef.RefinedADT
import public LanguageDef.PolyCat
import public LanguageDef.ADTCat
import public LanguageDef.Figures
import public LanguageDef.Theories
import public LanguageDef.Syntax
import public LanguageDef.DiagramCat

%default total

-------------------------------
-------------------------------
---- Copresheaf categories ----
-------------------------------
-------------------------------

public export
record PCopresheaf (j : PreDiagram) where
  constructor PCoprshf
  pcprObj : pdVert j -> Type
  pcprMorph : (x, y : pdVert j) ->
    pdEdge j (x, y) -> pcprObj x -> pcprObj y

-- (Co)presheaves over a given diagram themselves form a category.
-- Since a copresheaf is a functor, a morphism in a category
-- of (co)presheaves is a natural transformation.
public export
PCMorphComponents : {j : PreDiagram} -> PCopresheaf j -> PCopresheaf j -> Type
PCMorphComponents {j} pcpr pcpr' =
  SliceMorphism {a=(pdVert j)} (pcprObj pcpr) (pcprObj pcpr')

public export
0 PCMorphNaturality : {j : PreDiagram} -> {pcpr, pcpr' : PCopresheaf j} ->
  PCMorphComponents {j} pcpr pcpr' -> Type
PCMorphNaturality {j} {pcpr} {pcpr'} alpha =
  (x, y : pdVert j) -> (e : pdEdge j (x, y)) ->
  ExtEq (alpha y . pcprMorph pcpr x y e) (pcprMorph pcpr' x y e . alpha x)

public export
PCMorph : {j : PreDiagram} -> PCopresheaf j -> PCopresheaf j -> Type
PCMorph {j} pcpr pcpr' =
  Subset0
    (PCMorphComponents {j} pcpr pcpr')
    (PCMorphNaturality {j} {pcpr} {pcpr'})

--------------------------------
--------------------------------
---- Categories of elements ----
--------------------------------
--------------------------------

public export
ElemCatObj : {j : PreDiagram} -> PCopresheaf j -> Type
ElemCatObj {j} pcpr = Sigma {a=(pdVert j)} (pcprObj pcpr)

public export
ElemCatDiagMorph : {j : PreDiagram} -> {0 pcpr : PCopresheaf j} ->
  ElemCatObj {j} pcpr -> ElemCatObj {j} pcpr -> Type
ElemCatDiagMorph {j} {pcpr} x y =
  Subset0 (pdEdge j (fst x, fst y)) $
    \e => pcprMorph pcpr (fst x) (fst y) e (snd x) = snd y

-----------------------------------
-----------------------------------
---- Prafunctors (Bicomodules) ----
-----------------------------------
-----------------------------------

-- See https://topos.site/blog/2022/08/imagining-bicomodules-with-type-theory/ .

public export
record PRAFunctor (dom, cod : PreDiagram) where
  constructor PRAf
  prafPos : PCopresheaf cod
  -- `prafDir` and `prafAssign` between them comprise a contravariant functor
  -- from the category of elements of `prafPos` (which is a copresheaf over
  -- `cod`) to the category of copresheaves over `dom`.
  prafDir : ElemCatObj {j=cod} prafPos -> PCopresheaf dom
  prafAssign :
    (p, p' : ElemCatObj {j=cod} prafPos) ->
    ElemCatDiagMorph {j=cod} {pcpr=prafPos} p' p ->
    PCMorph {j=dom} (prafDir p) (prafDir p')

-----------------------------------------
-----------------------------------------
---- Inductive-inductive definitions ----
-----------------------------------------
-----------------------------------------

-- See
-- https://www.semanticscholar.org/paper/A-Categorical-Semantics-for-Inductive-Inductive-Altenkirch-Morris/4653b2f69670c358063bac0d57d4288fbfe6d52c

--------------------------------
---- Non-indexed definition ----
--------------------------------

public export
FamSetObj : Type
FamSetObj = PolyFunc

public export
FamSetMorph : FamSetObj -> FamSetObj -> Type
FamSetMorph = DirichNatTrans

public export
IndIndF1 : Type
IndIndF1 = FamSetObj -> Type

public export
IndIndAlg : IndIndF1 -> (a : Type) -> (a -> Type) -> Type
IndIndAlg f1 a b = f1 (a ** b) -> a

public export
IndIndF2 : IndIndF1 -> Type
IndIndF2 f1 = (a : Type) -> (b : a -> Type) ->
  IndIndAlg f1 a b -> f1 (a ** b) -> Type

public export
IndInd : Type
IndInd = DPair IndIndF1 IndIndF2

--------------------------------------
---- Example (dependent contexts) ----
--------------------------------------

public export
data ArgDCtx : IndIndF1 where
  DCnil : {0 a : Type} -> {0 b : a -> Type} -> ArgDCtx (a ** b)
  DCcons : {0 a : Type} -> {0 b : a -> Type} ->
    (ctx : a) -> b ctx -> ArgDCtx (a ** b)

public export
data ArgDType : IndIndF2 ArgDCtx where
  DTbase : {0 a : Type} -> {0 b : a -> Type} ->
    {0 alg : IndIndAlg ArgDCtx a b} ->
    (ctx : ArgDCtx (a ** b)) -> ArgDType a b alg ctx
  DTpi : {0 a : Type} -> {0 b : a -> Type} ->
    {0 alg : IndIndAlg ArgDCtx a b} ->
    (ctx : ArgDCtx (a ** b)) ->
    (dom : b (alg ctx)) -> (cod : b (alg $ DCcons {a} {b} (alg ctx) dom)) ->
    ArgDType a b alg ctx

mutual
  public export
  partial
  data DCtx : Type where
    InDCtx : ArgDCtx (DCtx ** DType) -> DCtx

  public export
  partial
  data DType : DCtx -> Type where
    InDType : (ctx : ArgDCtx (DCtx ** DType)) ->
      ArgDType DCtx DType InDCtx ctx -> DType (InDCtx ctx)

--------------------------------------
---- Indexed/dependent definition ----
--------------------------------------

public export
DepFamSetObj : Type -> Type
DepFamSetObj x = (a : Type ** (x, a) -> Type)

public export
DepFamSetMorph : {x : Type} -> DepFamSetObj x -> DepFamSetObj x -> x -> Type
DepFamSetMorph {x} (a ** b) (a' ** b') elx =
  (onPos : (x, a) -> (x, a') ** SliceMorphism {a=(x, a)} b (b' . onPos))

public export
DepIndIndF1 : Type -> Type
DepIndIndF1 x = DepFamSetObj x -> Type

public export
DepIndIndAlg : {0 x : Type} ->
  DepIndIndF1 x -> (a : Type) -> ((x, a) -> Type) -> Type
DepIndIndAlg {x} f1 a b = f1 (a ** b) -> a

public export
DepIndIndF2 : {x : Type} -> DepIndIndF1 x -> Type
DepIndIndF2 {x} f1 = (a : Type) -> (b : (x, a) -> Type) ->
  DepIndIndAlg {x} f1 a b -> x -> f1 (a ** b) -> Type

public export
DepIndInd : Type -> Type
DepIndInd x = DPair (DepIndIndF1 x) (DepIndIndF2 {x})

---------------------------------------------------------
---- Nat-dependent indexed inductive-inductive types ----
---------------------------------------------------------

public export
NatFamSetObj : Type
NatFamSetObj = DepFamSetObj Nat

public export
NatFamSetMorph : NatFamSetObj -> NatFamSetObj -> Nat -> Type
NatFamSetMorph = DepFamSetMorph {x=Nat}

public export
NatIndIndF1 : Type
NatIndIndF1 = DepIndIndF1 Nat

public export
NatIndIndAlg : NatIndIndF1 -> (a : Type) -> ((Nat, a) -> Type) -> Type
NatIndIndAlg = DepIndIndAlg {x=Nat}

public export
NatIndIndF2 : NatIndIndF1 -> Type
NatIndIndF2 = DepIndIndF2 {x=Nat}

public export
NatIndInd : Type
NatIndInd = DepIndInd Nat

--------------------------------
---- Example (sorted lists) ----
--------------------------------

public export
data ArgSList : NatIndIndF1 where
  SLnil : {0 a : Type} -> {0 b : (Nat, a) -> Type} -> ArgSList (a ** b)
  SLcons : {0 a : Type} -> {0 b : (Nat, a) -> Type} ->
    (n : Nat) -> (l : a) -> b (n, l) -> ArgSList (a ** b)

public export
data ArgLteL : NatIndIndF2 ArgSList where
  IsSLnil : {0 a : Type} -> {0 b : (Nat, a) -> Type} ->
    {0 alg : NatIndIndAlg ArgSList a b} -> {0 m : Nat} ->
    ArgLteL a b alg m (SLnil {a} {b})
  IsSLcons : {0 a : Type} -> {0 b : (Nat, a) -> Type} ->
    {0 alg : NatIndIndAlg ArgSList a b} ->
    {m, n : Nat} -> LTE m n -> {l : a} -> (p : b (n, l)) ->
    ArgLteL a b alg m (SLcons {a} {b} n l p)

mutual
  public export
  partial
  data SortedList : Type where
    InSL : ArgSList (SortedList ** LteAll) -> SortedList

  public export
  partial
  data LteAll : (Nat, SortedList) -> Type where
    InLte : (m : Nat) -> (sl : ArgSList (SortedList ** LteAll)) ->
      ArgLteL SortedList LteAll InSL m sl -> LteAll (m, InSL sl)

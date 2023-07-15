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
---- Slices with relations ----
-------------------------------
-------------------------------

public export
record SliceRelPF (dom, cod : Type) where
  constructor SRPF

---------------------------------------
---------------------------------------
---- Dependent polynomial functors ----
---------------------------------------
---------------------------------------

public export
SliceGenPF : Type -> Type -> Type
SliceGenPF dom cod = (pos : SliceObj cod ** SliceObj (dom, Sigma pos))

public export
SGPFtoSPF : {dom, cod : Type} -> SliceGenPF dom cod -> SlicePolyFunc dom cod
SGPFtoSPF {dom} {cod} (pos ** dir) =
  (pos ** Sigma {a=dom} . flip (curry dir) ** \i => fst $ snd $ i)

public export
SPFtoSGPF : {dom, cod : Type} -> SlicePolyFunc dom cod -> SliceGenPF dom cod
SPFtoSGPF {dom} {cod} (pos ** dir ** assign) =
  (pos ** \(i, j) => Subset0 (dir j) $ \d => Equal (assign (j ** d)) i)

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
IndIndF1 : Type
IndIndF1 = PolyFunc -> Type

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

mutual
  public export
  partial
  data IndInd1 : IndInd -> PolyFunc -> Type where
    InI1v : {0 f1 : IndIndF1} -> {0 f2 : IndIndF2 f1} -> {0 p : PolyFunc} ->
      pfPos p -> IndInd1 (f1 ** f2) p
    InI1c : {0 f1 : IndIndF1} -> {0 f2 : IndIndF2 f1} -> {0 p : PolyFunc} ->
      f1 (IndInd1 (f1 ** f2) p ** IndInd2 (f1 ** f2) p) -> IndInd1 (f1 ** f2) p

  public export
  partial
  data IndInd2 : (ii : IndInd) -> (p : PolyFunc) -> IndInd1 ii p -> Type where
    InI2v : {0 f1 : IndIndF1} -> {0 f2 : IndIndF2 f1} -> {0 p : PolyFunc} ->
      (i : pfPos p) -> pfDir {p} i -> IndInd2 (f1 ** f2) p (InI1v i)
    InI2c : {0 f1 : IndIndF1} -> {0 f2 : IndIndF2 f1} -> {0 p : PolyFunc} ->
      (i1 : f1 (IndInd1 (f1 ** f2) p ** IndInd2 (f1 ** f2) p)) ->
      f2 (IndInd1 (f1 ** f2) p) (IndInd2 (f1 ** f2) p) InI1c i1 ->
      IndInd2 (f1 ** f2) p (InI1c i1)

public export
partial
IndIndF : IndInd -> PolyFunc -> PolyFunc
IndIndF ii p = (IndInd1 ii p ** IndInd2 ii p)

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
  FunExt -> alpha y . pcprMorph pcpr x y e = pcprMorph pcpr' x y e . alpha x

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

public export
ElemCatDiagOpMorph : {j : PreDiagram} -> {0 pcpr : PCopresheaf j} ->
  ElemCatObj {j} pcpr -> ElemCatObj {j} pcpr -> Type
ElemCatDiagOpMorph {j} {pcpr} = flip $ ElemCatDiagMorph {j} {pcpr}

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
  -- `prafDirObj` and `prafDirMorph` between them comprise a contravariant
  -- functor from the category of elements of `prafPos` (which is a copresheaf
  -- over `cod`) to the category of copresheaves over `dom`.
  prafDirObj : ElemCatObj {j=cod} prafPos -> PCopresheaf dom
  prafDirMorph :
    (p, p' : ElemCatObj {j=cod} prafPos) ->
    ElemCatDiagOpMorph {j=cod} {pcpr=prafPos} p p' ->
    PCMorph {j=dom} (prafDirObj p) (prafDirObj p')

public export
PRAEndoFunctor : PreDiagram -> Type
PRAEndoFunctor base = PRAFunctor base base

public export
InterpPRAobj : {dom, cod : PreDiagram} -> PRAFunctor dom cod ->
  PCopresheaf dom -> pdVert cod -> Type
InterpPRAobj {dom} {cod} praf pcpr i =
  (p : pcprObj (prafPos praf) i ** PCMorph (prafDirObj praf (i ** p)) pcpr)

public export
InterpPRAmorphPos : {dom, cod : PreDiagram} -> (praf : PRAFunctor dom cod) ->
  (pcdom : PCopresheaf dom) -> (i, j : pdVert cod) -> pdEdge cod (i, j) ->
  InterpPRAobj {dom} {cod} praf pcdom i ->
  pcprObj (prafPos praf) j
InterpPRAmorphPos {dom} {cod} praf pcdom i j e p =
  pcprMorph (prafPos praf) i j e (fst p)

public export
InterpPRAmorphComponents :
  {dom, cod : PreDiagram} -> (praf : PRAFunctor dom cod) ->
  (pcdom : PCopresheaf dom) -> (i, j : pdVert cod) -> (e : pdEdge cod (i, j)) ->
  (p : InterpPRAobj {dom} {cod} praf pcdom i) ->
  PCMorphComponents {j=dom}
    (prafDirObj praf (j ** InterpPRAmorphPos praf pcdom i j e p)) pcdom
InterpPRAmorphComponents {dom=(MkPreDiag domv dome)} {cod=(MkPreDiag codv code)}
  (PRAf (PCoprshf objcod morphcod) dir fmap)
  pcdom i j e (p ** Element0 alpha natural) vd dvd =
    alpha vd $
      fst0 (fmap (j ** morphcod i j e p) (i ** p) (Element0 e Refl)) vd dvd

public export
0 InterpPRAmorphNaturality :
  {dom, cod : PreDiagram} -> (praf : PRAFunctor dom cod) ->
  (pcdom : PCopresheaf dom) -> (i, j : pdVert cod) -> (e : pdEdge cod (i, j)) ->
  (p : InterpPRAobj {dom} {cod} praf pcdom i) ->
  PCMorphNaturality
    {pcpr=(prafDirObj praf (j ** InterpPRAmorphPos praf pcdom i j e p))}
    {pcpr'=pcdom}
    (InterpPRAmorphComponents {dom} {cod} praf pcdom i j e p)
InterpPRAmorphNaturality {dom=(MkPreDiag domv dome)} {cod=(MkPreDiag codv code)}
  (PRAf (PCoprshf objcod morphcod) dir fmap)
  pcdom i j e (p ** Element0 alpha natural) i' j' e'
  funext =
    funExt $ \el =>
      trans
        (cong (alpha j')
          (fcong (snd0 (fmap
            (j ** morphcod i j e p) (i ** p) (Element0 e Refl))
            i' j' e' funext) {x=el})
        )
        (fcong (natural i' j' e' funext)
          {x=(fst0 (fmap
            (j ** morphcod i j e p) (i ** p) (Element0 e Refl)) i' el)})

public export
InterpPRAmorphDir : {dom, cod : PreDiagram} -> (praf : PRAFunctor dom cod) ->
  (pcdom : PCopresheaf dom) -> (i, j : pdVert cod) -> (e : pdEdge cod (i, j)) ->
  (p : InterpPRAobj {dom} {cod} praf pcdom i) ->
  PCMorph (prafDirObj praf (j ** InterpPRAmorphPos praf pcdom i j e p)) pcdom
InterpPRAmorphDir {dom} {cod} praf pcdom i j e p =
  Element0
    (InterpPRAmorphComponents {dom} {cod} praf pcdom i j e p)
    (InterpPRAmorphNaturality {dom} {cod} praf pcdom i j e p)

public export
InterpPRAmorph : {dom, cod : PreDiagram} -> (praf : PRAFunctor dom cod) ->
  (pcdom : PCopresheaf dom) -> (i, j : pdVert cod) -> pdEdge cod (i, j) ->
  InterpPRAobj {dom} {cod} praf pcdom i ->
  InterpPRAobj {dom} {cod} praf pcdom j
InterpPRAmorph {dom} {cod} praf pcdom i j e p =
  (InterpPRAmorphPos praf pcdom i j e p ** InterpPRAmorphDir praf pcdom i j e p)

public export
InterpPRA : {dom, cod : PreDiagram} -> (praf : PRAFunctor dom cod) ->
  PCopresheaf dom -> PCopresheaf cod
InterpPRA {dom} {cod} praf pcdom =
  PCoprshf
    (InterpPRAobj {dom} {cod} praf pcdom)
    (InterpPRAmorph {dom} {cod} praf pcdom)

public export
InterpPRAfmapComponents :
  {dom, cod : PreDiagram} -> (praf : PRAFunctor dom cod) ->
  {pc, pc' : PCopresheaf dom} ->
  PCMorph {j=dom} pc pc' ->
  PCMorphComponents {j=cod} (InterpPRA praf pc) (InterpPRA praf pc')
InterpPRAfmapComponents {dom=(MkPreDiag domv dome)} {cod=(MkPreDiag codv code)}
  (PRAf (PCoprshf objcod morphcod) dir fmap) (Element0 comp natural)
  i (p ** Element0 alpha alphanat) =
    (p **
     Element0
      (sliceComp comp alpha) $
      \i', j', e', funext => funExt $ \el' =>
        trans
          (cong (comp j') $ fcong (alphanat i' j' e' funext) {x=el'})
          (fcong (natural i' j' e' funext) {x=(alpha i' el')}))

public export
0 InterpPRAfmapNaturality :
  {dom, cod : PreDiagram} -> (praf : PRAFunctor dom cod) ->
  {pc, pc' : PCopresheaf dom} ->
  (m : PCMorph {j=dom} pc pc') ->
  PCMorphNaturality
    {pcpr=(InterpPRA {dom} {cod} praf pc)}
    {pcpr'=(InterpPRA {dom} {cod} praf pc')}
    (InterpPRAfmapComponents {pc} {pc'} praf m)
InterpPRAfmapNaturality {dom=(MkPreDiag domv dome)} {cod=(MkPreDiag codv code)}
  (PRAf (PCoprshf objcod morphcod) dir fmap) (Element0 comp natural)
  i j e funext = funExt $ \(p ** Element0 alpha alphanat) =>
    dpEq12 Refl $
      s0Eq12
        (funExt $ \i' => funExt $ \el => Refl)
        (funExt $ \i' => funExt $ \j' => funExt $ \e' => funExt $ \funext' =>
          uip)

public export
InterpPRAfmap : {dom, cod : PreDiagram} -> (praf : PRAFunctor dom cod) ->
  {pc, pc' : PCopresheaf dom} ->
  PCMorph {j=dom} pc pc' ->
  PCMorph {j=cod} (InterpPRA praf pc) (InterpPRA praf pc')
InterpPRAfmap praf m =
  Element0 (InterpPRAfmapComponents praf m) (InterpPRAfmapNaturality praf m)

mutual
  public export
  partial
  data PRAFmuObj : {base : PreDiagram} ->
      (praf : PRAEndoFunctor base) -> pdVert base -> Type where
    InPRAo : {0 base : PreDiagram} -> {0 praf : PRAEndoFunctor base} ->
      (0 i : pdVert base) ->
      InterpPRAobj {dom=base} {cod=base} praf (PRAFmu {base} praf) i ->
      PRAFmuObj {base} praf i

  public export
  partial
  PRAFmuMorph : {base : PreDiagram} ->
    (praf : PRAEndoFunctor base) ->
    (i, j : pdVert base) -> pdEdge base (i, j) ->
    PRAFmuObj praf i -> PRAFmuObj praf j
  PRAFmuMorph {base} praf i j e (InPRAo i x) =
    InPRAo {base} {praf} j $
      InterpPRAmorph {dom=base} {cod=base} praf (PRAFmu {base} praf) i j e x

  public export
  partial
  PRAFmu : {base : PreDiagram} ->
    (praf : PRAEndoFunctor base) ->
    PCopresheaf base
  PRAFmu {base} praf = PCoprshf {j=base} (PRAFmuObj praf) (PRAFmuMorph praf)

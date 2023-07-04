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

-----------------------------------
-----------------------------------
---- Prafunctors (Bicomodules) ----
-----------------------------------
-----------------------------------

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

public export
ElemCatObj : {j : PreDiagram} -> PCopresheaf j -> Type
ElemCatObj {j} pcpr = Sigma {a=(pdVert j)} (pcprObj pcpr)

public export
ElemCatDiagMorph : {j : PreDiagram} -> {0 pcpr : PCopresheaf j} ->
  ElemCatObj {j} pcpr -> ElemCatObj {j} pcpr -> Type
ElemCatDiagMorph {j} {pcpr} x y =
  Subset0 (pdEdge j (fst x, fst y)) $
    \e => pcprMorph pcpr (fst x) (fst y) e (snd x) = snd y

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

module LanguageDef.SlicePolyDialg

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.SlicePolyCat
import public LanguageDef.SlicePolyUMorph

-- Comma categories, algebras, coalgebras, and dialgebras of slice polynomial
-- functors.

-------------------------------------------
-------------------------------------------
---- Polynomial slice comma categories ----
-------------------------------------------
-------------------------------------------

-- See for example https://en.wikipedia.org/wiki/Comma_category .
--
-- Here we define comma categories whose (two) domains and (one) codomain are
-- all slice categories, and whose functors are polynomial.

-- The morphism component of a comma-category object.
public export
SPCommaObjMor : {a, b, c : Type} ->
  (s : SPFData a c) -> (t : SPFData b c) -> SliceObj a -> SliceObj b -> Type
SPCommaObjMor {a} {b} {c} s t sa sb =
   SliceMorphism {a=c}
    (InterpSPFData {dom=a} {cod=c} s sa)
    (InterpSPFData {dom=b} {cod=c} t sb)

public export
SPCommaObj: {a, b, c : Type} -> (s : SPFData a c) -> (t : SPFData b c) -> Type
SPCommaObj {a} {b} {c} s t =
  (sab : (SliceObj a, SliceObj b) ** SPCommaObjMor s t (fst sab) (snd sab))

-------------------------------------------------------
-------------------------------------------------------
---- Objects and morphisms of algebraic categories ----
-------------------------------------------------------
-------------------------------------------------------

-- The evaluator for a dialgebra between two slice polynomial functors,
-- whose carrier is the given slice object.
public export
SPDialgEval : {c : Type} -> (dom, cod : SPFData c c) -> SliceObj c -> Type
SPDialgEval {c} f g x = SPCommaObjMor {a=c} {b=c} {c} f g x x

public export
SPAlgEval : {c : Type} -> SPFData c c -> SliceObj c -> Type
SPAlgEval {c} = flip (SPDialgEval {c}) (SPFDid c)

public export
SPCoalgEval : {c : Type} -> SPFData c c -> SliceObj c -> Type
SPCoalgEval {c} = SPDialgEval {c} (SPFDid c)

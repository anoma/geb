module LanguageDef.SlicePolyDialg

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.SlicePolyCat
import public LanguageDef.SlicePolyUMorph

-- Algebras, coalgebras, and dialgebras of slice polynomial functors.

-------------------------------------------------------
-------------------------------------------------------
---- Objects and morphisms of algebraic categories ----
-------------------------------------------------------
-------------------------------------------------------

-- The evaluator for a dialgebra between two slice polynomial functors,
-- whose carrier is the given slice object.
public export
SPDialgEval : {c : Type} -> (dom, cod : SPFData c c) -> SliceObj c -> Type
SPDialgEval {c} f g x =
  SliceMorphism {a=c}
    (InterpSPFData {dom=c} {cod=c} f x)
    (InterpSPFData {dom=c} {cod=c} g x)

public export
SPAlgEval : {c : Type} -> SPFData c c -> SliceObj c -> Type
SPAlgEval {c} = flip (SPDialgEval {c}) (SPFDid c)

public export
SPCoalgEval : {c : Type} -> SPFData c c -> SliceObj c -> Type
SPCoalgEval {c} = SPDialgEval {c} (SPFDid c)

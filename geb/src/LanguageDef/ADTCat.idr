module LanguageDef.ADTCat

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.NatPrefixCat
import LanguageDef.PolyCat

%default total

--------------------------------------------
---- Morphisms of substitutive category ----
--------------------------------------------

public export
SubstTermAlg : MetaSOAlg Type
SubstTermAlg SO0 = Void
SubstTermAlg SO1 = ()
SubstTermAlg (x !!+ y) = Either x y
SubstTermAlg (x !!* y) = Pair x y

public export
SubstTerm : SubstObjMu -> Type
SubstTerm = substObjCata SubstTermAlg

public export
SubstContradictionAlg : MetaSOAlg Type
SubstContradictionAlg SO0 = ()
SubstContradictionAlg SO1 = Void
SubstContradictionAlg (x !!+ y) = Pair x y
SubstContradictionAlg (x !!* y) = Either x y

-- `SubstContradiction x` is inhabited if and only if `x` is uninhabited;
-- it is the dual of `SubstTerm x` (reflecting that a type is contradictory
-- if and only if it has no terms)
public export
SubstContradiction : SubstObjMu -> Type
SubstContradiction = substObjCata SubstContradictionAlg

-------------------------------------
---- Hom-objects from an algebra ----
-------------------------------------

public export
SubstHomObjAlg : MetaSOAlg (SubstObjMu -> SubstObjMu)
-- 0 -> x == 1
SubstHomObjAlg SO0 _ = Subst1
-- 1 -> x == x
SubstHomObjAlg SO1 q = q
-- (p + q) -> r == (p -> r) * (q -> r)
SubstHomObjAlg (p !!+ q) r = p r !* q r
-- (p * q) -> r == p -> q -> r
SubstHomObjAlg (p !!* q) r = p $ q r

public export
SubstHomObj' : SubstObjMu -> SubstObjMu -> SubstObjMu
SubstHomObj' = substObjCata SubstHomObjAlg

---------------------------------------------
---- Morphisms from terms of hom-objects ----
---------------------------------------------

public export
SubstMorph' : SubstObjMu -> SubstObjMu -> Type
SubstMorph' = SubstTerm .* SubstHomObj'

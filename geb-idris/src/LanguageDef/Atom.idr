module LanguageDef.Atom

import Library.IdrisUtils

%default total

-- This module implements decidable equality, ordering, and string
-- representation on an enumerated type, the one used within Geb
-- s-expressions; these are the kinds of things that a `deriving`
-- mechanism would provide automatically.

---------------------------------
---------------------------------
---- Atoms used in `GebTerm` ----
---------------------------------
---------------------------------

public export
data OldAtom : Type where
  -- Slices of the Geb S-expression type itself.
  SL_ATOM : OldAtom
  SL_NAT : OldAtom
  SL_NATL : OldAtom
  SL_EXP : OldAtom
  SL_EXPL : OldAtom

  -- Positions of the (dependent) polynomial endofunctor whose fixed point
  -- is the Geb S-expression.
  POS_Z : OldAtom
  POS_S : OldAtom
  POS_X : OldAtom
  POS_NN : OldAtom
  POS_NC : OldAtom
  POS_XN : OldAtom
  POS_XC : OldAtom

  -- Directions of the Geb S-expression endofunctor.
  DIR_S : OldAtom
  DIR_XA : OldAtom
  DIR_XNL : OldAtom
  DIR_XXL : OldAtom
  DIR_NCHD : OldAtom
  DIR_NCTL : OldAtom
  DIR_XCHD : OldAtom
  DIR_XCTL : OldAtom

  -- Finite unrefined types
  FBT_ATOM : OldAtom
  FBT_BNAT : OldAtom
  FBT_INITIAL : OldAtom
  FBT_COPRODUCT : OldAtom
  FBT_COPRODUCT_L : OldAtom
  FBT_TERMINAL : OldAtom
  FBT_PRODUCT : OldAtom
  FBT_PRODUCT_L : OldAtom

  -- Terms of finite product/coproduct types
  TERM_U : OldAtom
  TERM_L : OldAtom
  TERM_R : OldAtom
  TERM_P : OldAtom

-- The rest of this file implements enumerated-type interfaces for `OldAtom`,
-- since Idris-2 doesn't have built-in enums.

public export
GASize : Nat
GASize = 32

public export
GAFin : Type
GAFin = Fin GASize

public export
GADecoder : FinDecoder OldAtom GASize
GADecoder FZ = SL_ATOM
GADecoder (FS FZ) = SL_NAT
GADecoder (FS (FS FZ)) = SL_NATL
GADecoder (FS (FS (FS FZ))) = SL_EXP
GADecoder (FS (FS (FS (FS FZ)))) = SL_EXPL
GADecoder (FS (FS (FS (FS (FS FZ))))) = POS_Z
GADecoder (FS (FS (FS (FS (FS (FS FZ)))))) = POS_S
GADecoder (FS (FS (FS (FS (FS (FS (FS FZ))))))) = POS_X
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))) = POS_NN
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ))))))))) = POS_NC
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))) = POS_XN
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ))))))))))) =
  POS_XC
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))))) =
  DIR_S
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  FZ))))))))))))) =
    DIR_XA
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS FZ)))))))))))))) =
    DIR_XNL
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS FZ))))))))))))))) =
    DIR_XXL
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS FZ)))))))))))))))) =
    DIR_NCHD
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS FZ))))))))))))))))) =
    DIR_NCTL
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS FZ)))))))))))))))))) =
    DIR_XCHD
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS FZ))))))))))))))))))) =
    DIR_XCTL
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS FZ)))))))))))))))))))) =
    FBT_ATOM
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS FZ))))))))))))))))))))) =
    FBT_BNAT
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))))))))))))))) =
    FBT_INITIAL
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ))))))))))))))))))))))) =
    FBT_COPRODUCT
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))))))))))))))))) =
    FBT_COPRODUCT_L
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  FZ))))))))))))))))))))))))) =
    FBT_TERMINAL
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS FZ)))))))))))))))))))))))))) =
    FBT_PRODUCT
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS FZ))))))))))))))))))))))))))) =
    FBT_PRODUCT_L
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS FZ)))))))))))))))))))))))))))) =
    TERM_U
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS FZ))))))))))))))))))))))))))))) =
    TERM_L
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS FZ)))))))))))))))))))))))))))))) =
    TERM_R
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS FZ))))))))))))))))))))))))))))))) =
    TERM_P

public export
GAEncoder : NatEncoder GADecoder
GAEncoder SL_ATOM = (0 ** Refl ** Refl)
GAEncoder SL_NAT = (1 ** Refl ** Refl)
GAEncoder SL_NATL = (2 ** Refl ** Refl)
GAEncoder SL_EXP = (3 ** Refl ** Refl)
GAEncoder SL_EXPL = (4 ** Refl ** Refl)
GAEncoder POS_Z = (5 ** Refl ** Refl)
GAEncoder POS_S = (6 ** Refl ** Refl)
GAEncoder POS_X = (7 ** Refl ** Refl)
GAEncoder POS_NN = (8 ** Refl ** Refl)
GAEncoder POS_NC = (9 ** Refl ** Refl)
GAEncoder POS_XN = (10 ** Refl ** Refl)
GAEncoder POS_XC = (11 ** Refl ** Refl)
GAEncoder DIR_S = (12 ** Refl ** Refl)
GAEncoder DIR_XA = (13 ** Refl ** Refl)
GAEncoder DIR_XNL = (14 ** Refl ** Refl)
GAEncoder DIR_XXL = (15 ** Refl ** Refl)
GAEncoder DIR_NCHD = (16 ** Refl ** Refl)
GAEncoder DIR_NCTL = (17 ** Refl ** Refl)
GAEncoder DIR_XCHD = (18 ** Refl ** Refl)
GAEncoder DIR_XCTL = (19 ** Refl ** Refl)
GAEncoder FBT_ATOM = (20 ** Refl ** Refl)
GAEncoder FBT_BNAT = (21 ** Refl ** Refl)
GAEncoder FBT_INITIAL = (22 ** Refl ** Refl)
GAEncoder FBT_COPRODUCT = (23 ** Refl ** Refl)
GAEncoder FBT_COPRODUCT_L = (24 ** Refl ** Refl)
GAEncoder FBT_TERMINAL = (25 ** Refl ** Refl)
GAEncoder FBT_PRODUCT = (26 ** Refl ** Refl)
GAEncoder FBT_PRODUCT_L = (27 ** Refl ** Refl)
GAEncoder TERM_U = (28 ** Refl ** Refl)
GAEncoder TERM_L = (29 ** Refl ** Refl)
GAEncoder TERM_R = (30 ** Refl ** Refl)
GAEncoder TERM_P = (31 ** Refl ** Refl)

public export
OldAtomEncoding : FinDecEncoding OldAtom GASize
OldAtomEncoding = NatDecEncoding GADecoder GAEncoder

public export
gaToString : OldAtom -> String
gaToString SL_ATOM = "SL_ATOM"
gaToString SL_NAT = "SL_NAT"
gaToString SL_NATL = "SL_NATL"
gaToString SL_EXP = "SL_EXP"
gaToString SL_EXPL = "SL_EXPL"
gaToString POS_Z = "POS_Z"
gaToString POS_S = "POS_S"
gaToString POS_X = "POS_X"
gaToString POS_NN = "POS_NN"
gaToString POS_NC = "POS_NC"
gaToString POS_XN = "POS_XN"
gaToString POS_XC = "POS_XC"
gaToString DIR_S = "DIR_S"
gaToString DIR_XA = "DIR_XA"
gaToString DIR_XNL = "DIR_XNL"
gaToString DIR_XXL = "DIR_XXL"
gaToString DIR_NCHD = "DIR_NCHD"
gaToString DIR_NCTL = "DIR_NCTL"
gaToString DIR_XCHD = "DIR_XCHD"
gaToString DIR_XCTL = "DIR_XCTL"
gaToString FBT_ATOM = "FBT_ATOM"
gaToString FBT_BNAT = "FBT_BNAT"
gaToString FBT_INITIAL = "FBT_INITIAL"
gaToString FBT_COPRODUCT = "FBT_COPRODUCT"
gaToString FBT_COPRODUCT_L = "FBT_COPRODUCT_L"
gaToString FBT_TERMINAL = "FBT_TERMINAL"
gaToString FBT_PRODUCT = "FBT_PRODUCT"
gaToString FBT_PRODUCT_L = "FBT_PRODUCT_L"
gaToString TERM_U = "TERM_U"
gaToString TERM_L = "TERM_L"
gaToString TERM_R = "TERM_R"
gaToString TERM_P = "TERM_P"

public export
Show OldAtom where
  show a = gaToString a

public export
Eq OldAtom where
  (==) = fdeEq OldAtomEncoding

public export
Ord OldAtom where
  (<) = fdeLt OldAtomEncoding

public export
DecEq OldAtom where
  decEq = fdeDecEq OldAtomEncoding

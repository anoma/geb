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
OASize : Nat
OASize = 32

public export
OAFin : Type
OAFin = Fin OASize

public export
OADecoder : FinDecoder OldAtom OASize
OADecoder FZ = SL_ATOM
OADecoder (FS FZ) = SL_NAT
OADecoder (FS (FS FZ)) = SL_NATL
OADecoder (FS (FS (FS FZ))) = SL_EXP
OADecoder (FS (FS (FS (FS FZ)))) = SL_EXPL
OADecoder (FS (FS (FS (FS (FS FZ))))) = POS_Z
OADecoder (FS (FS (FS (FS (FS (FS FZ)))))) = POS_S
OADecoder (FS (FS (FS (FS (FS (FS (FS FZ))))))) = POS_X
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))) = POS_NN
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ))))))))) = POS_NC
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))) = POS_XN
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ))))))))))) =
  POS_XC
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))))) =
  DIR_S
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  FZ))))))))))))) =
    DIR_XA
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS FZ)))))))))))))) =
    DIR_XNL
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS FZ))))))))))))))) =
    DIR_XXL
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS FZ)))))))))))))))) =
    DIR_NCHD
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS FZ))))))))))))))))) =
    DIR_NCTL
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS FZ)))))))))))))))))) =
    DIR_XCHD
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS FZ))))))))))))))))))) =
    DIR_XCTL
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS FZ)))))))))))))))))))) =
    FBT_ATOM
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS FZ))))))))))))))))))))) =
    FBT_BNAT
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))))))))))))))) =
    FBT_INITIAL
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ))))))))))))))))))))))) =
    FBT_COPRODUCT
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))))))))))))))))) =
    FBT_COPRODUCT_L
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  FZ))))))))))))))))))))))))) =
    FBT_TERMINAL
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS FZ)))))))))))))))))))))))))) =
    FBT_PRODUCT
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS FZ))))))))))))))))))))))))))) =
    FBT_PRODUCT_L
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS FZ)))))))))))))))))))))))))))) =
    TERM_U
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS FZ))))))))))))))))))))))))))))) =
    TERM_L
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS FZ)))))))))))))))))))))))))))))) =
    TERM_R
OADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS (FS FZ))))))))))))))))))))))))))))))) =
    TERM_P

public export
OAEncoder : NatEncoder OADecoder
OAEncoder SL_ATOM = (0 ** Refl ** Refl)
OAEncoder SL_NAT = (1 ** Refl ** Refl)
OAEncoder SL_NATL = (2 ** Refl ** Refl)
OAEncoder SL_EXP = (3 ** Refl ** Refl)
OAEncoder SL_EXPL = (4 ** Refl ** Refl)
OAEncoder POS_Z = (5 ** Refl ** Refl)
OAEncoder POS_S = (6 ** Refl ** Refl)
OAEncoder POS_X = (7 ** Refl ** Refl)
OAEncoder POS_NN = (8 ** Refl ** Refl)
OAEncoder POS_NC = (9 ** Refl ** Refl)
OAEncoder POS_XN = (10 ** Refl ** Refl)
OAEncoder POS_XC = (11 ** Refl ** Refl)
OAEncoder DIR_S = (12 ** Refl ** Refl)
OAEncoder DIR_XA = (13 ** Refl ** Refl)
OAEncoder DIR_XNL = (14 ** Refl ** Refl)
OAEncoder DIR_XXL = (15 ** Refl ** Refl)
OAEncoder DIR_NCHD = (16 ** Refl ** Refl)
OAEncoder DIR_NCTL = (17 ** Refl ** Refl)
OAEncoder DIR_XCHD = (18 ** Refl ** Refl)
OAEncoder DIR_XCTL = (19 ** Refl ** Refl)
OAEncoder FBT_ATOM = (20 ** Refl ** Refl)
OAEncoder FBT_BNAT = (21 ** Refl ** Refl)
OAEncoder FBT_INITIAL = (22 ** Refl ** Refl)
OAEncoder FBT_COPRODUCT = (23 ** Refl ** Refl)
OAEncoder FBT_COPRODUCT_L = (24 ** Refl ** Refl)
OAEncoder FBT_TERMINAL = (25 ** Refl ** Refl)
OAEncoder FBT_PRODUCT = (26 ** Refl ** Refl)
OAEncoder FBT_PRODUCT_L = (27 ** Refl ** Refl)
OAEncoder TERM_U = (28 ** Refl ** Refl)
OAEncoder TERM_L = (29 ** Refl ** Refl)
OAEncoder TERM_R = (30 ** Refl ** Refl)
OAEncoder TERM_P = (31 ** Refl ** Refl)

public export
OldAtomEncoding : FinDecEncoding OldAtom OASize
OldAtomEncoding = NatDecEncoding OADecoder OAEncoder

public export
oaToString : OldAtom -> String
oaToString SL_ATOM = "SL_ATOM"
oaToString SL_NAT = "SL_NAT"
oaToString SL_NATL = "SL_NATL"
oaToString SL_EXP = "SL_EXP"
oaToString SL_EXPL = "SL_EXPL"
oaToString POS_Z = "POS_Z"
oaToString POS_S = "POS_S"
oaToString POS_X = "POS_X"
oaToString POS_NN = "POS_NN"
oaToString POS_NC = "POS_NC"
oaToString POS_XN = "POS_XN"
oaToString POS_XC = "POS_XC"
oaToString DIR_S = "DIR_S"
oaToString DIR_XA = "DIR_XA"
oaToString DIR_XNL = "DIR_XNL"
oaToString DIR_XXL = "DIR_XXL"
oaToString DIR_NCHD = "DIR_NCHD"
oaToString DIR_NCTL = "DIR_NCTL"
oaToString DIR_XCHD = "DIR_XCHD"
oaToString DIR_XCTL = "DIR_XCTL"
oaToString FBT_ATOM = "FBT_ATOM"
oaToString FBT_BNAT = "FBT_BNAT"
oaToString FBT_INITIAL = "FBT_INITIAL"
oaToString FBT_COPRODUCT = "FBT_COPRODUCT"
oaToString FBT_COPRODUCT_L = "FBT_COPRODUCT_L"
oaToString FBT_TERMINAL = "FBT_TERMINAL"
oaToString FBT_PRODUCT = "FBT_PRODUCT"
oaToString FBT_PRODUCT_L = "FBT_PRODUCT_L"
oaToString TERM_U = "TERM_U"
oaToString TERM_L = "TERM_L"
oaToString TERM_R = "TERM_R"
oaToString TERM_P = "TERM_P"

public export
Show OldAtom where
  show a = oaToString a

public export
Eq OldAtom where
  (==) = fdeEq OldAtomEncoding

public export
Ord OldAtom where
  (<) = fdeLt OldAtomEncoding

public export
DecEq OldAtom where
  decEq = fdeDecEq OldAtomEncoding

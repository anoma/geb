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
data GebAtom : Type where
  SL_ATOM : GebAtom
  SL_NAT : GebAtom
  SL_NATL : GebAtom
  SL_EXP : GebAtom
  SL_EXPL : GebAtom
  POS_A : GebAtom
  POS_Z : GebAtom
  POS_S : GebAtom
  POS_X : GebAtom
  POS_NN : GebAtom
  POS_NC : GebAtom
  POS_XN : GebAtom
  POS_XC : GebAtom
  DIR_S : GebAtom
  DIR_XA : GebAtom
  DIR_XNL : GebAtom
  DIR_XXL : GebAtom
  DIR_NCHD : GebAtom
  DIR_NCTL : GebAtom
  DIR_XCHD : GebAtom
  DIR_XCTL : GebAtom

-- The rest of this file implements enumerated-type interfaces for `GebAtom`,
-- since Idris-2 doesn't have built-in enums.

public export
GASize : Nat
GASize = 21

public export
GAFin : Type
GAFin = Fin GASize

public export
GADecoder : FinDecoder GebAtom GASize
GADecoder FZ = SL_ATOM
GADecoder (FS FZ) = SL_NAT
GADecoder (FS (FS FZ)) = SL_NATL
GADecoder (FS (FS (FS FZ))) = SL_EXP
GADecoder (FS (FS (FS (FS FZ)))) = SL_EXPL
GADecoder (FS (FS (FS (FS (FS FZ))))) = POS_A
GADecoder (FS (FS (FS (FS (FS (FS FZ)))))) = POS_Z
GADecoder (FS (FS (FS (FS (FS (FS (FS FZ))))))) = POS_S
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))) = POS_X
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ))))))))) = POS_NN
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))) = POS_NC
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ))))))))))) = POS_XN
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))))) =
  POS_XC
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ))))))))))))) =
  DIR_S
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  FZ)))))))))))))) =
    DIR_XA
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS FZ))))))))))))))) =
    DIR_XNL
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS FZ)))))))))))))))) =
    DIR_XXL
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS FZ))))))))))))))))) =
    DIR_NCHD
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS FZ)))))))))))))))))) =
    DIR_NCTL
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS FZ))))))))))))))))))) =
    DIR_XCHD
GADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS
  (FS (FS (FS (FS (FS FZ)))))))))))))))))))) =
    DIR_XCTL

public export
GAEncoder : NatEncoder GADecoder
GAEncoder SL_ATOM = (0 ** Refl ** Refl)
GAEncoder SL_NAT = (1 ** Refl ** Refl)
GAEncoder SL_NATL = (2 ** Refl ** Refl)
GAEncoder SL_EXP = (3 ** Refl ** Refl)
GAEncoder SL_EXPL = (4 ** Refl ** Refl)
GAEncoder POS_A = (5 ** Refl ** Refl)
GAEncoder POS_Z = (6 ** Refl ** Refl)
GAEncoder POS_S = (7 ** Refl ** Refl)
GAEncoder POS_X = (8 ** Refl ** Refl)
GAEncoder POS_NN = (9 ** Refl ** Refl)
GAEncoder POS_NC = (10 ** Refl ** Refl)
GAEncoder POS_XN = (11 ** Refl ** Refl)
GAEncoder POS_XC = (12 ** Refl ** Refl)
GAEncoder DIR_S = (13 ** Refl ** Refl)
GAEncoder DIR_XA = (14 ** Refl ** Refl)
GAEncoder DIR_XNL = (15 ** Refl ** Refl)
GAEncoder DIR_XXL = (16 ** Refl ** Refl)
GAEncoder DIR_NCHD = (17 ** Refl ** Refl)
GAEncoder DIR_NCTL = (18 ** Refl ** Refl)
GAEncoder DIR_XCHD = (19 ** Refl ** Refl)
GAEncoder DIR_XCTL = (20 ** Refl ** Refl)

public export
GebAtomEncoding : FinDecEncoding GebAtom GASize
GebAtomEncoding = NatDecEncoding GADecoder GAEncoder

public export
gaToString : GebAtom -> String
gaToString SL_ATOM = "SL_ATOM"
gaToString SL_NAT = "SL_NAT"
gaToString SL_NATL = "SL_NATL"
gaToString SL_EXP = "SL_EXP"
gaToString SL_EXPL = "SL_EXPL"
gaToString POS_A = "POS_A"
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

public export
Show GebAtom where
  show a = gaToString a

public export
Eq GebAtom where
  (==) = fdeEq GebAtomEncoding

public export
Ord GebAtom where
  (<) = fdeLt GebAtomEncoding

public export
DecEq GebAtom where
  decEq = fdeDecEq GebAtomEncoding

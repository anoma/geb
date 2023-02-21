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
  -- Slices of the Geb S-expression type itself.
  SL_ATOM : GebAtom
  SL_NAT : GebAtom
  SL_NATL : GebAtom
  SL_EXP : GebAtom
  SL_EXPL : GebAtom

  -- Positions of the (dependent) polynomial endofunctor whose fixed point
  -- is the Geb S-expression.
  POS_Z : GebAtom
  POS_S : GebAtom
  POS_X : GebAtom
  POS_NN : GebAtom
  POS_NC : GebAtom
  POS_XN : GebAtom
  POS_XC : GebAtom

  -- Directions of the Geb S-expression endofunctor.
  DIR_S : GebAtom
  DIR_XA : GebAtom
  DIR_XNL : GebAtom
  DIR_XXL : GebAtom
  DIR_NCHD : GebAtom
  DIR_NCTL : GebAtom
  DIR_XCHD : GebAtom
  DIR_XCTL : GebAtom

  -- Finite unrefined types
  FBT_ATOM : GebAtom
  FBT_BNAT : GebAtom

-- The rest of this file implements enumerated-type interfaces for `GebAtom`,
-- since Idris-2 doesn't have built-in enums.

public export
GASize : Nat
GASize = 22

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

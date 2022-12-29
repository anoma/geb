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
  NAT : GebAtom
  PRODUCT : GebAtom
  COPRODUCT : GebAtom

public export
GASize : Nat
GASize = 3

public export
GAFin : Type
GAFin = Fin GASize

public export
GADecoder : FinDecoder GebAtom GASize
GADecoder FZ = NAT
GADecoder (FS FZ) = PRODUCT
GADecoder (FS $ FS FZ) = COPRODUCT

public export
GAEncoder : FinEncoder GADecoder
GAEncoder NAT = (natToFinLT 0 ** Refl)
GAEncoder PRODUCT = (natToFinLT 1 ** Refl)
GAEncoder COPRODUCT = (natToFinLT 2 ** Refl)

public export
GebAtomEncoding : FinDecEncoding GebAtom GASize
GebAtomEncoding = (GADecoder ** GAEncoder)

public export
gaToString : GebAtom -> String
gaToString NAT = "#"
gaToString PRODUCT = "*"
gaToString COPRODUCT = "+"

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

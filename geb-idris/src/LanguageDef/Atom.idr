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
  PRODUCT : GebAtom
  COPRODUCT : GebAtom

public export
gaEncode : GebAtom -> Nat
gaEncode PRODUCT = 0
gaEncode COPRODUCT = 1

public export
gaDecode : Nat -> Maybe GebAtom
gaDecode 0 = Just PRODUCT
gaDecode 1 = Just COPRODUCT
gaDecode _ = Nothing

public export
gaEncodeDecodeIsJust : (a : GebAtom) -> gaDecode (gaEncode a) = Just a
gaEncodeDecodeIsJust PRODUCT = Refl
gaEncodeDecodeIsJust COPRODUCT = Refl

public export
gaToString : GebAtom -> String
gaToString PRODUCT = ":*:"
gaToString COPRODUCT = ":+:"

public export
Show GebAtom where
  show a = gaToString a

public export
gaEq : GebAtom -> GebAtom -> Bool
gaEq a a' = gaEncode a == gaEncode a'

public export
Eq GebAtom where
  (==) = gaEq

public export
Ord GebAtom where
  a < a' = gaEncode a < gaEncode a'

public export
gaDecEq : (a, a' : GebAtom) -> Dec (a = a')
gaDecEq = encodingDecEq gaEncode gaDecode gaEncodeDecodeIsJust decEq

public export
DecEq GebAtom where
  decEq = gaDecEq

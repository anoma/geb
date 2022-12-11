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
gaEncode : GebAtom -> Nat
gaEncode NAT = 0
gaEncode PRODUCT = 1
gaEncode COPRODUCT = 2

public export
gaDecode : Nat -> Maybe GebAtom
gaDecode 0 = Just NAT
gaDecode 1 = Just PRODUCT
gaDecode 2 = Just COPRODUCT
gaDecode _ = Nothing

public export
gaEncodeDecodeIsJust : (a : GebAtom) -> gaDecode (gaEncode a) = Just a
gaEncodeDecodeIsJust NAT = Refl
gaEncodeDecodeIsJust PRODUCT = Refl
gaEncodeDecodeIsJust COPRODUCT = Refl

public export
gaToString : GebAtom -> String
gaToString NAT = "#"
gaToString PRODUCT = "*"
gaToString COPRODUCT = "+"

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

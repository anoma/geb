module LanguageDef.Test.GebToposTest

import Test.TestLibrary
import LanguageDef.Test.ProgFinSetTest
import LanguageDef.GebTopos

%default total

--------------------
--------------------
---- TypeFamily ----
--------------------
--------------------

-- Type family with four types:  objects, lists of objects, morphisms,
-- and pairs of morphisms.
TFsz : Nat
TFsz = 4

-- Index of the object type.
tfObj : Fin TFsz
tfObj = natToFinLT 0

-- Index of the object-list type.
tfObjL : Fin TFsz
tfObjL = natToFinLT 1

-- Index of the morphism type.
tfMor : Fin TFsz
tfMor = natToFinLT 2

-- Index of the morphism-list type.
tfMorL : Fin TFsz
tfMorL = natToFinLT 3

-- Constructor for lists of objects.
objcL : Constructor TFsz
objcL = Ctor 0 [] 0 []

-- Constructor for finite products.
-- Takes a list of objects.
objcP : Constructor TFsz
objcP = Ctor 0 [] 0 []

-----------------------------
-----------------------------
---- Simple s-expression ----
-----------------------------
-----------------------------

ox1 : OExp
ox1 = InS BCDObjInitial [] []

ox1_fbt : Assertion
ox1_fbt = Assert $ checkAsBCDO ox1

ox1' : OExp
ox1' = InS BCDObjInitial [0] []

ox1'_nfbt : Assertion
ox1'_nfbt = Assert $ not $ checkAsBCDO ox1'

ox1'' : OExp
ox1'' = InS BCDObjInitial [] [InS BCDObjInitial [] []]

ox1''_nfbt : Assertion
ox1''_nfbt = Assert $ not $ checkAsBCDO ox1''

ox2 : OExp
ox2 = InS BCDObjTerminal [] []

ox2_fbt : Assertion
ox2_fbt = Assert $ checkAsBCDO ox2

ox3 : OExp
ox3 = InS BCDObjCoproduct [] [ox1, ox2]

ox3_fbt : Assertion
ox3_fbt = Assert $ checkAsBCDO ox3

ox3' : OExp
ox3' = InS BCDObjCoproduct [] [ox1]

ox3'_nfbt : Assertion
ox3'_nfbt = Assert $ not $ checkAsBCDO ox3'

ox3'' : OExp
ox3'' = InS BCDObjCoproduct [0, 1] [ox1, ox2]

ox3''_nfbt : Assertion
ox3''_nfbt = Assert $ not $ checkAsBCDO ox3''

ox4 : OExp
ox4 = InS BCDObjProduct [] [ox1, ox2]

ox4_fbt : Assertion
ox4_fbt = Assert $ checkAsBCDO ox4

ox5 : OExp
ox5 = InS BCDObjProduct [] [ox3, ox4]

ox5_fbt : Assertion
ox5_fbt = Assert $ checkAsBCDO ox5

ox5' : OExp
ox5' = InS BCDObjProduct [] []

ox5'_fbt : Assertion
ox5'_fbt = Assert $ not $ checkAsBCDO ox5'

ox5'' : OExp
ox5'' = InS BCDObjProduct [] [ox3', ox4]

ox5''_fbt : Assertion
ox5''_fbt = Assert $ not $ checkAsBCDO ox5''

tx6 : TExp
tx6 = InS BCDTermUnit [] []

tx6_ft : Assertion
tx6_ft = Assert $ checkAsBCDT tx6

tx7 : TExp
tx7 = InS BCDTermLeft [] [tx6]

tx7_ft : Assertion
tx7_ft = Assert $ checkAsBCDT tx7

tx8 : TExp
tx8 = InS BCDTermRight [] [tx6]

tx8_ft : Assertion
tx8_ft = Assert $ checkAsBCDT tx8

tx9 : TExp
tx9 = InS BCDTermPair [] [tx7, tx8]

tx9_ft : Assertion
tx9_ft = Assert $ checkAsBCDT tx9

tx10 : TExp
tx10 = InS BCDTermLeft [] [tx9]

tx10_ft : Assertion
tx10_ft = Assert $ checkAsBCDT tx10

--------------------------
--------------------------
---- Geb s-expression ----
--------------------------
--------------------------

gx1 : GExp
gx1 = InS FBT_INITIAL [] []

gx1_fbt : Assertion
gx1_fbt = Assert $ checkAsFinPC gx1

gx1' : GExp
gx1' = InS FBT_INITIAL [0] []

gx1'_nfbt : Assertion
gx1'_nfbt = Assert $ not $ checkAsFinPC gx1'

gx1'' : GExp
gx1'' = InS FBT_INITIAL [] [InS FBT_INITIAL [] []]

gx1''_nfbt : Assertion
gx1''_nfbt = Assert $ not $ checkAsFinPC gx1''

gx2 : GExp
gx2 = InS FBT_TERMINAL [] []

gx2_fbt : Assertion
gx2_fbt = Assert $ checkAsFinPC gx2

gx3 : GExp
gx3 = InS FBT_COPRODUCT [] [gx1, gx2]

gx3_fbt : Assertion
gx3_fbt = Assert $ checkAsFinPC gx3

gx3' : GExp
gx3' = InS FBT_COPRODUCT [] [gx1]

gx3'_nfbt : Assertion
gx3'_nfbt = Assert $ not $ checkAsFinPC gx3'

gx3'' : GExp
gx3'' = InS FBT_COPRODUCT [0, 1] [gx1, gx2]

gx3''_nfbt : Assertion
gx3''_nfbt = Assert $ not $ checkAsFinPC gx3''

gx4 : GExp
gx4 = InS FBT_PRODUCT [] [gx1, gx2]

gx4_fbt : Assertion
gx4_fbt = Assert $ checkAsFinPC gx4

gx5 : GExp
gx5 = InS FBT_PRODUCT [] [gx3, gx4]

gx5_fbt : Assertion
gx5_fbt = Assert $ checkAsFinPC gx5

gx5' : GExp
gx5' = InS FBT_PRODUCT [] []

gx5'_fbt : Assertion
gx5'_fbt = Assert $ not $ checkAsFinPC gx5'

gx5'' : GExp
gx5'' = InS FBT_PRODUCT [] [gx3', gx4]

gx5''_fbt : Assertion
gx5''_fbt = Assert $ not $ checkAsFinPC gx5''

gx6 : GExp
gx6 = InS TERM_U [] []

gx6_ft : Assertion
gx6_ft = Assert $ checkAsFinT gx6

gx7 : GExp
gx7 = InS TERM_L [] [gx6]

gx7_ft : Assertion
gx7_ft = Assert $ checkAsFinT gx7

gx8 : GExp
gx8 = InS TERM_R [] [gx6]

gx8_ft : Assertion
gx8_ft = Assert $ checkAsFinT gx8

gx9 : GExp
gx9 = InS TERM_P [] [gx7, gx8]

gx9_ft : Assertion
gx9_ft = Assert $ checkAsFinT gx9

gx10 : GExp
gx10 = InS TERM_L [] [gx9]

gx10_ft : Assertion
gx10_ft = Assert $ checkAsFinT gx10

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
gebToposTest : IO ()
gebToposTest = do
  putStrLn ""
  putStrLn "==================="
  putStrLn "Begin GebToposTest:"
  putStrLn "-------------------"
  putStrLn ""
  putStrLn "-----------------"
  putStrLn "End GebToposTest."
  putStrLn "================="
  pure ()

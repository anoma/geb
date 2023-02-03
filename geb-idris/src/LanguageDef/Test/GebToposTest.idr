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

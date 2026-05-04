module LanguageDef.Test.NockTest

import Test.TestLibrary
import LanguageDef.Nock

%default total

----------------------------------
----------------------------------
----- Exported test function -----
---------------------------------
----------------------------------

testNoun : Noun -> Formula -> Noun -> IO ()
testNoun subject formula expected =
  case eval subject formula of
    Just result =>
      if result == expected
        then putStrLn "✓ Test passed"
        else putStrLn $ "✗ Test failed: expected " ++ show expected ++
                       " but got " ++ show result
    Nothing => putStrLn "✗ Test failed: evaluation returned Nothing"

export
nockTestInternal : IO ()
nockTestInternal = do
  -- Test slot addressing
  testNoun (Cell (Atom 42) (Atom 43)) (Slot 2) (Atom 42)
  testNoun (Cell (Atom 42) (Atom 43)) (Slot 3) (Atom 43)

  -- Test quote
  testNoun (Atom 0) (Quote (Atom 42)) (Atom 42)

  -- Test increment
  testNoun (Atom 0) (Inc (Quote (Atom 41))) (Atom 42)

  -- Test equality
  testNoun (Atom 0) (Eq (Quote (Cell (Atom 1) (Atom 1)))) (Atom 0)
  testNoun (Atom 0) (Eq (Quote (Cell (Atom 1) (Atom 2)))) (Atom 1)

  -- Test conditional
  let ifTest = If (Quote (Atom 0))
                  (Quote (Atom 42))
                  (Quote (Atom 43))
  testNoun (Atom 0) ifTest (Atom 42)

export
nockTest : IO ()
nockTest = do
  putStrLn ""
  putStrLn "==============="
  putStrLn "Begin NockTest:"
  putStrLn "---------------"
  putStrLn ""
  nockTestInternal
  putStrLn ""
  putStrLn "-------------"
  putStrLn "End NockTest."
  putStrLn "============="
  pure ()

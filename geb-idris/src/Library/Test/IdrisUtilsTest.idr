module Library.Test.IdrisUtilsTest

import Test.TestLibrary
import Library.IdrisUtils

%default total

divt0 : Assertion
divt0 = Assert $ divSucc 7 3 == 1

minmodt0 : Assertion
minmodt0 = Assert $ minusModulo 3 18 12 == 0

minmodt1 : Assertion
minmodt1 = Assert $ minusModulo 3 25 12 == 1

minmodt2 : Assertion
minmodt2 = Assert $ minusModulo 3 64 53 == 2

minmodt3 : Assertion
minmodt3 = Assert $ minusModulo 3 12 18 == 0

minmodt4 : Assertion
minmodt4 = Assert $ minusModulo 3 12 25 == 2

minmodt5 : Assertion
minmodt5 = Assert $ minusModulo 3 53 64 == 1

minmodt6 : Assertion
minmodt6 = Assert $ minusModulo 13 72 18 == 2

minmodt7 : Assertion
minmodt7 = Assert $ minusModulo 9 55 77 == 5

minmodt8 : Assertion
minmodt8 = Assert $ minusModulo 201 64 139 == 126

-- Log-base-2 tests

bitsNeededTest0 : Assertion
bitsNeededTest0 = Assert $ bitsNeeded 0 == 0

bitsNeededTest1 : Assertion
bitsNeededTest1 = Assert $ bitsNeeded 1 == 1

bitsNeededTest2 : Assertion
bitsNeededTest2 = Assert $ bitsNeeded 2 == 2

bitsNeededTest3 : Assertion
bitsNeededTest3 = Assert $ bitsNeeded 3 == 2

bitsNeededTest4 : Assertion
bitsNeededTest4 = Assert $ bitsNeeded 4 == 3

bitsNeededTest5 : Assertion
bitsNeededTest5 = Assert $ bitsNeeded 5 == 3

bitsNeededTest6 : Assertion
bitsNeededTest6 = Assert $ bitsNeeded 6 == 3

bitsNeededTest7 : Assertion
bitsNeededTest7 = Assert $ bitsNeeded 7 == 3

bitsNeededTest8 : Assertion
bitsNeededTest8 = Assert $ bitsNeeded 8 == 4

bitsNeededTest15 : Assertion
bitsNeededTest15 = Assert $ bitsNeeded 15 == 4

bitsNeededTest16 : Assertion
bitsNeededTest16 = Assert $ bitsNeeded 16 == 5

export
idrisUtilsTest : IO ()
idrisUtilsTest = do
  putStrLn "Begin idrisUtilsTest:"
  putStrLn $ "expect 17 bits needed: " ++
    (show $ bitsNeeded (minus (power 2 17) 1))
  putStrLn $ "expect 18 bits needed: " ++
    (show $ bitsNeeded (power 2 17))
  putStrLn "End idrisUtilsTest."
  pure ()

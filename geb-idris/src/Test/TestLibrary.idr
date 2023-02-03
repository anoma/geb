module Test.TestLibrary

import public Library.IdrisUtils
import public Library.IdrisCategories

%default total

public export
Assertion : Type
Assertion = ()

public export
Assert : (b : Bool) -> if b then () else List ()
Assert True = ()
Assert False = []

export
testLibraryTest : IO ()
testLibraryTest = do
  -- putStrLn "Begin testLibraryTest:"
  -- putStrLn "End testLibraryTest."
  pure ()

export
showTerminated :
  {0 a : Type} -> (String -> a -> IO ()) -> (String, a) -> IO ()
showTerminated showFull (name, t) = do
  showFull name t
  putStrLn "----"

export
showList :
  {0 a : Type} -> (String -> a -> IO ()) -> List (String, a) -> IO ()
showList showFull [] = pure ()
showList showFull ts@(_ :: _) = do
  putStrLn "----"
  foldlM (const $ showTerminated showFull) () ts

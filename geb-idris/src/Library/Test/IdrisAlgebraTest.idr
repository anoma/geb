module Library.Test.IdrisAlgebraTest

import Test.TestLibrary
import Library.IdrisCategories
import Library.IdrisAlgebra

%default total

export
libraryIdrisAlgebraTest : IO ()
libraryIdrisAlgebraTest = do
  putStrLn "Begin libraryAlgebraTest:"
  putStrLn "End libraryIdrisAlgebraTest."
  pure ()

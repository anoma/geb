module Executable.Test.Main

import Test.TestLibrary
import Library.Test.IdrisUtilsTest
import Library.Test.IdrisCategoriesTest
import LanguageDef.Test.GebTest
import LanguageDef.Test.RefinedADTTest
import LanguageDef.Test.FiguresTest
import LanguageDef.Test.TheoriesTest
import LanguageDef.Test.NatPrefixCatTest
import LanguageDef.Test.ADTCatTest
import LanguageDef.Test.ProgFinSetTest
import LanguageDef.Test.DiagramCatTest
import LanguageDef.Test.AdjunctionsTest
import LanguageDef.Test.GebToposTest
import LanguageDef.Test.GenPolyFuncTest
import LanguageDef.Test.PolyCatTest
import LanguageDef.Test.PolyProfunctorTest
import LanguageDef.Test.AtomTest
import LanguageDef.Test.UniversalCategoryTest
import LanguageDef.Test.InterpretationTest
import LanguageDef.Test.SyntaxTest
import LanguageDef.Test.ExpressionTest
import LanguageDef.Test.MetaprogrammingTest
import LanguageDef.Test.LogicTest
import LanguageDef.Test.ComputationalEffectsTest
import LanguageDef.Test.EmbeddedTest
import Library.Test.CategoryTheoryTest

%default total

export
totalTests : IO ()
totalTests = do
  Test.TestLibrary.testLibraryTest
  Library.Test.IdrisUtilsTest.idrisUtilsTest
  Library.Test.IdrisCategoriesTest.libraryIdrisCategoriesTest
  LanguageDef.Test.AtomTest.languageDefAtomTest
  LanguageDef.Test.UniversalCategoryTest.languageDefUniversalCategoryTest
  LanguageDef.Test.InterpretationTest.languageDefInterpretationTest
  LanguageDef.Test.ExpressionTest.languageDefExpressionTest
  LanguageDef.Test.MetaprogrammingTest.languageDefMetaprogrammingTest
  LanguageDef.Test.LogicTest.languageDefLogicTest
  LanguageDef.Test.ComputationalEffectsTest.languageDefComputationalEffectsTest
  LanguageDef.Test.EmbeddedTest.languageDefEmbeddedTest
  Library.Test.CategoryTheoryTest.libraryCategoryTheoryTest
  LanguageDef.Test.PolyCatTest.polyCatTest
  LanguageDef.Test.NatPrefixCatTest.natPrefixCatTest
  LanguageDef.Test.PolyProfunctorTest.polyProfunctorTest
  LanguageDef.Test.ADTCatTest.adtCatTest
  LanguageDef.Test.ProgFinSetTest.progFinSetTest
  LanguageDef.Test.DiagramCatTest.diagramCatTest
  LanguageDef.Test.AdjunctionsTest.adjunctionsTest
  LanguageDef.Test.GenPolyFuncTest.genPolyFuncTest
  LanguageDef.Test.GebToposTest.gebToposTest
  LanguageDef.Test.RefinedADTTest.languageDefRefinedADTTest
  LanguageDef.Test.SyntaxTest.languageDefSyntaxTest
  LanguageDef.Test.TheoriesTest.theoriesTest
  LanguageDef.Test.FiguresTest.figuresTest
  LanguageDef.Test.GebTest.gebTest

export
partial potentiallyNonTerminatingTests : IO ()
potentiallyNonTerminatingTests = pure ()

export
partial main : IO ()
main = do
  totalTests
  potentiallyNonTerminatingTests

module Library.Test.IdrisCategoriesTest

import Test.TestLibrary
import Library.IdrisCategories

%default total

testNat0 : NatObj
testNat0 = NatOZ

testNat1 : NatObj
testNat1 = NatO1

testNat2 : NatObj
testNat2 = MetaToNatObj 2

testNat3 : NatObj
testNat3 = MetaToNatObj 3

testNat4 : NatObj
testNat4 = MetaToNatObj 4

testNat5 : NatObj
testNat5 = MetaToNatObj 5

testNat9 : NatObj
testNat9 = MetaToNatObj 9

twoLteFiveMeta : LTE 2 5
twoLteFiveMeta with (isLTE 2 5) proof p
  twoLteFiveMeta | Yes lte = lte
  twoLteFiveMeta | No nlte = case p of Refl impossible

twoLteFive : NatLTMorph (MetaToNatObj 2, MetaToNatObj 5)
twoLteFive = LTEToNatMorph {mn=(2, 5)} twoLteFiveMeta

zeroPlusThree : Assertion
zeroPlusThree = Assert $ natObjSum testNat0 testNat3 == testNat3

threePlusZero : Assertion
threePlusZero = Assert $ natObjSum testNat3 testNat0 == testNat3

twoPlusThree : Assertion
twoPlusThree = Assert $ natObjSum testNat2 testNat3 == testNat5

threePlusTwo : Assertion
threePlusTwo = Assert $ natObjSum testNat2 testNat3 == testNat5

fiveMinusTwo : Assertion
fiveMinusTwo = Assert $ natObjMinus twoLteFive == testNat3

emptyNatPrefix : PrefixArray NatOZ Nat
emptyNatPrefix = prefixArrayFromList []

exampleNatSlice : SliceArray (MetaToNatObj 4) Nat
exampleNatSlice = sliceArrayFromList 8 [0, 12, 3, 1]

exampleNatPrefix : PrefixArray (MetaToNatObj 5) Nat
exampleNatPrefix = prefixArrayFromSlice exampleNatSlice

testPrefixMap : MetaPrefixMap 3 6
testPrefixMap = InitPrefixMap 6 [2, 5, 0]

TwBidirAlg : (f, g : Type -> Type) -> Functor f -> Functor g -> Type -> Type
TwBidirAlg f g fm gm x =
  (mfg : f x -> g x ** mgf : g x -> f x **
   FunExtEq {a=(f x -> f x)} {b=(f x -> f x)} Prelude.id (mgf . mfg))

TwBidirAlgMap : (f, g : Type -> Type) ->
  (fm : Functor f) -> (gm : Functor g) ->
  (fmid : (x : Type) ->
    (map {a=x} {b=x} {f=f} (\ex : x => ex)) = (\efx : f x => efx)) ->
  (fcomp : {a, b, c : Type} -> (mbc : b -> c) -> (mab : a -> b) ->
    FunExtEq (map {f=f} (mbc . mab)) (map {f=f} mbc . map {f=f} mab)) ->
  (gmid : (x : Type) ->
    (map {a=x} {b=x} {f=g} (\ex : x => ex)) = (\egx : g x => egx)) ->
  (gcomp : {a, b, c : Type} -> (mbc : b -> c) -> (mab : a -> b) ->
    FunExtEq (map {f=g} (mbc . mab)) (map {f=g} mbc . map {f=g} mab)) ->
  (x, y : Type) -> (mxy : x -> y) -> (myx : y -> x) ->
  FunExtInverse {a=x} {b=y} mxy myx ->
  TwBidirAlg f g fm gm x -> TwBidirAlg f g fm gm y
TwBidirAlgMap f g fm gm fmid fcomp gmid gcomp x y mxy myx (eqyxy, eqxyx)
  (mfgx ** mgfx ** fgfeq) =
    (map {f=g} mxy . mfgx . map {f} myx **
     map {f} mxy . mgfx . map {f=g} myx **
     \fext =>
      funExt $ \ex =>
        rewrite sym (fcong {x=(mfgx (map myx ex))} $ gcomp myx mxy fext) in
        rewrite eqxyx fext in
        trans {a=ex}
        (sym $
         rewrite sym (fcong {x=ex} (fcomp mxy myx fext)) in
         rewrite eqyxy fext in fcong {x=ex} (fmid y))
        $ trans (cong (map mxy) $ fcong {x=((map myx ex))} (fgfeq fext))
        $ cong (map mxy . mgfx)
        $ sym (fcong {x=(mfgx (map myx ex))} (gmid x)))

export
libraryIdrisCategoriesTest : IO ()
libraryIdrisCategoriesTest = do
  putStrLn "Begin libraryIdrisCategoriesTest:"
  putStrLn $ show emptyNatPrefix
  putStrLn $ show exampleNatSlice
  putStrLn $ show exampleNatPrefix
  putStrLn $ showPrefixMap testPrefixMap
  putStrLn $ show $ fst $ testPrefixMap $ InitNatOPrefix NatOZ
  putStrLn $ show $ fst $ testPrefixMap $ InitNatOPrefix $ NatOS (NatOS (NatOZ))
  putStrLn "End libraryIdrisCategoriesTest."
  pure ()

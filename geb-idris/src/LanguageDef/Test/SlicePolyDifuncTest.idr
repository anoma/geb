module LanguageDef.Test.SlicePolyDifuncTest

import Test.TestLibrary
import LanguageDef.SlicePolyDifunc
import LanguageDef.DislicePolyCat

%default total

-- The base change, or pullback, functor internal to `PolyFunc`.
-- A natural transformation `q -> p` induces a functor from slices
-- over `p` to slices over `q`.
public export
PolyBCFtot : {p, q : PolyFunc} -> (f : PolyNatTrans q p) ->
  (r : PolyFunc) -> (sl : PolyNatTrans r p) ->
  PolyFunc
PolyBCFtot {p} {q} f r sl = pfPullbackAr {p=r} {q} {r=p} sl f

public export
PolyBCFprojOnPos : {p, q : PolyFunc} -> (f : PolyNatTrans q p) ->
  (r : PolyFunc) -> (sl : PolyNatTrans r p) ->
  pfPos (PolyBCFtot {p} {q} f r sl) -> pfPos q
PolyBCFprojOnPos {p} {q} f r sl i = snd (fst i)

public export
PolyBCFprojOnDir : {p, q : PolyFunc} -> (f : PolyNatTrans q p) ->
  (r : PolyFunc) -> (sl : PolyNatTrans r p) ->
  (i : pfPos (PolyBCFtot {p} {q} f r sl)) ->
  pfDir {p=q} (PolyBCFprojOnPos {p} {q} f r sl i) ->
  pfDir {p=(PolyBCFtot {p} {q} f r sl)} i
PolyBCFprojOnDir {p} {q} f r sl i qd x el = fst el $ Right qd

public export
PolyBCFproj : {p, q : PolyFunc} -> (f : PolyNatTrans q p) ->
  (r : PolyFunc) -> (sl : PolyNatTrans r p) ->
  PolyNatTrans (PolyBCFtot {p} {q} f r sl) q
PolyBCFproj {p} {q} f r sl =
  (PolyBCFprojOnPos {p} {q} f r sl ** PolyBCFprojOnDir {p} {q} f r sl)

public export
PolyBCFtotMapPos : {p, q : PolyFunc} -> (f : PolyNatTrans q p) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  (s : PolyFunc) -> (ssl : PolyNatTrans s p) ->
  (alpha : PolyNatTrans r s) ->
  PNTisSliceM {p} {q=r} {r=s} rsl ssl alpha ->
  pfPos (PolyBCFtot {p} {q} f r rsl) -> pfPos (PolyBCFtot {p} {q} f s ssl)
PolyBCFtotMapPos {p} {q} f r rsl s ssl (rsonpos ** rsondir) (poseq ** direq)
  ((ri, qi) ** ieq) =
    ((rsonpos ri, qi) ** trans (poseq ri) ieq)

public export
PolyBCFtotMapDir : {p, q : PolyFunc} -> (f : PolyNatTrans q p) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  (s : PolyFunc) -> (ssl : PolyNatTrans s p) ->
  (alpha : PolyNatTrans r s) ->
  (comm : PNTisSliceM {p} {q=r} {r=s} rsl ssl alpha) ->
  (i : pfPos (PolyBCFtot {p} {q} f r rsl)) ->
  pfDir {p=(PolyBCFtot {p} {q} f s ssl)}
    (PolyBCFtotMapPos {p} {q} f r rsl s ssl alpha comm i) ->
  pfDir {p=(PolyBCFtot {p} {q} f r rsl)} i
PolyBCFtotMapDir {p} {q} f r rsl s ssl (rsonpos ** rsondir) (poseq ** direq)
  ((ri, qi) ** ieq) eleq x (dmx ** dmeq) =
    eleq x
      (dmx . mapFst {f=Either} (rsondir ri) **
       \pd =>
        trans
          (cong dmx $ cong Left $ direq ri pd)
          (dmeq $ rewrite sym $ poseq ri in pd))

public export
PolyBCFtotMap : {p, q : PolyFunc} -> (f : PolyNatTrans q p) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  (s : PolyFunc) -> (ssl : PolyNatTrans s p) ->
  (alpha : PolyNatTrans r s) ->
  PNTisSliceM {p} {q=r} {r=s} rsl ssl alpha ->
  PolyNatTrans (PolyBCFtot {p} {q} f r rsl) (PolyBCFtot {p} {q} f s ssl)
PolyBCFtotMap {p} {q} f r rsl s ssl alpha comm =
  (PolyBCFtotMapPos {p} {q} f r rsl s ssl alpha comm **
   PolyBCFtotMapDir {p} {q} f r rsl s ssl alpha comm)

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
slicePolyDifuncTest : IO ()
slicePolyDifuncTest = do
  putStrLn ""
  putStrLn "==========================="
  putStrLn "Begin SlicePolyDifuncTest:"
  putStrLn "--------------------------"
  putStrLn ""
  putStrLn "------------------------"
  putStrLn "End SlicePolyDifuncTest."
  putStrLn "========================="
  pure ()

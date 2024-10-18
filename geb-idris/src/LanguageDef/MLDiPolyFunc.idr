module LanguageDef.MLDiPolyFunc

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.InternalProfunctor
import public LanguageDef.SlicePolyCat
import public LanguageDef.DiPolyFunc

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

-- Dipolynomial functors in Idris's metalanguage(s).

-------------------------------
-------------------------------
---- Objects and morphisms ----
-------------------------------
-------------------------------

public export
MLPolyDiSig : Type
MLPolyDiSig = PolyDiSig Type

public export
mlpdPos : MLPolyDiSig -> Type
mlpdPos = pdPos {c=Type}

public export
mlpdDirL : (pd : MLPolyDiSig) -> mlpdPos pd -> Type
mlpdDirL = pdDirL {c=Type}

public export
mlpdDirR : (pd : MLPolyDiSig) -> mlpdPos pd -> Type
mlpdDirR = pdDirR {c=Type}

public export
InterpMLPolyDi : MLPolyDiSig -> IntDifunctorSig Type
InterpMLPolyDi = InterpPolyDi {c=Type} TypeMor

public export
InterpMLPolyDiDiag : MLPolyDiSig -> Type -> Type
InterpMLPolyDiDiag p x = InterpMLPolyDi p x x

public export
mlipdPos : {p : MLPolyDiSig} ->
  {x, y : Type} -> InterpMLPolyDi p x y -> mlpdPos p
mlipdPos = ipdPos {c=Type} {mor=TypeMor}

public export
mlipdDirL : {p : MLPolyDiSig} ->
  {x, y : Type} -> (ipd : InterpMLPolyDi p x y) ->
  x -> mlpdDirL p (mlipdPos {p} {x} {y} ipd)
mlipdDirL = ipdDirL {c=Type} {mor=TypeMor}

public export
mlipdDirR : {p : MLPolyDiSig} ->
  {x, y : Type} -> (ipd : InterpMLPolyDi p x y) ->
  mlpdDirR p (mlipdPos {p} {x} {y} ipd) -> y
mlipdDirR = ipdDirR {c=Type} {mor=TypeMor}

public export
InterpMLPolyLmap : (p : MLPolyDiSig) ->
  IntEndoLmapSig Type TypeMor (InterpMLPolyDi p)
InterpMLPolyLmap = InterpPolyLmap {c=Type} {mor=TypeMor} typeComp

public export
InterpMLPolyRmap : (p : MLPolyDiSig) ->
  IntEndoRmapSig Type TypeMor (InterpMLPolyDi p)
InterpMLPolyRmap = InterpPolyRmap {c=Type} {mor=TypeMor} typeComp

public export
InterpMLPolyDimap : (p : MLPolyDiSig) ->
  IntEndoDimapSig Type TypeMor (InterpMLPolyDi p)
InterpMLPolyDimap = InterpPolyDimap {c=Type} {mor=TypeMor} typeComp

public export
MLPPNTonPos : (p, q : MLPolyDiSig) -> Type
MLPPNTonPos = PPNTonPos {c=Type} {mor=TypeMor}

public export
MLPPNTonL : (p, q : MLPolyDiSig) -> MLPPNTonPos p q -> Type
MLPPNTonL = PPNTonL {c=Type} {mor=TypeMor}

public export
MLPPNTonR : (p, q : MLPolyDiSig) -> MLPPNTonPos p q -> Type
MLPPNTonR = PPNTonR {c=Type} {mor=TypeMor}

public export
MLPolyParaNT : IntMorSig MLPolyDiSig
MLPolyParaNT = PolyParaNT {c=Type} TypeMor

public export
mlppntOnPos : {p, q : MLPolyDiSig} -> MLPolyParaNT p q -> MLPPNTonPos p q
mlppntOnPos = ppntOnPos {c=Type} {mor=TypeMor}

public export
mlppntOnL : {p, q : MLPolyDiSig} -> (nt : MLPolyParaNT p q) ->
  MLPPNTonL p q (mlppntOnPos {p} {q} nt)
mlppntOnL = ppntOnL {c=Type} {mor=TypeMor}

public export
mlppntOnR : {p, q : MLPolyDiSig} -> (nt : MLPolyParaNT p q) ->
  MLPPNTonR p q (mlppntOnPos {p} {q} nt)
mlppntOnR = ppntOnR {c=Type} {mor=TypeMor}

public export
0 MLParaNTinterp : (p, q : MLPolyDiSig) -> Type
MLParaNTinterp p q = TypeProfDiNT (InterpMLPolyDi p) (InterpMLPolyDi q)

public export
InterpMLPolyParaNT : {p, q : MLPolyDiSig} ->
  MLPolyParaNT p q -> MLParaNTinterp p q
InterpMLPolyParaNT = InterpPolyParaNT {c=Type} {mor=TypeMor} typeComp

-----------------------------------------
-----------------------------------------
---- Correctness/completeness proofs ----
-----------------------------------------
-----------------------------------------

------------------------
---- Paranaturality ----
------------------------

-- Here we show that our interpretation of a polynomial "paranatural" arena
-- is indeed paranatural.

public export
0 MLPolyParanaturality : {p, q : MLPolyDiSig} ->
  (nt : MLParaNTinterp p q) -> Type
MLPolyParanaturality {p} {q} =
  IntParaNTCond Type TypeMor
    (InterpMLPolyDi p) (InterpMLPolyDi q)
    (InterpMLPolyLmap p) (InterpMLPolyRmap p)
    (InterpMLPolyLmap q) (InterpMLPolyRmap q)

public export
0 MLPolyParaNTisParanatural : {p, q : MLPolyDiSig} ->
  (nt : MLPolyParaNT p q) ->
  MLPolyParanaturality {p} {q} (InterpMLPolyParaNT {p} {q} nt)
MLPolyParaNTisParanatural =
  PolyParaNTisParanatural {c=Type} {mor=TypeMor} typeComp typeAssoc

-- Here we show that our representation of paranatural transformations
-- as arenas is complete -- that is, for any paranatural transformation
-- that we can write in the metalanguage, we can derive an arena whose
-- interpretation is the given transformation.

public export
0 MLPolyParaArFromParaNT : (p, q : MLPolyDiSig) ->
  (gamma : MLParaNTinterp p q) ->
  MLPolyParanaturality {p} {q} gamma -> MLPolyParaNT p q
MLPolyParaArFromParaNT p@(ppos ** (pdirL, pdirR)) q@(qpos ** (qdirL, qdirR))
  gamma cond =
    (\pi, asn =>
      mlipdPos {p=q} (gamma (pdirL pi) (pi ** (asn, id))) **
     (\pi, asn, pdr =>
        rewrite
          sym $ dpeq1 $ cond (pdirL pi) (pdirR pi) asn
            (pi ** (asn, id))
            (pi ** (id, asn))
            Refl
        in
        mlipdDirL {p=q} (gamma (pdirR pi) (pi ** (id, asn))) pdr,
      \pi, asn =>
        mlipdDirR {p=q} (gamma (pdirL pi) (pi ** (asn, id)))))

public export
0 MLPolyParaArCompleteFst :
  (p, q : MLPolyDiSig) -> (gamma : MLParaNTinterp p q) ->
  (cond : MLPolyParanaturality {p} {q} gamma) ->
  (x : Type) ->
  (i : InterpMLPolyDiDiag p x) ->
    mlipdPos {p=q} (gamma x i) =
    mlipdPos {p=q}
      (InterpMLPolyParaNT {p} {q} (MLPolyParaArFromParaNT p q gamma cond) x i)
MLPolyParaArCompleteFst (ppos ** (pdirL, pdirR)) (qpos ** (qdirL, qdirR))
  gamma cond x (pi ** (dmr, dml)) =
    rewrite
      dpeq1 $
        cond (pdirL pi) x dml (pi ** (dmr . dml, id)) (pi ** (dmr, dml)) Refl
    in
    Refl

public export
0 MLPolyParaArCompleteL :
  (p, q : MLPolyDiSig) -> (gamma : MLParaNTinterp p q) ->
  (cond : MLPolyParanaturality {p} {q} gamma) ->
  (x : Type) ->
  (i : InterpMLPolyDiDiag p x) ->
    (mlipdDirL {p=q} (gamma x i)) =
    (rewrite MLPolyParaArCompleteFst p q gamma cond x i in
     mlipdDirL {p=q}
      (InterpMLPolyParaNT {p} {q} (MLPolyParaArFromParaNT p q gamma cond) x i))
MLPolyParaArCompleteL (ppos ** (pdirL, pdirR)) (qpos ** (qdirL, qdirR))
  gamma cond x (pi ** (dmr, dml)) =
    let
      condapp =
        cond x (pdirR pi) dmr (pi ** (dmr, dml)) (pi ** (id, dmr . dml)) Refl
    in
    trans
      (sym $
        bimapIdL1 {g=((.) dmr)} {eac=(((gamma x (pi ** (dmr, dml))) .snd))})
    $ rewrite sym (fstEqHetTy $ dpeq2 condapp) in
      trans (sym $ fstEqHet $ dpeq2 condapp) bimapIdR1

public export
0 MLPolyParaArCompleteR :
  (p, q : MLPolyDiSig) -> (gamma : MLParaNTinterp p q) ->
  (cond : MLPolyParanaturality {p} {q} gamma) ->
  (x : Type) ->
  (i : InterpMLPolyDiDiag p x) ->
    (mlipdDirR {p=q} (gamma x i)) =
    (rewrite MLPolyParaArCompleteFst p q gamma cond x i in
     mlipdDirR {p=q}
      (InterpMLPolyParaNT {p} {q} (MLPolyParaArFromParaNT p q gamma cond) x i))
MLPolyParaArCompleteR (ppos ** (pdirL, pdirR)) (qpos ** (qdirL, qdirR))
  gamma cond x (pi ** (dmr, dml)) =
    let
      condapp =
        cond (pdirL pi) x dml (pi ** (dmr . dml, id)) (pi ** (dmr, dml)) Refl
    in
    trans (sym $
      bimapIdR2 {f=((|>) dml)} {ead=(((gamma x (pi ** (dmr, dml))) .snd))})
    $
      trans
        (sndEqHet $ dpeq2 condapp)
        (rewrite (sndEqHetTy $ dpeq2 condapp) in
         bimapIdL2
          {g=((.) dml)}
          {eac=((gamma (pdirL pi) (pi ** (\x => dmr (dml x), id))) .snd)})

public export
0 MLPolyParaArComplete :
  (p, q : MLPolyDiSig) -> (gamma : MLParaNTinterp p q) ->
  (cond : MLPolyParanaturality {p} {q} gamma) ->
  (x : Type) ->
  ExtEq {a=(InterpMLPolyDiDiag p x)} {b=(InterpMLPolyDiDiag q x)}
    (gamma x)
    (InterpMLPolyParaNT {p} {q} (MLPolyParaArFromParaNT p q gamma cond) x)
MLPolyParaArComplete p@(ppos ** (pdirL, pdirR)) q@(qpos ** (qdirL, qdirR))
  gamma cond x i@(pi ** (dmr, dml)) =
    rewrite sym $ MLPolyParaArCompleteFst p q gamma cond x i in
    rewrite sym $ MLPolyParaArCompleteL p q gamma cond x i in
    rewrite dpEqPat {dp=(gamma x (pi ** (dmr, dml)))} in
    dpEq12
      Refl
    $ rewrite pairFstSnd (snd $ gamma x (pi ** (dmr, dml))) in
      pairEqCong Refl (MLPolyParaArCompleteR p q gamma cond x i)

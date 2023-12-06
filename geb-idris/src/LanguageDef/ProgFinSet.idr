module LanguageDef.ProgFinSet

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import LanguageDef.PolyCat
import public LanguageDef.Adjunctions
import public LanguageDef.Geb

%default total

----------------------------------
----------------------------------
---- Applicative binary trees ----
----------------------------------
----------------------------------

-----------------------------------
---- Well-founded (free monad) ----
-----------------------------------

public export
data BTB : Type -> Type where
  BTa : a -> BTB a
  BTp : BTB a -> BTB a -> BTB a

public export
btsz : BTB a -> Nat
btsz (BTa _) = 1
btsz (BTp l r) = btsz l + btsz r

public export
0 btszNonZero : (bt : BTB a) -> Not (btsz bt = 0)
btszNonZero (BTa v) Refl impossible
btszNonZero (BTp l r) eq = void $ btszNonZero l $ plusZeroLeftZero eq

public export
0 btlsz : List (BTB a) -> Nat
btlsz [] = 0
btlsz (bt :: bts) = btsz bt + btlsz bts

public export
btevalstack : (a -> b) -> (b -> b -> b) -> BTB a -> b
btevalstack subst alg bt = btevalsm (btsz bt) Nothing [] bt
    (plusZeroRightNeutral _) where
  public export
  algsubst : Maybe b -> a -> b
  algsubst Nothing a = subst a
  algsubst (Just x) a = alg x $ subst a

  public export
  btevalsm : (n : Nat) -> Maybe b -> (bts : List (BTB a)) -> (bt : BTB a) ->
    (0 _ : btsz bt + btlsz bts = n) -> b
  btevalsm Z _ _ bt eq = void $ btszNonZero bt $ plusZeroLeftZero eq
  btevalsm (S fuel) acc [] (BTa v) eq = algsubst acc v
  btevalsm (S fuel) acc (bt :: bts) (BTa v) eq =
    btevalsm fuel (Just $ algsubst acc v) bts bt (injective eq)
  btevalsm (S fuel) acc stack (BTp l r) eq =
    btevalsm (S fuel) acc (r :: stack) l $
      trans (plusAssociative (btsz l) (btsz r) (btlsz stack)) eq

public export
btevalcps : (a -> b) -> (b -> b -> b) -> BTB a -> b
btevalcps subst alg = btevalcont id where
  mutual
    public export
    btevalpaircont : (b -> b) -> BTB a -> BTB a -> b
    btevalpaircont cont l r = btevalcont (flip btevalcont r . (.) cont . alg) l

    public export
    btevalcont : (b -> b) -> BTB a -> b
    btevalcont cont (BTa v) = cont $ subst v
    btevalcont cont (BTp l r) = btevalpaircont cont l r

public export
bteval : (a -> b) -> (b -> b -> b) -> BTB a -> b
bteval subst alg (BTa v) = subst v
bteval subst alg (BTp l r) = alg (bteval subst alg l) (bteval subst alg r)

-- Evaluate using a monoid.
public export
btevalmon : (a -> a -> a) -> BTB a -> a
btevalmon = bteval {a} {b=a} id

-- Pattern-matching of arbitrary depth, folding to a single value
-- (not (necessarily) a tree).
public export
btgeval : BTB (a -> b) -> (b -> b -> b) -> BTB a -> b
btgeval alg mon = bteval {a} {b} (btevalmon {a=(a -> b)} (biapp mon) alg) mon

public export
btvar : a -> BTB a
btvar = BTa

public export
btcom : BTB a -> BTB a -> BTB a
btcom = BTp

-- Binding is substitution.
public export
btbind : (a -> BTB b) -> BTB a -> BTB b
btbind f = bteval f BTp

public export
btmap : (a -> b) -> BTB a -> BTB b
btmap f = btbind {a} {b} (BTa . f)

public export
btjoin : BTB (BTB a) -> BTB a
btjoin = btbind {a=(BTB a)} {b=a} id

public export
btapp : BTB (a -> b) -> BTB a -> BTB b
btapp {a} {b} = bteval {a=(a -> b)} {b=(BTB a -> BTB b)} btmap (biapp BTp)

-- Pattern-matching of arbitrary depth, folding to a tree.
public export
btgteval : BTB (a -> BTB b) -> BTB a -> BTB b
btgteval = bteval {a=(a -> BTB b)} {b=(BTB a -> BTB b)} btbind (biapp BTp)

-- Performs more substitutions than `btgteval` on the fly by composition in the
-- metalanguage.
public export
btgtsubst : BTB (a -> BTB a) -> BTB a -> BTB a
btgtsubst = bteval {a=(a -> BTB a)} {b=(BTB a -> BTB a)} (btbind {b=a}) (|>)

------------------------------------------------------------------
---- Potentially-infinite (cofree comonad) -- "binary stream" ----
------------------------------------------------------------------

public export
data BSB : Type -> Type where
  BSn : a -> Inf (BSB a) -> Inf (BSB a) -> BSB a

public export
bssub : BSB a -> (BSB a, BSB a)
bssub (BSn v l r) = (l, r)

-- The `erase` of the comonad.
public export
bslabel : BSB a -> a
bslabel (BSn v l r) = v

public export
bslmap : (a -> b) -> BSB a -> b
bslmap f = f . bslabel

public export
bstrace : (a -> b) -> (a -> (a, a)) -> a -> BSB b
bstrace subst coalg v =
  BSn
    (subst v)
    (bstrace subst coalg $ fst $ coalg v)
    (bstrace subst coalg $ snd $ coalg v)

-- The `duplicate` of the comonad.
public export
bsdup : BSB a -> BSB (BSB a)
bsdup = bstrace {a=(BSB a)} {b=(BSB a)} id bssub

public export
bsmap : (a -> b) -> BSB a -> BSB b
bsmap f = bstrace {a=(BSB a)} {b} (f . bslabel) bssub

public export
bsextend : (BSB a -> b) -> BSB a -> BSB b
bsextend f = bstrace {a=(BSB a)} {b} f bssub

public export
bsapp : BSB (a -> b) -> BSB a -> BSB b
bsapp (BSn f fl fr) (BSn v l r) = BSn (f v) (bsapp fl l) (bsapp fr r)

-- Use a well-founded binary tree to represent an arbitrarily deep
-- pattern-match on a binary stream.
public export
bsgeval : BTB (a -> b) -> (a -> b -> b -> b) -> BSB a -> b
bsgeval pat alg =
  bteval {a=(a -> b)} {b=(BSB a -> b)}
    bslmap
    (\f, g, bs => biapp (alg $ bslabel bs) f g bs)
    pat

-- Well-founded-tree-guided pattern matching, with output to a binary stream.
public export
btsapp : BTB (a -> a) -> BSB a -> BSB a
btsapp (BTa f) bs = bsmap f bs
btsapp (BTp fl fr) (BSn v l r) = BSn v (btsapp fl l) (btsapp fr r)

public export
bsnuout : BTB a -> (a -> a -> a) -> BSB () -> a
bsnuout (BTa v) alg (BSn () l r) = v
bsnuout (BTp fl fr) alg (BSn () l r) = alg (bsnuout fl alg l) (bsnuout fr alg r)

--------------------------------------------
--------------------------------------------
---- Explicitly-recursive digital topos ----
--------------------------------------------
--------------------------------------------

mutual
  public export
  data DigTObj : Type where
    DTO_0 : DigTObj
    DTO_1 : DigTObj
    DTO_C : DigTObj -> DigTObj -> DigTObj
    DTO_P : DigTObj -> DigTObj -> DigTObj
    DTO_FN : DigTObj -> DigTObj

  public export
  data DigTMorph : Type where

  public export
  data DigTEq : Type where

  public export
  data DigTNeq : Type where

  public export
  dtDomM : DigTMorph -> DigTObj
  dtDomM _ impossible

  public export
  dtCodM : DigTMorph -> DigTObj
  dtCodM _ impossible

  public export
  dtDomEq : DigTEq -> DigTObj
  dtDomEq _ impossible

  public export
  dtCodEq : DigTEq -> DigTObj
  dtCodEq _ impossible

  public export
  dtDomNeq : DigTNeq -> DigTObj
  dtDomNeq _ impossible

  public export
  dtCodNeq : DigTNeq -> DigTObj
  dtCodNeq _ impossible

mutual
  public export
  dtHomObj : DigTObj -> DigTObj -> DigTObj
  dtHomObj DTO_0 y = DTO_1
  dtHomObj DTO_1 y = y
  dtHomObj (DTO_C x x') y = DTO_P (dtHomObj x y) (dtHomObj x' y)
  dtHomObj (DTO_P x x') y = dtHomObj x (dtHomObj x' y)
  dtHomObj (DTO_FN x) y = ?dtHomObj_hole

--------------------------
--------------------------
---- "Reduced" FinSet ----
--------------------------
--------------------------

public export
data DRFSObj : Type where
  DRFS0 : DRFSObj
  DRFS1 : DRFSObj
  DRFSC : DRFSObj -> DRFSObj -> DRFSObj
  DRFSP : DRFSObj -> DRFSObj -> DRFSObj

public export
DecEq DRFSObj where
  decEq DRFS0 DRFS0 = Yes Refl
  decEq DRFS0 DRFS1 = No $ \eq => case eq of Refl impossible
  decEq DRFS0 (DRFSC _ _) = No $ \eq => case eq of Refl impossible
  decEq DRFS0 (DRFSP _ _) = No $ \eq => case eq of Refl impossible
  decEq DRFS1 DRFS0 = No $ \eq => case eq of Refl impossible
  decEq DRFS1 DRFS1 = Yes Refl
  decEq DRFS1 (DRFSC _ _) = No $ \eq => case eq of Refl impossible
  decEq DRFS1 (DRFSP _ _) = No $ \eq => case eq of Refl impossible
  decEq (DRFSC _ _) DRFS0 = No $ \eq => case eq of Refl impossible
  decEq (DRFSC _ _) DRFS1 = No $ \eq => case eq of Refl impossible
  decEq (DRFSC x y) (DRFSC x' y') = case (decEq x x', decEq y y') of
    (Yes Refl, Yes Refl) => Yes Refl
    (No neq, _) => No $ \eq => case eq of Refl => neq Refl
    (_, No neq) => No $ \eq => case eq of Refl => neq Refl
  decEq (DRFSC _ _) (DRFSP _ _) = No $ \eq => case eq of Refl impossible
  decEq (DRFSP _ _) DRFS0 = No $ \eq => case eq of Refl impossible
  decEq (DRFSP _ _) DRFS1 = No $ \eq => case eq of Refl impossible
  decEq (DRFSP _ _) (DRFSC _ _) = No $ \eq => case eq of Refl impossible
  decEq (DRFSP x y) (DRFSP x' y') = case (decEq x x', decEq y y') of
    (Yes Refl, Yes Refl) => Yes Refl
    (No neq, _) => No $ \eq => case eq of Refl => neq Refl
    (_, No neq) => No $ \eq => case eq of Refl => neq Refl

public export
Eq DRFSObj where
  x == y = isYes (decEq x y)

public export
data DDRFSTerm : DRFSObj -> Type where
  DRTu : DDRFSTerm DRFS1
  DRTl : {x : DRFSObj} -> DDRFSTerm x -> (y : DRFSObj) -> DDRFSTerm (DRFSC x y)
  DRTr : (x : DRFSObj) -> {y : DRFSObj} -> DDRFSTerm y -> DDRFSTerm (DRFSC x y)
  DRTp : {x, y : DRFSObj} -> DDRFSTerm x -> DDRFSTerm y -> DDRFSTerm (DRFSP x y)

public export
data DDRFSContra : DRFSObj -> Type where
  DRCv : DDRFSContra DRFS0
  DRCc : {x, y : DRFSObj} ->
    DDRFSContra x -> DDRFSContra y -> DDRFSContra (DRFSC x y)
  DRC1 :
    {x : DRFSObj} -> DDRFSContra x -> (y : DRFSObj) -> DDRFSContra (DRFSP x y)
  DRC2 :
    (x : DRFSObj) -> {y : DRFSObj} -> DDRFSContra y -> DDRFSContra (DRFSP x y)

public export
data DRFSLeftAdjuncts : DRFSObj -> Type where
  DLA_1 : DRFSLeftAdjuncts DRFS1
  DLA_P : {y, z : DRFSObj} ->
    DRFSLeftAdjuncts y -> DRFSLeftAdjuncts z ->
    DRFSLeftAdjuncts (DRFSP y z)

public export
data DRFSRightAdjuncts : DRFSObj -> Type where
  DRA_0 : DRFSRightAdjuncts DRFS0
  DRA_C : {x, y : DRFSObj} ->
    DRFSRightAdjuncts x -> DRFSRightAdjuncts y ->
    DRFSRightAdjuncts (DRFSC x y)
  DRA_D : {w, x, y : DRFSObj} ->
    DRFSRightAdjuncts (DRFSP w x) -> DRFSRightAdjuncts (DRFSP w y) ->
    DRFSRightAdjuncts (DRFSP w (DRFSC x y))

public export
data DDRFSMorph : DRFSObj -> DRFSObj -> Type where
  DDRMid : (x : DRFSObj) -> DDRFSMorph x x
  DDRM0 : (y : DRFSObj) -> DDRFSMorph DRFS0 y
  DDRM1 : (x : DRFSObj) -> DDRFSMorph x DRFS1
  DDRMcpR : {x, y, z : DRFSObj} -> -- right adjunct
    DDRFSMorph x z -> DDRFSMorph y z -> DDRFSMorph (DRFSC x y) z
  DDRMcpL1 : {x, y, z : DRFSObj} -> -- left adjunct (first component)
    DDRFSMorph (DRFSC x y) z -> DDRFSMorph x z
  DDRMcpL2 : {x, y, z : DRFSObj} -> -- left adjunct (second component)
    DDRFSMorph (DRFSC x y) z -> DDRFSMorph y z
  DDRMprL : {x, y, z : DRFSObj} -> -- left adjunct
    DDRFSMorph x y -> DDRFSMorph x z -> DDRFSMorph x (DRFSP y z)
  DDRMprR1 : {x, y, z : DRFSObj} -> -- right adjunct (first component)
    DDRFSMorph x (DRFSP y z) -> DDRFSMorph x y
  DDRMprR2 : {x, y, z : DRFSObj} -> -- right adjunct (second component)
    DDRFSMorph x (DRFSP y z) -> DDRFSMorph x z
  DDRMdistrib : {w, x, y, z : DRFSObj} -> -- right adjunct (left unneeded)
    -- (the other category is the Kleisli category of (w x _))
    DDRFSMorph (DRFSP w x) z -> DDRFSMorph (DRFSP w y) z ->
    DDRFSMorph (DRFSP w (DRFSC x y)) z

public export
DDRFSm0Contra : {x : DRFSObj} -> DDRFSMorph x DRFS0 -> DDRFSContra x
DDRFSm0Contra (DDRMid DRFS0) = DRCv
DDRFSm0Contra (DDRM0 DRFS0) = DRCv
DDRFSm0Contra (DDRMcpR f g) = DRCc (DDRFSm0Contra f) (DDRFSm0Contra g)
DDRFSm0Contra (DDRMcpL1 y) = ?DDRFSmContra_hole_1
DDRFSm0Contra (DDRMcpL2 y) = ?DDRFSmContra_hole_2
DDRFSm0Contra (DDRMprR1 y) = ?DDRFSmContra_hole_3
DDRFSm0Contra (DDRMprR2 y) = ?DDRFSmContra_hole_4
DDRFSm0Contra (DDRMdistrib y z) = ?DDRFSmContra_hole_5

public export
DDRFSno10 : Not (DDRFSMorph DRFS1 DRFS0)
DDRFSno10 f with (DDRFSm0Contra {x=DRFS1} f)
  DDRFSno10 f | _ impossible

public export
data UDRFSTerm : Type where
  DRFSu : UDRFSTerm
  DRFSl : UDRFSTerm -> UDRFSTerm
  DRFSr : UDRFSTerm -> UDRFSTerm
  DRFSp : UDRFSTerm -> UDRFSTerm -> UDRFSTerm

public export
DecEq UDRFSTerm where
  decEq DRFSu DRFSu = Yes Refl
  decEq DRFSu (DRFSl _) = No $ \eq => case eq of Refl impossible
  decEq DRFSu (DRFSr _) = No $ \eq => case eq of Refl impossible
  decEq DRFSu (DRFSp _ _) = No $ \eq => case eq of Refl impossible
  decEq (DRFSl _) DRFSu = No $ \eq => case eq of Refl impossible
  decEq (DRFSl t) (DRFSl t') = case decEq t t' of
    Yes Refl => Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl
  decEq (DRFSl _) (DRFSr _) = No $ \eq => case eq of Refl impossible
  decEq (DRFSl _) (DRFSp _ _) = No $ \eq => case eq of Refl impossible
  decEq (DRFSr _) DRFSu = No $ \eq => case eq of Refl impossible
  decEq (DRFSr _) (DRFSl _) = No $ \eq => case eq of Refl impossible
  decEq (DRFSr t) (DRFSr t') = case decEq t t' of
    Yes Refl => Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl
  decEq (DRFSr _) (DRFSp _ _) = No $ \eq => case eq of Refl impossible
  decEq (DRFSp _ _) DRFSu = No $ \eq => case eq of Refl impossible
  decEq (DRFSp _ _) (DRFSl _) = No $ \eq => case eq of Refl impossible
  decEq (DRFSp _ _) (DRFSr _) = No $ \eq => case eq of Refl impossible
  decEq (DRFSp t u) (DRFSp t' u') = case (decEq t t', decEq u u') of
    (Yes Refl, Yes Refl) => Yes Refl
    (No neq, _) => No $ \eq => case eq of Refl => neq Refl
    (_, No neq) => No $ \eq => case eq of Refl => neq Refl

public export
Eq UDRFSTerm where
  t == t' = isYes (decEq t t')

public export
checkDRFSTerm : DRFSObj -> UDRFSTerm -> Bool
checkDRFSTerm DRFS0 _ = False
checkDRFSTerm DRFS1 DRFSu = True
checkDRFSTerm DRFS1 _ = False
checkDRFSTerm (DRFSC x _) (DRFSl t) = checkDRFSTerm x t
checkDRFSTerm (DRFSC _ y) (DRFSr t) = checkDRFSTerm y t
checkDRFSTerm (DRFSC _ _) _ = False
checkDRFSTerm (DRFSP x y) (DRFSp t u) = checkDRFSTerm x t && checkDRFSTerm y u
checkDRFSTerm (DRFSP _ _) _ = False

public export
DRFSTermSl : SliceObj DRFSObj
DRFSTermSl x = Refinement {a=UDRFSTerm} (checkDRFSTerm x)

public export
DRFSTerm : Type
DRFSTerm = Refinement {a=(DRFSObj, UDRFSTerm)} (uncurry checkDRFSTerm)

public export
DecEq DRFSTerm where
  decEq (Element0 p eq) (Element0 p' eq') = case decEq p p' of
    Yes Refl => Yes $ rewrite uip {eq} {eq'} in Refl
    No neq => No $ \eq => case eq of Refl => neq Refl

public export
DRFSTermObj : DRFSTerm -> DRFSObj
DRFSTermObj = fst . shape

public export
DRFSTermUTerm : DRFSTerm -> UDRFSTerm
DRFSTermUTerm = snd . shape

public export
data UDRFSContra : Type where
  DRFSc : UDRFSTerm -> UDRFSContra

public export
DecEq UDRFSContra where
  decEq (DRFSc c) (DRFSc c') = case decEq c c' of
    Yes Refl => Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl

public export
Eq UDRFSContra where
  c == c' = isYes (decEq c c')

public export
checkDRFSTermAsContra : DRFSObj -> UDRFSTerm -> Bool
checkDRFSTermAsContra DRFS0 DRFSu = True
checkDRFSTermAsContra DRFS0 _ = False
checkDRFSTermAsContra DRFS1 _ = False
checkDRFSTermAsContra (DRFSC x y) (DRFSp t u) =
  checkDRFSTermAsContra x t && checkDRFSTermAsContra y u
checkDRFSTermAsContra (DRFSC _ _) _ = False
checkDRFSTermAsContra (DRFSP x _) (DRFSl t) = checkDRFSTermAsContra x t
checkDRFSTermAsContra (DRFSP _ y) (DRFSr t) = checkDRFSTermAsContra y t
checkDRFSTermAsContra (DRFSP _ _) _ = False

public export
checkDRFSContra : DRFSObj -> UDRFSContra -> Bool
checkDRFSContra x (DRFSc t) = checkDRFSTermAsContra x t

public export
DRFSContraSl : SliceObj DRFSObj
DRFSContraSl x = Refinement {a=UDRFSContra} (checkDRFSContra x)

public export
DRFSContra : Type
DRFSContra = Refinement {a=(DRFSObj, UDRFSContra)} (uncurry checkDRFSContra)

public export
DecEq DRFSContra where
  decEq (Element0 p eq) (Element0 p' eq') = case decEq p p' of
    Yes Refl => Yes $ rewrite uip {eq} {eq'} in Refl
    No neq => No $ \eq => case eq of Refl => neq Refl

public export
DRFSContraObj : DRFSContra -> DRFSObj
DRFSContraObj = fst . shape

public export
DRFSContraUContra : DRFSContra -> UDRFSContra
DRFSContraUContra = snd . shape

public export
data UDRFSMorph : Type where
  -- Identity.
  DRFSid  : DRFSObj -> UDRFSMorph

  -- Ex falso: from an uninhabited type we may form a morphism to anywhere.
  DRFSm0 : DRFSObj -> UDRFSContra -> DRFSObj -> UDRFSMorph

  -- Constant: from anywhere we may form a morphism to unit (and from there
  -- to any inhabited type by specifying a term of it).
  DRFSm1 : DRFSObj -> DRFSObj -> UDRFSTerm -> UDRFSMorph

public export
DecEq UDRFSMorph where
  decEq (DRFSid x) (DRFSid y) = case decEq x y of
    Yes Refl => Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl
  decEq (DRFSid _) (DRFSm0 _ _ _) = No $ \eq => case eq of Refl impossible
  decEq (DRFSid _) (DRFSm1 _ _ _) = No $ \eq => case eq of Refl impossible
  decEq (DRFSm0 _ _ _) (DRFSid _) = No $ \eq => case eq of Refl impossible
  decEq (DRFSm0 x c y) (DRFSm0 x' c' y') =
    case (decEq x x', decEq c c', decEq y y') of
      (Yes Refl, Yes Refl, Yes Refl) => Yes Refl
      (No neq, _, _) => No $ \eq => case eq of Refl => neq Refl
      (_, No neq, _) => No $ \eq => case eq of Refl => neq Refl
      (_, _, No neq) => No $ \eq => case eq of Refl => neq Refl
  decEq (DRFSm0 _ _ _) (DRFSm1 _ _ _) = No $ \eq => case eq of Refl impossible
  decEq (DRFSm1 _ _ _) (DRFSid _) = No $ \eq => case eq of Refl impossible
  decEq (DRFSm1 _ _ _) (DRFSm0 _ _ _) = No $ \eq => case eq of Refl impossible
  decEq (DRFSm1 x y t) (DRFSm1 x' y' t') =
    case (decEq x x', decEq y y', decEq t t') of
      (Yes Refl, Yes Refl, Yes Refl) => Yes Refl
      (No neq, _, _) => No $ \eq => case eq of Refl => neq Refl
      (_, No neq, _) => No $ \eq => case eq of Refl => neq Refl
      (_, _, No neq) => No $ \eq => case eq of Refl => neq Refl

public export
Eq UDRFSMorph where
  m == m' = isYes (decEq m m')

public export
checkDRFSMorph : DRFSObj -> DRFSObj -> UDRFSMorph -> Bool
checkDRFSMorph x y (DRFSid x') = x == x' && y == x'
checkDRFSMorph x y (DRFSm0 x' c y') = x == x' && y == y' && checkDRFSContra x' c
checkDRFSMorph x y (DRFSm1 x' y' t) = x == x' && y == y' && checkDRFSTerm x' t

public export
checkDRFSMorphCurried : (SignatureT DRFSObj, UDRFSMorph) -> Bool
checkDRFSMorphCurried ((x, y), m) = checkDRFSMorph x y m

public export
DRFSMorphSl : HomSlice DRFSObj
DRFSMorphSl (x, y) = Refinement {a=UDRFSMorph} (checkDRFSMorph x y)

public export
DRFSMorph : Type
DRFSMorph =
  Refinement {a=(SignatureT DRFSObj, UDRFSMorph)} checkDRFSMorphCurried

public export
data CRFSObj : Type where
  CRFS0 : CRFSObj
  CRFS1 : CRFSObj
  CRFSC : CRFSObj -> CRFSObj -> CRFSObj
  CRFSP : CRFSObj -> CRFSObj -> CRFSObj
  CRFSH : CRFSObj -> CRFSObj -> CRFSObj

----------------------------
---- Functorial version ----
----------------------------

-- A version of (unrefined) `FinSet` with explicit finite products
-- and explicit holes for implementing all compositions as substitutions,
-- and domains and codomains implemented through objects embedded in the
-- morphisms rather than explicit dependent types.  We also explicitly
-- distinguish terms, also known as global elements.  `FinSet` is well-pointed,
-- so the terms completely characterize the objects.  We can also distinguish
-- the duals of terms -- contradictions, which correspond to proofs that
-- their types are uninhabited (just as terms may be viewed as proofs that
-- their types are inhabited).
--
-- The functors which generate each of these classes of expressions all
-- take at least a carrier of their own type, and may also take type
-- parameters corresponding to one or me of the other classes of expressions.

public export
data RFS_Term0_F : Type -> Type where
  -- The initial object has no terms.

public export
data RFS_Contra0_F : Type -> Type where
  -- The initial object, or void type, is always provably uninhabited.
  RFS_contra : RFS_Contra0_F contr

public export
data RFS_Morph0_F : Type -> Type -> Type where
  -- A composition through `void` requires a proof that the domain type
  -- is uninhabited.  Its parameters are therefore a domain, a proof
  -- that the domain is uninhabited, and a codomain.
  RFS_absurd : obj -> contr -> obj -> RFS_Morph0_F obj contr

public export
data RFS_Term1_F : Type -> Type where
  -- The only term of the terminal object (unit type) is the unit term.
  RFS_unit : RFS_Term1_F term

public export
data RFS_Contra1_F : Type -> Type where
  -- The terminal object is never uninhabited.

-- In RFS specifically, a morphism from the terminal object is a term.
-- Therefore, a composition _through_ the terminal object is a constant.
-- The parameters of a morphism through the terminal object are therefore
-- a domain, a codomain, and a term of the codomain.
public export
data RFS_Morph1_F : Type -> Type -> Type where
  RFS_const : obj -> obj -> term -> RFS_Morph1_F obj term

------------------------------
------------------------------
---- Algebraic interfaces ----
------------------------------
------------------------------

------------------------
---- Unital magmas ----
------------------------

-- Functor which generates objects of a monoidal category.
public export
data UMagObjF : Type -> Type where
  MOu : UnitalF a -> UMagObjF a
  MOm : MagObjF a -> UMagObjF a

public export
UMagmaI : Type -> Type
UMagmaI = Algebra UMagObjF

public export
MkUMag : {0 a : Type} -> UnitalAlg a -> MagmaI a -> UMagmaI a
MkUMag ui mi (MOu uo) = ui uo
MkUMag ui mu (MOm mo) = mu mo

public export
MUu : {0 a : Type} -> UMagmaI a -> UnitalAlg a
MUu alg = alg . MOu

public export
MUm : {0 a : Type} -> UMagmaI a -> MagmaI a
MUm alg = alg . MOm

public export
UMagU : {a : Type} -> UMagmaI a -> a
UMagU = Uu . MUu

public export
UMagM : {a : Type} -> UMagmaI a -> a -> a -> a
UMagM = Mb . MUm

public export
UMagObjFM : Type -> Type
UMagObjFM = FreeMonad UMagObjF

-- The free monad of `UMagObjF` implements the unital magma interface.
public export
UMagObjFUMI : (a : Type) -> UMagmaI (UMagObjFM a)
UMagObjFUMI a =  inFC {a}

----------------------------
---- Dual unital magmas ----
----------------------------

public export
data DUMagObjF : Type -> Type where
  UM1 : UMagObjF a -> DUMagObjF a
  UM2 : UMagObjF a -> DUMagObjF a

public export
DUMagmaI : Type -> Type
DUMagmaI = Algebra DUMagObjF

public export
MkDUMag : {0 a : Type} -> UMagmaI a -> UMagmaI a -> DUMagmaI a
MkDUMag um1 um2 (UM1 um) = um1 um
MkDUMag um1 um2 (UM2 um) = um2 um

public export
DU1 : {0 a : Type} -> DUMagmaI a -> UMagmaI a
DU1 alg = alg . UM1

public export
DU2 : {0 a : Type} -> DUMagmaI a -> UMagmaI a
DU2 alg = alg . UM2

public export
DUMagU1 : {a : Type} -> DUMagmaI a -> a
DUMagU1 = UMagU . DU1

public export
DUMagM1 : {a : Type} -> DUMagmaI a -> a -> a -> a
DUMagM1 = UMagM . DU1

public export
DUMagU2 : {a : Type} -> DUMagmaI a -> a
DUMagU2 = UMagU . DU2

public export
DUMagM2 : {a : Type} -> DUMagmaI a -> a -> a -> a
DUMagM2 = UMagM . DU2

public export
DUMagObjFM : Type -> Type
DUMagObjFM = FreeMonad DUMagObjF

public export
DUMagObjFUMI : (a : Type) -> DUMagmaI (DUMagObjFM a)
DUMagObjFUMI a = inFC {a}

---------------
---- Sized ----
---------------

public export
data SizedF : Type -> Type where
  Ssz : Nat -> SizedF a

public export
SizedI : Type -> Type
SizedI = Coalgebra SizedF

public export
SIsz : {0 a : Type} -> SizedI a -> a -> Nat
SIsz {a} coalg x with (coalg x)
  SIsz {a} coalg x | Ssz l = l

public export
SizedCFCM : Type -> Type
SizedCFCM = CofreeComonad SizedF

public export
SizedCFCMI : (a : Type) -> SizedI (SizedCFCM a)
SizedCFCMI a = outCFC {f=SizedF} {a}

public export
SizedIF : (Type -> Type) -> Type
SizedIF f = NaturalTransformation f (SizedF . f)

public export
SizedIFtoI : {0f : Type -> Type} -> SizedIF f -> (a : Type) -> SizedI (f a)
SizedIFtoI {f} sz a fx = sz a fx

-------------------
---- Indexable ----
-------------------

public export
data IndexableI : (f : Type -> Type) -> SizedIF f -> Type where
  Iidx : {0 f : Type -> Type} -> {0 sz : SizedIF f} ->
    ({0 a : Type} -> (fx : f a) -> (i : Nat) ->
     (ok : LT i (SIsz {a=(f a)} (sz a) fx)) -> a) ->
    IndexableI f sz

public export
IxSz : {0 f : Type -> Type} -> {sz : SizedIF f} -> IndexableI f sz ->
  {a : Type} -> f a -> Nat
IxSz {f} {sz} (Iidx {f} {sz} idx) {a} fx = SIsz {a=(f a)} (sz a) fx

public export
IxI : {0 f : Type -> Type} -> {0 sz : SizedIF f} -> (ixi : IndexableI f sz) ->
  {0 a : Type} -> (fx : f a) -> (i : Nat) ->
  (ok : LT i (IxSz {f} {sz} ixi {a} fx)) -> a
IxI {f} {sz} (Iidx {f} {sz} idx) {a} fx i ok = idx {a} fx i ok

--------------
---- List ----
--------------

-- `List` itself (as opposed to the functor which _generates_ a list of a
-- given type, `ListF a` for any `a`) can be treated as an interface:  that
-- of a type of which any list of terms can be treated as a (single) term.
-- We call this `ListH` where the `H` is for "higher-order".
public export
ListHI : Type -> Type
ListHI = Algebra List

public export
ListHIL : {a : Type} -> ListHI a -> List a -> a
ListHIL {a} = Prelude.id {a=(Algebra List a)}

public export
ListHFM : Type -> Type
ListHFM = FreeMonad List

public export
ListHFMI : (a : Type) -> ListHI (ListHFM a)
ListHFMI a = inFC {f=List} {a}

-- A type that implements the unital magma interface also implements
-- the ListH interface.
public export
LHIfromUMI : {a : Type} -> UMagmaI a -> ListHI a
LHIfromUMI {a} um =
  foldl {t=List} {acc=a} {elem=a} (UMagM {a} um) (UMagU {a} um)

-- A type that implements the ListH interface also implements the
-- unital magma interface.
public export
UMIfromLHI : {a : Type} -> ListHI a -> UMagmaI a
UMIfromLHI {a} li (MOu UOu) = li []
UMIfromLHI {a} li (MOm (MOb x y)) = li [x, y]

---------------------------
---- Internal diagrams ----
---------------------------

---------------------------------------------
---------------------------------------------
---- Algebraic interface implementations ----
---------------------------------------------
---------------------------------------------

--------------
---- Unit ----
--------------

public export
UnitUI : UnitalAlg Unit
UnitUI = MkU ()

--------------
---- List ----
--------------

-- For any `a`, `List a` implements the ListH interface itself:  a list of lists
-- may be treated as a list by concatenating them all.
public export
ListLHI : (a : Type) -> ListHI (List a)
ListLHI a = concat {a=(List a)} {t=List}

-- `List a` implements the unital interface.
public export
ListUI : (a : Type) -> UnitalAlg (List a)
ListUI a = MkU []

-- `List a` implements the magma interface.
public export
ListMagI : (a : Type) -> MagmaI (List a)
ListMagI a = MkMag (++)

-- `List a` implements the unital magma interface.
public export
ListUMI : (a : Type) -> UMagmaI (List a)
ListUMI a = MkUMag (ListUI a) (ListMagI a)

-- `List` implements the Sized interface.
public export
ListSzI : SizedIF List
ListSzI a l = Ssz (length l)

-- `List` implements the Indexable interface.
public export
ListIdxI : IndexableI List ListSzI
ListIdxI = Iidx {f=List} {sz=ListSzI} $
  \fx, i, ok => index' fx (natToFinLT i)

--------------------------------------------------
--------------------------------------------------
---- Categorial universal-property interfaces ----
--------------------------------------------------
--------------------------------------------------

----------------------------------
---- Categories from diagrams ----
----------------------------------

public export
CatMorphF : {a : Type} -> HomEndofunctor a
CatMorphF {a} = CatHomF {obj=a}

public export
CategoryI : {a : Type} -> HomSlice a -> Type
CategoryI {a} = SliceAlg {a=(SignatureT a)} (CatMorphF {a})

public export
CatI : {a : Type} -> {h : HomSlice a} ->
  ((x : a) -> h (x, x)) ->
  ({x, y, z : a} -> h (y, z) -> h (x, y) -> h (x, z)) ->
  CategoryI {a} h
CatI {a} {h} cid ccomp (x, x) (CHId x) = cid x
CatI {a} {h} cid ccomp (x, z) (CHComp {x} {y} {z} g f) = ccomp g f

public export
ciId : {a : Type} -> {h : HomSlice a} -> CategoryI {a} h -> (x : a) -> h (x, x)
ciId {a} {h} alg x = alg (x, x) $ CHId x

public export
ciComp : {a : Type} -> {h : HomSlice a} -> CategoryI {a} h ->
  {x, y, z : a} -> h (y, z) -> h (x, y) -> h (x, z)
ciComp {a} {h} alg {x} {y} {z} g f = alg (x, z) $ CHComp g f

public export
CatMorphFM : {a : Type} -> HomEndofunctor a
CatMorphFM {a} = FreeHomM a

public export
CatMorphFMI : {a : Type} -> (h : HomSlice a) -> CategoryI {a} (CatMorphFM {a} h)
CatMorphFMI {a} h sig =
  InSlFc {f=(CatMorphF {a})} {a=(SignatureT a)} {sa=h} {ea=sig}

public export
HomInterface : Type -> Type
HomInterface a = SliceObj (HomSlice a)

-- Morphisms which can be derived in any category which implements
-- the given (universal-morphism) interface.
public export
DerivedF : {a : Type} -> HomInterface a -> Type
DerivedF {a} iface =
  (h : HomSlice a) -> CategoryI {a} h -> iface h -> HomSlice a

-- The signature of the implementation of one universal-morphism interface
-- in terms of another.
public export
ImplementationI : {a : Type} -> {iface : HomInterface a} ->
  (dom, cod : DerivedF {a} iface) ->
  (h : HomSlice a) -> CategoryI {a} h -> iface h -> Type
ImplementationI {a} {iface} dom cod h cat impl =
  SliceMorphism {a=(SignatureT a)} (dom h cat impl) (cod h cat impl)

-- The signature of an interface to morphisms derivable from a given
-- (universal-morphism) interface.
public export
DerivedI : {a : Type} -> {iface : HomInterface a} ->
  DerivedF {a} iface -> (h : HomSlice a) -> CategoryI {a} h -> iface h -> Type
DerivedI {a} {iface} diface = ImplementationI {a} {iface} diface (\h, _, _ => h)

-- The implementation of one universal-morphism interface in terms of another.
public export
ImplementationF : {a : Type} -> (dom, cod : HomInterface a) -> Type
ImplementationF {a} dom cod =
  (h : HomSlice a) -> CategoryI {a} h -> dom h -> cod h

--------------------------
---- Terminal objects ----
--------------------------

-- The morphism interface of a terminal object, where `u` is the object
-- component.
public export
data TermMorphF : {a : Type} -> (u : UnitalAlg a) -> HomEndofunctor a where
  TM1 : (x : a) -> TermMorphF {a} u h (x, Uu u)

public export
TerminalI : {a : Type} -> UnitalAlg a -> HomSlice a -> Type
TerminalI {a} u = SliceAlg {a=(SignatureT a)} (TermMorphF {a} u)

public export
TermI : {a : Type} -> {u : UnitalAlg a} -> {h : HomSlice a} ->
  ((x : a) -> h (x, Uu u)) -> TerminalI {a} u h
TermI {a} {u} {h} tid (x, Uu u) (TM1 x) = tid x

public export
TermMorphFM : {a : Type} -> (u : UnitalAlg a) -> HomEndofunctor a
TermMorphFM {a} u = SliceFreeM (TermMorphF {a} u)

public export
TermMorphFMI : {a : Type} -> (u : UnitalAlg a) -> (h : HomSlice a) ->
  TerminalI {a} u (TermMorphFM {a} u h)
TermMorphFMI {a} u h sig =
  InSlFc {f=(TermMorphF {a} u)} {a=(SignatureT a)} {sa=h} {ea=(sig)}

-------------------------
---- Initial objects ----
-------------------------

-- The morphism interface of an initial object, where `u` is the object
-- component.
public export
data InitMorphF : {a : Type} -> (u : UnitalAlg a) -> HomEndofunctor a where
  IM0 : (x : a) -> InitMorphF {a} u h (Uu u, x)

public export
InitialI : {a : Type} -> UnitalAlg a -> HomSlice a -> Type
InitialI {a} u = SliceAlg {a=(SignatureT a)} (InitMorphF {a} u)

public export
InitI : {a : Type} -> {u : UnitalAlg a} -> {h : HomSlice a} ->
  ((x : a) -> h (Uu u, x)) -> InitialI {a} u h
InitI {a} {u} {h} iid (Uu u, x) (IM0 x) = iid x

public export
InitMorphFM : {a : Type} -> (u : UnitalAlg a) -> HomEndofunctor a
InitMorphFM {a} u = SliceFreeM (InitMorphF {a} u)

public export
InitMorphFMI : {a : Type} -> (u : UnitalAlg a) -> (h : HomSlice a) ->
  InitialI {a} u (InitMorphFM {a} u h)
InitMorphFMI {a} u h sig =
  InSlFc {f=(InitMorphF {a} u)} {a=(SignatureT a)} {sa=h} {ea=(sig)}

------------------
---- Products ----
------------------

-- If the terms of `a` and `b` are the objects of two categories,
-- `h` is a profunctor `a |-> b` internal to `Type`, then for each pair of
-- objects in `b`, this produces the contravariant functor internal to
-- `Type` resulting from taking the product of the contravariant functors
-- represented by each of the pair of objects in `b`.
--
-- In particular, if `b` is `a`, `a` has products, and `h` is the hom-functor
-- of `a` internal to `Type`, then this is the contravariant hom-functor
-- represented by (i.e. into) a product in `a`.
public export
PPContraHomT : {0 a, b : Type} -> (h : a -> b -> Type) -> (b, b) -> a -> Type
PPContraHomT {a} {b} = PPContraHom {a} {b} {c=Type} {d=Type} Pair

-- The counit of the diagonal/product adjunction between `(Type, Type)`
-- and `Type`.
public export
ProdCounit : (a, b : Type) -> ((a, b) -> a, (a, b) -> b)
ProdCounit a b = (fst {a} {b}, snd {a} {b})

public export
data ProdMorphF : {a : Type} -> (mag : MagmaI a) -> HomEndofunctor a where
  PMPair :
    PPContraHomT {a} {b=a} (curry h) (y, z) x ->
    ProdMorphF mag h (x, Mb mag y z)
  PMProj1 : (x, y : a) -> ProdMorphF mag h (Mb mag x y, x)
  PMProj2 : (x, y : a) -> ProdMorphF mag h (Mb mag x y, y)

public export
ProductI : {a : Type} -> MagmaI a -> HomSlice a -> Type
ProductI {a} m = SliceAlg {a=(SignatureT a)} (ProdMorphF {a} m)

public export
ProdMorphFM : {a : Type} -> (mag : MagmaI a) -> HomEndofunctor a
ProdMorphFM {a} mag = SliceFreeM (ProdMorphF {a} mag)

public export
ProdMorphFMI : {a : Type} -> (mag : MagmaI a) -> (h : HomSlice a) ->
  ProductI {a} mag (ProdMorphFM {a} mag h)
ProdMorphFMI {a} mag h sig =
  InSlFc {f=(ProdMorphF {a} mag)} {a=(SignatureT a)} {sa=h} {ea=sig}

-- Morphisms which can be implemented in any category with pairwise products.
public export
data ProdLibF : {a : Type} -> {mag : MagmaI a} ->
    DerivedF {a} (ProductI {a} mag) where
  -- Products commute in any category.
  PLSwap : {0 a : Type} -> {0 mag : MagmaI a} -> {0 h : HomSlice a} ->
    {0 cat : CategoryI {a} h} -> {0 prod : ProductI {a} mag h} ->
    (x, y : a) -> ProdLibF {a} {mag} h cat prod (Mb mag x y, Mb mag y x)

public export
ProdLibI : {a : Type} -> {mag : MagmaI a} -> {h : HomSlice a} ->
  CategoryI {a} h -> ProductI {a} mag h -> Type
ProdLibI {a} {mag} {h} = DerivedI {a} (ProdLibF {a} {mag}) h

-- Default implementations for `ProdLibI`, which require only an implementation
-- of `ProductI`.

public export
swapProd : {a : Type} ->
  (mag : MagmaI a) -> (h : HomSlice a) ->
  ProductI {a} mag h ->
  (x, y : a) -> h (Mb mag x y, Mb mag y x)
swapProd {a} mag h prod x y = prod (_, _) $
  PMPair (prod (_, _) $ PMProj2 x y, prod (_, _) $ PMProj1 x y)

public export
ProdLibDefault : {a : Type} -> {mag : MagmaI a} -> {h : HomSlice a} ->
  (cat : CategoryI {a} h) -> (prod : ProductI {a} mag h) ->
  ProdLibI {a} {mag} {h} cat prod
ProdLibDefault {a} {mag} {h} cat prod (_, _) (PLSwap x y) =
  swapProd {a} mag h prod x y

--------------------
---- Coproducts ----
--------------------

-- A specialization of `PCCovarHom` where the hom-functor is internal to
-- `Type`. In particular, if additionally `b` is `a` and `h` is the hom-functor
-- of `a` internal to `Type`, then this returns the covariant hom-functor
-- represented by a pairwise coproduct of objects of `a` (hence `PCHomT` --
-- "pairwise coproduct hom-object in `Type`").
public export
PCCovarHomT : {0 a, b : Type} -> (h : a -> b -> Type) -> (a, a) -> b -> Type
PCCovarHomT {a} {b} = PCCovarHom {a} {b} {c=Type} {d=Type} Pair

-- A specialization of `PCCovarHom` where the hom-functor is internal to
-- `a`, and `a` has products (given by `p`).  In this case, if the category also
-- has coproducts (that is, if it is bicartesian closed), then this produces the
-- internal covariant hom-functor out of a coproduct.
public export
BCCCovarHom : {0 a : Type} ->
  (p : a -> a -> a) -> (h : a -> a -> a) -> (a, a) -> a -> a
BCCCovarHom {a} = PCCovarHom {a} {b=a} {c=a} {d=a}

-- The morphism interface of a coproduct, where `mag` is the object component.
public export
data CoprodMorphF : {a : Type} -> (mag : MagmaI a) -> HomEndofunctor a where
  CMInjL : (x, y : a) -> CoprodMorphF mag h (x, Mb mag x y)
  CMInjR : (x, y : a) -> CoprodMorphF mag h (y, Mb mag x y)
  CMCase :
    PCCovarHomT {a} {b=a} (curry h) (x, y) z ->
    CoprodMorphF mag h (Mb mag x y, z)

public export
CoproductI : {a : Type} -> MagmaI a -> HomSlice a -> Type
CoproductI {a} m = SliceAlg {a=(SignatureT a)} (CoprodMorphF {a} m)

public export
CoprodMorphFM : {a : Type} -> (mag : MagmaI a) -> HomEndofunctor a
CoprodMorphFM {a} mag = SliceFreeM (CoprodMorphF {a} mag)

public export
CoprodMorphFMI : {a : Type} -> (mag : MagmaI a) -> (h : HomSlice a) ->
  CoproductI {a} mag (CoprodMorphFM {a} mag h)
CoprodMorphFMI {a} mag h sig =
  InSlFc {f=(CoprodMorphF {a} mag)} {a=(SignatureT a)} {sa=h} {ea=sig}

-------------------------
---- Finite products ----
-------------------------

-- If `a` and `b` are types of the objects of categories, `h` is a
-- profunctor `a |-> b` internal to the monoidal category `c` with
-- unit `u` and tensor product `p`, then this returns the contravariant
-- functor from `a` to `c` represented by a finite product in `b`
-- (assuming `b` has finite products).
public export
FPContraHom : {0 a, b, c : Type} -> UMagmaI c ->
  (h : a -> b -> c) -> UMagObjF b -> a -> c
FPContraHom {a} {b} {c} umag h (MOu UOu) x =
  ContravarTerm {a} {b} {c} {d=c} (MkU $ Uu $ MUu umag) h x
FPContraHom {a} {b} {c} umag h (MOm (MOb y z)) x =
  PPContraHom {a} {b} {c} {d=c} (Mb $ MUm umag) h (y, z) x

-- If `c` has finite products, then the contravariant hom-functor
-- represented by a finite product in `b` may be internal to `c`
-- (`c`'s unit produces the contravariant functor represented by `b`'s unit,
-- and `c`'s product produces the contravariant functor represented
-- by `b`'s product).
public export
FPContraHomI : {0 a, b, c : Type} ->
  (h : a -> b -> c) -> UMagObjF b -> a -> UMagObjF c
FPContraHomI {a} {b} {c} h (MOu UOu) x =
  ContravarTerm {a} {b} {c} {d=(UMagObjF c)} (MkU $ MOu UOu) h x
FPContraHomI {a} {b} {c} h (MOm (MOb y z)) x =
  PPContraHom {a} {b} {c} {d=(UMagObjF c)} (MOm .* MOb) h (y, z) x

-- If `a` is a type of objects, `UMagObjF a` is interpreted as a type of
-- finite products, and `h x` is the covariant hom-functor represented by
-- `x` for any `x : a` (where the hom-functor itself is internal to a category
-- with objects in `b`), then this returns the covariant hom-functor represented
-- by a finite product.
public export
FPCovarHom : {0 a, b : Type} -> (h : a -> b -> b) -> UMagObjF a -> b -> b
FPCovarHom {a} {b} h (MOu UOu) x = CovarTerm {a} {b} h x
FPCovarHom {a} {b} h (MOm (MOb x y)) z = PPCovarHom {a} {b} h (x, y) z

-- A specialization of `FPCovarHom` where `b` is `Type`:  in this case, the
-- hom-functor is internal to `Type`.
public export
FPCovarHomT : {0 a : Type} ->
  (h : a -> Type -> Type) -> UMagObjF a -> Type -> Type
FPCovarHomT {a} = FPCovarHom {a} {b=Type}

-- If a type has a terminal object and pairwise products, then we say
-- it has all finite products.
public export
data FinProdMorphF : {a : Type} -> (umag : UMagmaI a) -> HomEndofunctor a where
  FPFTerm : {0 a : Type} -> {0 umag : UMagmaI a} ->
    {0 h : HomSlice a} -> {0 x, y : a} ->
    TermMorphF {a} (MUu umag) h (x, y) -> FinProdMorphF {a} umag h (x, y)
  FPFProd : {0 a : Type} -> {0 umag : UMagmaI a} ->
    {0 h : HomSlice a} -> {0 x, y : a} ->
    ProdMorphF {a} (MUm umag) h (x, y) -> FinProdMorphF {a} umag h (x, y)

---------------------------
---- Finite coproducts ----
---------------------------

-- If `a` and `b` are types of the objects of categories, `h` is a
-- profunctor `a |-> b` internal to the monoidal category `c` with
-- unit `u` and tensor product `p`, then this returns the covariant
-- functor from `a` to `c` represented by a finite coproduct in `b`
-- (assuming `b` has finite coproducts).
public export
FCCovarHom : {0 a, b, c : Type} -> UMagmaI c ->
  (h : a -> b -> c) -> UMagObjF a -> b -> c
FCCovarHom {a} {b} {c} umag h (MOu UOu) x =
  CovarInit {a} {b} {c} {d=c} (MkU $ Uu $ MUu umag) h x
FCCovarHom {a} {b} {c} umag h (MOm (MOb x y)) z =
  PCCovarHom {a} {b} {c} {d=c} (Mb $ MUm umag) h (x, y) z

-- If `c` has finite products, then the covariant hom-functor
-- represented by a finite coproduct in `a` may be internal to `c`
-- (`c`'s unit produces the covariant functor represented by `a`'s void,
-- and `c`'s product produces the covariant functor represented
-- by `a`'s coproduct).
public export
FCCovarHomI : {0 a, b, c : Type} ->
  (h : a -> b -> c) -> UMagObjF a -> b -> UMagObjF c
FCCovarHomI {a} {b} {c} h (MOu UOu) x =
  CovarInit {a} {b} {c} {d=(UMagObjF c)} (MkU $ MOu UOu) h x
FCCovarHomI {a} {b} {c} h (MOm (MOb x y)) z =
  PCCovarHom {a} {b} {c} {d=(UMagObjF c)} (MOm .* MOb) h (x, y) z

-- If a type has an initial object and pairwise coproducts, then we say
-- it has all finite coproducts.
public export
data FinCoprodMorphF : {a : Type} -> (umag : UMagmaI a) ->
    HomEndofunctor a where
  FCPFTerm : {0 a : Type} -> {0 umag : UMagmaI a} ->
    {0 h : HomSlice a} -> {0 x, y : a} ->
    InitMorphF {a} (MUu umag) h (x, y) -> FinCoprodMorphF {a} umag h (x, y)
  FPFCoprod : {0 a : Type} -> {0 umag : UMagmaI a} ->
    {0 h : HomSlice a} -> {0 x, y : a} ->
    CoprodMorphF {a} (MUm umag) h (x, y) -> FinCoprodMorphF {a} umag h (x, y)

------------------------
---- Distributivity ----
------------------------

-- If a category has products and coproducts, then we can define in it
-- a notion of distributivity of products over coproducts.
public export
data DistribMorphF : {a : Type} -> (prod : MagmaI a) -> (coprod : MagmaI a) ->
    HomEndofunctor a where
  DMDist : (x, y, z : a) ->
    DistribMorphF prod coprod h
      (Mb prod x (Mb coprod y z), Mb coprod (Mb prod x y) (Mb prod x z))

public export
DistributiveI : {a : Type} -> MagmaI a -> MagmaI a -> HomSlice a -> Type
DistributiveI {a} prod coprod =
  SliceAlg {a=(SignatureT a)} (DistribMorphF {a} prod coprod)

public export
DistribMorphFM : {a : Type} -> (prod, coprod : MagmaI a) -> HomEndofunctor a
DistribMorphFM {a} prod coprod = SliceFreeM (DistribMorphF {a} prod coprod)

public export
DistribMorphFMI : {a : Type} -> (prod, coprod : MagmaI a) -> (h : HomSlice a) ->
  DistributiveI {a} prod coprod (DistribMorphFM {a} prod coprod h)
DistribMorphFMI {a} prod coprod h sig =
  InSlFc {f=(DistribMorphF {a} prod coprod)} {a=(SignatureT a)} {sa=h} {ea=sig}

------------------------------------
---- Hom-objects (exponentials) ----
------------------------------------

-- A specialization of `FPCovarHom` where `b` is `a`:  in this case, the
-- hom-functor is internal to a category, which, since the category also
-- has finite products (a prerequisite of using `FPCovarHom`), means that
-- the category is cartesian closed.
public export
CCPHom : {0 a : Type} -> (h : a -> a -> a) -> UMagObjF a -> a -> a
CCPHom {a} = FPCovarHom {a} {b=a}

public export
data CCMorphF : {a : Type} -> (prod : MagmaI a) -> (hom : MagmaI a) ->
    HomEndofunctor a where
  CCCurry : {x, y, z : a} ->
    h (Mb prod x y, z) -> CCMorphF prod hom h (x, Mb hom y z)
  CCEval : (x, y : a) -> CCMorphF prod hom h (Mb prod (Mb hom x y) x, y)

public export
CartClosedI : {a : Type} -> MagmaI a -> MagmaI a -> HomSlice a -> Type
CartClosedI {a} prod hom = SliceAlg {a=(SignatureT a)} (CCMorphF {a} prod hom)

public export
CCMorphFM : {a : Type} -> (prod, hom : MagmaI a) -> HomEndofunctor a
CCMorphFM {a} prod hom = SliceFreeM (CCMorphF {a} prod hom)

public export
CCMorphFMI : {a : Type} -> (prod, hom : MagmaI a) -> (h : HomSlice a) ->
  CartClosedI {a} prod hom (CCMorphFM {a} prod hom h)
CCMorphFMI {a} prod hom h sig =
  InSlFc {f=(CCMorphF {a} prod hom)} {a=(SignatureT a)} {sa=h} {ea=sig}

--------------------------------
---- Finite data structures ----
--------------------------------

-- If a type has all finite products and coproducts, and is distributive,
-- then we say of it that it has finite data structures.
public export
data FinDSF : {a : Type} -> (prod : UMagmaI a) -> (coprod : UMagmaI a) ->
      HomEndofunctor a where
  FDSProdF : {0 a : Type} -> {0 prod, coprod : UMagmaI a} ->
    {0 h : HomSlice a} -> {0 x, y : a} ->
    FinProdMorphF {a} prod h (x, y) -> FinDSF prod coprod h (x, y)
  FDSCoprodF : {0 a : Type} -> {0 prod, coprod : UMagmaI a} ->
    {0 h : HomSlice a} -> {0 x, y : a} ->
    FinCoprodMorphF {a} coprod h (x, y) -> FinDSF prod coprod h (x, y)
  FDSDistF : {0 a : Type} -> {0 prod, coprod : UMagmaI a} ->
    {0 h : HomSlice a} -> {0 x, y : a} ->
    DistribMorphF {a} (MUm prod) (MUm coprod) h (x, y) ->
    FinDSF prod coprod h (x, y)

public export
FinDSFI : {a : Type} -> UMagmaI a -> UMagmaI a -> HomSlice a -> Type
FinDSFI {a} prod coprod = SliceAlg {a=(SignatureT a)} (FinDSF {a} prod coprod)

---------------------------
---- Finite data types ----
---------------------------

-- If a type has all finite products and coproducts, and also
-- hom-objects (which is to say, it is bicartesian closed), then
-- we say it has all finite data types.
public export
data FinDTF : {a : Type} ->
      (prod : UMagmaI a) -> (coprod : UMagmaI a) -> (hom : MagmaI a) ->
      HomEndofunctor a where
  FDTProdF : {0 a : Type} -> {0 prod, coprod : UMagmaI a} ->
    {0 hom : MagmaI a} ->
    {0 h : HomSlice a} -> {0 x, y : a} ->
    FinProdMorphF {a} prod h (x, y) -> FinDTF prod coprod hom h (x, y)
  FDTCoprodF : {0 a : Type} -> {0 prod, coprod : UMagmaI a} ->
    {0 hom : MagmaI a} ->
    {0 h : HomSlice a} -> {0 x, y : a} ->
    FinCoprodMorphF {a} coprod h (x, y) -> FinDTF prod coprod hom h (x, y)
  FDTHomF : {0 a : Type} -> {0 prod, coprod : UMagmaI a} ->
    {0 hom : MagmaI a} ->
    {0 h : HomSlice a} -> {0 x, y : a} ->
    CCMorphF {a} (MUm prod) hom h (x, y) ->
    FinDTF prod coprod hom h (x, y)

public export
FinDTFI : {a : Type} -> UMagmaI a -> UMagmaI a -> MagmaI a -> HomSlice a -> Type
FinDTFI {a} prod coprod hom =
  SliceAlg {a=(SignatureT a)} (FinDTF {a} prod coprod hom)

-- Finite data types imply finite data structures:  specifically, a
-- bicartesian closed category is always distributive.
public export
FDTDist : {a : Type} ->
  (prod : UMagmaI a) -> (coprod : UMagmaI a) -> (hom : MagmaI a) ->
  ImplementationF {a}
    (FinDTFI {a} prod coprod hom)
    (DistributiveI {a} (MUm prod) (MUm coprod))
FDTDist {a} prod coprod hom h cat fdt (_, _) (DMDist x y z) =
  ?FDTDist_hole

public export
FDTStruct : {a : Type} ->
  (prod : UMagmaI a) -> (coprod : UMagmaI a) -> (hom : MagmaI a) ->
  ImplementationF {a} (FinDTFI {a} prod coprod hom) (FinDSFI {a} prod coprod)
FDTStruct {a} prod coprod hom h cat fdt (x, y) (FDSProdF p) =
  fdt (x, y) $ FDTProdF p
FDTStruct {a} prod coprod hom h cat fdt (x, y) (FDSCoprodF c) =
  fdt (x, y) $ FDTCoprodF c
FDTStruct {a} prod coprod hom h cat fdt (v, w) (FDSDistF d) =
  FDTDist {a} prod coprod hom h cat fdt (v, w) d

--------------------
--------------------
---- Arithmetic ----
--------------------
--------------------

---------------------------------------
---- Bounded polynomial arithmetic ----
---------------------------------------

public export
data BNatF : Type -> Type where
  BNn : {0 a : Type} -> (n : Nat) -> {auto 0 non_z : Not (n = 0)} -> BNatF a

public export
BNatI : Type -> Type
BNatI = Algebra BNatF

public export
BNI : {0 a : Type} -> ((n : Nat) -> {auto 0 non_z : Not (n = 0)} -> a) ->
  BNatI a
BNI {a} bn (BNn {a} n {non_z}) = bn n {non_z}

public export
bNat : {0 a : Type} -> BNatI a -> (n : Nat) -> {auto 0 non_z : Not (n = 0)} -> a
bNat {a} alg n {non_z} = alg $ BNn {a} n {non_z}

public export
data BoundedArithMorphF : {a : Type} -> (fprod : UMagmaI a) ->
    (bnat : BNatI a) -> HomEndofunctor a where
  BAinj : (m, n : Nat) ->
    {auto 0 m_ok : Not (m = 0)} -> {auto 0 n_ok : Not (n = 0)} ->
    BoundedArithMorphF fprod bnat h (bNat bnat m, bNat bnat n)
  BAconst : (n : Nat) ->
    {auto 0 n_ok : Not (n = 0)} ->
    Nat ->
    BoundedArithMorphF fprod bnat h (Uu $ MUu fprod, bNat bnat n)
  BAadd : (n : Nat) -> {auto 0 ok : Not (n = 0)} ->
    BoundedArithMorphF fprod bnat h
      (Mb (MUm fprod) (bNat bnat n) (bNat bnat n), bNat bnat n)
  BAmult : (n : Nat) -> {auto 0 ok : Not (n = 0)} ->
    BoundedArithMorphF fprod bnat h
      (Mb (MUm fprod) (bNat bnat n) (bNat bnat n), bNat bnat n)

public export
BoundedArithI : {a : Type} -> UMagmaI a -> BNatI a -> HomSlice a -> Type
BoundedArithI {a} fprod bnat =
  SliceAlg {a=(SignatureT a)} (BoundedArithMorphF {a} fprod bnat)

public export
BoundedArithMorphFM : {a : Type} -> (fprod : UMagmaI a) -> (bnat : BNatI a) ->
  HomEndofunctor a
BoundedArithMorphFM {a} fprod bnat =
  SliceFreeM (BoundedArithMorphF {a} fprod bnat)

public export
BoundedArithMorphFMI : {a : Type} -> (fprod : UMagmaI a) -> (bnat : BNatI a) ->
  (h : HomSlice a) ->
  BoundedArithI {a} fprod bnat (BoundedArithMorphFM {a} fprod bnat h)
BoundedArithMorphFMI {a} fprod bnat h sig =
  InSlFc {f=(BoundedArithMorphF {a} fprod bnat)}
    {a=(SignatureT a)} {sa=h} {ea=sig}

-----------------------------------------------------
---- Bounded polynomial arithmetic with inverses ----
-----------------------------------------------------

public export
data BArithInvMorphF : {a : Type} -> (maybeM : UnarAlg a) ->
    (fprod : UMagmaI a) -> (bnat : BNatI a) -> HomEndofunctor a where
  BAIsub : (n : Nat) -> {auto 0 ok : Not (n = 0)} ->
    BArithInvMorphF maybeM fprod bnat h
      (Mb (MUm fprod) (bNat bnat n) (bNat bnat n), bNat bnat n)
  BAIdiv : (n : Nat) -> {auto 0 ok : Not (n = 0)} ->
    BArithInvMorphF maybeM fprod bnat h
      (Mb (MUm fprod) (bNat bnat n) (bNat bnat n), Uun maybeM (bNat bnat n))
  BAImod : (n : Nat) -> {auto 0 ok : Not (n = 0)} ->
    BArithInvMorphF maybeM fprod bnat h
      (Mb (MUm fprod) (bNat bnat n) (bNat bnat n), Uun maybeM (bNat bnat n))

public export
BArithInvI : {a : Type} -> UnarAlg a -> UMagmaI a -> BNatI a ->HomSlice a -> Type
BArithInvI {a} maybeM fprod bnat =
  SliceAlg {a=(SignatureT a)} (BArithInvMorphF {a} maybeM fprod bnat)

public export
BArithInvMorphFM : {a : Type} -> (maybeM : UnarAlg a) -> (fprod : UMagmaI a) ->
  (bnat : BNatI a) -> HomEndofunctor a
BArithInvMorphFM {a} maybeM fprod bnat =
  SliceFreeM (BArithInvMorphF {a} maybeM fprod bnat)

public export
BArithInvMorphFMI : {a : Type} -> (maybeM : UnarAlg a) -> (fprod : UMagmaI a) ->
  (bnat : BNatI a) -> (h : HomSlice a) ->
  BArithInvI {a} maybeM fprod bnat (BArithInvMorphFM {a} maybeM fprod bnat h)
BArithInvMorphFMI {a} maybeM fprod bnat h sig =
  InSlFc {f=(BArithInvMorphF {a} maybeM fprod bnat)}
    {a=(SignatureT a)} {sa=h} {ea=sig}

--------------------------------------------
---- Bounded natural number comparisons ----
--------------------------------------------

public export
data BACompMorphF : {a : Type} -> (bool : UnitalAlg a) -> (fprod : UMagmaI a) ->
    (bnat : BNatI a) -> HomEndofunctor a where
  BACeq : (n : Nat) -> {auto 0 ok : Not (n = 0)} ->
    BACompMorphF bool fprod bnat h
      (Mb (MUm fprod) (bNat bnat n) (bNat bnat n), Uu bool)
  BAClt : (n : Nat) -> {auto 0 ok : Not (n = 0)} ->
    BACompMorphF bool fprod bnat h
      (Mb (MUm fprod) (bNat bnat n) (bNat bnat n), Uu bool)

public export
BACompI : {a : Type} -> UnitalAlg a -> UMagmaI a -> BNatI a -> HomSlice a -> Type
BACompI {a} bool fprod bnat =
  SliceAlg {a=(SignatureT a)} (BACompMorphF {a} bool fprod bnat)

public export
BACompMorphFM : {a : Type} -> (bool : UnitalAlg a) -> (fprod : UMagmaI a) ->
  (bnat : BNatI a) -> HomEndofunctor a
BACompMorphFM {a} bool fprod bnat =
  SliceFreeM (BACompMorphF {a} bool fprod bnat)

public export
BACompMorphFMI : {a : Type} -> (bool : UnitalAlg a) -> (fprod : UMagmaI a) ->
  (bnat : BNatI a) -> (h : HomSlice a) ->
  BACompI {a} bool fprod bnat (BACompMorphFM {a} bool fprod bnat h)
BACompMorphFMI {a} bool fprod bnat h sig =
  InSlFc {f=(BACompMorphF {a} bool fprod bnat)}
    {a=(SignatureT a)} {sa=h} {ea=sig}

------------------------------------------------
---- (Parameterized) natural numbers object ----
------------------------------------------------

public export
data ParamNNOMorphF : {a : Type} -> (fprod : UMagmaI a) ->
    (nat : UnitalAlg a) -> HomEndofunctor a where
  PNNOZ : ParamNNOMorphF {a} fprod nat h (Uu $ MUu fprod, Uu nat)
  PNNOS : ParamNNOMorphF {a} fprod nat h (Uu nat, Uu nat)
  PNNOcata : {x, y : a} ->
    h (x, y) -> h ((Mb (MUm fprod) x (Mb (MUm fprod) (Uu nat) y)), y) ->
    ParamNNOMorphF {a} fprod nat h (Mb (MUm fprod) x (Uu nat), y)

public export
ParamNNOI : {a : Type} -> UMagmaI a -> UnitalAlg a -> HomSlice a -> Type
ParamNNOI {a} fprod nat =
  SliceAlg {a=(SignatureT a)} (ParamNNOMorphF {a} fprod nat)

public export
ParamNNOMorphFM : {a : Type} -> (fprod : UMagmaI a) -> (nat : UnitalAlg a) ->
  HomEndofunctor a
ParamNNOMorphFM {a} fprod nat =
  SliceFreeM (ParamNNOMorphF {a} fprod nat)

public export
ParamNNOMorphFMI : {a : Type} -> (fprod : UMagmaI a) -> (nat : UnitalAlg a) ->
  (h : HomSlice a) ->
  ParamNNOI {a} fprod nat (ParamNNOMorphFM {a} fprod nat h)
ParamNNOMorphFMI {a} fprod nat h sig =
  InSlFc {f=(ParamNNOMorphF {a} fprod nat)} {a=(SignatureT a)} {sa=h} {ea=sig}

---------------------------------
---------------------------------
---- Metalanguage categories ----
---------------------------------
---------------------------------

-- Interpretation of various universal properties into `Type` and some
-- of its sub-categories.

----------------
---- `Type` ----
----------------

-- `Type` is a category.
public export
TypeCat : CategoryI {a=Type} (\(x, y) => x -> y)
TypeCat (x, x) (CHId x) = id {a=x}
TypeCat (x, z) (CHComp {x} {y} {z} g f) = g . f

public export
TypeUIv : UnitalAlg Type
TypeUIv = MkU Void

public export
TypeUIu : UnitalAlg Type
TypeUIu = MkU Unit

public export
TypeMIc : MagmaI Type
TypeMIc = MkMag Either

public export
TypeMIp : MagmaI Type
TypeMIp = MkMag Pair

public export
TypeUMIp : UMagmaI Type
TypeUMIp = MkUMag TypeUIu TypeMIp

-- A specialization of `CovarInit` where the hom-functor is internal to `Type`.
public export
InitHomT : {0 a, b, c : Type} -> (h : a -> b -> c) -> b -> Type
InitHomT {a} {b} {c} = CovarInit {a} {b} {c} {d=Type} TypeUIu

-- A specialization of `ContravarTerm` where the hom-functor is internal to
-- `Type`.
public export
TermContraHomT : {0 a, b, c : Type} -> (h : a -> b -> c) -> a -> Type
TermContraHomT {a} {b} {c} = ContravarTerm {a} {b} {c} {d=Type} TypeUIu

public export
TypeHomSlice : HomSlice Type
TypeHomSlice (x, y) = x -> y

-- `Type` has an initial object.
public export
TypeInitI : InitialI {a=Type} TypeUIv TypeHomSlice
TypeInitI = InitI (\a => voidF a)

-- `Type` has a terminal object.
public export
TypeTermI : TerminalI {a=Type} TypeUIu TypeHomSlice
TypeTermI = TermI (\a => const ())

-- `Type` has all coproducts.
public export
TypeCoprodI : CoproductI {a=Type} TypeMIc TypeHomSlice
TypeCoprodI (x, Mb TypeMIc x y) (CMInjL x y) = Left
TypeCoprodI (y, Mb TypeMIc x y) (CMInjR x y) = Right
TypeCoprodI (Mb TypeMIc x y, z) (CMCase f) = uncurry eitherElim f

-- `Type` has all products.
public export
TypeProdI : ProductI {a=Type} TypeMIp TypeHomSlice
TypeProdI (x, Mb TypeMIp y z) (PMPair (f, g)) = \ex => (f ex, g ex)
TypeProdI (Mb TypeMIp x y, x) (PMProj1 x y) = \(ex, ey) => ex
TypeProdI (Mb TypeMIp x y, y) (PMProj2 x y) = \(ex, ey) => ey

-----------------------------------------------------------------
---- `Type x Type` (endofunctors on `Type`, so AKA `TypeEF`) ----
-----------------------------------------------------------------

-- `TypeEF` is a category.
public export
TypeEFCat : CategoryI {a=(Type -> Type)} (\(f, g) => NaturalTransformation f g)
TypeEFCat (f, f) (CHId f) = \x => Prelude.id {a=(f x)}
TypeEFCat (f, h) (CHComp {x=f} {y=g} {z=h} beta alpha) = \x => beta x . alpha x

public export
TypeEFUIv : UnitalAlg (Type -> Type)
TypeEFUIv = MkU (const Void)

public export
TypeEFUIu : UnitalAlg (Type -> Type)
TypeEFUIu = MkU (const Unit)

public export
TypeEFMIc : MagmaI (Type -> Type)
TypeEFMIc = MkMag CoproductF

public export
TypeEFMIp : MagmaI (Type -> Type)
TypeEFMIp = MkMag ProductF

public export
TypeEFUMIp : UMagmaI (Type -> Type)
TypeEFUMIp = MkUMag TypeEFUIu TypeEFMIp

public export
TypeEFHomSlice : HomSlice (Type -> Type)
TypeEFHomSlice (f, g) = NaturalTransformation f g

-- `Type -> Type` has an initial object.
public export
TypeEFInitI : InitialI {a=(Type -> Type)} TypeEFUIv TypeEFHomSlice
TypeEFInitI = InitI (\f, a, v => voidF (f a) v)

-- `Type -> Type` has a terminal object.
public export
TypeEFTermI : TerminalI {a=(Type -> Type)} TypeEFUIu TypeEFHomSlice
TypeEFTermI = TermI (\f, a => const ())

-- `Type -> Type` has all coproducts.
public export
TypeEFCoprodI : CoproductI {a=(Type -> Type)} TypeEFMIc TypeEFHomSlice
TypeEFCoprodI (f, (Mb TypeEFMIc f g)) (CMInjL f g) = \_ => Left
TypeEFCoprodI (g, (Mb TypeEFMIc f g)) (CMInjR f g) = \_ => Right
TypeEFCoprodI ((Mb TypeEFMIc f g), h) (CMCase (alpha, beta)) =
  \x => eitherElim (alpha x) (beta x)

-- `Type -> Type` has all products.
public export
TypeEFProdI : ProductI {a=(Type -> Type)} TypeEFMIp TypeEFHomSlice
TypeEFProdI (f, (Mb TypeEFMIp g h)) (PMPair (alpha, beta)) =
  \x, fx => (alpha x fx, beta x fx)
TypeEFProdI ((Mb TypeEFMIp f g), f) (PMProj1 f g) = \_ => fst
TypeEFProdI ((Mb TypeEFMIp f g), g) (PMProj2 f g) = \_ => snd

-----------------------------------
---- Boolean circuits ("BITC") ----
-----------------------------------

public export
data BITCObj : Type where
  -- `BITCn n` is a vector of `n` bits.
  BITCn : Nat -> BITCObj

public export
BITCSig : Type
BITCSig = SignatureT BITCObj

public export
data BITCMorphF : HomEndofunctor BITCObj where
  BITCident : (n : Nat) -> BITCMorphF h (BITCn n, BITCn n)
  BITCcompose : {k, m, n : Nat} ->
    BITCMorphF h (BITCn m, BITCn n) ->
    BITCMorphF h (BITCn k, BITCn m) ->
    BITCMorphF h (BITCn k, BITCn n)
  BITCfork : (n : Nat) -> BITCMorphF h (BITCn n, BITCn $ 2 * n)
  BITCparallel : {a, b, c, d : Nat} ->
    h (BITCn a, BITCn b) -> h (BITCn c, BITCn d) ->
    BITCMorphF h (BITCn (a + c), BITCn (b + d))
  BITCswap : (n, m : Nat) -> BITCMorphF h (BITCn (n + m), BITCn (m + n))
  BITCone : BITCMorphF h (BITCn 0, BITCn 1)
  BITCzero : BITCMorphF h (BITCn 0, BITCn 1)
  BITCdrop : (n : Nat) -> BITCMorphF h (BITCn n, BITCn 0)
  BITCbranch : {a, b : Nat} ->
    h (BITCn a, BITCn b) -> h (BITCn a, BITCn b) ->
    BITCMorphF h (BITCn (1 + a), BITCn b)

public export
BITCMorphI : HomSlice BITCObj -> Type
BITCMorphI = SliceAlg {a=(SignatureT BITCObj)} BITCMorphF

-------------------------
-------------------------
---- Free categories ----
-------------------------
-------------------------

-------------------------------------
---- Generic category interfaces ----
-------------------------------------

public export
record HomSig where
  constructor MkHom
  hsObj : Type
  hsMorph : HomSlice hsObj

public export
HomObjFunc : Type
HomObjFunc = SliceObj HomSig

public export
HomObjAlg : SliceEndofunctor HomSig
HomObjAlg hof hs = hof hs -> hsObj hs

public export
HomObjCoalg : SliceEndofunctor HomSig
HomObjCoalg hof hs = hsObj hs -> hof hs

public export
data HomFuncTranslateObj : HomObjFunc -> HomObjFunc where
  HFTO_v : {0 hof : HomObjFunc} -> {0 hs : HomSig} ->
    hsObj hs -> HomFuncTranslateObj hof hs
  HFTO_c : {0 hof : HomObjFunc} -> {0 hs : HomSig} ->
    hof hs -> HomFuncTranslateObj hof hs

public export
HomFuncTranslateAlg : (hof : HomObjFunc) -> (hs : HomSig) ->
  HomObjAlg hof hs -> HomObjAlg (HomFuncTranslateObj hof) hs
HomFuncTranslateAlg hof hs alg (HFTO_v a) = a
HomFuncTranslateAlg hof hs alg (HFTO_c a) = alg a

public export
HomMorphFunc : SliceObj HomObjFunc
HomMorphFunc hof = SliceMorphism {a=HomSig} (HomObjAlg hof) (HomSlice . hof)

public export
record HomFuncFunc where
  constructor HFF
  hffObj : HomObjFunc
  hffMorph : HomMorphFunc hffObj

public export
HomFuncFuncAlg : HomFuncFunc -> HomSig -> Type
HomFuncFuncAlg hff = HomObjAlg (hffObj hff)

-------------------------------------------------------------
---- Initial unrefined distributive bicartesian category ----
-------------------------------------------------------------

---------------------------------------------------
---- As above with built-in bounded arithmetic ----
---------------------------------------------------

-------------------------------------------------------
---- Initial unrefined bicartesian closed category ----
-------------------------------------------------------

---------------------------------------------------
---- As above with built-in bounded arithmetic ----
---------------------------------------------------

---------------------------
---------------------------
---- Finite-index type ----
---------------------------
---------------------------

------------------------------------------
---- Explicitly-recursive formulation ----
------------------------------------------

mutual
  public export
  data FIObj : Type where
    FI0 : FIObj
    FI1 : FIObj
    FIC : FIObj -> FIObj -> FIObj
    FIP : FIObj -> FIObj -> FIObj
    FIS : {a : FIObj} -> FPred a -> FIObj
    FIN : Nat -> FIObj

  public export
  data FPred : FIObj -> Type where
    FP0 : FPred FI0 -- sum of no representables
    FPR : FIObj -> FPred FI1 -- representable
    FPC : FPred a -> FPred b -> FPred (FIC a b) -- sum of sum of representables
    FPN : {n : Nat} -> Vect n FIObj -> FPred (FIN n) -- sum of representables

mutual
  public export
  FITerm : FIObj -> Type
  FITerm FI0 = Void
  FITerm FI1 = ()
  FITerm (FIC a b) = Either (FITerm a) (FITerm b)
  FITerm (FIP a b) = Pair (FITerm a) (FITerm b)
  FITerm (FIS {a=FI0} FP0) = Void
  FITerm (FIS {a} b) = FISigTerm {a} b
  FITerm (FIN n) = Subset0 Nat (GT n)

  public export
  FISigTerm : {a : FIObj} -> FPred a -> Type
  FISigTerm {a=FI0} FP0 = Void
  FISigTerm {a=FI1} (FPR b) = FITerm b
  FISigTerm {a=(FIC a a')} (FPC b b') =
    Either (FISigTerm {a} b) (FISigTerm {a=a'} b')
  FISigTerm {a=(FIN n)} (FPN bs) = FIListTerm {n} bs

  public export
  FIListTerm : {n : Nat} -> Vect n FIObj -> Type
  FIListTerm {n=Z} [] = Void
  FIListTerm {n=(S n)} (b :: bs) = Either (FITerm b) (FIListTerm {n} bs)

mutual
  public export
  FIndexed : Type -> FIObj -> Type
  FIndexed x FI0 = Unit
  FIndexed x FI1 = x
  FIndexed x (FIC a b) = Pair (FIndexed x a) (FIndexed x b)
  FIndexed x (FIP a b) = FIndexed (FIndexed x b) a
  FIndexed x (FIS {a} b) = FSigIndexed x {a} b
  FIndexed x (FIN n) = Vect n x

  public export
  FSigIndexed : Type -> {a : FIObj} -> FPred a -> Type
  FSigIndexed x {a=FI0} FP0 = Unit
  FSigIndexed x {a=FI1} (FPR b) = FIndexed x b
  FSigIndexed x {a=(FIC a a')} (FPC b b') =
    Pair (FSigIndexed x {a} b) (FSigIndexed x {a=a'} b')
  FSigIndexed x {a=(FIN n)} (FPN bs) = FListIndexed x {n} bs

  public export
  FListIndexed : Type -> {n : Nat} -> Vect n FIObj -> Type
  FListIndexed x {n=Z} [] = Unit
  FListIndexed x {n=(S n)} (b :: bs) =
    Pair (FIndexed x b) (FListIndexed x {n} bs)

public export
FIndexedBy : FIObj -> Type -> Type
FIndexedBy = flip FIndexed

public export
record FDepArena (dom, cod : FIObj) where
  constructor FDA
  fdaPos : FPred cod
  fdaDir : FPred (FIS {a=cod} fdaPos)
  fdaBC : FIndexedBy (FIS {a=(FIS {a=cod} fdaPos)} fdaDir) (FITerm dom)

----------------------------
---- W-type formulation ----
----------------------------

{-
 - A formulation of `FinSet` specifically intended as a minimal type to
 - be used for constructors of ADTs, atoms of expressions, and indexes
 - for finitely-indexed dependent types or type families.
 -}

-- The type of objects of the category in which the telescope which constitutes
-- this formulation of `FinSet` is the initial algebra of a polynomial
-- endofunctor.
public export
record IdxCatObj where
  constructor ICObj
  -- The type of objects of a category which can be characterized
  -- by an `IdxCatObj`.
  icObj : Type

  -- The type of terms of objects of such a category -- global elements, in
  -- the categorical view.  These categories will be well-pointed, meaning that
  -- their objects will be completely characterized by their global elements.
  icTerm : icObj -> Type

  -- The type of morphisms of such a category.
  icMorph : HomSlice icObj

  -- The type of indexed terms of a given type (the `iObj` parameter
  -- is the index type).
  icIndexed : (icObj, Type) -> Type

public export
IdxCatCoproduct : IdxCatObj -> IdxCatObj -> IdxCatObj
IdxCatCoproduct a b =
  ICObj
    (Either (icObj a) (icObj b))
    (\x => case x of
      Left x' => icTerm a x'
      Right x' => icTerm b x')
    (\(x, y) => case (x, y) of
      (Left x', Left y') => icMorph a (x', y')
      (Right x', Right y') => icMorph b (x', y')
      _ => Void)
    (\(x, ty) => case x of
      Left x' => icIndexed a (x', ty)
      Right x' => icIndexed b (x', ty))

public export
FIData0 : IdxCatObj
FIData0 = ICObj Void (\v => void v) (\(v, _) => void v) (\(v, _) => void v)

public export
FinIdxDataIter : IdxCatObj -> IdxCatObj
FinIdxDataIter = ?FinIdxIter_hole

public export
FinIdxDataEitherIter : IdxCatObj -> IdxCatObj
FinIdxDataEitherIter a = IdxCatCoproduct a (FinIdxDataIter a)

public export
FinIdxDataN : Nat -> IdxCatObj
FinIdxDataN Z = FIData0
FinIdxDataN (S n) = FinIdxDataEitherIter (FinIdxDataN n)

public export
FinIdxObjN : Nat -> Type
FinIdxObjN = icObj . FinIdxDataN

public export
finIdxObjInj : {0 n : Nat} -> FinIdxObjN n -> FinIdxObjN (S n)
finIdxObjInj {n} = Left

public export
finIdxObjInjN : {m, n : Nat} -> {auto islte : LTE m n} ->
  FinIdxObjN m -> FinIdxObjN n
finIdxObjInjN {m=Z} {n=Z} {islte=LTEZero} v = void v
finIdxObjInjN {m=Z} {n=(S n)} {islte=LTEZero} v = void v
finIdxObjInjN {m=(S m)} {n=(S n)} {islte=(LTESucc islte)} (Left a) =
  Left $ finIdxObjInjN {m} {n} {islte} a
finIdxObjInjN {m=(S m)} {n=(S n)} {islte=(LTESucc islte)} (Right a) =
  Right $ ?finIdxObjInjN_hole

public export
FinIdxObjMu : Type
FinIdxObjMu = Sigma {a=Nat} FinIdxObjN

public export
FinIdxTermN : {n : Nat} -> FinIdxObjN n -> Type
FinIdxTermN {n} = icTerm (FinIdxDataN n)

public export
FinIdxTermMu : FinIdxObjMu -> Type
FinIdxTermMu (n ** a) = FinIdxTermN {n} a

public export
FinIdxMorphN : {n : Nat} -> HomSlice (FinIdxObjN n)
FinIdxMorphN {n} = icMorph (FinIdxDataN n)

public export
FinIdxMorphMu : HomSlice FinIdxObjMu
FinIdxMorphMu ((k ** a), (n ** b)) = ?FinIdxMorphMu_hole

public export
FinIdxIndexedN : {n : Nat} -> (FinIdxObjN n, Type) -> Type
FinIdxIndexedN {n} = icIndexed (FinIdxDataN n)

public export
FinIdxIndexedMu : (FinIdxObjMu, Type) -> Type
FinIdxIndexedMu ((n ** a), b) = FinIdxIndexedN {n} (a, b)

public export
FinIdxDataMu : IdxCatObj
FinIdxDataMu = ICObj FinIdxObjMu FinIdxTermMu FinIdxMorphMu FinIdxIndexedMu

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---- Core types via manual version of category-spec API (to bootstrap) ----
---------------------------------------------------------------------------
---------------------------------------------------------------------------

-- The type of initial objects of a category internal to `Type` is
-- isomorphic to `Unit`, because up to ismomorphism there is only one
-- initial object.
public export
InitialTF : Type -> Type
InitialTF _ = Unit

-- Given a type of objects, produce the covariant hom-functor for
-- the intial object.
public export
InitialTFCovarHom : (obj : Type) -> (hom : HomSlice obj) ->
  InitialTF obj -> obj -> Type
InitialTFCovarHom obj hom () _ = ()

-- The type of terminal objects of a category internal to `Type` is
-- isomorphic to `Unit`, because up to ismomorphism there is only one
-- terminal object.
public export
TerminalTF : Type -> Type
TerminalTF _ = Unit

-- Given a type of objects, produce the contravariant hom-functor for
-- the terminal object.
public export
TerminalTFContraHomT : (obj : Type) -> (hom : HomSlice obj) ->
  TerminalTF obj -> obj -> Type
TerminalTFContraHomT obj hom () _ = ()

-- Given a type of objects of a category internal to `Type`, if
-- the category has all coproducts, then the type of its coproduct types
-- is isomorphic to the type of its pairs of types, because precisely
-- two objects determine a coproduct (up to isomorphism).
public export
CoproductTF : Type -> Type
CoproductTF carrier = (carrier, carrier)

-- Given a type of objects and a hom-functor, produce the covariant
-- hom-functor for coproducts.
public export
CoproductTFCovarHom : (obj : Type) -> (hom : HomSlice obj) ->
  CoproductTF obj -> obj -> Type
CoproductTFCovarHom obj hom (a, b) c = (hom (a, c), hom (b, c))

-- Given a type of objects of a category internal to `Type`, if
-- the category has all products, then the type of its product types
-- is isomorphic to the type of its pairs of types, because precisely
-- two objects determine a product (up to isomorphism).
public export
ProductTF : Type -> Type
ProductTF carrier = (carrier, carrier)

-- Given a type of objects and a hom-functor, produce the contravariant
-- hom-functor for products.
public export
ProductTFContraHomT : (obj : Type) -> (hom : HomSlice obj) ->
  ProductTF obj -> obj -> Type
ProductTFContraHomT obj hom (a, b) c = (hom (c, a), hom (c, b))

-- Objects of unrefined FinSet.
public export
data UFSObjF : Type -> Type where
  UFS0 : InitialTF carrier -> UFSObjF carrier
  UFS1 : TerminalTF carrier -> UFSObjF carrier
  UFSC : CoproductTF carrier -> UFSObjF carrier
  UFSP : ProductTF carrier -> UFSObjF carrier

public export
UFSEitherObjF : Type -> Type
UFSEitherObjF = TrEitherF UFSObjF

public export
UFSEitherHomSliceF : Type -> Type
UFSEitherHomSliceF = HomSlice . UFSEitherObjF

public export
data UFSEitherMorphF : (obj : Type) -> (hom : HomSlice obj) ->
    UFSEitherHomSliceF obj where
  UFSM0 :
    (b : UFSEitherObjF obj) -> UFSEitherMorphF obj hom (TFC $ UFS0 (), b)
  UFSM1 :
    (a : UFSEitherObjF obj) -> UFSEitherMorphF obj hom (a, TFC $ UFS1 ())

public export
UFSMorphF : (obj : Type) -> (hom : HomSlice obj) -> HomSlice (UFSObjF obj)
UFSMorphF = ?UFSMorphF_hole

public export
UFSDiagN : Nat -> PreDiagram
UFSDiagN Z = MkPreDiag Void (\(v, _) => void v)
UFSDiagN (S n) with (UFSDiagN n)
  UFSDiagN (S n) | MkPreDiag obj hom =
    MkPreDiag (UFSObjF obj) (UFSMorphF obj hom)

-----------------------------------------------------------------
-----------------------------------------------------------------
---- Functor vs. explicitly-recursive versions of core logic ----
-----------------------------------------------------------------
-----------------------------------------------------------------

public export
ObjF_Alg : (objF : (obj' : Type) -> (hom' : obj' -> obj' -> Type) -> Type) ->
  (obj : Type) -> (hom : obj -> obj -> Type) -> Type
ObjF_Alg objF obj hom = objF obj hom -> obj

public export
MorphF_Coproduct :
  {objF : (obj' : Type) -> (hom' : obj' -> obj' -> Type) -> Type} ->
  (homFl, homFr :
    (obj' : Type) ->
    (hom' : obj' -> obj' -> Type) ->
    ObjF_Alg objF obj' hom' ->
    obj' -> obj' -> Type) ->
  (obj : Type) ->
  (hom : obj -> obj -> Type) ->
  ObjF_Alg objF obj hom ->
  obj -> obj -> Type
MorphF_Coproduct {objF} homFl homFr obj hom alg a b =
  Either (homFl obj hom alg a b) (homFr obj hom alg a b)

public export
CatMorph_F :
  {objF : (obj' : Type) -> (hom' : obj' -> obj' -> Type) -> Type} ->
  (homF :
    (obj' : Type) -> (hom' : obj' -> obj' -> Type) ->
    ObjF_Alg objF obj' hom' -> obj' -> obj' -> Type) ->
  (obj : Type) -> (hom : obj -> obj -> Type) ->
  ObjF_Alg objF obj hom -> obj -> obj -> Type
CatMorph_F {objF} homF =
  MorphF_Coproduct {objF}
    (\obj, hom, alg, a, b => CatHomF {obj} (uncurry hom) (a, b))
    homF

public export
FMF_id :
  {objF : (obj' : Type) -> (hom' : obj' -> obj' -> Type) -> Type} ->
  {homF :
    (obj' : Type) -> (hom' : obj' -> obj' -> Type) ->
    ObjF_Alg objF obj' hom' -> obj' -> obj' -> Type} ->
  {obj : Type} -> {hom : obj -> obj -> Type} ->
  {objAlg : ObjF_Alg objF obj hom} ->
  (a : obj) -> CatMorph_F {objF} homF obj hom objAlg a a
FMF_id {objF} {homF} {obj} {hom} {objAlg} a =
  Left $ CHId {obj} {hom=(uncurry hom)} a

public export
FMF_comp :
  {objF : (obj' : Type) -> (hom' : obj' -> obj' -> Type) -> Type} ->
  {homF :
    (obj' : Type) -> (hom' : obj' -> obj' -> Type) ->
    ObjF_Alg objF obj' hom' -> obj' -> obj' -> Type} ->
  {obj : Type} -> {hom : obj -> obj -> Type} ->
  {objAlg : ObjF_Alg objF obj hom} -> {a, b, c : obj} ->
  hom b c -> hom a b -> CatMorph_F {objF} homF obj hom objAlg a c
FMF_comp {objF} {homF} {obj} {hom} {objAlg} {a} {b} {c} g f =
  Left $ CHComp {obj} {hom=(uncurry hom)} {x=a} {y=b} {z=c} g f

----------------------------------
---- FinSet-specific functors ----
----------------------------------

public export
data FinSetObj_F : (obj : Type) -> (hom : obj -> obj -> Type) -> Type where
  FSOF_0 : FinSetObj_F obj hom
  FSOF_1 : FinSetObj_F obj hom
  FSOF_C : obj -> obj -> FinSetObj_F obj hom
  FSOF_P : obj -> obj -> FinSetObj_F obj hom
  FSOF_H : obj -> obj -> FinSetObj_F obj hom
  FSOF_Eq : {a, b : obj} -> hom a b -> hom a b -> FinSetObj_F obj hom
  FSOF_Coeq : {a, b : obj} -> hom a b -> hom a b -> FinSetObj_F obj hom

public export
FSOF_objAlg : (obj : Type) -> (hom : obj -> obj -> Type) -> Type
FSOF_objAlg = ObjF_Alg FinSetObj_F

public export
FSOF_B : (obj : Type) -> (hom : obj -> obj -> Type) -> FSOF_objAlg obj hom ->
  obj
FSOF_B obj hom objAlg = objAlg $ FSOF_C (objAlg FSOF_1) (objAlg FSOF_1)

public export
FSCatMorph_F :
  (homF :
    (obj' : Type) -> (hom' : obj' -> obj' -> Type) ->
    FSOF_objAlg obj' hom' -> obj' -> obj' -> Type) ->
  (obj : Type) -> (hom : obj -> obj -> Type) ->
  FSOF_objAlg obj hom -> obj -> obj -> Type
FSCatMorph_F = CatMorph_F {objF=FinSetObj_F}

public export
FSMF_id :
  {homF :
    (obj' : Type) -> (hom' : obj' -> obj' -> Type) ->
    FSOF_objAlg obj' hom' -> obj' -> obj' -> Type} ->
  {obj : Type} -> {hom : obj -> obj -> Type} ->
  {objAlg : FSOF_objAlg obj hom} -> (a : obj) ->
  FSCatMorph_F homF obj hom objAlg a a
FSMF_id {homF} {objAlg} = FMF_id {objF=FinSetObj_F} {homF} {objAlg}

public export
FSMF_comp :
  {homF :
    (obj' : Type) -> (hom' : obj' -> obj' -> Type) ->
    FSOF_objAlg obj' hom' -> obj' -> obj' -> Type} ->
  {obj : Type} -> {hom : obj -> obj -> Type} ->
  {objAlg : FSOF_objAlg obj hom} -> {a, b, c : obj} ->
  hom b c -> hom a b -> FSCatMorph_F homF obj hom objAlg a c
FSMF_comp {homF} {obj} {hom} {objAlg} {a} {b} {c} =
  FMF_comp {objF=FinSetObj_F} {homF} {obj} {hom} {objAlg} {a} {b} {c}

public export
data FinSetUniv_F :
    (obj : Type) -> (hom : obj -> obj -> Type) ->
    FSOF_objAlg obj hom -> obj -> obj -> Type where
  FSUF_0 :
    {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
    {0 objAlg : FSOF_objAlg obj hom} ->
    (a : obj) -> FinSetUniv_F obj hom objAlg (objAlg FSOF_0) a
  FSUF_1 :
    {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
    {0 objAlg : FSOF_objAlg obj hom} ->
    (a : obj) -> FinSetUniv_F obj hom objAlg a (objAlg FSOF_1)
  FSUF_inj_l :
    {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
    {0 objAlg : FSOF_objAlg obj hom} ->
    (a, b : obj) -> FinSetUniv_F obj hom objAlg a (objAlg $ FSOF_C a b)
  FSUF_inj_r :
    {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
    {0 objAlg : FSOF_objAlg obj hom} ->
    (a, b : obj) -> FinSetUniv_F obj hom objAlg b (objAlg $ FSOF_C a b)
  FSUF_proj_1 :
    {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
    {0 objAlg : FSOF_objAlg obj hom} ->
    (a, b : obj) -> FinSetUniv_F obj hom objAlg (objAlg $ FSOF_P a b) a
  FSUF_proj_2 :
    {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
    {0 objAlg : FSOF_objAlg obj hom} ->
    (a, b : obj) -> FinSetUniv_F obj hom objAlg (objAlg $ FSOF_P a b) b
  FSUF_distrib :
    {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
    {0 objAlg : FSOF_objAlg obj hom} ->
    (a, b, c : obj) ->
    FinSetUniv_F obj hom objAlg
      (objAlg $ FSOF_P a (objAlg $ FSOF_C b c))
      (objAlg $ FSOF_C (objAlg $ FSOF_P a b) (objAlg $ FSOF_P a c))
  FSUF_eq_elim :
    {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
    {0 objAlg : FSOF_objAlg obj hom} ->
    {0 a, b : obj} ->
    (f, g : hom a b) ->
    FinSetUniv_F obj hom objAlg (objAlg $ FSOF_Eq {a} {b} f g) a
  FSUF_coeq_intro :
    {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
    {0 objAlg : FSOF_objAlg obj hom} ->
    {0 a, b : obj} ->
    (f, g : hom a b) ->
    FinSetUniv_F obj hom objAlg b (objAlg $ FSOF_Coeq {a} {b} f g)
  FSUF_eval :
    {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
    {0 objAlg : FSOF_objAlg obj hom} ->
    (0 a, b : obj) ->
    FinSetUniv_F obj hom objAlg (objAlg $ FSOF_P (objAlg $ FSOF_H a b) a) b
  FSUF_chi :
    {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
    {0 objAlg : FSOF_objAlg obj hom} ->
    {0 a, b : obj} ->
    (f, g : hom a b) ->
    FinSetUniv_F obj hom objAlg a (FSOF_B obj hom objAlg)

public export
data FinSetAdjunct_F :
    (obj : Type) -> (hom : obj -> obj -> Type) ->
    FSOF_objAlg obj hom -> obj -> obj -> Type where
  FSAF_case :
    {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
    {0 objAlg : FSOF_objAlg obj hom} ->
    {0 a, b, c : obj} ->
    hom a c -> hom b c ->
    FinSetAdjunct_F obj hom objAlg (objAlg $ FSOF_C a b) c
  FSAF_pair :
    {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
    {0 objAlg : FSOF_objAlg obj hom} ->
    {0 a, b, c : obj} ->
    hom a b -> hom a c ->
    FinSetAdjunct_F obj hom objAlg a (objAlg $ FSOF_P b c)
  FSAF_curry :
    {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
    {0 objAlg : FSOF_objAlg obj hom} ->
    {0 a, b, c : obj} ->
    hom (objAlg $ FSOF_P a b) c ->
    FinSetAdjunct_F obj hom objAlg a (objAlg $ FSOF_H b c)

public export
FinSetDistinctMorph_F :
  (obj : Type) -> (hom : obj -> obj -> Type) ->
  FSOF_objAlg obj hom -> obj -> obj -> Type
FinSetDistinctMorph_F = MorphF_Coproduct FinSetUniv_F FinSetAdjunct_F

public export
FinSetMorph_F :
  (obj : Type) -> (hom : obj -> obj -> Type) ->
  FSOF_objAlg obj hom -> obj -> obj -> Type
FinSetMorph_F = FSCatMorph_F FinSetDistinctMorph_F

mutual
  public export
  partial
  data Free_FSO_From_F : (obj : Type) -> (hom : obj -> obj -> Type) ->
      Type where
    FFSOFv :
      {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
      obj ->
      Free_FSO_From_F obj hom
    FFSOFc :
      {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
      FinSetObj_F (Free_FSO_From_F obj hom) (Free_FSM_From_F obj hom) ->
      Free_FSO_From_F obj hom

  public export
  partial
  data Free_FSM_From_F : (obj : Type) -> (hom : obj -> obj -> Type) ->
      Free_FSO_From_F obj hom -> Free_FSO_From_F obj hom -> Type where
    FFSMFv :
      {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
      {0 a, b : obj} ->
      hom a b ->
      Free_FSM_From_F obj hom (FFSOFv a) (FFSOFv b)
    FFSMFc :
      {0 obj : Type} -> {0 hom : obj -> obj -> Type} ->
      {0 a, b : Free_FSO_From_F obj hom} ->
      FinSetMorph_F
        (Free_FSO_From_F obj hom) (Free_FSM_From_F obj hom) FFSOFc a b ->
      Free_FSM_From_F obj hom a b

mutual
  public export
  partial
  data FSO_From_F : Type where
    FSOFc : FinSetObj_F FSO_From_F FSM_From_F -> FSO_From_F

  public export
  partial
  data FSM_From_F : FSO_From_F -> FSO_From_F -> Type where
    FSMFc : {0 a, b : FSO_From_F} ->
      FinSetMorph_F FSO_From_F FSM_From_F FSOFc a b ->
      FSM_From_F a b

--------------------------------------
---- Explicitly-recursive version ----
--------------------------------------

mutual
  public export
  data FinSetObj : Type where
    FSO_0 : FinSetObj
    FSO_1 : FinSetObj
    FSO_C : FinSetObj -> FinSetObj -> FinSetObj
    FSO_P : FinSetObj -> FinSetObj -> FinSetObj
    FSO_H : FinSetObj -> FinSetObj -> FinSetObj
    FSO_Eq : FinSetMorph a b -> FinSetMorph a b -> FinSetObj
    FSO_Coeq : FinSetMorph a b -> FinSetMorph a b -> FinSetObj

  -- An alias for `Bool`.
  public export
  FSO_B : FinSetObj
  FSO_B = FSO_C FSO_1 FSO_1

  public export
  data FinSetMorph : FinSetObj -> FinSetObj -> Type where
    FSM_clos : FinSetClosure a b -> FinSetMorph a b
    FSM_univ : FinSetUniv a b -> FinSetMorph a b
    FSM_adj : FinSetAdjunct a b -> FinSetMorph a b

  public export
  data FinSetClosure : FinSetObj -> FinSetObj -> Type where
    FSC_id : (a : FinSetObj) -> FinSetClosure a a
    FSC_comp : FinSetMorph b c -> FinSetMorph a b -> FinSetClosure a c

  public export
  FSM_id : (a : FinSetObj) -> FinSetMorph a a
  FSM_id a = FSM_clos (FSC_id a)

  public export
  FSM_comp : FinSetMorph b c -> FinSetMorph a b -> FinSetMorph a c
  FSM_comp g f = FSM_clos (FSC_comp g f)

  public export
  data FinSetUniv : FinSetObj -> FinSetObj -> Type where
    FSU_0 : (a : FinSetObj) -> FinSetUniv FSO_0 a
    FSU_1 : (a : FinSetObj) -> FinSetUniv a FSO_1
    FSU_inj_l : (a, b : FinSetObj) -> FinSetUniv a (FSO_C a b)
    FSU_inj_r : (a, b : FinSetObj) -> FinSetUniv b (FSO_C a b)
    FSU_proj_1 : (a, b : FinSetObj) -> FinSetUniv (FSO_P a b) a
    FSU_proj_2 : (a, b : FinSetObj) -> FinSetUniv (FSO_P a b) b
    FSU_distrib : (a, b, c : FinSetObj) ->
      FinSetUniv (FSO_P a (FSO_C b c)) (FSO_C (FSO_P a b) (FSO_P a c))
    FSU_eq_elim : (f, g : FinSetMorph a b) -> FinSetUniv (FSO_Eq f g) a
    FSU_coeq_intro : (f, g : FinSetMorph a b) -> FinSetUniv b (FSO_Coeq f g)
    FSU_eval : (a, b : FinSetObj) -> FinSetUniv (FSO_P (FSO_H a b) a) b

    -- Classifier for equalizers.  It therefore can be used to classify
    -- all regular monomorphisms through composition with the isomorphism
    -- between the monomorphism and some equalizer.  And FinSet is balanced,
    -- so this can be used to classify all monomorphisms -- that is, it is
    -- the universal morphism of a subobject classifier (which, in FinSet,
    -- is `Bool`).
    FSU_chi : {0 a, b : FinSetObj} ->
      (f, g : FinSetMorph a b) -> FinSetUniv a FSO_B

  public export
  data FinSetAdjunct : FinSetObj -> FinSetObj -> Type where
    FSM_case :
      FinSetMorph a c -> FinSetMorph b c -> FinSetAdjunct (FSO_C a b) c
    FSM_pair :
      FinSetMorph a b -> FinSetMorph a c -> FinSetAdjunct a (FSO_P b c)
    FSM_curry : FinSetMorph (FSO_P a b) c -> FinSetAdjunct a (FSO_H b c)
    FSM_eq_intro : (h : FinSetMorph c a) -> (f, g : FinSetMorph a b) ->
      FinSetMorphEq (FSM_comp f h) (FSM_comp g h) ->
      FinSetAdjunct c (FSO_Eq f g)
    FSM_coeq_elim : (h : FinSetMorph b c) -> (f, g : FinSetMorph a b) ->
      FinSetMorphEq (FSM_comp h f) (FSM_comp h g) ->
      FinSetAdjunct (FSO_Coeq f g) c
    FSM_ec_inj : {0 a, b, c : FinSetObj} -> {0 f, g : FinSetMorph a b} ->
      {0 h : FinSetMorph c a} ->
      FinSetMorphEq
        (FSM_comp (FSM_univ (FSU_inj_r FSO_1 FSO_1)) (FSM_univ (FSU_1 c)))
        (FSM_comp (FSM_univ (FSU_chi f g)) h) ->
      FinSetAdjunct c (FSO_Eq f g)

  public export
  CompIsId : {a, b : FinSetObj} ->
    (g : FinSetMorph b a) -> (f : FinSetMorph a b) -> Type
  CompIsId {a} {b} g f = FinSetMorphEq (FSM_comp g f) (FSM_id a)

  public export
  AreInverses : {a, b : FinSetObj} ->
    (g : FinSetMorph b a) -> (f : FinSetMorph a b) -> Type
  AreInverses g f = (CompIsId g f, CompIsId f g)

  public export
  IsIso : {a, b : FinSetObj} -> (0 _ : FinSetMorph b a) -> Type
  IsIso {a} {b} g = Exists0 (FinSetMorph a b) (\f => AreInverses g f)

  public export
  AreIso : FinSetObj -> FinSetObj -> Type
  AreIso a b = Exists0 (FinSetMorph a b) IsIso

  public export
  IsRegularMono : {a, b : FinSetObj} -> FinSetMorph a b -> Type
  IsRegularMono {a} {b} f =
    (c : FinSetObj ** g : FinSetMorph b c ** h : FinSetMorph b c **
     k : FinSetMorph a (FSO_Eq g h) **
     ii : IsIso k ** FinSetMorphEq (FSM_comp (FSM_univ (FSU_eq_elim g h)) k) f)

  -- A pullback is isomorphic to an equalizer of products.
  public export
  IsPullback : {a, b, c : FinSetObj} ->
    (f : FinSetMorph a c) -> (g : FinSetMorph b c) -> Type
  IsPullback {a} {b} {c} f g =
    AreIso c $ FSO_Eq
      (FSM_comp f (FSM_univ (FSU_proj_1 a b)))
      (FSM_comp g (FSM_univ (FSU_proj_2 a b)))

  public export
  data FinSetMorphEq :
      FinSetMorph dom cod -> FinSetMorph dom cod -> Type where

    --
    -- Equivalence
    --
    FSME_refl : (f : FinSetMorph a b) -> FinSetMorphEq f f
    FSME_sym : FinSetMorphEq f g -> FinSetMorphEq g f
    FSME_trans : FinSetMorphEq h g -> FinSetMorphEq g f -> FinSetMorphEq h f

    --
    -- Congruence (rewriting)
    --
    FSME_rewL : FinSetMorphEq f g -> FinSetMorphEq (FSM_comp f h) (FSM_comp g h)
    FSME_rewR : FinSetMorphEq f g -> FinSetMorphEq (FSM_comp h f) (FSM_comp h g)

    --
    -- Category theory axioms
    --
    FSME_idL : {f : FinSetMorph a b} -> FinSetMorphEq f (FSM_comp (FSM_id b) f)
    FSME_idR : {f : FinSetMorph a b} -> FinSetMorphEq f (FSM_comp f (FSM_id a))
    FSME_assoc :
      FinSetMorphEq (FSM_comp h (FSM_comp g f)) (FSM_comp (FSM_comp h g) f)

    --
    -- Universal properties
    --

    -- Initial object
    FSME_0 : (0 f : FinSetMorph FSO_0 a) -> FinSetMorphEq f (FSM_univ (FSU_0 a))

    -- Terminal object
    FSME_1 : (0 f : FinSetMorph a FSO_1) -> FinSetMorphEq f (FSM_univ (FSU_1 a))

    -- Coproduct
    FSME_C_l : (0 f : FinSetMorph a b) -> (0 g : FinSetMorph a' b) ->
      FinSetMorphEq
        f
        (FSM_comp (FSM_adj (FSM_case f g)) (FSM_univ (FSU_inj_l a a')))
    FSME_C_r : (0 f : FinSetMorph a b) -> (0 g : FinSetMorph a' b) ->
      FinSetMorphEq
        g
        (FSM_comp (FSM_adj (FSM_case f g)) (FSM_univ (FSU_inj_r a a')))
    FSME_C_u : {0 f : FinSetMorph a b} -> {0 g : FinSetMorph a' b} ->
      {0 h : FinSetMorph (FSO_C a a') b} ->
      FinSetMorphEq f (FSM_comp h (FSM_univ (FSU_inj_l a a'))) ->
      FinSetMorphEq g (FSM_comp h (FSM_univ (FSU_inj_r a a'))) ->
      FinSetMorphEq h (FSM_adj (FSM_case f g))
    FSME_C_rew : {0 f, f' : FinSetMorph a c} -> {0 g, g' : FinSetMorph b c} ->
      FinSetMorphEq f f' -> FinSetMorphEq g g' ->
      FinSetMorphEq (FSM_adj (FSM_case f g)) (FSM_adj (FSM_case f' g'))
    FSME_C_sub_l : {0 f, f' : FinSetMorph a c} -> {0 g, g' : FinSetMorph b c} ->
      FinSetMorphEq (FSM_adj (FSM_case f g)) (FSM_adj (FSM_case f' g')) ->
      FinSetMorphEq f f'
    FSME_C_sub_r : {0 f, f' : FinSetMorph a c} -> {0 g, g' : FinSetMorph b c} ->
      FinSetMorphEq (FSM_adj (FSM_case f g)) (FSM_adj (FSM_case f' g')) ->
      FinSetMorphEq g g'

    -- Product
    FSME_P_1 : (0 f : FinSetMorph a b) -> (0 g : FinSetMorph a b') ->
      FinSetMorphEq
        f
        (FSM_comp (FSM_univ (FSU_proj_1 b b')) (FSM_adj (FSM_pair f g)))
    FSME_P_2 : (0 f : FinSetMorph a b) -> (0 g : FinSetMorph a b') ->
      FinSetMorphEq
        g
        (FSM_comp (FSM_univ (FSU_proj_2 b b')) (FSM_adj (FSM_pair f g)))
    FSME_P_u : {0 f : FinSetMorph a b} -> {0 g : FinSetMorph a b'} ->
      {0 h : FinSetMorph a (FSO_P b b')} ->
      FinSetMorphEq f (FSM_comp (FSM_univ (FSU_proj_1 b b')) h) ->
      FinSetMorphEq g (FSM_comp (FSM_univ (FSU_proj_2 b b')) h) ->
      FinSetMorphEq h (FSM_adj (FSM_pair f g))
    FSME_P_rew : {0 f, f' : FinSetMorph a b} -> {0 g, g' : FinSetMorph a c} ->
      FinSetMorphEq f f' -> FinSetMorphEq g g' ->
      FinSetMorphEq (FSM_adj (FSM_pair f g)) (FSM_adj (FSM_pair f' g'))
    FSME_P_sub_1 : {0 f, f' : FinSetMorph a b} -> {0 g, g' : FinSetMorph a c} ->
      FinSetMorphEq (FSM_adj (FSM_pair f g)) (FSM_adj (FSM_pair f' g')) ->
      FinSetMorphEq f f'
    FSME_P_sub_2 : {0 f, f' : FinSetMorph a b} -> {0 g, g' : FinSetMorph a c} ->
      FinSetMorphEq (FSM_adj (FSM_pair f g)) (FSM_adj (FSM_pair f' g')) ->
      FinSetMorphEq g g'

    -- Distributivity
    FSME_distrib_iso_l : (0 a, b, c : FinSetObj) ->
      FinSetMorphEq
        (FSM_id (FSO_P a (FSO_C b c)))
        (FSM_comp
          (FSM_adj (FSM_pair
            (FSM_adj (FSM_case
              (FSM_univ (FSU_proj_1 a b))
              (FSM_univ (FSU_proj_1 a c))))
            (FSM_adj (FSM_case
              (FSM_comp
                (FSM_univ (FSU_inj_l b c))
                (FSM_univ (FSU_proj_2 a b)))
              (FSM_comp
                (FSM_univ (FSU_inj_r b c))
                (FSM_univ (FSU_proj_2 a c)))))))
          (FSM_univ (FSU_distrib a b c)))

    FSME_distrib_iso_r : (0 a, b, c : FinSetObj) ->
      FinSetMorphEq
        (FSM_id (FSO_C (FSO_P a b) (FSO_P a c)))
        (FSM_comp
          (FSM_univ (FSU_distrib a b c))
          (FSM_adj (FSM_pair
            (FSM_adj (FSM_case
              (FSM_univ (FSU_proj_1 a b))
              (FSM_univ (FSU_proj_1 a c))))
            (FSM_adj (FSM_case
              (FSM_comp
                (FSM_univ (FSU_inj_l b c))
                (FSM_univ (FSU_proj_2 a b)))
              (FSM_comp
                (FSM_univ (FSU_inj_r b c))
                (FSM_univ (FSU_proj_2 a c))))))))

    -- Hom-object
    FSME_H_univ :
      (0 g : FinSetMorph (FSO_P x y) z) ->
      FinSetMorphEq
        g
        (FSM_comp
          (FSM_univ (FSU_eval y z))
          -- We have to spell out `(FSM_adj (FSM_curry g)) _x_ (FSM_id y)`
          -- here since Idris won't let us define it as a utility function
          -- in the `mutual` block.
          (FSM_adj
            (FSM_pair
              (FSM_comp (FSM_adj (FSM_curry g)) (FSM_univ (FSU_proj_1 x y)))
              (FSM_comp (FSM_id y) (FSM_univ (FSU_proj_2 x y)))
            )
          )
        )
    FSME_H_unique :
      (0 g : FinSetMorph (FSO_P x y) z) -> (0 h : FinSetMorph x (FSO_H y z)) ->
      FinSetMorphEq
        g
        (FSM_comp
          (FSM_univ (FSU_eval y z))
          -- We have to spell out `h _x_ (FSM_id y)`
          -- here since Idris won't let us define it as a utility function
          -- in the `mutual` block.
          (FSM_adj
            (FSM_pair
              (FSM_comp h (FSM_univ (FSU_proj_1 x y)))
              (FSM_comp (FSM_id y) (FSM_univ (FSU_proj_2 x y)))
            )
          )
        ) ->
      FinSetMorphEq h (FSM_adj (FSM_curry g))
    FSME_cur_subst : {0 g, g' : FinSetMorph (FSO_P x y) z} ->
      FinSetMorphEq g g' ->
      FinSetMorphEq (FSM_adj (FSM_curry g)) (FSM_adj (FSM_curry g'))
    FSME_cur_rew : {0 g, g' : FinSetMorph (FSO_P x y) z} ->
      FinSetMorphEq (FSM_adj (FSM_curry g)) (FSM_adj (FSM_curry g')) ->
      FinSetMorphEq g g'

    -- Equalizer
    FSME_eq_inj : (0 f, g : FinSetMorph a b) ->
      FinSetMorphEq
        (FSM_comp f (FSM_univ (FSU_eq_elim f g)))
        (FSM_comp g (FSM_univ (FSU_eq_elim f g)))

    FSME_eq_intro : {0 h : FinSetMorph c a} -> {0 f, g : FinSetMorph a b} ->
      (eq : FinSetMorphEq (FSM_comp f h) (FSM_comp g h)) ->
      FinSetMorphEq
        h
        (FSM_comp
          (FSM_univ (FSU_eq_elim f g))
          (FSM_adj (FSM_eq_intro h f g eq)))

    FSME_eq_intro_proof_irr :
      {0 h : FinSetMorph c a} -> {0 f, g : FinSetMorph a b} ->
      (eq, eq' : FinSetMorphEq (FSM_comp f h) (FSM_comp g h)) ->
      FinSetMorphEq
        (FSM_adj (FSM_eq_intro h f g eq))
        (FSM_adj (FSM_eq_intro h f g eq'))

    -- Coequalizer
    FSME_coeq_inj : (0 f, g : FinSetMorph a b) ->
      FinSetMorphEq
        (FSM_comp (FSM_univ (FSU_coeq_intro f g)) f)
        (FSM_comp (FSM_univ (FSU_coeq_intro f g)) g)

    FSME_coeq_elim : {0 h : FinSetMorph b c} -> {0 f, g : FinSetMorph a b} ->
      (eq : FinSetMorphEq (FSM_comp h f) (FSM_comp h g)) ->
      FinSetMorphEq
        h
        (FSM_comp
          (FSM_adj (FSM_coeq_elim h f g eq))
          (FSM_univ (FSU_coeq_intro f g)))

    FSME_coeq_elim_proof_irr :
      {0 h : FinSetMorph b c} -> {0 f, g : FinSetMorph a b} ->
      (eq, eq' : FinSetMorphEq (FSM_comp h f) (FSM_comp h g)) ->
      FinSetMorphEq
          (FSM_adj (FSM_coeq_elim h f g eq))
          (FSM_adj (FSM_coeq_elim h f g eq'))

    -- Equalizer/regular-monomorphism classifier
    FSME_EC_chi_commutes : {0 a, b : FinSetObj} ->
      (f, g : FinSetMorph a b) ->
      FinSetMorphEq
        (FSM_comp
          (FSM_univ (FSU_chi f g))
          (FSM_univ (FSU_eq_elim f g)))
        (FSM_comp
          (FSM_univ (FSU_inj_r FSO_1 FSO_1))
          (FSM_univ (FSU_1 (FSO_Eq f g))))
    FSM_EC_inj_commutes :
      {0 a, b, c : FinSetObj} -> {0 f, g : FinSetMorph a b} ->
      {h : FinSetMorph c a} ->
      (eq : FinSetMorphEq
        (FSM_comp (FSM_univ (FSU_inj_r FSO_1 FSO_1)) (FSM_univ (FSU_1 c)))
        (FSM_comp (FSM_univ (FSU_chi f g)) h)) ->
      FinSetMorphEq
        h
        (FSM_comp (FSM_univ (FSU_eq_elim f g)) (FSM_adj (FSM_ec_inj eq)))
    FSM_EC_inj_proof_irr :
      {0 a, b, c : FinSetObj} -> {0 f, g : FinSetMorph a b} ->
      {h : FinSetMorph c a} ->
      (eq, eq' : FinSetMorphEq
        (FSM_comp (FSM_univ (FSU_inj_r FSO_1 FSO_1)) (FSM_univ (FSU_1 c)))
        (FSM_comp (FSM_univ (FSU_chi f g)) h)) ->
      FinSetMorphEq
        (FSM_adj (FSM_ec_inj eq))
        (FSM_adj (FSM_ec_inj eq'))
    FSM_EC_inj_unique :
      {0 a, b, c : FinSetObj} -> {0 f, g : FinSetMorph a b} ->
      {h : FinSetMorph c a} -> {k : FinSetMorph c (FSO_Eq f g)} ->
      (eq : FinSetMorphEq
        (FSM_comp (FSM_univ (FSU_inj_r FSO_1 FSO_1)) (FSM_univ (FSU_1 c)))
        (FSM_comp (FSM_univ (FSU_chi f g)) h)) ->
      FinSetMorphEq
        h
        (FSM_comp (FSM_univ (FSU_eq_elim f g)) k) ->
      FinSetMorphEq
        k
        (FSM_adj (FSM_ec_inj eq))

mutual
  public export
  record FinSetSlObj (base : FinSetObj) where
    constructor FSlObj
    fsloTot : FinSetObj
    fsloProj : FinSetMorph fsloTot base

  public export
  record FinSetSlMorph (dom, cod : FinSetSlObj base) where
    constructor FSlMorph
    fslmTot : FinSetMorph (fsloTot dom) (fsloTot cod)
    fslmComm : FinSetMorphEq (fsloProj dom) (FSM_comp (fsloProj cod) fslmTot)

--------------------------------------
--------------------------------------
---- W-type version of core logic ----
--------------------------------------
--------------------------------------

public export
data Order : Type where
  OrdN : Nat -> Order  -- 0 is FinSet; 1 is primitive recursion
  OrdW : Order         -- higher-order arithmetic
  OrdT : Order         -- Turing-complete

public export
data PerCatDir : Type where
  CStd : PerCatDir
  COp : PerCatDir

public export
data PerCatClass : Type where
  PC_OBJ : PerCatClass
  PC_OBJ_EQ : PerCatClass
  PC_MORPH : PerCatClass
  PC_MORPH_EQ : PerCatClass

public export
data PerDoubleCatClass : Type where
  PDC_CELL : PerDoubleCatClass
  PDC_CELL_EQ : PerDoubleCatClass

mutual
  public export
  data Ord0Obj : Type where

  public export
  data Ord0ObjEq : Ord0Obj -> Ord0Obj -> Type where

  public export
  data Ord0Vert : Ord0Obj -> Ord0Obj -> Type where

  public export
  data Ord0VEq : {dom, dom', cod, cod' : Ord0Obj} ->
      Ord0ObjEq dom dom' -> Ord0ObjEq cod cod' ->
      Ord0Vert dom cod -> Ord0Vert dom' cod' ->
      Type where

  public export
  data Ord0Horiz : Ord0Obj -> Ord0Obj -> Type where

  public export
  data Ord0HEq : {dom, dom', cod, cod' : Ord0Obj} ->
      Ord0ObjEq dom dom' -> Ord0ObjEq cod cod' ->
      Ord0Horiz dom cod -> Ord0Horiz dom' cod' ->
      Type where

-------------------------------------------------------------------------
-------------------------------------------------------------------------
---- FinSet without id, composition, or (co)equality/dependent types ----
-------------------------------------------------------------------------
-------------------------------------------------------------------------

-----------------------------------------------------
-----------------------------------------------------
---- Minimal bicartesian distributive categories ----
-----------------------------------------------------
-----------------------------------------------------

------------------------------------------------------
---- Objects included in any bicartesian category ----
------------------------------------------------------

public export
data BCDOPos : Type where
  BCDO_0 : BCDOPos
  BCDO_1 : BCDOPos
  BCDO_C : BCDOPos
  BCDO_P : BCDOPos

public export
Show BCDOPos where
  show BCDO_0 = "0"
  show BCDO_1 = "1"
  show BCDO_C = "+"
  show BCDO_P = "*"

public export
BCDOPosSz : Nat
BCDOPosSz = 4

public export
BCDOVectDecoder : VectDecoder BCDOPos BCDOPosSz
BCDOVectDecoder = [ BCDO_0, BCDO_1, BCDO_C, BCDO_P ]

public export
BCDOVectEncoder : VectEncoder BCDOVectDecoder
BCDOVectEncoder BCDO_0 = (0 ** Refl ** Refl)
BCDOVectEncoder BCDO_1 = (1 ** Refl ** Refl)
BCDOVectEncoder BCDO_C = (2 ** Refl ** Refl)
BCDOVectEncoder BCDO_P = (3 ** Refl ** Refl)

public export
BCDOFinDecEncoding : FinDecEncoding BCDOPos BCDOPosSz
BCDOFinDecEncoding = VectDecEncoding BCDOVectDecoder BCDOVectEncoder

public export
DecEq BCDOPos where
  decEq = fdeDecEq BCDOFinDecEncoding

public export
BicartDistInitialDir : Type
BicartDistInitialDir = Void

public export
BicartDistTerminalDir : Type
BicartDistTerminalDir = Void

public export
data BicartDistCoproductDir : Type where
  BCDCopL : BicartDistCoproductDir
  BCDCopR : BicartDistCoproductDir

public export
Show BicartDistCoproductDir where
  show BCDCopL = "l"
  show BCDCopR = "r"

public export
Eq BicartDistCoproductDir where
  BCDCopL == BCDCopL = True
  BCDCopR == BCDCopR = True
  _ == _ = False

public export
data BicartDistProductDir : Type where
  BCDProd1 : BicartDistProductDir
  BCDProd2 : BicartDistProductDir

public export
Show BicartDistProductDir where
  show BCDProd1 = "fst"
  show BCDProd2 = "snd"

public export
Eq BicartDistProductDir where
  BCDProd1 == BCDProd1 = True
  BCDProd2 == BCDProd2 = True
  _ == _ = False

public export
BicartDistObjDir : SliceObj BCDOPos
BicartDistObjDir BCDO_0 = BicartDistInitialDir
BicartDistObjDir BCDO_1 = BicartDistTerminalDir
BicartDistObjDir BCDO_C = BicartDistCoproductDir
BicartDistObjDir BCDO_P = BicartDistProductDir

public export
BicartDistObjF : PolyFunc
BicartDistObjF = (BCDOPos ** BicartDistObjDir)

public export
BicartDistObj : Type
BicartDistObj = PolyFuncMu BicartDistObjF

public export
BCDOAlg : SliceObj Type
BCDOAlg = PFAlg BicartDistObjF

public export
bcdoCata : {0 a : Type} -> BCDOAlg a -> BicartDistObj -> a
bcdoCata = pfCata {p=BicartDistObjF}

public export
BCDOShowAlg : BCDOAlg String
BCDOShowAlg BCDO_0 dir = show BCDO_0
BCDOShowAlg BCDO_1 dir = show BCDO_1
BCDOShowAlg BCDO_C dir =
  "[" ++ dir BCDCopL ++ " " ++ show BCDO_C ++ " " ++ dir BCDCopR ++ "]"
BCDOShowAlg BCDO_P dir =
  "(" ++ dir BCDProd1 ++ " " ++ show BCDO_P ++ " " ++ dir BCDProd2 ++ ")"

public export
bcdoShow : BicartDistObj -> String
bcdoShow = bcdoCata BCDOShowAlg

public export
Show BicartDistObj where
  show = bcdoShow

public export
BCDOProductAlg : SliceObj Type
BCDOProductAlg = PFProductAlg BicartDistObjF BicartDistObjF

public export
bcdoProductCata : {0 a : Type} ->
  BCDOProductAlg a -> BicartDistObj -> BicartDistObj -> a
bcdoProductCata = pfProductCata {p=BicartDistObjF}

public export
BCDOEqAlg : PFProductBoolAlg BicartDistObjF BicartDistObjF
BCDOEqAlg =
  [
    ((BCDO_0, BCDO_0) **
     [])
  , ((BCDO_1, BCDO_1) **
     [])
  , ((BCDO_C, BCDO_C) **
     [ (BCDCopL, BCDCopL), (BCDCopR, BCDCopR) ])
  , ((BCDO_P, BCDO_P) **
     [ (BCDProd1, BCDProd1), (BCDProd2, BCDProd2) ]
    )
  ]

public export
bcdoEq : BicartDistObj -> BicartDistObj -> Bool
bcdoEq = pfProductBoolCata decEq decEq BCDOEqAlg

public export
Eq BicartDistObj where
  (==) = bcdoEq

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Terms (global elements) of objects of bicartesian categories ----
----------------------------------------------------------------------
----------------------------------------------------------------------

public export
data BCDTPos : Type where
  BCDT_U : BCDTPos
  BCDT_L : BCDTPos
  BCDT_R : BCDTPos
  BCDT_P : BCDTPos

public export
Show BCDTPos where
  show BCDT_U = "_"
  show BCDT_L = "l"
  show BCDT_R = "r"
  show BCDT_P = ","

public export
BCDTPosSz : Nat
BCDTPosSz = 4

public export
BCDTFinDecoder : FinDecoder BCDTPos BCDTPosSz
BCDTFinDecoder FZ = BCDT_U
BCDTFinDecoder (FS FZ) = BCDT_L
BCDTFinDecoder (FS (FS FZ)) = BCDT_R
BCDTFinDecoder (FS (FS (FS FZ))) = BCDT_P

public export
BCDTNatEncoder : NatEncoder BCDTFinDecoder
BCDTNatEncoder BCDT_U = (0 ** Refl ** Refl)
BCDTNatEncoder BCDT_L = (1 ** Refl ** Refl)
BCDTNatEncoder BCDT_R = (2 ** Refl ** Refl)
BCDTNatEncoder BCDT_P = (3 ** Refl ** Refl)

public export
BCDTFinDecEncoding : FinDecEncoding BCDTPos BCDTPosSz
BCDTFinDecEncoding = NatDecEncoding BCDTFinDecoder BCDTNatEncoder

public export
DecEq BCDTPos where
  decEq = fdeDecEq BCDTFinDecEncoding

public export
BicartDistTermUnitDir : Type
BicartDistTermUnitDir = Void

public export
data BicartDistTermLeftDir : Type where
  BCDTermL : BicartDistTermLeftDir

public export
Show BicartDistTermLeftDir where
  show BCDTermL = show BCDT_L

public export
Eq BicartDistTermLeftDir where
  BCDTermL == BCDTermL = True

public export
data BicartDistTermRightDir : Type where
  BCDTermR : BicartDistTermRightDir

public export
Show BicartDistTermRightDir where
  show BCDTermR = show BCDT_R

public export
Eq BicartDistTermRightDir where
  BCDTermR == BCDTermR = True

public export
data BicartDistTermPairDir : Type where
  BCDTerm1 : BicartDistTermPairDir
  BCDTerm2 : BicartDistTermPairDir

public export
Show BicartDistTermPairDir where
  show BCDTerm1 = show BCDProd1
  show BCDTerm2 = show BCDProd2

public export
Eq BicartDistTermPairDir where
  BCDTerm1 == BCDTerm1 = True
  BCDTerm2 == BCDTerm2 = True
  _ == _ = False

public export
BicartDistTermDir : SliceObj BCDTPos
BicartDistTermDir BCDT_U = BicartDistTermUnitDir
BicartDistTermDir BCDT_L = BicartDistTermLeftDir
BicartDistTermDir BCDT_R = BicartDistTermRightDir
BicartDistTermDir BCDT_P = BicartDistTermPairDir

public export
BicartDistTermF : PolyFunc
BicartDistTermF = (BCDTPos ** BicartDistTermDir)

public export
BicartDistTerm : Type
BicartDistTerm = PolyFuncMu BicartDistTermF

public export
BicartDistTrAlg : SliceObj Type
BicartDistTrAlg = PFAlg BicartDistTermF

public export
bicartDistTermCata : {0 a : Type} -> BicartDistTrAlg a -> BicartDistTerm -> a
bicartDistTermCata = pfCata {p=BicartDistTermF}

public export
BCDTShowAlg : BicartDistTrAlg String
BCDTShowAlg BCDT_U dir =
  show BCDT_U
BCDTShowAlg BCDT_L dir =
  show BCDT_L ++ "[" ++ dir BCDTermL ++ "]"
BCDTShowAlg BCDT_R dir =
  show BCDT_R ++ "[" ++ dir BCDTermR ++ "]"
BCDTShowAlg BCDT_P dir =
  "(" ++ dir BCDTerm1 ++ " " ++ show BCDT_P ++ " " ++ dir BCDTerm2 ++ ")"

public export
bcdtShow : BicartDistTerm -> String
bcdtShow = bicartDistTermCata BCDTShowAlg

public export
Show BicartDistTerm where
  show = bcdtShow

public export
BCDTProductAlg : SliceObj Type
BCDTProductAlg = PFProductAlg BicartDistTermF BicartDistTermF

public export
bcdtProductCata : {0 a : Type} ->
  BCDTProductAlg a -> BicartDistTerm -> BicartDistTerm -> a
bcdtProductCata = pfProductCata {p=BicartDistTermF}

public export
BCDTEqAlg : PFProductBoolAlg BicartDistTermF BicartDistTermF
BCDTEqAlg =
  [
    ((BCDT_U, BCDT_U) **
     [])
  , ((BCDT_L, BCDT_L) **
     [ (BCDTermL, BCDTermL) ])
  , ((BCDT_R, BCDT_R) **
     [ (BCDTermR, BCDTermR) ])
  , ((BCDT_P, BCDT_P) **
     [ (BCDTerm1, BCDTerm1), (BCDTerm2, BCDTerm2) ]
    )
  ]

public export
bcdtEq : BicartDistTerm -> BicartDistTerm -> Bool
bcdtEq = pfProductBoolCata decEq decEq BCDTEqAlg

public export
Eq BicartDistTerm where
  (==) = bcdtEq

public export
BCDObjTrAlg : SliceObj Type
BCDObjTrAlg = PFProductAlg BicartDistTermF BicartDistObjF

public export
bcdObjTermCata : {0 a : Type} ->
  BCDObjTrAlg a -> BicartDistTerm -> BicartDistObj -> a
bcdObjTermCata = pfProductCata {p=BicartDistTermF} {q=BicartDistObjF}

-- Type-checking for terms against objects (determing whether a given general
-- term is a term of a given object).
public export
BicartDistTermCheckAlg : PFProductBoolAlg BicartDistTermF BicartDistObjF
BicartDistTermCheckAlg =
  [
    ((BCDT_U, BCDO_1) **
     [])
  , ((BCDT_L, BCDO_C) **
     [(BCDTermL, BCDCopL)])
  , ((BCDT_R, BCDO_C) **
     [(BCDTermR, BCDCopR)])
  , ((BCDT_P, BCDO_P) **
     [ (BCDTerm1, BCDProd1), (BCDTerm2, BCDProd2) ]
    )
  ]

public export
bicartDistTermCheck : BicartDistTerm -> BicartDistObj -> Bool
bicartDistTermCheck = pfProductBoolCata decEq decEq BicartDistTermCheckAlg

-- The type-checking allows us to view a checked term as a slice object.
public export
BicartDistTypedTerm : SliceObj BicartDistObj
BicartDistTypedTerm a =
  Refinement {a=BicartDistTerm} (flip bicartDistTermCheck a)

public export
MkBicartDistTypedTerm : {0 o : BicartDistObj} -> (t : BicartDistTerm) ->
  {auto 0 checks : IsTrue (bicartDistTermCheck t o)} -> BicartDistTypedTerm o
MkBicartDistTypedTerm t {checks} = MkRefinement {a=BicartDistTerm} t

-------------------
---- Utilities ----
-------------------

public export
BCDTNumLeavesAlg : BicartDistTrAlg Nat
BCDTNumLeavesAlg BCDT_U d = 1
BCDTNumLeavesAlg BCDT_L d = d BCDTermL
BCDTNumLeavesAlg BCDT_R d = d BCDTermR
BCDTNumLeavesAlg BCDT_P d = d BCDTerm1 + d BCDTerm2

public export
bcdtNumLeaves : BicartDistTerm -> Nat
bcdtNumLeaves = bicartDistTermCata BCDTNumLeavesAlg

public export
BCDTNumInternalNodesAlg : BicartDistTrAlg Nat
BCDTNumInternalNodesAlg BCDT_U d = 0
BCDTNumInternalNodesAlg BCDT_L d = 1 + d BCDTermL
BCDTNumInternalNodesAlg BCDT_R d = 1 + d BCDTermR
BCDTNumInternalNodesAlg BCDT_P d = 1 + d BCDTerm1 + d BCDTerm2

public export
bcdtNumInternalNodes : BicartDistTerm -> Nat
bcdtNumInternalNodes = bicartDistTermCata BCDTNumInternalNodesAlg

public export
BCDTSizeAlg : BicartDistTrAlg Nat
BCDTSizeAlg BCDT_U d = 1
BCDTSizeAlg BCDT_L d = 1 + d BCDTermL
BCDTSizeAlg BCDT_R d = 1 + d BCDTermR
BCDTSizeAlg BCDT_P d = 1 + d BCDTerm1 + d BCDTerm2

public export
bcdtSize : BicartDistTerm -> Nat
bcdtSize = bicartDistTermCata BCDTSizeAlg

public export
BCDTDepthAlg : BicartDistTrAlg Nat
BCDTDepthAlg BCDT_U d = 0
BCDTDepthAlg BCDT_L d = 1 + d BCDTermL
BCDTDepthAlg BCDT_R d = 1 + d BCDTermR
BCDTDepthAlg BCDT_P d = 1 + maximum (d BCDTerm1) (d BCDTerm2)

public export
bcdtDepth : BicartDistTerm -> Nat
bcdtDepth = bicartDistTermCata BCDTDepthAlg

---------------------------------------------------------------------
---------------------------------------------------------------------
---- Morphisms included in any bicartesian distributive category ----
---------------------------------------------------------------------
---------------------------------------------------------------------

public export
data BicartDistReducedMorphPos : Type where
  BCDRMorphId : BicartDistReducedMorphPos
  BCDRMorphAbsurd : BicartDistReducedMorphPos
  BCDRMorphConst : BicartDistReducedMorphPos
  BCDRMorphInjL : BicartDistReducedMorphPos
  BCDRMorphInjR : BicartDistReducedMorphPos
  BCDRMorphCase : BicartDistReducedMorphPos
  BCDRMorphBi : BicartDistReducedMorphPos
  BCDRMorphProj1 : BicartDistReducedMorphPos
  BCDRMorphProj2 : BicartDistReducedMorphPos
  BCDRMorphDist : BicartDistReducedMorphPos

public export
Eq BicartDistReducedMorphPos where
  BCDRMorphId == BCDRMorphId = True
  BCDRMorphAbsurd == BCDRMorphAbsurd = True
  BCDRMorphConst == BCDRMorphConst = True
  BCDRMorphInjL == BCDRMorphInjL = True
  BCDRMorphInjR == BCDRMorphInjR = True
  BCDRMorphCase == BCDRMorphCase = True
  BCDRMorphBi == BCDRMorphBi = True
  BCDRMorphProj1 == BCDRMorphProj1 = True
  BCDRMorphProj2 == BCDRMorphProj2 = True
  BCDRMorphDist == BCDRMorphDist = True
  _ == _ = False

public export
data BicartDistReducedMorphDirObj : SliceObj BicartDistReducedMorphPos where
  BCDRMorphIdDir : BicartDistReducedMorphDirObj BCDRMorphId
  BCDRMorphAbsurdDom : BicartDistReducedMorphDirObj BCDRMorphAbsurd
  BCDRMorphAbsurdCod : BicartDistReducedMorphDirObj BCDRMorphAbsurd
  BCDRMorphConstDom : BicartDistReducedMorphDirObj BCDRMorphConst
  BCDRMorphConstCod : BicartDistReducedMorphDirObj BCDRMorphConst
  BCDRMorphInjLDom : BicartDistReducedMorphDirObj BCDRMorphInjL
  BCDRMorphInjLCodR : BicartDistReducedMorphDirObj BCDRMorphInjL
  BCDRMorphInjRDom : BicartDistReducedMorphDirObj BCDRMorphInjR
  BCDRMorphInjRCodL : BicartDistReducedMorphDirObj BCDRMorphInjR
  BCDRMorphCaseDomL : BicartDistReducedMorphDirObj BCDRMorphCase
  BCDRMorphCaseDomR : BicartDistReducedMorphDirObj BCDRMorphCase
  BCDRMorphCaseCod : BicartDistReducedMorphDirObj BCDRMorphCase
  BCDRMorphBiDom : BicartDistReducedMorphDirObj BCDRMorphBi
  BCDRMorphBiCodL : BicartDistReducedMorphDirObj BCDRMorphBi
  BCDRMorphBiCodR : BicartDistReducedMorphDirObj BCDRMorphBi
  BCDRMorphProj1DomR : BicartDistReducedMorphDirObj BCDRMorphProj1
  BCDRMorphProj1Cod : BicartDistReducedMorphDirObj BCDRMorphProj1
  BCDRMorphProj2DomL : BicartDistReducedMorphDirObj BCDRMorphProj2
  BCDRMorphProj2Cod : BicartDistReducedMorphDirObj BCDRMorphProj2
  BCDRMorphDistDom1 : BicartDistReducedMorphDirObj BCDRMorphDist
  BCDRMorphDistDom2L : BicartDistReducedMorphDirObj BCDRMorphDist
  BCDRMorphDistDom2R : BicartDistReducedMorphDirObj BCDRMorphDist

public export
data BicartDistReducedMorphDirTerm : SliceObj BicartDistReducedMorphPos where
  BCDRMorphTerm : BicartDistReducedMorphDirTerm BCDRMorphConst

public export
data BicartDistReducedMorphDirMorph : SliceObj BicartDistReducedMorphPos where
  BCDRMorphContra : BicartDistReducedMorphDirMorph BCDRMorphAbsurd
  BCDRMorphCases : BicartDistReducedMorphDirMorph BCDRMorphCase
  BCDRMorphComponents : BicartDistReducedMorphDirMorph BCDRMorphBi

public export
data BicartDistReducedMorphPosBase : Type where
  BCDRMorphPosMorph : BicartDistReducedMorphPosBase
  BCDRMorphPosObj : BicartDistReducedMorphPosBase
  BCDRMorphPosTerm : BicartDistReducedMorphPosBase

public export
BicartDistReducedMorphPosDep : SliceObj BicartDistReducedMorphPosBase
BicartDistReducedMorphPosDep BCDRMorphPosMorph = BicartDistReducedMorphPos
BicartDistReducedMorphPosDep BCDRMorphPosObj = BCDOPos
BicartDistReducedMorphPosDep BCDRMorphPosTerm = BCDTPos

public export
BicartDistReducedMorphDirDep : SliceObj (Sigma BicartDistReducedMorphPosDep)
BicartDistReducedMorphDirDep (BCDRMorphPosMorph ** i) =
  BicartDistReducedMorphDirMorph i
BicartDistReducedMorphDirDep (BCDRMorphPosObj ** i) =
  BicartDistObjDir i
BicartDistReducedMorphDirDep (BCDRMorphPosTerm ** i) =
  BicartDistTermDir i

public export
BicartDistReducedMorphIdSlice :
  SlicePolyEndoFuncId BicartDistReducedMorphPosBase
BicartDistReducedMorphIdSlice =
  (BicartDistReducedMorphPosDep ** BicartDistReducedMorphDirDep)

public export
BicartDistUnrefinedReducedMorphSPF :
  SlicePolyEndoFunc BicartDistReducedMorphPosBase
BicartDistUnrefinedReducedMorphSPF =
  SlicePolyEndoFuncFromId BicartDistReducedMorphIdSlice

public export
BicartDistUnrefinedReducedMorphSlice : SliceObj BicartDistReducedMorphPosBase
BicartDistUnrefinedReducedMorphSlice = SPFMu BicartDistUnrefinedReducedMorphSPF

public export
BicartDistUnrefinedReducedMorph : Type
BicartDistUnrefinedReducedMorph =
  BicartDistUnrefinedReducedMorphSlice BCDRMorphPosMorph

----------------------------------------------------------------------------
----------------------------------------------------------------------------
---- Polynomial functors in locally bicartesian distributive categories ----
----------------------------------------------------------------------------
----------------------------------------------------------------------------

public export
data PolyBCDPosPoly : Type where
  PolyBCDPosPF : BCDOPos -> PolyBCDPosPoly
  PolyBCDPosSlice : BCDOPos -> PolyBCDPosPoly

public export
data PolyBCDPosBase : Type where
  PolyBCDSourceObj : PolyBCDPosBase
  PolyBCDPoly : PolyBCDPosBase

public export
PolyBCDPosDep : SliceObj PolyBCDPosBase
PolyBCDPosDep PolyBCDSourceObj = BCDOPos
PolyBCDPosDep PolyBCDPoly = PolyBCDPosPoly

public export
PolyBCDPos : Type
PolyBCDPos = DPair PolyBCDPosBase PolyBCDPosDep

---------------------------------
---------------------------------
---- Programmer's finite set ----
---------------------------------
---------------------------------

----------------------------------------
----------------------------------------
---- Categories as initial algebras ----
----------------------------------------
----------------------------------------

public export
data CatObj : (obj : Type) -> (obj -> obj -> Type) -> Type where

public export
data CatMorph : (obj : Type) -> (morph : obj -> obj -> Type) ->
    Either obj (CatObj obj morph) ->
    Either obj (CatObj obj morph) ->
    Type where
  CatMorphId :
    (x : obj) -> CatMorph obj morph (Left x) (Left x)
  CatMorphComp :
    {x, y, z : obj} ->
    CatMorph obj morph (Left y) (Left z) ->
    CatMorph obj morph (Left x) (Left y) ->
    CatMorph obj morph (Left x) (Left z)

public export
data InitialObj : (obj : Type) -> (obj -> obj -> Type) -> Type where
  InitialObjSelf : InitialObj obj morph

public export
InitialCatObj : (obj : Type) -> (obj -> obj -> Type) -> Type
InitialCatObj obj morph =
  Either obj (Either (CatObj obj morph) (InitialObj obj morph))

public export
data InitialMorph : (obj : Type) -> (morph : obj -> obj -> Type) ->
    InitialCatObj obj morph -> InitialCatObj obj morph -> Type where
  InitialMorphExFalso :
    (x : obj) ->
    InitialMorph obj morph (Right (Right InitialObjSelf)) (Left x)

public export
data TerminalObj : (obj : Type) -> (obj -> obj -> Type) -> Type where
  TerminalObjSelf : TerminalObj obj morph

public export
TerminalCatObj : (obj : Type) -> (obj -> obj -> Type) -> Type
TerminalCatObj obj morph =
  Either obj (Either (CatObj obj morph) (TerminalObj obj morph))

public export
data TerminalMorph : (obj : Type) -> (morph : obj -> obj -> Type) ->
    TerminalCatObj obj morph -> TerminalCatObj obj morph -> Type where
  TerminalMorphUnique :
    (x : obj) ->
    TerminalMorph obj morph (Left x) (Right (Right TerminalObjSelf))

public export
data InitTermCatObj : (obj : Type) -> (obj -> obj -> Type) -> Type where
  ITCObjSelf : obj -> InitTermCatObj obj morph
  ITCObjCat : CatObj obj morph -> InitTermCatObj obj morph
  ITCObjInit : InitialObj obj morph -> InitTermCatObj obj morph
  ITCObjTerm : TerminalObj obj morph -> InitTermCatObj obj morph

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
---- Interpretation of morphisms as metalanguage natural transformations ----
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

public export
MorphCovarNT : {obj : Type} -> (obj -> obj -> Type) -> obj -> obj -> Type
MorphCovarNT {obj} morph a b = (x : obj) -> morph b x -> morph a x

public export
MorphContravarNT : {obj : Type} -> (obj -> obj -> Type) -> obj -> obj -> Type
MorphContravarNT {obj} morph a b = (x : obj) -> morph x a -> morph x b

public export
MorphNT : {obj : Type} -> (obj -> obj -> Type) -> obj -> obj -> Type
MorphNT {obj} morph a b =
  Pair (MorphContravarNT {obj} morph a b) (MorphCovarNT {obj} morph a b)

public export
morphComposeNT :
  {obj : Type} -> {morph : obj -> obj -> Type} -> {a, b, c : obj} ->
  MorphNT {obj} morph b c -> MorphNT {obj} morph a b -> MorphNT {obj} morph a c
morphComposeNT {obj} {morph} {a} {b} {c} (g, g') (f, f') =
  (\x => g x . f x, \x => f' x . g' x)

public export
morphNTId :
  {obj : Type} -> {morph : obj -> obj -> Type} ->
  (a : obj) -> MorphNT {obj} morph a a
morphNTId {obj} {morph} a = (\_ => id, \_ => id)

-------------------------------
-------------------------------
---- Types with predicates ----
-------------------------------
-------------------------------

public export
PType : Type
PType = Subset0 Type SliceObj

public export
PBase : PType -> Type
PBase = fst0

public export
0 PPred : (x : PType) -> SliceObj (PBase x)
PPred = snd0

public export
PFunc : PType -> PType -> Type
PFunc x y = PBase x -> PBase y

public export
0 PPres : (x, y : PType) -> SliceObj (PFunc x y)
PPres x y f = (b : PBase x) -> PPred x b -> PPred y (f b)

public export
PMorph : PType -> PType -> Type
PMorph x y = Subset0 (PFunc x y) (PPres x y)

public export
PSigma : PType -> Type
PSigma x = Subset0 (PBase x) (PPred x)

--------------------------------
--------------------------------
---- Bicartesian categories ----
--------------------------------
--------------------------------

public export
data BicartObjF : Type -> Type where
  BCOInitial : BicartObjF a
  BCOTerminal : BicartObjF a
  BCOCoproduct : a -> a -> BicartObjF a
  BCOProduct : a -> a -> BicartObjF a

public export
data BicartObj : Type where
  InBCO : BicartObjF BicartObj -> BicartObj

public export
BCO0 : BicartObj
BCO0 = InBCO BCOInitial

public export
BCO1 : BicartObj
BCO1 = InBCO BCOInitial

public export
BCOC : BicartObj -> BicartObj -> BicartObj
BCOC = InBCO .* BCOCoproduct

public export
BCOP : BicartObj -> BicartObj -> BicartObj
BCOP = InBCO .* BCOProduct

public export
record BCOAlg (a : Type) where
  constructor MkBCOAlg
  bcoAlg0 : a
  bcoAlg1 : a
  bcoAlgC : a -> a -> a
  bcoAlgP : a -> a -> a

public export
bcoCata : BCOAlg a -> BicartObj -> a
bcoCata alg (InBCO BCOInitial) = alg.bcoAlg0
bcoCata alg (InBCO BCOTerminal) = alg.bcoAlg1
bcoCata alg (InBCO (BCOCoproduct x y)) =
  alg.bcoAlgC (bcoCata alg x) (bcoCata alg y)
bcoCata alg (InBCO (BCOProduct x y)) =
  alg.bcoAlgP (bcoCata alg x) (bcoCata alg y)

public export
record BCOCompAlg (a : Type) where
  constructor MkBCOCompAlg
  bcoCompAlg0 : a
  bcoCompAlg1 : a
  bcoCompAlgC : a -> a -> a

public export
bcoCompAlg : BCOCompAlg (a -> a) -> BCOAlg (a -> a)
bcoCompAlg (MkBCOCompAlg a0 a1 ac) =
  MkBCOAlg a0 a1 ac (.)

public export
bcoCompCata : BCOCompAlg (a -> a) -> BicartObj -> a -> a
bcoCompCata = bcoCata . bcoCompAlg

public export
BCOTrAlg : BCOAlg Type
BCOTrAlg = MkBCOAlg Void Unit Either Pair

public export
BCOTerm : BicartObj -> Type
BCOTerm = bcoCata BCOTrAlg

public export
BCOHomAlg : BCOCompAlg (BicartObj -> BicartObj)
BCOHomAlg = MkBCOCompAlg (const BCO1) id (biapp BCOP)

public export
bcoHomObj : BicartObj -> BicartObj -> BicartObj
bcoHomObj = bcoCompCata BCOHomAlg

public export
data PFSObjF : Type -> Type where
  PFSObjBC : BicartObjF a -> PFSObjF a
  PFSHomObj : a -> a -> PFSObjF a

public export
data PFSObj : Type where
  InPFSO : PFSObjF ProgFinSet.PFSObj -> PFSObj

public export
InPFSBC : BicartObjF ProgFinSet.PFSObj -> ProgFinSet.PFSObj
InPFSBC = ProgFinSet.InPFSO . PFSObjBC

public export
PFS0 : ProgFinSet.PFSObj
PFS0 = InPFSBC BCOInitial

public export
PFS1 : ProgFinSet.PFSObj
PFS1 = InPFSBC BCOTerminal

public export
PFSC : ProgFinSet.PFSObj -> ProgFinSet.PFSObj -> ProgFinSet.PFSObj
PFSC = InPFSBC .* BCOCoproduct

public export
PFSP : ProgFinSet.PFSObj -> ProgFinSet.PFSObj -> ProgFinSet.PFSObj
PFSP = InPFSBC .* BCOProduct

-- Endofunctors on the initial bicartesian distributive category (equivalently,
-- the initial bicartesian closed category).
public export
data PFSEFPosBase : Type where
  PPBObj : PFSEFPosBase
  PPBFunc : PFSEFPosBase

public export
data PFSEFF : (PFSEFPosBase -> Type) -> PFSEFPosBase -> Type where
  PPFObj : PFSObjF (a PPBObj) -> PFSEFF a PPBObj
  PPFCovarRep : a PPBObj -> PFSEFF a PPBFunc
  PPFFunc : PFSObjF (a PPBFunc) -> PFSEFF a PPBFunc

public export
data PFSEndoFuncMut : PFSEFPosBase -> Type where
  InPEFM : {0 i : PFSEFPosBase} -> PFSEFF PFSEndoFuncMut i -> PFSEndoFuncMut i

public export
PFSEndoFunc : Type
PFSEndoFunc = PFSEndoFuncMut PPBFunc

-- Endofunctors in the initial bicartesian category, indexed by the
-- type of their positions.
public export
data PFSDepObj : ProgFinSet.PFSObj -> Type where
  PFSDO0 : PFSDepObj PFS0
  PFSDOy : ProgFinSet.PFSObj -> PFSDepObj PFS1
  PFSDOC : PFSDepObj a -> PFSDepObj b -> PFSDepObj (PFSC a b)
  PFSDOP : PFSDepObj a -> PFSDepObj b -> PFSDepObj (PFSP a b)

---------------------
---------------------
---- Experiments ----
---------------------
---------------------

public export
data OmType : Type where
  OmObj : OmType
  OmObjPair : OmType
  OmMorph : OmType

public export
data OmObjPos : Type where
  Om0 : OmObjPos
  Om1 : OmObjPos
  OmP : OmObjPos
  OmC : OmObjPos

public export
data OmObjDir : SliceObj (OmType, OmObjPos) where
  OmObj1 : OmObjDir (OmObj, OmP)
  OmObj2 : OmObjDir (OmObj, OmP)
  OmObjL : OmObjDir (OmObj, OmC)
  OmObjR : OmObjDir (OmObj, OmC)

public export
data OmObjPairPos : Type where
  OmOPP : OmObjPairPos

public export
data OmObjPairDir : SliceObj (OmType, OmObjPairPos) where
  OmOPP1 : OmObjPairDir (OmObj, OmOPP)
  OmOPP2 : OmObjPairDir (OmObj, OmOPP)

public export
data OmMorphPosMorph : Type where
  OmId : OmMorphPosMorph
  OmComp : OmMorphPosMorph
  OmCase : OmMorphPosMorph

public export
record OmMorphPos where
  constructor MkOmMorphPos
  OMPParam : OmObjPairPos
  OMPMorph : OmMorphPosMorph

public export
OmMorphDirParam : SliceObj (OmType, OmObjPairPos)
OmMorphDirParam = OmObjPairDir

public export
data OmMorphDirMorph : SliceObj (OmType, OmMorphPosMorph) where
  OmIdObj : OmMorphDirMorph (OmObj, OmId)
  OmMorphPrec : OmMorphDirMorph (OmMorph, OmComp)
  OmMorphMid : OmMorphDirMorph (OmObj, OmComp)
  OmMorphAnt : OmMorphDirMorph (OmMorph, OmComp)
  OmMorphL : OmMorphDirMorph (OmMorph, OmCase)
  OmMorphR : OmMorphDirMorph (OmMorph, OmCase)

public export
OmMorphDir : SliceObj (OmType, OmMorphPos)
OmMorphDir (ty, i) =
  (OmMorphDirParam (ty, OMPParam i), OmMorphDirMorph (ty, OMPMorph i))

public export
OmPos : OmType -> Type
OmPos OmObj = OmObjPos
OmPos OmObjPair = OmObjPairPos
OmPos OmMorph = OmMorphPos

public export
OmDirDep : (ty : OmType) -> SliceObj (OmType, OmPos ty)
OmDirDep OmObj = OmObjDir
OmDirDep OmObjPair = OmObjPairDir
OmDirDep OmMorph = OmMorphDir

public export
OmDir : SliceObj (DPair OmType OmPos, OmType)
OmDir ((posty ** i), dirty) = OmDirDep posty (dirty, i)

public export
OmSPFId : SlicePolyEndoFuncId OmType
OmSPFId = (OmPos ** \i => (dirty : OmType ** OmDir (i, dirty)))

public export
OmSPF'' : SlicePolyEndoFunc'' OmType
OmSPF'' = (OmPos ** OmDir .* MkPair)

public export
OmSPF : SlicePolyEndoFunc OmType
OmSPF = SlicePolyEndoFuncFromId OmSPFId

public export
OmMu : SliceObj OmType
OmMu = SPFMu OmSPF

public export
OmObjMu : Type
OmObjMu = OmMu OmObj

public export
OmObjPairMu : Type
OmObjPairMu = OmMu OmObjPair

public export
OmMorphMu : Type
OmMorphMu = OmMu OmMorph

public export
OmCheckAlgCtx : SliceObj OmType
OmCheckAlgCtx OmObj = Bool
OmCheckAlgCtx OmObjPair = Bool
OmCheckAlgCtx OmMorph = Bool

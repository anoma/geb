module LanguageDef.Theories

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.RefinedADT

%default total

---------------------------------
---------------------------------
---- Computational substrate ----
---------------------------------
---------------------------------

public export
data CompCatObj : Type where
  CC0 : CompCatObj
  CCOnb : Nat -> CompCatObj

public export
Show CompCatObj where
  show (CC0) = "0"
  show (CCOnb n) = "2^" ++ show n

public export
DecEq CompCatObj where
  decEq CC0 CC0 = Yes Refl
  decEq CC0 (CCOnb _) = No $ \eq => case eq of Refl impossible
  decEq (CCOnb _) CC0 = No $ \eq => case eq of Refl impossible
  decEq (CCOnb m) (CCOnb n) = case decEq m n of
    Yes Refl => Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl

public export
Eq CompCatObj where
  a == b = isYes $ decEq a b

public export
isVoid : CompCatObj -> Bool
isVoid CC0 = True
isVoid (CCOnb _) = False

public export
IsVoid : CompCatObj -> Type
IsVoid = IsTrue . isVoid

public export
isInhabited : CompCatObj -> Bool
isInhabited = not . isVoid

public export
IsInhabited : CompCatObj -> Type
IsInhabited = IsTrue . isInhabited

-- The terminal object ("1"), which has 0 bits (so its cardinality is 2^0 == 1).
public export
CC1 : CompCatObj
CC1 = CCOnb 0

-- The boolean object, which has 1 bit (so its cardinality is 2^1 == 2).
public export
CCB : CompCatObj
CCB = CCOnb 1

public export
CCInterpObj : CompCatObj -> Type
CCInterpObj CC0 = Void
CCInterpObj (CCOnb Z) = Unit
CCInterpObj (CCOnb n@(S _)) = Vect n Bool

public export
data CompCatMorph : CompCatObj -> CompCatObj -> Type where
  -- Identity: the one (auto-)morphism that every object in every category has.
  CCid : (a : CompCatObj) -> CompCatMorph a a

  -- The universal morphism which characterizes the initial object.
  CCv : (a : CompCatObj) -> CompCatMorph CC0 a

  -- The universal morphism which characterizes the terminal object.
  -- As an optimization, we can use this term to represent not only the
  -- unique morphism into the terminal object, but also a composition
  -- through the terminal object, which produces a constant.
  CCconst : (a : CompCatObj) -> {b : CompCatObj} ->
    CompCatMorph CC1 b -> CompCatMorph a b

  -- The universal morphisms which characterize `Bool` (as a coproduct
  -- of two terminal objects).
  CCif : {a : CompCatObj} ->
    -- The parameters are "true branch" then "false branch".
    CompCatMorph CC1 a -> CompCatMorph CC1 a -> CompCatMorph CCB a
  CCt : CompCatMorph CC1 CCB
  CCf : CompCatMorph CC1 CCB

  -- Pairing and projecting allow us to rearrange, repeat, and forget
  -- "variables".  These can all be subsumed by the notion of permuting bits,
  -- and can all be implemented in terms of the universal morphisms of
  -- products by pre-composing and/or post-composing pairings and/or
  -- projections.
  CCpdom : {dom, dom', cod : Nat} ->
    Vect dom (Fin dom') ->
    CompCatMorph (CCOnb dom) (CCOnb cod) ->
    CompCatMorph (CCOnb dom') (CCOnb cod)
  CCpcod : {dom, cod, cod' : Nat} ->
    Vect cod' (Fin cod) ->
    CompCatMorph (CCOnb dom) (CCOnb cod) ->
    CompCatMorph (CCOnb dom) (CCOnb cod')

public export
ccInterpMorph : {a, b : CompCatObj} ->
  CompCatMorph a b -> CCInterpObj a -> CCInterpObj b
ccInterpMorph (CCid _) x = x
ccInterpMorph (CCv _) x = void x
ccInterpMorph (CCconst a {b} f) _ = ccInterpMorph f ()
ccInterpMorph (CCif tb fb) [True] = ccInterpMorph tb ()
ccInterpMorph (CCif tb fb) [False] = ccInterpMorph fb ()
ccInterpMorph CCt () = [True]
ccInterpMorph CCf () = [False]
ccInterpMorph (CCpdom {dom} {dom'} {cod} vec f) x =
  case cod of
    Z => ()
    S cod => ccInterpMorph f $
      case dom of
        Z => ()
        S dom => case dom' of
          Z => case vec of
            [] impossible
            j :: _ => case j of _ impossible
          S dom' => map (flip index x) vec
ccInterpMorph (CCpcod {dom} {cod} {cod'} vec f) x =
  case cod' of
    Z => ()
    S cod' => case cod of
      Z => case vec of
        [] impossible
        j :: _ => case j of _ impossible
      S cod => map (flip index $ ccInterpMorph f x) vec

public export
ccInterpTerm : {a : CompCatObj} ->
  CompCatMorph CC1 a -> CCInterpObj a
ccInterpTerm f = ccInterpMorph f ()

public export
ccConsis : (n : Nat) -> Not (CompCatMorph (CCOnb n) CC0)
ccConsis _ (CCid CC0) impossible
ccConsis _ (CCv CC0) impossible
ccConsis _ (CCconst (CCOnb _) f) = void $ ccConsis 0 f
ccConsis _ (CCif tb _) = void $ ccConsis 0 tb
ccConsis _ CCt impossible
ccConsis _ CCf impossible

public export
cc0Absurd : {0 a : Type} -> {0 n : Nat} -> CompCatMorph (CCOnb n) CC0 -> a
cc0Absurd {a} {n} f = void $ ccConsis n f

public export
Show (CompCatMorph a b) where
  show (CCid c) = "id(" ++ show c ++ ")"
  show (CCv a) = "0->(" ++ show a ++ ")"
  show (CCconst a {b} f) = "!" ++ show a ++ "(" ++ show f ++ ")"
  show (CCif f g) = "[" ++ show f ++ " | " ++ show g ++ "]"
  show CCt = "t"
  show CCf = "f"
  show (CCpdom vec f) = "pdom(" ++ show vec ++ "," ++ show f ++ ")"
  show (CCpcod vec f) = "pcod(" ++ show vec ++ "," ++ show f ++ ")"

public export
DecEq (CompCatMorph a b) where
  decEq (CCid c) (CCid c) = Yes Refl
  decEq (CCid _) (CCv _) = No $ \eq => case eq of Refl impossible
  decEq (CCid _) (CCconst _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCid CCB) (CCif _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCid _) (CCpdom _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCid _) (CCpcod _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCv CC0) (CCid CC0) = No $ \eq => case eq of Refl impossible
  decEq (CCv _) (CCv _) = Yes Refl
  decEq (CCv _) (CCconst CC0 _) = No $ \eq => case eq of Refl impossible
  decEq (CCconst _ _) (CCid _) = No $ \eq => case eq of Refl impossible
  decEq (CCconst CC0 _) (CCv _) = No $ \eq => case eq of Refl impossible
  decEq (CCconst _ f) (CCconst _ g) = case decEq f g of
    Yes Refl => Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl
  decEq (CCconst CCB _) (CCif _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCconst _ _) CCt = No $ \eq => case eq of Refl impossible
  decEq (CCconst _ _) CCf = No $ \eq => case eq of Refl impossible
  decEq (CCconst _ _) (CCpdom _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCconst _ _) (CCpcod _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCif _ _) (CCid CCB) = No $ \eq => case eq of Refl impossible
  decEq (CCif _ _) (CCconst CCB _) = No $ \eq => case eq of Refl impossible
  decEq (CCif f g) (CCif f' g') = case (decEq f f', decEq g g') of
    (Yes Refl, Yes Refl) => Yes Refl
    (No neq, _) => No $ \eq => case eq of Refl => neq Refl
    (_, No neq) => No $ \eq => case eq of Refl => neq Refl
  decEq (CCif _ _) (CCpdom _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCif _ _) (CCpcod _ _) = No $ \eq => case eq of Refl impossible
  decEq CCt (CCconst _ _) = No $ \eq => case eq of Refl impossible
  decEq CCt CCt = Yes Refl
  decEq CCt CCf = No $ \eq => case eq of Refl impossible
  decEq CCt (CCpdom _ _) = No $ \eq => case eq of Refl impossible
  decEq CCt (CCpcod _ _) = No $ \eq => case eq of Refl impossible
  decEq CCf (CCconst _ _) = No $ \eq => case eq of Refl impossible
  decEq CCf CCt = No $ \eq => case eq of Refl impossible
  decEq CCf CCf = Yes Refl
  decEq CCf (CCpdom _ _) = No $ \eq => case eq of Refl impossible
  decEq CCf (CCpcod _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCpdom _ _) (CCid _) = No $ \eq => case eq of Refl impossible
  decEq (CCpdom _ _) (CCconst _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCpdom _ _) (CCif _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCpdom _ _) CCt = No $ \eq => case eq of Refl impossible
  decEq (CCpdom _ _) CCf = No $ \eq => case eq of Refl impossible
  decEq (CCpdom {dom} vec f) (CCpdom {dom=dom''} vec' f') =
    case decEq dom dom'' of
      Yes Refl => case (decEq vec vec', decEq f f') of
        (Yes Refl, Yes Refl) => Yes Refl
        (No neq, _) => No $ \eq => case eq of Refl => neq Refl
        (_, No neq) => No $ \eq => case eq of Refl => neq Refl
      No neq => No $ \eq => case eq of Refl => neq Refl
  decEq (CCpdom _ _) (CCpcod _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCpcod _ _) (CCid _) = No $ \eq => case eq of Refl impossible
  decEq (CCpcod _ _) (CCconst _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCpcod _ _) (CCif _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCpcod _ _) CCt = No $ \eq => case eq of Refl impossible
  decEq (CCpcod _ _) CCf = No $ \eq => case eq of Refl impossible
  decEq (CCpcod _ _) (CCpdom _ _) = No $ \eq => case eq of Refl impossible
  decEq (CCpcod {cod} vec f) (CCpcod {cod=cod''} vec' f') =
    case decEq cod cod'' of
      Yes Refl => case (decEq vec vec', decEq f f') of
        (Yes Refl, Yes Refl) => Yes Refl
        (No neq, _) => No $ \eq => case eq of Refl => neq Refl
        (_, No neq) => No $ \eq => case eq of Refl => neq Refl
      No neq => No $ \eq => case eq of Refl => neq Refl

public export
Eq (CompCatMorph a b) where
  f == g = isYes $ decEq f g

-- "True" branch of the right adjunct of the boolean-defining adjunction.
public export
CCbrat : {a : CompCatObj} -> CompCatMorph CCB a -> CompCatMorph CC1 a
CCbrat (CCid CCB) = CCt
CCbrat (CCconst CCB f) = f
CCbrat (CCif tb fb) = tb
CCbrat (CCpdom vec f) = ?CCbrat_pdom_hole
CCbrat (CCpcod vec f) = ?CCbrat_pcod_hole

-- "False" branch of the right adjunct of the boolean-defining adjunction.
public export
CCbraf : {a : CompCatObj} -> CompCatMorph CCB a -> CompCatMorph CC1 a
CCbraf (CCid CCB) = CCf
CCbraf (CCconst CCB f) = f
CCbraf (CCif tb fb) = fb
CCbraf (CCpdom vec f) = ?CCbraf_pdom_hole
CCbraf (CCpcod vec f) = ?CCbraf_pcod_hole

public export
ccComp : {a, b, c : CompCatObj} ->
  CompCatMorph b c -> CompCatMorph a b -> CompCatMorph a c
ccComp (CCid c) f = f
ccComp {a=CC0} {b=CC0} {c} (CCv c) f = CCv c
ccComp {a=(CCOnb n)} {b=CC0} {c} (CCv c) f = cc0Absurd f
ccComp (CCconst b {b=c} g) f = CCconst a g
ccComp (CCif tb fb) (CCid CCB) = CCif tb fb
ccComp (CCif tb fb) (CCv CCB) = CCv c
ccComp (CCif tb fb) (CCconst a f) = case ccInterpTerm f of
  [True] => CCconst a tb
  [False] => CCconst a fb
ccComp {c} (CCif tb fb) (CCif {a=CCB} f g) =
  case (ccInterpTerm f, ccInterpTerm g) of
    ([True], [True]) => CCconst CCB tb
    ([True], [False]) => CCif tb fb
    ([False], [True]) => CCif fb tb
    ([False], [False]) => CCconst CCB fb
ccComp (CCif tb fb) CCt = tb
ccComp (CCif tb fb) CCf = fb
ccComp (CCif tb fb) (CCpdom vec f) = ?ccComp_if_pdom_hole
ccComp (CCif tb fb) (CCpcod vec f) = ?ccComp_if_pcod_hole
ccComp {a} CCt x = CCconst a CCt
ccComp {a} CCf x = CCconst a CCf
ccComp (CCpdom vec g) f = ?ccComp_pdom_hole
ccComp (CCpcod vec g) f = ?ccComp_pcod_hole

-- XXX cardinality; relationship to initial object

{-
  CCconst : (a : CompCatObj) -> {0 b : CompCatObj} ->
    CompCatMorph CC1 b -> CompCatMorph a b
  CCb2 : {a : CompCatObj} ->
    CompCatMorph CC1 a -> CompCatMorph CC1 a -> CompCatMorph CCB a
  CCbt : {0 a : CompCatObj} -> CompCatMorph CCB a -> CompCatMorph CC1 a
  CCbf : {0 a : CompCatObj} -> CompCatMorph CCB a -> CompCatMorph CC1 a
  CCp : {0 a, b, c : CompCatObj} ->
    CompCatMorph a b -> CompCatMorph a c -> CompCatMorph a (CCP b c)
  CCp1 : (a, b : CompCatObj) -> CompCatMorph (CCP a b) a
  CCp2 : (a, b : CompCatObj) -> CompCatMorph (CCP a b) b

public export
CCpa1 : {a, b, c : CompCatObj} -> CompCatMorph a (CCP b c) -> CompCatMorph a b
CCpa1 {a=(CCP b c)} {b} {c} (CCid (CCP b c)) = CCp1 b c
CCpa1 {a} {b} {c} (CCconst a f) = CCconst a {b} $ CCpa1 f
CCpa1 {a=CCB} {b} {c} (CCb2 f g) = ?CCpa1_hole_1
CCpa1 {a=CC1} {b} {c} (CCbt g) = ?CCpa1_hole_2
CCpa1 {a=CC1} {b} {c} (CCbf g) = ?CCpa1_hole_3
CCpa1 {a} {b} {c} (CCp f g) = ?CCpa1_hole_4
CCpa1 (CCp1 (CCP a' a'') b') = ?foo
CCpa1 (CCp2 a' (CCP b' b'')) = ?foo2

public export
CCpa2 : {a, b, c : CompCatObj} -> CompCatMorph a (CCP b c) -> CompCatMorph a c
CCpa2 {a} {b} {c} f = ?CCpa2_hole

public export
CCInterpMorph : {a, b : CompCatObj} ->
  CompCatMorph a b -> CCInterpObj a -> CCInterpObj b
CCInterpMorph (CCid a) x = x
CCInterpMorph (CCconst a t) _ = CCInterpMorph t ()
CCInterpMorph (CCb2 tb fb) x = case x of
  True => CCInterpMorph tb ()
  False => CCInterpMorph fb ()
CCInterpMorph (CCbt x) () = CCInterpMorph x True
CCInterpMorph (CCbf x) () = CCInterpMorph x False
CCInterpMorph (CCp f g) x = (CCInterpMorph f x, CCInterpMorph g x)
CCInterpMorph (CCp1 a b) x = fst x
CCInterpMorph (CCp2 a b) x = snd x

public export
CCInterpTerm : {a : CompCatObj} -> CompCatMorph CC1 a -> CCInterpObj a
CCInterpTerm t = CCInterpMorph t ()

public export
cm1 : (a : CompCatObj) -> CompCatMorph a CC1
cm1 a = CCconst a {b=CC1} $ CCid CC1

public export
cmu : CompCatMorph CC1 CC1
cmu = CCid CC1

public export
cct1 : CompCatMorph CC1 CCB
cct1 = CCbt {a=CCB} $ (CCid CCB)

public export
cct : (a : CompCatObj) -> CompCatMorph a CCB
cct a = CCconst a {b=CCB} cct1

public export
ccf1 : CompCatMorph CC1 CCB
ccf1 = CCbf {a=CCB} $ (CCid CCB)

public export
ccf : (a : CompCatObj) -> CompCatMorph a CCB
ccf a = CCconst a {b=CCB} ccf1

public export
CCGenTerm : {a : CompCatObj} -> CCInterpObj a -> CompCatMorph CC1 a
CCGenTerm {a=CC1} () = cmu
CCGenTerm {a=CCB} True = cct1
CCGenTerm {a=CCB} False = ccf1
CCGenTerm {a=(CCP a b)} (x, x') =
  CCp {a=CC1} {b=a} {c=b} (CCGenTerm x) (CCGenTerm x')

public export
CCMetaReduceTerm : {a : CompCatObj} -> CompCatMorph CC1 a -> CompCatMorph CC1 a
CCMetaReduceTerm t = CCGenTerm $ CCInterpTerm t

public export
ccReduce : {a, b : CompCatObj} -> CompCatMorph a b -> CompCatMorph a b
ccReduce {a} {b} f = ?ccReduce_hole

public export
ccComp : {a, b, c : CompCatObj} ->
  CompCatMorph b c -> CompCatMorph a b -> CompCatMorph a c
ccComp (CCid _) f = f
ccComp {a} (CCconst b {b=b'} t) f = CCconst a {b=b'} t
ccComp {a=CCB} {b=CCB} {c} (CCb2 {a=c} tb fb) (CCid CCB) = CCb2 {a=c} tb fb
ccComp {a} {b=CCB} {c} (CCb2 {a=c} tb fb) (CCconst a {b=CCB} f) =
  CCconst a $ ccComp (CCb2 tb fb) f
ccComp {a=CCB} {b=CCB} {c} (CCb2 {a=c} tb fb) (CCb2 {a=CCB} tb' fb') =
  CCb2 {a=c}
    (?ccComp_hole_b2_1')
    (?ccComp_hole_b2_1'')
ccComp {a=CC1} {b=CCB} {c} (CCb2 {a=c} tb fb) (CCbt {a=CCB} f) = tb
ccComp {a=CC1} {b=CCB} {c} (CCb2 {a=c} tb fb) (CCbf {a=CCB} f) = fb
ccComp {a=(CCP CCB b')} {b=CCB} {c} (CCb2 {a=c} tb fb) (CCp1 CCB b') = ?ccComp_b2p1_hole
ccComp (CCb2 {a=a'} tb fb) (CCp2 a'' CCB) = ?ccComp_b221_hole
-- ccComp {a} {b=CCB} {c} (CCb2 {a=c} tb fb) (CCpa1 {a} {b=CCB} {c=c'} f) = ?ccComp_hole_b2_4
-- ccComp {a} {b=CCB} {c} (CCb2 {a=c} tb fb) (CCpa2 {a} {b=b'} {c=CCB} f) = ?ccComp_hole_b2_5
{-
ccComp {a} {b} {c} (CCif {a=b} {b=c} cond g g') f =
  case ccComp cond f of
    CCt => ccComp g f
    CCf => ccComp g' f
    CCconst d {b=CCB} CCt => ccComp g f
    CCconst d {b=CCB} CCf => ccComp g' f
    evalcond => CCif evalcond (ccComp g f) (ccComp g' f)
    -}
ccComp {a} {b=CC1} {c} (CCbt {a=c} g) f = CCconst a {b=c} $ CCbt {a=c} g
ccComp {a} {b=CC1} {c} (CCbf {a=c} g) f = CCconst a {b=c} $ CCbf {a=c} g
ccComp (CCp g g') f = CCp (ccComp g f) (ccComp g' f)
ccComp (CCp1 a' b') f = ?ccComp_p1_hole
ccComp (CCp2 a' b') f = ?ccComp_p2_hole
{-
ccComp {a} {b} {c} (CCpa1 {a=b} {b=c} {c=c'} g) f =
  case g of
    CCp g1 g2 => ccComp g1 f
    g' => CCpa1 {a} {b=c} {c=c'} $ ccComp g' f
ccComp {a} {b} {c} (CCpa2 {a=b} {b=b'} {c} g) f =
  case g of
    CCp g1 g2 => ccComp g2 f
    g' => CCpa2 {a} {b=b'} {c} $ ccComp g' f
-}

public export
ccReduceComp : {a, b, c : CompCatObj} ->
  CompCatMorph b c -> CompCatMorph a b -> CompCatMorph a c
ccReduceComp g f = ccComp (ccReduce g) (ccReduce f)

public export
CCif : {a, b : CompCatObj} ->
  CompCatMorph a CCB -> CompCatMorph a b -> CompCatMorph a b ->
  CompCatMorph a b
CCif {a=CCB} {b} (CCid CCB) tb fb = CCb2 {a=b} (CCbt {a=b} tb) (CCbf {a=b} fb)
CCif {a} {b} (CCconst a cond) tb fb = ?CCif_hole_0'
CCif {a=CCB} {b} (CCb2 tt ft) tb fb = ?CCif_hole_1
CCif {a=CC1} {b} (CCbt x) tb fb = ?CCif_hole_2
CCif {a=CC1} {b} (CCbf x) tb fb = ?CCif_hole_3
CCif {a=(CCP CCB b')} {b} (CCp1 CCB b') tb fb = ?CCif_hole_4
CCif {a=(CCP a' CCB)} {b} (CCp2 a' CCB) tb fb = ?CCif_hole_5

public export
ccHomObj : CompCatObj -> CompCatObj -> CompCatObj
ccHomObj CC1 b = b
ccHomObj CCB b = CCP b b
ccHomObj (CCP a b) c = ccHomObj a (ccHomObj b c)

public export
CCHomInterpInv : (a, b : CompCatObj) ->
  (CCInterpObj a -> CCInterpObj b) -> CCInterpObj (ccHomObj a b)
CCHomInterpInv CC1 b f = f ()
CCHomInterpInv CCB b f = (f True, f False)
CCHomInterpInv (CCP a a') b f = CCHomInterpInv a (ccHomObj a' b) $
  CCHomInterpInv a' b . curry f

public export
ccCurry : {a, b, c : CompCatObj} ->
  CompCatMorph (CCP a b) c -> CompCatMorph a (ccHomObj b c)
ccCurry {a} {b=CC1} {c} f = ccComp f $ CCp (CCid a) $ cm1 a
ccCurry {a} {b=CCB} {c} f =
  CCp (ccComp f $ CCp (CCid a) $ cct a) (ccComp f $ CCp (CCid a) $ ccf a)
ccCurry {a} {b=(CCP b b')} {c} f =
  ccCurry {a} {b} {c=(ccHomObj b' c)} $ ccCurry {a=(CCP a b)} {b=b'} {c} $
    ccComp f $
      CCp
        (ccComp (CCp1 a b) (CCp1 (CCP a b) b'))
        (CCp
          (ccComp (CCp2 a b) (CCp1 (CCP a b) b'))
          (CCp2 (CCP a b) b'))

public export
ccEval1 : (a : CompCatObj) -> CompCatMorph (CCP (ccHomObj CC1 a) CC1) a
ccEval1 a = CCp1 a CC1

public export
ccEval : (a, b : CompCatObj) -> CompCatMorph (CCP (ccHomObj a b) a) b
ccEval CC1 b = ccEval1 b
ccEval CCB b =
  CCif
    -- Second parameter to `eval` is condition
    (CCp2 (CCP b b) CCB)
    -- First half of first parameter to `eval` is true branch
    (ccComp (CCp1 b b) (CCp1 (CCP b b) CCB))
    -- Second half of first parameter to `eval` is false branch
    (ccComp (CCp2 b b) (CCp1 (CCP b b) CCB))
ccEval (CCP a a') b =
  ccComp
    (ccEval a' b) $
    CCp
      (ccComp
        (ccEval a $ ccHomObj a' b)
        (CCp
          (CCp1 (ccHomObj a (ccHomObj a' b)) (CCP a a'))
          (ccComp
            (CCp1 a a')
            (CCp2 (ccHomObj a (ccHomObj a' b)) (CCP a a')))))
      (ccComp (CCp2 a a') (CCp2 (ccHomObj a (ccHomObj a' b)) (CCP a a')))

public export
ccUncurry : {a, b, c : CompCatObj} ->
  CompCatMorph a (ccHomObj b c) -> CompCatMorph (CCP a b) c
ccUncurry {a} {b} {c} f =
  ccComp (ccEval b c) $ CCp (ccComp f (CCp1 a b)) (CCp2 a b)

public export
CCGenMorph : {a, b : CompCatObj} ->
  (CCInterpObj a -> CCInterpObj b) -> CompCatMorph a b
CCGenMorph {a=CC1} {b} f = CCGenTerm {a=b} $ f ()
CCGenMorph {a=CCB} {b} f =
  CCb2 {a=b} (CCGenTerm {a=b} $ f True) (CCGenTerm {a=b} $ f False)
CCGenMorph {a=(CCP a a')} {b} f =
  ccUncurry $ CCGenMorph {a} {b=(ccHomObj a' b)} $
  CCHomInterpInv a' b . curry f
  -}

---------------------------------
---------------------------------
---- Minimal topos interface ----
---------------------------------
---------------------------------

{-
mutual
  public export
  data MinToposCat : Type where
    MTCb : MinToposCat
    MTCs : (cat : MinToposCat) -> MinToposObj cat -> MinToposCat

  public export
  data MinToposObj : MinToposCat -> Type where
    MT1 : (cat : MinToposCat) -> MinToposObj cat
    MTB : (cat : MinToposCat) -> MinToposObj cat
    MTP : {0 cat : MinToposCat} -> {0 x, y, z : MinToposObj cat} ->
      MinToposMorph {cat} x z -> MinToposMorph {cat} y z -> MinToposObj cat
    MTS : {0 cat : MinToposCat} -> {0 x : MinToposObj cat} ->
      MinToposMorph {cat} x z -> MinToposMorph {cat} y z -> MinToposObj cat
    MTT : {0 cat : MinToposCat} -> MinToposObj cat -> MinToposObj cat

  public export
  data MinToposMorph : {0 cat : MinToposCat} ->
      MinToposObj cat -> MinToposObj cat -> Type where
  public export
  data MinToposObj : Type where
    MTP : MinToposObj -> MinToposObj -> MinToposObj
    MTE : {0 a, b : MinToposObj} ->
      MinToposMorph a b -> MinToposMorph a b -> MinToposObj
    MTT : MinToposObj -> MinToposObj

  public export
  data MinToposMorph : MinToposObj -> MinToposObj -> Type where
    MTid : (a : MinToposObj) -> MinToposMorph a a
    MTcomp : {0 a, b, c : MinToposObj} ->
      MinToposMorph b c -> MinToposMorph a b -> MinToposMorph a c
    MTterm : (a : MinToposObj) -> MinToposMorph a MT1
    Mtif : {0 a : MinToposObj} ->
      MinToposMorph MT1 a -> MinToposMorph MT1 a -> MinToposMorph MTB a
    Mtbt : {0 a : MinToposObj} -> MinToposMorph MTB a -> MinToposMorph MT1 a
    Mtbf : {0 a : MinToposObj} -> MinToposMorph MTB a -> MinToposMorph MT1 a

  public export
  data MinToposEq : {0 a, b : MinToposObj} ->
      MinToposMorph a b -> MinToposMorph a b -> Type where

mutual
  public export
  interpMinToposObj : MinToposObj -> Type
  interpMinToposObj x = ?interpMinToposObj_hole

  public export
  interpMinToposMorph : {0 a, b : MinToposObj} ->
    MinToposMorph a b -> interpMinToposObj a -> interpMinToposObj b
  interpMinToposMorph f = ?interpMinToposMorph_hole

  public export
  interpMinToposEq : {0 a, b : MinToposObj} -> {0 f, g : MinToposMorph a b} ->
    MinToposEq {a} {b} f g ->
    ExtEq (interpMinToposMorph {a} {b} f) (interpMinToposMorph {a} {b} g)
  interpMinToposEq {a} {b} {f} {g} eq = ?interpMinToposEq_hole
    -}

-----------------------------------------
-----------------------------------------
---- FinSet as minimal digital topos ----
-----------------------------------------
-----------------------------------------

-- Unrefined version:  finite products of Booleans (the free Lawvere
-- theory with generic object `Bool`).
public export
data LawBoolObj : Type where
  -- The number of bits in the object.
  LBOn : Nat -> LawBoolObj

public export
DecEq LawBoolObj where
  decEq (LBOn m) (LBOn n) = case decEq m n of
    Yes Refl => Yes Refl
    No neq => case neq of Refl impossible

public export
Eq LawBoolObj where
  x == y = isYes $ decEq x y

public export
Show LawBoolObj where
  show (LBOn n) = "2^" ++ show n

public export
LawBoolSig : Type
LawBoolSig = ProductMonad LawBoolObj

public export
LBOTerminal : LawBoolObj
LBOTerminal = LBOn 0

public export
LBOBool : LawBoolObj
LBOBool = LBOn 1

public export
LawBoolMorphDom : Type
LawBoolMorphDom = LawBoolSig

public export
LawBoolMorphCod : Type
LawBoolMorphCod = LawBoolSig

public export
data LawBoolMorphPos : Type where
  LBMPosId : LawBoolObj -> LawBoolMorphPos
  LBMPosConst : LawBoolObj -> LawBoolObj -> LawBoolMorphPos
  LBMPosBranch : LawBoolObj -> LawBoolObj -> LawBoolMorphPos
  LBMPosProd : LawBoolObj -> LawBoolObj -> LawBoolObj -> LawBoolMorphPos
  LBMPosProj1 : LawBoolObj -> LawBoolObj -> LawBoolMorphPos
  LBMPosProj2 : LawBoolObj -> LawBoolObj -> LawBoolMorphPos

public export
data LawBoolMorphDir : Type where
  LBMDirId : LawBoolObj -> LawBoolMorphDir

public export
lbmSigma : LawBoolMorphPos -> LawBoolMorphCod
lbmSigma (LBMPosId x) = (x, x)
lbmSigma (LBMPosConst x y) = (x, y)
lbmSigma (LBMPosBranch (LBOn n) y) = (LBOn (S n), y)
lbmSigma (LBMPosProd x (LBOn m) (LBOn n)) = (x, LBOn (m + n))
lbmSigma (LBMPosProj1 (LBOn m) (LBOn n)) = (LBOn (m + n), LBOn m)
lbmSigma (LBMPosProj2 (LBOn m) (LBOn n)) = (LBOn (m + n), LBOn n)

public export
lbmPi : LawBoolMorphDir -> LawBoolMorphPos
lbmPi (LBMDirId x) = LBMPosId x

public export
lbmBaseChange : LawBoolMorphDir -> LawBoolMorphDom
lbmBaseChange (LBMDirId x) = (x, x)

public export
LawBoolMorphF : CSliceObj LawBoolSig -> CSliceObj LawBoolSig
LawBoolMorphF = CSPolyF lbmBaseChange lbmPi lbmSigma

---------------------------------------
---------------------------------------
---- Bool as (one-object) category ----
---------------------------------------
---------------------------------------

-------------------------------
---- Objects and morphisms ----
-------------------------------

public export
data BoolObj : Type where
  BOBool : BoolObj

public export
DecEq BoolObj where
  decEq BOBool BOBool = Yes Refl

public export
Eq BoolObj where
  b == b' = isYes (decEq b b')

public export
Show BoolObj where
  show BOBool = "Bool"

public export
data BoolMorph : Type where
  BMid : BoolMorph
  BMnot : BoolMorph
  BMtrue : BoolMorph
  BMfalse : BoolMorph

public export
DecEq BoolMorph where
  decEq BMid BMid = Yes Refl
  decEq BMid BMnot = No $ \eq => case eq of Refl impossible
  decEq BMid BMtrue = No $ \eq => case eq of Refl impossible
  decEq BMid BMfalse = No $ \eq => case eq of Refl impossible
  decEq BMnot BMid = No $ \eq => case eq of Refl impossible
  decEq BMnot BMnot = Yes Refl
  decEq BMnot BMtrue = No $ \eq => case eq of Refl impossible
  decEq BMnot BMfalse = No $ \eq => case eq of Refl impossible
  decEq BMtrue BMid = No $ \eq => case eq of Refl impossible
  decEq BMtrue BMnot = No $ \eq => case eq of Refl impossible
  decEq BMtrue BMtrue = Yes Refl
  decEq BMtrue BMfalse = No $ \eq => case eq of Refl impossible
  decEq BMfalse BMid = No $ \eq => case eq of Refl impossible
  decEq BMfalse BMnot = No $ \eq => case eq of Refl impossible
  decEq BMfalse BMtrue = No $ \eq => case eq of Refl impossible
  decEq BMfalse BMfalse = Yes Refl

public export
Eq BoolMorph where
  bm == bm' = isYes (decEq bm bm')

public export
Show BoolMorph where
  show BMid = "id"
  show BMnot = "not"
  show BMtrue = "t"
  show BMfalse = "f"

public export
bmDom : BoolMorph -> BoolObj
bmDom _ = BOBool

public export
bmCod : BoolMorph -> BoolObj
bmCod _ = BOBool

public export
bmId : (a : BoolObj) -> BoolMorph
bmId BOBool = BMid

public export
0 bmIdDom : (0 a : BoolObj) -> bmDom (bmId a) = a
bmIdDom BOBool = Refl

public export
0 bmIdCod : (0 a : BoolObj) -> bmCod (bmId a) = a
bmIdCod BOBool = Refl

public export
bmComp : (g, f : BoolMorph) -> bmCod f = bmDom g -> BoolMorph
bmComp BMid f Refl = f
bmComp BMnot BMid Refl = BMnot
bmComp BMnot BMnot Refl = BMid
bmComp BMnot BMtrue Refl = BMfalse
bmComp BMnot BMfalse Refl = BMtrue
bmComp BMtrue _ Refl = BMtrue
bmComp BMfalse _ Refl = BMfalse

public export
0 bmCompDom :
  (0 g, f : BoolMorph) -> {0 eq : bmCod f = bmDom g} ->
  bmDom (bmComp g f eq) = bmDom f
bmCompDom g f {eq} = Refl

public export
0 bmCompCod :
  (0 g, f : BoolMorph) -> {0 eq : bmCod f = bmDom g} ->
  bmCod (bmComp g f eq) = bmCod g
bmCompCod g f {eq} = Refl

------------------------------------
---- Interpretation into `Type` ----
------------------------------------

public export
interpBoolObj : BoolObj -> Type
interpBoolObj BOBool = Bool

public export
RefinedBoolMorph : BoolObj -> BoolObj -> Type
RefinedBoolMorph b b' =
  Refinement {a=BoolMorph} $ (\m => bmDom m == b && bmCod m == b')

public export
interpBoolMorph : {0 b, b' : BoolObj} -> RefinedBoolMorph b b' ->
  interpBoolObj b -> interpBoolObj b'
interpBoolMorph {b=BOBool} {b'=BOBool} (Element0 BMid eq) = id
interpBoolMorph {b=BOBool} {b'=BOBool} (Element0 BMnot eq) = not
interpBoolMorph {b=BOBool} {b'=BOBool} (Element0 BMtrue eq) = const True
interpBoolMorph {b=BOBool} {b'=BOBool} (Element0 BMfalse eq) = const False

------------------------------------------------------------------------
------------------------------------------------------------------------
---- Boolean circuits (such as modeled by BITC) as a Lawvere theory ----
------------------------------------------------------------------------
------------------------------------------------------------------------

--------------------
---- Definition ----
--------------------

-- Every object of this category is some natural number of bits.
public export
data BCLawObj : Type where
  BCLOnbits : Nat -> BCLawObj

public export
DecEq BCLawObj where
  decEq (BCLOnbits m) (BCLOnbits n) = case decEq m n of
    Yes Refl => Yes Refl
    No neq => case neq of Refl impossible

public export
Eq BCLawObj where
  x == y = isYes $ decEq x y

public export
Show BCLawObj where
  show (BCLOnbits n) = "2^" ++ show n

public export
BCLawSig : Type
BCLawSig = (BCLawObj, BCLawObj)

-- The total space of morphisms in the boolean-Lawvere category.
-- Slices of this provide the morphisms indexed by signature
-- (domain and codomain).  These should compile very directly to BITC.
public export
data BCLawMorph : Type where
  -- The identity which is present in all categories.  Composition
  -- is not explicit here, but derived.
  BCLMid : BCLawObj -> BCLawMorph

  -- Every object of of the BCLaw category is a finite product (of Bool).
  --
  -- This is the left adjunct, which provides the product introduction rule.
  BCLMprodAdjL : List BCLawMorph -> BCLawMorph
  --
  -- This is the right adjunct, which provides the product elimination rule
  -- (in particular when applied to `id`, in which case it becomes the counit).
  -- The `Nat` parameter is an index into the returned list.
  BCLMprodAdjR : BCLawMorph -> Nat -> BCLawMorph

  -- Every BCLawObj with a non-zero number of bits may also be viewed as a
  -- product of the first bit (which itself is a coproduct of two terminal
  -- objects, which in turn are products of zero bits) with a BCLawObj with
  -- one fewer bit.  This is the right adjunct which distributes the product
  -- of the first bit with the rest of the bits over the coproduct which
  -- comprises the first bit, traverses the isomorphism between `1 * a` and `a`,
  -- and then applies the coproduct elimination rule (to produce from two
  -- morphisms of the same signature a morphism whose domain is one bit longer).
  BCLMbranchAdjR : BCLawMorph -> BCLawMorph -> BCLawMorph

  -- The left adjunct which inverts `BCLMbranchAdjR` -- a morphism from
  -- `1 + a` bits to `b` bits can be decomposed into two morphisms from
  -- `a` bits to `b` bits.
  BCLMbranchAdjL1 : BCLawMorph -> BCLawMorph
  BCLMbranchAdjL2 : BCLawMorph -> BCLawMorph

public export
DecEq BCLawMorph where
  decEq = decEqOne where
    mutual
      public export
      decEqOne : DecEqPred BCLawMorph
      decEqOne (BCLMid m) (BCLMid n) = case decEq m n of
        Yes Refl => Yes Refl
        No neq => case neq of Refl impossible
      decEqOne (BCLMid _) (BCLMprodAdjL _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMid _) (BCLMprodAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMid _) (BCLMbranchAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMid _) (BCLMbranchAdjL1 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMid _) (BCLMbranchAdjL2 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjL _) (BCLMid _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjL fs) (BCLMprodAdjL gs) = case decEqList fs gs of
        Yes Refl => Yes Refl
        No neq => case neq of Refl impossible
      decEqOne (BCLMprodAdjL _) (BCLMprodAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjL _) (BCLMbranchAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjL _) (BCLMbranchAdjL1 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjL _) (BCLMbranchAdjL2 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjR _ _) (BCLMid _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjR _ _) (BCLMprodAdjL _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjR f m) (BCLMprodAdjR g n) =
        case decEqOne f g of
          Yes Refl => case decEq m n of
            Yes Refl => Yes Refl
            No neq => case neq of Refl impossible
          No neq => case neq of Refl impossible
      decEqOne (BCLMprodAdjR _ _) (BCLMbranchAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjR _ _) (BCLMbranchAdjL1 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMprodAdjR _ _) (BCLMbranchAdjL2 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjR _ _) (BCLMid _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjR _ _) (BCLMprodAdjL _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjR _ _) (BCLMprodAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjR f g) (BCLMbranchAdjR f' g') =
        case (decEqOne f f', decEqOne g g') of
          (Yes Refl, Yes Refl) => Yes Refl
          (No neq, _) => No $ \eq => case eq of Refl => neq Refl
          (_, No neq) => No $ \eq => case eq of Refl => neq Refl
      decEqOne (BCLMbranchAdjR _ _) (BCLMbranchAdjL1 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjR _ _) (BCLMbranchAdjL2 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL1 _) (BCLMid _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL1 _) (BCLMprodAdjL _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL1 _) (BCLMprodAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL1 _) (BCLMbranchAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL1 f) (BCLMbranchAdjL1 g) =
        case decEqOne f g of
          Yes Refl => Yes Refl
          No neq => case neq of Refl impossible
      decEqOne (BCLMbranchAdjL1 _) (BCLMbranchAdjL2 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL2 _) (BCLMid _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL2 _) (BCLMprodAdjL _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL2 _) (BCLMprodAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL2 _) (BCLMbranchAdjR _ _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL2 _) (BCLMbranchAdjL1 _) =
        No $ \eq => case eq of Refl impossible
      decEqOne (BCLMbranchAdjL2 f) (BCLMbranchAdjL2 g) =
        case decEqOne f g of
          Yes Refl => Yes Refl
          No neq => case neq of Refl impossible

      public export
      decEqList : DecEqPred (List BCLawMorph)
      decEqList [] [] = Yes Refl
      decEqList [] (_ :: _) = No $ \eq => case eq of Refl impossible
      decEqList (_ :: _) [] = No $ \eq => case eq of Refl impossible
      decEqList (f :: fs) (g :: gs) = case (decEqOne f g, decEqList fs gs) of
        (Yes Refl, Yes Refl) => Yes Refl
        (No neq, _) => No $ \eq => case eq of Refl => neq Refl
        (_, No neq) => No $ \eq => case eq of Refl => neq Refl

public export
Eq BCLawMorph where
  f == g = isYes $ decEq f g

public export
Show BCLawMorph where
  show = showOne where
    mutual
      public export
      showOne : BCLawMorph -> String
      showOne (BCLMid n) = "id[" ++ show n ++ "]"
      showOne (BCLMprodAdjL fs) = "prodAdjL[" ++ showList fs ++ "]"
      showOne (BCLMprodAdjR f n) =
        "prodAdjR[" ++ showOne f ++ ":" ++ show n ++ "]"
      showOne (BCLMbranchAdjR f g) =
        "branchAdjR[" ++ showOne f ++ "/" ++ showOne g ++ "]"
      showOne (BCLMbranchAdjL1 f) = "branchAdjL1[" ++ showOne f ++ "]"
      showOne (BCLMbranchAdjL2 f) = "branchAdjL2[" ++ showOne f ++ "]"

      public export
      showList : List BCLawMorph -> String
      showList fs = "[" ++ showListRec fs ++ "]"

      public export
      showListRec : List BCLawMorph -> String
      showListRec [] = ""
      showListRec (f :: []) = showOne f
      showListRec (f :: fs@(g :: gs)) = showOne f ++ ", " ++ showListRec fs

mutual
  public export
  checkBCLMOne : BCLawObj -> BCLawObj -> BCLawMorph -> Bool
  checkBCLMOne m n (BCLMid k) =
    m == k && n == k
  checkBCLMOne m (BCLOnbits n) (BCLMprodAdjL fs) =
    length fs == n && checkBCLMList m (BCLOnbits 1) fs
  checkBCLMOne (BCLOnbits m) (BCLOnbits n) (BCLMprodAdjR f k) =
    k < m && n == 1
  checkBCLMOne (BCLOnbits m) (BCLOnbits n) (BCLMbranchAdjR f g) =
    case m of
      S m' =>
        checkBCLMOne (BCLOnbits m') (BCLOnbits n) f &&
        checkBCLMOne (BCLOnbits m') (BCLOnbits n) g
      Z => False
  checkBCLMOne (BCLOnbits m) (BCLOnbits n) (BCLMbranchAdjL1 f) =
    checkBCLMOne (BCLOnbits (S m)) (BCLOnbits n) f
  checkBCLMOne (BCLOnbits m) (BCLOnbits n) (BCLMbranchAdjL2 f) =
    checkBCLMOne (BCLOnbits (S m)) (BCLOnbits n) f

  public export
  checkBCLMList : BCLawObj -> BCLawObj -> List BCLawMorph -> Bool
  checkBCLMList m n [] = True
  checkBCLMList m n (f :: fs) = checkBCLMOne m n f && checkBCLMList m n fs

public export
checkBCLM : BCLawSig -> BCLawMorph -> Bool
checkBCLM = uncurry checkBCLMOne

public export
checkBCLMs : BCLawSig -> List BCLawMorph -> Bool
checkBCLMs = uncurry checkBCLMList

public export
checkSignedBCLM : (BCLawSig, BCLawMorph) -> Bool
checkSignedBCLM = uncurry checkBCLM

public export
checkSignedBCLMs : (BCLawSig, List BCLawMorph) -> Bool
checkSignedBCLMs = uncurry checkBCLMs

public export
SignedBCLM : Type
SignedBCLM = PullbackDec {a=BCLawSig} {b=BCLawMorph} checkSignedBCLM

public export
SignedBCLMList : Type
SignedBCLMList = PullbackDec {a=BCLawSig} {b=(List BCLawMorph)} checkSignedBCLMs

---------------------
---- Composition ----
---------------------

------------------------------
---- Universal properties ----
------------------------------

--------------------------------------
--------------------------------------
---- Single-sorted Lawvere theory ----
--------------------------------------
--------------------------------------

-----------------------------------------------------------------
-----------------------------------------------------------------
---- Single-sorted Lawvere theory with generic object `Bool` ----
-----------------------------------------------------------------
-----------------------------------------------------------------

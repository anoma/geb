module LanguageDef.Test.FinCatPRATest

import Test.TestLibrary
import LanguageDef.FinCatPRA

%default total

-----------------------------------------------------------------
-----------------------------------------------------------------
---- Example: Even/Odd predicates with multiple dependencies ----
-----------------------------------------------------------------
-----------------------------------------------------------------

-----------------------------------------
---- Standard Idris datatype version ----
-----------------------------------------

mutual
  data FTestNat : Type where
    FTNz : FTestNat
    FTNs : FTestNat -> FTestNat

  data FTestNatWithParity : Type where
    FTNPeven : (n : FTestNat) -> FTestNatEven n -> FTestNatWithParity
    FTNPodd : (n : FTestNat) -> FTestNatOdd n -> FTestNatWithParity

  data FTestNatEven : FTestNat -> Type where
    FTNEvenZero : FTestNatEven FTNz
    FTNEvenSuccOdd : (n : FTestNat) -> FTestNatOdd n -> FTestNatEven (FTNs n)

  data FTestNatOdd : FTestNat -> Type where
    FTNOddSuccEven : (n : FTestNat) -> FTestNatEven n -> FTestNatOdd (FTNs n)

-------------------------------------------
---- Functor representation of the type ----
-------------------------------------------

-- Functor for FTestNat (only self-recursive, no dependencies)
FTestNatF : Type -> Type
FTestNatF recNat = Either () recNat  -- Zero or Successor

-- Functor for FTestNatWithParity
-- Depends on recNat and the two families recEven and recOdd
FTestNatWithParityF : (recNat : Type) ->
                      (recEven : recNat -> Type) ->
                      (recOdd : recNat -> Type) ->
                      Type
FTestNatWithParityF recNat recEven recOdd =
  Either (DPair recNat recEven)      -- Even case: nat with even proof
         (DPair recNat recOdd)        -- Odd case: nat with odd proof

-- Functor for FTestNatEven
-- Takes the index n and returns the type of evidence that n is even
FTestNatEvenF : (recNat : Type) ->
                (recOdd : recNat -> Type) ->
                FTestNatF recNat -> Type
FTestNatEvenF recNat recOdd (Left ()) =
  ()                                           -- Zero is even (trivial proof)
FTestNatEvenF recNat recOdd (Right n) =
  recOdd n                                     -- Succ n is even if n is odd

-- Functor for FTestNatOdd
-- Takes the index n and returns the type of evidence that n is odd
FTestNatOddF : (recNat : Type) ->
               (recEven : recNat -> Type) ->
               FTestNatF recNat -> Type
FTestNatOddF recNat recEven (Left ()) =
  Void                                         -- Zero is not odd (no proof)
FTestNatOddF recNat recEven (Right n) =
  recEven n                                    -- Succ n is odd if n is even

------------------------------------------------
---- Verification: Fixed point isomorphisms ----
------------------------------------------------

-- FTestNat is a fixed point of FTestNatF
natToF : FTestNat -> FTestNatF FTestNat
natToF FTNz = Left ()
natToF (FTNs n) = Right n

natFromF : FTestNatF FTestNat -> FTestNat
natFromF (Left ()) = FTNz
natFromF (Right n) = FTNs n

-- FTestNatWithParity is a fixed point of FTestNatWithParityF
parityToF : FTestNatWithParity ->
            FTestNatWithParityF FTestNat FTestNatEven FTestNatOdd
parityToF (FTNPeven n prf) = Left (n ** prf)
parityToF (FTNPodd n prf) = Right (n ** prf)

parityFromF : FTestNatWithParityF FTestNat FTestNatEven FTestNatOdd ->
              FTestNatWithParity
parityFromF (Left (n ** prf)) = FTNPeven n prf
parityFromF (Right (n ** prf)) = FTNPodd n prf

-- FTestNatEven is a fixed point of FTestNatEvenF
evenToF : {n : FTestNat} -> FTestNatEven n ->
          FTestNatEvenF FTestNat FTestNatOdd (natToF n)
evenToF {n=FTNz} FTNEvenZero = ()
evenToF {n=(FTNs m)} (FTNEvenSuccOdd m prf) = prf

evenFromF : {n : FTestNat} ->
            FTestNatEvenF FTestNat FTestNatOdd (natToF n) -> FTestNatEven n
evenFromF {n=FTNz} () = FTNEvenZero
evenFromF {n=(FTNs m)} prf = FTNEvenSuccOdd m prf

-- FTestNatOdd is a fixed point of FTestNatOddF
oddToF : {n : FTestNat} -> FTestNatOdd n ->
         FTestNatOddF FTestNat FTestNatEven (natToF n)
oddToF {n=FTNz} prf impossible  -- No proof that zero is odd
oddToF {n=(FTNs m)} (FTNOddSuccEven m prf) = prf

oddFromF : {n : FTestNat} ->
           FTestNatOddF FTestNat FTestNatEven (natToF n) -> FTestNatOdd n
oddFromF {n=FTNz} prf = void prf  -- Void has no inhabitants
oddFromF {n=(FTNs m)} prf = FTNOddSuccEven m prf

------------------------------------------------
---- Encoding as copresheaf over 2-level forest
------------------------------------------------

-- Forest structure: 2 base types
-- Base 0: FTestNat type (has 2 dependent types)
-- Base 1: FTestNatWithParity type (has 0 dependent types)
-- Dep 0 on Base 0: FTestNatEven (proof that a nat is even)
-- Dep 1 on Base 0: FTestNatOdd (proof that a nat is odd)
EvenOddForest : Fin2Forest
EvenOddForest = [2, 0]  -- Base 0 has 2 deps, Base 1 has 0 deps

-- Object mapping for the copresheaf
EvenOddCoprObjMap : F2FCoprObjMap EvenOddForest
EvenOddCoprObjMap (BaseObj FZ) = FTestNat                    -- Base 0
EvenOddCoprObjMap (BaseObj (FS FZ)) = FTestNatWithParity    -- Base 1
EvenOddCoprObjMap (DepObj FZ FZ) = DPair FTestNat FTestNatEven  -- Dep 0/Base 0
EvenOddCoprObjMap (DepObj FZ (FS FZ)) = DPair FTestNat FTestNatOdd -- Dep 1 on 0
-- Base 1 has no dependent types, so these cases are impossible
EvenOddCoprObjMap (DepObj (FS FZ) dep) = void (absurd dep)  -- Fin 0 impossible
EvenOddCoprObjMap (DepObj (FS (FS i)) dep) = void (absurd i)  -- No more bases

-- Morphism mapping for the copresheaf
EvenOddCoprMorMap : F2FCoprMorMap {forest=EvenOddForest} EvenOddCoprObjMap
-- Identity morphisms preserve elements
EvenOddCoprMorMap {a} {b=a} IdMor x = x
-- DepToBase morphisms extract the underlying nat from dependent pairs
EvenOddCoprMorMap (DepToBase {base=FZ} {dep=FZ}) x = fst x
EvenOddCoprMorMap (DepToBase {base=FZ} {dep=(FS FZ)}) x = fst x
EvenOddCoprMorMap (DepToBase {base=(FS FZ)} {dep}) x = absurd dep

-- The complete copresheaf
EvenOddCopr : F2FCopr EvenOddForest
EvenOddCopr = (EvenOddCoprObjMap ** EvenOddCoprMorMap)

-- Verify functor law: identity preservation
-- F(id) = id for all objects
evenOddPresId : {a : F2FObj EvenOddForest} ->
  (x : EvenOddCoprObjMap a) ->
  EvenOddCoprMorMap {a} {b=a} IdMor x = x
evenOddPresId {a} x = Refl  -- By definition of EvenOddCoprMorMap

-- Verify functor law: composition preservation
-- F(g ∘ f) = F(g) ∘ F(f) for all composable morphisms
evenOddPresComp : {a, b, c : F2FObj EvenOddForest} ->
  (g : F2FMor {forest=EvenOddForest} b c) ->
  (f : F2FMor {forest=EvenOddForest} a b) ->
  (x : EvenOddCoprObjMap a) ->
  EvenOddCoprMorMap (f2fComposeMor g f) x =
  EvenOddCoprMorMap g (EvenOddCoprMorMap f x)
evenOddPresComp {a} {b=a} {c=a} IdMor IdMor x = Refl
evenOddPresComp IdMor DepToBase x = Refl
evenOddPresComp DepToBase IdMor x = Refl
evenOddPresComp DepToBase DepToBase x impossible

-----------------------------------------------
---- Building a PRA functor for this example --
-----------------------------------------------

-- We're building an endofunctor on EvenOddForest

-- T1: A finite copresheaf on EvenOddForest that encodes the constructors
-- For each type, T1 tells us how many constructors it has
T1FinObjMap : F2FFinCoprObjMap EvenOddForest
-- FTestNat has two constructors: Zero and Succ
T1FinObjMap (BaseObj FZ) = 2
-- FTestNatWithParity has two constructors: Even case and Odd case
T1FinObjMap (BaseObj (FS FZ)) = 2
-- FTestNatEven has two constructors: Zero (always even) and SuccOdd
T1FinObjMap (DepObj FZ FZ) = 2
-- FTestNatOdd has one constructor: SuccEven
T1FinObjMap (DepObj FZ (FS FZ)) = 1
-- Impossible cases
T1FinObjMap (DepObj (FS FZ) dep) = void (absurd dep)
T1FinObjMap (DepObj (FS (FS i)) dep) = void (absurd i)

T1FinMorMap : F2FFinCoprMorMap {forest=EvenOddForest} T1FinObjMap
T1FinMorMap IdMor x = x
T1FinMorMap (DepToBase {base=FZ} {dep=FZ}) x = case x of
  FZ => FZ -- EvenZero -> Zero
  FS FZ => FS FZ -- EvenSuccOdd -> Succ
T1FinMorMap (DepToBase {base=FZ} {dep=(FS FZ)}) x = case x of
  FZ => FS FZ -- OddSuccEven -> Succ
T1FinMorMap (DepToBase {base=(FS FZ)} {dep}) x = absurd dep

T1FinCopr : F2FFinCopr EvenOddForest
T1FinCopr = (T1FinObjMap ** T1FinMorMap)

-- Now we need E_T: for each element of T1, specify what arguments it takes
-- This is a functor from el(T1)^op to finite copresheaves on EvenOddForest

-- Helper functions for each constructor's argument copresheaf

-- FTestNat Zero takes no arguments
FTestNatZeroArgsFinObjMap : F2FFinCoprObjMap EvenOddForest
FTestNatZeroArgsFinObjMap _ = 0

FTestNatZeroArgsFinMorMap :
  F2FFinCoprMorMap {forest=EvenOddForest} FTestNatZeroArgsFinObjMap
FTestNatZeroArgsFinMorMap _ x = absurd x

FTestNatZeroArgsFinCopr : F2FFinCopr EvenOddForest
FTestNatZeroArgsFinCopr =
  (FTestNatZeroArgsFinObjMap ** FTestNatZeroArgsFinMorMap)

-- FTestNat Succ takes one FTestNat
FTestNatSuccArgsFinObjMap : F2FFinCoprObjMap EvenOddForest
FTestNatSuccArgsFinObjMap (BaseObj FZ) = 1  -- One nat argument
FTestNatSuccArgsFinObjMap (BaseObj (FS FZ)) = 0
FTestNatSuccArgsFinObjMap (DepObj FZ FZ) = 0
FTestNatSuccArgsFinObjMap (DepObj FZ (FS FZ)) = 0
FTestNatSuccArgsFinObjMap (DepObj (FS FZ) dep) = void (absurd dep)
FTestNatSuccArgsFinObjMap (DepObj (FS (FS i)) dep) = void (absurd i)

FTestNatSuccArgsFinMorMap :
  F2FFinCoprMorMap {forest=EvenOddForest} FTestNatSuccArgsFinObjMap
FTestNatSuccArgsFinMorMap IdMor x = x
FTestNatSuccArgsFinMorMap (DepToBase {base=FZ} {dep=FZ}) x = absurd x
FTestNatSuccArgsFinMorMap (DepToBase {base=FZ} {dep=(FS FZ)}) x = absurd x
FTestNatSuccArgsFinMorMap (DepToBase {base=(FS FZ)} {dep}) x = absurd dep

FTestNatSuccArgsFinCopr : F2FFinCopr EvenOddForest
FTestNatSuccArgsFinCopr =
  (FTestNatSuccArgsFinObjMap ** FTestNatSuccArgsFinMorMap)

-- FTestNatWithParity Even takes a nat and an even proof
FTestNatWithParityEvenArgsFinObjMap : F2FFinCoprObjMap EvenOddForest
FTestNatWithParityEvenArgsFinObjMap (BaseObj FZ) = 1  -- One nat argument
FTestNatWithParityEvenArgsFinObjMap (BaseObj (FS FZ)) = 0
FTestNatWithParityEvenArgsFinObjMap (DepObj FZ FZ) = 1  -- One even proof
FTestNatWithParityEvenArgsFinObjMap (DepObj FZ (FS FZ)) = 0
FTestNatWithParityEvenArgsFinObjMap (DepObj (FS FZ) dep) = void (absurd dep)
FTestNatWithParityEvenArgsFinObjMap (DepObj (FS (FS i)) dep) = void (absurd i)

FTestNatWithParityEvenArgsFinMorMap :
  F2FFinCoprMorMap {forest=EvenOddForest} FTestNatWithParityEvenArgsFinObjMap
FTestNatWithParityEvenArgsFinMorMap IdMor x = x
FTestNatWithParityEvenArgsFinMorMap (DepToBase {base=FZ} {dep=FZ}) x = x
FTestNatWithParityEvenArgsFinMorMap (DepToBase {base=FZ} {dep=(FS FZ)}) x =
  absurd x
FTestNatWithParityEvenArgsFinMorMap (DepToBase {base=(FS FZ)} {dep}) x =
  absurd dep

FTestNatWithParityEvenArgsFinCopr : F2FFinCopr EvenOddForest
FTestNatWithParityEvenArgsFinCopr =
  (FTestNatWithParityEvenArgsFinObjMap ** FTestNatWithParityEvenArgsFinMorMap)

-- FTestNatWithParity Odd takes a nat and an odd proof
FTestNatWithParityOddArgsFinObjMap : F2FFinCoprObjMap EvenOddForest
FTestNatWithParityOddArgsFinObjMap (BaseObj FZ) = 1  -- One nat argument
FTestNatWithParityOddArgsFinObjMap (BaseObj (FS FZ)) = 0
FTestNatWithParityOddArgsFinObjMap (DepObj FZ FZ) = 0
FTestNatWithParityOddArgsFinObjMap (DepObj FZ (FS FZ)) = 1  -- One odd proof
FTestNatWithParityOddArgsFinObjMap (DepObj (FS FZ) dep) = void (absurd dep)
FTestNatWithParityOddArgsFinObjMap (DepObj (FS (FS i)) dep) = void (absurd i)

FTestNatWithParityOddArgsFinMorMap :
  F2FFinCoprMorMap {forest=EvenOddForest} FTestNatWithParityOddArgsFinObjMap
FTestNatWithParityOddArgsFinMorMap IdMor x = x
FTestNatWithParityOddArgsFinMorMap (DepToBase {base=FZ} {dep=FZ}) x = absurd x
FTestNatWithParityOddArgsFinMorMap (DepToBase {base=FZ} {dep=(FS FZ)}) x = x
FTestNatWithParityOddArgsFinMorMap (DepToBase {base=(FS FZ)} {dep}) x =
  absurd dep

FTestNatWithParityOddArgsFinCopr : F2FFinCopr EvenOddForest
FTestNatWithParityOddArgsFinCopr =
  (FTestNatWithParityOddArgsFinObjMap ** FTestNatWithParityOddArgsFinMorMap)

-- FTestNatEven Zero takes no arguments, reuse FTestNatZeroArgsFinCopr

-- FTestNatEven SuccOdd takes a nat and an odd proof
FTestNatEvenSuccOddArgsFinObjMap : F2FFinCoprObjMap EvenOddForest
FTestNatEvenSuccOddArgsFinObjMap (BaseObj FZ) = 1  -- One nat argument
FTestNatEvenSuccOddArgsFinObjMap (BaseObj (FS FZ)) = 0
FTestNatEvenSuccOddArgsFinObjMap (DepObj FZ FZ) = 0
FTestNatEvenSuccOddArgsFinObjMap (DepObj FZ (FS FZ)) = 1  -- One odd proof
FTestNatEvenSuccOddArgsFinObjMap (DepObj (FS FZ) dep) = void (absurd dep)
FTestNatEvenSuccOddArgsFinObjMap (DepObj (FS (FS i)) dep) = void (absurd i)

FTestNatEvenSuccOddArgsFinMorMap :
  F2FFinCoprMorMap {forest=EvenOddForest} FTestNatEvenSuccOddArgsFinObjMap
FTestNatEvenSuccOddArgsFinMorMap IdMor x = x
FTestNatEvenSuccOddArgsFinMorMap (DepToBase {base=FZ} {dep=FZ}) x = absurd x
FTestNatEvenSuccOddArgsFinMorMap (DepToBase {base=FZ} {dep=(FS FZ)}) x = x
FTestNatEvenSuccOddArgsFinMorMap (DepToBase {base=(FS FZ)} {dep}) x = absurd dep

FTestNatEvenSuccOddArgsFinCopr : F2FFinCopr EvenOddForest
FTestNatEvenSuccOddArgsFinCopr =
  (FTestNatEvenSuccOddArgsFinObjMap ** FTestNatEvenSuccOddArgsFinMorMap)

-- FTestNatOdd SuccEven takes a nat and an even proof
FTestNatOddSuccEvenArgsFinObjMap : F2FFinCoprObjMap EvenOddForest
FTestNatOddSuccEvenArgsFinObjMap (BaseObj FZ) = 1  -- One nat argument
FTestNatOddSuccEvenArgsFinObjMap (BaseObj (FS FZ)) = 0
FTestNatOddSuccEvenArgsFinObjMap (DepObj FZ FZ) = 1  -- One even proof argument
FTestNatOddSuccEvenArgsFinObjMap (DepObj FZ (FS FZ)) = 0
FTestNatOddSuccEvenArgsFinObjMap (DepObj (FS FZ) dep) = void (absurd dep)
FTestNatOddSuccEvenArgsFinObjMap (DepObj (FS (FS i)) dep) = void (absurd i)

FTestNatOddSuccEvenArgsFinMorMap :
  F2FFinCoprMorMap {forest=EvenOddForest} FTestNatOddSuccEvenArgsFinObjMap
FTestNatOddSuccEvenArgsFinMorMap IdMor x = x
FTestNatOddSuccEvenArgsFinMorMap (DepToBase {base=FZ} {dep=FZ}) x = x
FTestNatOddSuccEvenArgsFinMorMap (DepToBase {base=FZ} {dep=(FS FZ)}) x =
  absurd x
FTestNatOddSuccEvenArgsFinMorMap (DepToBase {base=(FS FZ)} {dep}) x = absurd dep

FTestNatOddSuccEvenArgsFinCopr : F2FFinCopr EvenOddForest
FTestNatOddSuccEvenArgsFinCopr =
  (FTestNatOddSuccEvenArgsFinObjMap ** FTestNatOddSuccEvenArgsFinMorMap)

-- Now define ETFinObjMap using the helper finite copresheaves
ETFinObjMap :
  F2FFinElemToFinCoprsObjMap {tgtForest=EvenOddForest} T1FinCopr EvenOddForest
-- FTestNat constructors
ETFinObjMap (BaseObj FZ ** FZ) = FTestNatZeroArgsFinCopr
ETFinObjMap (BaseObj FZ ** FS FZ) = FTestNatSuccArgsFinCopr
-- FTestNatWithParity constructors
ETFinObjMap (BaseObj (FS FZ) ** FZ) = FTestNatWithParityEvenArgsFinCopr
ETFinObjMap (BaseObj (FS FZ) ** FS FZ) = FTestNatWithParityOddArgsFinCopr
-- FTestNatEven constructors
ETFinObjMap (DepObj FZ FZ ** FZ) = FTestNatZeroArgsFinCopr
ETFinObjMap (DepObj FZ FZ ** FS FZ) = FTestNatEvenSuccOddArgsFinCopr
-- FTestNatOdd constructors
ETFinObjMap (DepObj FZ (FS FZ) ** FZ) = FTestNatOddSuccEvenArgsFinCopr
-- Impossible cases
ETFinObjMap (DepObj (FS FZ) dep ** _) = void (absurd dep)
ETFinObjMap (DepObj (FS (FS i)) dep ** _) = void (absurd i)

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
finCatPRATest : IO ()
finCatPRATest = do
  putStrLn ""
  putStrLn "===================="
  putStrLn "Begin FinCatPRATest:"
  putStrLn "--------------------"
  putStrLn ""
  putStrLn "------------------"
  putStrLn "End FinCatPRATest."
  putStrLn "=================="
  pure ()

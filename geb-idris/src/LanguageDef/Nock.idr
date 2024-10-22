module LanguageDef.Nock

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import Data.Nat
import Data.Maybe
import Decidable.Equality
import Data.String
import Text.Parser
import Text.Lexer
import Text.Parser.Core
import Text.Lexer.Core

%default total

-- Nouns are either atoms (natural numbers) or cells (pairs of nouns)
public export
data Noun = Atom Nat | Cell Noun Noun

-- Add after data Noun definition
export
decEq : (x, y : Noun) -> Dec (x = y)
decEq (Atom x) (Atom y) with (decEq x y)
  decEq (Atom x) (Atom x) | Yes Refl = Yes Refl
  decEq (Atom x) (Atom y) | No neq = No (\Refl => neq Refl)
decEq (Cell x1 y1) (Cell x2 y2) with (decEq x1 x2, decEq y1 y2)
  decEq (Cell x1 y1) (Cell x1 y1) | (Yes Refl, Yes Refl) = Yes Refl
  decEq (Cell x1 y1) (Cell x2 y2) | (No neq, _) = No (\Refl => neq Refl)
  decEq (Cell x1 y1) (Cell x2 y2) | (_, No neq) = No (\Refl => neq Refl)
decEq (Atom _) (Cell _ _) = No (\Refl impossible)
decEq (Cell _ _) (Atom _) = No (\Refl impossible)

export
implementation DecEq Noun where
  decEq = LanguageDef.Nock.decEq

export
implementation Eq Noun where
  x == y = case LanguageDef.Nock.decEq x y of
    Yes _ => True
    No _ => False

-- Nock formulas represent the computation rules
public export
data Formula =
    Slot Nat          -- 0, axis addressing
  | Quote Noun        -- 1, constant
  | Deep Formula      -- 2, cell navigation
  | Bump Formula      -- 3, increment
  | Inc Formula       -- 4, increment
  | Eq Formula        -- 5, equality test
  | If Formula Formula Formula    -- 6, conditional
  | Comp Formula Formula          -- 7, composition
  | Push Formula                  -- 8, extend subject
  | Call Formula                  -- 9, invoke
  | Hint Formula Formula          -- 10, debug hint
  | Core Formula Formula          -- 11, core operation

-- Basic noun operations
export
slot : Nat -> Noun -> Maybe Noun
slot 1 n = Just n
slot 2 (Cell a _) = Just a
slot 3 (Cell _ b) = Just b
slot n (Cell a b) =
  if n `mod` 2 == 0
    then slot (n `div` 2) a
    else slot (n `div` 2) b
slot _ _ = Nothing

-- Convert a Noun to a Formula
nounToFormula : Noun -> Maybe Formula
nounToFormula (Atom n) = Just (Slot n)  -- Simple conversion for atoms
nounToFormula (Cell (Atom 0) (Atom n)) = Just (Slot n)
nounToFormula (Cell (Atom 1) n) = Just (Quote n)
nounToFormula (Cell (Atom 2) n) = map Deep (nounToFormula n)
nounToFormula (Cell (Atom 3) n) = map Bump (nounToFormula n)
nounToFormula (Cell (Atom 4) n) = map Inc (nounToFormula n)
nounToFormula (Cell (Atom 5) n) = map Eq (nounToFormula n)
nounToFormula (Cell (Atom 6) (Cell a (Cell b c))) =
  [| If (nounToFormula a) (nounToFormula b) (nounToFormula c) |]
nounToFormula (Cell (Atom 7) (Cell a b)) =
  [| Comp (nounToFormula a) (nounToFormula b) |]
nounToFormula (Cell (Atom 8) n) = map Push (nounToFormula n)
nounToFormula (Cell (Atom 9) n) = map Call (nounToFormula n)
nounToFormula (Cell (Atom 10) (Cell a b)) =
  [| Hint (nounToFormula a) (nounToFormula b) |]
nounToFormula (Cell (Atom 11) (Cell a b)) =
  [| Core (nounToFormula a) (nounToFormula b) |]
nounToFormula _ = Nothing

export
evalBounded : (fuel : Nat) -> Noun -> Formula -> Maybe Noun
evalBounded 0 _ _ = Nothing  -- Out of fuel
evalBounded (S fuel) subject (Slot n) = slot n subject
evalBounded (S fuel) _ (Quote n) = Just n
evalBounded (S fuel) subject (Deep f) = case evalBounded fuel subject f of
  Just (Cell a _) => Just a
  _ => Nothing
evalBounded (S fuel) subject (Bump f) = case evalBounded fuel subject f of
  Just (Atom n) => Just (Atom (S n))
  _ => Nothing
evalBounded (S fuel) subject (Inc f) = case evalBounded fuel subject f of
  Just (Atom n) => Just (Atom (S n))
  _ => Nothing
evalBounded (S fuel) subject (Eq f) = case evalBounded fuel subject f of
  Just (Cell a b) => Just $ if a == b then Atom 0 else Atom 1
  _ => Nothing
evalBounded (S fuel) subject (If a b c) = case evalBounded fuel subject a of
  Just (Atom 0) => evalBounded fuel subject b
  Just _ => evalBounded fuel subject c
  Nothing => Nothing
evalBounded (S fuel) subject (Comp f g) = case evalBounded fuel subject f of
  Just res => evalBounded fuel subject g
  Nothing => Nothing
evalBounded (S fuel) subject (Push f) = case evalBounded fuel subject f of
  Just res => Just (Cell res subject)
  Nothing => Nothing
evalBounded (S fuel) subject (Call f) = case evalBounded fuel subject f of
  Just n => case nounToFormula n of
    Just formula => evalBounded fuel subject formula
    Nothing => Nothing
  Nothing => Nothing
evalBounded (S fuel) subject (Hint _ f) = evalBounded fuel subject f
evalBounded (S fuel) subject (Core f g) = case evalBounded fuel subject f of
  Just core => evalBounded fuel (Cell core subject) g
  Nothing => Nothing

-- Wrapper function with default fuel value
export
eval : Noun -> Formula -> Maybe Noun
eval = evalBounded 1000  -- Pick appropriate default fuel value

-- Show instances for debugging
export
implementation Show Noun where
  show (Atom n) = show n
  show (Cell a b) = "[" ++ show a ++ " " ++ show b ++ "]"

export
implementation Show Formula where
  show (Slot n) = "." ++ show n
  show (Quote n) = show n
  show (Deep f) = "*" ++ show f
  show (Bump f) = "+" ++ show f
  show (Inc f) = "++" ++ show f
  show (Eq f) = "=" ++ show f
  show (If a b c) = "?(" ++ show a ++ " " ++ show b ++ " " ++ show c ++ ")"
  show (Comp f g) = "(" ++ show f ++ " " ++ show g ++ ")"
  show (Push f) = ">" ++ show f
  show (Call f) = "%" ++ show f
  show (Hint a b) = "~(" ++ show a ++ " " ++ show b ++ ")"
  show (Core f g) = "#(" ++ show f ++ " " ++ show g ++ ")"

export
showNockNoun : Noun -> String
showNockNoun (Atom n) = show n
showNockNoun (Cell a b) = "[" ++ showNockNoun a ++ " " ++ showNockNoun b ++ "]"

showNockFormulaIndent : Nat -> Formula -> String
showNockFormulaIndent i f = pack (replicate i ' ') ++ showNockFormula' f where
  showNockFormula' : Formula -> String
  showNockFormula' (Slot n) = "[0 " ++ show n ++ "]"
  showNockFormula' (Quote n) = "[1 " ++ showNockNoun n ++ "]"
  showNockFormula' (Deep f) = "[2 " ++ showNockFormula' f ++ "]"
  showNockFormula' (Bump f) = "[3 " ++ showNockFormula' f ++ "]"
  showNockFormula' (Inc f) = "[4 " ++ showNockFormula' f ++ "]"
  showNockFormula' (Eq f) = "[5 " ++ showNockFormula' f ++ "]"
  showNockFormula' (If a b c) =
    "[6 " ++ showNockFormula' a ++ "\n" ++
    pack (replicate (i + 3) ' ') ++ showNockFormula' b ++ "\n" ++
    pack (replicate (i + 3) ' ') ++ showNockFormula' c ++ "]"
  showNockFormula' (Comp f g) =
    "[7 " ++ showNockFormula' f ++ "\n" ++
    pack (replicate (i + 3) ' ') ++ showNockFormula' g ++ "]"
  showNockFormula' (Push f) = "[8 " ++ showNockFormula' f ++ "]"
  showNockFormula' (Call f) = "[9 " ++ showNockFormula' f ++ "]"
  showNockFormula' (Hint a b) =
    "[10 " ++ showNockFormula' a ++ "\n" ++
    pack (replicate (i + 4) ' ') ++ showNockFormula' b ++ "]"
  showNockFormula' (Core a b) =
    "[11 " ++ showNockFormula' a ++ "\n" ++
    pack (replicate (i + 4) ' ') ++ showNockFormula' b ++ "]"

export
showNockFormula : Formula -> String
showNockFormula = showNockFormulaIndent 0

module Library.IdrisAlgebra

import Library.IdrisUtils
import Library.IdrisCategories

%default total

----------------------------------------
----------------------------------------
---- F-algebra universal properties ----
----------------------------------------
----------------------------------------

public export
FAlgEq : {f : Type -> Type} -> {a : Type} -> Algebra f a -> Algebra f a -> Type
FAlgEq {f} a b = ExtEq a b

public export
FAlgIso :
  {f : Type -> Type} -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  FAlgObj f -> FAlgObj f -> Type
FAlgIso {f} {fm} a b =
  Subset0 (FAlgMorph {fm} a b, FAlgMorph {fm} b a) $
    \(m, m') => ExtInverse (fst0 m) (fst0 m')

public export
IsCandidateInitialFAlg :
  {f : Type -> Type} -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  FAlgObj f -> Type
IsCandidateInitialFAlg {f} {fm} a = (b : FAlgObj f) -> FAlgMorph {fm} a b

public export
IsUniqueInitialFAlg :
  {f : Type -> Type} -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  FAlgObj f -> Type
IsUniqueInitialFAlg {f} {fm} a =
  (b : FAlgObj f) -> IsCandidateInitialFAlg {f} {fm} b -> FAlgIso {fm} a b

public export
IsInitialFAlg :
  {f : Type -> Type} -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  FAlgObj f -> Type
IsInitialFAlg {f} {fm} a =
  (IsCandidateInitialFAlg {f} {fm} a, IsUniqueInitialFAlg {f} {fm} a)

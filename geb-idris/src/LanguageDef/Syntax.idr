module LanguageDef.Syntax

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom

%default total

--------------------------------------
--------------------------------------
---- Geb term for core categories ----
--------------------------------------
--------------------------------------

----------------------------------
----------------------------------
---- General syntax utilities ----
----------------------------------
----------------------------------

public export
INDENT_DEPTH : Nat
INDENT_DEPTH = 2

public export
indentLines : List String -> List String
indentLines = map (indent INDENT_DEPTH)

public export
showLines : (a -> List String) -> a -> String
showLines sh = trim . unlines . sh

----------------------
----------------------
---- Binary trees ----
----------------------
----------------------

public export
data BTExpF : Type -> Type -> Type where
  BTA : atom -> BTExpF atom btty
  BTP : btty -> btty -> BTExpF atom btty

public export
data BTExp : Type -> Type where
  InBT : BTExpF atom (BTExp atom) -> BTExp atom

public export
InBTA : atom -> BTExp atom
InBTA = InBT . BTA

public export
InBTP : BTExp atom -> BTExp atom -> BTExp atom
InBTP = InBT .* BTP

public export
BTAlg : Type -> Type -> Type
BTAlg atom a = BTExpF atom a -> a

public export
btCata : BTAlg atom a -> BTExp atom -> a
btCata alg (InBT e) = alg $ case e of
  BTA a => BTA a
  BTP x y => BTP (btCata alg x) (btCata alg y)

public export
BTShowLinesAlg : Show atom => BTAlg atom (List String)
BTShowLinesAlg (BTA a) = [show a]
BTShowLinesAlg (BTP x y) = ["::"] ++ indentLines x ++ indentLines y

public export
btLines : Show atom => BTExp atom -> List String
btLines = btCata BTShowLinesAlg

public export
Show atom => Show (BTExp atom) where
  show = showLines btLines

-----------------------
-----------------------
---- S-expressions ----
-----------------------
-----------------------

public export
data SExpF : Type -> Type -> Type where
  SXF : atom -> List Nat -> List xty -> SExpF atom xty

public export
Bifunctor SExpF where
  bimap f g (SXF a ns xs) = SXF (f a) ns (map g xs)

public export
sxfAtom : SExpF atom xty -> atom
sxfAtom (SXF a _ _) = a

public export
sxfConsts : SExpF atom xty -> List Nat
sxfConsts (SXF _ ns _) = ns

public export
sxfSubexprs : SExpF atom xty -> List xty
sxfSubexprs (SXF _ _ xs) = xs

-- "Translate" the SExp functor, meaning, take its coproduct with a constant
-- type.
public export
data TrSExpF : Type -> Type -> Type -> Type where
  TrV : v -> TrSExpF atom v a -- variable
  TrC : SExpF atom a -> TrSExpF atom v a -- compound term

public export
Bifunctor (TrSExpF atom) where
  bimap f g (TrV v) = TrV (f v)
  bimap f g (TrC c) = TrC (bimap id g c)

public export
data FrSExpM : Type -> Type -> Type where
  InFS : TrSExpF atom ty (FrSExpM atom ty) -> FrSExpM atom ty

public export
SExp : Type -> Type
SExp atom = FrSExpM atom Void

public export
InSX : SExpF atom (FrSExpM atom ty) -> FrSExpM atom ty
InSX = InFS . TrC

public export
InSV : ty -> FrSExpM atom ty
InSV = InFS . TrV

public export
FrSListM : Type -> Type -> Type
FrSListM atom ty = List (FrSExpM atom ty)

public export
SList : Type -> Type
SList atom = FrSListM atom Void

public export
InS : atom -> List Nat -> FrSListM atom ty -> FrSExpM atom ty
InS a ns xs = InSX $ SXF a ns xs

public export
InSA : atom -> FrSExpM atom ty
InSA a = InS a [] []

-- "Scale" the SExp functor, meaning, take its product with a constant
-- type.
public export
data ScSExpF : Type -> Type -> Type -> Type where
  ScL : v -> SExpF atom a -> ScSExpF atom v a -- labeled term

public export
Bifunctor (ScSExpF atom) where
  bimap f g (ScL v c) = ScL (f v) (bimap id g c)

public export
data CoSExpCM : Type -> Type -> Type where
  InSXL : ScSExpF atom ty (CoSExpCM atom ty) -> CoSExpCM atom ty

public export
record FrSXLAlg (atom, ty, a, b : Type) where
  constructor FrSXA
  frsubst : ty -> a
  frxalg : atom -> List Nat -> b -> a
  frsxnil : b
  frsxcons : a -> b -> b

public export
record SXLAlg (atom, a, b : Type) where
  constructor SXA
  xalg : atom -> List Nat -> b -> a
  sxnil : b
  sxcons : a -> b -> b

public export
SXLSubstAlgToFr : {0 atom, ty, a, b : Type} ->
  (ty -> a) -> SXLAlg atom a b -> FrSXLAlg atom ty a b
SXLSubstAlgToFr {atom} {ty} {a} {b} subst (SXA xalg sxnil sxcons) =
  FrSXA subst xalg sxnil sxcons

public export
SXLAlgToFr : {0 atom, a, b : Type} -> SXLAlg atom a b -> FrSXLAlg atom Void a b
SXLAlgToFr {atom} {a} {b} = SXLSubstAlgToFr (voidF a)

mutual
  public export
  frsxCata : FrSXLAlg atom ty a b -> FrSExpM atom ty -> a
  frsxCata alg (InFS (TrV v)) = alg.frsubst v
  frsxCata alg (InFS (TrC x)) = case x of
    SXF a ns xs => alg.frxalg a ns $ frslCata alg xs

  public export
  frslCata : FrSXLAlg atom ty a b -> FrSListM atom ty -> b
  frslCata alg [] = alg.frsxnil
  frslCata alg (x :: xs) = alg.frsxcons (frsxCata alg x) (frslCata alg xs)

public export
sxSubstCata : (ty -> a) -> SXLAlg atom a b -> FrSExpM atom ty -> a
sxSubstCata subst alg = frsxCata (SXLSubstAlgToFr subst alg)

public export
slSubstCata : (ty -> a) -> SXLAlg atom a b -> FrSListM atom ty -> b
slSubstCata subst alg = frslCata (SXLSubstAlgToFr subst alg)

public export
sxCata : SXLAlg atom a b -> SExp atom -> a
sxCata = frsxCata . SXLAlgToFr

public export
slCata : SXLAlg atom a b -> SList atom -> b
slCata = frslCata . SXLAlgToFr

public export
SExpAlg : Type -> Type -> Type
SExpAlg atom a = SExpF atom a -> a

public export
SExpTypeAlg : Type -> Type
SExpTypeAlg atom = SExpAlg atom Type

public export
SExpTypeCtxAlg : Type -> Type -> Type
SExpTypeCtxAlg atom ctx = SExpAlg atom (ctx -> Type)

public export
SExpConsAlg : SExpAlg atom a -> SXLAlg atom a (List a)
SExpConsAlg alg = SXA (\x, ns, l => alg $ SXF x ns l) [] (::)

public export
sexpCata : SExpAlg atom a -> SExp atom -> a
sexpCata = sxCata . SExpConsAlg

public export
frsexpCata : (ty -> a) -> SExpAlg atom a -> FrSExpM atom ty -> a
frsexpCata subst alg = sxSubstCata subst (SExpConsAlg alg)

public export
slistCata : SExpAlg atom a -> SList atom -> List a
slistCata = slCata . SExpConsAlg

public export
frslistCata : (ty -> a) -> SExpAlg atom a -> FrSListM atom ty -> List a
frslistCata subst alg = slSubstCata subst (SExpConsAlg alg)

public export
slcPreservesLen : (alg : SExpAlg atom a) -> (l : SList atom) ->
  length (slistCata alg l) = length l
slcPreservesLen alg [] = Refl
slcPreservesLen alg (x :: l) = cong S (slcPreservesLen alg l)

public export
frslcPreservesLen : (subst : ty -> a) -> (alg : SExpAlg atom a) ->
  (l : FrSListM atom ty) -> length (frslistCata subst alg l) = length l
frslcPreservesLen subst alg [] = Refl
frslcPreservesLen subst alg (x :: l) = cong S (frslcPreservesLen subst alg l)

public export
SExpMaybeAlg : Type -> Type -> Type
SExpMaybeAlg atom a = SExpF atom a -> Maybe a

public export
SExpAlgFromMaybe : SExpMaybeAlg atom a -> SXLAlg atom (Maybe a) (Maybe (List a))
SExpAlgFromMaybe alg =
  SXA
    (\x, ns, ml => case ml of
      Just l => alg $ SXF x ns l
      _ => Nothing)
    (Just [])
    (\mx, ml => case (mx, ml) of
      (Just x, Just l) => Just (x :: l)
      _ => Nothing)

public export
sexpMaybeCata : SExpMaybeAlg atom a -> SExp atom -> Maybe a
sexpMaybeCata = sxCata . SExpAlgFromMaybe

public export
frsexpMaybeCata :
  (ty -> Maybe a) -> SExpMaybeAlg atom a -> FrSExpM atom ty -> Maybe a
frsexpMaybeCata subst = sxSubstCata subst . SExpAlgFromMaybe

public export
slistMaybeCata : SExpMaybeAlg atom a -> SList atom -> Maybe (List a)
slistMaybeCata = slCata . SExpAlgFromMaybe

public export
frslistMaybeCata :
  (ty -> Maybe a) -> SExpMaybeAlg atom a -> FrSListM atom ty -> Maybe (List a)
frslistMaybeCata subst = slSubstCata subst . SExpAlgFromMaybe

public export
SExpMaybeCtxAlg : Type -> Type -> Type -> Type
SExpMaybeCtxAlg atom ctx a = SExpF atom a -> ctx -> Maybe a

public export
SExpCtxAlgFromMaybe : SExpMaybeCtxAlg atom ctx a ->
  SXLAlg atom (ctx -> Maybe a) (ctx -> Maybe (List a))
SExpCtxAlgFromMaybe alg =
  SXA
    (\x, ns, ml, ctx => case ml ctx of
      Just l => alg (SXF x ns l) ctx
      Nothing => Nothing)
    (const $ Just [])
    (\mx, ml, ctx => case (mx ctx, ml ctx) of
      (Just x, Just l) => Just (x :: l)
      _ => Nothing)

public export
sexpMaybeCtxCata : SExpMaybeCtxAlg atom ctx a -> SExp atom -> ctx -> Maybe a
sexpMaybeCtxCata = sxCata . SExpCtxAlgFromMaybe

public export
frsexpMaybeCtxCata : (ty -> ctx -> Maybe a) -> SExpMaybeCtxAlg atom ctx a ->
  FrSExpM atom ty -> ctx -> Maybe a
frsexpMaybeCtxCata subst = sxSubstCata subst . SExpCtxAlgFromMaybe

public export
slistMaybeCtxCata : SExpMaybeCtxAlg atom ctx a ->
  SList atom -> ctx -> Maybe (List a)
slistMaybeCtxCata = slCata . SExpCtxAlgFromMaybe

public export
frslistMaybeCtxCata : (ty -> ctx -> Maybe a) -> SExpMaybeCtxAlg atom ctx a ->
  FrSListM atom ty -> ctx -> Maybe (List a)
frslistMaybeCtxCata subst = slSubstCata subst . SExpCtxAlgFromMaybe

public export
SExpBoolAlg : Type -> Type
SExpBoolAlg atom = atom -> List Nat -> Maybe Nat

public export
SExpAlgFromBool : SExpBoolAlg atom -> SExpAlg atom Bool
SExpAlgFromBool alg (SXF a ns xs) = all id xs && alg a ns == Just (length xs)

public export
SExpBoolToMaybeAlg : SExpBoolAlg atom -> SExpMaybeAlg atom Unit
SExpBoolToMaybeAlg alg (SXF a ns xs) =
  if (alg a ns == Just (length xs)) then Just () else Nothing

public export
sexpBoolCata : SExpBoolAlg atom -> SExp atom -> Bool
sexpBoolCata = sexpCata . SExpAlgFromBool

public export
frsexpBoolCata :
  (ty -> Bool) -> SExpBoolAlg atom -> FrSExpM atom ty -> Bool
frsexpBoolCata subst = frsexpCata subst . SExpAlgFromBool

public export
slistBoolCataL : SExpBoolAlg atom -> SList atom -> List Bool
slistBoolCataL = slistCata . SExpAlgFromBool

public export
slistBoolCata : SExpBoolAlg atom -> SList atom -> Bool
slistBoolCata alg l = all id (slistBoolCataL alg l)

public export
frslistBoolCataL :
  (ty -> Bool) -> SExpBoolAlg atom -> FrSListM atom ty -> List Bool
frslistBoolCataL subst = frslistCata subst . SExpAlgFromBool

public export
frslistBoolCata :
  (ty -> Bool) -> SExpBoolAlg atom -> FrSListM atom ty -> Bool
frslistBoolCata subst alg l = all id (frslistBoolCataL subst alg l)

public export
SExpRefined : {atom : Type} -> SExpBoolAlg atom -> Type
SExpRefined alg = Refinement {a=(SExp atom)} (sexpBoolCata alg)

public export
SExpRefinedUnicity : {atom : Type} -> {alg : SExpBoolAlg atom} ->
  {x, x' : SExpRefined alg} ->
  shape {p=(sexpBoolCata alg)} x = shape {p=(sexpBoolCata alg)} x' -> x = x'
SExpRefinedUnicity {atom} {alg} =
  refinementFstEq {a=(SExp atom)} {pred=(sexpBoolCata alg)}

public export
ProdT : List Type -> Type
ProdT = foldr Pair Unit

public export
SExpForallAlg : SExpTypeAlg atom -> SExpTypeAlg atom
SExpForallAlg alg x = (alg x, ProdT (sxfSubexprs x))

public export
sexpForallCata : SExpTypeAlg atom -> SExp atom -> Type
sexpForallCata = sexpCata . SExpForallAlg

public export
slistForallCataL : SExpTypeAlg atom -> SList atom -> List Type
slistForallCataL = slistCata . SExpForallAlg

public export
slistForallCata : SExpTypeAlg atom -> SList atom -> Type
slistForallCata = ProdT .* slistForallCataL

public export
SExpTypeAlgFromBool : SExpBoolAlg atom -> SExpTypeAlg atom
SExpTypeAlgFromBool alg (SXF a ns tys) = alg a ns = Just (length tys)

public export
sexpBoolTypeCata : SExpBoolAlg atom -> SExp atom -> Type
sexpBoolTypeCata = sexpForallCata . SExpTypeAlgFromBool

public export
slistBoolTypeCataL : SExpBoolAlg atom -> SList atom -> List Type
slistBoolTypeCataL = slistForallCataL . SExpTypeAlgFromBool

public export
slistBoolTypeCata : SExpBoolAlg atom -> SList atom -> Type
slistBoolTypeCata = slistForallCata . SExpTypeAlgFromBool

public export
SExpConstrained : {atom : Type} -> SExpBoolAlg atom -> Type
SExpConstrained alg = Subset0 (SExp atom) (sexpBoolTypeCata alg)

mutual
  public export
  sexpBoolTypeCata_unique : {alg : SExpBoolAlg atom} -> {x : SExp atom} ->
    (w, w' : sexpBoolTypeCata alg x) -> w = w'
  sexpBoolTypeCata_unique {x=(InFS (TrV v))} w w' = void v
  sexpBoolTypeCata_unique {alg} {x=(InFS (TrC (SXF a ns xs)))}
    (algeq, subeq) (algeq', subeq') =
      rewrite uip {eq=algeq} {eq'=algeq'} in
      rewrite slistBoolTypeCata_unique {alg} {l=xs} subeq subeq' in
      Refl

  public export
  slistBoolTypeCata_unique : {alg : SExpBoolAlg atom} -> {l : SList atom} ->
    (w, w' : slistBoolTypeCata alg l) -> w = w'
  slistBoolTypeCata_unique {l=[]} () () = Refl
  slistBoolTypeCata_unique {alg} {l=(x :: xs)} (wx, wxs) (wx', wxs') =
    rewrite sexpBoolTypeCata_unique {alg} {x} wx wx' in
    rewrite slistBoolTypeCata_unique {alg} {l=xs} wxs wxs' in
    Refl

public export
SExpConstrainedUnicity : {atom : Type} -> {alg : SExpBoolAlg atom} ->
  {x, x' : SExpConstrained alg} ->
  fst0 x = fst0 x' -> x = x'
SExpConstrainedUnicity {alg} {x=(Element0 x p)} {x'=(Element0 _ p')} Refl =
  replace
    {p=(\p'' => Element0 x p = Element0 {dep=(sexpBoolTypeCata alg)} x p'')}
    (sexpBoolTypeCata_unique {alg} p p')
    Refl

mutual
  public export
  sexpBoolComputeToConstraint : (alg : SExpBoolAlg atom) -> (x : SExp atom) ->
    sexpBoolCata alg x = True -> sexpBoolTypeCata alg x
  sexpBoolComputeToConstraint alg (InFS (TrV v)) eq = void v
  sexpBoolComputeToConstraint alg (InFS (TrC (SXF a ns xs))) eq =
    (rewrite slcPreservesLen (SExpForallAlg (SExpTypeAlgFromBool alg)) xs in
     rewrite sym (slcPreservesLen (SExpAlgFromBool alg) xs) in
     fromIsTrueMaybeNat _ _ (andRight eq),
     slistBoolComputeToConstraint alg xs $ andLeft eq)

  public export
  slistBoolComputeToConstraint : (alg : SExpBoolAlg atom) -> (l : SList atom) ->
    slistBoolCata alg l = True -> slistBoolTypeCata alg l
  slistBoolComputeToConstraint alg [] eq = ()
  slistBoolComputeToConstraint alg (x :: xs) eq =
    (sexpBoolComputeToConstraint alg x $ foldTrueInit _ _ eq,
     slistBoolComputeToConstraint alg xs $ foldTrueList _ _ eq)

mutual
  public export
  sexpBoolConstraintToCompute : (alg : SExpBoolAlg atom) -> (x : SExp atom) ->
    sexpBoolTypeCata alg x -> sexpBoolCata alg x = True
  sexpBoolConstraintToCompute alg (InFS (TrV v)) w = void v
  sexpBoolConstraintToCompute alg (InFS (TrC (SXF a ns xs))) (algeq, subeq) =
    andBoth
      (slistBoolConstraintToCompute alg xs subeq)
      (toIsTrueMaybeNat _ _ $
        replace {p=(\len => alg a ns = Just len)}
          (sym (slcPreservesLen (SExpAlgFromBool alg) xs))
          (replace {p=(\len => alg a ns = Just len)}
            (slcPreservesLen (SExpForallAlg (SExpTypeAlgFromBool alg)) xs)
            algeq))

  public export
  slistBoolConstraintToCompute : (alg : SExpBoolAlg atom) -> (l : SList atom) ->
    slistBoolTypeCata alg l -> slistBoolCata alg l = True
  slistBoolConstraintToCompute alg [] () = Refl
  slistBoolConstraintToCompute alg (x :: xs) (xeq, xseq) =
    foldTrueBoth (sexpBoolCata alg x) (slistBoolCataL alg xs)
      (sexpBoolConstraintToCompute alg x xeq)
      (slistBoolConstraintToCompute alg xs xseq)

public export
sexpCtoR : {atom : Type} -> {alg : SExpBoolAlg atom} ->
  SExpConstrained alg -> SExpRefined alg
sexpCtoR (Element0 x p) = (Element0 x $ sexpBoolConstraintToCompute alg x p)

public export
sexpRtoC : {atom : Type} -> {alg : SExpBoolAlg atom} ->
  SExpRefined alg -> SExpConstrained alg
sexpRtoC (Element0 x p) = (Element0 x $ sexpBoolComputeToConstraint alg x p)

public export
sexpCtoRtoCid : {atom : Type} -> {alg : SExpBoolAlg atom} ->
  (x : SExpConstrained alg) -> sexpRtoC {alg} (sexpCtoR {alg} x) = x
sexpCtoRtoCid {alg} (Element0 x p) = SExpConstrainedUnicity {alg} Refl

public export
sexpRtoCtoRid : {atom : Type} -> {alg : SExpBoolAlg atom} ->
  (x : SExpRefined alg) -> sexpCtoR {alg} (sexpRtoC {alg} x) = x
sexpRtoCtoRid {alg} (Element0 x p) = SExpRefinedUnicity {alg} Refl

---------------------------------------
---- Context-dependent refinements ----
---------------------------------------

public export
SExpBoolCtxAlg : Type -> Type -> Type
SExpBoolCtxAlg atom ctx = atom -> List Nat -> ctx -> Maybe (List ctx)

public export
SExpAlgFromBoolCtx : SExpBoolCtxAlg atom ctx -> SExpAlg atom (ctx -> Bool)
SExpAlgFromBoolCtx alg (SXF a ns xs) c with (alg a ns c)
  SExpAlgFromBoolCtx alg (SXF a ns xs) c | Just cs =
    case decEq (length xs) (length cs) of
      Yes eq => all id $ zipLen id xs cs eq
      No neq => False
  SExpAlgFromBoolCtx alg (SXF a ns xs) c | Nothing = False

public export
sexpBoolCtxCata : SExpBoolCtxAlg atom ctx -> SExp atom -> ctx -> Bool
sexpBoolCtxCata = sexpCata . SExpAlgFromBoolCtx

public export
sexpBoolCtxCataFlip : SExpBoolCtxAlg atom ctx -> ctx -> SExp atom -> Bool
sexpBoolCtxCataFlip = flip . sexpBoolCtxCata

public export
frsexpBoolCtxCata : (ty -> ctx -> Bool) ->
  SExpBoolCtxAlg atom ctx -> FrSExpM atom ty -> ctx -> Bool
frsexpBoolCtxCata subst = frsexpCata subst . SExpAlgFromBoolCtx

public export
slistBoolCtxCataL : SExpBoolCtxAlg atom ctx -> SList atom -> List (ctx -> Bool)
slistBoolCtxCataL = slistCata . SExpAlgFromBoolCtx

public export
slistBoolCtxCata : SExpBoolCtxAlg atom ctx -> SList atom -> ctx -> Bool
slistBoolCtxCata alg l c = all id $ map (\f => f c) $ slistBoolCtxCataL alg l

public export
frslistBoolCtxCataL : (ty -> ctx -> Bool) -> SExpBoolCtxAlg atom ctx ->
  FrSListM atom ty -> List (ctx -> Bool)
frslistBoolCtxCataL subst = frslistCata subst . SExpAlgFromBoolCtx

public export
frslistBoolCtxCata : (ty -> ctx -> Bool) -> SExpBoolCtxAlg atom ctx ->
  FrSListM atom ty -> ctx -> Bool
frslistBoolCtxCata subst alg l c =
  all id $ map (\f => f c) $ frslistBoolCtxCataL subst alg l

public export
SExpCtxRefined : {atom, ctx : Type} -> SExpBoolCtxAlg atom ctx -> SliceObj ctx
SExpCtxRefined {atom} {ctx} alg c =
  Refinement {a=(SExp atom)} (sexpBoolCtxCataFlip alg c)

public export
SExpCtxRefinedUnicity : {atom, ctx : Type} -> {alg : SExpBoolCtxAlg atom ctx} ->
  {c : ctx} -> {x, x' : SExpCtxRefined alg c} ->
  shape {p=(sexpBoolCtxCataFlip alg c)} x =
    shape {p=(sexpBoolCtxCataFlip alg c)} x' ->
  x = x'
SExpCtxRefinedUnicity {atom} {ctx} {alg} {c} {x} {x'} =
  refinementFstEq {a=(SExp atom)} {pred=(sexpBoolCtxCataFlip alg c)}

public export
SExpForallConstCtxAlg : SExpTypeCtxAlg atom ctx -> SExpTypeCtxAlg atom ctx
SExpForallConstCtxAlg alg x c =
  (alg x c, ProdT $ map (\f => f c) $ sxfSubexprs x)

public export
sexpForallConstCtxCata : SExpTypeCtxAlg atom ctx -> SExp atom -> ctx -> Type
sexpForallConstCtxCata = sexpCata . SExpForallConstCtxAlg

public export
slistForallConstCtxCataL :
  SExpTypeCtxAlg atom ctx -> SList atom -> ctx -> List Type
slistForallConstCtxCataL alg l c =
  map (\f => f c) $ slistCata (SExpForallConstCtxAlg alg) l

public export
slistForallConstCtxCata : SExpTypeCtxAlg atom ctx -> SList atom -> ctx -> Type
slistForallConstCtxCata alg = ProdT .* slistForallConstCtxCataL alg

public export
SExpTypeForallCtxAlgFromBool : {ctx : Type} ->
  SExpBoolCtxAlg atom ctx -> SExpTypeCtxAlg atom ctx
SExpTypeForallCtxAlgFromBool {ctx} alg (SXF a ns tys) c =
  (j : IsJustTrue (alg a ns c) **
   eq : Prelude.List.length tys = Prelude.List.length (fromIsJust j) **
   ProdT $ zipLen id tys (fromIsJust j) eq)

public export
sexpBoolTypeCtxCata : {ctx : Type} -> SExpBoolCtxAlg atom ctx ->
  SExp atom -> ctx -> Type
sexpBoolTypeCtxCata = sexpCata . SExpTypeForallCtxAlgFromBool

public export
sexpBoolTypeCtxCataFlip : {ctx : Type} -> SExpBoolCtxAlg atom ctx ->
  ctx -> SExp atom -> Type
sexpBoolTypeCtxCataFlip = flip . sexpBoolTypeCtxCata

public export
slistBoolTypeCtxCataL : {ctx : Type} -> SExpBoolCtxAlg atom ctx ->
  SList atom -> List (ctx -> Type)
slistBoolTypeCtxCataL = slistCata . SExpTypeForallCtxAlgFromBool

public export
slistBoolTypeCtxCata : {ctx : Type} -> SExpBoolCtxAlg atom ctx ->
  SList atom -> ctx -> Type
slistBoolTypeCtxCata alg l c =
  ProdT $ map (\f => f c) $ slistBoolTypeCtxCataL alg l

public export
SExpCtxConstrained : {atom, ctx : Type} ->
  SExpBoolCtxAlg atom ctx -> SliceObj ctx
SExpCtxConstrained {atom} {ctx} alg c =
  Subset0 (SExp atom) (sexpBoolTypeCtxCataFlip alg c)

-------------------------------
---- Slice (cata)morphisms ----
-------------------------------

public export
record SExpSliceAlg {ty : Type}
    (sxa : SliceObj (FrSExpM atom ty)) (sxb : SliceObj (FrSExpM atom ty))
    (sla : SliceObj (FrSListM atom ty)) (slb : SliceObj (FrSListM atom ty))
    where
  constructor SSA
  ssaSubTy :
    (a : atom) -> (ns : List Nat) -> (xs : FrSListM atom ty) ->
    sxa (InFS (TrC (SXF a ns xs))) -> sla xs
  ssaHeadTy :
    (x : FrSExpM atom ty) -> (xs : FrSListM atom ty) -> sla (x :: xs) -> sxa x
  ssaTailTy :
    (x : FrSExpM atom ty) -> (xs : FrSListM atom ty) -> sla (x :: xs) -> sla xs
  ssaSubst : SliceMorphism {a=ty} (sxa . InSV) (sxb . InSV)
  ssaInd :
    (a : atom) -> (ns : List Nat) -> (xs : FrSListM atom ty) ->
    sxa (InFS (TrC (SXF a ns xs))) -> slb xs -> sxb (InFS (TrC (SXF a ns xs)))
  ssaNil : sla [] -> slb []
  ssaCons :
    (x : FrSExpM atom ty) -> (xs : FrSListM atom ty) ->
    sxb x -> slb xs -> slb (x :: xs)

mutual
  public export
  sexpDepCata :
    {sxa, sxb : SliceObj (FrSExpM atom ty)} ->
    {sla, slb : SliceObj (FrSListM atom ty)} ->
    (alg : SExpSliceAlg sxa sxb sla slb) ->
    SliceMorphism {a=(FrSExpM atom ty)} sxa sxb
  sexpDepCata alg (InFS (TrV v)) av = alg.ssaSubst v av
  sexpDepCata alg (InFS (TrC (SXF a ns xs))) ax =
    alg.ssaInd a ns xs ax (slistDepCata alg xs (alg.ssaSubTy a ns xs ax))

  public export
  slistDepCata :
    {sxa, sxb : SliceObj (FrSExpM atom ty)} ->
    {sla, slb : SliceObj (FrSListM atom ty)} ->
    (alg : SExpSliceAlg sxa sxb sla slb) ->
    SliceMorphism {a=(FrSListM atom ty)} sla slb
  slistDepCata alg [] al = alg.ssaNil al
  slistDepCata alg (x :: xs) al =
    alg.ssaCons x xs
      (sexpDepCata alg x (alg.ssaHeadTy x xs al))
      (slistDepCata alg xs (alg.ssaTailTy x xs al))

public export
SExpSliceMorphAlg : {atom : Type} ->
  SExpTypeAlg atom -> SExpTypeAlg atom -> Type
SExpSliceMorphAlg {atom} sa sb =
  (a : atom) -> (ns : List Nat) -> (xs : SList atom) ->
  sa (SXF a ns $ slistForallCataL sa xs) ->
  slistForallCata sa xs ->
  slistForallCata sb xs ->
  sb (SXF a ns $ slistForallCataL sb xs)

public export
SExpSliceAlgFromMorph : {sa, sb : SExpTypeAlg atom} ->
  SExpSliceMorphAlg sa sb ->
  SExpSliceAlg
    (sexpForallCata sa) (sexpForallCata sb)
    (slistForallCata sa) (slistForallCata sb)
SExpSliceAlgFromMorph alg =
  SSA
    (\a, ns, xs, (sxa, subs) => subs)
    (\x, xs, (sx, sxs) => sx)
    (\x, xs, (sx, sxs) => sxs)
    (\v, _ => void v)
    (\a, ns, xs, (sx, sxas), sxbs => (alg a ns xs sx sxas sxbs, sxbs))
    id
    (\x, xs, sx, sxs => (sx, sxs))

public export
sexpSliceCata : {sa, sb : SExpTypeAlg atom} ->
  SExpSliceMorphAlg sa sb ->
  SliceMorphism {a=(SExp atom)} (sexpForallCata sa) (sexpForallCata sb)
sexpSliceCata {sa} {sb} = sexpDepCata . (SExpSliceAlgFromMorph {sa} {sb})

public export
slistSliceCata : {sa, sb : SExpTypeAlg atom} ->
  SExpSliceMorphAlg sa sb ->
  SliceMorphism {a=(SList atom)} (slistForallCata sa) (slistForallCata sb)
slistSliceCata {sa} {sb} = slistDepCata . (SExpSliceAlgFromMorph {sa} {sb})

-------------------
---- Utilities ----
-------------------

public export
SExpLinesAlg : Show atom => SXLAlg atom (List String) (List String)
SExpLinesAlg =
  SXA
    (\a, ns, xs => (show a ++ " : " ++ show ns) :: indentLines xs)
    []
    (++)

public export
sexpLines : Show atom => SExp atom -> List String
sexpLines = sxCata SExpLinesAlg

public export
frsexpLines : Show atom => Show ty => FrSExpM atom ty -> List String
frsexpLines = sxSubstCata (\x => [show x]) SExpLinesAlg

public export
Show atom => Show ty => Show (FrSExpM atom ty) where
  show = showLines frsexpLines

public export
data SExpToBtAtom : Type -> Type where
  SBAtom : atom -> SExpToBtAtom atom
  SBNil : SExpToBtAtom atom
  SBNat : Nat -> SExpToBtAtom atom

public export
Show atom => Show (SExpToBtAtom atom) where
  show (SBAtom a) = show a
  show SBNil = "[]"
  show (SBNat n) = show n

-------------------------------------------------
---- S-expression <-> binary-tree conversion ----
-------------------------------------------------

mutual
  public export
  SExpToBtAlg : SExpAlg atom (BTExp $ SExpToBtAtom atom)
  SExpToBtAlg (SXF a ns xs) =
    InBTP (InBTA $ SBAtom a) $ InBTP (NatListToBtAlg ns) (SListToBtAlg xs)

  public export
  NatListToBtAlg : List Nat -> BTExp (SExpToBtAtom atom)
  NatListToBtAlg [] = InBTA SBNil
  NatListToBtAlg (n :: ns) = InBTP (InBTA $ SBNat n) (NatListToBtAlg ns)

  public export
  SListToBtAlg : List (BTExp $ SExpToBtAtom atom) -> BTExp (SExpToBtAtom atom)
  SListToBtAlg [] = InBTA SBNil
  SListToBtAlg (x :: xs) = InBTP x (SListToBtAlg xs)

public export
sexpToBt : SExp atom -> BTExp $ SExpToBtAtom atom
sexpToBt = sexpCata SExpToBtAlg

mutual
  public export
  btToSexp : BTExp (SExpToBtAtom atom) -> Maybe (SExp atom)
  btToSexp (InBT x) = case x of
    BTA a => case a of
      SBAtom a' => Just $ InS a' [] []
      SBNil => Nothing
      SBNat n => Nothing
    BTP (InBT y) (InBT z) => case y of
      BTA a => case a of
        SBAtom a' => case z of
          BTP y' z' => case (btToNatList y', btToSexpList z') of
            (Just ns, Just xs) => Just $ InS a' ns xs
            _ => Nothing
          _ => Nothing
        _ => Nothing
      BTP y z => Nothing

  public export
  btToNatList : BTExp (SExpToBtAtom atom) -> Maybe (List Nat)
  btToNatList (InBT x) = case x of
    BTA a => case a of
      SBNil => Just []
      _ => Nothing
    BTP y z => case y of
      InBT (BTA (SBNat n)) => case btToNatList z of
        Just ns => Just $ n :: ns
        Nothing => Nothing
      _ => Nothing

  public export
  btToSexpList : BTExp (SExpToBtAtom atom) -> Maybe (List $ SExp atom)
  btToSexpList (InBT x) = case x of
    BTA a => case a of
      SBNil => Just []
      _ => Nothing
    BTP y z => case (btToSexp y, btToSexpList z) of
      (Just x, Just xs) => Just $ x :: xs
      _ => Nothing

--------------------------------
---- Pairs of s-expressions ----
--------------------------------

public export
SExpDecEqNTAlg : Type -> Type
SExpDecEqNTAlg atom = NaturalTransformation DecEqPred (DecEqPred . SExpF atom)

public export
sexpDecEqNTAlg : DecEqPred atom -> SExpDecEqNTAlg atom
sexpDecEqNTAlg deqatom a deqa (SXF e ns xs) (SXF e' ns' xs') =
  case deqatom e e' of
    Yes Refl => case decEq ns ns' of
      Yes Refl => case decEq xs xs' of
        Yes Refl => Yes Refl
        No neq => No $ \eq => case eq of Refl => neq Refl
      No neq => No $ \eq => case eq of Refl => neq Refl
    No neq => No $ \eq => case eq of Refl => neq Refl
  where
    DecEq a where
      decEq = deqa

mutual
  public export
  sexpDecEq : {atom : Type} -> DecEq ty =>
    DecEqPred atom -> DecEqPred (FrSExpM atom ty)
  sexpDecEq deq (InFS (TrV v)) (InFS (TrV v')) =
    case decEq v v' of
      Yes Refl => Yes Refl
      No neq => No $ \Refl => neq Refl
  sexpDecEq deq (InFS (TrV _)) (InFS (TrC _)) =
    No $ \eq => case eq of Refl impossible
  sexpDecEq deq (InFS (TrC _)) (InFS (TrV _)) =
    No $ \eq => case eq of Refl impossible
  sexpDecEq deq (InFS (TrC (SXF a ns xs))) (InFS (TrC c')) =
    case c' of
      SXF a' ns' xs' => case deq a a' of
        Yes Refl => case decEq ns ns' of
          Yes Refl => case slistDecEq deq xs xs' of
            Yes Refl => Yes Refl
            No neq => No $ \eq => case eq of Refl => neq Refl
          No neq => No $ \eq => case eq of Refl => neq Refl
        No neq => No $ \eq => case eq of Refl => neq Refl

  public export
  slistDecEq : {atom : Type} -> DecEq ty =>
    DecEqPred atom -> DecEqPred (FrSListM atom ty)
  slistDecEq deq [] [] = Yes Refl
  slistDecEq deq [] (x :: xs) = No $ \eq => case eq of Refl impossible
  slistDecEq deq (x :: xs) [] = No $ \eq => case eq of Refl impossible
  slistDecEq deq (x :: xs) (x' :: xs') =
    case sexpDecEq deq x x' of
      Yes Refl => case slistDecEq deq xs xs' of
        Yes Refl => Yes Refl
        No neq => No $ \eq => case eq of Refl => neq Refl
      No neq => No $ \eq => case eq of Refl => neq Refl

public export
(atom : Type) => DecEq atom => DecEq ty => DecEq (FrSExpM atom ty) where
  decEq = sexpDecEq decEq

public export
(atom : Type) => DecEq atom => DecEq ty => Eq (FrSExpM atom ty) where
  x == x' = isYes $ decEq x x'

public export
(atom : Type) => DecEq atom => (alg : SExpBoolAlg atom) =>
    DecEq (SExpRefined alg) where
  decEq (Element0 x p) (Element0 x' p') = case decEq x x' of
    Yes eq => Yes $ SExpRefinedUnicity {alg} eq
    No neq => No $ \Refl => neq Refl

public export
(atom : Type) => DecEq atom => (alg : SExpBoolAlg atom) =>
    DecEq (SExpConstrained alg) where
  decEq (Element0 x p) (Element0 x' p') = case decEq x x' of
    Yes eq => Yes $ SExpConstrainedUnicity {alg} eq
    No neq => No $ \Refl => neq Refl

---------------------------------------------------------------------
---- SExp monad operations (where the domain is a type of atoms) ----
---------------------------------------------------------------------

public export
sexpMapAlg : (atom -> atom') -> SExpAlg atom (FrSExpM atom' ty)
sexpMapAlg f (SXF a ns xs) = InS (f a) ns xs

public export
Functor SExp where
  map = sexpCata . sexpMapAlg

public export
sexpReturn : atom -> SExp atom
sexpReturn a = InS a [] []

public export
SExpJoinAlg : SExpAlg (SExp atom) (SExp atom)
SExpJoinAlg (SXF (InFS (TrV v)) ns' xs') = void v
SExpJoinAlg (SXF (InFS (TrC (SXF a ns xs))) ns' xs') =
  InS a (ns ++ ns') (xs ++ xs')

public export
sexpJoin : SExp (SExp atom) -> SExp atom
sexpJoin = sexpCata SExpJoinAlg

public export
sexpBind : SExp atom -> (atom -> SExp atom') -> SExp atom'
sexpBind x f = sexpJoin (map {f=SExp} f x)

public export
sexpApp : SExp (a -> b) -> SExp a -> SExp b
sexpApp xf = sexpBind xf . flip (map {f=SExp})

public export
Applicative SExp where
  pure = sexpReturn
  (<*>) = sexpApp

public export
Monad SExp where
  (>>=) = sexpBind
  join = sexpJoin

----------------------------------------------------------------------------
---- FrSExpM monad operations (where the domain is a type of variables) ----
----------------------------------------------------------------------------

public export
Bifunctor FrSExpM where
  bimap f g = frsexpCata (InSV . g) (sexpMapAlg f)

public export
frsexpReturn : ty -> FrSExpM atom ty
frsexpReturn = InSV

public export
frsexpJoinAlg : SExpAlg atom (FrSExpM atom ty)
frsexpJoinAlg = InSX

public export
frsexpJoin : FrSExpM atom (FrSExpM atom ty) -> FrSExpM atom ty
frsexpJoin = frsexpCata id frsexpJoinAlg

public export
frsexpBind : FrSExpM atom a -> (a -> FrSExpM atom b) -> FrSExpM atom b
frsexpBind x f =
  frsexpJoin (map @{BifunctorToFunctor} {f=(FrSExpM atom)} f x)

public export
frsexpApp : FrSExpM atom (a -> b) -> FrSExpM atom a -> FrSExpM atom b
frsexpApp xf =
  frsexpBind xf . flip (map @{BifunctorToFunctor} {f=(FrSExpM atom)})

public export
Applicative (FrSExpM atom) using BifunctorToFunctor where
  pure = frsexpReturn
  (<*>) = frsexpApp

public export
Monad (FrSExpM atom) using BifunctorToFunctor where
  (>>=) = frsexpBind
  join = frsexpJoin

-------------------------------
-------------------------------
---- Refined s-expressions ----
-------------------------------
-------------------------------

---------------------------------------------
---- General induction for s-expressions ----
---------------------------------------------

public export
SExpGenTypeAlg : SExpTypeAlg atom -> SExpTypeAlg atom
SExpGenTypeAlg alg x = (IdrisUtils.HList $ sxfSubexprs x, alg x)

public export
sexpGenTypeCata : SExpTypeAlg atom -> SExp atom -> Type
sexpGenTypeCata = sexpCata . SExpGenTypeAlg

public export
slistGenTypeCataL : SExpTypeAlg atom -> SList atom -> List Type
slistGenTypeCataL = slistCata . SExpGenTypeAlg

public export
slistGenTypeCata : SExpTypeAlg atom -> SList atom -> Type
slistGenTypeCata alg l = IdrisUtils.HList (slistGenTypeCataL alg l)

public export
SExpDepAlg : {atom : Type} ->
  SExpTypeAlg atom -> SExpMaybeAlg atom (SExp atom) -> Type
SExpDepAlg alg paramAlg =
  (a : atom) -> (ns : List Nat) -> (xs : SList atom) ->
  (0 _ : slistGenTypeCata alg xs) ->
  (params : SList atom) ->
  (0 _ : slistMaybeCata paramAlg xs = Just params) ->
  Maybe (alg (SXF a ns (slistGenTypeCataL alg xs)))

mutual
  public export
  sexpGenTypeDec : {atom : Type} ->
    (alg : SExpTypeAlg atom) ->
    (paramAlg : SExpMaybeAlg atom (SExp atom)) ->
    (step : SExpDepAlg alg paramAlg) ->
    (x : SExp atom) ->
    Maybe (sexpGenTypeCata alg x)
  sexpGenTypeDec alg paramAlg step (InFS (TrC (SXF a ns xs))) with
    (slistGenTypeDec alg paramAlg step xs, slistMaybeCata paramAlg xs) proof prf
      sexpGenTypeDec alg paramAlg step (InFS (TrC (SXF a ns xs)))
        | (Just vxs, Just params) =
          case step a ns xs vxs params (sndEq prf) of
            Just ty => Just (vxs, ty)
            _ => Nothing
      sexpGenTypeDec alg paramAlg step (InFS (TrC (SXF a ns xs)))
        | _ = Nothing

  public export
  slistGenTypeDec : {atom : Type} ->
    (alg : SExpTypeAlg atom) ->
    (paramAlg : SExpMaybeAlg atom (SExp atom)) ->
    (step : SExpDepAlg alg paramAlg) ->
    (l : SList atom) ->
    Maybe (slistGenTypeCata alg l)
  slistGenTypeDec alg paramAlg step [] = Just HNil
  slistGenTypeDec alg paramAlg step (x :: xs) =
    case
      (sexpGenTypeDec alg paramAlg step x,
       slistGenTypeDec alg paramAlg step xs) of
        (Just v, Just vs) => Just (HCons v vs)
        _ => Nothing

---------------------------
---- Per-atom algebras ----
---------------------------

public export
SExpAtomAlg : Type -> Type -> Type
SExpAtomAlg atom a = List Nat -> List a -> a

public export
SExpAlgFromAtoms : (atom -> SExpAtomAlg atom a) -> SExpAlg atom a
SExpAlgFromAtoms alg (SXF a ns xs) = alg a ns xs

-----------------
---- Arities ----
-----------------

-- Test whether the first list is bounded by the second list:  that is,
-- whether the lists have the same lengths, and each element of the first
-- list is strictly less than the corresponding element of the second list.
public export
listBounded : List Nat -> List Nat -> Bool
listBounded [] [] = True
listBounded [] (_ :: _) = False
listBounded (_ :: _) [] = False
listBounded (x :: xs) (y :: ys) = x < y && listBounded xs ys

-- S-expressions whose lists of constants and sub-expressions are of
-- lengths determined by their atoms.  (Each atom can be said to have
-- an arity.)
public export
record SArity (atom : Type) where
  constructor SAr
  natBounds : atom -> List Nat
  expAr : atom -> Nat

public export
CheckSExpLenAlg : SArity atom -> SExpBoolAlg atom
CheckSExpLenAlg ar a ns =
  if listBounded ns (ar.natBounds a) then Just (ar.expAr a) else Nothing

public export
checkSExpAr : SArity atom -> SExp atom -> Bool
checkSExpAr = sexpBoolCata . CheckSExpLenAlg

public export
ValidSExpLenAlg : SArity atom -> SExpTypeAlg atom
ValidSExpLenAlg ar (SXF a ns xs) =
  (IsTrue (listBounded ns (ar.natBounds a)), length xs = ar.expAr a)

public export
ValidSExpArAlg: SArity atom -> SExpTypeAlg atom
ValidSExpArAlg = SExpGenTypeAlg . ValidSExpLenAlg

public export
ValidSExpAr : SArity atom -> SExp atom -> Type
ValidSExpAr = sexpGenTypeCata . ValidSExpLenAlg

public export
ValidSListArL : SArity atom -> SList atom -> List Type
ValidSListArL = slistGenTypeCataL . ValidSExpLenAlg

public export
ValidSListAr : SArity atom -> SList atom -> Type
ValidSListAr = slistGenTypeCata . ValidSExpLenAlg

public export
ValidSExpDepAlg :
  (ar : SArity atom) -> SExpDepAlg (ValidSExpLenAlg ar) (Just . InSX)
ValidSExpDepAlg ar a ns xs tys params paramseq =
  case
    (decEq (listBounded ns (ar.natBounds a)) True,
     decEq (length xs) (ar.expAr a)) of
      (Yes nseq, Yes xseq) =>
        Just (nseq, trans (slcPreservesLen (ValidSExpArAlg ar) xs) xseq)
      _ =>
        Nothing

public export
validSExpAr : {atom : Type} ->
  (ar : SArity atom) -> (x : SExp atom) -> (Maybe . ValidSExpAr ar) x
validSExpAr ar =
  sexpGenTypeDec (ValidSExpLenAlg ar) (Just . InSX) (ValidSExpDepAlg ar)

--------------------------
---- Mutual recursion ----
--------------------------

public export
record MutRecSExpFam (atom : Type) (tys : Type) where
  constructor MRSFam
  mrfAssign : atom -> tys
  mrfBounds : atom -> List Nat
  mrfDirTy : atom -> List tys

public export
CheckMRSFAlg : Eq tys => MutRecSExpFam atom tys -> SExpMaybeAlg atom atom
CheckMRSFAlg (MRSFam assign bounds dirTy) (SXF a ns xs) =
  if listBounded ns (bounds a) && map assign xs == dirTy a
  then
    Just a
  else
    Nothing

public export
checkMRSF : Eq tys => MutRecSExpFam atom tys -> SExp atom -> Bool
checkMRSF fam = isJust . sexpMaybeCata (CheckMRSFAlg fam)

-------------------------------------------------
---- S-expressions as terms of type families ----
-------------------------------------------------

public export
record SExpParamSig (tys : Type) where
  constructor SExpParams
  sfParam : tys -> Maybe tys
  sfOrder : tys -> Nat
  0 sfParamOrdered :
    (ty : tys) -> (j : IsJustTrue (sfParam ty)) ->
    LT (sfOrder $ fromIsJust {x=(sfParam ty)} j) (sfOrder ty)

public export
record SExpFam (atom, tys : Type) where
  constructor SFam
  sfSig : SExpParamSig tys
  sfMRF : MutRecSExpFam atom tys

-----------------
-----------------
---- Symbols ----
-----------------
-----------------

public export
record SymSet where
  constructor SS
  slType : Type
  slSize : Nat
  slEnc : FinDecEncoding slType slSize
  slShow : slType -> String

public export
Show SymSet where
  show (SS ty sz enc sh) = let _ = MkShow sh in show (finFToVect (fst enc))

public export
FinSS : Nat -> SymSet
FinSS n = SS (Fin n) n (FinIdDecEncoding n) show

public export
VoidSS : SymSet
VoidSS = FinSS 0

--------------------
--------------------
---- Namespaces ----
--------------------
--------------------

public export
record Namespace where
  constructor NS
  nsLocalSym : SymSet
  nsSubSym : SymSet
  nsSub : Vect nsSubSym.slSize Namespace

public export
FinNS : (nloc : Nat) -> {nsub : Nat} -> Vect nsub Namespace -> Namespace
FinNS nloc {nsub} = NS (FinSS nloc) (FinSS nsub)

public export
VoidNS : Namespace
VoidNS = FinNS 0 []

mutual
  public export
  nsLines : Namespace -> List String
  nsLines (NS ls ss sub) =
    ("loc: " ++ show ls ++ "; sub: " ++ show ss) ::
     indentLines (nsVectLines sub)

  public export
  nsVectLines : {n : Nat} -> Vect n Namespace -> List String
  nsVectLines [] = []
  nsVectLines (ns :: v) = nsLines ns ++ nsVectLines v

public export
Show Namespace where
  show = showLines nsLines

public export
numSub : Namespace -> Nat
numSub = slSize . nsSubSym

public export
LeafNS : SymSet -> Namespace
LeafNS ss = NS ss VoidSS []

public export
data Subspace : Namespace -> Type where
  This : {ns : Namespace} -> Subspace ns
  Child : {ns : Namespace} ->
    (i : ns.nsSubSym.slType) ->
    Subspace (index (fst (snd ns.nsSubSym.slEnc i)) ns.nsSub) ->
    Subspace ns

public export
(ns : Namespace) => Show (Subspace ns) where
  show {ns} sub = "/" ++ showSub sub where
    showSub : {ns : Namespace} -> Subspace ns -> String
    showSub {ns} This = ""
    showSub {ns} (Child i sub) = slShow ns.nsSubSym i ++ "/" ++ showSub sub

------------------------------------
---- Geb-specific s-expressions ----
------------------------------------

public export
NExp : Type
NExp = SExp Nat

public export
NList : Type
NList = SList Nat

public export
GExp : Type
GExp = SExp OldAtom

public export
FrGExp : Type -> Type
FrGExp = FrSExpM OldAtom

public export
GList : Type
GList = SList OldAtom

public export
FrGList : Type -> Type
FrGList = FrSListM OldAtom

public export
GBtAtom : Type
GBtAtom = SExpToBtAtom OldAtom

public export
GBTExp : Type
GBTExp = BTExp GBtAtom

public export
GExpAlg : Type -> Type
GExpAlg = SExpAlg OldAtom

public export
GExpMaybeAlg : Type -> Type
GExpMaybeAlg = SExpMaybeAlg OldAtom

public export
GExpBoolAlg : Type
GExpBoolAlg = SExpBoolAlg OldAtom

public export
GExpMaybeCtxAlg : Type -> Type -> Type
GExpMaybeCtxAlg = SExpMaybeCtxAlg OldAtom

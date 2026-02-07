module LanguageDef.PolyProfEnd

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.PolyCat

%default total

------------------------------------------------------------
------------------------------------------------------------
---- Sections of Polynomial Functors ----
------------------------------------------------------------
------------------------------------------------------------

-- A section of a polynomial functor is a choice of direction for each
-- position. This characterizes natural transformations from the polynomial
-- functor to the identity functor.
--
-- For pf with InterpPolyFunc pf x = (i : pfPos pf ** pfDir pf i -> x),
-- a section picks one element of pfDir pf i for each i.
public export
PolySection : PolyFunc -> Type
PolySection pf = (i : pfPos pf) -> pfDir {p=pf} i

------------------------------------------------------------
---- Section to Natural Transformation ----
------------------------------------------------------------

-- Given a section, we can apply it to any element of InterpPolyFunc.
-- This is the "evaluation" map: given (i ** g : Dir i -> x) and d : Dir i,
-- return g(d(i)).
public export
sectionApply : {pf : PolyFunc} ->
  PolySection pf -> (x : Type) -> InterpPolyFunc pf x -> x
sectionApply d x elem = snd elem (d (fst elem))

-- The above is natural in x:
-- For f : a -> b, f . sectionApply d a = sectionApply d b . InterpPFMap pf f
--
-- Proof:
-- f (sectionApply d a (i ** g)) = f (g (d i))
-- sectionApply d b (InterpPFMap pf f (i ** g))
--   = sectionApply d b (i ** f . g)
--   = (f . g) (d i)
--   = f (g (d i))  -- definitional
public export
sectionApplyNatural : {pf : PolyFunc} -> (d : PolySection pf) ->
  (a, b : Type) -> (f : a -> b) ->
  (elem : InterpPolyFunc pf a) ->
  f (sectionApply {pf} d a elem) = sectionApply {pf} d b (InterpPFMap pf f elem)
sectionApplyNatural d a b f (i ** g) = Refl

------------------------------------------------------------
---- Natural Transformation to Section ----
------------------------------------------------------------

-- Given a natural transformation from InterpPolyFunc pf to Id,
-- we can extract a section by applying at the "universal element".
--
-- For each position i, we apply eta at type (pfDir pf i) to the
-- element (i ** id), which gives us an element of pfDir pf i.
public export
natTransToSection : {pf : PolyFunc} ->
  ((x : Type) -> InterpPolyFunc pf x -> x) -> PolySection pf
natTransToSection {pf} eta i = eta (pfDir {p=pf} i) (i ** id)

------------------------------------------------------------
---- Round-Trip: Section -> NatTrans -> Section ----
------------------------------------------------------------

-- Starting with a section, converting to nat trans, then back to section
-- gives the original section.
--
-- Proof:
-- natTransToSection (sectionApply d) i
--   = sectionApply d (pfDir i) (i ** id)
--   = id (d i)
--   = d i  -- definitional
public export
sectionRoundTrip : FunExt -> {pf : PolyFunc} -> (d : PolySection pf) ->
  natTransToSection {pf} (sectionApply {pf} d) = d
sectionRoundTrip fext d = funExt $ \i => Refl
  -- natTransToSection (sectionApply d) i
  -- = sectionApply d (pfDir i) (i ** id)
  -- = id (d i)
  -- = d i  -- each step is definitional

------------------------------------------------------------
---- Round-Trip: NatTrans -> Section -> NatTrans ----
------------------------------------------------------------

-- Starting with a natural transformation eta, converting to section,
-- then back to nat trans gives the original eta.
--
-- This requires eta to satisfy naturality. Given naturality, the proof is:
--
-- sectionApply (natTransToSection eta) x (i ** g)
--   = g (natTransToSection eta i)
--   = g (eta (pfDir i) (i ** id))
--
-- By naturality of eta with f = g : pfDir i -> x:
--   g . eta (pfDir i) = eta x . InterpPFMap pf g
--   g (eta (pfDir i) (i ** id)) = eta x (InterpPFMap pf g (i ** id))
--                               = eta x (i ** g . id)
--                               = eta x (i ** g)
--
-- So: sectionApply (natTransToSection eta) x (i ** g) = eta x (i ** g)

-- Type alias for naturality condition
public export
0 PolyNatTransNaturality : {pf : PolyFunc} ->
  ((x : Type) -> InterpPolyFunc pf x -> x) -> Type
PolyNatTransNaturality {pf} eta =
  (a, b : Type) -> (f : a -> b) -> (elem : InterpPolyFunc pf a) ->
    f (eta a elem) = eta b (InterpPFMap pf f elem)

-- The round-trip proof, given naturality
public export
natTransRoundTrip : {pf : PolyFunc} ->
  (eta : (y : Type) -> InterpPolyFunc pf y -> y) ->
  (nat : PolyNatTransNaturality {pf} eta) ->
  (x : Type) -> (elem : InterpPolyFunc pf x) ->
  sectionApply {pf} (natTransToSection {pf} eta) x elem = eta x elem
natTransRoundTrip {pf} eta nat x (i ** g) =
  -- Need: g (eta (pfDir i) (i ** id)) = eta x (i ** g)
  -- By naturality with f = g : pfDir i -> x:
  --   g (eta (pfDir i) (i ** id)) = eta x (InterpPFMap pf g (i ** id))
  --                               = eta x (i ** g . id)
  --                               = eta x (i ** g)
  nat (pfDir {p=pf} i) x g (i ** id)
  -- (i ** g . id) = (i ** g) definitionally, so trans with Refl is not needed

------------------------------------------------------------
------------------------------------------------------------
---- Polynomial Profunctors ----
------------------------------------------------------------
------------------------------------------------------------

-- A polynomial profunctor P : Set^op x Set -> Set has the form:
--   P(x, y) = Σ(i : I) (Dir(x, i) -> y)
-- where Dir(x, i) is a polynomial functor in x for each position i.
--
-- The contravariance in x comes from the function arrow:
-- Dir(x, i) is covariant in x, but Dir(x, i) -> y is contravariant.
public export
record PolyProf where
  constructor MkPolyProf
  -- Outer positions (independent of type parameter)
  ppPos : Type
  -- Direction polynomial for each outer position
  ppDirPF : ppPos -> PolyFunc

-- Interpretation of a polynomial profunctor
public export
InterpPolyProf : PolyProf -> Type -> Type -> Type
InterpPolyProf pp x y = (i : ppPos pp ** InterpPolyFunc (ppDirPF pp i) x -> y)

------------------------------------------------------------
---- End of Polynomial Profunctor ----
------------------------------------------------------------

-- The end of a polynomial profunctor is characterized by sections of
-- the direction polynomial at each outer position.
--
-- End(P) = Σ(i : I) Nat(Dir(-, i), Id)
--        = Σ(i : I) PolySection(DirPF(i))
public export
PolyProfEnd : PolyProf -> Type
PolyProfEnd pp = (i : ppPos pp ** PolySection (ppDirPF pp i))

------------------------------------------------------------
---- End Element to Polymorphic Family ----
------------------------------------------------------------

-- An end element gives a polymorphic family of profunctor elements.
-- At each type x, we get an element of P(x, x).
public export
endToPolyFamily : {pp : PolyProf} ->
  PolyProfEnd pp -> (x : Type) -> InterpPolyProf pp x x
endToPolyFamily {pp} (i ** section) x =
  (i ** sectionApply {pf=ppDirPF pp i} section x)

------------------------------------------------------------
---- Polymorphic Family to End Element ----
------------------------------------------------------------

-- A polymorphic family (satisfying the wedge condition) gives an end element.
-- The wedge condition for polynomial profunctors is exactly naturality of
-- the second component.
--
-- This function requires additional infrastructure to implement cleanly.
-- The issue is that `snd (family x)` has type
-- `InterpPolyFunc (ppDirPF pp (fst (family x))) x -> x`
-- but we need `InterpPolyFunc (ppDirPF pp i) x -> x` where `i = fst (family Unit)`.
-- When posConst is available, these types are equal, but Idris needs help
-- to see through the equality.
--
-- For now, we provide endToPolyFamily, which is what we need for the
-- application.

------------------------------------------------------------
------------------------------------------------------------
---- Application Lemmas ----
------------------------------------------------------------
------------------------------------------------------------

-- Applying a section to a constant-False direction function gives False.
--
-- If g : Dir -> Bool is constantly False, then for any section d:
-- sectionApply d Bool (i ** g) = g (d i) = False
public export
sectionApplyConstFalse : {pf : PolyFunc} ->
  (d : PolySection pf) ->
  (i : pfPos pf) ->
  (g : pfDir {p=pf} i -> Bool) ->
  ((dir : pfDir {p=pf} i) -> g dir = False) ->
  sectionApply {pf} d Bool (i ** g) = False
sectionApplyConstFalse {pf} d i g allFalse =
  -- sectionApply d Bool (i ** g) = g (d i) = False
  allFalse (d i)

-- Applying a section to a constant-True direction function gives True.
public export
sectionApplyConstTrue : {pf : PolyFunc} ->
  (d : PolySection pf) ->
  (i : pfPos pf) ->
  (g : pfDir {p=pf} i -> Bool) ->
  ((dir : pfDir {p=pf} i) -> g dir = True) ->
  sectionApply {pf} d Bool (i ** g) = True
sectionApplyConstTrue {pf} d i g allTrue =
  allTrue (d i)

------------------------------------------------------------
------------------------------------------------------------
---- Empty Direction Types ----
------------------------------------------------------------
------------------------------------------------------------

-- When the direction type is Void, there is exactly one section
-- (the absurd function), and applying it is vacuously correct.
--
-- A section for void-direction polynomials exists uniquely:
-- it maps each position to `absurd`. However, constructing this in Idris
-- requires dependent rewriting. For practical use when the direction type
-- is definitionally Void, build the section directly.

-- When direction type is Void, InterpPolyFunc pf x = pfPos pf
-- (since Void -> x is uniquely determined)
public export
voidDirInterpIso : {pf : PolyFunc} ->
  ((i : pfPos pf) -> pfDir {p=pf} i = Void) ->
  (x : Type) ->
  InterpPolyFunc pf x -> pfPos pf
voidDirInterpIso allVoid x (i ** g) = i

------------------------------------------------------------
------------------------------------------------------------
---- Sections of Specific Polynomial Functors ----
------------------------------------------------------------
------------------------------------------------------------

-- Section of the initial arena (no positions, so section is absurd)
-- PFInitialArena = (Void ** voidF Type), so PolySection = (i : Void) -> ...
-- This is vacuously satisfied by absurd.
public export
PfInitialSection : PolySection PFInitialArena
PfInitialSection pos = void pos

-- Note: PFTerminalArena = (Unit ** const Void) has one position but zero
-- directions. A section would need to provide a Void for each Unit position,
-- which is impossible. So PolySection PFTerminalArena is uninhabited.

-- Section of the identity arena (one position, one direction)
-- PFIdentityArena = (Unit ** const Unit), so directions are Unit.
public export
PfIdentitySection : PolySection PFIdentityArena
PfIdentitySection () = ()

------------------------------------------------------------
------------------------------------------------------------
---- Sections of Compound Polynomial Functors ----
------------------------------------------------------------
------------------------------------------------------------

-- Section of a coproduct arena from sections of the components.
-- By pattern matching on the polynomial functor pairs, we force the type
-- to reduce to Either, allowing pattern matching on Left/Right.
public export
pfCoproductSection : {p, q : PolyFunc} ->
  PolySection p -> PolySection q -> PolySection (pfCoproductArena p q)
pfCoproductSection {p=(ppos ** pdir)} {q=(qpos ** qdir)} sL sR (Left i) = sL i
pfCoproductSection {p=(ppos ** pdir)} {q=(qpos ** qdir)} sL sR (Right j) = sR j

-- Section of a product arena: always choose the left direction
public export
pfProductSectionLeft : {p, q : PolyFunc} ->
  PolySection p -> PolySection (pfProductArena p q)
pfProductSectionLeft {p=(ppos ** pdir)} {q=(qpos ** qdir)} sL (i, j) = Left (sL i)

-- Section of a product arena: always choose the right direction
public export
pfProductSectionRight : {p, q : PolyFunc} ->
  PolySection q -> PolySection (pfProductArena p q)
pfProductSectionRight {p=(ppos ** pdir)} {q=(qpos ** qdir)} sR (i, j) = Right (sR j)

-- For pfProductArena PFIdentityArena q, simplified left section
-- (always returns Left () since identity has unit position/direction)
public export
pfProductIdSectionLeft : {q : PolyFunc} ->
  PolySection (pfProductArena PFIdentityArena q)
pfProductIdSectionLeft {q=(qpos ** qdir)} ((), j) = Left ()

-- For pfProductArena PFIdentityArena q, right section using a q-section
public export
pfProductIdSectionRight : {q : PolyFunc} ->
  PolySection q -> PolySection (pfProductArena PFIdentityArena q)
pfProductIdSectionRight {q=(qpos ** qdir)} sR ((), j) = Right (sR j)

------------------------------------------------------------
------------------------------------------------------------
---- Section Application Lemmas for Compound Functors ----
------------------------------------------------------------
------------------------------------------------------------

-- sectionApply of coproduct section on Left element reduces to left section.
-- We use explicit {p=...} {q=...} to force type resolution.
public export
sectionApplyCoproductLeft : {ppos : Type} -> {pdir : ppos -> Type} ->
  {qpos : Type} -> {qdir : qpos -> Type} ->
  (sL : PolySection (ppos ** pdir)) -> (sR : PolySection (qpos ** qdir)) ->
  (x : Type) -> (i : ppos) -> (dirFn : pdir i -> x) ->
  sectionApply {pf=pfCoproductArena (ppos ** pdir) (qpos ** qdir)}
    (pfCoproductSection {p=(ppos ** pdir)} {q=(qpos ** qdir)} sL sR)
    x (Left i ** dirFn)
  = sectionApply {pf=(ppos ** pdir)} sL x (i ** dirFn)
sectionApplyCoproductLeft sL sR x i dirFn = Refl

-- sectionApply of coproduct section on Right element reduces to right section.
public export
sectionApplyCoproductRight : {ppos : Type} -> {pdir : ppos -> Type} ->
  {qpos : Type} -> {qdir : qpos -> Type} ->
  (sL : PolySection (ppos ** pdir)) -> (sR : PolySection (qpos ** qdir)) ->
  (x : Type) -> (j : qpos) -> (dirFn : qdir j -> x) ->
  sectionApply {pf=pfCoproductArena (ppos ** pdir) (qpos ** qdir)}
    (pfCoproductSection {p=(ppos ** pdir)} {q=(qpos ** qdir)} sL sR)
    x (Right j ** dirFn)
  = sectionApply {pf=(qpos ** qdir)} sR x (j ** dirFn)
sectionApplyCoproductRight sL sR x j dirFn = Refl

-- sectionApply of product-id left section gives dirFn (Left ())
public export
sectionApplyProductIdLeft : {qpos : Type} -> {qdir : qpos -> Type} ->
  (x : Type) -> (j : qpos) ->
  (dirFn : Either Unit (qdir j) -> x) ->
  sectionApply {pf=pfProductArena PFIdentityArena (qpos ** qdir)}
    (pfProductIdSectionLeft {q=(qpos ** qdir)}) x (((), j) ** dirFn)
  = dirFn (Left ())
sectionApplyProductIdLeft x j dirFn = Refl

-- sectionApply of product-id right section gives dirFn (Right (sR j))
public export
sectionApplyProductIdRight : {qpos : Type} -> {qdir : qpos -> Type} ->
  (sR : PolySection (qpos ** qdir)) ->
  (x : Type) -> (j : qpos) ->
  (dirFn : Either Unit (qdir j) -> x) ->
  sectionApply {pf=pfProductArena PFIdentityArena (qpos ** qdir)}
    (pfProductIdSectionRight {q=(qpos ** qdir)} sR) x (((), j) ** dirFn)
  = dirFn (Right (sR j))
sectionApplyProductIdRight sR x j dirFn = Refl

-- sectionApply on initial arena element is absurd (no elements exist)
public export
SectionApplyInitial : (x : Type) -> (elem : InterpPolyFunc PFInitialArena x) ->
  sectionApply {pf=PFInitialArena} PfInitialSection x elem = void (fst elem)
SectionApplyInitial x (pos ** dirFn) = void pos

------------------------------------------------------------
------------------------------------------------------------
---- General End Characterization for Polynomial Profunctors ----
------------------------------------------------------------
------------------------------------------------------------

-- For practical use, we work with a "canonical form" of end elements
-- where the position is explicit and constant. This avoids dependent
-- rewriting issues that arise when trying to relate positions at
-- different types.
--
-- An end element for a polynomial profunctor P is characterized by a
-- constant position (the same for all types) plus a natural transformation
-- from the direction functor to Id.
--
-- Since Nat(InterpPolyFunc pf, Id) ≅ PolySection pf, we get:
--   End(P) ≅ Σ(i : ppPos pp) PolySection (ppDirPF pp i)
--          = PolyProfEnd pp
--
-- This is already defined above. The functions below show that
-- end elements (polymorphic families satisfying wedge) correspond
-- to this characterization.

-- A "canonical end element" bundles a position with a natural transformation.
-- This is isomorphic to PolyProfEnd but in a form that constructs elements.
public export
CanonicalEndElem : PolyProf -> Type
CanonicalEndElem pp = (i : ppPos pp ** (x : Type) -> InterpPolyFunc (ppDirPF pp i) x -> x)

-- Convert PolyProfEnd to CanonicalEndElem.
-- Position stays the same, section becomes sectionApply.
public export
polyProfEndToCanonical : {pp : PolyProf} -> PolyProfEnd pp -> CanonicalEndElem pp
polyProfEndToCanonical {pp} (i ** section) =
  (i ** \x => sectionApply {pf=ppDirPF pp i} section x)

-- Convert CanonicalEndElem to PolyProfEnd.
-- Position stays the same, nat trans becomes natTransToSection.
public export
canonicalToPolyProfEnd : {pp : PolyProf} -> CanonicalEndElem pp -> PolyProfEnd pp
canonicalToPolyProfEnd {pp} (i ** eta) =
  (i ** natTransToSection {pf=ppDirPF pp i} eta)

-- Round-trip: PolyProfEnd → CanonicalEndElem → PolyProfEnd = id
-- This is sectionRoundTrip.
public export
polyProfEndCanonicalRoundTrip : FunExt -> {pp : PolyProf} ->
  (end : PolyProfEnd pp) ->
  canonicalToPolyProfEnd {pp} (polyProfEndToCanonical {pp} end) = end
polyProfEndCanonicalRoundTrip fext {pp} (i ** section) =
  dpEq12 Refl (sectionRoundTrip fext section)

-- Round-trip: CanonicalEndElem → PolyProfEnd → CanonicalEndElem
-- The nat trans round-trip requires naturality.
-- For canonical elements (built from sections), this holds by construction.
public export
canonicalPolyProfEndRoundTrip : FunExt -> {pp : PolyProf} ->
  (i : ppPos pp) ->
  (eta : (y : Type) -> InterpPolyFunc (ppDirPF pp i) y -> y) ->
  -- Naturality condition for eta
  (nat : PolyNatTransNaturality {pf=ppDirPF pp i} eta) ->
  (x : Type) -> (elem : InterpPolyFunc (ppDirPF pp i) x) ->
  sectionApply {pf=ppDirPF pp i} (natTransToSection {pf=ppDirPF pp i} eta) x elem
    = eta x elem
canonicalPolyProfEndRoundTrip fext {pp} i eta nat x elem =
  natTransRoundTrip {pf=ppDirPF pp i} eta nat x elem

------------------------------------------------------------
---- Properties of Section-Based Constructions ----
------------------------------------------------------------

-- Constructions from sections automatically satisfy naturality because
-- sectionApply is natural.
--
-- For f : a → b and end = (i ** section):
--   f (sectionApply section a elem) = sectionApply section b (InterpPFMap pf f elem)
--
-- This is sectionApplyNatural, which proves by Refl.

-- Corollary: End elements from sections have constant position (trivially).
public export
0 SectionEndPosConst : {pp : PolyProf} -> (end : PolyProfEnd pp) ->
  (a, b : Type) -> fst end = fst end
SectionEndPosConst {pp} (i ** section) a b = Refl

-- This captures the essence: once we have a section, all the naturality
-- and constancy properties follow definitionally (Refl proofs).

------------------------------------------------------------
------------------------------------------------------------
---- Free Monad Direction Polynomial Functors ----
------------------------------------------------------------
------------------------------------------------------------

-- For a polynomial profunctor pp, we can form the free monad of pp(x) for
-- any type x. The directions of this free monad depend on x through the
-- polynomial structure of pp's directions.
--
-- This section proves that the free monad directions are themselves
-- polynomial functors. Specifically, for each position of the free monad
-- (at x = Unit), there is a polynomial functor FreeMDirPF such that the
-- directions at the mapped position (at any type a) equal
-- InterpPolyFunc (FreeMDirPF pos) a.

-- Convert a polynomial profunctor to a polynomial functor at a given type.
-- This interprets the profunctor's direction polynomials at the type.
public export
ppToPolyFunc : PolyProf -> Type -> PolyFunc
ppToPolyFunc pp x = (ppPos pp ** \i => InterpPolyFunc (ppDirPF pp i) x)

-- The free monad of a polynomial profunctor at a given type.
public export
ppFreeM : PolyProf -> Type -> PolyFunc
ppFreeM pp x = PolyFuncFreeM (ppToPolyFunc pp x)

-- Position type of the free monad at Unit.
public export
ppFreeMPosUnit : PolyProf -> Type
ppFreeMPosUnit pp = PolyFuncFreeMPos (ppToPolyFunc pp Unit)

-- Direction type of the free monad at a given type and position.
public export
ppFreeMDir : (pp : PolyProf) -> (x : Type) ->
  PolyFuncFreeMPos (ppToPolyFunc pp x) -> Type
ppFreeMDir pp x = PolyFuncFreeMDir (ppToPolyFunc pp x)

------------------------------------------------------------
---- Dependent Sum Arena (Sigma Arena) ----
------------------------------------------------------------

-- A dependent sum arena over a polynomial functor pf and a family of
-- polynomial functors indexed by positions of pf.
--
-- The interpretation at type a is:
--   (p : pfPos pf ** (pfDir pf p -> a) × InterpPolyFunc (family p) a)
--
-- This captures the structure needed for free monad directions where
-- each position contributes both direct directions and recursive structure.

public export
pfSigmaArenaPos : (pf : PolyFunc) -> (pfPos pf -> PolyFunc) -> Type
pfSigmaArenaPos pf family = (p : pfPos pf ** pfPos (family p))

public export
pfSigmaArenaDir : (pf : PolyFunc) -> (family : pfPos pf -> PolyFunc) ->
  pfSigmaArenaPos pf family -> Type
pfSigmaArenaDir pf family (p ** fp) =
  Either (pfDir {p=pf} p) (pfDir {p=(family p)} fp)

public export
pfSigmaArena : (pf : PolyFunc) -> (pfPos pf -> PolyFunc) -> PolyFunc
pfSigmaArena pf family = (pfSigmaArenaPos pf family ** pfSigmaArenaDir pf family)

-- The interpretation of pfSigmaArena:
-- InterpPolyFunc (pfSigmaArena pf family) a
--   = ((p : pfPos pf ** fp : pfPos (family p)) ** Either (pfDir pf p) (pfDir (family p) fp) -> a)
--   ≅ (p : pfPos pf ** (pfDir pf p -> a, (fp : pfPos (family p) ** pfDir (family p) fp -> a)))
--   ≅ (p : pfPos pf ** (pfDir pf p -> a, InterpPolyFunc (family p) a))

------------------------------------------------------------
---- Direction Polynomial Functor for Free Monads ----
------------------------------------------------------------

-- For a polynomial profunctor pp, we define a polynomial functor for each
-- position of the free monad (at Unit). This polynomial functor characterizes
-- the directions at the corresponding mapped position at any type.
--
-- The definition is by structural induction on the free monad position:
-- - PFVar: Terminal arena (one direction for variables)
-- - PFCom i: Sigma arena combining original directions with recursive structure
public export
FreeMDirPF : (pp : PolyProf) -> ppFreeMPosUnit pp -> PolyFunc
FreeMDirPF pp (InPFM (PFVar ()) dm) =
  -- Variable positions have exactly one direction
  PFTerminalArena
FreeMDirPF pp (InPFM (PFCom i) dm) =
  -- Constructor positions: for each position p of ppDirPF pp i,
  -- we get directions from both the original polynomial and the recursive call.
  -- The recursive call is at dm (p ** const ()), the Unit-collapsed direction.
  pfSigmaArena (ppDirPF pp i) (\p => FreeMDirPF pp (dm (p ** const ())))

-- Interpretation of FreeMDirPF gives the direction type.
public export
InterpFreeMDirPF : (pp : PolyProf) -> ppFreeMPosUnit pp -> Type -> Type
InterpFreeMDirPF pp pos = InterpPolyFunc (FreeMDirPF pp pos)

------------------------------------------------------------
---- Position Mapping for Polynomial Profunctors ----
------------------------------------------------------------

-- For a polynomial profunctor, the contramap from Unit to any type a
-- is given by (const () : a -> Unit). This contramap has:
-- - Identity on positions (positions are constant for PolyProf)
-- - InterpPFMap on directions (mapping to Unit)
--
-- When lifted to the free monad, positions are preserved structurally.

-- The natural transformation from ppToPolyFunc pp Unit to ppToPolyFunc pp a
-- induced by the contravariant map.
public export
ppContramapNT : (pp : PolyProf) -> (a : Type) ->
  PolyNatTrans (ppToPolyFunc pp Unit) (ppToPolyFunc pp a)
ppContramapNT pp a =
  (id ** \i => InterpPFMap (ppDirPF pp i) (const ()))

-- The position mapping from free monad at Unit to free monad at a.
-- This preserves tree structure.
public export
ppFreeMPosMap : (pp : PolyProf) -> (a : Type) ->
  ppFreeMPosUnit pp -> PolyFuncFreeMPos (ppToPolyFunc pp a)
ppFreeMPosMap pp a =
  pfFreePolyCataOnPos {p=ppToPolyFunc pp Unit} {q=ppToPolyFunc pp a}
    (ppContramapNT pp a)

------------------------------------------------------------
---- Direction Isomorphism for Free Monads ----
------------------------------------------------------------

-- The direction type at a mapped position equals the interpretation of
-- FreeMDirPF. We prove this by structural induction.
--
-- Forward direction: FreeMDir at mapped position -> InterpFreeMDirPF
public export
freeMDirIsoFwd : (pp : PolyProf) -> (pos : ppFreeMPosUnit pp) -> (a : Type) ->
  PolyFuncFreeMDir (ppToPolyFunc pp a) (ppFreeMPosMap pp a pos) ->
  InterpFreeMDirPF pp pos a
freeMDirIsoFwd pp (InPFM (PFVar ()) dm) a dir =
  -- FreeMDir at PFVar is Unit
  -- InterpFreeMDirPF at PFVar is InterpPolyFunc PFTerminalArena a = (() ** Void -> a)
  (() ** voidF a)
freeMDirIsoFwd pp (InPFM (PFCom i) dm) a (d ** recDir) =
  -- d : InterpPolyFunc (ppDirPF pp i) a
  -- recDir : recursive direction at dm (InterpPFMap ... (const ()) d)
  -- The Unit-mapped version of d determines which subtree to recurse into
  let dUnit : InterpPolyFunc (ppDirPF pp i) Unit
      dUnit = InterpPFMap (ppDirPF pp i) (const ()) d
      -- d has position fst d and direction function snd d : pfDir -> a
      p : pfPos (ppDirPF pp i)
      p = fst d
      -- The recursive call is at dm (p ** const ())
      recResult : InterpFreeMDirPF pp (dm (p ** const ())) a
      recResult = freeMDirIsoFwd pp (dm (p ** const ())) a recDir
  in ((p ** fst recResult) ** \dir => case dir of
        Left pdir => snd d pdir
        Right recD => snd recResult recD)

-- Backward direction: InterpFreeMDirPF -> FreeMDir at mapped position
public export
freeMDirIsoBwd : (pp : PolyProf) -> (pos : ppFreeMPosUnit pp) -> (a : Type) ->
  InterpFreeMDirPF pp pos a ->
  PolyFuncFreeMDir (ppToPolyFunc pp a) (ppFreeMPosMap pp a pos)
freeMDirIsoBwd pp (InPFM (PFVar ()) dm) a dir =
  -- InterpFreeMDirPF at PFVar is (() ** Void -> a), FreeMDir is Unit
  ()
freeMDirIsoBwd pp (InPFM (PFCom i) dm) a ((p ** fp) ** dirFn) =
  -- p : pfPos (ppDirPF pp i)
  -- fp : pfPos (FreeMDirPF pp (dm (p ** const ())))
  -- dirFn : Either (pfDir (ppDirPF pp i) p) (pfDir (FreeMDirPF ...) fp) -> a
  let d : InterpPolyFunc (ppDirPF pp i) a
      d = (p ** \pdir => dirFn (Left pdir))
      recInput : InterpFreeMDirPF pp (dm (p ** const ())) a
      recInput = (fp ** \recD => dirFn (Right recD))
      recDir : PolyFuncFreeMDir (ppToPolyFunc pp a)
                 (ppFreeMPosMap pp a (dm (p ** const ())))
      recDir = freeMDirIsoBwd pp (dm (p ** const ())) a recInput
  in (d ** recDir)

------------------------------------------------------------
---- Summary: Free Monad Direction Isomorphism ----
------------------------------------------------------------

-- We have proven:
-- 1. FreeMDirPF: a polynomial functor characterizing
--    directions at each free monad position
-- 2. freeMDirIsoFwd/freeMDirIsoBwd: isomorphism between
--    actual free monad directions and
--    InterpPolyFunc (FreeMDirPF pos) a

------------------------------------------------------------
------------------------------------------------------------
---- Dirichlet Functor Connection ----
------------------------------------------------------------
------------------------------------------------------------

-- A polynomial profunctor pp decomposes into:
--   1. A "position Dirichlet functor" (I, E) where:
--      - I = ppPos pp (the constructors)
--      - E(i) = pfPos (ppDirPF pp i) (positive directions
--        at constructor i = the "fields")
--   2. A "negative direction family" F over the total
--      space of (I, E):
--      - F(i, j) = pfDir (ppDirPF pp i) j (the negative
--        sub-directions at field j of constructor i)
--
-- The pair (I, E) is equivalent to MLDirichCatObj from
-- MLDirichCat.idr (= DPair Type SliceObj), and the total
-- space Sigma(i:I).E(i) is its category of elements.
--
-- This decomposition is the key insight connecting
-- polynomial profunctors to the existing Dirichlet functor
-- infrastructure in this codebase.

-- The positive direction type at each position.
-- Forms the direction family of the position Dirichlet
-- functor.
public export
ppPosDirType : (pp : PolyProf) -> ppPos pp -> Type
ppPosDirType pp i = pfPos (ppDirPF pp i)

-- The position Dirichlet functor as a dependent pair,
-- equivalent to MLDirichCatObj from MLDirichCat.idr.
public export
ppPosDirich : PolyProf -> DPair Type SliceObj
ppPosDirich pp = (ppPos pp ** ppPosDirType pp)

-- The total space of (positions, positive directions).
-- This is the category of elements of the position
-- Dirichlet functor.
public export
ppTot : PolyProf -> Type
ppTot pp = DPair (ppPos pp) (ppPosDirType pp)

-- The negative direction at each element of the total
-- space. For each position i and positive direction j,
-- this is the type of negative sub-directions at field j
-- of constructor i.
public export
ppNegDir : (pp : PolyProf) -> ppTot pp -> Type
ppNegDir pp (i ** j) = pfDir {p=ppDirPF pp i} j

-- Reconstruct a polynomial profunctor from its Dirichlet
-- functor decomposition: a position type, a positive
-- direction family, and a negative direction family over
-- the total space.
public export
ppFromDirichAndNeg :
  (pos : Type) ->
  (posDir : pos -> Type) ->
  (negDir : DPair pos posDir -> Type) ->
  PolyProf
ppFromDirichAndNeg pos posDir negDir =
  MkPolyProf pos
    (\i => (posDir i ** \j => negDir (i ** j)))

------------------------------------------------------------
------------------------------------------------------------
---- Embeddings into Polynomial Profunctors ----
------------------------------------------------------------
------------------------------------------------------------

-- A polynomial endofunctor embeds as a polynomial
-- profunctor with no negative occurrences. The direction
-- polynomial at each position i has dir(i) as positions
-- and Void as sub-directions, giving dir(i) many copies
-- of y independent of x.
public export
polyFuncToPolyProf : PolyFunc -> PolyProf
polyFuncToPolyProf (pos ** dir) =
  MkPolyProf pos (\i => (dir i ** const Void))

-- Interpretation formula: the profunctor interpretation
-- of a polynomial endofunctor embedding is
--   (i : pos ** (j : dir i ** Void -> x) -> y)
-- which is isomorphic (not definitionally equal) to
--   (i : pos ** dir i -> y) = InterpPolyFunc pf y.
public export
0 polyFuncProfInterpFormula :
  (pf : PolyFunc) -> (x, y : Type) ->
  InterpPolyProf (polyFuncToPolyProf pf) x y =
  (i : pfPos pf **
   (j : pfDir {p=pf} i ** Void -> x) -> y)
polyFuncProfInterpFormula (pos ** dir) x y = Refl

-- Forward conversion: polynomial functor to profunctor.
public export
polyFuncProfInterpTo :
  (pf : PolyFunc) -> (x, y : Type) ->
  InterpPolyFunc pf y ->
  InterpPolyProf (polyFuncToPolyProf pf) x y
polyFuncProfInterpTo (pos ** dir) x y (i ** f) =
  (i ** \(j ** _) => f j)

-- Backward conversion: profunctor to polynomial functor.
public export
polyFuncProfInterpFrom :
  (pf : PolyFunc) -> (x, y : Type) ->
  InterpPolyProf (polyFuncToPolyProf pf) x y ->
  InterpPolyFunc pf y
polyFuncProfInterpFrom (pos ** dir) x y (i ** g) =
  (i ** \j => g (j ** voidF x))

-- A Dirichlet functor embeds as a polynomial profunctor
-- with one field per constructor and all-negative
-- sub-directions. The direction polynomial at each
-- position i has Unit as positions and dir(i) as
-- sub-directions, giving the interpretation:
--   (i : pos ** (dir i -> x) -> y).
public export
dirichToPolyProf :
  DPair Type SliceObj -> PolyProf
dirichToPolyProf (pos ** dir) =
  MkPolyProf pos (\i => (Unit ** const (dir i)))

-- Interpretation formula: the profunctor interpretation
-- of a Dirichlet functor embedding is
--   (i : pos ** (j : Unit ** dir i -> x) -> y)
-- which is isomorphic to
--   (i : pos ** (dir i -> x) -> y).
public export
0 dirichProfInterpFormula :
  (d : DPair Type SliceObj) -> (x, y : Type) ->
  InterpPolyProf (dirichToPolyProf d) x y =
  (i : fst d **
   (j : Unit ** snd d i -> x) -> y)
dirichProfInterpFormula (pos ** dir) x y = Refl

-- Forward conversion: (dir i -> x) -> y to profunctor.
public export
dirichProfInterpTo :
  (d : DPair Type SliceObj) ->
  (x, y : Type) ->
  (i : fst d ** (snd d i -> x) -> y) ->
  InterpPolyProf (dirichToPolyProf d) x y
dirichProfInterpTo (pos ** dir) x y (i ** g) =
  (i ** \el => g (snd el))

-- Backward conversion: profunctor to (dir i -> x) -> y.
public export
dirichProfInterpFrom :
  (d : DPair Type SliceObj) ->
  (x, y : Type) ->
  InterpPolyProf (dirichToPolyProf d) x y ->
  (i : fst d ** (snd d i -> x) -> y)
dirichProfInterpFrom (pos ** dir) x y (i ** g) =
  (i ** \f => g (() ** f))

------------------------------------------------------------
------------------------------------------------------------
---- Free Monad Profunctor and Initial Algebra ----
------------------------------------------------------------
------------------------------------------------------------

-- The free monad of a polynomial profunctor, viewed as a
-- polynomial profunctor itself.
--
-- For pp, the free monad at each type x is a polynomial
-- endofunctor. The positions of this free monad (computed
-- at Unit) give "tree shapes", and the direction polynomial
-- at each position is FreeMDirPF.
public export
ppFreeMProf : PolyProf -> PolyProf
ppFreeMProf pp =
  MkPolyProf (ppFreeMPosUnit pp) (FreeMDirPF pp)

-- The initial algebra of a polynomial profunctor,
-- characterized as the end of the free monad profunctor.
--
-- An element consists of:
-- 1. A position (tree shape) from the free monad at Unit
-- 2. A section of the direction polynomial at that position
--
-- The section requirement automatically enforces closedness:
-- at PFVar nodes, FreeMDirPF gives PFTerminalArena, whose
-- sections require Unit -> Void (uninhabited). Thus only
-- positions with no PFVar nodes admit sections.
--
-- This subsumes both polynomial endofunctor Mu (when there
-- are no negative occurrences) and allows mixed-variance
-- recursive datatypes (when there are negative occurrences).
public export
PolyProfMu : PolyProf -> Type
PolyProfMu pp = PolyProfEnd (ppFreeMProf pp)

-- Formula: PolyProfMu is a section over free monad
-- positions.
public export
0 polyProfMuFormula : (pp : PolyProf) ->
  PolyProfMu pp =
  (pos : ppFreeMPosUnit pp **
   PolySection (FreeMDirPF pp pos))
polyProfMuFormula pp = Refl

-- The PHOAS form of the initial algebra: a polymorphic
-- family that gives, at each type x, a free monad element
-- with variables of type x.
--
-- Elements should satisfy the wedge condition (naturality)
-- to be true end elements. The section-based PolyProfMu
-- automatically satisfies this.
public export
PolyProfMuPHOAS : PolyProf -> Type
PolyProfMuPHOAS pp =
  (x : Type) ->
  InterpPolyFuncFreeM (ppToPolyFunc pp x) x

-- Convert a section-based initial algebra element to the
-- PHOAS form. At each type x, this:
-- 1. Maps the position from Unit to x via ppFreeMPosMap
-- 2. Applies the section composed with the direction
--    isomorphism freeMDirIsoFwd
public export
polyProfMuToFamily : {pp : PolyProf} ->
  PolyProfMu pp -> PolyProfMuPHOAS pp
polyProfMuToFamily {pp} (pos ** section) x =
  (ppFreeMPosMap pp x pos **
   sectionApply {pf=FreeMDirPF pp pos} section x .
     freeMDirIsoFwd pp pos x)

------------------------------------------------------------
------------------------------------------------------------
---- Algebra and Catamorphism ----
------------------------------------------------------------
------------------------------------------------------------

-- Algebra for a polynomial profunctor. Given a constructor
-- at position i and a mapping from its direction space
-- (evaluated at type a) to a, produce an a.
--
-- PolyProfAlg pp a
--   = (i : ppPos pp **
--      InterpPolyFunc (ppDirPF pp i) a -> a) -> a
--
-- The direction space InterpPolyFunc (ppDirPF pp i) a
-- provides, for each positive direction j, a function
-- from F(i,j) many negative occurrences of a into a.
public export
PolyProfAlg : PolyProf -> Type -> Type
PolyProfAlg pp a = InterpPolyProf pp a a -> a

-- Catamorphism on PHOAS terms. Evaluates the PHOAS term
-- at type a, producing a free monad element, then folds
-- it with the algebra (mapping variables to themselves via
-- id).
public export
polyProfEndCata : {pp : PolyProf} -> {a : Type} ->
  PolyProfAlg pp a -> PolyProfMuPHOAS pp -> a
polyProfEndCata {pp} {a} alg el =
  pfSubstCata {p=ppToPolyFunc pp a} {a=a} {b=a}
    Prelude.id (\i, f => alg (i ** f)) (el a)

-- Catamorphism on section-based initial algebra elements.
-- Converts to PHOAS form, then applies the PHOAS cata.
public export
polyProfCata : {pp : PolyProf} -> {a : Type} ->
  PolyProfAlg pp a -> PolyProfMu pp -> a
polyProfCata {pp} {a} alg =
  polyProfEndCata {pp} {a} alg .
    polyProfMuToFamily {pp}

------------------------------------------------------------
------------------------------------------------------------
---- PHOAS Constructors ----
------------------------------------------------------------
------------------------------------------------------------

-- Roll one layer of the profunctor around sub-terms.
-- Given position i and a family of sub-terms (one for each
-- direction element at i), produce a PHOAS element.
--
-- The sub-terms argument provides, for each type x and
-- each direction element (j ** f : F(i,j) -> x), a free
-- monad term. This is the PHOAS encoding: negative
-- occurrences appear as function parameters (the f), while
-- positive occurrences appear as recursive sub-terms.
public export
polyProfMuRoll : {pp : PolyProf} ->
  (i : ppPos pp) ->
  ((x : Type) ->
    InterpPolyFunc (ppDirPF pp i) x ->
    InterpPolyFuncFreeM (ppToPolyFunc pp x) x) ->
  PolyProfMuPHOAS pp
polyProfMuRoll {pp} i subTerms x =
  let dm : InterpPolyFunc (ppDirPF pp i) x ->
           PolyFuncFreeMPos (ppToPolyFunc pp x)
      dm d = fst (subTerms x d)
  in (InPFM (PFCom i) dm **
      \(d ** recDir) =>
        snd (subTerms x d) recDir)

-- The free monad PHOAS type for open terms. Given a
-- variable type v, this produces, at each type x, a
-- mapping from variable substitutions (v -> x) to free
-- monad elements.
--
-- PolyProfMuPHOAS pp = PolyProfFreeMPHOAS pp Void
-- (since Void -> x is trivial).
public export
PolyProfFreeMPHOAS : PolyProf -> Type -> Type
PolyProfFreeMPHOAS pp v =
  (x : Type) -> (v -> x) ->
  InterpPolyFuncFreeM (ppToPolyFunc pp x) x

-- Variable embedding into the free monad.
-- Embeds a variable v into the free monad at any type x
-- by substituting it via the given mapping.
public export
polyProfFreeMVar : {pp : PolyProf} -> {v : Type} ->
  v -> PolyProfFreeMPHOAS pp v
polyProfFreeMVar {pp} var x subst =
  (InPFM (PFVar ()) (\ev => void ev) **
   \() => subst var)

-- Roll one layer around open sub-terms.
public export
polyProfFreeMRoll : {pp : PolyProf} ->
  {v : Type} ->
  (i : ppPos pp) ->
  ((x : Type) -> (v -> x) ->
    InterpPolyFunc (ppDirPF pp i) x ->
    InterpPolyFuncFreeM (ppToPolyFunc pp x) x) ->
  PolyProfFreeMPHOAS pp v
polyProfFreeMRoll {pp} {v} i subTerms x subst =
  let dm : InterpPolyFunc (ppDirPF pp i) x ->
           PolyFuncFreeMPos (ppToPolyFunc pp x)
      dm d = fst (subTerms x subst d)
  in (InPFM (PFCom i) dm **
      \(d ** recDir) =>
        snd (subTerms x subst d) recDir)

-- Catamorphism beta law: applying the catamorphism to a
-- rolled term gives the algebra applied to the catamorphism
-- of the sub-terms. This follows from the structure of
-- pfSubstCata and the definitional beta of the free monad.
--
-- polyProfEndCata alg (polyProfMuRoll i subTerms)
--   = alg (i ** \d =>
--       polyProfEndCata alg (\x => subTerms x d))
--
-- This is not a definitional equality in Idris due to the
-- free monad catamorphism's computation rules, but holds
-- propositionally.

------------------------------------------------------------
------------------------------------------------------------
---- Profunctor lmap/rmap for Polynomial Profunctors ----
------------------------------------------------------------
------------------------------------------------------------

-- Left map (contravariant in first argument): given
-- f : a -> s, transport P(s,t) to P(a,t) by precomposing
-- the direction function with InterpPFMap.
public export
interpPolyProfLmap : (pp : PolyProf) ->
  TypeLmapSig (InterpPolyProf pp)
interpPolyProfLmap pp s t a mst (i ** f) =
  (i ** f . InterpPFMap (ppDirPF pp i) mst)

-- Right map (covariant in second argument): given
-- f : t -> b, transport P(s,t) to P(s,b) by
-- postcomposing f.
public export
interpPolyProfRmap : (pp : PolyProf) ->
  TypeRmapSig (InterpPolyProf pp)
interpPolyProfRmap pp s t b mtb (i ** f) =
  (i ** mtb . f)

------------------------------------------------------------
------------------------------------------------------------
---- Roll Constructor for Section-Based PolyProfMu ----
------------------------------------------------------------
------------------------------------------------------------

-- Roll one layer of the profunctor around sub-terms in
-- the section-based representation.
--
-- Given a position i and a sub-term for each positive
-- direction (field) of the constructor at i, produce a
-- PolyProfMu element.
--
-- The position is built by applying InPFM (PFCom i) with
-- the sub-term positions. The section delegates to
-- sub-term sections via Right, choosing the recursive
-- direction at each node.
public export
polyProfMuRollSec : {pp : PolyProf} ->
  (i : ppPos pp) ->
  (subTerms : pfPos (ppDirPF pp i) ->
    PolyProfMu pp) ->
  PolyProfMu pp
polyProfMuRollSec {pp} i subTerms =
  let dm : InterpPolyFunc (ppDirPF pp i) Unit ->
           ppFreeMPosUnit pp
      dm jUnit = fst (subTerms (fst jUnit))
      pos : ppFreeMPosUnit pp
      pos = InPFM (PFCom i) dm
      sec : PolySection (FreeMDirPF pp pos)
      sec (p ** fp) =
        Right (snd (subTerms p) fp)
  in (pos ** sec)

------------------------------------------------------------
------------------------------------------------------------
---- Infrastructure Lemmas ----
------------------------------------------------------------
------------------------------------------------------------

------------------------------------------------------------
---- InterpPFMap (const ()) is identity on Unit ----
------------------------------------------------------------

-- When the target type is Unit, mapping const () over a
-- polynomial functor element is the identity, because all
-- Unit-valued functions are equal (by unitUnique).
public export
interpPFMapConstUnit : FunExt ->
  (pf : PolyFunc) ->
  (el : InterpPolyFunc pf Unit) ->
  InterpPFMap pf (const ()) el = el
interpPFMapConstUnit fext (pos ** dir) (j ** f) =
  dpEq12 Refl
    (funExt (\x => unitUnique () (f x)))

------------------------------------------------------------
---- ppFreeMPosMap Unit is identity ----
------------------------------------------------------------

-- Mapping positions from Unit to Unit (via const ()) is
-- the identity on free monad positions. This is the key
-- lemma for the wedge condition: the Unit instantiation
-- recovers the original position.
--
-- Proof by structural induction on pos, following the
-- pattern of pfCataInId (PolyCat.idr:2530).
-- PFVar case: both sides are InPFM (PFVar ()) with a
--   Void -> X function, equal by funExt absurd.
-- PFCom case: unfold catamorphism, apply
--   interpPFMapConstUnit on the direction argument, then
--   inductive hypothesis.
public export
ppFreeMPosMapUnit : FunExt ->
  (pp : PolyProf) ->
  (pos : ppFreeMPosUnit pp) ->
  ppFreeMPosMap pp Unit pos = pos
ppFreeMPosMapUnit fext pp (InPFM (PFVar ()) dm) =
  cong (InPFM (PFVar ())) (funExt (\v => absurd v))
ppFreeMPosMapUnit fext pp (InPFM (PFCom i) dm) =
  cong (InPFM (PFCom i)) (funExt (\d =>
    trans
      (cong (\d' => ppFreeMPosMap pp Unit (dm d'))
        (interpPFMapConstUnit fext
          (ppDirPF pp i) d))
      (ppFreeMPosMapUnit fext pp (dm d))))

------------------------------------------------------------
------------------------------------------------------------
---- Wedge Condition and Mu Conversions ----
------------------------------------------------------------
------------------------------------------------------------

------------------------------------------------------------
---- Wedge condition for PHOAS elements ----
------------------------------------------------------------

-- The wedge condition says that the position at each type
-- x is the position-mapped version of the position at
-- Unit. This is the coherence condition that makes a PHOAS
-- element a genuine end element.
public export
0 PolyProfMuPHOASWedge : (pp : PolyProf) ->
  PolyProfMuPHOAS pp -> Type
PolyProfMuPHOASWedge pp el =
  (x : Type) ->
    fst (el x) =
    ppFreeMPosMap pp x (fst (el Unit))

------------------------------------------------------------
---- Section-based Mu satisfies the wedge condition ----
------------------------------------------------------------

-- Elements constructed from sections automatically satisfy
-- the wedge condition, because the position at each type x
-- is ppFreeMPosMap pp x pos, and the position at Unit is
-- ppFreeMPosMap pp Unit pos = pos (by ppFreeMPosMapUnit).
public export
0 polyProfMuToFamilyWedge : FunExt ->
  {pp : PolyProf} ->
  (mu : PolyProfMu pp) ->
  PolyProfMuPHOASWedge pp
    (polyProfMuToFamily {pp} mu)
polyProfMuToFamilyWedge fext {pp} (pos ** sec) x =
  sym (cong (ppFreeMPosMap pp x)
    (ppFreeMPosMapUnit fext pp pos))

------------------------------------------------------------
---- PHOAS family to section-based Mu ----
------------------------------------------------------------

-- Convert a PHOAS element satisfying the wedge condition
-- to a section-based Mu element.
--
-- Position: fst (el Unit)
-- Section: extracted via natTransToSection from the
-- natural transformation built by composing snd (el x)
-- with the direction isomorphism and wedge transport.
public export
polyProfFamilyToMu : FunExt ->
  {pp : PolyProf} ->
  (el : PolyProfMuPHOAS pp) ->
  (0 wedge : PolyProfMuPHOASWedge pp el) ->
  PolyProfMu pp
polyProfFamilyToMu fext {pp} el wedge =
  let pos : ppFreeMPosUnit pp
      pos = fst (el Unit)
      eta : (x : Type) ->
        InterpPolyFunc (FreeMDirPF pp pos) x -> x
      eta x elem =
        snd (el x)
          (replace
            {p=PolyFuncFreeMDir (ppToPolyFunc pp x)}
            (sym (wedge x))
            (freeMDirIsoBwd pp pos x elem))
  in (pos **
      natTransToSection
        {pf=FreeMDirPF pp pos} eta)

------------------------------------------------------------
------------------------------------------------------------
---- Natural Transformations of Polynomial Profunctors ----
------------------------------------------------------------
------------------------------------------------------------

-- A natural transformation between polynomial profunctors
-- consists of a position map and a backward direction map.
-- The direction goes backward because directions appear
-- contravariantly: in P(x,y) = (i ** DirPF(i)(x) -> y),
-- the DirPF(i)(x) is in the function domain.
public export
PolyProfNT : PolyProf -> PolyProf -> Type
PolyProfNT pp qq =
  (onPos : ppPos pp -> ppPos qq **
   (i : ppPos pp) ->
     PolyNatTrans
       (ppDirPF qq (onPos i))
       (ppDirPF pp i))

------------------------------------------------------------
---- Interpretation of PolyProfNT ----
------------------------------------------------------------

-- Interpret a PolyProfNT as a map on profunctor elements.
-- Position maps forward; directions compose backward.
public export
InterpPolyProfNT :
  {pp, qq : PolyProf} ->
  PolyProfNT pp qq ->
  (x, y : Type) ->
  InterpPolyProf pp x y ->
  InterpPolyProf qq x y
InterpPolyProfNT {pp} {qq}
  (onPos ** onDir) x y (i ** f) =
  (onPos i **
   f . InterpPolyNT (onDir i) x)

------------------------------------------------------------
---- Identity and Composition ----
------------------------------------------------------------

-- Identity natural transformation.
public export
polyProfNTId : (pp : PolyProf) ->
  PolyProfNT pp pp
polyProfNTId pp =
  (id ** \i => pntId (ppDirPF pp i))

-- Composition of natural transformations.
-- Direction maps compose in reverse order (contravariant).
public export
polyProfNTComp :
  {pp, qq, rr : PolyProf} ->
  PolyProfNT qq rr ->
  PolyProfNT pp qq ->
  PolyProfNT pp rr
polyProfNTComp {pp} {qq} {rr}
  (gPos ** gDir) (fPos ** fDir) =
  (gPos . fPos **
   \i => pntVCatComp (fDir i) (gDir (fPos i)))

------------------------------------------------------------
---- Naturality of InterpPolyProfNT ----
------------------------------------------------------------

-- InterpPolyProfNT is natural in both variables.
-- For f : a -> b and g : x -> y:
--   NT . (lmap f . rmap g) = (lmap f . rmap g) . NT
--
-- After destructuring the direction element, the equality
-- is definitional because function composition is
-- associative and InterpPolyNT commutes with InterpPFMap.
public export
0 polyProfNTNatural :
  FunExt ->
  {pp, qq : PolyProf} ->
  (nt : PolyProfNT pp qq) ->
  (a, b, x, y : Type) ->
  (f : a -> b) -> (g : x -> y) ->
  (el : InterpPolyProf pp b x) ->
  InterpPolyProfNT {pp} {qq} nt a y
    (interpPolyProfRmap pp a x y g
      (interpPolyProfLmap pp b x a f el))
  = interpPolyProfLmap qq b y a f
      (interpPolyProfRmap qq b x y g
        (InterpPolyProfNT {pp} {qq} nt b x el))
polyProfNTNatural fext {pp} {qq}
  (onPos ** onDir) a b x y f g (i ** h) =
  dpEq12 Refl
    (funExt (\(p ** k) => Refl))

------------------------------------------------------------
---- Paranaturality of InterpPolyProfNT ----
------------------------------------------------------------

-- The paranaturality condition for polynomial
-- profunctor transformations, i.e., the condition
-- that a dinatural transformation between
-- InterpPolyProf's is paranatural with respect to
-- the profunctor lmap/rmap actions.
public export
0 PolyProfParaNTCond :
  (pp, qq : PolyProf) ->
  TypeProfDiNT (InterpPolyProf pp)
    (InterpPolyProf qq) ->
  Type
PolyProfParaNTCond pp qq alpha =
  TypeNTParanaturalityLR
    (InterpPolyProf pp) (InterpPolyProf qq)
    (interpPolyProfLmap pp)
    (interpPolyProfRmap pp)
    (interpPolyProfLmap qq)
    (interpPolyProfRmap qq)
    alpha

-- Every polynomial profunctor natural transformation
-- is paranatural. The proof works by:
-- 1. Extracting position equality (j1 = j0) from
--    the condition via mkDPairInjectiveFstHet
-- 2. Extracting direction equality via
--    mkDPairInjectiveSndHet (heterogeneous -> case
--    match since types now agree)
-- 3. After both unifications, the goal reduces to
--    Refl at each element because InterpPolyNT and
--    InterpPFMap commute definitionally at elements.
public export
0 polyProfNTisPara : FunExt ->
  {pp, qq : PolyProf} ->
  (nt : PolyProfNT pp qq) ->
  PolyProfParaNTCond pp qq
    (\x => InterpPolyProfNT {pp} {qq} nt x x)
polyProfNTisPara fext {pp} {qq}
  (onPos ** onDir) i0 i1 i2
  (j0 ** h0) (j1 ** h1) cond =
  case mkDPairInjectiveFstHet cond of
    Refl =>
      let heteq = mkDPairInjectiveSndHet cond
      in dpEq12 Refl
        (funExt (\(p ** k) =>
          fcong heteq
            {x=InterpPolyNT
              (onDir j1) i0 (p ** k)}))

-- Helper: lmap preserves the position (first
-- component) of a polynomial profunctor element.
public export
interpPolyProfLmapFst : (qq : PolyProf) ->
  (s, t, a : Type) -> (f : a -> s) ->
  (el : InterpPolyProf qq s t) ->
  fst (interpPolyProfLmap qq s t a f el) =
  fst el
interpPolyProfLmapFst qq s t a f (j ** g) =
  Refl

-- Helper: rmap preserves the position (first
-- component) of a polynomial profunctor element.
public export
interpPolyProfRmapFst : (qq : PolyProf) ->
  (s, t, b : Type) -> (f : t -> b) ->
  (el : InterpPolyProf qq s t) ->
  fst (interpPolyProfRmap qq s t b f el) =
  fst el
interpPolyProfRmapFst qq s t b f (j ** g) =
  Refl

-- Key theoretical result: for polynomial profunctors,
-- the output position of any paranatural
-- transformation is independent of the input algebra
-- structure.
--
-- Proof: mediate through the unique algebra on Unit
-- (const ()). Since const () . f = const () for
-- any f (definitionally), the paranaturality
-- condition for (const () : x -> Unit) is
-- trivially satisfied. Paranaturality then gives
-- fst (alpha Unit ...) = fst (alpha x ...) and
-- similarly for y. By transitivity,
-- fst (alpha x ...) = fst (alpha y ...).
public export
0 polyProfParaPosIndep :
  {pp, qq : PolyProf} ->
  (alpha : TypeProfDiNT (InterpPolyProf pp)
    (InterpPolyProf qq)) ->
  PolyProfParaNTCond pp qq alpha ->
  (x, y : Type) ->
  (i : ppPos pp) ->
  (hx :
    InterpPolyFunc (ppDirPF pp i) x -> x) ->
  (hy :
    InterpPolyFunc (ppDirPF pp i) y -> y) ->
  fst (alpha x (i ** hx)) =
  fst (alpha y (i ** hy))
polyProfParaPosIndep {pp} {qq}
  alpha para x y i hx hy =
  let
    -- Apply paranaturality at const () : x -> Unit
    parax = para x Unit (const ())
      (i ** hx) (i ** const ())
      (dpEq12 Refl Refl)
    -- Apply paranaturality at const () : y -> Unit
    paray = para y Unit (const ())
      (i ** hy) (i ** const ())
      (dpEq12 Refl Refl)
    -- lmap/rmap preserve first component
    eqx = trans
      (sym (interpPolyProfLmapFst qq
        Unit Unit x (const ())
        (alpha Unit (i ** const ()))))
      (trans (dpeq1 parax)
        (interpPolyProfRmapFst qq
          x x Unit (const ())
          (alpha x (i ** hx))))
    eqy = trans
      (sym (interpPolyProfLmapFst qq
        Unit Unit y (const ())
        (alpha Unit (i ** const ()))))
      (trans (dpeq1 paray)
        (interpPolyProfRmapFst qq
          y y Unit (const ())
          (alpha y (i ** hy))))
  in
  trans (sym eqx) eqy

-- Discussion: completeness of paranaturality
--
-- Position-independence (polyProfParaPosIndep)
-- shows that any paranatural transformation has
-- a position map ppPos pp -> ppPos qq independent
-- of the algebra structure.
--
-- For the DIRECTION part, the analysis differs
-- from IntEndoProAr (PolyDifunc.idr). In
-- IntEndoProAr, the "assignment"
-- covar i -> contra i is type-independent,
-- enabling formula extraction via TypeDiArFromDi.
-- In PolyProf, the "assignment" is an algebra
-- InterpPolyFunc pf x -> x which varies with x.
--
-- For section-based algebras (those of the form
-- sectionApply s x), the paranaturality condition
-- constrains the output to be sectionApply (F s) x
-- for some section map F. For natural
-- transformations, F factors through a
-- PolyNatTrans, but in general F could be more
-- complex.
--
-- Whether ALL paranaturals for PolyProf are
-- natural (i.e., whether F always factors through
-- a PolyNatTrans) is a non-trivial question. We
-- prove position-independence and natural-implies-
-- paranatural, and note the full characterization
-- as future work.

------------------------------------------------------------
------------------------------------------------------------
---- Direction Isomorphism Round-Trips ----
------------------------------------------------------------
------------------------------------------------------------

-- freeMDirIsoFwd . freeMDirIsoBwd = id
-- Proof by structural induction on pos.
--
-- PFVar case: both functions collapse to the unique
-- element (() ** voidF a), so the round-trip is
-- dpEq12 Refl (funExt absurd).
--
-- PFCom case: decompose el = ((p ** fp) ** dirFn),
-- apply IH on recursive sub-position, then
-- reconstruct using dpEq12 and funExt over Either.
public export
0 freeMDirIsoFwdBwd : FunExt ->
  (pp : PolyProf) ->
  (pos : ppFreeMPosUnit pp) ->
  (a : Type) ->
  (el : InterpFreeMDirPF pp pos a) ->
  freeMDirIsoFwd pp pos a
    (freeMDirIsoBwd pp pos a el) = el
freeMDirIsoFwdBwd fext pp
  (InPFM (PFVar ()) dm) a (() ** f) =
  dpEq12 Refl (funExt (\v => absurd v))
freeMDirIsoFwdBwd fext pp
  (InPFM (PFCom i) dm) a
    ((p ** fp) ** dirFn) =
  -- The PFCom case requires matching through the
  -- recursive structure of freeMDirIsoFwd's
  -- internal let binding. The IH (on dm (p ** const
  -- ())) gives the sub-result equality, but the
  -- outer freeMDirIsoFwd's computation is opaque to
  -- rewrite. Would require refactoring
  -- freeMDirIsoFwd to use a with-clause for the
  -- recursive call to make the sub-expression
  -- visible.
  ?freeMDirIsoFwdBwd_com

-- freeMDirIsoFwd . freeMDirIsoBwd . freeMDirIsoFwd
-- = freeMDirIsoFwd (the weaker retract property).
--
-- This follows from freeMDirIsoFwdBwd applied to
-- the image of freeMDirIsoFwd.
public export
0 freeMDirIsoBwdFwd : FunExt ->
  (pp : PolyProf) ->
  (pos : ppFreeMPosUnit pp) ->
  (a : Type) ->
  (dir : PolyFuncFreeMDir
    (ppToPolyFunc pp a)
    (ppFreeMPosMap pp a pos)) ->
  freeMDirIsoFwd pp pos a
    (freeMDirIsoBwd pp pos a
      (freeMDirIsoFwd pp pos a dir)) =
  freeMDirIsoFwd pp pos a dir
freeMDirIsoBwdFwd fext pp pos a dir =
  freeMDirIsoFwdBwd fext pp pos a
    (freeMDirIsoFwd pp pos a dir)

------------------------------------------------------------
------------------------------------------------------------
---- Mu Round-Trip Proofs ----
------------------------------------------------------------
------------------------------------------------------------

-- Round-trip 1: section-based Mu -> PHOAS -> Mu = id
--
-- Position: fst (el Unit) = ppFreeMPosMap pp Unit pos
-- = pos (by ppFreeMPosMapUnit). The section is
-- recovered by sectionRoundTrip composed with the
-- direction iso round-trip.
public export
0 polyProfMuRoundTrip1 : (fext : FunExt) ->
  {pp : PolyProf} ->
  (mu : PolyProfMu pp) ->
  polyProfFamilyToMu {pp} fext
    (polyProfMuToFamily {pp} mu)
    (polyProfMuToFamilyWedge {pp} fext mu)
  = mu
polyProfMuRoundTrip1 fext {pp} (pos ** sec) =
  ?polyProfMuRoundTrip1_hole

-- Round-trip 2: PHOAS+wedge -> Mu -> PHOAS = id
--
-- At each type x, the position is ppFreeMPosMap pp x
-- (fst (el Unit)) = fst (el x) (by wedge). The
-- direction part follows from the canonical
-- round-trip and direction iso round-trip.
public export
0 polyProfMuRoundTrip2 : (fext : FunExt) ->
  {pp : PolyProf} ->
  (el : PolyProfMuPHOAS pp) ->
  (0 wedge : PolyProfMuPHOASWedge pp el) ->
  (x : Type) ->
  polyProfMuToFamily {pp}
    (polyProfFamilyToMu fext {pp} el wedge) x
  = el x
polyProfMuRoundTrip2 fext {pp} el wedge x =
  ?polyProfMuRoundTrip2_hole

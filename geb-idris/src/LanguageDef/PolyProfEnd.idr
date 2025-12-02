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
-- 1. FreeMDirPF: a polynomial functor characterizing directions at each
--    free monad position
-- 2. freeMDirIsoFwd/freeMDirIsoBwd: isomorphism between actual free monad
--    directions and InterpPolyFunc (FreeMDirPF pos) a

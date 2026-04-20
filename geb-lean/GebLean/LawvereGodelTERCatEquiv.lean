import GebLean.LawvereERQuot
import GebLean.LawvereGodelTQuot
import GebLean.LawvereGodelTInterp
import GebLean.Utilities.ERArith
import Mathlib.CategoryTheory.Equivalence

/-!
# Categorical equivalence `LawvereGodelTCat ≃ LawvereERCat`

Back-translation `GodelTMor1.toER` is a direct structural
recursion with one named-ER case per constructor.  Forward
translation `ERMor1.toGodelT` similarly maps each ER
constructor to a `GodelTMor1` term, with `sub` built from
`disc` / `pred`.  Interp preservation holds
constructor-by-constructor; round-trip identities follow from
the two interp-preservation theorems.
-/

namespace GebLean

open CategoryTheory

/-- Back-translation from a `GodelTMor1 n` term to an
`ERMor1 n` term.  Each constructor maps to its named ER
backing: `ERMor1.zero` / `succ` / `pred` / `proj` / `discN` /
`bsum` / `bprod` / `comp`. -/
def GodelTMor1.toER : {n : ℕ} → GodelTMor1 n → ERMor1 n
  | _, .zero       => ERMor1.zero
  | _, .succ       => ERMor1.succ
  | _, .pred       => ERMor1.pred
  | _, .proj i     => ERMor1.proj i
  | _, .sub        => ERMor1.sub
  | _, .disc       => ERMor1.discN
  | _, .bsum f     => ERMor1.bsum f.toER
  | _, .bprod f    => ERMor1.bprod f.toER
  | _, .comp f g   =>
      ERMor1.comp f.toER (fun i => (g i).toER)

/-- Interp preservation of `toER`: structural induction whose
cases are either `rfl` or reduce to a matching ER simp lemma. -/
theorem GodelTMor1.toER_interp : {n : ℕ} → (t : GodelTMor1 n) →
    (ctx : Fin n → ℕ) → t.toER.interp ctx = t.interp ctx
  | _, .zero, _ => rfl
  | _, .succ, _ => rfl
  | _, .pred, _ => rfl
  | _, .proj _, _ => rfl
  | _, .sub, _ => rfl
  | _, .disc, ctx => by
      change ERMor1.discN.interp ctx = _
      rw [ERMor1.interp_discN]
      change (if ctx 0 = 0 then ctx 1 else ctx 2) =
        (match ctx 0 with | 0 => ctx 1 | _ + 1 => ctx 2)
      by_cases h : ctx 0 = 0
      · simp [h]
      · rcases Nat.exists_eq_succ_of_ne_zero h with ⟨k, hk⟩
        simp [hk]
  | _, .bsum f, ctx => by
      change (ERMor1.bsum f.toER).interp ctx = _
      rw [ERMor1.interp_bsum]
      change natBSum _ _ = natBSum _ _
      congr 1
      funext i
      exact GodelTMor1.toER_interp f _
  | _, .bprod f, ctx => by
      change (ERMor1.bprod f.toER).interp ctx = _
      rw [ERMor1.interp_bprod]
      change natBProd _ _ = natBProd _ _
      congr 1
      funext i
      exact GodelTMor1.toER_interp f _
  | _, .comp f g, ctx => by
      change (ERMor1.comp f.toER (fun i => (g i).toER)).interp
          ctx = _
      rw [ERMor1.interp_comp, GodelTMor1.toER_interp f]
      congr 1
      funext i
      exact GodelTMor1.toER_interp (g i) ctx

/-- Forward translation from an `ERMor1 n` term to a
`GodelTMor1 n` term.  The primitive sets match modulo
`GodelTMor1`'s two T⁻′ extras (`pred`, `disc`), so each ER
constructor maps to its same-named `GodelTMor1` constructor. -/
def ERMor1.toGodelT : {n : ℕ} → ERMor1 n → GodelTMor1 n
  | _, .zero       => GodelTMor1.zero
  | _, .succ       => GodelTMor1.succ
  | _, .proj i     => GodelTMor1.proj i
  | _, .sub        => GodelTMor1.sub
  | _, .bsum f     => GodelTMor1.bsum f.toGodelT
  | _, .bprod f    => GodelTMor1.bprod f.toGodelT
  | _, .comp f g   =>
      GodelTMor1.comp f.toGodelT (fun i => (g i).toGodelT)

/-- Interp preservation of `toGodelT`: structural induction
whose cases all reduce to the matching `GodelTMor1` simp
lemma (the constructors' semantics agree by construction). -/
theorem ERMor1.toGodelT_interp : {n : ℕ} → (t : ERMor1 n) →
    (ctx : Fin n → ℕ) → t.toGodelT.interp ctx = t.interp ctx
  | _, .zero, _ => rfl
  | _, .succ, _ => rfl
  | _, .proj _, _ => rfl
  | _, .sub, _ => rfl
  | _, .bsum f, ctx => by
      change (GodelTMor1.bsum f.toGodelT).interp ctx = _
      rw [GodelTMor1.interp_bsum, ERMor1.interp_bsum]
      congr 1
      funext i
      exact ERMor1.toGodelT_interp f _
  | _, .bprod f, ctx => by
      change (GodelTMor1.bprod f.toGodelT).interp ctx = _
      rw [GodelTMor1.interp_bprod, ERMor1.interp_bprod]
      congr 1
      funext i
      exact ERMor1.toGodelT_interp f _
  | _, .comp f g, ctx => by
      change (GodelTMor1.comp f.toGodelT
          (fun i => (g i).toGodelT)).interp ctx = _
      rw [GodelTMor1.interp_comp, ERMor1.interp_comp,
        ERMor1.toGodelT_interp f]
      congr 1
      funext i
      exact ERMor1.toGodelT_interp (g i) ctx

/-- Round-trip identity: at the term level, `toER.toGodelT`
preserves interp of the original `GodelTMor1`. -/
theorem GodelTMor1.toER_toGodelT_interp {n : ℕ}
    (t : GodelTMor1 n) (ctx : Fin n → ℕ) :
    t.toER.toGodelT.interp ctx = t.interp ctx := by
  rw [ERMor1.toGodelT_interp, GodelTMor1.toER_interp]

/-- Round-trip identity: at the term level, `toGodelT.toER`
preserves interp of the original `ERMor1`. -/
theorem ERMor1.toGodelT_toER_interp {n : ℕ}
    (t : ERMor1 n) (ctx : Fin n → ℕ) :
    t.toGodelT.toER.interp ctx = t.interp ctx := by
  rw [GodelTMor1.toER_interp, ERMor1.toGodelT_interp]

/-- Componentwise lift of `GodelTMor1.toER` to `GodelTMorN`
tuples. -/
def GodelTMorN.toER {n m : ℕ} (f : GodelTMorN n m) :
    ERMorN n m :=
  fun i => (f i).toER

/-- Componentwise lift of `ERMor1.toGodelT` to `ERMorN`
tuples. -/
def ERMorN.toGodelT {n m : ℕ} (f : ERMorN n m) :
    GodelTMorN n m :=
  fun i => (f i).toGodelT

theorem GodelTMorN.toER_interp {n m : ℕ}
    (f : GodelTMorN n m) (ctx : Fin n → ℕ) :
    f.toER.interp ctx = f.interp ctx := by
  funext i
  exact GodelTMor1.toER_interp (f i) ctx

theorem ERMorN.toGodelT_interp {n m : ℕ}
    (f : ERMorN n m) (ctx : Fin n → ℕ) :
    f.toGodelT.interp ctx = f.interp ctx := by
  funext i
  exact ERMor1.toGodelT_interp (f i) ctx

/-- Lift `GodelTMorN.toER` to quotient classes.  Well-defined
because extensionally equal tuples translate to extensionally
equal ER tuples via `toER_interp`. -/
def GodelTMorNQuo.toER {n m : ℕ} (f : GodelTMorNQuo n m) :
    ERMorNQuo n m :=
  Quotient.lift (s := godelTMorNSetoid n m)
    (fun f' => Quotient.mk (erMorNSetoid n m) f'.toER)
    (fun a b h => Quotient.sound
      (s := erMorNSetoid n m) (fun ctx => by
        rw [GodelTMorN.toER_interp, GodelTMorN.toER_interp,
          h ctx]))
    f

/-- Lift `ERMorN.toGodelT` to quotient classes. -/
def ERMorNQuo.toGodelT {n m : ℕ} (f : ERMorNQuo n m) :
    GodelTMorNQuo n m :=
  Quotient.lift (s := erMorNSetoid n m)
    (fun f' => Quotient.mk (godelTMorNSetoid n m) f'.toGodelT)
    (fun a b h => Quotient.sound
      (s := godelTMorNSetoid n m) (fun ctx => by
        rw [ERMorN.toGodelT_interp, ERMorN.toGodelT_interp,
          h ctx]))
    f

@[simp] theorem GodelTMorNQuo.toER_mk {n m : ℕ}
    (f : GodelTMorN n m) :
    GodelTMorNQuo.toER
        (Quotient.mk (godelTMorNSetoid n m) f) =
      Quotient.mk (erMorNSetoid n m) f.toER := rfl

@[simp] theorem ERMorNQuo.toGodelT_mk {n m : ℕ}
    (f : ERMorN n m) :
    ERMorNQuo.toGodelT (Quotient.mk (erMorNSetoid n m) f) =
      Quotient.mk (godelTMorNSetoid n m) f.toGodelT := rfl

/-- The back functor from `LawvereGodelTCat` to `LawvereERCat`.
Acts as the identity on arity objects and sends each morphism
class to its `toER` image. -/
def godelTToERFunctor : LawvereGodelTCat ⥤ LawvereERCat where
  obj n := n
  map {_ _} f := GodelTMorNQuo.toER f
  map_id _ := rfl
  map_comp {_ _ _} f g := by
    revert f g
    apply Quotient.ind₂
    intro f_raw g_raw
    apply Quotient.sound (s := erMorNSetoid _ _)
    intro ctx
    rw [ERMorN.interp_comp, GodelTMorN.toER_interp,
      GodelTMorN.toER_interp, GodelTMorN.toER_interp,
      GodelTMorN.interp_comp]

/-- The forward functor from `LawvereERCat` to
`LawvereGodelTCat`. -/
def erToGodelTFunctor : LawvereERCat ⥤ LawvereGodelTCat where
  obj n := n
  map {_ _} f := ERMorNQuo.toGodelT f
  map_id _ := rfl
  map_comp {_ _ _} f g := by
    revert f g
    apply Quotient.ind₂
    intro f_raw g_raw
    apply Quotient.sound (s := godelTMorNSetoid _ _)
    intro ctx
    rw [GodelTMorN.interp_comp, ERMorN.toGodelT_interp,
      ERMorN.toGodelT_interp, ERMorN.toGodelT_interp,
      ERMorN.interp_comp]

/-- Round-trip identity at the quotient level: `toER.toGodelT`
of any `GodelTMorNQuo` morphism recovers the original. -/
theorem GodelTMorNQuo.toER_toGodelT_id {n m : ℕ}
    (f : GodelTMorNQuo n m) :
    ERMorNQuo.toGodelT (GodelTMorNQuo.toER f) = f := by
  revert f
  apply Quotient.ind
  intro f_raw
  apply Quotient.sound (s := godelTMorNSetoid n m)
  intro ctx
  funext i
  exact GodelTMor1.toER_toGodelT_interp (f_raw i) ctx

/-- Round-trip identity at the quotient level: `toGodelT.toER`
of any `ERMorNQuo` morphism recovers the original. -/
theorem ERMorNQuo.toGodelT_toER_id {n m : ℕ}
    (f : ERMorNQuo n m) :
    GodelTMorNQuo.toER (ERMorNQuo.toGodelT f) = f := by
  revert f
  apply Quotient.ind
  intro f_raw
  apply Quotient.sound (s := erMorNSetoid n m)
  intro ctx
  funext i
  exact ERMor1.toGodelT_toER_interp (f_raw i) ctx

/-- Unit isomorphism: `𝟭 LawvereGodelTCat ≅ godelTToERFunctor
⋙ erToGodelTFunctor`.  Both functors are identity on arity
objects; naturality uses the round-trip identity
`GodelTMorNQuo.toER_toGodelT_id`. -/
def lawvereGodelTERCatUnitIso :
    𝟭 LawvereGodelTCat ≅ godelTToERFunctor ⋙ erToGodelTFunctor :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun {_ _} f => by
      revert f
      apply Quotient.ind
      intro f_raw
      simp only [Iso.refl_hom, Category.id_comp,
        Category.comp_id, Functor.comp_map, Functor.id_map]
      exact (GodelTMorNQuo.toER_toGodelT_id _).symm)

/-- Counit isomorphism: `erToGodelTFunctor ⋙ godelTToERFunctor
≅ 𝟭 LawvereERCat`.  Symmetric to the unit, via
`ERMorNQuo.toGodelT_toER_id`. -/
def lawvereGodelTERCatCounitIso :
    erToGodelTFunctor ⋙ godelTToERFunctor ≅ 𝟭 LawvereERCat :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun {_ _} f => by
      revert f
      apply Quotient.ind
      intro f_raw
      simp only [Iso.refl_hom, Category.id_comp,
        Category.comp_id, Functor.comp_map, Functor.id_map]
      change GodelTMorNQuo.toER
          (ERMorNQuo.toGodelT (Quotient.mk _ f_raw)) =
        Quotient.mk _ f_raw
      exact ERMorNQuo.toGodelT_toER_id _)

/-- The categorical equivalence `LawvereGodelTCat ≌
LawvereERCat`.  Both unit and counit are identity isos: the
two functors are identity on arity objects, and the
round-trip identities at the quotient level make naturality
immediate. -/
def lawvereGodelTERCatEquivalence :
    LawvereGodelTCat ≌ LawvereERCat where
  functor := godelTToERFunctor
  inverse := erToGodelTFunctor
  unitIso := lawvereGodelTERCatUnitIso
  counitIso := lawvereGodelTERCatCounitIso
  functor_unitIso_comp n := by
    change ERMorNQuo.comp
        (GodelTMorNQuo.toER (GodelTMorNQuo.id n))
        (ERMorNQuo.id n) =
      ERMorNQuo.id n
    rw [show GodelTMorNQuo.toER (GodelTMorNQuo.id n) =
          ERMorNQuo.id n from rfl,
      ERMorNQuo.id_comp]

end GebLean

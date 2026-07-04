import GebLean.Ramified.Definability.Machine
import GebLean.Ramified.Definability.Bounds
import GebLean.LawvereERKSim.Top
import GebLean.LawvereERKSim.RuntimeBound

/-!
# The elementary-recurrence definability family

The completeness direction of Leivant III's principal result (Theorem 14
(1) ⇒ (2), section 6.1) at the `1 + X` word-algebra instantiation: every
elementary-recurrence morphism is ramified-definable. An object-sort context is
a length-indexed family of object sorts (`ObjCtx`); its numeric denotation
(`ramifiedDenotation`) builds a standard-model environment from a numeric input
through the carrier-copy transports, evaluates a syntactic-category morphism by
`Hom.eval`, and reads each output back through `objToNat` / `natFreeAlgEquiv`
(standing decision 8). The family `erMor_ramified_definable` chains the ER
compiler (`compileER`, `compileER_runFor`) and its runtime tower bound
(`boundExprKParams_dominates`, converted to Leivant's clock format `c · 2_q` by
`tower_clock_format`) into Lemma 6 (`urm_ramified_definable`): the realizer is
`machineRealizer` over `machineCtx`, retyped over the object-sort contexts. The
`m`-output form `erMorN_ramified_definable` assembles the components over a
common clock, the `m` realizers sharing `machineCtx` and tupled into
`oCtx m`'s context.

## Main definitions

* `ObjCtx` — object-sort contexts of length `n`.
* `ObjCtx.toCtx` — the underlying context of an object-sort context.
* `oCtx` — the object-sort context of `m` copies of the base sort `o`.
* `objFromNat` — the carrier-copy transport of a natural into an object-sort
  denotation (the inverse direction of `objToNat`).
* `ramifiedEnv` — the numeric environment over an object-sort context.
* `ramifiedDenotation` — the numeric denotation of a morphism between
  object-sort contexts.
* `machineObjCtx` — `machineCtx a q` packaged as an object-sort context.
* `erRealizer`, `machineTupleHom`, `erRealizerN` — the eq. (8) realizer and its
  `m`-output tuple, retyped over the object-sort contexts.

## Main statements

* `erMor_ramified_definable` — the definability family: every ER morphism has an
  object-sort context and realizer with matching denotation.
* `erMorN_ramified_definable` — the `m`-output definability family, assembled
  componentwise over a common clock.

## Implementation notes

The `{s // IsObj s}` subtype pattern for `ObjCtx` follows the Phase 4 review
record. `ramifiedDenotation` and the two families are novel packaging of the
section 6.1 definability statement (spec s6.1). Phase 7 re-states this family as
`ramified_definability` against `collapseDenotation`.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The definability direction
is Theorem 14 (1) ⇒ (2), section 6.1 (via sections 2.7 and 3.2).

Categorical/doctrinal treatment of tiered (ramified) recurrence via
height-graded multi-sorted equational theories, with complexity classes
as images of initial doctrine-categories: J. R. Otto, "Complexity
Doctrines", PhD thesis, McGill University, 1995, DOI 10.82308/7828
(§1.1 sketch theories; Chapter 4 the Kalmar-elementary doctrines
`R`/`C`/`C'` with the enough-maps / not-too-many-maps pair). The present
development differs in: (i) it formalizes Leivant's higher-type system
`RMRec-omega` (Leivant III, APAL 96 (1999) 209-229, DOI
10.1016/S0168-0072(98)00040-2), which postdates Otto and which Otto does
not treat, his positive characterizations being first-order and his
higher-type LCC-comprehension attempt a negative result; (ii) it uses a
multi-sorted Lawvere theory with a syntactic category under
interpretative equality and a soundness functor into `LawvereERCat`,
rather than set-valued sketch models and images in `set^2`/`set^V`/
`set^3`; (iii) it realizes syntax as W-types of polynomial endofunctors,
a device with no counterpart in Otto.

## Tags

ramified recurrence, elementary recurrence, definability, Lawvere theory,
object sort, syntactic category, elementary complexity
-/

namespace GebLean.Ramified.Definability

open CategoryTheory
open GebLean.ZeroTestURM GebLean.LawvereERKSim

/-- Object-sort contexts of length `n`: every entry an object sort. -/
def ObjCtx (n : ℕ) : Type := Fin n → { s : RType // s.IsObj }

/-- The underlying context of an object-sort context. -/
def ObjCtx.toCtx {n : ℕ} (Γ : ObjCtx n) : Ctx RType :=
  List.ofFn (fun i => (Γ i).val)

/-- The underlying context has length `n`. -/
@[simp] theorem ObjCtx.toCtx_length {n : ℕ} (Γ : ObjCtx n) :
    Γ.toCtx.length = n :=
  List.length_ofFn

/-- The entry of the underlying context at a position. -/
theorem ObjCtx.toCtx_get {n : ℕ} (Γ : ObjCtx n) (i : Fin Γ.toCtx.length) :
    Γ.toCtx.get i = (Γ (Fin.cast Γ.toCtx_length i)).val := by
  simp only [ObjCtx.toCtx, List.get_ofFn]

/-- The all-object-sort context of `m` copies of the base sort `o`. -/
def oCtx (m : ℕ) : ObjCtx m := fun _ => oObj

/-- The underlying context of `oCtx m` is `m` copies of `o`. -/
theorem oCtx_toCtx (m : ℕ) : (oCtx m).toCtx = List.replicate m RType.o := by
  simp only [ObjCtx.toCtx, oCtx, oObj]
  exact List.ofFn_const m RType.o

/-- Every entry of the underlying context is an object sort. -/
theorem ObjCtx.toCtx_get_isObj {n : ℕ} (Γ : ObjCtx n) (i : Fin Γ.toCtx.length) :
    (Γ.toCtx.get i).IsObj :=
  (Γ.toCtx_get i).symm ▸ (Γ (Fin.cast Γ.toCtx_length i)).2

/-- The carrier-copy transport of a natural into an object-sort denotation
(the inverse direction of `objToNat`; Leivant III section 2.7): read the
numeral through `natToFreeAlg` and cast it into the object sort's carrier
copy. -/
def objFromNat {s : RType} (hs : s.IsObj) (k : ℕ) :
    RType.interp (FreeAlg natAlgSig) s :=
  cast (RType.interp_isObj (FreeAlg natAlgSig) hs).symm (natToFreeAlg k)

/-- The numeric reading inverts the carrier-copy transport:
`objToNat hs (objFromNat hs k) = k`. -/
theorem objToNat_objFromNat {s : RType} (hs : s.IsObj) (k : ℕ) :
    objToNat hs (objFromNat hs k) = k := by
  unfold objToNat objFromNat
  rw [cast_cast, cast_eq]
  exact freeAlgToNat_natToFreeAlg k

/-- The numeric reading of a value that is heterogeneously equal to a carrier
element is the carrier element's numeral: object sorts denote copies of the
carrier, so the reading forgets the copy. -/
theorem objToNat_heq_freeAlgToNat {s : RType} (hs : s.IsObj)
    (x : RType.interp (FreeAlg natAlgSig) s) (y : FreeAlg natAlgSig) (hxy : HEq x y) :
    objToNat hs x = freeAlgToNat y := by
  unfold objToNat
  exact congrArg freeAlgToNat (eq_of_heq ((cast_heq _ _).trans hxy))

/-- The numeric environment over an object-sort context: position `i` carries
the numeral of `v` at that position, transported into the object sort's carrier
copy. The environment `ramifiedDenotation` evaluates. -/
def ramifiedEnv {n : ℕ} (Γ : ObjCtx n) (v : Fin n → ℕ) :
    (standardModel (higherOrder natAlgSig)).Env Γ.toCtx :=
  fun i => objFromNat (Γ.toCtx_get_isObj i) (v (Fin.cast Γ.toCtx_length i))

/-- The numeric denotation of a morphism between object-sort contexts (standing
decision 8): build the environment from `v` through `objFromNat`, evaluate by
`Hom.eval` at the standard model, and read each output position back through
`objToNat`. -/
def ramifiedDenotation {n m : ℕ} {Γ : ObjCtx n} {Δ : ObjCtx m}
    (g : Hom (higherOrder natAlgSig)
      (interpQuotRel (higherOrder natAlgSig)) Γ.toCtx Δ.toCtx) :
    (Fin n → ℕ) → (Fin m → ℕ) :=
  fun v j =>
    objToNat (Δ.toCtx_get_isObj (Fin.cast (Δ.toCtx_length).symm j))
      (g.eval (ramifiedEnv Γ v) (Fin.cast (Δ.toCtx_length).symm j))

/-- The realizer input context `machineCtx a q` packaged as an object-sort
context of length `a`: entry `i` is the `i`-th sort of `machineCtx a q`, an
object sort by `machineCtx_isObj`. -/
def machineObjCtx (a q : ℕ) : ObjCtx a :=
  fun i => ⟨(machineCtx a q).get (Fin.cast (machineCtx_length a q).symm i),
    machineCtx_isObj a q _⟩

/-- The underlying context of `machineObjCtx a q` is `machineCtx a q`. -/
theorem machineObjCtx_toCtx (a q : ℕ) :
    (machineObjCtx a q).toCtx = machineCtx a q := by
  apply List.ext_getElem
  · rw [ObjCtx.toCtx_length]; exact (machineCtx_length a q).symm
  · intro i h1 h2
    simp only [ObjCtx.toCtx, machineObjCtx, List.getElem_ofFn, List.get_eq_getElem]
    rfl

/-- The carrier-copy transports of a natural at two object sorts are heterogeneously
equal: both are the numeral read through `natToFreeAlg`. -/
theorem objFromNat_heq {s s' : RType} (hs : s.IsObj) (hs' : s'.IsObj) (k : ℕ) :
    HEq (objFromNat hs k) (objFromNat hs' k) :=
  (cast_heq _ _).trans (cast_heq _ _).symm

/-- The numeric environment over `machineObjCtx a q` agrees heterogeneously with
`machineEnv q v`: both assign each position the numeral of `v` at that position,
transported into the object sort's carrier copy. -/
theorem heq_ramifiedEnv_machineEnv (a q : ℕ) (v : Fin a → ℕ) :
    HEq (ramifiedEnv (machineObjCtx a q) v) (machineEnv q v) := by
  refine Function.hfunext ?_ ?_
  · exact congrArg Fin
      ((ObjCtx.toCtx_length (machineObjCtx a q)).trans (machineCtx_length a q).symm)
  · intro i i' hii
    have hval : i.val = i'.val :=
      (Fin.heq_ext_iff
        ((ObjCtx.toCtx_length (machineObjCtx a q)).trans (machineCtx_length a q).symm)).mp hii
    have hk : v (Fin.cast (machineObjCtx a q).toCtx_length i)
        = v ⟨i'.val, Nat.lt_of_lt_of_eq i'.isLt (machineCtx_length a q)⟩ :=
      congrArg v (Fin.ext hval)
    have hL : ramifiedEnv (machineObjCtx a q) v i
        = objFromNat ((machineObjCtx a q).toCtx_get_isObj i)
            (v (Fin.cast (machineObjCtx a q).toCtx_length i)) := rfl
    have hR : machineEnv q v i'
        = objFromNat (machineCtx_isObj a q i')
            (v ⟨i'.val, Nat.lt_of_lt_of_eq i'.isLt (machineCtx_length a q)⟩) := rfl
    rw [hL, hR, ← hk]
    exact objFromNat_heq _ _ _

/-- Evaluation transported along a domain-context equality: a hom cast along a
domain equality evaluates by casting the environment back. -/
theorem eval_cast_dom {P : Presentation} {Γ Γ' Δ : Ctx P.S} (h : Γ = Γ')
    (f : Hom P (interpQuotRel P) Γ Δ) (ρ : (standardModel P).Env Γ') :
    (h ▸ f).eval ρ = f.eval (h ▸ ρ) := by
  subst h; rfl

/-- Evaluation transported along a codomain-context equality: evaluating a hom
cast along a codomain equality is the transport of the original evaluation. -/
theorem eval_cast_cod {P : Presentation} {Γ Δ Δ' : Ctx P.S} (h : Δ = Δ')
    (f : Hom P (interpQuotRel P) Γ Δ) (ρ : (standardModel P).Env Γ) :
    (h ▸ f).eval ρ = h ▸ (f.eval ρ) := by
  subst h; rfl

/-- Leivant III eq. (8)'s realizer, retyped over the object-sort contexts of the
definability family: `machineRealizer p c q` transported along the
context equalities `machineObjCtx_toCtx` and `oCtx_toCtx`. -/
def erRealizer {a : ℕ} (p : URMProgram a) (c q : ℕ) :
    Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
      (machineObjCtx a q).toCtx (oCtx 1).toCtx :=
  (machineObjCtx_toCtx a q).symm ▸ ((oCtx_toCtx 1).symm ▸ machineRealizer p c q)

/-- Evaluation transported along domain and codomain equalities, read at
transported indices, is heterogeneously equal to the untransported evaluation:
transporting a hom's contexts and its environment does not change the values it
computes. -/
theorem eval_heq {P : Presentation} {Γ Γ' Δ Δ' : Ctx P.S} (hΓ : Γ = Γ')
    (hΔ : Δ = Δ') (f : Hom P (interpQuotRel P) Γ Δ)
    (ρ : (standardModel P).Env Γ) (ρ' : (standardModel P).Env Γ') (hρ : HEq ρ ρ')
    (i : Fin Δ'.length) (i0 : Fin Δ.length) (hi : HEq i i0) :
    HEq ((hΓ ▸ hΔ ▸ f).eval ρ' i) (f.eval ρ i0) := by
  subst hΓ; subst hΔ
  obtain rfl := eq_of_heq hρ
  obtain rfl := eq_of_heq hi
  rfl

/-- The numeric denotation of `erRealizer p c q` reads off `machineRealizer`'s
evaluation at the machine environment: the object-sort retyping and the numeric
readback compose to `freeAlgToNat` of the eq. (8) realizer's output. -/
theorem ramifiedDenotation_erRealizer {a : ℕ} (p : URMProgram a) (c q : ℕ)
    (v : Fin a → ℕ) (j : Fin 1) :
    ramifiedDenotation (erRealizer p c q) v j
      = freeAlgToNat ((machineRealizer p c q).eval (machineEnv q v) 0) := by
  refine objToNat_heq_freeAlgToNat _ _ _
    (eval_heq (machineObjCtx_toCtx a q).symm (oCtx_toCtx 1).symm (machineRealizer p c q)
      (machineEnv q v) (ramifiedEnv (machineObjCtx a q) v)
      (heq_ramifiedEnv_machineEnv a q v).symm _ 0 ?_)
  refine (Fin.heq_ext_iff (ObjCtx.toCtx_length (oCtx 1))).mpr ?_
  have := j.isLt
  simp only [Fin.val_cast, Fin.val_zero]
  omega

/-- The elementary-recurrence definability family (Leivant III Theorem 14
(1) ⇒ (2), section 6.1, DOI `10.1016/S0168-0072(98)00040-2`): every ER morphism
`e : ERMor1 a` has an object-sort context `Γ` and a ramified realizer `g` with
`ramifiedDenotation g = fun v _ => e.interp v`. The context and realizer are
`machineObjCtx a q` and `erRealizer (compileER e) c q`; the clock `(c, q)` comes
from `tower_clock_format` applied to the runtime tower bound
`boundExprKParams_dominates`, `compileER_runFor` supplies the stabilized
computation, and `urm_ramified_definable` (Lemma 6) reads off the realizer. -/
theorem erMor_ramified_definable {a : ℕ} (e : ERMor1 a) :
    ∃ (Γ : ObjCtx a)
      (g : Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
        Γ.toCtx (oCtx 1).toCtx),
      ramifiedDenotation g = fun v _ => e.interp v := by
  obtain ⟨c, q, hcq⟩ := tower_clock_format (boundExprKParams e).1 (boundExprKParams e).2
  refine ⟨machineObjCtx a q, erRealizer (compileER e) c q, ?_⟩
  funext v j
  rw [ramifiedDenotation_erRealizer]
  refine urm_ramified_definable (compileER e) e.interp c q (fun w t ht => ?_) v
  refine compileER_runFor e w t ?_
  calc compileER_runtime e w
      ≤ tower (boundExprKParams e).1 (Fin.maxOfNat a w + (boundExprKParams e).2) :=
        (boundExprKParams_dominates e w).1
    _ ≤ c * tower q (Fin.maxOfNat a w) := hcq (Fin.maxOfNat a w)
    _ ≤ t := ht

/-- The sole defining term of `machineRealizer p c q`: the identifier operation
of `machineIdent p c q` applied to the context variables. The representative
term reused as a tuple component in the `m`-output assembly. -/
def machineTerm {a : ℕ} (p : URMProgram a) (c q : ℕ) :
    Tm (higherOrder natAlgSig).sig (machineCtx a q) RType.o :=
  Tm.op (sig := (higherOrder natAlgSig).sig)
    (Sum.inl (Sum.inr ⟨machineCtx a q, RType.o, machineIdent p c q⟩))
    (fun k => Tm.var k)

/-- The defining term evaluates to `machineIdent`'s denotation. -/
theorem machineTerm_eval {a : ℕ} (p : URMProgram a) (c q : ℕ)
    (ρ : (standardModel (higherOrder natAlgSig)).Env (machineCtx a q)) :
    (machineTerm p c q).eval (standardModel (higherOrder natAlgSig)) ρ
      = (machineIdent p c q).interp ρ :=
  rfl

/-- The `m`-output eq. (8) realizer over `machineCtx a q`: the tuple whose
`i`-th component is the defining term of `machineRealizer (compileER (e i)) c q`,
retyped at the `i`-th `o`-copy of `replicate m o`. All `m` components share the
context `machineCtx a q`; the common clock `(c, q)` is supplied by the caller. -/
def machineTupleHom {a m : ℕ} (e : Fin m → ERMor1 a) (c q : ℕ) :
    Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
      (machineCtx a q) (List.replicate m RType.o) :=
  Quotient.mk _ (fun i =>
    Tm.reind (get_replicate m RType.o i).symm
      (machineTerm
        (compileER (e ⟨i.val, Nat.lt_of_lt_of_eq i.isLt List.length_replicate⟩)) c q))

/-- The `i`-th component of the `m`-output realizer evaluates, up to the
`o`-copy retyping, to the `i`-th machine identifier's denotation. -/
theorem machineTupleHom_eval_heq {a m : ℕ} (e : Fin m → ERMor1 a) (c q : ℕ)
    (ρ : (standardModel (higherOrder natAlgSig)).Env (machineCtx a q))
    (i : Fin (List.replicate m RType.o).length) (hi : i.val < m) :
    HEq ((machineTupleHom e c q).eval ρ i)
        ((machineIdent (compileER (e ⟨i.val, hi⟩)) c q).interp ρ) := by
  have h1 : (machineTupleHom e c q).eval ρ i
      = (Tm.reind (get_replicate m RType.o i).symm
          (machineTerm (compileER (e ⟨i.val, hi⟩)) c q)).eval
            (standardModel (higherOrder natAlgSig)) ρ := rfl
  have h2 := Tm.eval_transport (standardModel (higherOrder natAlgSig)) ρ
    (get_replicate m RType.o i).symm (machineTerm (compileER (e ⟨i.val, hi⟩)) c q)
  have h3 := machineTerm_eval (compileER (e ⟨i.val, hi⟩)) c q ρ
  rw [h1]
  exact (heq_of_eq h2).trans ((cast_heq _ _).trans (heq_of_eq h3))

/-- The `m`-output eq. (8) realizer retyped over the object-sort contexts:
`machineTupleHom e c q` transported along `machineObjCtx_toCtx` and `oCtx_toCtx`. -/
def erRealizerN {a m : ℕ} (e : Fin m → ERMor1 a) (c q : ℕ) :
    Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
      (machineObjCtx a q).toCtx (oCtx m).toCtx :=
  (machineObjCtx_toCtx a q).symm ▸ ((oCtx_toCtx m).symm ▸ machineTupleHom e c q)

/-- The `j`-th numeric output of `erRealizerN e c q` reads off the `j`-th
machine identifier's denotation at the machine environment. -/
theorem ramifiedDenotation_erRealizerN {a m : ℕ} (e : Fin m → ERMor1 a) (c q : ℕ)
    (v : Fin a → ℕ) (j : Fin m) :
    ramifiedDenotation (erRealizerN e c q) v j
      = freeAlgToNat ((machineIdent (compileER (e j)) c q).interp (machineEnv q v)) := by
  refine objToNat_heq_freeAlgToNat _ _ _
    ((eval_heq (machineObjCtx_toCtx a q).symm (oCtx_toCtx m).symm (machineTupleHom e c q)
      (machineEnv q v) (ramifiedEnv (machineObjCtx a q) v)
      (heq_ramifiedEnv_machineEnv a q v).symm _
      (Fin.cast List.length_replicate.symm j) ?_).trans ?_)
  · refine (Fin.heq_ext_iff
      ((ObjCtx.toCtx_length (oCtx m)).trans List.length_replicate.symm)).mpr ?_
    simp only [Fin.val_cast]
  · exact machineTupleHom_eval_heq e c q (machineEnv q v) (Fin.cast List.length_replicate.symm j)
      (Nat.lt_of_lt_of_eq (Fin.cast List.length_replicate.symm j).isLt List.length_replicate)

/-- The `m`-output definability family (Leivant III Theorem 14 (1) ⇒ (2),
section 6.1): every finite tuple of ER morphisms of a common arity has an
object-sort context and a ramified realizer whose numeric denotation is the
tuple's componentwise interpretation. The `m` realizers share `machineCtx a q`;
the common clock height `q` is the supremum over the components of the
per-component tower heights, so a single clock dominates every component's
runtime bound (`tower_add_le_tower`, `tower_mono_left`). -/
theorem erMorN_ramified_definable {a m : ℕ} (e : Fin m → ERMor1 a) :
    ∃ (Γ : ObjCtx a)
      (g : Hom (higherOrder natAlgSig) (interpQuotRel (higherOrder natAlgSig))
        Γ.toCtx (oCtx m).toCtx),
      ramifiedDenotation g = fun v j => (e j).interp v := by
  let q : ℕ :=
    Finset.univ.sup (fun j => (boundExprKParams (e j)).1 + (boundExprKParams (e j)).2)
  refine ⟨machineObjCtx a q, erRealizerN e 1 q, ?_⟩
  funext v j
  rw [ramifiedDenotation_erRealizerN,
    ← identHom_eval (machineIdent (compileER (e j)) 1 q) (machineEnv q v)]
  refine urm_ramified_definable (compileER (e j)) (e j).interp 1 q (fun w t ht => ?_) v
  refine compileER_runFor (e j) w t ?_
  calc compileER_runtime (e j) w
      ≤ tower (boundExprKParams (e j)).1 (Fin.maxOfNat a w + (boundExprKParams (e j)).2) :=
        (boundExprKParams_dominates (e j) w).1
    _ ≤ tower ((boundExprKParams (e j)).1 + (boundExprKParams (e j)).2) (Fin.maxOfNat a w) :=
        tower_add_le_tower _ _ _
    _ ≤ tower q (Fin.maxOfNat a w) :=
        tower_mono_left (Finset.le_sup
          (f := fun j => (boundExprKParams (e j)).1 + (boundExprKParams (e j)).2)
          (Finset.mem_univ j)) _
    _ = 1 * tower q (Fin.maxOfNat a w) := (Nat.one_mul _).symm
    _ ≤ t := ht

end GebLean.Ramified.Definability

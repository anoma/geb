import GebLean.Ramified.AlgSig

/-!
# Ramified types and object sorts

The ramified types (r-types) of Leivant's higher-type ramified recurrence
and their object sorts. An r-type is generated from a base type `o`, a
binary `arrow`, and a unary `Omega`; the object sorts are `o` and every
`Omega tau`; the tower sorts `Omega^m o` are the finite iterates of
`Omega` on `o`; and `RType.interp` realizes each r-type as a type over a
carrier, sending every object sort to a copy of the carrier and every
arrow to a function space.

These definitions transcribe Leivant III section 2.3 (the r-types),
section 2.4(3) (the tower sorts), and section 2.7 (the standard denotation
of object sorts). The realization of `RType` as the `PolyFix` W-type of a
three-shape signature endofunctor is novel packaging (decision 8: every
recursive type in this development is a W-type of a `PolyEndo`, not a
Lean-native inductive); it reuses the free-algebra layer `FreeAlg` of
`GebLean/Ramified/AlgSig.lean`, instantiated at the signature `rTypeSig`
whose shapes are a nullary `o`, a binary `arrow`, and a unary `omega`.

## Main definitions

* `RTypeShape` — the three constructor shapes of the r-type signature.
* `rTypeSig` — the r-type signature: shapes with arities `0`, `2`, `1`.
* `RType` — the ramified types: the `FreeAlg` of `rTypeSig` (the `PolyFix`
  W-type of its signature endofunctor).
* `RType.o`, `RType.arrow`, `RType.omega` — the derived constructors.
* `RType.shape` — the top constructor shape of an r-type.
* `RType.IsObj` — the object-sort predicate (`o` and every `Omega tau`).
* `RType.tower` — the tower sorts `Omega^m o`.
* `RType.IsTower` — the tower-sort predicate (a chain of `Omega`s ending in
  `o`), with a `DecidablePred` instance.
* `RType.IsSimple` — the omega-free predicate (no `Omega` occurs anywhere in
  the r-type), with a `DecidablePred` instance.
* `RType.interp` — the denotation of an r-type over a carrier.
* `RType.interpCongr` — the congruence of the denotation along a base-carrier
  equivalence.
* `oObj` — the base object sort `o` as an object-sort witness.

## Main statements

* `RType.arrow_eq_arrow`, `RType.omega_eq_omega` — injectivity of the
  derived constructors.
* `RType.tower_isObj` — every tower sort is an object sort.
* `RType.tower_isTower` — every tower sort satisfies `RType.IsTower`.
* `RType.interp_isObj` — every object sort denotes a copy of the carrier.
* `RType.interpCongr_isObj` — the denotation congruence at an object sort is
  the base equivalence.
* `RType.o_isSimple`, `RType.arrow_isSimple_iff` — the simple-type predicate
  on the base type and on `arrow`.

## Implementation notes

`RType` reuses `FreeAlg rTypeSig`, so its constructors are the generic
`FreeAlg.mk` at the three shapes and its recursions go through the
dependent eliminator `PolyFix.ind`. `DecidableEq RType` and
`DecidablePred RType.IsObj` are built by structural recursion via
`PolyFix.ind` rather than by `deriving`: a `PolyFix` node carries its
children as a function, which `deriving` cannot handle, so the decision
procedures compare shapes and recurse on children at the literal arity
positions. `RType.interp` sends every object sort — `o` and every
`Omega tau`, regardless of `tau` — to a copy of the carrier, and each
arrow to the function space of the denotations of its two subterms.

## References

D. Leivant, "Ramified recurrence and computational complexity III:
Higher type recurrence and elementary complexity", Annals of Pure and
Applied Logic 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.
The r-types are section 2.3; the tower sorts `Omega^m o` are section
2.4(3); the standard denotation of object sorts as copies of the base
carrier is section 2.7; the simple (omega-free) types are section 4.2
("the types are not ramified").

## Tags

ramified recurrence, ramified type, object sort, tower sort, free algebra,
polynomial functor, W-type, interpretation
-/

namespace GebLean.Ramified

open CategoryTheory

/-- The three constructor shapes of the r-type signature (Leivant III
section 2.3): the base type `o`, the binary `arrow`, and the unary
`omega`. A finite label type, carrying no recursion. -/
inductive RTypeShape where
  | o
  | arrow
  | omega
  deriving DecidableEq

/-- The r-type signature: the three shapes `o`, `arrow`, `omega` with
arities `0`, `2`, `1`, presented as a free-algebra signature (Leivant III
section 2.3). -/
def rTypeSig : AlgSig :=
  ⟨RTypeShape, fun s => match s with
    | RTypeShape.o => 0
    | RTypeShape.arrow => 2
    | RTypeShape.omega => 1⟩

/-- Leivant III section 2.3's definition of the ramified types (r-types),
generated from a base type `o`, a binary `arrow`, and a unary `Omega`.
Realized (decision 8) as the `FreeAlg` of `rTypeSig` — the `PolyFix`
W-type of the r-type signature endofunctor, a `PolyEndo PUnit` with a
nullary shape (`o`), a binary shape (`arrow`), and a unary shape
(`omega`). The W-type packaging is novel; the r-type conventions
transcribe Leivant III section 2.3. -/
def RType : Type := FreeAlg rTypeSig

/-- The base type `o` (Leivant III section 2.3): the nullary shape. -/
def RType.o : RType := FreeAlg.mk RTypeShape.o Fin.elim0

/-- The function type `arrow tau sigma`, written `tau → sigma` (Leivant
III section 2.3): the binary shape applied to domain `a` and codomain
`b`. -/
def RType.arrow (a b : RType) : RType := FreeAlg.mk RTypeShape.arrow ![a, b]

/-- The type `Omega tau` (Leivant III section 2.3): the unary shape
applied to `a`. `Omega tau` is the typing license for base-algebra
elements to serve as the recurrence argument of a recurrence whose
recursive results carry type `tau`. -/
def RType.omega (a : RType) : RType := FreeAlg.mk RTypeShape.omega ![a]

/-- The top constructor shape of an r-type: `o` for the base type,
`arrow` for a function type, `omega` for an `Omega` type. -/
def RType.shape (t : RType) : RTypeShape := PolyFix.index t

@[simp] theorem RType.shape_o : RType.o.shape = RTypeShape.o := rfl

@[simp] theorem RType.shape_arrow (a b : RType) :
    (RType.arrow a b).shape = RTypeShape.arrow := rfl

@[simp] theorem RType.shape_omega (a : RType) :
    (RType.omega a).shape = RTypeShape.omega := rfl

/-- Injectivity of the children of a free-algebra node at a fixed shape:
two nodes with the same shape are equal exactly when their children agree.
A fact local to the decision procedures on `RType`. -/
theorem RType.mk_children_inj {b : rTypeSig.B}
    {c c' : Fin (rTypeSig.ar b) → RType}
    (h : FreeAlg.mk b c = FreeAlg.mk b c') : c = c' := by
  have h' : (@PolyFix.mk PUnit rTypeSig.polyEndo PUnit.unit b c) =
      @PolyFix.mk PUnit rTypeSig.polyEndo PUnit.unit b c' := h
  rw [PolyFix.mk.injEq] at h'
  simpa using h'

@[simp] theorem RType.arrow_eq_arrow {a b c d : RType} :
    RType.arrow a b = RType.arrow c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have hc : (![a, b] : Fin 2 → RType) = ![c, d] := RType.mk_children_inj h
    exact ⟨congrFun hc 0, congrFun hc 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem RType.omega_eq_omega {a b : RType} :
    RType.omega a = RType.omega b ↔ a = b := by
  constructor
  · intro h
    have hc : (![a] : Fin 1 → RType) = ![b] := RType.mk_children_inj h
    exact congrFun hc 0
  · rintro rfl
    rfl

instance : DecidableEq RType := fun x =>
  PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} x => (y : RType) → Decidable (x = y))
    (fun i childx ihx y =>
      match y with
      | PolyFix.mk _ j childy => by
        letI : DecidableEq
            (polyBetweenIndex PUnit PUnit rTypeSig.polyEndo PUnit.unit) :=
          (inferInstance : DecidableEq RTypeShape)
        exact
          if hij : i = j then by
            subst hij
            let cx : Fin (rTypeSig.ar i) → RType := childx
            let cy : Fin (rTypeSig.ar i) → RType := childy
            letI : DecidablePred fun e => cx e = cy e := fun e => ihx e (cy e)
            haveI : Decidable (cx = cy) :=
              decidable_of_iff (∀ e, cx e = cy e) funext_iff.symm
            exact decidable_of_iff (cx = cy)
              ⟨fun h => congrArg (PolyFix.mk PUnit.unit i) h,
                RType.mk_children_inj⟩
          else
            isFalse fun h => hij (congrArg PolyFix.index h)) x

/-- Object sorts (Leivant III section 2.3): `o` and every `Omega tau`,
equivalently the r-types whose top shape is `o` or `omega`. `Omega tau` is
the typing license for base-algebra elements to serve as the recurrence
argument of a recurrence whose recursive results carry type `tau`. -/
def RType.IsObj (t : RType) : Prop :=
  t.shape = RTypeShape.o ∨ t.shape = RTypeShape.omega

instance : DecidablePred RType.IsObj := fun t => by
  unfold RType.IsObj
  infer_instance

/-- The tower sorts `Omega^m o` (Leivant III section 2.4(3)): the `m`-fold
iterate of `omega` on `o`. -/
def RType.tower : Nat → RType
  | 0 => RType.o
  | n + 1 => RType.omega (RType.tower n)

/-- Every tower sort `Omega^m o` is an object sort (Leivant III section
2.4(3) with section 2.3): `o` at `m = 0`, an `Omega` type otherwise. -/
theorem RType.tower_isObj (m : Nat) : (RType.tower m).IsObj := by
  cases m with
  | zero => exact Or.inl rfl
  | succ n => exact Or.inr rfl

/-- The denotation of an r-type over a carrier (Leivant III section 2.7):
every object sort — `o` and every `Omega tau`, regardless of `tau` —
denotes a copy of the carrier, and each arrow denotes the function space
of the denotations of its subterms. `Omega` adds typing license only, so
it does not change the denotation. Realized by the dependent eliminator
`PolyFix.ind` (decision 8). Novel packaging. -/
def RType.interp (carrier : Type) (t : RType) : Type :=
  PolyFix.ind (P := rTypeSig.polyEndo) (motive := fun {_} _ => Type)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => carrier
      | RTypeShape.arrow, _, ih =>
        ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)) →
          ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))
      | RTypeShape.omega, _, _ => carrier) t

/-- The denotation of an object sort is a copy of the carrier (Leivant III
section 2.7): for any `s` with `s.IsObj`, `RType.interp C s = C`. -/
theorem RType.interp_isObj (C : Type) {s : RType} (h : s.IsObj) :
    RType.interp C s = C := by
  rcases s with ⟨_, i, children⟩
  rcases h with h | h <;> (simp only [RType.shape, PolyFix.index] at h; subst h; rfl)

/-- The congruence of the denotation along a base-carrier equivalence
(Leivant III section 2.7): every object sort transports by `e`, and each
arrow by `Equiv.arrowCongr` of the equivalences on its subterms. Realized by
the dependent eliminator `PolyFix.ind` (decision 8), following
`RType.interp`'s pattern. -/
def RType.interpCongr {C D : Type} (e : C ≃ D) (t : RType) :
    RType.interp C t ≃ RType.interp D t :=
  PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} t => RType.interp C t ≃ RType.interp D t)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => e
      | RTypeShape.arrow, _, ih =>
        Equiv.arrowCongr (ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)))
          (ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)))
      | RTypeShape.omega, _, _ => e) t

/-- The denotation congruence at an object sort is the base equivalence, read
through the object-sort denotation equalities (Leivant III section 2.7): for
`s.IsObj`, `RType.interpCongr e s` transports to `e`. -/
theorem RType.interpCongr_isObj {C D : Type} (e : C ≃ D) {s : RType} (h : s.IsObj)
    (w : RType.interp C s) :
    cast (RType.interp_isObj D h) (RType.interpCongr e s w)
      = e (cast (RType.interp_isObj C h) w) := by
  rcases s with ⟨_, i, children⟩
  rcases h with h | h <;>
    (simp only [RType.shape, PolyFix.index] at h; subst h; rfl)

/-- The base object sort `o` as an object-sort witness. -/
def oObj : { s : RType // RType.IsObj s } := ⟨RType.o, Or.inl rfl⟩

/-- The tower-sort predicate (Leivant III section 2.4(3)): `t` is a tower sort
`Omega^m o`, equivalently a chain of `Omega`s terminating in the base type `o`.
Unlike `RType.IsObj`, which inspects only the top shape, `IsTower` recurses the
whole spine: `o` qualifies, an `arrow` does not, and `Omega tau` qualifies
exactly when `tau` does. Realized by the dependent eliminator `PolyFix.ind`
(decision 8), following `RType.interp`'s pattern. Novel packaging. -/
def RType.IsTower (t : RType) : Prop :=
  PolyFix.ind (P := rTypeSig.polyEndo) (motive := fun {_} _ => Prop)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => True
      | RTypeShape.arrow, _, _ => False
      | RTypeShape.omega, _, ih =>
        ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega))) t

instance : DecidablePred RType.IsTower := fun t =>
  PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} t => Decidable (RType.IsTower t))
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => isTrue True.intro
      | RTypeShape.arrow, _, _ => isFalse (fun h => h)
      | RTypeShape.omega, _, ih =>
        ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega))) t

/-- Every tower sort `Omega^m o` satisfies `RType.IsTower` (Leivant III section
2.4(3)): `o` at `m = 0`, and `Omega` of a tower sort at `m + 1`. -/
theorem RType.tower_isTower (m : Nat) : (RType.tower m).IsTower := by
  induction m with
  | zero => exact True.intro
  | succ n ih => exact ih

/-- The omega-free (simple-type) predicate (Leivant III section 4.2: "the
types are not ramified"): `o` is simple, `arrow a b` is simple exactly when
both `a` and `b` are, and no `omega tau` is simple. Unlike `RType.IsTower`'s
`arrow` case, which contributes no recursive obligation, `arrow` here recurses
on both children. Realized by the dependent eliminator `PolyFix.ind`
(decision 8), following `RType.IsTower`'s pattern. Novel packaging. -/
def RType.IsSimple (t : RType) : Prop :=
  PolyFix.ind (P := rTypeSig.polyEndo) (motive := fun {_} _ => Prop)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => True
      | RTypeShape.arrow, _, ih =>
        ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)) ∧
          ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))
      | RTypeShape.omega, _, _ => False) t

instance : DecidablePred RType.IsSimple := fun t =>
  PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} t => Decidable (RType.IsSimple t))
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => isTrue True.intro
      | RTypeShape.arrow, _, ih =>
        match ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)),
            ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)) with
        | isTrue h0, isTrue h1 => isTrue ⟨h0, h1⟩
        | isFalse h0, _ => isFalse (fun h => h0 h.1)
        | isTrue _, isFalse h1 => isFalse (fun h => h1 h.2)
      | RTypeShape.omega, _, _ => isFalse (fun h => h)) t

/-- The base type `o` is simple (Leivant III section 4.2). -/
theorem RType.o_isSimple : RType.o.IsSimple := True.intro

/-- `arrow a b` is simple exactly when both `a` and `b` are (Leivant III
section 4.2). -/
theorem RType.arrow_isSimple_iff {a b : RType} :
    (RType.arrow a b).IsSimple ↔ a.IsSimple ∧ b.IsSimple := Iff.rfl

end GebLean.Ramified

import GebLean.LawvereERLex
import GebLean.LawvereERQuot
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
-- 91 chars (external mathlib path)
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Embedding `Δ : LawvereERCat ⥤ LawvereERLexCat`

Defines the canonical embedding of `LawvereERCat`
(the Lawvere theory of elementary recursive
functions) into `LawvereERLexCat` (its finite-limit
completion via decidable subobjects), sending arity
`n` to the object `(n, ⊤)` cut out by the always-true
predicate.
-/

namespace GebLean

open CategoryTheory

/-- Object map of the embedding: arity `n` is sent
to `(n, ⊤)`, the object whose predicate is the
constantly-true predicate at arity `n`. -/
def erDelta.obj (n : LawvereERCat) : LawvereERLexCat :=
  { arity := n, pred := ERBoolPredE.alwaysTrue n }

/-- The underlying arity of `erDelta.obj n` is `n`. -/
@[simp] theorem erDelta.obj_arity (n : ℕ) :
    (erDelta.obj n).arity = n := rfl

/-- Raw morphism lift: an `ERMorN n m` becomes an
`ERLexMorN` from `(n, ⊤)` to `(m, ⊤)`.  The respect
proof is trivial because the target predicate `⊤`
always evaluates to `1`. -/
def erDeltaRaw {n m : ℕ} (f : ERMorN n m) :
    ERLexMorN (erDelta.obj n) (erDelta.obj m) :=
  ⟨f, fun _ _ => rfl⟩

/-- Morphism map of the embedding: lift through the
quotient.  Well-defined because full extensional
equality of `ERMorN` tuples implies their lifted
forms agree on `⊤`-satisfying contexts. -/
def erDelta.map {n m : ℕ} (f : ERMorNQuo n m) :
    ERLexMorNQuo (erDelta.obj n) (erDelta.obj m) :=
  Quotient.lift
    (s := erMorNSetoid n m)
    (fun f' =>
      Quotient.mk
        (erLexMorNSetoid (erDelta.obj n)
          (erDelta.obj m))
        (erDeltaRaw f'))
    (fun _ _ h =>
      Quotient.sound
        (s := erLexMorNSetoid (erDelta.obj n)
          (erDelta.obj m))
        (fun ctx _ => h ctx))
    f

/-- Δ preserves identity morphisms. -/
theorem erDelta.map_id (n : LawvereERCat) :
    erDelta.map (ERMorNQuo.id n) =
      ERLexMorNQuo.id (erDelta.obj n) := by
  rfl

/-- Δ preserves composition of morphisms. -/
theorem erDelta.map_comp {n m k : ℕ}
    (f : ERMorNQuo n m) (g : ERMorNQuo m k) :
    erDelta.map (ERMorNQuo.comp f g) =
      ERLexMorNQuo.comp (erDelta.map f)
        (erDelta.map g) := by
  refine Quotient.ind₂ ?_ f g
  intro f_raw g_raw
  rfl

/-- The full and faithful embedding
`LawvereERCat ⥤ LawvereERLexCat`. -/
def erDeltaFunctor :
    LawvereERCat ⥤ LawvereERLexCat where
  obj := erDelta.obj
  map := erDelta.map
  map_id := erDelta.map_id
  map_comp := erDelta.map_comp

/-- Δ is faithful: distinct ER morphism classes give
distinct `LawvereERLexCat` morphism classes.
Immediate because the source-restricted setoid on
the always-true predicate `⊤` reduces to full
extensional equality. -/
instance : erDeltaFunctor.Faithful where
  map_injective {n m} {f g} h := by
    induction f using Quotient.ind with
    | _ f_raw =>
      induction g using Quotient.ind with
      | _ g_raw =>
        apply Quotient.sound
          (s := erMorNSetoid n m)
        intro ctx
        have hrel := Quotient.exact
          (s := erLexMorNSetoid (erDelta.obj n)
            (erDelta.obj m)) h
        exact hrel ctx rfl

/-- Preimage of a `LawvereERLexCat` morphism between
trivially-cut-out objects.  Lifts through the
quotient by extracting the underlying `ERMorN` tuple;
well-defined because source-restricted equivalence
under `⊤` reduces to full extensional equality. -/
def erDelta.preimage {n m : ℕ}
    (h : ERLexMorNQuo (erDelta.obj n)
      (erDelta.obj m)) :
    ERMorNQuo n m :=
  Quotient.lift
    (s := erLexMorNSetoid (erDelta.obj n)
      (erDelta.obj m))
    (fun h_raw =>
      Quotient.mk (erMorNSetoid n m) h_raw.val)
    (fun _ _ hrel =>
      Quotient.sound
        (s := erMorNSetoid n m)
        (fun ctx => hrel ctx rfl))
    h

/-- The preimage is a section of `Δ.map`: applying
Δ to the preimage of `h` recovers `h`. -/
theorem erDelta.map_preimage {n m : ℕ}
    (h : ERLexMorNQuo (erDelta.obj n)
      (erDelta.obj m)) :
    erDelta.map (erDelta.preimage h) = h := by
  induction h using Quotient.ind with
  | _ h_raw =>
    apply Quotient.sound
      (s := erLexMorNSetoid (erDelta.obj n)
        (erDelta.obj m))
    intro ctx _
    rfl

/-- Δ is full: every `LawvereERLexCat` morphism
between trivially-cut-out objects comes from a
unique `LawvereERCat` morphism (uniqueness via
faithfulness; existence via `erDelta.preimage`). -/
instance : erDeltaFunctor.Full where
  map_surjective h :=
    ⟨erDelta.preimage h, erDelta.map_preimage h⟩

/-! ## Preservation of finite products

`Δ` sends the chosen terminal `0 : LawvereERCat` to
`LexObj.terminal` literally, and the chosen binary
product `n + m` to `LexObj.prod (Δ n) (Δ m)` up to
equality of predicates.  Hence `Δ` preserves both
the chosen terminal and chosen binary products,
which gives `PreservesFiniteProducts`. -/

/-- Δ sends the source terminal `0` literally to
the target chosen terminal `LexObj.terminal`. -/
@[simp] theorem erDelta.obj_terminal :
    erDelta.obj (0 : LawvereERCat) =
      LexObj.terminal :=
  rfl

/-- Δ sends the source binary product `n + m`
literally to the target chosen product
`LexObj.prod (Δ n) (Δ m)`. -/
theorem erDelta.obj_prod (n m : ℕ) :
    erDelta.obj (n + m) =
      LexObj.prod (erDelta.obj n) (erDelta.obj m) := by
  change LexObj.mk (n + m)
      (ERBoolPredE.alwaysTrue (n + m)) =
    LexObj.mk (n + m)
      (ERBoolPredE.and
        (ERBoolPredE.alwaysTrue n)
        (ERBoolPredE.alwaysTrue m))
  congr 1
  apply ERBoolPredE.eval_injective
  intro ctx
  rw [ERBoolPredE.alwaysTrue_eval,
      ERBoolPredE.and_eval,
      ERBoolPredE.alwaysTrue_eval,
      ERBoolPredE.alwaysTrue_eval]

/-- Δ preserves the source terminal object.
Proved by mapping the source's chosen terminal cone
to the target's chosen terminal cone, using that
`erDelta.obj 0 = LexObj.terminal` literally. -/
instance :
    Limits.PreservesLimit
      (Functor.empty.{0} LawvereERCat) erDeltaFunctor :=
  Limits.preservesLimit_of_preserves_limit_cone
    (chosenTerminalIsTerminal (C := LawvereERCat))
    ((Limits.isLimitMapConeEmptyConeEquiv
        erDeltaFunctor 0).symm
      (chosenTerminalIsTerminal
        (C := LawvereERLexCat)))

/-- Δ preserves limits over the empty discrete
diagram. -/
instance :
    Limits.PreservesLimitsOfShape
      (Discrete PEmpty.{1}) erDeltaFunctor :=
  Limits.preservesLimitsOfShape_pempty_of_preservesTerminal
    erDeltaFunctor

/-! ### Δ preserves binary products

The image of the source chosen product `(n, n+m, m)`
cone under Δ is, via `erDelta.obj_prod`, the target's
chosen product `(Δ n, LexObj.prod (Δ n) (Δ m), Δ m)`
cone.  We establish `PreservesLimit (pair n m)` by
constructing an `IsLimit` on the mapped binary fan
directly, delegating to the target's chosen product
after transporting along the object equality. -/

/-- Pair-lift from the image of `Δ` directly: given
any morphisms into `Δ n` and `Δ m` from `Z` in
`LawvereERLexCat`, produce a morphism into
`Δ (n + m)`.  The underlying tuple is the standard
pair; respect holds because `Δ (n + m)` has the
always-true predicate. -/
def erDelta.pairLiftRaw {n m : ℕ}
    {Z : LexObj}
    (f : ERLexMorN Z (erDelta.obj n))
    (g : ERLexMorN Z (erDelta.obj m)) :
    ERLexMorN Z (erDelta.obj (n + m)) :=
  ⟨ERMorN.pair f.val g.val, fun _ _ => rfl⟩

/-- Quotient version of `erDelta.pairLiftRaw`. -/
def erDelta.pairLift' {n m : ℕ}
    {Z : LexObj}
    (f : ERLexMorNQuo Z (erDelta.obj n))
    (g : ERLexMorNQuo Z (erDelta.obj m)) :
    ERLexMorNQuo Z (erDelta.obj (n + m)) :=
  Quotient.lift₂
    (s₁ := erLexMorNSetoid Z (erDelta.obj n))
    (s₂ := erLexMorNSetoid Z (erDelta.obj m))
    (fun f' g' =>
      Quotient.mk
        (erLexMorNSetoid Z (erDelta.obj (n + m)))
        (erDelta.pairLiftRaw f' g'))
    (fun _ _ _ _ hf hg =>
      Quotient.sound
        (s := erLexMorNSetoid Z
          (erDelta.obj (n + m)))
        (fun ctx hctx => by
          change (ERMorN.pair _ _).interp ctx =
            (ERMorN.pair _ _).interp ctx
          rw [ERMorN.interp_pair,
              ERMorN.interp_pair]
          funext i
          split_ifs with h
          · exact congrFun (hf ctx hctx)
              ⟨i.val, h⟩
          · exact congrFun (hg ctx hctx)
              ⟨i.val - n, by
                have hi : i.val <
                  (erDelta.obj (n + m)).arity :=
                  i.isLt
                simp only [erDelta.obj_arity] at hi
                change i.val - n < m
                omega⟩))
    f g

/-- Composing `pairLift'` with `Δ.map fst` recovers
the first component. -/
theorem erDelta.pairLift'_fst {n m : ℕ}
    {Z : LexObj}
    (f : ERLexMorNQuo Z (erDelta.obj n))
    (g : ERLexMorNQuo Z (erDelta.obj m)) :
    ERLexMorNQuo.comp (erDelta.pairLift' f g)
        (erDelta.map
          (ERMorNQuo.fst (n := n) (m := m)))
      = f := by
  refine Quotient.ind₂
    (motive := fun f g =>
      ERLexMorNQuo.comp (erDelta.pairLift' f g)
          (erDelta.map ERMorNQuo.fst) = f)
    ?_ f g
  intro f_raw g_raw
  apply Quotient.sound
    (s := erLexMorNSetoid Z (erDelta.obj n))
  intro ctx hctx
  change (ERMorN.comp (ERMorN.pair _ _)
      ERMorN.fst).interp ctx = f_raw.val.interp ctx
  rw [ERMorN.interp_comp, ERMorN.interp_pair,
      ERMorN.interp_fst]
  funext i
  dsimp only [erDelta.obj] at *
  have h : i.val < n := i.isLt
  rw [dif_pos h]
  rfl

/-- Composing `pairLift'` with `Δ.map snd` recovers
the second component. -/
theorem erDelta.pairLift'_snd {n m : ℕ}
    {Z : LexObj}
    (f : ERLexMorNQuo Z (erDelta.obj n))
    (g : ERLexMorNQuo Z (erDelta.obj m)) :
    ERLexMorNQuo.comp (erDelta.pairLift' f g)
        (erDelta.map
          (ERMorNQuo.snd (n := n) (m := m)))
      = g := by
  refine Quotient.ind₂
    (motive := fun f g =>
      ERLexMorNQuo.comp (erDelta.pairLift' f g)
          (erDelta.map ERMorNQuo.snd) = g)
    ?_ f g
  intro f_raw g_raw
  apply Quotient.sound
    (s := erLexMorNSetoid Z (erDelta.obj m))
  intro ctx hctx
  change (ERMorN.comp (ERMorN.pair _ _)
      ERMorN.snd).interp ctx = g_raw.val.interp ctx
  rw [ERMorN.interp_comp, ERMorN.interp_pair,
      ERMorN.interp_snd]
  funext i
  have hi_lt : i.val < m := by
    have := i.isLt
    simp only [erDelta.obj_arity] at this
    exact this
  have h : ¬ (n + i.val < n) := by omega
  rw [dif_neg h]
  have hi : (⟨n + i.val - n, by omega⟩ :
      Fin m) = ⟨i.val, hi_lt⟩ := by
    apply Fin.ext
    change n + i.val - n = i.val
    omega
  rw [hi]
  rfl

/-- Uniqueness of the pair lift. -/
theorem erDelta.pairLift'_uniq {n m : ℕ}
    {Z : LexObj}
    (f : ERLexMorNQuo Z (erDelta.obj n))
    (g : ERLexMorNQuo Z (erDelta.obj m))
    (h : ERLexMorNQuo Z (erDelta.obj (n + m)))
    (hf : ERLexMorNQuo.comp h
        (erDelta.map ERMorNQuo.fst) = f)
    (hg : ERLexMorNQuo.comp h
        (erDelta.map ERMorNQuo.snd) = g) :
    h = erDelta.pairLift' f g := by
  subst hf hg
  refine Quotient.ind
    (motive := fun h =>
      h = erDelta.pairLift'
        (ERLexMorNQuo.comp h
          (erDelta.map ERMorNQuo.fst))
        (ERLexMorNQuo.comp h
          (erDelta.map ERMorNQuo.snd)))
    ?_ h
  intro h_raw
  apply Quotient.sound
    (s := erLexMorNSetoid Z (erDelta.obj (n + m)))
  intro ctx hctx
  change h_raw.val.interp ctx =
    (ERMorN.pair
      (ERMorN.comp h_raw.val ERMorN.fst)
      (ERMorN.comp h_raw.val ERMorN.snd)).interp ctx
  rw [ERMorN.interp_pair]
  funext i
  have hi_lt : i.val < n + m := by
    have := i.isLt
    simp only [erDelta.obj_arity] at this
    exact this
  by_cases hlt : i.val < n
  · rw [dif_pos hlt]
    change (h_raw.val i).interp ctx =
      (ERMor1.comp (ERMorN.fst ⟨i.val, hlt⟩)
        h_raw.val).interp ctx
    rw [ERMor1.interp_comp]
    change (h_raw.val i).interp ctx =
      (ERMor1.proj ⟨i.val, by omega⟩).interp _
    rw [ERMor1.interp_proj]
    change (h_raw.val i).interp ctx =
      (h_raw.val ⟨i.val, hi_lt⟩).interp ctx
    have : i = ⟨i.val, hi_lt⟩ := by
      apply Fin.ext; rfl
    rw [← this]
  · rw [dif_neg hlt]
    change (h_raw.val i).interp ctx =
      (ERMor1.comp (ERMorN.snd ⟨i.val - n, by
        have := i.isLt
        simp only [erDelta.obj_arity] at this
        omega⟩) h_raw.val).interp ctx
    rw [ERMor1.interp_comp]
    change (h_raw.val i).interp ctx =
      (ERMor1.proj ⟨n + (i.val - n), by omega⟩).interp
        _
    rw [ERMor1.interp_proj]
    change (h_raw.val i).interp ctx =
      (h_raw.val ⟨n + (i.val - n), by omega⟩).interp
        ctx
    have : i = ⟨n + (i.val - n), by omega⟩ := by
      apply Fin.ext
      change i.val = n + (i.val - n)
      omega
    rw [← this]

/-- The image of the source chosen binary product
cone at `(n, m)` under Δ is a limit cone. -/
def erDelta.mapBinaryFanIsLimit (n m : ℕ) :
    Limits.IsLimit
      (Limits.BinaryFan.mk (X := erDelta.obj n)
        (Y := erDelta.obj m)
        (P := erDelta.obj (n + m))
        (erDelta.map
          (ERMorNQuo.fst (n := n) (m := m)))
        (erDelta.map
          (ERMorNQuo.snd (n := n) (m := m)))) :=
  Limits.BinaryFan.isLimitMk
    (fun s => erDelta.pairLift' s.fst s.snd)
    (fun s => erDelta.pairLift'_fst s.fst s.snd)
    (fun s => erDelta.pairLift'_snd s.fst s.snd)
    (fun s m' hf hs =>
      erDelta.pairLift'_uniq s.fst s.snd m' hf hs)

/-- Δ preserves the source chosen binary product at
`(n, m)`. -/
instance (n m : ℕ) :
    Limits.PreservesLimit (Limits.pair n m)
      erDeltaFunctor :=
  Limits.preservesLimit_of_preserves_limit_cone
    (Limits.BinaryFan.isLimitMk
      (fun s =>
        (lawvereERProduct n m).lift s.fst s.snd)
      (fun s =>
        (lawvereERProduct n m).lift_fst s.fst s.snd)
      (fun s =>
        (lawvereERProduct n m).lift_snd s.fst s.snd)
      (fun s m' hf hs =>
        (lawvereERProduct n m).lift_uniq
          s.fst s.snd m' hf hs) :
        Limits.IsLimit (Limits.BinaryFan.mk
          (ERMorNQuo.fst (n := n) (m := m))
          ERMorNQuo.snd))
    ((Limits.isLimitMapConeBinaryFanEquiv
        erDeltaFunctor _ _).symm
      (erDelta.mapBinaryFanIsLimit n m))

/-- Δ preserves limits over the walking-pair
discrete diagram. -/
instance :
    Limits.PreservesLimitsOfShape
      (Discrete Limits.WalkingPair) erDeltaFunctor
    where
  preservesLimit {K} := by
    have : Limits.PreservesLimit
        (Limits.pair (K.obj ⟨Limits.WalkingPair.left⟩)
          (K.obj ⟨Limits.WalkingPair.right⟩))
        erDeltaFunctor := inferInstance
    exact Limits.preservesLimit_of_iso_diagram
      erDeltaFunctor
      (Limits.diagramIsoPair K).symm

/-- Δ preserves finite products. -/
instance :
    Limits.PreservesFiniteProducts erDeltaFunctor :=
  Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal
    erDeltaFunctor

end GebLean

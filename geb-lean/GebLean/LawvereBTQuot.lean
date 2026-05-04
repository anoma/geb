import GebLean.LawvereBTEq

/-!
# Quotient Lawvere Theory of Binary Trees

Defines the quotient of the syntactic Lawvere theory
`LawvereBTCat` by the congruence relation `btMorRel`,
yielding a category `LawvereBTQuotCat` whose morphisms
are equivalence classes of `BTMorN` tuples.

The quotient is taken on entire morphism tuples
(`BTMorN n m = Fin m → BTMor1 n`), using the
pointwise extension of `btMorRel` as the equivalence
relation.  Composition lifts via `Quotient.lift₂` and
the category laws follow from the syntactic laws in
`LawvereBT.lean` via `Quotient.ind`.
-/

namespace GebLean

open CategoryTheory

/-- The setoid on `BTMorN n m` induced by pointwise
`btMorRel`: two morphism tuples are related when each
component pair is related. -/
def btMorNSetoid (n m : ℕ) :
    Setoid (BTMorN n m) where
  r f g := ∀ i, btMorRel n (f i) (g i)
  iseqv := {
    refl := fun f i => btMorRel.refl (f i)
    symm := fun h i => btMorRel.symm (h i)
    trans := fun h1 h2 i =>
      btMorRel.trans (h1 i) (h2 i)
  }

/-- Quotient morphism type for the Lawvere theory of
binary trees: equivalence classes of `BTMorN n m`
tuples under pointwise `btMorRel`. -/
def BTMorNQuo (n m : ℕ) : Type :=
  Quotient (btMorNSetoid n m)

/-- The identity morphism in the quotient category:
the equivalence class of the tuple of projections. -/
def BTMorNQuo.id (n : ℕ) : BTMorNQuo n n :=
  Quotient.mk (btMorNSetoid n n) (BTMorN.id n)

/-- Composition of quotient morphisms, lifted from
`BTMorN.comp` via `Quotient.lift₂`.  Well-definedness
follows from `subst_cong`. -/
def BTMorNQuo.comp {n m k : ℕ}
    (f : BTMorNQuo n m) (g : BTMorNQuo m k) :
    BTMorNQuo n k :=
  Quotient.lift₂
    (s₁ := btMorNSetoid n m)
    (s₂ := btMorNSetoid m k)
    (fun f' g' =>
      Quotient.mk (btMorNSetoid n k)
        (BTMorN.comp f' g'))
    (fun _ _ _ _ hf hg =>
      Quotient.sound
        (s := btMorNSetoid n k)
        (fun j => subst_cong (hg j) hf))
    f g

/-- Left identity: `comp (id n) f = f`. -/
theorem BTMorNQuo.id_comp {n m : ℕ}
    (f : BTMorNQuo n m) :
    BTMorNQuo.comp (BTMorNQuo.id n) f = f :=
  Quotient.ind
    (motive := fun f =>
      BTMorNQuo.comp (BTMorNQuo.id n) f = f)
    (fun f_raw => by
      change Quotient.mk _ (BTMorN.comp
        (BTMorN.id n) f_raw) =
        Quotient.mk _ f_raw
      rw [BTMorN.id_comp])
    f

/-- Right identity: `comp f (id m) = f`. -/
theorem BTMorNQuo.comp_id {n m : ℕ}
    (f : BTMorNQuo n m) :
    BTMorNQuo.comp f (BTMorNQuo.id m) = f :=
  Quotient.ind
    (motive := fun f =>
      BTMorNQuo.comp f (BTMorNQuo.id m) = f)
    (fun f_raw => by
      change Quotient.mk _ (BTMorN.comp
        f_raw (BTMorN.id m)) =
        Quotient.mk _ f_raw
      rw [BTMorN.comp_id])
    f

/-- Associativity of composition in the quotient. -/
theorem BTMorNQuo.comp_assoc {n m k l : ℕ}
    (f : BTMorNQuo n m)
    (g : BTMorNQuo m k)
    (h : BTMorNQuo k l) :
    BTMorNQuo.comp (BTMorNQuo.comp f g) h =
      BTMorNQuo.comp f (BTMorNQuo.comp g h) :=
  Quotient.ind
    (motive := fun f =>
      ∀ (g : BTMorNQuo m k)
        (h : BTMorNQuo k l),
        BTMorNQuo.comp
          (BTMorNQuo.comp f g) h =
          BTMorNQuo.comp f
            (BTMorNQuo.comp g h))
    (fun f_raw =>
      Quotient.ind
        (motive := fun g =>
          ∀ (h : BTMorNQuo k l),
            BTMorNQuo.comp
              (BTMorNQuo.comp
                (Quotient.mk _ f_raw) g) h =
              BTMorNQuo.comp
                (Quotient.mk _ f_raw)
                (BTMorNQuo.comp g h))
        (fun g_raw =>
          Quotient.ind
            (motive := fun h =>
              BTMorNQuo.comp
                (BTMorNQuo.comp
                  (Quotient.mk _ f_raw)
                  (Quotient.mk _ g_raw)) h =
                BTMorNQuo.comp
                  (Quotient.mk _ f_raw)
                  (BTMorNQuo.comp
                    (Quotient.mk _ g_raw) h))
            (fun h_raw => by
              change Quotient.mk _
                (BTMorN.comp
                  (BTMorN.comp f_raw g_raw)
                  h_raw) =
                Quotient.mk _
                  (BTMorN.comp f_raw
                    (BTMorN.comp g_raw h_raw))
              rw [BTMorN.comp_assoc])))
    f g h

/-- The quotient Lawvere theory of binary trees.
Objects are natural numbers (powers of the generating
object).  Morphisms are equivalence classes of
`BTMorN` tuples under the congruence relation
`btMorRel`. -/
def LawvereBTQuotCat := ℕ

instance (n : ℕ) : OfNat LawvereBTQuotCat n :=
  ⟨(n : ℕ)⟩

instance : BEq LawvereBTQuotCat := inferInstanceAs (BEq ℕ)
instance : DecidableEq LawvereBTQuotCat :=
  inferInstanceAs (DecidableEq ℕ)

instance : CategoryStruct LawvereBTQuotCat where
  Hom := BTMorNQuo
  id n := BTMorNQuo.id n
  comp f g := BTMorNQuo.comp f g

instance : Category LawvereBTQuotCat where
  id_comp := BTMorNQuo.id_comp
  comp_id := BTMorNQuo.comp_id
  assoc := BTMorNQuo.comp_assoc

/-- The terminal morphism in the quotient category:
the equivalence class of the empty-codomain
morphism. -/
def BTMorNQuo.terminal (n : ℕ) :
    BTMorNQuo n 0 :=
  Quotient.mk (btMorNSetoid n 0)
    (BTMorN.terminal n)

/-- Any quotient morphism to `0` equals the
terminal morphism. -/
theorem BTMorNQuo.terminal_uniq {n : ℕ}
    (f : BTMorNQuo n 0) :
    f = BTMorNQuo.terminal n :=
  Quotient.ind
    (motive := fun f =>
      f = BTMorNQuo.terminal n)
    (fun _ => Quotient.sound
      (s := btMorNSetoid n 0)
      (fun i => i.elim0))
    f

/-- First projection in the quotient category. -/
def BTMorNQuo.fst {n m : ℕ} :
    BTMorNQuo (n + m) n :=
  Quotient.mk (btMorNSetoid (n + m) n)
    BTMorN.fst

/-- Second projection in the quotient category. -/
def BTMorNQuo.snd {n m : ℕ} :
    BTMorNQuo (n + m) m :=
  Quotient.mk (btMorNSetoid (n + m) m)
    BTMorN.snd

/-- Pairing in the quotient category, lifted from
`BTMorN.pair` via `Quotient.lift₂`. -/
def BTMorNQuo.pair {k n m : ℕ}
    (f : BTMorNQuo k n)
    (g : BTMorNQuo k m) :
    BTMorNQuo k (n + m) :=
  Quotient.lift₂
    (s₁ := btMorNSetoid k n)
    (s₂ := btMorNSetoid k m)
    (fun f_raw g_raw =>
      Quotient.mk (btMorNSetoid k (n + m))
        (BTMorN.pair f_raw g_raw))
    (fun f1 g1 f2 g2 hf hg =>
      Quotient.sound
        (s := btMorNSetoid k (n + m))
        (fun i => by
          unfold BTMorN.pair
          split_ifs with h
          · exact hf ⟨i.val, h⟩
          · exact hg ⟨i.val - n, by omega⟩))
    f g

/-- Composing pairing with the first projection
recovers the first component. -/
theorem BTMorNQuo.pair_fst {k n m : ℕ}
    (f : BTMorNQuo k n)
    (g : BTMorNQuo k m) :
    BTMorNQuo.comp (BTMorNQuo.pair f g)
      BTMorNQuo.fst = f :=
  Quotient.ind₂
    (motive := fun f g =>
      BTMorNQuo.comp (BTMorNQuo.pair f g)
        BTMorNQuo.fst = f)
    (fun f_raw g_raw => by
      change Quotient.mk _
        (BTMorN.comp
          (BTMorN.pair f_raw g_raw)
          BTMorN.fst) =
        Quotient.mk _ f_raw
      rw [BTMorN.pair_fst])
    f g

/-- Composing pairing with the second projection
recovers the second component. -/
theorem BTMorNQuo.pair_snd {k n m : ℕ}
    (f : BTMorNQuo k n)
    (g : BTMorNQuo k m) :
    BTMorNQuo.comp (BTMorNQuo.pair f g)
      BTMorNQuo.snd = g :=
  Quotient.ind₂
    (motive := fun f g =>
      BTMorNQuo.comp (BTMorNQuo.pair f g)
        BTMorNQuo.snd = g)
    (fun f_raw g_raw => by
      change Quotient.mk _
        (BTMorN.comp
          (BTMorN.pair f_raw g_raw)
          BTMorN.snd) =
        Quotient.mk _ g_raw
      rw [BTMorN.pair_snd])
    f g

/-- Uniqueness of pairing in the quotient: any
morphism whose compositions with the projections
yield `f` and `g` equals `pair f g`. -/
theorem BTMorNQuo.pair_uniq {k n m : ℕ}
    (f : BTMorNQuo k n)
    (g : BTMorNQuo k m)
    (h : BTMorNQuo k (n + m))
    (hfst : BTMorNQuo.comp h
      BTMorNQuo.fst = f)
    (hsnd : BTMorNQuo.comp h
      BTMorNQuo.snd = g) :
    h = BTMorNQuo.pair f g :=
  Quotient.ind
    (motive := fun h =>
      ∀ (f : BTMorNQuo k n)
        (g : BTMorNQuo k m),
        BTMorNQuo.comp h BTMorNQuo.fst = f →
        BTMorNQuo.comp h BTMorNQuo.snd = g →
        h = BTMorNQuo.pair f g)
    (fun h_raw =>
      Quotient.ind
        (motive := fun f =>
          ∀ (g : BTMorNQuo k m),
            BTMorNQuo.comp
              (Quotient.mk _ h_raw)
              BTMorNQuo.fst = f →
            BTMorNQuo.comp
              (Quotient.mk _ h_raw)
              BTMorNQuo.snd = g →
            Quotient.mk _ h_raw =
              BTMorNQuo.pair f g)
        (fun f_raw =>
          Quotient.ind
            (motive := fun g =>
              BTMorNQuo.comp
                (Quotient.mk _ h_raw)
                BTMorNQuo.fst =
                Quotient.mk _ f_raw →
              BTMorNQuo.comp
                (Quotient.mk _ h_raw)
                BTMorNQuo.snd = g →
              Quotient.mk _ h_raw =
                BTMorNQuo.pair
                  (Quotient.mk _ f_raw) g)
            (fun g_raw hf_eq hs_eq => by
              have hf_rel :=
                Quotient.exact
                  (s := btMorNSetoid k n)
                  hf_eq
              have hs_rel :=
                Quotient.exact
                  (s := btMorNSetoid k m)
                  hs_eq
              apply Quotient.sound
                (s := btMorNSetoid k (n + m))
              intro i
              unfold BTMorN.pair
              split_ifs with hlt
              · have := hf_rel ⟨i.val, hlt⟩
                simp only [BTMorN.comp,
                  BTMorN.fst,
                  BTMor1.subst_proj] at this
                exact this
              · have := hs_rel
                  ⟨i.val - n, by omega⟩
                simp only [BTMorN.comp,
                  BTMorN.snd,
                  BTMor1.subst_proj] at this
                convert this using 2
                exact Fin.ext
                  (by dsimp; omega))))
    h f g hfst hsnd

/-- Chosen binary product for `LawvereBTQuotCat`:
the product of `n` and `m` is `n + m`. -/
def lawvereBTQuotProduct
    (n m : LawvereBTQuotCat) :
    ChosenBinaryProduct n m where
  obj := (Nat.add n m : ℕ)
  fst := BTMorNQuo.fst
  snd := BTMorNQuo.snd
  lift f g := BTMorNQuo.pair f g
  lift_fst := BTMorNQuo.pair_fst
  lift_snd := BTMorNQuo.pair_snd
  lift_uniq f g h hf hs :=
    BTMorNQuo.pair_uniq f g h hf hs

/-- Chosen terminal object for
`LawvereBTQuotCat`. -/
def lawvereBTQuotTerminal :
    ChosenTerminal LawvereBTQuotCat where
  obj := (0 : ℕ)
  from_ n := BTMorNQuo.terminal n
  uniq f := BTMorNQuo.terminal_uniq f

/-- `LawvereBTQuotCat` has chosen finite
products. -/
instance : HasChosenFiniteProducts
    LawvereBTQuotCat where
  terminal := lawvereBTQuotTerminal
  product := lawvereBTQuotProduct

/-- Embed `BTMor1 n` into `BTMor1 (n + k)` via
substitution with projections.  Equivalent to
`BTMor1.shift` but defined via `subst` to enable
use of `subst_cong_right`. -/
def BTMor1.embed {n : ℕ} (k : ℕ)
    (t : BTMor1 n) : BTMor1 (n + k) :=
  t.subst (fun i =>
    BTMor1.proj ⟨i.val, by omega⟩)

/-- `embed` preserves `btMorRel`. -/
theorem embed_cong {n : ℕ} (k : ℕ)
    {t1 t2 : BTMor1 n}
    (h : btMorRel n t1 t2) :
    btMorRel (n + k)
      (t1.embed k) (t2.embed k) :=
  subst_cong_right _ h

/-- Variant of `btFoldFullMor` using `embed` (subst
with projections) instead of `shift` (rename).  The
two produce `btMorRel`-equivalent results but `embed`
enables direct use of `subst_cong_right` for
well-definedness of the quotient lift. -/
def btFoldFullMorE {n m : ℕ}
    (f : BTMorN n m)
    (g : BTMorN (m + m) m) :
    BTMorN (n + 1) m :=
  fun j => BTMor1.fold m
    (fun i => (f i).embed 1)
    g
    (BTMor1.proj ⟨n, by omega⟩)
    j

/-- The fold morphism in the quotient category,
lifted from `btFoldFullMorE` via `Quotient.lift₂`.
Well-definedness follows from `btMorRel.congFold`
and `embed_cong`. -/
def elimQ {n m : ℕ}
    (f : BTMorNQuo n m)
    (g : BTMorNQuo (m + m) m) :
    BTMorNQuo (n + 1) m :=
  Quotient.lift₂
    (s₁ := btMorNSetoid n m)
    (s₂ := btMorNSetoid (m + m) m)
    (fun f_raw g_raw =>
      Quotient.mk (btMorNSetoid (n + 1) m)
        (btFoldFullMorE f_raw g_raw))
    (fun _ _ _ _ hf hg =>
      Quotient.sound
        (s := btMorNSetoid (n + 1) m)
        (fun _ => btMorRel.congFold
          (fun i => embed_cong 1 (hf i))
          hg
          (btMorRel.refl _)))
    f g

/-- The insert-leaf substitution at the raw level:
sends variable `i < n` to `proj i` and
variable `n` to `leaf`.  This is the raw form
of `cfpInsertSnd btLeafQ n`. -/
private def insertLeafRaw (n : ℕ) :
    BTMorN n (n + 1) :=
  BTMorN.pair (BTMorN.id n)
    (fun _ => BTMor1.leaf)

/-- `insertLeafRaw` sends variables `i < n` to
`proj i` and variables `i >= n` to `leaf`. -/
private theorem insertLeafRaw_lt
    {n : ℕ} (i : Fin (n + 1))
    (h : i.val < n) :
    insertLeafRaw n i =
      BTMor1.proj ⟨i.val, h⟩ := by
  unfold insertLeafRaw BTMorN.pair BTMorN.id
  rw [dif_pos h]

/-- `insertLeafRaw` sends variable `n` to leaf. -/
private theorem insertLeafRaw_last
    {n : ℕ} (i : Fin (n + 1))
    (h : ¬ i.val < n) :
    insertLeafRaw n i = BTMor1.leaf := by
  unfold insertLeafRaw BTMorN.pair
  rw [dif_neg h]

/-- Substituting `insertLeafRaw` into `embed 1`
recovers the original term. -/
private theorem embed_subst_insertLeaf
    {n : ℕ} (t : BTMor1 n) :
    (t.embed 1).subst (insertLeafRaw n) = t := by
  unfold BTMor1.embed
  rw [BTMor1.subst_comp]
  conv_rhs => rw [← BTMor1.subst_id t]
  congr 1
  funext v
  rw [BTMor1.subst_proj,
    insertLeafRaw_lt ⟨v.val, by omega⟩
      (by exact v.isLt)]

/-- Substituting `insertLeafRaw` into `proj n`
yields `leaf`. -/
private theorem proj_n_subst_insertLeaf
    (n : ℕ) :
    (BTMor1.proj (n := n + 1)
      ⟨n, by omega⟩).subst
      (insertLeafRaw n) = BTMor1.leaf := by
  rw [BTMor1.subst_proj]
  have hge : ¬ (⟨n, (by omega : n < n + 1)⟩ :
      Fin (n + 1)).val < n := by
    simp
  exact insertLeafRaw_last _ hge

/-- At the raw level, composing `insertLeafRaw`
with `btFoldFullMorE` yields a morphism tuple
pointwise `btMorRel`-related to `f_raw`. -/
private theorem foldE_insertLeaf_rel
    {n m : ℕ}
    (f_raw : BTMorN n m)
    (g_raw : BTMorN (m + m) m)
    (j : Fin m) :
    btMorRel n
      ((btFoldFullMorE f_raw g_raw j).subst
        (insertLeafRaw n))
      (f_raw j) := by
  unfold btFoldFullMorE
  rw [fold_subst_eq]
  rw [proj_n_subst_insertLeaf]
  conv_lhs =>
    arg 2; ext i
    rw [embed_subst_insertLeaf]
  exact btMorRel.foldLeaf m j f_raw g_raw

/-- The leaf morphism in the quotient category. -/
def btLeafQ : BTMorNQuo 0 1 :=
  Quotient.mk (btMorNSetoid 0 1) btLeaf

/-- The branch morphism in the quotient category. -/
def btBranchQ : BTMorNQuo 2 1 :=
  Quotient.mk (btMorNSetoid 2 1) btBranch

/-- Leaf computation rule for `elimQ`:
composing with the insert-leaf morphism recovers
the base morphism. -/
theorem elimQ_ℓ {n m : ℕ}
    (f : BTMorNQuo n m)
    (g : BTMorNQuo (m + m) m) :
    cfpInsertSnd (C := LawvereBTQuotCat)
      btLeafQ n ≫ elimQ f g = f :=
  Quotient.ind₂
    (motive := fun f g =>
      cfpInsertSnd (C := LawvereBTQuotCat)
        btLeafQ n ≫ elimQ f g = f)
    (fun f_raw g_raw => by
      -- The composition unfolds to:
      -- comp (insertSnd btLeafQ) (elimQ f g)
      -- = comp (pair (id n) (comp (terminal n) btLeafQ)) ⟦btFoldFullMorE f_raw g_raw⟧
      -- which at the raw level is
      -- ⟦BTMorN.comp (insertLeafRaw n) (btFoldFullMorE f_raw g_raw)⟧
      -- We show this is ≈ ⟦f_raw⟧
      -- using foldE_insertLeaf_rel.
      apply Quotient.sound
        (s := btMorNSetoid n m)
      intro j
      change btMorRel n
        ((btFoldFullMorE f_raw g_raw j).subst
          (BTMorN.pair (BTMorN.id n)
            (BTMorN.comp
              (BTMorN.terminal n) btLeaf)))
        (f_raw j)
      have heq :
          BTMorN.pair (BTMorN.id n)
            (BTMorN.comp
              (BTMorN.terminal n) btLeaf) =
          insertLeafRaw n := by
        funext i
        unfold insertLeafRaw BTMorN.pair
          BTMorN.id BTMorN.comp btLeaf
        split_ifs with h
        · rfl
        · exact BTMor1.subst_leaf _
      rw [heq]
      exact foldE_insertLeaf_rel
        f_raw g_raw j)
    f g

/-- The raw morphism for `cfpMap (𝟙 n) btBranch`:
sends variable `i < n` to `proj i` and variable `n`
to `branch (proj n) (proj (n+1))`. -/
private def mapBranchRaw (n : ℕ) :
    BTMorN (n + 2) (n + 1) :=
  BTMorN.pair
    (fun i => BTMor1.proj
      ⟨i.val, by omega⟩)
    (fun _ => BTMor1.branch
      (BTMor1.proj ⟨n, by omega⟩)
      (BTMor1.proj ⟨n + 1, by omega⟩))

/-- `mapBranchRaw` sends variable `i < n` to
`proj ⟨i, ...⟩`. -/
private theorem mapBranchRaw_lt
    {n : ℕ} (i : Fin (n + 1))
    (h : i.val < n) :
    mapBranchRaw n i =
      BTMor1.proj ⟨i.val, by omega⟩ := by
  unfold mapBranchRaw BTMorN.pair
  rw [dif_pos h]

/-- `mapBranchRaw` sends variable `n` to
`branch (proj n) (proj (n+1))`. -/
private theorem mapBranchRaw_last
    {n : ℕ} (i : Fin (n + 1))
    (h : ¬ i.val < n) :
    mapBranchRaw n i =
      BTMor1.branch
        (BTMor1.proj ⟨n, by omega⟩)
        (BTMor1.proj
          ⟨n + 1, by omega⟩) := by
  unfold mapBranchRaw BTMorN.pair
  rw [dif_neg h]

/-- Substituting `mapBranchRaw` into `embed 1`
gives `embed 2`. -/
private theorem embed_subst_mapBranch
    {n : ℕ} (t : BTMor1 n) :
    (t.embed 1).subst (mapBranchRaw n) =
    t.embed 2 := by
  unfold BTMor1.embed
  rw [BTMor1.subst_comp]
  congr 1
  funext v
  rw [BTMor1.subst_proj,
    mapBranchRaw_lt ⟨v.val, by omega⟩
      (by exact v.isLt)]

/-- Substituting `mapBranchRaw` into `proj n`
yields `branch (proj n) (proj (n+1))`. -/
private theorem proj_n_subst_mapBranch
    (n : ℕ) :
    (BTMor1.proj (n := n + 1)
      ⟨n, by omega⟩).subst
      (mapBranchRaw n) =
    BTMor1.branch
      (BTMor1.proj ⟨n, by omega⟩)
      (BTMor1.proj ⟨n + 1, by omega⟩) := by
  rw [BTMor1.subst_proj]
  have hge : ¬ (⟨n, (by omega : n < n + 1)⟩ :
      Fin (n + 1)).val < n := by
    simp
  exact mapBranchRaw_last _ hge

/-- At the raw level, composing `mapBranchRaw`
with `btFoldFullMorE` and component `j` yields
a term `btMorRel`-related to the foldBranch
computation. -/
private theorem foldE_mapBranch_rel
    {n m : ℕ}
    (f_raw : BTMorN n m)
    (g_raw : BTMorN (m + m) m)
    (j : Fin m) :
    btMorRel (n + 2)
      ((btFoldFullMorE f_raw g_raw j).subst
        (mapBranchRaw n))
      ((g_raw j).subst (fun i =>
        if h : i.val < m
        then BTMor1.fold m
          (fun k => (f_raw k).embed 2)
          g_raw
          (BTMor1.proj ⟨n, by omega⟩)
          ⟨i.val, h⟩
        else BTMor1.fold m
          (fun k => (f_raw k).embed 2)
          g_raw
          (BTMor1.proj
            ⟨n + 1, by omega⟩)
          ⟨i.val - m, by omega⟩)) := by
  unfold btFoldFullMorE
  rw [fold_subst_eq]
  rw [proj_n_subst_mapBranch]
  conv_lhs =>
    arg 2; ext i
    rw [embed_subst_mapBranch]
  exact btMorRel.foldBranch m j
    (fun k => (f_raw k).embed 2)
    g_raw
    (BTMor1.proj ⟨n, by omega⟩)
    (BTMor1.proj ⟨n + 1, by omega⟩)

/-- The raw LHS substitution for `elim_β`:
the composition `cfpMap (id n) btBranch`
at the raw level. -/
private def elimβ_lhs_subst (n : ℕ) :
    BTMorN (n + 2) (n + 1) :=
  BTMorN.pair
    (BTMorN.comp BTMorN.fst (BTMorN.id n))
    (BTMorN.comp BTMorN.snd btBranch)

/-- The raw RHS substitution for `elim_β`:
the composition `cfpLiftAssoc φ φ` at
the raw level. -/
private def elimβ_rhs_subst {n m : ℕ}
    (f_raw : BTMorN n m)
    (g_raw : BTMorN (m + m) m) :
    BTMorN (n + 2) (m + m) :=
  BTMorN.pair
    (BTMorN.comp
      (BTMorN.pair
        (BTMorN.fst (n := n) (m := 2))
        (BTMorN.comp
          (BTMorN.snd (n := n) (m := 2))
          (BTMorN.fst (n := 1) (m := 1))))
      (btFoldFullMorE f_raw g_raw))
    (BTMorN.comp
      (BTMorN.pair
        (BTMorN.fst (n := n) (m := 2))
        (BTMorN.comp
          (BTMorN.snd (n := n) (m := 2))
          (BTMorN.snd (n := 1) (m := 1))))
      (btFoldFullMorE f_raw g_raw))

/-- `elimβ_lhs_subst` equals `mapBranchRaw`. -/
private theorem elimβ_lhs_eq (n : ℕ) :
    elimβ_lhs_subst n = mapBranchRaw n := by
  funext i
  unfold elimβ_lhs_subst mapBranchRaw
    BTMorN.pair BTMorN.comp BTMorN.fst
    BTMorN.snd BTMorN.id btBranch
  split_ifs with h
  · rfl
  · change
      (BTMor1.branch
        (BTMor1.proj ⟨0, by omega⟩)
        (BTMor1.proj ⟨1, by omega⟩)).subst
      (BTMorN.snd (n := n) (m := 2)) =
      BTMor1.branch
        (BTMor1.proj ⟨n, by omega⟩)
        (BTMor1.proj ⟨n + 1, by omega⟩)
    rw [BTMor1.subst_branch,
      BTMor1.subst_proj,
      BTMor1.subst_proj]
    simp only [BTMorN.snd]; rfl

/-- `elimβ_rhs_subst` pointwise equals the
foldBranch substitution. -/
private theorem elimβ_rhs_eq {n m : ℕ}
    (f_raw : BTMorN n m)
    (g_raw : BTMorN (m + m) m)
    (i : Fin (m + m)) :
    elimβ_rhs_subst f_raw g_raw i =
    (if h : i.val < m
    then BTMor1.fold m
      (fun k => (f_raw k).embed 2)
      g_raw
      (BTMor1.proj ⟨n, by omega⟩)
      ⟨i.val, h⟩
    else BTMor1.fold m
      (fun k => (f_raw k).embed 2)
      g_raw
      (BTMor1.proj ⟨n + 1, by omega⟩)
      ⟨i.val - m, by omega⟩) := by
  unfold elimβ_rhs_subst BTMorN.pair
    BTMorN.comp btFoldFullMorE
  split_ifs with h
  · -- i < m: the pair selects the left comp
    rw [fold_subst_eq]; congr 1
    · -- base: embed subst assocFst = embed 2
      funext k; unfold BTMor1.embed
      rw [BTMor1.subst_comp]; congr 1
      funext v; rw [BTMor1.subst_proj]
      change (if _ : v.val < n then _
        else _) = _
      exact dif_pos v.isLt
    · rw [BTMor1.subst_proj]
      change (if _ : _ then _ else _) = _
      rw [dif_neg (by simp)]
      simp only [BTMorN.fst, BTMor1.subst_proj,
        BTMorN.snd]
      congr 1; exact Fin.ext (by simp)
  · -- i >= m: the pair selects the right comp
    rw [fold_subst_eq]; congr 1
    · funext k; unfold BTMor1.embed
      rw [BTMor1.subst_comp]; congr 1
      funext v; rw [BTMor1.subst_proj]
      change (if _ : v.val < n then _
        else _) = _
      exact dif_pos v.isLt
    · rw [BTMor1.subst_proj]
      change (if _ : _ then _ else _) = _
      rw [dif_neg (by simp)]
      simp only [BTMorN.snd,
        BTMor1.subst_proj]
      congr 1; exact Fin.ext (by simp)

-- Reduction of `cfpMap`/`cfpLiftAssoc` through
-- quotient lifts requires extended elaboration.
/-- Branch computation rule for `elimQ`. -/
theorem elimQ_β {n m : ℕ}
    (f : BTMorNQuo n m)
    (g : BTMorNQuo (m + m) m) :
    cfpMap (C := LawvereBTQuotCat)
      (BTMorNQuo.id n) btBranchQ ≫ elimQ f g =
    cfpLiftAssoc (C := LawvereBTQuotCat)
      (elimQ f g) (elimQ f g) ≫ g :=
  Quotient.ind₂
    (motive := fun f g =>
      cfpMap (C := LawvereBTQuotCat)
        (BTMorNQuo.id n) btBranchQ ≫ elimQ f g =
      cfpLiftAssoc (C := LawvereBTQuotCat)
        (elimQ f g) (elimQ f g) ≫ g)
    (fun f_raw g_raw => by
      apply Quotient.sound
        (s := btMorNSetoid (n + 2) m)
      intro j
      -- LHS: reduce substitution to
      -- mapBranchRaw
      change btMorRel (n + 2)
        ((btFoldFullMorE f_raw g_raw
          j).subst
          (elimβ_lhs_subst n))
        _
      rw [elimβ_lhs_eq]
      -- Apply foldBranch computation
      apply btMorRel.trans
      · exact foldE_mapBranch_rel
          f_raw g_raw j
      -- RHS: show the categorical
      -- composition reduces to the same
      -- substitution
      apply btMorRel.symm
      change btMorRel (n + 2)
        ((g_raw j).subst
          (elimβ_rhs_subst f_raw g_raw))
        _
      have hrw : elimβ_rhs_subst f_raw
          g_raw =
          (fun i : Fin (m + m) =>
            if h : i.val < m
            then BTMor1.fold m
              (fun k => (f_raw k).embed 2)
              g_raw
              (BTMor1.proj ⟨n, by omega⟩)
              ⟨i.val, h⟩
            else BTMor1.fold m
              (fun k => (f_raw k).embed 2)
              g_raw
              (BTMor1.proj
                ⟨n + 1, by omega⟩)
              ⟨i.val - m,
                by omega⟩) :=
        funext (fun i =>
          elimβ_rhs_eq f_raw g_raw i)
      rw [hrw]
      exact btMorRel.refl _)
    f g

/-- Embedding substitution: maps `Fin n` into
`BTMor1 (n + 1)` via projections. -/
private def embedSubst (n : ℕ) :
    Fin n → BTMor1 (n + 1) :=
  fun v => BTMor1.proj ⟨v.val, by omega⟩

/-- `btSubstSnoc embedSubst (proj n)` is the
identity substitution on `Fin (n + 1)`. -/
private theorem embedSubst_snoc_proj_id
    {n : ℕ} (i : Fin (n + 1)) :
    btSubstSnoc (embedSubst n)
      (BTMor1.proj ⟨n, by omega⟩) i =
    BTMor1.proj i := by
  refine Fin.lastCases ?_ ?_ i
  · rw [btSubstSnoc_last]; congr 1
  · intro j; rw [btSubstSnoc_castSucc]
    unfold embedSubst; congr 1

/-- `insertLeafRaw n` composed with `embedSubst`
equals `btSubstSnoc (embedSubst n) leaf`. -/
private theorem insertLeaf_comp_embed
    {n : ℕ} (i : Fin (n + 1)) :
    (insertLeafRaw n i).subst
      (embedSubst n) =
    btSubstSnoc (embedSubst n)
      BTMor1.leaf i := by
  refine Fin.lastCases ?_ ?_ i
  · rw [btSubstSnoc_last]
    have h : ¬ (Fin.last n).val < n := by
      simp
    rw [insertLeafRaw_last _ h,
      BTMor1.subst_leaf]
  · intro j
    rw [btSubstSnoc_castSucc,
      insertLeafRaw_lt _ j.isLt,
      BTMor1.subst_proj]; congr 1

/-- `mapBranchRaw n` composed with the branch
embedding substitution equals the `btSubstSnoc`
form for the branch case. -/
private theorem mapBranch_comp_embed
    {n : ℕ} (i : Fin (n + 1)) :
    (mapBranchRaw n i).subst
      (btSubstSnoc
        (btSubstSnoc
          (btSubstEmbed 2 (embedSubst n))
          (BTMor1.proj ⟨n + 1, by omega⟩))
        (BTMor1.proj ⟨n + 2, by omega⟩)) =
    btSubstSnoc
      (btSubstEmbed 2 (embedSubst n))
      (BTMor1.branch
        (BTMor1.proj ⟨n + 1, by omega⟩)
        (BTMor1.proj ⟨n + 2, by omega⟩))
      i := by
  refine Fin.lastCases ?_ ?_ i
  · rw [btSubstSnoc_last]
    have hlt : ¬ (Fin.last n).val < n := by
      simp
    rw [mapBranchRaw_last _ hlt,
      BTMor1.subst_branch,
      BTMor1.subst_proj,
      BTMor1.subst_proj]
    have hn : (⟨n, by omega⟩ : Fin (n + 2)) =
        Fin.castSucc (Fin.last n) := by
      ext; simp
    have hn1 : (⟨n + 1, by omega⟩ : Fin (n + 2)) =
        Fin.last (n + 1) := by
      ext; simp
    rw [hn, btSubstSnoc_castSucc,
      btSubstSnoc_last,
      hn1, btSubstSnoc_last]
  · intro j
    rw [btSubstSnoc_castSucc,
      mapBranchRaw_lt _ j.isLt,
      BTMor1.subst_proj]
    have hjlt : (⟨(Fin.castSucc j).val,
          by omega⟩ : Fin (n + 2)) =
        Fin.castSucc (Fin.castSucc j) := by
      ext; simp
    rw [hjlt, btSubstSnoc_castSucc,
      btSubstSnoc_castSucc]

set_option backward.isDefEq.respectTransparency false in
-- The proof involves iterated substitution on
-- parameterized tree morphisms, requiring extra
-- elaboration budget.
/-- Uniqueness of `elimQ`: any quotient morphism
satisfying the leaf and branch computation rules
equals `elimQ f g`. -/
theorem elimQ_uniq {n m : ℕ}
    (f : BTMorNQuo n m)
    (g : BTMorNQuo (m + m) m)
    (φ : BTMorNQuo (n + 1) m)
    (hleaf :
      cfpInsertSnd (C := LawvereBTQuotCat)
        btLeafQ n ≫ φ = f)
    (hbranch :
      cfpMap (C := LawvereBTQuotCat)
        (BTMorNQuo.id n) btBranchQ ≫ φ =
      cfpLiftAssoc (C := LawvereBTQuotCat)
        φ φ ≫ g) :
    φ = elimQ f g := by
  revert hleaf hbranch
  refine Quotient.ind₂
    (motive := fun f g => ∀ (φ :
        BTMorNQuo (n + 1) m),
      cfpInsertSnd (C := LawvereBTQuotCat)
        btLeafQ n ≫ φ = f →
      cfpMap (C := LawvereBTQuotCat)
        (BTMorNQuo.id n) btBranchQ ≫ φ =
      cfpLiftAssoc (C := LawvereBTQuotCat)
        φ φ ≫ g →
      φ = elimQ f g)
    ?_ f g φ
  intro f_raw g_raw
  refine Quotient.ind
    (motive := fun φ =>
      cfpInsertSnd (C := LawvereBTQuotCat)
        btLeafQ n ≫ φ =
        Quotient.mk _ f_raw →
      cfpMap (C := LawvereBTQuotCat)
        (BTMorNQuo.id n) btBranchQ ≫ φ =
      cfpLiftAssoc (C := LawvereBTQuotCat)
        φ φ ≫ Quotient.mk _ g_raw →
      φ = elimQ
        (Quotient.mk _ f_raw)
        (Quotient.mk _ g_raw))
    ?_
  intro φ_raw hℓ_eq hβ_eq
  apply Quotient.sound
    (s := btMorNSetoid (n + 1) m)
  intro j
  -- Identity subst fact
  have hsnoc_id :
      ∀ (t : BTMor1 (n + 1)),
      t.subst (btSubstSnoc (embedSubst n)
        (BTMor1.proj ⟨n, by omega⟩)) =
      t := by
    intro t
    conv_rhs => rw [← BTMor1.subst_id t]
    congr 1; funext i
    exact embedSubst_snoc_proj_id i
  rw [← hsnoc_id (φ_raw j)]
  change btMorRel (n + 1)
    ((φ_raw j).subst
      (btSubstSnoc (embedSubst n)
        (BTMor1.proj ⟨n, by omega⟩)))
    (btFoldFullMorE f_raw g_raw j)
  have hfold_eq :
      btFoldFullMorE f_raw g_raw j =
      BTMor1.fold m
        (fun i =>
          (f_raw i).subst (embedSubst n))
        g_raw
        (BTMor1.proj ⟨n, by omega⟩) j := by
    unfold btFoldFullMorE BTMor1.embed
      embedSubst; rfl
  rw [hfold_eq]
  -- Extract raw hypotheses
  have hℓ_raw :=
    Quotient.exact
      (s := btMorNSetoid n m) hℓ_eq
  have hβ_raw :=
    Quotient.exact
      (s := btMorNSetoid (n + 2) m)
      hβ_eq
  -- Reduce leaf hypothesis to insertLeafRaw form
  have hℓ_il : ∀ j', btMorRel n
      ((φ_raw j').subst (insertLeafRaw n))
      (f_raw j') := by
    intro j'
    have h := hℓ_raw j'
    have heq :
        BTMorN.pair (BTMorN.id n)
          (BTMorN.comp
            (BTMorN.terminal n) btLeaf) =
        insertLeafRaw n := by
      funext i
      unfold insertLeafRaw BTMorN.pair
        BTMorN.id BTMorN.comp btLeaf
      split_ifs
      · rfl
      · exact BTMor1.subst_leaf _
    rw [heq] at h; exact h
  -- Lift leaf hypothesis to arity n+1
  have hℓ_lifted : ∀ j', btMorRel (n + 1)
      ((φ_raw j').subst
        (btSubstSnoc (embedSubst n)
          BTMor1.leaf))
      ((f_raw j').subst
        (embedSubst n)) := by
    intro j'
    have h := subst_cong_right
      (embedSubst n) (hℓ_il j')
    rw [BTMor1.subst_comp] at h
    rw [show btSubstSnoc (embedSubst n)
          BTMor1.leaf =
        fun i => (insertLeafRaw n i).subst
          (embedSubst n)
      from (funext insertLeaf_comp_embed).symm]
    exact h
  -- Lift branch hypothesis to arity n+3
  have hβ_lifted : ∀ j', btMorRel (n + 3)
      ((φ_raw j').subst
        (btSubstSnoc
          (btSubstEmbed 2 (embedSubst n))
          (BTMor1.branch
            (BTMor1.proj
              ⟨n + 1, by omega⟩)
            (BTMor1.proj
              ⟨n + 2, by omega⟩))))
      ((g_raw j').subst
        (btFoldBranchSubstPhi φ_raw
          (embedSubst n))) := by
    intro j'
    let τ : Fin (n + 2) → BTMor1 (n + 3) :=
      btSubstSnoc
        (btSubstSnoc
          (btSubstEmbed 2 (embedSubst n))
          (BTMor1.proj ⟨n + 1, by omega⟩))
        (BTMor1.proj ⟨n + 2, by omega⟩)
    have hraw := hβ_raw j'
    change btMorRel (n + 2)
      ((φ_raw j').subst
        (elimβ_lhs_subst n)) _ at hraw
    rw [elimβ_lhs_eq] at hraw
    have h := subst_cong_right τ hraw
    simp only [BTMorN.comp] at h
    rw [BTMor1.subst_comp,
      BTMor1.subst_comp] at h
    -- Show RHS substitution equals
    -- btFoldBranchSubstPhi form.
    have hrhs_eq : (fun i =>
        (if h : i.val < m
         then (φ_raw ⟨i.val, h⟩).subst
           (BTMorN.fst.pair
             (BTMorN.snd.comp BTMorN.fst))
         else (φ_raw ⟨i.val - m,
               Nat.sub_lt_right_of_lt_add
                 (by omega)
                 (i.isLt)⟩).subst
           (BTMorN.fst.pair
             (BTMorN.snd.comp
               BTMorN.snd))).subst τ) =
        btFoldBranchSubstPhi φ_raw
          (embedSubst n) := by
      funext i
      unfold btFoldBranchSubstPhi
      split_ifs with h_lt
      · rw [BTMor1.subst_comp]; congr 1
        funext v
        refine Fin.lastCases ?_ ?_ v
        · simp only [btSubstSnoc_last]
          have heval :
              (BTMorN.fst (n := n) (m := 2)).pair
                ((BTMorN.snd (n := n) (m := 2)).comp
                  (BTMorN.fst (n := 1) (m := 1)))
                (Fin.last n) =
              BTMor1.proj
                (⟨n, by omega⟩ : Fin (n + 2)) := by
            unfold BTMorN.pair
            simp only [Fin.val_last]
            split_ifs with hc
            · exact absurd hc (lt_irrefl n)
            · simp only [Nat.sub_self,
                BTMorN.comp, BTMorN.fst,
                BTMorN.snd, BTMor1.subst_proj,
                Nat.add_zero]
          rw [heval, BTMor1.subst_proj]
          change btSubstSnoc
              (btSubstSnoc
                (btSubstEmbed 2 (embedSubst n))
                (BTMor1.proj ⟨n + 1, by omega⟩))
              (BTMor1.proj ⟨n + 2, by omega⟩)
              (⟨n, by omega⟩ : Fin (n + 2)) =
            BTMor1.proj ⟨n + 1, by omega⟩
          have hn :
              (⟨n, by omega⟩ : Fin (n + 2)) =
              Fin.castSucc (Fin.last n) := by
            ext; simp
          rw [hn, btSubstSnoc_castSucc,
            btSubstSnoc_last]
        · intro w
          simp only [btSubstSnoc_castSucc]
          have heval :
              (BTMorN.fst (n := n) (m := 2)).pair
                ((BTMorN.snd (n := n) (m := 2)).comp
                  (BTMorN.fst (n := 1) (m := 1)))
                (Fin.castSucc w) =
              BTMor1.proj
                (⟨w.val, by omega⟩ : Fin (n + 2)) := by
            unfold BTMorN.pair
            simp only [Fin.val_castSucc, BTMorN.fst]
            rw [dif_pos w.isLt]
          rw [heval, BTMor1.subst_proj]
          change btSubstSnoc
              (btSubstSnoc
                (btSubstEmbed 2 (embedSubst n))
                (BTMor1.proj ⟨n + 1, by omega⟩))
              (BTMor1.proj ⟨n + 2, by omega⟩)
              (⟨w.val, by omega⟩ : Fin (n + 2)) =
            btSubstEmbed 2 (embedSubst n) w
          have hw :
              (⟨w.val, by omega⟩ : Fin (n + 2)) =
              Fin.castSucc (Fin.castSucc w) := by
            ext; simp
          rw [hw, btSubstSnoc_castSucc,
            btSubstSnoc_castSucc]
      · rw [BTMor1.subst_comp]; congr 1
        funext v
        refine Fin.lastCases ?_ ?_ v
        · simp only [btSubstSnoc_last]
          have heval :
              (BTMorN.fst (n := n) (m := 2)).pair
                ((BTMorN.snd (n := n) (m := 2)).comp
                  (BTMorN.snd (n := 1) (m := 1)))
                (Fin.last n) =
              BTMor1.proj
                (⟨n + 1, by omega⟩ : Fin (n + 2)) := by
            unfold BTMorN.pair
            simp only [Fin.val_last]
            split_ifs with hc
            · exact absurd hc (lt_irrefl n)
            · simp only [Nat.sub_self,
                BTMorN.comp,
                BTMorN.snd, BTMor1.subst_proj,
                Nat.add_zero]
          rw [heval, BTMor1.subst_proj]
          change btSubstSnoc
              (btSubstSnoc
                (btSubstEmbed 2 (embedSubst n))
                (BTMor1.proj ⟨n + 1, by omega⟩))
              (BTMor1.proj ⟨n + 2, by omega⟩)
              (⟨n + 1, by omega⟩ : Fin (n + 2)) =
            BTMor1.proj ⟨n + 2, by omega⟩
          have hn1 :
              (⟨n + 1, by omega⟩ : Fin (n + 2)) =
              Fin.last (n + 1) := by
            ext; simp
          rw [hn1, btSubstSnoc_last]
        · intro w
          simp only [btSubstSnoc_castSucc]
          have heval :
              (BTMorN.fst (n := n) (m := 2)).pair
                ((BTMorN.snd (n := n) (m := 2)).comp
                  (BTMorN.snd (n := 1) (m := 1)))
                (Fin.castSucc w) =
              BTMor1.proj
                (⟨w.val, by omega⟩ : Fin (n + 2)) := by
            unfold BTMorN.pair
            simp only [Fin.val_castSucc, BTMorN.fst]
            rw [dif_pos w.isLt]
          rw [heval, BTMor1.subst_proj]
          change btSubstSnoc
              (btSubstSnoc
                (btSubstEmbed 2 (embedSubst n))
                (BTMor1.proj ⟨n + 1, by omega⟩))
              (BTMor1.proj ⟨n + 2, by omega⟩)
              (⟨w.val, by omega⟩ : Fin (n + 2)) =
            btSubstEmbed 2 (embedSubst n) w
          have hw :
              (⟨w.val, by omega⟩ : Fin (n + 2)) =
              Fin.castSucc (Fin.castSucc w) := by
            ext; simp
          rw [hw, btSubstSnoc_castSucc,
            btSubstSnoc_castSucc]
    rw [show btSubstSnoc
          (btSubstEmbed 2 (embedSubst n))
          (BTMor1.branch
            (BTMor1.proj ⟨n + 1, by omega⟩)
            (BTMor1.proj ⟨n + 2, by omega⟩)) =
        fun i => (mapBranchRaw n i).subst τ
      from (funext mapBranch_comp_embed).symm]
    rw [show btFoldBranchSubstPhi φ_raw
          (embedSubst n) =
        fun i =>
          (if h : i.val < m
           then (φ_raw ⟨i.val, h⟩).subst
             (BTMorN.fst.pair
               (BTMorN.snd.comp BTMorN.fst))
           else (φ_raw ⟨i.val - m,
                 Nat.sub_lt_right_of_lt_add
                   (by omega)
                   (i.isLt)⟩).subst
             (BTMorN.fst.pair
               (BTMorN.snd.comp
                 BTMorN.snd))).subst τ
      from hrhs_eq.symm]
    exact h
  exact btMorRel.foldUniq j φ_raw f_raw g_raw
    (embedSubst n)
    (BTMor1.proj ⟨n, by omega⟩)
    hℓ_lifted hβ_lifted

/-- `LawvereBTQuotCat` has a parameterized binary
tree object. -/
instance : HasPBTO LawvereBTQuotCat where
  T := (1 : ℕ)
  ℓ := btLeafQ
  β := btBranchQ
  elim f g := elimQ f g
  elim_ℓ f g := elimQ_ℓ f g
  elim_β f g := elimQ_β f g
  elim_uniq f g φ hℓ hβ :=
    elimQ_uniq f g φ hℓ hβ

end GebLean

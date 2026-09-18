/-!
# Interaction combinators as an interface-graded polynomial coalgebra

Prototype (core Lean only, executable). Nets follow Lafont,
"Interaction combinators" (Inf. & Comp. 137, 1997), § 1.1:
free ports `X`, cells `C` with symbols, wires partitioning ports into pairs.

* `CSym` with `arity` is the signature polynomial `p(y) = Σ_α y^{ar α}`.
* `Net` is a state graded by its interface size `n` (the slice over `ℕ`).
* `par` / `cut` are the gluing operations: the algebra side.
* `obs` and `step` form the coalgebra `Net → Q Net` for the polynomial
  `Q(X)(n) = (Fin n → Option CSym) × X(n)`: observe which agents are
  visible at the interface (principal port free), then do one maximal
  parallel reduction step (well defined by Lafont Prop. 1: active
  pairs are pairwise disjoint).
-/

namespace GebLean

/-- The symbols of the interaction combinators (Lafont § 2): constructor `γ`,
duplicator `δ`, eraser `ε`. -/
inductive CSym | γ | δ | ε
  deriving DecidableEq, Repr

/-- Number of auxiliary ports of a symbol: `γ` and `δ` are binary, `ε` is nullary. -/
def CSym.arity : CSym → Nat
  | .γ => 2 | .δ => 2 | .ε => 0

/-- A port: a free port of the interface, or port `i` of cell `c`
(`i = 0` principal, `1..arity` auxiliary), or a temporary connector used
while splicing a rule's right-hand side into a net. -/
inductive Port
  | free (i : Nat)
  | cell (c : Nat) (i : Nat)
  | conn (k : Nat)
  deriving DecidableEq, Repr

/-- A net (Lafont § 1.1) graded by its interface size `n`: cells carrying symbols and
wires pairing ports. -/
structure Net where
  /-- Number of free ports (the interface size). -/
  n : Nat
  /-- Cells indexed by position; `none` marks a cell removed by an interaction. -/
  cells : Array (Option CSym)
  /-- Wires, each pairing two ports; every live port occurs in exactly one wire. -/
  wires : List (Port × Port)

namespace Net

/-- The port wired to `p`, if any. -/
def partner (N : Net) (p : Port) : Option Port :=
  (N.wires.findSome? fun (a, b) =>
    if a = p then some b else if b = p then some a else none)

/-- CSymbol of a live cell. -/
def sym (N : Net) (c : Nat) : Option CSym := (N.cells.getD c none)

/-! ## Algebra: gluing (the `T_P`-algebra structure on nets) -/

/-- Offset cell indices by `dc` and free-port indices by `df`; connectors are unchanged. -/
def shiftPort (dc df : Nat) : Port → Port
  | .free i => .free (i + df)
  | .cell c i => .cell (c + dc) i
  | .conn k => .conn k

/-- Juxtaposition `Net n → Net m → Net (n + m)`. -/
def par (M N : Net) : Net where
  n := M.n + N.n
  cells := M.cells ++ N.cells
  wires := M.wires ++ N.wires.map fun (a, b) =>
    (shiftPort M.cells.size M.n a, shiftPort M.cells.size M.n b)

/-- Eliminate a connector `conn k` occurring in two wires (or once as a
cyclic wire), joining its two neighbours. -/
def contractOne (ws : List (Port × Port)) (k : Nat) : List (Port × Port) :=
  let touches := fun (w : Port × Port) => w.1 = .conn k ∨ w.2 = .conn k
  let other := fun (w : Port × Port) => if w.1 = .conn k then w.2 else w.1
  match ws.filter touches with
  | [w] =>                        -- (conn k, conn k): a cyclic wire; drop
    if w.1 = .conn k ∧ w.2 = .conn k then ws.filter (fun w => ¬ touches w)
    else ws
  | [w₁, w₂] => (other w₁, other w₂) :: ws.filter (fun w => ¬ touches w)
  | _ => ws

/-- Eliminate the connectors `conn 0`, …, `conn (m - 1)` by `contractOne`, highest first. -/
def contractAll (ws : List (Port × Port)) : Nat → List (Port × Port)
  | 0 => ws
  | k + 1 => contractAll (contractOne ws k) k

/-- Connect free ports `i` and `j` (`i < j`) of `N : Net (n + 2)`,
renumbering the remaining free ports: `Net (n+2) → Net n`. -/
def cut (N : Net) (i j : Nat) : Net :=
  let ren : Port → Port
    | .free k => if k = i ∨ k = j then .conn 0
                 else .free (k - (if k > i then 1 else 0) - (if k > j then 1 else 0))
    | p => p
  { n := N.n - 2
    cells := N.cells
    wires := contractAll (N.wires.map fun (a, b) => (ren a, ren b)) 1 }

/-- A single cell as a net with `arity + 1` free ports, principal port at
free port `0`. -/
def cell (s : CSym) : Net where
  n := s.arity + 1
  cells := #[some s]
  wires := (List.range (s.arity + 1)).map fun i => (.free i, .cell 0 i)

/-! ## Interaction rules (Lafont, Fig. 2) -/

/-- Right-hand side for the pair `(a, b)`: a net with `ar a + ar b` free
ports; free ports `0 .. ar a - 1` stand for the auxiliary ports of `a`,
the rest for those of `b`. -/
def rhs : CSym → CSym → Net
  | .γ, .γ => ⟨4, #[], [(.free 0, .free 3), (.free 1, .free 2)]⟩
  | .δ, .δ => ⟨4, #[], [(.free 0, .free 2), (.free 1, .free 3)]⟩
  | .ε, .ε => ⟨0, #[], []⟩
  | .γ, .ε | .δ, .ε =>
    ⟨2, #[some .ε, some .ε], [(.free 0, .cell 0 0), (.free 1, .cell 1 0)]⟩
  | .ε, .γ | .ε, .δ =>
    ⟨2, #[some .ε, some .ε], [(.free 0, .cell 0 0), (.free 1, .cell 1 0)]⟩
  | .γ, .δ =>
    ⟨4, #[some .δ, some .δ, some .γ, some .γ],
      [(.free 0, .cell 0 0), (.free 1, .cell 1 0),
       (.free 2, .cell 2 0), (.free 3, .cell 3 0),
       (.cell 0 1, .cell 2 1), (.cell 0 2, .cell 3 1),
       (.cell 1 1, .cell 2 2), (.cell 1 2, .cell 3 2)]⟩
  | .δ, .γ =>
    ⟨4, #[some .γ, some .γ, some .δ, some .δ],
      [(.free 0, .cell 0 0), (.free 1, .cell 1 0),
       (.free 2, .cell 2 0), (.free 3, .cell 3 0),
       (.cell 0 1, .cell 2 1), (.cell 0 2, .cell 3 1),
       (.cell 1 1, .cell 2 2), (.cell 1 2, .cell 3 2)]⟩

/-! ## Coalgebra: observation and one parallel step -/

/-- Fire the active pair `(c, d)` (principal ports wired together). -/
def fire (N : Net) (c d : Nat) : Net :=
  match N.sym c, N.sym d with
  | some a, some b =>
    let R := rhs a b
    let off := N.cells.size
    let m := R.n                          -- number of connectors
    -- rename the active pair's auxiliary ports to connectors
    let renOld : Port → Port
      | .cell k i => if k = c ∧ i ≥ 1 then .conn (i - 1)
                     else if k = d ∧ i ≥ 1 then .conn (a.arity + i - 1)
                     else .cell k i
      | p => p
    let renNew : Port → Port
      | .free i => .conn i
      | .cell k i => .cell (k + off) i
      | p => p
    let old := N.wires.filter fun (x, y) =>
      ¬ (x = .cell c 0 ∨ y = .cell c 0)   -- drop the principal wire
    let ws := old.map (fun (x, y) => (renOld x, renOld y)) ++
              R.wires.map (fun (x, y) => (renNew x, renNew y))
    { n := N.n
      cells := (N.cells.set! c none).set! d none ++ R.cells
      wires := contractAll ws m }
  | _, _ => N

/-- The active pairs: pairs of live cells whose principal ports are wired together. -/
def activePairs (N : Net) : List (Nat × Nat) :=
  N.wires.filterMap fun
    | (.cell c 0, .cell d 0) =>
      if (N.sym c).isSome ∧ (N.sym d).isSome then some (c, d) else none
    | _ => none

/-- One maximal parallel reduction step (all active pairs, which are
pairwise disjoint). -/
def step (N : Net) : Net := N.activePairs.foldl (fun M (c, d) => M.fire c d) N

/-- The interface observation: for each free port, the symbol whose
principal port it is wired to, if any (`none` = silent). -/
def obs (N : Net) : List (Option CSym) :=
  (List.range N.n).map fun i =>
    match N.partner (.free i) with
    | some (.cell c 0) => N.sym c
    | _ => none

/-- The `Q`-coalgebra structure, `Q(X)(n) = (Fin n → Option CSym) × X(n)`. -/
def coalg (N : Net) : List (Option CSym) × Net := (N.obs, N.step)

/-- `k` iterations of `step`. -/
def iterate (N : Net) : Nat → Net
  | 0 => N
  | k + 1 => iterate N.step k

end Net

/-! ## Sanity checks -/

open Net

/-- `γ` cut against `γ`: annihilation, ports exchanged `0–3`, `1–2`. -/
def gg : Net := (par (cell .γ) (cell .γ)).cut 0 3

/-- `γ` cut against `δ`: commutation, producing two `δ` and two `γ`. -/
def gd : Net := (par (cell .γ) (cell .δ)).cut 0 3

/-- `δ(ε, ε)` cut against `γ`: two steps to a wiring plus erasers. -/
def dg : Net :=
  let dee := ((par (cell .δ) (par (cell .ε) (cell .ε))).cut 1 3).cut 1 2
  (par dee (cell .γ)).cut 0 1

end GebLean

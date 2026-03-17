# Workstream: Prop-free subobject classifier via WSubfunctor

## Goal

Build a completely Prop-free subobject classifier for
presheaf categories using `WSubfunctor`, confirming that
no Classical axioms (AC, propext, Quot.sound beyond
the standard three) are needed.

## Design

### WSieve

A witnessed sieve on `U : C` assigns to each morphism
`f : V ⟶ U` a `Subsingleton` witness type. The witness
type being inhabited means `f` is "in the sieve."

```lean
structure WSieve (U : C) where
  arrows : ∀ {V : C}, (V ⟶ U) → Type w
  arrowsSubsingleton : ∀ {V} (f : V ⟶ U),
    Subsingleton (arrows f)
  downward_closed : ∀ {V W} {f : V ⟶ U}
    (w : arrows f) (g : W ⟶ V),
    arrows (g ≫ f)
```

### wSieveFunctor

The presheaf of witnessed sieves:
`Cᵒᵖ ⥤ Type (max u v)` sending `c` to `WSieve c.unop`.
Restriction along `f : c ⟶ d` in `Cᵒᵖ` (i.e.,
`f.unop : d.unop ⟶ c.unop` in `C`) sends a WSieve `S`
on `c.unop` to the pullback WSieve on `d.unop`.

### wSieveTruth

The maximal witnessed sieve: `PUnit` as the witness type
for every morphism.

### wSieveCharMap

The classifying map: at stage `c` and element `x`,
the witnessed sieve has `arrows f` =
`WSubfunctor.fiber (range m) (op V) (F.map f.op x)` =
`{a : U.obj (op V) // m.app (op V) a = F.map f.op x}`.

When `m` is mono, each fiber is a `Subsingleton`.

### Axiom check

After construction, verify via `lean_verify` or
`check_axioms_inline.sh` that `wPshClassifierData`
and `wPshHasClassifier` depend only on `propext`,
`Quot.sound`, and no `Classical`.

## Status

In progress — defining WSieve.

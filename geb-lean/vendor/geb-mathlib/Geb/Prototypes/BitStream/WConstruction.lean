/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.BitStream
public import Geb.Prototypes.MType.Equiv

set_option doc.verso true

/-!
# Bitstreams constructed using W-types

The M-type {name}`Geb.MType.M` constructed from W-types, at the bitstring
polynomial {name}`Geb.BitStream.sig`, is a carrier of bitstreams. This module
states its interface in the layer form {name}`Geb.BitStream.Layer` of the
first development, termination or a bit with a continuation, and compares
it with that development's bounded prefixes, observations and sequences.

## Main definitions

* {lit}`Stream` is {name}`Geb.MType.M` at {name}`Geb.BitStream.sig`.
* {lit}`succEquiv` and {lit}`corecApprox` are the successor computation rule
  of the observations and their finite unfoldings, in layer form.
* {lit}`corec`, {lit}`mk`, {lit}`dest` and {lit}`tail` are the corecursor,
  constructor, destructor and tail in layer form.
* {lit}`prefixEquiv`, {lit}`seqEquiv` and {lit}`observationsEquiv` compare
  observations and streams with {name}`Geb.BitStream.Prefix`,
  {name}`Stream'.Seq` and {name}`Geb.BitStream.Observations`.
* {lit}`ofW` embeds the finite bitstrings.

## Main statements

* {lit}`dest_corec` — the corecursor in layer form is a morphism of
  coalgebras.
* {lit}`seqEquiv_corec` — it is the corecursor of {name}`Stream'.Seq`.
* {lit}`seqEquiv_ofW` — the embedding of finite bitstrings is the inclusion
  of lists in sequences.

## Tags

W-type, M-type, bitstream, finite approximation
-/

@[expose] public section

namespace Geb.BitStream.WConstruction

open Geb.MType (M Approx Depth)
open Geb.MType.Depth (succ toNat)

/-- Bitstreams: the M-type of {name}`Geb.BitStream.sig` constructed from
W-types. -/
abbrev Stream := M sig

/-- An observation at a successor depth is termination or a bit with an
observation at the preceding depth. -/
def succEquiv (n : Depth.{0, 0}) : Approx sig (succ n) ≃ Layer (Approx sig n) :=
  (Geb.MType.succEquiv sig n).trans (layerEquiv _)

/-- The finite unfoldings of a coalgebra in layer form. -/
def corecApprox {α : Type*} (step : α → Layer α) : ∀ n : Depth.{0, 0}, α → Approx sig n :=
  Geb.MType.corecApprox fun a ↦ (layerEquiv α).symm (step a)

/-- Successor unfolding reads one layer and observes its continuation. -/
theorem corecApprox_succ {α : Type*} (step : α → Layer α) (n : Depth.{0, 0}) (a : α) :
    succEquiv n (corecApprox step (succ n) a) =
      (step a).map (Prod.map id (corecApprox step n)) := by
  rw [succEquiv, Equiv.trans_apply, corecApprox, Geb.MType.corecApprox_succ, layerEquiv_map,
    Equiv.apply_symm_apply]

/-- The observations at a depth are the bit lists of bounded length. -/
def prefixEquiv (n : Depth.{0, 0}) : Approx sig n ≃ Prefix (toNat n) :=
  (Geb.MType.approxEquiv sig n).trans (Geb.BitStream.approxEquiv (toNat n))

/-- The corecursor of a coalgebra in layer form. -/
def corec {α : Type*} (step : α → Layer α) : α → Stream :=
  M.corec fun a ↦ (layerEquiv α).symm (step a)

/-- Terminate, or prepend a bit. -/
def mk (x : Layer Stream) : Stream := M.mk ((layerEquiv _).symm x)

/-- Termination, or the first bit and the stream after it. -/
def dest (w : Stream) : Layer Stream := layerEquiv _ w.dest

/-- The destructor inverts the constructor. -/
@[simp] theorem dest_mk (x : Layer Stream) : dest (mk x) = x := by
  rw [dest, mk, M.dest_mk, Equiv.apply_symm_apply]

/-- The corecursor is a morphism of coalgebras in layer form. -/
theorem dest_corec {α : Type*} (step : α → Layer α) (a : α) :
    dest (corec step a) = (step a).map (Prod.map id (corec step)) := by
  rw [dest, corec, M.dest_corec, layerEquiv_map, Equiv.apply_symm_apply]

/-- The stream after the first bit; a terminated stream is its own tail. -/
def tail (w : Stream) : Stream := ((dest w).map Prod.snd).getD (mk none)

/-- Bitstreams are terminating or infinite sequences of bits. -/
def seqEquiv : Stream ≃ Stream'.Seq Bool := (Geb.MType.mEquiv sig).trans Geb.BitStream.seqEquiv

/-- The corecursor is the corecursor of sequences. -/
theorem seqEquiv_corec {α : Type*} (step : α → Layer α) (a : α) :
    seqEquiv (corec step a) = Stream'.Seq.corec step a := by
  have h := (congrArg Geb.BitStream.seqEquiv
    (Geb.MType.mEquiv_corec (fun b ↦ (layerEquiv α).symm (step b)) a)).trans
      (Geb.BitStream.seqEquiv_corec _ a)
  simp only [Equiv.apply_symm_apply] at h
  exact h

/-- Bitstreams are the bounded-list observations of the first development. -/
def observationsEquiv : Stream ≃ Observations := (Geb.MType.mEquiv sig).trans Geb.BitStream.mEquiv

/-- Embed a finite bitstring by corecursion on its destructor. -/
def ofW : sig.W → Stream := M.corec PFunctor.W.dest

/-- The embedding is the M-type embedding of the first development. -/
theorem mEquiv_ofW (w : sig.W) : Geb.MType.mEquiv sig (ofW w) = Geb.BitStream.ofW w :=
  Geb.MType.mEquiv_corec PFunctor.W.dest w

/-- The embedding is the inclusion of lists in sequences. -/
theorem seqEquiv_ofW (w : sig.W) : seqEquiv (ofW w) = Stream'.Seq.ofList (wEquiv w) :=
  (congrArg Geb.BitStream.seqEquiv (mEquiv_ofW w)).trans (Geb.BitStream.seqEquiv_ofW w)

end Geb.BitStream.WConstruction

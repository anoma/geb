import GebLean.LawvereER
import Mathlib.Computability.Primrec.List

/-!
# Translation of ER Terms to Mathlib's Primitive Recursive Predicate

For every `ERMor1 n` term `t`, the interpretation
`fun v : List.Vector ℕ n => t.interp v.get` is primitive recursive in the
sense of `Nat.Primrec'`.  This places the elementary recursive functions
strictly within the primitive recursive functions and gives a route to
proving that `erInterpFunctor` is not full via `not_primrec₂_ack`.
-/

namespace GebLean

open Nat

theorem natBSum_rec (b : ℕ) (f : ℕ → ℕ) :
    natBSum b f = b.rec 0 (fun y IH => IH + f y) := rfl

theorem natBProd_rec (b : ℕ) (f : ℕ → ℕ) :
    natBProd b f = b.rec 1 (fun y IH => IH * f y) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem fin_tail_get {n : ℕ} (v : List.Vector ℕ (n + 1)) :
    Fin.tail (v.get) = v.tail.get := by
  funext j
  simp [Fin.tail, List.Vector.get_tail_succ]

/-- Every elementary recursive term's interpretation is primitive
recursive. -/
theorem ERMor1.toPrimrec' :
    ∀ {n : ℕ} (t : ERMor1 n),
      Nat.Primrec' (fun v : List.Vector ℕ n => t.interp v.get)
  | _, ERMor1.zero => by
    change Nat.Primrec' (fun _ : List.Vector ℕ 0 => 0)
    exact Nat.Primrec'.zero
  | _, ERMor1.succ => by
    change Nat.Primrec' (fun v : List.Vector ℕ 1 =>
      (v.get 0).succ)
    have hsucc : Nat.Primrec' (fun v : List.Vector ℕ 1 =>
        v.head.succ) := Nat.Primrec'.succ
    convert hsucc using 1
    funext v
    rw [List.Vector.get_zero]
  | _, ERMor1.proj i => by
    change Nat.Primrec' (fun v => v.get i)
    exact Nat.Primrec'.get i
  | _, ERMor1.sub => by
    change Nat.Primrec' (fun v : List.Vector ℕ 2 =>
      v.get 0 - v.get 1)
    have hsub : Nat.Primrec' (fun v : List.Vector ℕ 2 =>
        v.head - v.tail.head) := Nat.Primrec'.sub
    convert hsub using 1
    funext v
    rw [List.Vector.get_zero, show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
      ← List.Vector.get_tail_succ, List.Vector.get_zero]
  | _, ERMor1.comp f g => by
    change Nat.Primrec' (fun v =>
      f.interp (fun i => (g i).interp v.get))
    have hbase : Nat.Primrec' (fun a =>
        f.interp (List.Vector.ofFn
          (fun i => (g i).interp a.get)).get) :=
      Nat.Primrec'.comp
        (fun i v => (g i).interp v.get)
        (ERMor1.toPrimrec' f)
        (fun i => ERMor1.toPrimrec' (g i))
    convert hbase using 1
    funext a
    congr 1
    funext i
    rw [List.Vector.get_ofFn]
  | _, ERMor1.bsum (k := k) f => by
    change Nat.Primrec' (fun v : List.Vector ℕ (k+1) =>
      natBSum (v.get 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail v.get))))
    have h_ih_applied :
        Nat.Primrec' (fun a : List.Vector ℕ (k + 2) =>
          f.interp (a.head ::ᵥ a.tail.tail).get) := by
      have hc := Nat.Primrec'.comp
        (fun (i : Fin (k+1)) (a : List.Vector ℕ (k+2)) =>
          (a.head ::ᵥ a.tail.tail).get i)
        (ERMor1.toPrimrec' f)
        (fun i => by
          refine Fin.cases ?_ ?_ i
          · exact Nat.Primrec'.head
          · intro j
            exact (Nat.Primrec'.get j).tail.tail)
      convert hc using 1
      funext a
      congr 1
      funext i
      rw [List.Vector.get_ofFn]
    have h_step :
        Nat.Primrec' (fun a : List.Vector ℕ (k + 2) =>
          a.tail.head +
          f.interp (a.head ::ᵥ a.tail.tail).get) := by
      have hadd : Nat.Primrec' (fun w : List.Vector ℕ 2 =>
          w.head + w.tail.head) := Nat.Primrec'.add
      have hc := Nat.Primrec'.comp
        (fun (i : Fin 2) (a : List.Vector ℕ (k+2)) =>
          if i = 0 then a.tail.head
          else f.interp (a.head ::ᵥ a.tail.tail).get)
        hadd
        (fun i => by
          refine Fin.cases ?_ ?_ i
          · exact Nat.Primrec'.head.tail
          · intro j
            have hj : j = 0 := Subsingleton.elim _ _
            subst hj
            exact h_ih_applied)
      convert hc using 1
    have h_prec := Nat.Primrec'.prec
      (Nat.Primrec'.const (n := k) 0) h_step
    convert h_prec using 1
    funext v
    rw [List.Vector.get_zero, natBSum_rec]
    congr 1
    funext y ih
    simp only [List.Vector.head_cons, List.Vector.tail_cons]
    congr 2
    funext j
    refine Fin.cases ?_ ?_ j
    · simp [List.Vector.get_zero]
    · intro j'
      simp [Fin.cons_succ, List.Vector.get_cons_succ,
        fin_tail_get]
  | _, ERMor1.bprod (k := k) f => by
    change Nat.Primrec' (fun v : List.Vector ℕ (k+1) =>
      natBProd (v.get 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail v.get))))
    have h_ih_applied :
        Nat.Primrec' (fun a : List.Vector ℕ (k + 2) =>
          f.interp (a.head ::ᵥ a.tail.tail).get) := by
      have hc := Nat.Primrec'.comp
        (fun (i : Fin (k+1)) (a : List.Vector ℕ (k+2)) =>
          (a.head ::ᵥ a.tail.tail).get i)
        (ERMor1.toPrimrec' f)
        (fun i => by
          refine Fin.cases ?_ ?_ i
          · exact Nat.Primrec'.head
          · intro j
            exact (Nat.Primrec'.get j).tail.tail)
      convert hc using 1
      funext a
      congr 1
      funext i
      rw [List.Vector.get_ofFn]
    have h_step :
        Nat.Primrec' (fun a : List.Vector ℕ (k + 2) =>
          a.tail.head *
          f.interp (a.head ::ᵥ a.tail.tail).get) := by
      have hmul : Nat.Primrec' (fun w : List.Vector ℕ 2 =>
          w.head * w.tail.head) := Nat.Primrec'.mul
      have hc := Nat.Primrec'.comp
        (fun (i : Fin 2) (a : List.Vector ℕ (k+2)) =>
          if i = 0 then a.tail.head
          else f.interp (a.head ::ᵥ a.tail.tail).get)
        hmul
        (fun i => by
          refine Fin.cases ?_ ?_ i
          · exact Nat.Primrec'.head.tail
          · intro j
            have hj : j = 0 := Subsingleton.elim _ _
            subst hj
            exact h_ih_applied)
      convert hc using 1
    have h_prec := Nat.Primrec'.prec
      (Nat.Primrec'.const (n := k) 1) h_step
    convert h_prec using 1
    funext v
    rw [List.Vector.get_zero, natBProd_rec]
    congr 1
    funext y ih
    simp only [List.Vector.head_cons, List.Vector.tail_cons]
    congr 2
    funext j
    refine Fin.cases ?_ ?_ j
    · simp [List.Vector.get_zero]
    · intro j'
      simp [Fin.cons_succ, List.Vector.get_cons_succ,
        fin_tail_get]

end GebLean

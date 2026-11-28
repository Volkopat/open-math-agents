import OMAStatements.S_oeis_a234307
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset OMA.S_oeis_a234307

private theorem interval (m : ℕ) (f : ℕ → ℚ) :
    ∑ j ∈ Icc 1 m, f j = ∑ j ∈ range m, f (j+1) := by
  have h : Icc 1 m = Ico 1 (m+1) := by ext; simp
  rw [h, sum_Ico_eq_sum_range]
  simp [add_comm]

private theorem pairs (m : ℕ) (f : ℕ → ℚ) :
    ∑ j ∈ range (2*m), f j = ∑ j ∈ range m, (f (2*j) + f (2*j+1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1)=2*m+1+1 by omega, sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a234307.main := by
  intro n _
  let g (s j : ℕ) : ℚ := Nat.gcd (j+1) (2^s*n)
  have ev (s j : ℕ) : g (s+1) (2*j+1) = 2*g s j := by
    simp [g, pow_succ', mul_assoc, show 2*j+1+1=2*(j+1) by omega, Nat.gcd_mul_left]
  have od (s j : ℕ) : g s (2*j) = g 0 (2*j) := by
    have h : Nat.Coprime 2 (2*j+1) := by
      change Nat.gcd 2 (2*j+1) = 1
      rw [Nat.gcd_rec]
      simp
    simp [g, (h.pow_left s).gcd_mul_left_cancel_right n]
  have per (j : ℕ) : g 0 (2*(n+j)) = g 0 (2*j) := by
    simp [g, show 2*(n+j)+1=2*j+1+2*n by omega]
  have hA : (a n : ℚ) = ∑ j ∈ range n, g 1 j := by
    unfold a
    rw [Nat.cast_sum, interval]
    apply sum_congr rfl
    intro j hj
    rw [Nat.gcd_sub_self_left (by have := mem_range.mp hj; omega), Nat.gcd_comm]
    rfl
  rw [hA, interval, show 4*n=2*(2*n) by omega]
  change _ = 1/4 * ∑ j ∈ range (2*(2*n)), (-1 : ℚ) ^ (j+1) * g 3 j
  rw [pairs]
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one, neg_one_mul,
    od 3, ev 2, sum_add_distrib, sum_neg_distrib, ← mul_sum]
  rw [pairs (n) (g 2)]
  simp only [od 2, ev 1, sum_add_distrib, ← mul_sum]
  rw [two_mul n, sum_range_add]
  simp only [per]
  ring

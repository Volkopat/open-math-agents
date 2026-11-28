import OMAStatements.S_oeis_a373561
import Mathlib

namespace OMA.S_oeis_a373561

open Finset

lemma weight_group (n : ℕ) (hn : 0 < n) (w : ℤ) :
    (∑ k ∈ Icc 1 n, if Int.gcd w n = k then w else 0) = w := by
  have hg : Int.gcd w n ∈ Icc 1 n := by
    change Nat.gcd w.natAbs n ∈ Icc 1 n
    exact mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_right _ hn, Nat.le_of_dvd hn (Nat.gcd_dvd_right _ _)⟩
  simp only [Finset.sum_ite_eq, if_pos hg]

def squareSum (n : ℕ) : ℤ := ∑ j ∈ range n, ((j + 1 : ℕ) : ℤ)^2

lemma grouped_eq (n : ℕ) : groupedSum n = (n : ℤ)^2 * squareSum n := by
  cases n with
  | zero => simp [groupedSum]
  | succ n =>
    unfold groupedSum
    simp_rw [sum_comm (s := Icc 1 (n+1)) (t := range (n+1))]
    simp_rw [weight_group _ (Nat.succ_pos n)]
    simp only [weight, sum_sub_distrib, sum_add_distrib, sum_const, card_range, nsmul_eq_mul,
      ← Finset.mul_sum, squareSum]
    ring

lemma six_squareSum (n : ℕ) : 6 * squareSum n = (n : ℤ) * (n+1) * (2*n+1) := by
  induction n with
  | zero => simp [squareSum]
  | succ n ih =>
    simp only [squareSum, sum_range_succ] at *
    push_cast at ih ⊢
    linear_combination ih

theorem granvik (n : ℕ) :
    (1/3 : ℚ) * n^5 + (1/2 : ℚ) * n^4 + (1/6 : ℚ) * n^3 = (groupedSum n : ℚ) := by
  rw [grouped_eq]
  push_cast
  have h : (6 : ℚ) * (squareSum n : ℚ) = (n : ℚ) * (n+1) * (2*n+1) := by
    exact_mod_cast six_squareSum n
  linear_combination -(n : ℚ)^2 / 6 * h

end OMA.S_oeis_a373561

theorem OMA.solution : type_of% @OMA.S_oeis_a373561.main := OMA.S_oeis_a373561.granvik

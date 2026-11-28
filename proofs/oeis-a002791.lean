import OMAStatements.S_oeis_a002791
import Mathlib

/-!
Credit: @ivillar
Proof: 4*sigma(n) - a(n) = Sum_{d|n, d <= 4} d*(4 - d) = 3 + 4*[2|n] + 3*[3|n] (the divisor 4
contributes 0), which is f(n mod 6).
-/

namespace OMAA002791Helpers
open OMA.S_oeis_a002791

theorem small_divisors (n : ℕ) (hn : n ≠ 0) :
    (n.divisors.filter (fun d => d ≤ 4)) = (Finset.Icc 1 4).filter (fun d => d ∣ n) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd, -⟩, h4⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn), h4⟩, hd⟩
  · rintro ⟨⟨-, h4⟩, hd⟩
    exact ⟨⟨hd, hn⟩, h4⟩

theorem key (n : ℕ) (hn : n ≠ 0) :
    (a n : ℤ) = 4 * (ArithmeticFunction.sigma 1 n : ℤ) -
      ∑ d ∈ (Finset.Icc 1 4).filter (fun d => d ∣ n), ((d : ℤ) * (4 - d)) := by
  rw [← small_divisors n hn]
  have hsplit : (∑ d ∈ n.divisors with d ≤ 4, (d : ℤ)) + (∑ d ∈ n.divisors with 4 < d, (d : ℤ)) =
      ∑ d ∈ n.divisors, (d : ℤ) := by
    rw [← Finset.sum_filter_add_sum_filter_not n.divisors (fun d => d ≤ 4)]
    congr 1
    exact Finset.sum_congr (Finset.filter_congr (fun d _ => by omega)) (fun _ _ => rfl)
  have hσ : (ArithmeticFunction.sigma 1 n : ℤ) = ∑ d ∈ n.divisors, (d : ℤ) := by
    rw [ArithmeticFunction.sigma_one_apply]
    push_cast
    rfl
  have hQ : ∑ d ∈ n.divisors with d ≤ 4, ((d : ℤ) * (4 - d)) =
      4 * ∑ d ∈ n.divisors with d ≤ 4, (d : ℤ) - ∑ d ∈ n.divisors with d ≤ 4, (d : ℤ) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  unfold a
  push_cast
  rw [hσ, ← hsplit, hQ]
  ring

theorem f_eq (r : ℕ) (hr : r < 6) :
    f r = if r = 0 then 10 else if r = 1 then 3 else if r = 2 then 7 else if r = 3 then 6 else
      if r = 4 then 7 else 3 := by
  interval_cases r <;> rfl

end OMAA002791Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a002791.main := by
  intro n hn
  rw [OMAA002791Helpers.key n (by omega), Finset.sum_filter,
    Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 3 + 1),
    Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 2 + 1),
    Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 1 + 1), Finset.Icc_self, Finset.sum_singleton]
  norm_num
  have hr : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rw [OMAA002791Helpers.f_eq (n % 6) hr]
  split_ifs <;> omega

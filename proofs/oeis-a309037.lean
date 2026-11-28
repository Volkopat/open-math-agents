import OMAStatements.S_oeis_a309037

namespace OMA.S_oeis_a309037

open PowerSeries Finset


lemma first_sum (n : ℕ) : 19 * (∑ k ∈ range n, 2 ^ (k + 1) * 10 ^ k : ℚ) = 2 * (20 ^ n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (20 : ℚ) ^ n = 2 ^ n * 10 ^ n := by rw [← mul_pow]; norm_num
    rw [sum_range_succ, mul_add]
    linear_combination ih + (-38) * h

lemma second_sum (m : ℕ) :
    2 * (∑ k ∈ range m, 2 ^ (k + 1) * 10 ^ (2 * m - k) : ℚ) = 5 * (100 ^ m - 20 ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have e : ∑ k ∈ range m, (2 : ℚ) ^ (k + 1) * 10 ^ (2 * (m + 1) - k) =
        100 * ∑ k ∈ range m, (2 : ℚ) ^ (k + 1) * 10 ^ (2 * m - k) := by
      rw [mul_sum]
      refine sum_congr rfl (fun k hk => ?_)
      have hk' : k < m := mem_range.mp hk
      rw [show 2 * (m + 1) - k = (2 * m - k) + 2 by omega, pow_add]
      ring
    have h : (20 : ℚ) ^ m = 2 ^ m * 10 ^ m := by rw [← mul_pow]; norm_num
    rw [e, show 2 * (m + 1) - m = m + 2 by omega]
    linear_combination 100 * ih + (-400) * h

lemma a_succ_q (m : ℕ) : (a (m + 1) : ℚ) = (∑ k ∈ range (m + 1), (2 : ℚ) ^ (k + 1) * 10 ^ k) +
    ∑ k ∈ range m, (2 : ℚ) ^ (k + 1) * 10 ^ (2 * m - k) := by
  have e : ∀ k, 2 * (m + 1) - 2 - k = 2 * m - k := fun k => by omega
  simp only [a, e, show m + 1 - 1 = m by omega]
  push_cast
  rfl

/-- Barker's closed form, for n >= 1. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n →
    (a n : ℚ) = (-80 - 3 * 4 ^ n * 5 ^ (1 + n) + 19 * 100 ^ n) / 760 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := first_sum (m + 1)
  have h2 := second_sum m
  have h20 : (20 : ℚ) ^ m = 4 ^ m * 5 ^ m := by
    rw [← mul_pow]; norm_num
  rw [a_succ_q]
  linear_combination (1 / 19) * h1 + (1 / 2) * h2 + (-15 / 38) * h20

lemma a_q (m : ℕ) : (a (m + 1) : ℚ) = (-80 - 15 * 20 ^ (m + 1) + 19 * 100 ^ (m + 1)) / 760 := by
  rw [closed_form (m + 1) (by omega)]
  have h20 : (20 : ℚ) ^ (m + 1) = 4 ^ (m + 1) * 5 ^ (m + 1) := by
    rw [← mul_pow]; norm_num
  linear_combination (15 / 760) * h20

lemma a_rec (m : ℕ) : (a (m + 4) : ℚ) = 121 * a (m + 3) - 2120 * a (m + 2) + 2000 * a (m + 1) := by
  rw [a_q (m + 3), a_q (m + 2), a_q (m + 1), a_q m]
  ring

lemma a_one : a 1 = 2 := by decide

lemma a_two : a 2 = 242 := by decide

lemma a_three : a 3 = 24842 := by decide

/-- Barker's recurrence, for n > 3, in the integers. -/
theorem recurrence : ∀ n : ℕ, 3 < n →
    (a n : ℤ) = 121 * a (n - 1) - 2120 * a (n - 2) + 2000 * a (n - 3) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega]
  have h := a_rec m
  exact_mod_cast h

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = 2x(1 - 10x)(1 + 10x)/((1 - x)(1 - 20x)(1 - 100x)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (1 - 20 * X) * (1 - 100 * X)) = 2 * X * (1 - 10 * X) * (1 + 10 * X) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 20 * X) * (1 - 100 * X)) =
      A - C (121 : ℚ) * (A * X ^ 1) + C (2120 : ℚ) * (A * X ^ 2) - C (2000 : ℚ) * (A * X ^ 3) := by
    rw [show (C (121 : ℚ) : ℚ⟦X⟧) = 121 from map_ofNat C 121,
      show (C (2120 : ℚ) : ℚ⟦X⟧) = 2120 from map_ofNat C 2120,
      show (C (2000 : ℚ) : ℚ⟦X⟧) = 2000 from map_ofNat C 2000]
    ring
  have e2 : (2 : ℚ⟦X⟧) * X * (1 - 10 * X) * (1 + 10 * X) = C (2 : ℚ) * X ^ 1 - C (200 : ℚ) * X ^ 3 := by
    rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2,
      show (C (200 : ℚ) : ℚ⟦X⟧) = 200 from map_ofNat C 200]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> simp [a_one, a_two, a_three] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h' := a_rec m
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega, show ¬ m + 4 = 0 by omega, show ¬ m + 3 = 0 by omega,
      show ¬ m + 2 = 0 by omega, show ¬ m + 1 = 0 by omega, show 1 ≤ m + 4 by omega,
      show 2 ≤ m + 4 by omega, show 3 ≤ m + 4 by omega, if_true, if_false]
    linear_combination h'

/-- All three of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 20 * X) * (1 - 100 * X)) = 2 * X * (1 - 10 * X) * (1 + 10 * X) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (-80 - 3 * 4 ^ n * 5 ^ (1 + n) + 19 * 100 ^ n) / 760) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 121 * a (n - 1) - 2120 * a (n - 2) + 2000 * a (n - 3)) :=
  ⟨gf, closed_form, recurrence⟩

end OMA.S_oeis_a309037

theorem OMA.solution : type_of% @OMA.S_oeis_a309037.main :=
  OMA.S_oeis_a309037.conjecture

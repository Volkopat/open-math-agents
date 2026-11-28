import OMAStatements.S_oeis_a032086
import Mathlib

/-!
# A032086: the conjectured formulas

For k ≥ 2, a(k) = (3^k − 3^ceil(k/2))/2. The power 3^k satisfies x(n) = 3x(n−1) + 3x(n−2) − 9x(n−3)
identically, and so does c(k) = 3^ceil(k/2), because c(n) = 3c(n−2) and c(n−1) = 3c(n−3); this gives
the recurrence for n > 4. Multiplying the series by (1 − 3x)(1 − 3x²) = 1 − 3x − 3x² + 9x³ kills
every coefficient from x⁵ on, and the first five come from a(0..4) = 0, 3, 3, 9, 36. The parity
formulas are the defining formula with ceil(n/2) = n/2 or (n+1)/2.
-/

open OMA.S_oeis_a032086

theorem a_ge (k : ℕ) (hk : 2 ≤ k) : a k = ((3:ℚ)^k - (3:ℚ)^((k+1)/2))/2 := by
  unfold a
  rw [if_neg (by omega), if_neg (by omega)]

theorem rec (m : ℕ) : a (m + 5) = 3 * a (m + 4) + 3 * a (m + 3) - 9 * a (m + 2) := by
  rw [a_ge _ (by omega), a_ge _ (by omega), a_ge _ (by omega), a_ge _ (by omega),
    show (m + 5 + 1) / 2 = (m + 3 + 1) / 2 + 1 by omega,
    show (m + 4 + 1) / 2 = (m + 2 + 1) / 2 + 1 by omega]
  generalize (m + 3 + 1) / 2 = A
  generalize (m + 2 + 1) / 2 = B
  ring

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a032086.main := by
  have hrec : ∀ n : ℕ, 4 < n → a n = 3 * a (n - 1) + 3 * a (n - 2) - 9 * a (n - 3) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega]
    exact rec m
  refine ⟨hrec, ?_, ?_, ?_⟩
  · have v0 : a 0 = 0 := by simp [a]
    have v1 : a 1 = 3 := by simp [a]
    have v2 : a 2 = 3 := by rw [a_ge 2 (by omega)]; norm_num
    have v3 : a 3 = 9 := by rw [a_ge 3 (by omega)]; norm_num
    have v4 : a 4 = 36 := by rw [a_ge 4 (by omega)]; norm_num
    have hexp : ((1 - C 3 * X) * (1 - C 3 * X ^ 2)) * series =
        series - C 3 * (X ^ 1 * series) - C 3 * (X ^ 2 * series) + C 9 * (X ^ 3 * series) := by
      have h9 : (C 9 : ℚ⟦X⟧) = C 3 * C 3 := by rw [← map_mul]; norm_num
      rw [h9]
      ring
    rw [hexp]
    ext n
    unfold series
    simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_X]
    rcases Nat.lt_or_ge n 5 with hn | hn
    · interval_cases n <;> simp [v0, v1, v2, v3, v4] <;> norm_num
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), hrec n (by omega)]
      simp only [show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
        show n ≠ 4 by omega, if_false]
      ring
  · intro n hn he
    rw [a_ge n (by omega), show (n + 1) / 2 = n / 2 by obtain ⟨k, rfl⟩ := he; omega]
    ring
  · intro n hn ho
    rw [a_ge n (by omega)]
    ring

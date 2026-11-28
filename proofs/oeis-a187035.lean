import OMAStatements.S_oeis_a187035

-- Problem: A187035, Mathar's recurrence and generating function for the diagonal sums of A187034.
-- Credit: @ShoQo
-- Proof: T(n-k, k) = (-1)^n exactly when n/3 <= k <= n/2, so a(n) = (-1)^n (floor(n/2) + 1 -
-- ceil(n/3)); the recurrence is then an identity of floors, and the denominator expands to
-- 1 - x^2 + x^3 - x^5.

open PowerSeries OMA.S_oeis_a187035

namespace OMA_A187035_Proof

lemma a_closed (n : ℕ) : a n = (-1) ^ n * ((n / 2 + 1 - (n + 2) / 3 : ℕ) : ℤ) := by
  have hterm : ∀ k ∈ Finset.range (n + 1),
      T (n - k) k = if 2 * k ≤ n ∧ n ≤ 3 * k then (-1) ^ n else 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    unfold T
    by_cases h1 : 2 * k ≤ n
    · have hpos : 0 < Nat.choose k (n - k - k) ↔ n ≤ 3 * k := by
        rw [Nat.pos_iff_ne_zero, Ne, Nat.choose_eq_zero_iff]; omega
      have hpar : ((-1 : ℤ)) ^ (n - k - k) = (-1) ^ n := by
        rw [show n = (n - k - k) + 2 * k by omega, pow_add, pow_mul]; norm_num
        rw [show n - k - k + 2 * k - k - k = n - k - k by omega]
      by_cases h2 : n ≤ 3 * k
      · rw [if_pos ⟨by omega, hpos.mpr h2⟩, if_pos ⟨h1, h2⟩, hpar]
      · rw [if_neg (by rintro ⟨_, h⟩; exact h2 (hpos.mp h)), if_neg (by rintro ⟨_, h⟩; exact h2 h)]
    · rw [if_neg (by omega), if_neg (by omega)]
  unfold a
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  have : (Finset.range (n + 1)).filter (fun k => 2 * k ≤ n ∧ n ≤ 3 * k)
      = Finset.Icc ((n + 2) / 3) (n / 2) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc]

lemma rec (n : ℕ) (hn : 5 ≤ n) : a n = a (n - 2) - a (n - 3) + a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [a_closed, a_closed, a_closed, a_closed, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 5 = m by omega]
  have h3 : ((-1 : ℤ)) ^ (m + 5) = -(-1) ^ m := by rw [pow_add]; norm_num
  have h4 : ((-1 : ℤ)) ^ (m + 3) = -(-1) ^ m := by rw [pow_add]; norm_num
  have h5 : ((-1 : ℤ)) ^ (m + 2) = (-1) ^ m := by rw [pow_add]; norm_num
  rw [h3, h4, h5]
  have key : ((m + 5) / 2 + 1 - (m + 5 + 2) / 3 : ℕ) + ((m / 2 + 1 - (m + 2) / 3) : ℕ)
      = ((m + 3) / 2 + 1 - (m + 3 + 2) / 3 : ℕ) + ((m + 2) / 2 + 1 - (m + 2 + 2) / 3 : ℕ) := by
    omega
  have key' : (((m + 5) / 2 + 1 - (m + 5 + 2) / 3 : ℕ) : ℤ) + (((m / 2 + 1 - (m + 2) / 3) : ℕ) : ℤ)
      = (((m + 3) / 2 + 1 - (m + 3 + 2) / 3 : ℕ) : ℤ) + (((m + 2) / 2 + 1 - (m + 2 + 2) / 3 : ℕ) : ℤ) := by
    exact_mod_cast key
  linear_combination (-(-1 : ℤ) ^ m) * key'

end OMA_A187035_Proof

open OMA_A187035_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a187035.main := by
  refine ⟨rec, ?_⟩
  rw [show ((1 - X) * (1 - X + X ^ 2) * (1 + X) ^ 2 : PowerSeries ℤ)
      = 1 - X ^ 2 + X ^ 3 - X ^ 5 by ring]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, coeff_mul_X_pow', coeff_mk, coeff_one]
  rcases lt_or_ge n 5 with h | h
  · interval_cases n <;> simp [a_closed]
  · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega), rec n h]
    ring


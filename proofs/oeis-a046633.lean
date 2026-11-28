import OMAStatements.S_oeis_a046633

open OMA.S_oeis_a046633 PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a046633.main := by
  have hb (n : ℕ) : b (n + 3) = b n := by simp [b, Nat.add_mod_right]
  -- 5^3 = 125 ≡ 1 (mod 31) and b has period 3, so 31 divides 5^(n+2) + 2 b(n)
  have hdvd (n : ℕ) : 31 ∣ 5 ^ (n + 2) + 2 * b n := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n, ih with
      | 0, _ => decide
      | 1, _ => decide
      | 2, _ => decide
      | m + 3, ih =>
        have h := ih m (by omega)
        rw [hb m, show m + 3 + 2 = m + 2 + 3 by ring, pow_add,
          show 5 ^ (m + 2) * 5 ^ 3 + 2 * b m = 124 * 5 ^ (m + 2) + (5 ^ (m + 2) + 2 * b m) by ring]
        exact dvd_add (dvd_mul_of_dvd_left (by norm_num) _) h
  have ha (n : ℕ) : (31 : ℤ) * a n = 5 ^ (n + 2) + 2 * b n := by
    have := Nat.mul_div_cancel' (hdvd n)
    simp only [a]
    exact_mod_cast this
  have hrec (m : ℕ) : (a (m + 4) : ℤ) = 5 * a (m + 3) + a (m + 1) - 5 * a m := by
    have h4 := ha (m + 4)
    have h3 := ha (m + 3)
    have h1 := ha (m + 1)
    have h0 := ha m
    rw [show b (m + 4) = b (m + 1) from hb (m + 1)] at h4
    rw [hb m] at h3
    have : (31 : ℤ) * (a (m + 4) - (5 * a (m + 3) + a (m + 1) - 5 * a m)) = 0 := by
      linear_combination h4 - 5 * h3 - h1 + 5 * h0
    omega
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 3 = m + 1 by omega,
      show m + 4 - 4 = m by omega]
    exact hrec m
  · have hD : denominator = 1 - C 5 * X ^ 1 - X ^ 3 + C 5 * X ^ 4 := by
      simp only [denominator]
      ring
    ext n
    rw [hD, numerator, generating]
    simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add, coeff_C_mul,
      coeff_X_pow_mul', coeff_mk, coeff_one, coeff_X_pow]
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | rfl | rfl | h
    · norm_num [a, b]
    · norm_num [a, b]
    · norm_num [a, b]
    · norm_num [a, b]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have hq : (a (m + 4) : ℚ) = 5 * a (m + 3) + a (m + 1) - 5 * a m := by
        exact_mod_cast hrec m
      simp only [show 1 ≤ m + 4 by omega, show 3 ≤ m + 4 by omega, show 4 ≤ m + 4 by omega,
        if_true, show m + 4 - 1 = m + 3 by omega, show m + 4 - 3 = m + 1 by omega,
        show m + 4 - 4 = m by omega, show m + 4 ≠ 0 by omega, show m + 4 ≠ 2 by omega,
        show m + 4 ≠ 3 by omega, if_false]
      linarith

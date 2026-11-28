import OMAStatements.S_oeis_a159715
import Mathlib

/-!
# A159715: `a(n) = 2 n 3^(n-2)` — generating function, closed form and recurrence

For `n ≥ 2`, `a n = 2 n 3^(n-2)`.  Multiplying the generating function by
`(1 - 3X)² = 1 - 6X + 9X²` gives the coefficients `a n - 6 a (n-1) + 9 a (n-2)`, which are
`0, 0, 4, -6` for `n = 0, 1, 2, 3` and `0` afterwards, because
`2(m+4) · 9 - 6 · 2(m+3) · 3 + 9 · 2(m+2) = 0`.  The recurrence is the same identity.
-/

open OMA.S_oeis_a159715 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a159715.main := by
  -- the value of `a` from index `2` on
  have ha : ∀ m : ℕ, a (m + 2) = 2 * ((m : ℤ) + 2) * 3 ^ m := by
    intro m
    unfold a
    rw [if_neg (by omega)]
    have e : m + 2 - 2 = m := by omega
    rw [e]
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · have el : ∀ S : PowerSeries ℚ, S * (1 - 3 * X) ^ 2 =
        S * X ^ 0 - C 6 * (S * X ^ 1) + C 9 * (S * X ^ 2) := by
      intro S
      simp only [map_ofNat]
      ring
    have er : (2 * X ^ 2 * (2 - 3 * X) : PowerSeries ℚ) = X ^ 2 * C 4 - X ^ 3 * C 6 := by
      simp only [map_ofNat]
      ring
    rw [el, er]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, coeff_mk]
    rcases n with _ | _ | _ | _ | n
    · simp [a]
    · simp [a]
    · simp [a]
    · simp [a]
      norm_num
    · have h1 : n + 4 - 0 = n + 2 + 2 := rfl
      have h2 : n + 4 - 1 = n + 1 + 2 := rfl
      have h3 : n + 4 - 2 = n + 2 := rfl
      rw [h1, h2, h3, ha (n + 2), ha (n + 1), ha n]
      simp
      push_cast
      ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have e : m + 2 - 2 = m := by omega
    rw [ha m, e]
    push_cast
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have e1 : m + 4 - 1 = m + 1 + 2 := by omega
    have e2 : m + 4 - 2 = m + 2 := by omega
    have e0 : m + 4 = m + 2 + 2 := by omega
    rw [e1, e2, e0, ha (m + 2), ha (m + 1), ha m]
    push_cast
    ring

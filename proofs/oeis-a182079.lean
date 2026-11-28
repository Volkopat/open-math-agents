import OMAStatements.S_oeis_a182079
import Mathlib

/-!
Credit: @ivillar
Proof idea (as in Sela Fried's remark that the g.f. is correct): a(n+6) = a(n) + 2n + 4 + (n mod 2),
so the denominator (1-x)(1-x^2)(1-x^6) annihilates the sequence beyond the numerator's degree;
the first nine coefficients are checked directly.
-/

namespace OMAA182079Helpers
open PowerSeries OMA.S_oeis_a182079

def f (x : ℤ) : ℤ := x * ((x - 1) / 2) / 3

theorem a_eq (n : ℕ) : a n = f n := by
  unfold a f
  have e1 : ⌊((n : ℚ) - 1) / 2⌋ = ((n : ℤ) - 1) / 2 := by
    have := Rat.floor_intCast_div_natCast ((n : ℤ) - 1) 2
    push_cast at this
    exact this
  rw [e1]
  have e2 := Rat.floor_intCast_div_natCast ((n : ℤ) * (((n : ℤ) - 1) / 2)) 3
  push_cast at e2
  exact e2

theorem f_add_six (x : ℤ) : f (x + 6) = f x + 2 * x + 4 + x % 2 := by
  unfold f
  rcases Int.even_or_odd' x with ⟨k, rfl | rfl⟩
  · rw [show (2 * k + 6 - 1) / 2 = k + 2 by omega, show (2 * k - 1) / 2 = k - 1 by omega,
      show (2 * k + 6) * (k + 2) = 2 * k * (k - 1) + (4 * k + 4) * 3 by ring,
      Int.add_mul_ediv_right _ _ (by norm_num)]
    omega
  · rw [show (2 * k + 1 + 6 - 1) / 2 = k + 3 by omega, show (2 * k + 1 - 1) / 2 = k by omega,
      show (2 * k + 1 + 6) * (k + 3) = (2 * k + 1) * k + (4 * k + 7) * 3 by ring,
      Int.add_mul_ediv_right _ _ (by norm_num)]
    omega

theorem a_add_six (k j : ℕ) (hj : j = k + 6) : a j = a k + 2 * k + 4 + (k : ℤ) % 2 := by
  subst hj
  rw [a_eq, a_eq]
  push_cast
  exact f_add_six k

theorem coeff_mk_mul_X_pow (n k : ℕ) :
    coeff n (PowerSeries.mk a * X ^ k) = if k ≤ n then a (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

end OMAA182079Helpers

open PowerSeries OMAA182079Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a182079.main := by
  ext n
  have hD : ((1 - X) ^ 3 * (1 + X) ^ 2 * (X ^ 2 - X + 1) * (X ^ 2 + X + 1) : PowerSeries ℤ) =
      X ^ 0 - X ^ 1 - X ^ 2 + X ^ 3 - X ^ 6 + X ^ 7 + X ^ 8 - X ^ 9 := by ring
  have hN : (X ^ 3 * (X ^ 4 + X ^ 3 + X ^ 2 + 1) : PowerSeries ℤ) =
      X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3 := by ring
  rw [hD, hN]
  simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_X_pow, coeff_X_pow]
  rcases Nat.lt_or_ge n 9 with h | h
  · interval_cases n <;> simp [a_eq, f]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    have h0 := a_add_six m (m + 6) (by omega)
    have h1 := a_add_six (m + 1) (m + 7) (by omega)
    have h2 := a_add_six (m + 2) (m + 8) (by omega)
    have h3 := a_add_six (m + 3) (m + 9) (by omega)
    simp only [show 0 ≤ m + 9 by omega, show 1 ≤ m + 9 by omega, show 2 ≤ m + 9 by omega,
      show 3 ≤ m + 9 by omega, show 6 ≤ m + 9 by omega, show 7 ≤ m + 9 by omega,
      show 8 ≤ m + 9 by omega, show 9 ≤ m + 9 by omega, ↓reduceIte,
      show m + 9 - 0 = m + 9 by omega, show m + 9 - 1 = m + 8 by omega,
      show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega,
      show m + 9 - 6 = m + 3 by omega, show m + 9 - 7 = m + 2 by omega,
      show m + 9 - 8 = m + 1 by omega, show m + 9 - 9 = m by omega,
      show m + 9 ≠ 7 by omega, show m + 9 ≠ 6 by omega, show m + 9 ≠ 5 by omega,
      show m + 9 ≠ 3 by omega]
    push_cast at h0 h1 h2 h3
    omega

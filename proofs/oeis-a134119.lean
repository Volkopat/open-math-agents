import OMAStatements.S_oeis_a134119
import Mathlib

/-!
Credit: @ivillar
Proof idea (as in Sela Fried's remark that the g.f. is correct): a(n+10) = a(n) + 2, so
(1-x)(1-x^10) annihilates the sequence beyond the numerator degree; the first coefficients are
checked directly.
-/

namespace OMAA134119Helpers
open PowerSeries OMA.S_oeis_a134119

def f (x : ℤ) : ℤ := x ^ 2 / 10 - (x - 1) ^ 2 / 10

theorem a_eq (n : ℕ) : a n = f n := by
  unfold a f
  have e1 := Rat.floor_intCast_div_natCast ((n : ℤ) ^ 2) 10
  have e2 := Rat.floor_intCast_div_natCast (((n : ℤ) - 1) ^ 2) 10
  push_cast at e1 e2
  rw [e1, e2]

theorem f_add_ten (x : ℤ) : f (x + 10) = f x + 2 := by
  unfold f
  rw [show (x + 10) ^ 2 = x ^ 2 + (2 * x + 10) * 10 by ring,
    show (x + 10 - 1) ^ 2 = (x - 1) ^ 2 + (2 * x + 8) * 10 by ring,
    Int.add_mul_ediv_right _ _ (by norm_num), Int.add_mul_ediv_right _ _ (by norm_num)]
  ring

theorem a_add_ten (k j : ℕ) (hj : j = k + 10) : a j = a k + 2 := by
  subst hj
  rw [a_eq, a_eq]
  push_cast
  exact f_add_ten k

theorem coeff_mk_mul_X_pow (n k : ℕ) :
    coeff n (PowerSeries.mk a * X ^ k) = if k ≤ n then a (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

end OMAA134119Helpers

open PowerSeries OMAA134119Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a134119.main := by
  ext n
  have hD : (X ^ 11 - X ^ 10 - X + 1 : PowerSeries ℤ) = X ^ 11 - X ^ 10 - X ^ 1 + X ^ 0 := by
    ring
  have hN : (X ^ 4 * (X ^ 4 + 1) : PowerSeries ℤ) = X ^ 8 + X ^ 4 := by ring
  rw [hD, hN]
  simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_X_pow, coeff_X_pow]
  rcases Nat.lt_or_ge n 11 with h | h
  · interval_cases n <;> simp [a_eq, f]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
    have h0 := a_add_ten m (m + 10) (by omega)
    have h1 := a_add_ten (m + 1) (m + 11) (by omega)
    simp only [show 10 ≤ m + 11 by omega,
      ↓reduceIte,
      show m + 11 - 0 = m + 11 by omega, show m + 11 - 1 = m + 10 by omega,
      show m + 11 - 10 = m + 1 by omega, show m + 11 - 11 = m by omega,
      show m + 11 ≠ 4 by omega]
    omega

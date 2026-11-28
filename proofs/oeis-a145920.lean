import OMAStatements.S_oeis_a145920
import Mathlib

/-!
# A145920: recurrence and generating function

Here `x(2m) = m` and `x(2m + 1) = -m`, so with `P(t) = (27 t⁴ - 18 t³ - 3 t² + 2 t) / 8` we have
`a(2m) = P(m)` and `a(2m + 1) = P(-m)`.  Substituting these polynomials, the order-9 recurrence
becomes a polynomial identity in `m` on each parity class; it already holds from `n = 10` on.
The generating-function identity is the same statement read coefficientwise
(`(1 + X)⁴ (1 - X)⁵` is the recurrence operator), together with a direct check of the
coefficients `n = 0, …, 9`.
-/

namespace OMA.S_oeis_a145920

lemma x_even (m : ℕ) : x (2 * m) = (m : ℚ) := by
  unfold x
  rw [Nat.mul_div_cancel_left m (by norm_num), Even.neg_one_pow ⟨m, by ring⟩, mul_one]

lemma x_odd (m : ℕ) : x (2 * m + 1) = -(m : ℚ) := by
  unfold x
  have e : (2 * m + 1) / 2 = m := by omega
  rw [e, Odd.neg_one_pow ⟨m, rfl⟩]
  ring

lemma a_even (m : ℕ) : a (2 * m) =
    (27 * (m : ℚ) ^ 4 - 18 * (m : ℚ) ^ 3 - 3 * (m : ℚ) ^ 2 + 2 * (m : ℚ)) / 8 := by
  unfold a
  rw [x_even]

lemma a_odd (m : ℕ) : a (2 * m + 1) =
    (27 * (-(m : ℚ)) ^ 4 - 18 * (-(m : ℚ)) ^ 3 - 3 * (-(m : ℚ)) ^ 2 + 2 * (-(m : ℚ))) / 8 := by
  unfold a
  rw [x_odd]

lemma rec_even (k : ℕ) : a (2 * (k + 5)) = a (2 * (k + 4) + 1) + 4 * a (2 * (k + 4)) - 4 * a (2 * (k + 3) + 1) - 6 * a (2 * (k + 3)) + 6 * a (2 * (k + 2) + 1) + 4 * a (2 * (k + 2)) - 4 * a (2 * (k + 1) + 1) - a (2 * (k + 1)) + a (2 * k + 1) := by
  simp only [a_even, a_odd]
  push_cast
  ring

lemma rec_odd (k : ℕ) : a (2 * (k + 5) + 1) = a (2 * (k + 5)) + 4 * a (2 * (k + 4) + 1) - 4 * a (2 * (k + 4)) - 6 * a (2 * (k + 3) + 1) + 6 * a (2 * (k + 3)) + 4 * a (2 * (k + 2) + 1) - 4 * a (2 * (k + 2)) - a (2 * (k + 1) + 1) + a (2 * (k + 1)) := by
  simp only [a_even, a_odd]
  push_cast
  ring

/-- The recurrence in shifted form. -/
lemma rec_shift (j : ℕ) : a (j + 10) = a (j + 9) + 4 * a (j + 8) - 4 * a (j + 7) - 6 * a (j + 6) + 6 * a (j + 5) + 4 * a (j + 4) - 4 * a (j + 3) - a (j + 2) + a (j + 1) := by
  rcases Nat.even_or_odd' j with ⟨k, rfl | rfl⟩
  · have h := rec_even k
    simp only [show 2 * k + 10 = 2 * (k + 5) from by ring, show 2 * k + 9 = 2 * (k + 4) + 1 from by ring, show 2 * k + 8 = 2 * (k + 4) from by ring, show 2 * k + 7 = 2 * (k + 3) + 1 from by ring, show 2 * k + 6 = 2 * (k + 3) from by ring, show 2 * k + 5 = 2 * (k + 2) + 1 from by ring, show 2 * k + 4 = 2 * (k + 2) from by ring, show 2 * k + 3 = 2 * (k + 1) + 1 from by ring, show 2 * k + 2 = 2 * (k + 1) from by ring, show 2 * k + 1 = 2 * k + 1 from by ring]
    exact h
  · have h := rec_odd k
    simp only [show 2 * k + 1 + 10 = 2 * (k + 5) + 1 from by ring, show 2 * k + 1 + 9 = 2 * (k + 5) from by ring, show 2 * k + 1 + 8 = 2 * (k + 4) + 1 from by ring, show 2 * k + 1 + 7 = 2 * (k + 4) from by ring, show 2 * k + 1 + 6 = 2 * (k + 3) + 1 from by ring, show 2 * k + 1 + 5 = 2 * (k + 3) from by ring, show 2 * k + 1 + 4 = 2 * (k + 2) + 1 from by ring, show 2 * k + 1 + 3 = 2 * (k + 2) from by ring, show 2 * k + 1 + 2 = 2 * (k + 1) + 1 from by ring, show 2 * k + 1 + 1 = 2 * (k + 1) from by ring]
    exact h

end OMA.S_oeis_a145920

open OMA.S_oeis_a145920 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a145920.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 10 := ⟨n - 10, by omega⟩
    exact rec_shift j
  · have el : ∀ S : PowerSeries ℚ, S * ((1 + X) ^ 4 * (1 - X) ^ 5) =
        C 1 * (S * X ^ 0) + C (-1) * (S * X ^ 1) + C (-4) * (S * X ^ 2) + C 4 * (S * X ^ 3) +
          C 6 * (S * X ^ 4) + C (-6) * (S * X ^ 5) + C (-4) * (S * X ^ 6) + C 4 * (S * X ^ 7) +
          C 1 * (S * X ^ 8) + C (-1) * (S * X ^ 9) := by
      intro S
      simp only [map_neg, map_one, map_ofNat]
      ring
    have er : (X ^ 2 * (1 + 4 * X + 26 * X ^ 2 + 19 * X ^ 3 + 26 * X ^ 4 + 4 * X ^ 5 + X ^ 6) :
        PowerSeries ℚ) = X ^ 2 * C 1 + X ^ 3 * C 4 + X ^ 4 * C 26 + X ^ 5 * C 19 + X ^ 6 * C 26 +
          X ^ 7 * C 4 + X ^ 8 * C 1 := by
      simp only [map_one, map_ofNat]
      ring
    rw [el, er]
    ext n
    simp only [map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, coeff_mk]
    by_cases hn : n < 10
    · interval_cases n <;> norm_num [a, x]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 10 := ⟨n - 10, by omega⟩
      have h := rec_shift j
      simp
      linarith

import OMAStatements.S_oeis_a230089
import Mathlib

/-!
Credit: @ivillar (original proof); shortened by Left to Solve (Grok Bot)
Proof: (-1)^n, i^n and (-i)^n depend only on n mod 4, and the closed form is checked for each
residue. For the g.f., the denominator is (1-x^2)(1-x^4) = 1 - x^2 - x^4 + x^6; the first seven
coefficients are checked directly, and for n ≥ 7 the coefficient identity
a(n) - a(n-2) - a(n-4) + a(n-6) = 0 follows by a case split on divisibility.
-/

namespace OMAA230089Helpers
open PowerSeries OMA.S_oeis_a230089 Complex

theorem closed (n : ℕ) (_hn : 1 ≤ n) : ((a n : ℤ) : ℂ) =
    (3 + 3 * (-1) ^ n + (-I) ^ n + I ^ n + n - (-1) ^ n * n) / 2 := by
  have h4 : I ^ 4 = 1 := by norm_num
  have e : ∀ z : ℂ, z ^ 4 = 1 → z ^ n = z ^ (n % 4) := fun z hz => by
    conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul, hz, one_pow, one_mul]
  rw [e (-1) (by norm_num), e (-I) (by rw [neg_pow, h4]; norm_num), e I h4]
  have : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h2 : n % 2 = n % 4 % 2 := by omega
  interval_cases h : n % 4 <;> simp [a, Nat.dvd_iff_mod_eq_zero, h, h2] <;> (ring_nf; try simp)

def c (n : ℕ) : ℤ := if n = 0 then 0 else a n

theorem cX (n k : ℕ) :
    coeff n (PowerSeries.mk c * X ^ k) = if k ≤ n then c (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

end OMAA230089Helpers

open PowerSeries OMA.S_oeis_a230089 OMAA230089Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a230089.main := by
  refine ⟨closed, ?_⟩
  change PowerSeries.mk c * _ = _
  ext n
  have hD : ((X - 1) ^ 2 * (X + 1) ^ 2 * (X ^ 2 + 1) : PowerSeries ℤ) =
      X ^ 6 - X ^ 4 - X ^ 2 + X ^ 0 := by ring
  have hN : (-X * (4 * X ^ 5 - X ^ 4 - 2 * X ^ 3 - 2 * X ^ 2 - 2 * X - 1) : PowerSeries ℤ) =
      X ^ 5 + C 2 * X ^ 4 + C 2 * X ^ 3 + C 2 * X ^ 2 + X ^ 1 - C 4 * X ^ 6 := by
    rw [map_ofNat C 2, map_ofNat C 4]; ring
  rw [hD, hN]
  simp only [mul_add, mul_sub, map_add, map_sub, cX, coeff_C_mul, coeff_X_pow]
  rcases Nat.lt_or_ge n 7 with h | h
  · interval_cases n <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    simp (disch := omega) only [if_pos, if_neg, c, a, Nat.sub_zero, show m + 7 - 6 = m + 1 by omega,
      show m + 7 - 4 = m + 3 by omega, show m + 7 - 2 = m + 5 by omega]
    split_ifs <;> omega

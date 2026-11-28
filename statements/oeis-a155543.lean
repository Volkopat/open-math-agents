import Mathlib

/-!
# A155543: a(n) = 2*A081294(n).

Source: https://oeis.org/A155543
Credit: @jagong-cmu

The entry states the conjecture
Conjecture: a(n) = A090129(2*n+2).

Definitions, as in the OEIS entries:
* A081294 is the expansion of `(1-2*x)/(1-4*x)` (offset 0). Here `A081294 n` is the
  coefficient of `x^n` of that series in `ℚ[[x]]`. The inverse `(1 - 4*X)⁻¹` is the power
  series inverse over `ℚ`; it exists, because the constant coefficient is `1`.
* A155543 is `a(n) = 2*A081294(n)` (offset 0, data 2, 4, 16, 64, ...).
* A090129 is the smallest exponent `k` such that `-1 + 3^k` is divisible by `2^m`. The exponent
  is positive (`k = 0` gives `0`, divisible by every `2^m`; the data start `1, 2, 2, 4`).
  Here `A090129 m = sInf {k | 0 < k ∧ 2^m ∣ 3^k - 1}`. The truncated subtraction `3^k - 1` on
  `ℕ` is the usual one, since `3^k ≥ 1`.

The conjecture is stated for every `n ≥ 0`, as an equality in `ℚ`.
-/

namespace OMA.S_oeis_a155543

open PowerSeries

/-- A081294: the coefficients of `(1-2*x)/(1-4*x)`. -/
noncomputable def A081294 (n : ℕ) : ℚ :=
  coeff n ((1 - 2 * X : PowerSeries ℚ) * (1 - 4 * X)⁻¹)

/-- A155543: `a(n) = 2*A081294(n)`. -/
noncomputable def a (n : ℕ) : ℚ := 2 * A081294 n

/-- A090129: the smallest positive exponent `k` with `2^m ∣ 3^k - 1`. -/
noncomputable def A090129 (m : ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ 2 ^ m ∣ 3 ^ k - 1}

/-- For every `n ≥ 0`, `a(n) = A090129(2*n+2)`. -/
theorem main : ∀ n : ℕ, a n = (A090129 (2 * n + 2) : ℚ) := by
  sorry

end OMA.S_oeis_a155543

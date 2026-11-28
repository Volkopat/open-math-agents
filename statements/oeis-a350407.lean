import Mathlib

/-!
# OEIS A350407: `a(n) = [x^n] 1/(1 + x + x² + x³ + x⁴)^n`

Source: https://oeis.org/A350407
Credit: @goncalomsdias (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the coefficient of `x^n` in the power series `1/(1 + x + x² + x³ + x⁴)^n`, offset 0
(`1, -1, 1, -1, 1, 4, -35, 146, -447, 1133, …`).

The entry (Peter Bala, Apr 16 2023): "Conjecture: the supercongruence
a(n*p^r) == a(n*p^(r-1)) (mod p^(2*r)) holds for positive integers n and r and all primes p >= 3."
This file states that conjecture exactly as written.

Note for reviewers and provers: as written, the conjecture is false for `p = 5`. The data of the
entry gives `a(1) = -1` and `a(5) = 4`, so for `n = r = 1`, `p = 5` the difference
`a(5) - a(1) = 5` is not divisible by `5² = 25`. (Both values were recomputed here in two independent
ways.) An exact computation found no failure for `p ∈ {3, 7, 11, 13}`, `1 ≤ r ≤ 3`,
`n * p^r ≤ 300`. The statement is kept faithful to the source; it is expected to be settled by a
disproof (`OMA.disproof`).

Conventions:
* `1 + x + x² + x³ + x⁴` has constant term `1`, so it is a unit of `PowerSeries ℤ`; its inverse is
  Mathlib's `PowerSeries.invOfUnit _ 1`, and `a(n)` is an integer.
* The congruence is `Int.ModEq` modulo `p^(2r)`, for every `n ≥ 1`, `r ≥ 1` and prime `p ≥ 3`.
-/

namespace OMA.S_oeis_a350407

open PowerSeries

/-- `1 / (1 + x + x² + x³ + x⁴)` in `PowerSeries ℤ`. -/
noncomputable def g : PowerSeries ℤ :=
  invOfUnit (1 + X + X ^ 2 + X ^ 3 + X ^ 4) 1

/-- `A350407(n) = [x^n] 1/(1 + x + x² + x³ + x⁴)^n`. -/
noncomputable def a (n : ℕ) : ℤ :=
  coeff n (g ^ n)

/-- Conjecture (Bala): `a(n p^r) ≡ a(n p^(r-1)) (mod p^(2r))` for `n, r ≥ 1` and primes `p ≥ 3`. -/
theorem main :
    ∀ n r p : ℕ, 1 ≤ n → 1 ≤ r → p.Prime → 3 ≤ p →
      a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [ZMOD (p : ℤ) ^ (2 * r)] := by
  sorry

end OMA.S_oeis_a350407

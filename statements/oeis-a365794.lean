import Mathlib

/-!
# OEIS A365794: Expansion of e.g.f. 1 / (3 - 2 * exp(2*x))^(3/4)

Source: https://oeis.org/A365794
Conjecture: Peter Bala, Oct 23 2025.
Credit: @yooeonwoo

Entry A365794 (offset 0): Expansion of e.g.f. `1 / (3 - 2 * exp(2*x))^(3/4)`,
starting 1, 3, 27, 369, 6849, 160803, 4566987, ...

Conjecture (Peter Bala, Oct 23 2025):
The sequence `a(n)` taken modulo a positive integer `k` is eventually periodic with
the period dividing `phi(k)` (`Nat.totient k`).

Modeling notes:
* `exp2` is the formal exponential power series `exp(2*x) = sum_{n >= 0} (2^n / n!) x^n`
  in `PowerSeries ℚ`.
* The e.g.f. `A(x) = 1 / (3 - 2 * exp(2*x))^(3/4)` with `A(0) = 1` is uniquely
  characterized in `PowerSeries ℚ` by `constantCoeff A = 1` and
  `A ^ 4 * (3 - 2 * exp2) ^ 3 = 1`.
* `a : ℕ → ℤ` is the sequence of e.g.f. coefficients: `coeff n A = (a n : ℚ) / n!`.
* Eventual periodicity of `a(n) mod k` with period dividing `phi(k)` is stated as:
  there exist `N` and `p > 0` dividing `Nat.totient k` such that
  `a (n + p) ≡ a n [ZMOD k]` for all `n ≥ N`.
-/

namespace OMA.S_oeis_a365794

open PowerSeries

/-- Formal power series `exp(2*x) = sum_{n >= 0} (2^n / n!) * x^n` over `ℚ`. -/
noncomputable def exp2 : PowerSeries ℚ :=
  PowerSeries.mk fun n => (2 : ℚ) ^ n / (n.factorial : ℚ)

/-- Peter Bala's conjecture (Oct 23 2025) for OEIS A365794:
for every positive integer `k`, the sequence `a(n)` modulo `k` is eventually periodic
with period dividing `phi(k)`. -/
theorem main :
    ∀ (A : PowerSeries ℚ) (a : ℕ → ℤ),
      PowerSeries.constantCoeff A = 1 →
      A ^ 4 * (3 - 2 * exp2) ^ 3 = 1 →
      (∀ n : ℕ, PowerSeries.coeff n A = (a n : ℚ) / (n.factorial : ℚ)) →
      ∀ k : ℕ, 0 < k →
        ∃ N p : ℕ, 0 < p ∧ p ∣ Nat.totient k ∧
          ∀ n : ℕ, N ≤ n → a (n + p) ≡ a n [ZMOD (k : ℤ)] := by
  sorry

end OMA.S_oeis_a365794

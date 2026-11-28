import Mathlib

/-!
# OEIS A002190: a Catalan-type generating function identity

Source: https://oeis.org/A002190
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`∑_{n ≥ 0} a(n) xⁿ/n!² = -log J₀(2√x)`. Conjecture (OEIS entry):
`1 = ∑_{n ≥ 0} a(n+1) C_n xⁿ ∑_{k ≥ 0} C(2n+k, k)² (-x)^k` as formal power series, where `C_n` is
the `n`-th Catalan number.

Conventions:
* `J₀(2√x) = f(x) = ∑_{n ≥ 0} (-1)ⁿ xⁿ/n!²` in `ℚ⟦x⟧`; `g = -log f` is the series with `g(0) = 0`
  and `g' = -f'/f` (`f` has constant term `1`). Then `a(n) = n!² · [xⁿ] g`.
* The identity is stated coefficientwise: for every `m`, the coefficient of `x^m` on the right is
  `∑_{n + k = m} a(n+1) C_n C(2n+k, k)² (-1)^k`, which must be `1` for `m = 0` and `0` otherwise.
-/

namespace OMA.S_oeis_a002190

open PowerSeries

/-- `f(x) = J₀(2√x)`. -/
noncomputable def f : PowerSeries ℚ := PowerSeries.mk fun n => (-1) ^ n / (n.factorial : ℚ) ^ 2

/-- The formal derivative `f'`. -/
noncomputable def fd : PowerSeries ℚ := PowerSeries.mk fun n => (n + 1) * coeff (n + 1) f

/-- `g' = -f'/f`. -/
noncomputable def gd : PowerSeries ℚ := -fd * invOfUnit f 1

/-- `a(n) = n!² [xⁿ] (-log f)`, with `[xⁿ] g = [x^(n-1)] g' / n` for `n ≥ 1` and `g(0) = 0`. -/
noncomputable def a (n : ℕ) : ℚ :=
  if n = 0 then 0 else (n.factorial : ℚ) ^ 2 * (coeff (n - 1) gd / n)

/-- The conjectured identity, coefficientwise. -/
theorem main : ∀ m : ℕ,
    ∑ n ∈ Finset.range (m + 1), a (n + 1) * (catalan n : ℚ) *
      ((((2 * n + (m - n)).choose (m - n) : ℕ) : ℚ) ^ 2 * (-1) ^ (m - n)) =
    if m = 0 then 1 else 0 := by
  sorry

end OMA.S_oeis_a002190

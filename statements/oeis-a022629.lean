import Mathlib

/-!
# A022629: Expansion of Product_{m>=1} (1 + m * q^m)

Source: https://oeis.org/A022629
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
Let `a(n)` be the coefficient of `q^n` in `∏_{m ≥ 1} (1 + m * q^m)`.
Then `log(a(n)) ~ sqrt(n / 2) * (log(2 * n) - 2)` as `n → ∞`.

Conventions:
- Since factors with `m > n` do not contribute to the coefficient of `q^n`,
  `a(n)` is defined as the `n`-th coefficient of `∏_{m=1..n} (1 + m * X^m)`.
- Asymptotic equivalence `f(n) ~ g(n)` is stated as `f(n) / g(n) → 1` as `n → ∞`.
-/

namespace OMA.S_oeis_a022629

noncomputable def aSeq (n : ℕ) : ℕ :=
  (∏ m ∈ Finset.Icc 1 n, (1 + Polynomial.C m * Polynomial.X ^ m : Polynomial ℕ)).coeff n

theorem main :
    Filter.Tendsto
      (fun n : ℕ =>
        Real.log (aSeq n : ℝ) /
          (Real.sqrt ((n : ℝ) / 2) * (Real.log (2 * (n : ℝ)) - 2)))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a022629

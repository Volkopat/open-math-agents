import Mathlib

/-!
# Inequalities concerning cumulative distributions of binomials

Source: https://mathoverflow.net/questions/479805
Credit: @koolkao

Question (Marcos Kiwi, MathOverflow 479805, 2024; CC BY-SA 4.0). For random variable `Z`, let
`F_Z` denote its cdf, i.e., `F_Z(t) = ℙ(Z ≤ t)`. Let `X` be a binomial distribution with parameters
`(n,p)` and `Y` a binomial distribution with parameters `(m,p)`. Let `n,m` be non-negative integers
such that `n > m`. Does the following inequality hold for all `k ∈ {1,...,m-1}`:
`1/(m-k) · (F_Y(k)+F_Y(k+1))/(F_Y(k-1)+F_Y(k)) ≥ 1/(n-k) · (F_X(k)+F_X(k+1))/(F_X(k-1)+F_X(k))`?
I have checked numerically and it seems to hold. References to similarly looking inequalities would
also be appreciated. […]

`main` states that the inequality holds for every `p ∈ (0, 1)`; a disproof is a counterexample.

Translation choices:
* the cdf of a binomial `(n, p)` variable is only needed at the integers `t = k-1, k, k+1 ≥ 0`, where
  `F(t) = ∑_{i ≤ t} C(n,i) p^i (1-p)^(n-i)` (`cdf n p t`; for `t ≥ n` the extra terms vanish since
  `C(n,i) = 0` for `i > n`, so `cdf n p t = 1` there, as it should);
* `p` ranges over the open interval `(0, 1)`. At `p = 1` the denominators `F(k-1) + F(k)` vanish, so
  the source's expressions are undefined there; at `p = 0` every `F` equals `1` and the inequality
  reads `1/(m-k) ≥ 1/(n-k)`, which is immediate. Excluding the endpoints avoids Lean's `x / 0 = 0`
  convention;
* `n, m, k` are natural numbers with `m < n` and `1 ≤ k ≤ m - 1`; the differences `m - k` and
  `n - k` are taken in `ℝ` (both are positive in this range);
* the inequality is written as in the source, with `1/(m-k) · A / B` read as `(1/(m-k) · A) / B`,
  which is the same number as `1/(m-k) · (A / B)`;
* not stated: the request for references, and the one-term inequality that the source says it can
  prove.

Status: MathOverflow 479805 had no answers or comments in November 2026.
-/

namespace OMA.S_mo_479805

/-- The cdf of a binomial `(n, p)` random variable at the integer `t`:
`ℙ(X ≤ t) = ∑_{i ≤ t} C(n,i) p^i (1-p)^(n-i)`. -/
noncomputable def cdf (n : ℕ) (p : ℝ) (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (t + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)

/-- The inequality of MathOverflow 479805, for `0 < p < 1`, `m < n` and `1 ≤ k ≤ m - 1`. -/
theorem main :
    ∀ (p : ℝ), 0 < p → p < 1 → ∀ (n m : ℕ), m < n → ∀ k : ℕ, 1 ≤ k → k ≤ m - 1 →
      1 / ((n : ℝ) - k) * (cdf n p k + cdf n p (k + 1)) / (cdf n p (k - 1) + cdf n p k) ≤
        1 / ((m : ℝ) - k) * (cdf m p k + cdf m p (k + 1)) / (cdf m p (k - 1) + cdf m p k) := by
  sorry

end OMA.S_mo_479805

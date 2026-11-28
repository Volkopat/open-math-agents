import Mathlib

/-!
# Is a log-concave polynomial a log-concave function?

Source: https://mathoverflow.net/questions/229028
Credit: @koolkao

Question (Johnny Yin, MathOverflow 229028, 2016; CC BY-SA 3.0). A polynomial `∑_{k=0}^n a_k x^k`
is log-concave if `a_0, …, a_n` constitute a log-concave sequence. I wonder whether the log-concave
polynomial is also a log-concave function with respect to `x` if `a_k ≥ 0` for all `k` and
`x ≥ 0`.

`main` states that the answer is yes. A disproof is a polynomial with nonnegative log-concave
coefficient sequence that is not a log-concave function on `[0, ∞)`.

Translation choices:
* the polynomial is `p : Polynomial ℝ` with coefficients `a_k = p.coeff k`, all `≥ 0`;
* the sequence `a_0, …, a_n` is log-concave when `a_{k-1} a_{k+1} ≤ a_k^2` for `1 ≤ k ≤ n - 1`;
  it is stated for all `k ≥ 1`, which is equivalent because `a_k = 0` for `k > n`;
* a nonnegative function `f` is log-concave on `[0, ∞)` when
  `f(x)^(1-t) f(y)^t ≤ f((1-t)x + ty)` for all `x, y ≥ 0` and `t ∈ [0, 1]` (real powers
  `Real.rpow`); this is the usual definition, equivalent to concavity of `log f` where `f > 0`,
  and it avoids `log 0`.
-/

namespace OMA.S_mo_229028

open Polynomial

/-- A polynomial with nonnegative log-concave coefficients is a log-concave function on
`[0, ∞)`. -/
theorem main :
    ∀ p : ℝ[X], (∀ k, 0 ≤ p.coeff k) →
      (∀ k, 1 ≤ k → p.coeff (k - 1) * p.coeff (k + 1) ≤ p.coeff k ^ 2) →
      ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        p.eval x ^ (1 - t) * p.eval y ^ t ≤ p.eval ((1 - t) * x + t * y) := by
  sorry

end OMA.S_mo_229028

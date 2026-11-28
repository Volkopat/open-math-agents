import Mathlib

/-!
# A081923: Mathar's recurrence for the expansion of `exp(2x)/(1-x)^2`

Source: https://oeis.org/A081923
Credit: @sntntHb

`a(n)` is defined by the exponential generating function `exp(2x)/(1-x)^2`, with data
`1, 4, 18, 92, 536, 3552, 26608, ...` from `n = 0`. The entry records a conjecture of R. J. Mathar
(Nov 24 2012): `a(n) + (-n-3)*a(n-1) + 2*(n-1)*a(n-2) = 0`.

Since `exp(2x) = ∑ 2^j x^j / j!` and `1/(1-x)^2 = ∑ (k+1) x^k = ∑ (k+1)! x^k / k!`, the product of the
two exponential generating functions gives the binomial convolution
`a(n) = ∑_{k=0}^{n} C(n,k) * 2^(n-k) * (k+1)!`, which is the definition used here (it reproduces the
listed data).

`main` states the conjectured recurrence for all `n ≥ 2`, with the negative term moved to the other
side so that it reads in `ℕ`: `a(n) + 2(n-1) a(n-2) = (n+3) a(n-1)`.
-/

namespace OMA.S_oeis_a081923

/-- `a n = n! [x^n] exp(2x)/(1-x)^2` (OEIS A081923). -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k * 2 ^ (n - k) * (k + 1).factorial

/-- Mathar's conjectured recurrence for OEIS A081923. -/
theorem main : ∀ n : ℕ, 2 ≤ n → a n + 2 * (n - 1) * a (n - 2) = (n + 3) * a (n - 1) := by
  sorry

end OMA.S_oeis_a081923

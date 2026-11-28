import Mathlib

/-!
# OEIS A014963: `exp(Λ(n))` from the array A191898

Source: https://oeis.org/A014963
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = exp(Λ(n))`: `p` if `n` is a power of the prime `p`, else `1`. Conjecture (OEIS entry):
`a(n) = exp(∑_{k ≥ 1} T(n, k)/k)` for `n > 1`, where `T` is the symmetric array A191898:
`T(n, 1) = T(1, k) = 1`, `T(n, k) = -∑_{i=1}^{k-1} T(n-i, k)` for `n ≥ k`, and
`T(n, k) = -∑_{i=1}^{n-1} T(k-i, n)` for `n < k`.

Conventions:
* Indices start at `1`; `T` is `0` if an index is `0`. The infinite series is read as the limit
  of its partial sums `∑_{k=1}^{K} T(n, k)/k` (`K → ∞`); `main` states that this limit is
  `Λ(n) = log a(n)` for every `n > 1`, which is the conjecture after taking logarithms.
-/

namespace OMA.S_oeis_a014963

open Filter Topology

/-- The array A191898. -/
def T (n k : ℕ) : ℤ :=
  if h0 : n = 0 ∨ k = 0 then 0
  else if h1 : k = 1 ∨ n = 1 then 1
  else if hk : k ≤ n then -∑ i : Fin k, (if h : (i : ℕ) = 0 then 0 else T (n - i) k)
  else -∑ i : Fin n, (if h : (i : ℕ) = 0 then 0 else T (k - i) n)
termination_by n + k
decreasing_by all_goals (have := i.isLt; omega)

/-- `∑_{k ≥ 1} T(n, k)/k = Λ(n)` for `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n →
    Tendsto (fun K : ℕ => ∑ k ∈ Finset.Icc 1 K, (T n k : ℝ) / k) atTop
      (𝓝 (ArithmeticFunction.vonMangoldt n)) := by
  sorry

end OMA.S_oeis_a014963

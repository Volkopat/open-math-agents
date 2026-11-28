import Mathlib

/-!
# A191904: Square array read by antidiagonals up: T(n,k) = 1-k if k divides n, else 1

Source: https://oeis.org/A191904
Credit: @ivillar

Mats Granvik's array (n, k ≥ 1): T(n,k) = 1-k if k divides n, and T(n,k) = 1 otherwise.

Conjecture (in the formula section of A191904): Sum_{n>=1} T(n,k)/n = log(k).
The series converges only conditionally (its terms are not absolutely summable), so the sum is
read in the natural order n = 1, 2, 3, ...: the partial sums Sum_{n=1..N} T(n,k)/n tend to
log(k) as N → ∞, for every column k ≥ 1.
-/

namespace OMA.S_oeis_a191904

open Filter Topology

/-- T(n,k) = 1-k if k divides n, else 1 (n, k ≥ 1). -/
def T (n k : ℕ) : ℤ := if k ∣ n then 1 - k else 1

/-- Granvik's conjecture: for every k ≥ 1 the partial sums Sum_{n=1..N} T(n,k)/n tend to log(k). -/
theorem main : ∀ k : ℕ, 1 ≤ k →
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (T n k : ℝ) / n) atTop (𝓝 (Real.log k)) := by
  sorry

end OMA.S_oeis_a191904

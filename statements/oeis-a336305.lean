import Mathlib

/-!
# A336305: alternating row sums of A211343
Source: https://oeis.org/A336305 (conjecture in the entry of Omar E. Pol, Oct 05 2020)

A211343 is the irregular triangle T(n,k), n >= 1, 1 <= k <= A003056(n), in which column k lists
the positive integers interleaved with k-1 zeros, the first element of column k being in row
k(k+1)/2. Thus T(n,k) = j when n = k(k+1)/2 + (j-1)k for some j >= 1, and T(n,k) = 0 otherwise.
Row n has the A003056(n) entries with k(k+1)/2 <= n; the remaining k <= n give T(n,k) = 0 by
the same formula, so the row sum may be taken over 1 <= k <= n.

a(n) (offset 1) = Sum_k (-1)^(k-1) * T(n,k).

Conjecture: a(n) = (A000203(n) + A067742(n))/2, stated as 2 a(n) = sigma(n) + A067742(n), where
A067742(n) is the number of divisors d of n in the half-open interval [sqrt(n/2), sqrt(2n)),
i.e. with n <= 2 d^2 and d^2 < 2n.
-/

namespace OMA.S_oeis_a336305

/-- A211343(n,k). -/
def T (n k : ℕ) : ℕ :=
  if k * (k + 1) / 2 ≤ n ∧ k ∣ n - k * (k + 1) / 2 then (n - k * (k + 1) / 2) / k + 1 else 0

/-- A336305. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, (-1) ^ (k - 1) * (T n k : ℤ)

/-- A067742: number of middle divisors. -/
def A067742 (n : ℕ) : ℕ := (n.divisors.filter fun d => n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n).card

theorem main : ∀ n : ℕ, 1 ≤ n →
    2 * a n = (ArithmeticFunction.sigma 1 n : ℤ) + (A067742 n : ℤ) := by
  sorry

end OMA.S_oeis_a336305

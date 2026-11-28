import Mathlib

/-!
# A342591: Numbers k such that A340740(k) <= k

Source: https://oeis.org/A342591

Conjecture (OEIS A342591):
Let `A340740(k) = ∑_{1 ≤ j ≤ ⌊k / 2⌋, gcd(j, k) = 1} (k mod j)`.
Then `78` is the largest integer `k` satisfying `A340740(k) ≤ k` (the `38` terms
`1, 2, ..., 22, 24, 25, 26, 28, 30, 32, 33, 34, 36, 40, 42, 46, 48, 54, 60, 78`
are conjectured to be all the terms).

Conventions:
- For every `k > 78`, `A340740(k) > k`.
-/

namespace OMA.S_oeis_a342591

/-- `A340740(k) = ∑_{1 ≤ j ≤ k / 2, gcd(j, k) = 1} (k % j)`. -/
def a340740 (k : ℕ) : ℕ :=
  ∑ j ∈ (Finset.Icc 1 (k / 2)).filter (fun j => Nat.Coprime j k), k % j

/-- Conjecture: `78` is the last term of A342591, i.e., `A340740(k) > k` for all `k > 78`. -/
theorem main :
    ∀ k : ℕ, 78 < k → k < a340740 k := by
  sorry

end OMA.S_oeis_a342591

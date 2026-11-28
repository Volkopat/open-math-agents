import Mathlib

/-!
# A077510: Numbers k such that k + pi(k) is a prime.

Source: https://oeis.org/A077510
Credit: @divmxnd0x

Conjecture (stated in A077510): for `k > 5`, `prime(n) ≤ k < prime(n+1) ≤ k + pi(k)`, i.e. the
smallest prime greater than `k` is at most `k + pi(k)` (equality holds for `k = 7`).

Formalization notes:
* Stated as: for every `k > 5` there is a prime `q` with `k < q ≤ k + π(k)` (`Nat.primeCounting`);
  this is equivalent to the smallest prime greater than `k` being at most `k + π(k)`.
-/

namespace OMA.S_oeis_a077510

/-- For `k > 5` there is a prime in `(k, k + π(k)]`. -/
theorem main : ∀ k : ℕ, 5 < k → ∃ q : ℕ, q.Prime ∧ k < q ∧ q ≤ k + Nat.primeCounting k := by
  sorry

end OMA.S_oeis_a077510

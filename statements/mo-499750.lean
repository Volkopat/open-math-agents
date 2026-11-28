import Mathlib

/-!
# An odd prime p for which the last two base-p digits of k sum to at least p

Source: https://mathoverflow.net/questions/499750 (Max Alekseyev, CC BY-SA 4.0).

Conjecture: for every integer `k > 78` there exists an odd prime `p` such that the sum of the last
two base-`p` digits of `k` is `≥ p`. The last base-`p` digit of `k` is `k % p` and the one before
it is `(k / p) % p` (a missing digit is `0`). The bound is sharp: `k = 78` has no such prime.
-/

namespace OMA.S_mo_499750

theorem main : ∀ k : ℕ, 78 < k → ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≤ k % p + k / p % p := by
  sorry

end OMA.S_mo_499750

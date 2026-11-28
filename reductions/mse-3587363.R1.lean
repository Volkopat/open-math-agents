import OMAStatements.S_mse_3587363
import Mathlib

-- Reduction mse-3587363.R1 of If n! + k is a perfect power with k > 3, must n ≤ k?
-- Credit: @marcusbuffett

/-!
# A simple prime factor of `k` below `n / 2` excludes `n! + k = a^b`

Classical valuation argument (as for Brocard-type equations): if a prime `p` divides `k` exactly
once and `2p ≤ n`, then `p² ∣ n!` (both `p` and `2p` occur in the product), so `n! + k` is
divisible by `p` but not by `p²`; a perfect power `a^b`, `b ≥ 2`, divisible by `p` is divisible
by `p²`. So `n! + k` is not a perfect power.

* `H1` (proved in the step): that argument, for all `n, k, a, b, p`.
* `H2` (open core): a counterexample with `n > k` would need every prime `p` dividing `k`
  exactly once to satisfy `n < 2p`. Since `p ≤ k < n`, such a `p` exceeds `k / 2`, so `k = p`.
  Hence `H2` only concerns powerful `k` (every prime exponent at least 2) and prime `k` with
  `k < n < 2k`.

This is the elementary part of the problem, not progress on the powerful or prime cases.
-/

namespace OMA.R_mse_3587363_R1

/-- A prime dividing `k` exactly once with `2p ≤ n` makes `n! + k` a non-power. -/
def H1 : Prop :=
  ∀ n k a b p : ℕ, 2 ≤ b → n.factorial + k = a ^ b → p.Prime → p ∣ k → ¬ p ^ 2 ∣ k →
    2 * p ≤ n → False

/-- The open core: no counterexample `n > k > 3` all of whose simple prime factors `p` of `k`
satisfy `n < 2p` (that is, `k` powerful, or `k` prime with `k < n < 2k`). -/
def H2 : Prop :=
  ∀ n k a b : ℕ, 3 < k → 2 ≤ b → n.factorial + k = a ^ b → k < n →
    (∀ p : ℕ, p.Prime → p ∣ k → ¬ p ^ 2 ∣ k → n < 2 * p) → False

theorem main : H1 → H2 → type_of% @OMA.S_mse_3587363.main := by
  intro h1 h2 n k a b hk hb h
  by_contra hnk
  refine h2 n k a b hk hb h (by omega) ?_
  intro p hp hpk hp2
  by_contra hlt
  exact h1 n k a b p hb h hp hpk hp2 (by omega)

end OMA.R_mse_3587363_R1

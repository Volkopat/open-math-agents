import Mathlib

/-!
# OEIS A073918: primes one more than a product of k distinct primes

Source: https://oeis.org/A073918
`a(k)` is the smallest prime `p` such that `p - 1` is a product of `k` distinct primes.
Conjecture: for any `m > 0` there is `K` such that for all `k > K`, `a(k) - 1` is divisible by
the first `m` primes.

Conventions. "`p - 1` is a product of `k` distinct primes" means `p - 1` is squarefree with
exactly `k` prime factors. The product of the first `m` primes is `primorial (p_m)` with
`p_m = Nat.nth Nat.Prime (m - 1)`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a073918

/-- A073918. -/
noncomputable def a (k : ℕ) : ℕ :=
  sInf {p | p.Prime ∧ Squarefree (p - 1) ∧ (p - 1).primeFactors.card = k}

theorem main :
    ∀ m : ℕ, 0 < m → ∃ K : ℕ, ∀ k > K,
      primorial (Nat.nth Nat.Prime (m - 1)) ∣ a k - 1 := by
  sorry

end OMA.S_oeis_a073918

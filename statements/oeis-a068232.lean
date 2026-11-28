import Mathlib

/-!
# OEIS A068232: runs of consecutive primes `≡ 1 (mod 12)`

Source: https://oeis.org/A068232
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest prime `p` such that `p` and the next `n - 1` primes are all `≡ 1 (mod 12)`.
The entry notes that Dickson's conjecture implies that `a(n)` exists for all `n`; `main` states
this existence.

Conventions:
* Primes are indexed by `Nat.nth Nat.Prime`; 'p and the next `n - 1` primes' are
  `nth Prime i, …, nth Prime (i + n - 1)` with `p = nth Prime i`. `n ≥ 1`.
-/

namespace OMA.S_oeis_a068232

/-- For every `n ≥ 1` some `n` consecutive primes are all `≡ 1 (mod 12)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ i : ℕ, ∀ j < n, Nat.nth Nat.Prime (i + j) % 12 = 1 := by
  sorry

end OMA.S_oeis_a068232

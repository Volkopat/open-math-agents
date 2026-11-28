import Mathlib

/-!
# A156642: Number of decompositions of 4n+2 into unordered sums of two primes of the form 4k+3.

Source: https://oeis.org/A156642
Credit: @keiichisince1986-bot

A156642 is the sequence `a(n)` named in the title. The entry states:
Conjecture. For n >= 1, a(n) > 0.

Conventions:
- `a(n) > 0` means that `4n + 2 = p + q` for some primes `p` and `q` with `p ≡ q ≡ 3 (mod 4)`.
  The order of `p` and `q` does not matter for existence.
-/

namespace OMA.S_oeis_a156642

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p % 4 = 3 ∧ q % 4 = 3 ∧ p + q = 4 * n + 2 := by
  sorry

end OMA.S_oeis_a156642

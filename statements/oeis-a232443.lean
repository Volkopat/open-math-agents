import Mathlib

/-!
# A232443: Number of ways to write n = p + q - pi(q), where p and q are odd primes, and pi(q) is the number of primes not exceeding q.

Source: https://oeis.org/A232443
Credit: @keiichisince1986-bot

A232443 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 3. [The entry continues with a stronger form (p + 6 also prime)
and parts (ii) and (iii); only the first claim of part (i), about a(n) itself, is formalized here.]

Conventions:
- `pi(q)` is `Nat.primeCounting q`. Since `pi(q) ≤ q`, the natural-number subtraction `q - pi(q)` is
  exact.
- `a(n) > 0` means that `n = p + q - pi(q)` for some odd primes `p` and `q`.
-/

namespace OMA.S_oeis_a232443

theorem main :
    ∀ n : ℕ, 3 < n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ 2 ∧ q ≠ 2 ∧ n = p + (q - Nat.primeCounting q) := by
  sorry

end OMA.S_oeis_a232443

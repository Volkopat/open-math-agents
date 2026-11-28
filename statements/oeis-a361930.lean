import Mathlib

/-!
# A361930: a(n) is the greatest prime p such that p + q^2 + r^3 = prime(n)^4 for some primes q and r.

Source: https://oeis.org/A361930
Credit: @keiichisince1986-bot

A361930 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) exists for all n > 2.

Conventions:
- `n > 2` means `P = prime(n) ≥ 5`; we state the conjecture for every prime `P ≥ 5`. A greatest such `p`
  exists as soon as one exists (there are finitely many), so `a(n)` exists means that
  `p + q^2 + r^3 = P^4` for some primes `p, q, r`.
-/

namespace OMA.S_oeis_a361930

theorem main :
    ∀ P : ℕ, P.Prime → 5 ≤ P → ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q ^ 2 + r ^ 3 = P ^ 4 := by
  sorry

end OMA.S_oeis_a361930

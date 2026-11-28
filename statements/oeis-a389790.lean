import Mathlib

/-!
# A389790: Number of ways to write 2*n as p + p' + q + q', where p and q are primes with p <= q, and r' is the first prime greater than r.

Source: https://oeis.org/A389790
Credit: @keiichisince1986-bot

A389790 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n >= 474.

Conventions:
- `IsNextPrime r r'` says that `r'` is the first prime greater than `r`.
- `a(n) > 0` means that there are primes `p ≤ q` with `2n = p + p' + q + q'`.
-/

namespace OMA.S_oeis_a389790

/-- `r'` is the first prime greater than `r`. -/
def IsNextPrime (r r' : ℕ) : Prop :=
  r'.Prime ∧ r < r' ∧ ∀ s : ℕ, r < s → s < r' → ¬ s.Prime

theorem main :
    ∀ n : ℕ, 474 ≤ n → ∃ p q p' q' : ℕ, p.Prime ∧ q.Prime ∧ p ≤ q ∧ IsNextPrime p p' ∧
        IsNextPrime q q' ∧ 2 * n = p + p' + q + q' := by
  sorry

end OMA.S_oeis_a389790

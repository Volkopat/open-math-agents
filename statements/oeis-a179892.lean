import Mathlib

/-!
# A179892: Numbers not representable as the sum of three distinct twin primes

Source: https://oeis.org/A179892

Conjecture (OEIS A179892):
No odd integer `n ≥ 19` belongs to A179892; equivalently, every odd integer
`n ≥ 19` can be written as the sum of three distinct members of twin prime pairs.

Conventions:
- A prime `p` is a member of a twin prime pair (OEIS A001097) iff `p + 2` is prime
  or (`3 ≤ p` and `p - 2` is prime).
- Odd integers `< 19` not representable as a sum of three distinct twin primes are
  `1, 3, 5, 7, 9, 11, 13, 17` (`15 = 3 + 5 + 7`, `19 = 3 + 5 + 11`, ...).
-/

namespace OMA.S_oeis_a179892

/-- Predicate stating that `p` is a member of a twin prime pair (OEIS A001097). -/
def IsTwinPrimeMember (p : ℕ) : Prop :=
  Nat.Prime p ∧ (Nat.Prime (p + 2) ∨ (3 ≤ p ∧ Nat.Prime (p - 2)))

/-- Conjecture: every odd integer `n ≥ 19` is the sum of three distinct twin prime members. -/
theorem main :
    ∀ n : ℕ, 19 ≤ n → Odd n →
      ∃ p q r : ℕ,
        IsTwinPrimeMember p ∧ IsTwinPrimeMember q ∧ IsTwinPrimeMember r ∧
        p < q ∧ q < r ∧ p + q + r = n := by
  sorry

end OMA.S_oeis_a179892

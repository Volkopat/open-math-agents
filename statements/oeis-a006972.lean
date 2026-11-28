import Mathlib

/-!
# A006972: Lucas-Carmichael numbers: squarefree composite numbers k such that p | k => p+1 | k+1.

Source: https://oeis.org/A006972
Credit: @divmxnd0x

Conjecture (Davide Rotondo, Dec 23 2020, stated in A006972): if `k = p q r`, where
`p = a d - 1`, `q = b d - 1`, `r = c d - 1` are distinct odd primes, with
`d = gcd(p + 1, q + 1, r + 1)`, and `a b c d` divides `k + 1`, then `k` is a Lucas-Carmichael
number.

Formalization notes:
* A Lucas-Carmichael number is a squarefree composite `k` (`k > 1`, not prime) such that
  `p + 1 ∣ k + 1` for every prime `p ∣ k`, as in the name of A006972.
* `p = a d - 1` is written `p + 1 = a d` (and similarly for `q`, `r`) to avoid truncated
  subtraction.
-/

namespace OMA.S_oeis_a006972

/-- `k` is a Lucas-Carmichael number. -/
def IsLucasCarmichael (k : ℕ) : Prop :=
  Squarefree k ∧ 1 < k ∧ ¬ k.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ k → p + 1 ∣ k + 1

/-- Rotondo's construction always gives Lucas-Carmichael numbers. -/
theorem main : ∀ p q r a b c d : ℕ, p.Prime → q.Prime → r.Prime → Odd p → Odd q → Odd r →
    p ≠ q → p ≠ r → q ≠ r →
    p + 1 = a * d → q + 1 = b * d → r + 1 = c * d →
    d = Nat.gcd (Nat.gcd (p + 1) (q + 1)) (r + 1) →
    a * b * c * d ∣ p * q * r + 1 →
    IsLucasCarmichael (p * q * r) := by
  sorry

end OMA.S_oeis_a006972

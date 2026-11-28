import Mathlib

/-!
# A129813: lesser of consecutive prime pairs whose last digits differ by 8.

Source: https://oeis.org/A129813
Credit: @cjchaffin

Conjecture (on the OEIS page): the number of terms is infinite. Example: the last
digits of the consecutive primes 29 and 31 differ by 8, so 29 is a term.

Conventions: last digits are residues modulo 10; “differ by 8” means the natural
distance between those residues is 8. The infinitude statement does not depend on
the official offset.
-/

namespace OMA.S_oeis_a129813

def ConsecutivePrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r : ℕ, p < r → r < q → ¬ r.Prime

def LastDigitsDifferBy (d p q : ℕ) : Prop :=
  Int.natAbs ((p % 10 : ℤ) - (q % 10)) = d

theorem main : {p : ℕ | ∃ q : ℕ, ConsecutivePrimes p q ∧ LastDigitsDifferBy 8 p q}.Infinite := by
  sorry

end OMA.S_oeis_a129813

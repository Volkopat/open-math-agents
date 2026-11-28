import Mathlib

/-!
# A129809: lesser of consecutive prime pairs whose last digits differ by 2.

Source: https://oeis.org/A129809
Credit: @cjchaffin

Conjecture (on the OEIS page): the number of terms is infinite. Example: the last
digits of the consecutive primes 89 and 97 differ by 2, so 89 is a term.

Conventions: last digits are residues modulo 10; “differ by 2” means the natural
distance between those residues is 2.
-/

namespace OMA.S_oeis_a129809

def ConsecutivePrimes (p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ ∀ r : ℕ, p < r → r < q → ¬ r.Prime

def LastDigitsDifferBy (d p q : ℕ) : Prop :=
  Int.natAbs ((p % 10 : ℤ) - (q % 10)) = d

theorem main : {p : ℕ | ∃ q : ℕ, ConsecutivePrimes p q ∧ LastDigitsDifferBy 2 p q}.Infinite := by
  sorry

end OMA.S_oeis_a129809

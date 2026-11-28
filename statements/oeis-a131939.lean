import Mathlib

/-!
# A131939: Least k such that the difference between consecutive 3-almost primes A014612(k) equals n, or 0 if no such k exists.

Source: https://oeis.org/A131939
Credit: @divmxnd0x

Conjecture (stated in A131939): `a(n) > 0` for all `n`, i.e. every positive integer `n` occurs as
the difference between two consecutive 3-almost primes.

Formalization notes:
* A 3-almost prime is a number with exactly three prime factors counted with multiplicity
  (`(Nat.primeFactorsList m).length = 3`, A014612).
* `a(n) > 0` means that there are 3-almost primes `m < m + n` with no 3-almost prime strictly
  between them.
-/

namespace OMA.S_oeis_a131939

/-- `m` is a 3-almost prime. -/
def IsThreeAlmostPrime (m : ℕ) : Prop := (Nat.primeFactorsList m).length = 3

/-- Every `n ≥ 1` is the gap between two consecutive 3-almost primes. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, IsThreeAlmostPrime m ∧ IsThreeAlmostPrime (m + n) ∧
    ∀ j : ℕ, m < j → j < m + n → ¬ IsThreeAlmostPrime j := by
  sorry

end OMA.S_oeis_a131939

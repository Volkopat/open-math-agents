import Mathlib

/-!
# A216497: Primes p with property that there exists a number d>0 such that numbers p-k*d, k=1...4, are four primes.

Source: https://oeis.org/A216497
Credit: @darealpandaboi

Conjecture: only 653 primes are not in the sequence: 2, 3, ..., 100291.

Translation notes.
* S is the set of primes p for which no d > 0 makes p - d, p - 2d, p - 3d, p - 4d all prime.
  p - 4d must be prime, so p - 4d >= 2 and truncated subtraction never matters.
* The conjecture says S has exactly 653 elements and its largest is 100291.
* A computer check of all primes up to 3*10^6 finds exactly 653 primes outside the sequence,
  from 2, 3, 5, 7, 11 up to 100271, 100291, and reproduces the listed data.
-/

namespace OMA.S_oeis_a216497

/-- Primes p with no d > 0 such that p - k*d is prime for k = 1, 2, 3, 4. -/
def S : Set ℕ :=
  {p : ℕ | p.Prime ∧ ¬ ∃ d : ℕ, 0 < d ∧ 4 * d < p ∧
    (p - d).Prime ∧ (p - 2 * d).Prime ∧ (p - 3 * d).Prime ∧ (p - 4 * d).Prime}

theorem main : S.Finite ∧ S.ncard = 653 ∧ IsGreatest S 100291 := by
  sorry

end OMA.S_oeis_a216497

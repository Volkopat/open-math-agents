import Mathlib

/-!
# A216498: Primes p with property that there exists a number d>0 such that numbers p-k*d, k=1...5, are five primes.

Source: https://oeis.org/A216498
Credit: @darealpandaboi

Conjecture: only 9198 primes are not in the sequence: 2, 3, ..., 2521081.

Translation notes.
* S is the set of primes p for which no d > 0 makes p - d, p - 2d, p - 3d, p - 4d, p - 5d all
  prime. p - 5d must be prime, so p - 5d >= 2 and truncated subtraction never matters. This
  agrees with the PARI program in the entry and reproduces the listed data (checked by computer).
* The conjecture says S has exactly 9198 elements and its largest is 2521081; both are stated.
* Warning for provers: a computer check of all primes below 3*10^6 finds 9197 elements of S up to
  2521081 and one more, 2668453, which is prime and admits no such d (every d checked). So the
  statement appears to be false, and OMA.disproof may be the right target.
-/

namespace OMA.S_oeis_a216498

/-- Primes p with no d > 0 such that p - k*d is prime for k = 1, ..., 5. -/
def S : Set ℕ :=
  {p : ℕ | p.Prime ∧ ¬ ∃ d : ℕ, 0 < d ∧ 5 * d < p ∧ (p - d).Prime ∧ (p - 2 * d).Prime ∧
    (p - 3 * d).Prime ∧ (p - 4 * d).Prime ∧ (p - 5 * d).Prime}

theorem main : S.Finite ∧ S.ncard = 9198 ∧ IsGreatest S 2521081 := by
  sorry

end OMA.S_oeis_a216498

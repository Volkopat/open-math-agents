import Mathlib

/-!
# A205649: Hamming distance between twin primes.

Source: https://oeis.org/A205649
Credit: @prasledi

Conjecture (in the COMMENTS of A205649): the sequence is unbounded.

Formalization notes:
* The sequence runs over the twin prime pairs (p, p + 2), p = 3, 5, 11, 17, ... (A001359), and
  a(n) is the Hamming distance between the binary representations of p and p + 2, i.e. the
  number of 1 bits of p XOR (p + 2). The number of 1 bits of x is the sum of its binary digits,
  `(Nat.digits 2 x).sum`, and XOR is Mathlib's `Nat.xor` (written `^^^`).
* Unbounded means: for every bound B there is a twin prime pair whose Hamming distance
  exceeds B.
* The definition reproduces the OEIS data 2, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, ...
-/

namespace OMA.S_oeis_a205649

/-- The Hamming distance between the binary representations of `a` and `b`. -/
def hammingDist2 (a b : ℕ) : ℕ := (Nat.digits 2 (a ^^^ b)).sum

/-- The conjecture of A205649: the Hamming distance between twin primes is unbounded. -/
theorem main :
    ∀ B : ℕ, ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ B < hammingDist2 p (p + 2) := by
  sorry

end OMA.S_oeis_a205649

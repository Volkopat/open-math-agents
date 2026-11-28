import Mathlib

/-!
# A374365: Numbers m such that abs(Sum_{k=1..m} [k|m]*A008683(k)*(-1)^(2*k/5)) = 0.

Source: https://oeis.org/A374365
Credit: @agchua

Comment of A374365 (unsigned; the entry is by Mats Granvik, Jul 06 2024):
  Conjecture: Numbers having a prime factor congruent to 1 mod 10.
The sequence has offset 1, so the claim is stated for m ≥ 1. A008683 is the Moebius function
(ArithmeticFunction.moebius), [k|m] is 1 if k divides m and 0 otherwise, and (-1)^(2*k/5) is the
principal complex power, as in the entry's Mathematica program; Mathlib's complex power
(-1 : ℂ) ^ z is exp (log (-1) * z) with log (-1) = π * I, the same principal value.
S m is the sum, and InSeq m says that its absolute value is 0.
-/

namespace OMA.S_oeis_a374365

/-- Sum_{k=1..m} [k|m] * mu(k) * (-1)^(2*k/5), with the principal complex power. -/
noncomputable def S (m : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 m, (if k ∣ m then (1 : ℂ) else 0) *
    ((ArithmeticFunction.moebius k : ℤ) : ℂ) * (-1 : ℂ) ^ ((2 * (k : ℂ)) / 5)

/-- m is a term of A374365: the absolute value of S m is 0. -/
def InSeq (m : ℕ) : Prop := ‖S m‖ = 0

/-- The comment's conjecture: for m ≥ 1, m is a term iff m has a prime factor congruent to
1 mod 10. -/
theorem main : ∀ m : ℕ, 1 ≤ m → (InSeq m ↔ ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ p % 10 = 1) := by
  sorry

end OMA.S_oeis_a374365

import Mathlib

/-!
# A228541: Numbers having at least one prime factor of the form 30*k + 1.

Source: https://oeis.org/A228541
Credit: @agchua

Comment of A228541 (the entry is by Arkadiusz Wesolowski, Aug 25 2013), verbatim:
  Conjecture: Numbers m such that abs(Sum_{k=1..m} [k|m]*A008683(k)*(-1)^(k/15)) = 0.
  - Mats Granvik, Jul 06 2024
The sequence has offset 1, so the claim is stated for m ≥ 1: m is a term (m has a prime factor
p with p mod 30 = 1) if and only if the absolute value of the sum is 0. A008683 is the Moebius
function (ArithmeticFunction.moebius), [k|m] is 1 if k divides m and 0 otherwise, and
(-1)^(k/15) is the principal complex power; Mathlib's complex power (-1 : ℂ) ^ z is
exp (log (-1) * z) with log (-1) = π * I, the same principal value. S m is the sum, and
MZero m says that its absolute value is 0.
-/

namespace OMA.S_oeis_a228541

/-- Sum_{k=1..m} [k|m] * mu(k) * (-1)^(k/15), with the principal complex power. -/
noncomputable def S (m : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 m, (if k ∣ m then (1 : ℂ) else 0) *
    ((ArithmeticFunction.moebius k : ℤ) : ℂ) * (-1 : ℂ) ^ ((k : ℂ) / 15)

/-- The absolute value of S m is 0. -/
def MZero (m : ℕ) : Prop := ‖S m‖ = 0

/-- The comment's conjecture: for m ≥ 1, m has a prime factor congruent to 1 mod 30 if and only
if the absolute value of S m is 0. -/
theorem main : ∀ m : ℕ, 1 ≤ m → ((∃ p : ℕ, p.Prime ∧ p ∣ m ∧ p % 30 = 1) ↔ MZero m) := by
  sorry

end OMA.S_oeis_a228541

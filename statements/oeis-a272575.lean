import Mathlib

/-!
# A272575: Perfect powers that are the sum of two Fibonacci numbers.

Source: https://oeis.org/A272575
Credit: @azmiozgen

Conjecture (Charles R Greathouse IV, May 04 2016): there are no more terms in this sequence (beyond 1, 4, 8, 9, 16, 36, 144, 1000, 1600, 14930496).

Formalization notes:
* Perfect powers are m = a^b with b ≥ 2 and m ≥ 1 (A001597); Fibonacci numbers are `Nat.fib i`.
* Stated as equality of the set of terms with the ten listed values.
* Controls (computed): among F(i) + F(j) with i, j < 400 the positive perfect powers are exactly the
  listed values.
-/

namespace OMA.S_oeis_a272575

/-- `m` is a perfect power (A001597): `m = a^b` with `b ≥ 2` and `m ≥ 1`. -/
def IsPerfectPower (m : ℕ) : Prop := 0 < m ∧ ∃ a b : ℕ, 2 ≤ b ∧ a ^ b = m

/-- The conjecture of the entry. -/
theorem main :
    {m : ℕ | IsPerfectPower m ∧ ∃ i j : ℕ, Nat.fib i + Nat.fib j = m} =
      ({1, 4, 8, 9, 16, 36, 144, 1000, 1600, 14930496} : Set ℕ) := by
  sorry

end OMA.S_oeis_a272575

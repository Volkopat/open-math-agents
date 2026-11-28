import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Twin-prime midpoints with divisor-sum gcd three

Source: https://oeis.org/A394399
Credit: @anmolspace

Aied Sulaiman conjectured that every term of A394399 is twice a square. The entry also
identifies it conjecturally as the intersection of A014574 (twin-prime midpoints),
A392199 (positive integers with a prime divisor-sum gcd) and A001105 (twice a square).
The equivalence below states the intersection within the set of twin-prime midpoints.
-/

namespace OMA.S_oeis_a394399

/-- The neighboring numbers are the two primes of a twin-prime pair. -/
def TwinMidpoint (k : ℕ) : Prop := (k - 1).Prime ∧ (k + 1).Prime

/-- The gcd of a number and the sum of its positive divisors. -/
def divisorGcd (k : ℕ) : ℕ := Nat.gcd k (ArithmeticFunction.sigma 1 k)

/-- A twin-prime midpoint belongs to A394399 exactly when it also belongs to A392199 and A001105. -/
theorem main : ∀ k : ℕ, TwinMidpoint k →
    (divisorGcd k = 3 ↔ (divisorGcd k).Prime ∧ ∃ m : ℕ, k = 2 * m^2) := by
  sorry

end OMA.S_oeis_a394399

import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Twin-prime midpoints whose divisor-sum gcd is two

Source: https://oeis.org/A394815
Credit: @anmolspace

Aied Sulaiman conjectured that every term of A394815 is divisible by 36
and that A394757 is the disjoint union of A394815 and A394399.
-/

namespace OMA.S_oeis_a394815

/-- The gcd of k and the sum of all positive divisors of k. -/
def divisorGcd (k : ℕ) : ℕ := Nat.gcd k (ArithmeticFunction.sigma 1 k)

/-- Midpoints of pairs of neighboring primes at distance two. -/
def TwinMidpoint (k : ℕ) : Prop := (k-1).Prime ∧ (k+1).Prime

/-- The midpoints in A394757 have prime gcd. -/
def primeGcdMidpoints : Set ℕ := {k | TwinMidpoint k ∧ (divisorGcd k).Prime}

/-- A394815 and A394399 are the cases g = 2 and g = 3, respectively. -/
def midpointsWithGcd (g : ℕ) : Set ℕ := {k | TwinMidpoint k ∧ divisorGcd k = g}

/-- Both conjectures: divisibility by 36 and the disjoint union of sequences. -/
theorem main : (∀ k : ℕ, k ∈ midpointsWithGcd 2 → 36 ∣ k) ∧
    primeGcdMidpoints = midpointsWithGcd 2 ∪ midpointsWithGcd 3 ∧
    Disjoint (midpointsWithGcd 2) (midpointsWithGcd 3) := by
  sorry

end OMA.S_oeis_a394815

import Mathlib

/-!
# A140508: Mobius transform applied twice to A001414.

Source: https://oeis.org/A140508
Credit: @agchua

Entry by Mats Granvik, Jun 30 2008. Offset 1.

A001414(n) = sopfr(n) is the sum of the primes dividing n, with repetition (A001414(1) = 0).
The Mobius transform of f is n -> Sum_{d | n} mu(n/d) * f(d), and A140508 is this transform
applied twice to A001414.

Comment of the entry, verbatim:
Mobius transform applied once to A120007. Except for first term and zero divided by zero,
this sequence gives A008683 as:
mu(n) = -a(n)/abs(a(n)) through the conjecture in A140254.

The statement: for every n >= 2 (all terms except the first), a(n) = 0 exactly when
mu(n) = 0 (these are the zero divided by zero cases), and when a(n) /= 0 we have
mu(n) = -a(n)/|a(n)| (an exact integer division).
-/

namespace OMA.S_oeis_a140508

/-- A001414: the sum of the prime factors of n, counted with repetition. -/
def A001414 (n : ℕ) : ℕ := (Nat.primeFactorsList n).sum

/-- The Mobius transform of f: n -> Sum_{d | n} mu(n/d) * f(d). -/
def moebiusTransform (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, ArithmeticFunction.moebius (n / d) * f d

/-- A140508: the Mobius transform applied twice to A001414. -/
def a (n : ℕ) : ℤ := moebiusTransform (moebiusTransform (fun k => (A001414 k : ℤ))) n

theorem main : ∀ n : ℕ, 2 ≤ n →
    (a n = 0 ↔ ArithmeticFunction.moebius n = 0) ∧
    (a n ≠ 0 → ArithmeticFunction.moebius n = -a n / |a n|) := by
  sorry

end OMA.S_oeis_a140508

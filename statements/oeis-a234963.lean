import Mathlib

/-!
# A234963: Number of ways to write n = k + m with k > 0 and m > 2 such that C(2*sigma(k) + phi(m), sigma(k) + phi(m)/2) - 1 is prime, where sigma(k) is the sum of all positive divisors of k and phi(.) is Euler's totient function.

Source: https://oeis.org/A234963
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A234963 (Zhi-Wei Sun, Jan 01 2014): a(n) > 0 for all n
>= 180.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 1, 1, 2, 3, 0, 3, 2, 2, 3, ...). `a n` is the number of
  pairs (k, m) with k > 0, m > 2, n = k + m and C(2*sigma(k) + phi(m), sigma(k) + phi(m)/2) - 1
  prime, exactly as in the OEIS name.
* sigma(k) is the sum of the positive divisors of k, written as the sum over `Nat.divisors k`; phi
  is the Euler totient function `Nat.totient`. C is the binomial coefficient `Nat.choose`.
* For m > 2 the value phi(m) is even, so phi(m)/2 is an exact division; the binomial coefficient
  is at least 1, so the subtraction of 1 is exact.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a234963

/-- The condition in the name of A234963 on a tuple, for a given n. -/
def P (n : ℕ) (k m : ℕ) : Prop :=
  0 < k ∧ 2 < m ∧ k + m = n ∧
  (Nat.choose (2 * (∑ d ∈ k.divisors, d) + Nat.totient m)
    ((∑ d ∈ k.divisors, d) + Nat.totient m / 2) - 1).Prime

/-- A234963: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A234963. -/
theorem main : ∀ n : ℕ, 180 ≤ n → 0 < a n := by
  sorry

end OMA.S_oeis_a234963

import Mathlib

/-!
# A097967: a(n) = Sum_{k=1..n} (P(n,k) + C(n,k)).

Source: https://oeis.org/A097967
Credit: @agchua

R. J. Mathar (May 29 2013), in the formula section of A097967:
  Conjecture: a(n) +(-n-6)*a(n-1) +(6*n+7)*a(n-2) +(-13*n+14)*a(n-3) +4*(3*n-8)*a(n-4)
  +4*(-n+4)*a(n-5)=0.
Here P(n,k) = n!/(n-k)! is the number of k-permutations of n (Mathlib: n.descFactorial k) and
C(n,k) is the binomial coefficient (n.choose k). The sequence has offset 0 (a(0) = 0, an empty
sum). The recurrence uses a(n-5), so the conjecture is stated for n ≥ 5. Terms are taken in ℤ.
-/

namespace OMA.S_oeis_a097967

/-- A097967(n) = Sum_{k=1..n} (P(n,k) + C(n,k)) with P(n,k) = n!/(n-k)!. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, ((n.descFactorial k : ℤ) + (n.choose k : ℤ))

/-- Mathar's conjecture: the order-5 recurrence holds for all n ≥ 5. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    a n + (-(n : ℤ) - 6) * a (n - 1) + (6 * (n : ℤ) + 7) * a (n - 2)
      + (-13 * (n : ℤ) + 14) * a (n - 3) + 4 * (3 * (n : ℤ) - 8) * a (n - 4)
      + 4 * (-(n : ℤ) + 4) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a097967

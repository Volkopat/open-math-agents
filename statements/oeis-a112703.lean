import Mathlib

/-!
# A112703: Partial sum of Catalan numbers A000108 multiplied by powers of 9.

Source: https://oeis.org/A112703
Credit: @agchua

R. J. Mathar (Jun 08 2016), in the formula section of A112703:
  Conjecture: +(n+1)*a(n) +(-37*n+17)*a(n-1) +18*(2*n-1)*a(n-2)=0.
As in the formula section, a(n) = Sum_{k=0..n} C(k)*9^k with C(k) = A000108(k), the Catalan
numbers (Mathlib: `catalan`). The sequence has offset 0 (a(0) = 1). The recurrence uses a(n-2),
so the conjecture is stated for n ≥ 2. Terms are taken in ℤ.
-/

namespace OMA.S_oeis_a112703

/-- A112703(n) = Sum_{k=0..n} catalan(k) * 9^k. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (catalan k : ℤ) * 9 ^ k

/-- Mathar's conjecture: for n ≥ 2, (n+1) a(n) + (-37n+17) a(n-1) + 18(2n-1) a(n-2) = 0. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℤ) + 1) * a n + (-37 * (n : ℤ) + 17) * a (n - 1) + 18 * (2 * (n : ℤ) - 1) * a (n - 2)
      = 0 := by
  sorry

end OMA.S_oeis_a112703

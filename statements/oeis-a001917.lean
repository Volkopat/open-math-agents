import Mathlib

/-!
# Shevelev's conjecture for A001917

Sources: https://oeis.org/A001917 and https://oeis.org/A006694.
For an odd prime p the A001917 term at p is (p-1)/ord_p(2).
For odd m, A006694((m-1)/2) is the number of nonzero cyclotomic
cosets under doubling modulo m. The divisor formula in A006694
sums phi(d)/ord_d(2) over the divisors d > 1 of m.
Shevelev conjectured that the count at p^k is k times the count
at p, for every odd prime p and positive exponent k.
-/

namespace OMA.S_oeis_a001917

noncomputable def cosets (m : ℕ) : ℕ :=
  ∑ d ∈ m.divisors with 1 < d, d.totient / orderOf (2 : ZMod d)

noncomputable def primeTerm (p : ℕ) : ℕ := (p-1) / orderOf (2 : ZMod p)

theorem main : ∀ p k : ℕ, p.Prime → p ≠ 2 → 0 < k →
    k * primeTerm p = cosets (p^k) := by
  sorry

end OMA.S_oeis_a001917

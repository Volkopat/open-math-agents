import Mathlib

/-!
# A117119: Number of partitions of 2*n into two odd prime powers.

Source: https://oeis.org/A117119
Credit: @agchua

Comment of A117119 (the entry is by Reinhard Zumkeller, Apr 15 2006), verbatim:
  Conjecture: For all n, a(n) > 0; a(n) > A002375(n).
A002375 (offset 1): From Goldbach conjecture: number of decompositions of 2n into an unordered
sum of two odd primes.

Formalisation. As in the entry's examples (a(1) = #{1+1} = 1, a(2) = #{1+3} = 1) and programs,
the odd prime powers are those of A061345: 1 together with p^k for an odd prime p and k >= 1,
that is m = 1, or m odd and IsPrimePow m. A partition of 2n into two odd prime powers is
i + (2n - i) with 1 <= i <= n (so i <= 2n - i) and both parts odd prime powers; a(n) counts
these i. A002375(n) counts the odd primes p with p <= n for which 2n - p is an odd prime. Both
sequences have offset 1, so the conjecture is stated for all n >= 1.
-/

namespace OMA.S_oeis_a117119

/-- m is an odd prime power in the sense of A061345: m = 1, or m = p^k with p an odd prime. -/
def IsOddPrimePow (m : ℕ) : Prop := m = 1 ∨ (Odd m ∧ IsPrimePow m)

instance (m : ℕ) : Decidable (IsOddPrimePow m) :=
  inferInstanceAs (Decidable (m = 1 ∨ (Odd m ∧ IsPrimePow m)))

/-- A117119: the number of partitions of 2n into two odd prime powers. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun i => IsOddPrimePow i ∧ IsOddPrimePow (2 * n - i))).card

/-- A002375: the number of decompositions of 2n into an unordered sum of two odd primes. -/
noncomputable def A002375 (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter
    (fun p => Odd p ∧ p.Prime ∧ Odd (2 * n - p) ∧ (2 * n - p).Prime)).card

/-- Conjecture: For all n, a(n) > 0; a(n) > A002375(n). -/
theorem main : ∀ n : ℕ, 1 ≤ n → 0 < a n ∧ A002375 n < a n := by
  sorry

end OMA.S_oeis_a117119

import Mathlib

/-!
# A286971: Number of ways to write n as a sum of two numbers, one of which is the product of an even number of distinct primes (including 1) (A030229) and another is the product of an odd number of distinct primes (A030059).

Source: https://oeis.org/A286971
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A286971 (Ilya Gutkovskiy, May 17 2017): a(n) > 0 for
all n > 10.

Conventions:
* The sequence has offset 0 (data 0, 0, 0, 1, 1, 0, 1, 0, 2, 1, 0, 1, ...). `a n` is the number of
  pairs (i, j) with n = i + j, i a product of an even number of distinct primes (including 1;
  A030229) and j a product of an odd number of distinct primes (A030059), as in the OEIS name.
* A positive integer is a product of an even (resp. odd) number of distinct primes exactly when
  its Moebius function value is 1 (resp. -1); these are the sequences A030229 and A030059, and
  this is how the Mathematica program in the entry computes the sequence. The Moebius function is
  `ArithmeticFunction.moebius` (its value at 0 is 0, so i and j are positive).
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a286971

/-- The condition in the name of A286971 on a tuple, for a given n. -/
def P (n : ℕ) (i j : ℕ) : Prop :=
  i + j = n ∧ ArithmeticFunction.moebius i = 1 ∧ ArithmeticFunction.moebius j = -1

/-- A286971: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A286971. -/
theorem main : ∀ n : ℕ, 10 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a286971

import Mathlib

/-!
# A303932: Number of ways to write 2*n as p + 2^k + 3^m, where p is a prime with 11 a quadratic residue modulo p, and k and m are nonnegative integers.

Source: https://oeis.org/A303932
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A303932 (Zhi-Wei Sun, May 02 2018), Conjecture 1: a(n)
> 0 for all n > 1, i.e., any even number greater than two can be written as the sum of a power 2,
a power of 3 and a prime p with 11 a quadratic residue modulo p.

Conventions:
* The sequence has offset 1 (data 0, 1, 1, 1, 3, 4, 2, 3, 3, 1, 3, 5, ...). `a n` is the number of
  triples (p, k, m) with 2*n = p + 2^k + 3^m, where p is a prime with 11 a quadratic residue
  modulo p and k, m are natural numbers, exactly as in the OEIS name.
* `11 is a quadratic residue modulo the prime p` means that p does not divide 11 and 11 is
  congruent to a square modulo p: `p ≠ 11 ∧ IsSquare (11 : ZMod p)`. For odd p this is the
  Legendre symbol (11/p) = 1, and for p = 2 it holds (11 is odd), as in the OEIS examples (a(2) =
  1 since 2*2 = 2 + 2^0 + 3^0 with 11 a quadratic residue modulo the prime 2); p = 11 is excluded,
  as in the Mathematica program of the entry (Jacobi symbol equal to 1).
* Only Conjecture 1 is formalized; Conjecture 2 is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a303932

/-- The condition in the name of A303932 on a tuple, for a given n. -/
def P (n : ℕ) (p k m : ℕ) : Prop :=
  p.Prime ∧ p ≠ 11 ∧ IsSquare (11 : ZMod p) ∧ p + 2 ^ k + 3 ^ m = 2 * n

/-- A303932: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A303932. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a303932

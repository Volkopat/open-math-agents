import Mathlib

/-!
# A262985: Number of ordered ways to write n as 2^x + phi(y^2) + z*(z+1)/2 with x, y and z positive integers, where phi(.) is Euler's totient function given by A000010.

Source: https://oeis.org/A262985
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A262985 (Zhi-Wei Sun, Oct 06 2015): a(n) > 0 for all n
> 3.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 1, 1, 2, 2, 1, 3, 2, 5, 2, ...). `a n` is the number of
  triples (x, y, z) of positive integers with n = 2^x + phi(y^2) + z*(z+1)/2, exactly as in the
  OEIS name.
* phi is `Nat.totient`.
* The division by 2 is natural-number division, which is exact because z*(z+1) is even.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a262985

/-- The condition in the name of A262985 on a tuple, for a given n. -/
def P (n : ℕ) (x y z : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ 2 ^ x + Nat.totient (y ^ 2) + z * (z + 1) / 2 = n

/-- A262985: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A262985. -/
theorem main : ∀ n : ℕ, 3 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a262985

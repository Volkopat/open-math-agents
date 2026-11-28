import Mathlib

/-!
# A262979: Number of ordered ways to write n as x^4 + phi(y^2) + z*(3*z-1)/2 with x >= 0 and y > 0, where phi(.) is Euler's totient function given by A000010.

Source: https://oeis.org/A262979
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A262979 (Zhi-Wei Sun, Oct 06 2015), part (i): a(n) > 0
for all n > 0.

Conventions:
* The sequence has offset 1 (data 1, 3, 4, 3, 1, 2, 4, 5, 5, 3, 2, 2, ...). `a n` is the number of
  triples (x, y, z) with x a natural number, y a positive integer and z an integer such that n =
  x^4 + phi(y^2) + z*(3*z-1)/2, exactly as in the OEIS name.
* phi is the Euler totient function `Nat.totient`.
* z ranges over all integers (the OEIS examples use negative z, e.g. a(5) = 1 since 5 = 1^4 +
  phi(2^2) + (-1)*(3*(-1)-1)/2); the equation is stated in `ℤ` with the natural quantities cast,
  and the integer division by 2 is exact since z*(3z-1) is even.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a262979

/-- The condition in the name of A262979 on a tuple, for a given n. -/
def P (n : ℕ) (x y : ℕ) (z : ℤ) : Prop :=
  0 < y ∧ (x : ℤ) ^ 4 + (Nat.totient (y ^ 2) : ℤ) + z * (3 * z - 1) / 2 = n

/-- A262979: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℤ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A262979. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a262979

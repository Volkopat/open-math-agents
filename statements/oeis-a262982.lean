import Mathlib

/-!
# A262982: Number of ordered ways to write n as x^4 + phi(y^2) + z*(z+1)/2 with x >= 0, y > 0 and z > 0, where phi(.) is Euler's totient function given by A000010.

Source: https://oeis.org/A262982
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A262982 (Zhi-Wei Sun, Oct 06 2015): a(n) > 0 for all n > 1, and a(n) = 1 only for
n = 2, 6, 20, 26, 40, 82, 89, 105, 305, 416, 470, 725, 6135, 25430, 90285.

Conventions:
* The sequence has offset 1 (data 0, 1, 2, 2, 2, 1, 2, 3, 3, 2, 2, 4, ...). `a n` is the number
  of triples (x, y, z) of natural numbers with x >= 0, y > 0, z > 0 and
  n = x^4 + phi(y^2) + z*(z+1)/2, exactly as in the OEIS name.
* phi is `Nat.totient`; z*(z+1)/2 is natural number division, which is exact since
  z*(z+1) is even.
* The set of such triples is finite for every n, so `Set.ncard` is its number of elements.
* Both parts are stated for every n > 1 (the range of the conjecture; a(1) = 0). The second
  part is rendered literally as an only-if: a(n) = 1 implies n is one of the listed values.
-/

namespace OMA.S_oeis_a262982

/-- A262982: number of triples (x, y, z) with y > 0, z > 0 and
x^4 + phi(y^2) + z*(z+1)/2 = n. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℕ | 0 < x.2.1 ∧ 0 < x.2.2 ∧
    x.1 ^ 4 + Nat.totient (x.2.1 ^ 2) + x.2.2 * (x.2.2 + 1) / 2 = n}

/-- The conjecture of Sun: a(n) > 0 for all n > 1, and a(n) = 1 only for the 15 listed n. -/
theorem main : ∀ n : ℕ, 1 < n →
    0 < a n ∧ (a n = 1 → n ∈ ({2, 6, 20, 26, 40, 82, 89, 105, 305, 416, 470, 725, 6135,
      25430, 90285} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a262982

import Mathlib

/-!
# A301303: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x >= y >= 0 <= z <= w such that x^2 + 23*y^2 = 2^k*m^3 for some k = 0,1,2 and m = 1,2,3,....

Source: https://oeis.org/A301303
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A301303 (Zhi-Wei Sun, Mar 17 2018): a(n) > 0 for all n
> 0, and a(n) = 1 only for n = 2^k (k = 0,1,2,...), 3, 7, 115, 151, 219, 267, 1151, 1367.

Conventions:
* The sequence has offset 1 (data 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with n = x^2 + y^2 + z^2 + w^2, x >= y >= 0 <= z <=
  w, such that x^2 + 23*y^2 = 2^k*m^3 for some k = 0,1,2 and m = 1,2,3,..., exactly as in the OEIS
  name.
* The chain x >= y >= 0 <= z <= w is the two conditions y <= x and z <= w on natural numbers.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a301303

/-- The condition in the name of A301303 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ y ≤ x ∧ z ≤ w ∧
  ∃ k m : ℕ, k ≤ 2 ∧ 0 < m ∧ x ^ 2 + 23 * y ^ 2 = 2 ^ k * m ^ 3

/-- A301303: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A301303. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      (∃ k : ℕ, n = 2 ^ k) ∨ n ∈ ({3, 7, 115, 151, 219, 267, 1151, 1367} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a301303

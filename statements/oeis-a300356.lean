import Mathlib

/-!
# A300356: Number of ways to write n^2 as x^2 + y^2 + z^2 + w^2 with x >= y >= 0 <= z <= w such that x + 63*y = 2^(2k+1) for some nonnegative integer k.

Source: https://oeis.org/A300356
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A300356 (Zhi-Wei Sun, Mar 03 2018), part (i): a(n) > 0
for all n > 1, and a(n) = 1 only for n = 5, 13, 25, 29, 59, 61, 91, 95, 101, 103, 211, 247, 2^k (k
= 1,2,...), 4^k*79 (k = 0,1,2,...), 2^(2k+1)*m (k = 0,1,2,... and m = 3, 5, 7, 11, 15, 19, 23).

Conventions:
* The sequence has offset 1 (data 0, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with n^2 = x^2 + y^2 + z^2 + w^2, x >= y >= 0 <= z <=
  w, and x + 63*y = 2^(2k+1) for some nonnegative integer k, exactly as in the OEIS name.
* The chain x >= y >= 0 <= z <= w is the two conditions y <= x and z <= w on natural numbers.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a300356

/-- The condition in the name of A300356 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ^ 2 ∧ y ≤ x ∧ z ≤ w ∧ ∃ k : ℕ, x + 63 * y = 2 ^ (2 * k + 1)

/-- A300356: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A300356. -/
theorem main : ∀ n : ℕ, 1 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({5, 13, 25, 29, 59, 61, 91, 95, 101, 103, 211, 247} : Finset ℕ) ∨
      (∃ k : ℕ, 0 < k ∧ n = 2 ^ k) ∨ (∃ k : ℕ, n = 4 ^ k * 79) ∨
      (∃ k m : ℕ, m ∈ ({3, 5, 7, 11, 15, 19, 23} : Finset ℕ) ∧
      n = 2 ^ (2 * k + 1) * m))) := by
  sorry

end OMA.S_oeis_a300356

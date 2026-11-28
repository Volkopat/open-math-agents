import Mathlib

/-!
# A300396: Number of ways to write n^2 as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers and z <= w such that 2*x or y is a power of 4 (including 4^0 = 1) and x + 63*y = 2^(2k+1) for some k = 0,1,2,....

Source: https://oeis.org/A300396
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A300396 (Zhi-Wei Sun, Mar 05 2018): a(n) > 0 for all n
> 1, and a(n) = 1 only for n = 5, 13, 25, 29, 59, 61, 79, 91, 95, 101, 103, 1315, 2^k (k =
1,2,3,...), 2^(2k+1)*m (k = 0,1,2,... and m = 3, 5, 7, 11, 15, 19, 23, 887).

Conventions:
* The sequence has offset 1 (data 0, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with n^2 = x^2 + y^2 + z^2 + w^2, z <= w, such that
  2*x or y is a power of 4 (including 4^0 = 1) and x + 63*y = 2^(2k+1) for some k = 0,1,2,...,
  exactly as in the OEIS name.
* A power of 4 is 4^k with k = 0, 1, 2, ... (4^0 = 1 included).
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a300396

/-- The condition in the name of A300396 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ^ 2 ∧ z ≤ w ∧
  ((∃ k : ℕ, 2 * x = 4 ^ k) ∨ (∃ k : ℕ, y = 4 ^ k)) ∧
  ∃ k : ℕ, x + 63 * y = 2 ^ (2 * k + 1)

/-- A300396: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A300396. -/
theorem main : ∀ n : ℕ, 1 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({5, 13, 25, 29, 59, 61, 79, 91, 95, 101, 103, 1315} : Finset ℕ) ∨
      (∃ k : ℕ, 0 < k ∧ n = 2 ^ k) ∨
      (∃ k m : ℕ, m ∈ ({3, 5, 7, 11, 15, 19, 23, 887} : Finset ℕ) ∧
      n = 2 ^ (2 * k + 1) * m))) := by
  sorry

end OMA.S_oeis_a300396

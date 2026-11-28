import Mathlib

/-!
# A306239: Number of ways to write n as x^3 + y^3 + pen(z) + pen(w), where x, y, z, w are nonnegative integers with x <= y and z <= w, and pen(k) denotes the pentagonal number k*(3*k-1)/2.

Source: https://oeis.org/A306239
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A306239 (Zhi-Wei Sun, Jan 31 2019): a(n) > 0 for all n
>= 0, and a(n) = 1 only for n = 0, 4, 5, 16, 20, 46. Also, any nonnegative integer not equal to 16
can be written as x^6 + y^3 + pen(z) + pen(w) with x, y, z, w nonnegative integers.

Conventions:
* The sequence has offset 0 (data 1, 2, 3, 2, 1, 1, 2, 2, 2, 2, 3, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with x <= y, z <= w and n = x^3 + y^3 + pen(z) +
  pen(w), exactly as in the OEIS name.
* pen(k) = k*(3*k-1)/2 is the pentagonal number, for k = 0, 1, 2, ...; in `ℕ` the truncated
  subtraction only matters at k = 0, where the product is 0 anyway (pen(0) = 0), and the division
  by 2 is exact.
* Both sentences are formalized, as a conjunction.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a306239

/-- The pentagonal number pen(k) = k*(3*k-1)/2. -/
def pen (k : ℕ) : ℕ := k * (3 * k - 1) / 2

/-- The condition in the name of A306239 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ≤ y ∧ z ≤ w ∧ x ^ 3 + y ^ 3 + pen z + pen w = n

/-- A306239: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A306239. -/
theorem main : (∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n ∈ ({0, 4, 5, 16, 20, 46} : Finset ℕ))) ∧
    (∀ n : ℕ, n ≠ 16 → ∃ x y z w : ℕ, x ^ 6 + y ^ 3 + pen z + pen w = n) := by
  sorry

end OMA.S_oeis_a306239

import Mathlib

/-!
# A275824: Number of ways to write n as pen(x) + pen(y) + pen (z) + 2*pen(w), where x,y,z,w are nonnegative integers with x <= y <= z, and pen(k) denotes the pentagonal number k*(3*k-1)/2.

Source: https://oeis.org/A275824
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A275824 (Zhi-Wei Sun, Aug 10 2016), part (i): a(n) > 0
for all n = 0,1,2,...., and a(n) = 1 only for n = 0, 1, 4, 6, 8, 9, 18, 19, 21, 33, 40, 43.

Conventions:
* The sequence has offset 0 (data 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with x <= y <= z and n = pen(x) + pen(y) + pen(z) +
  2*pen(w), exactly as in the OEIS name.
* pen(k) = k*(3*k-1)/2 is the pentagonal number, for k = 0, 1, 2, ...; in `ℕ` the truncated
  subtraction only matters at k = 0, where the product is 0 anyway (pen(0) = 0), and the division
  by 2 is exact.
* Only part (i) of the conjecture is formalized; part (ii) is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a275824

/-- The pentagonal number pen(k) = k*(3*k-1)/2. -/
def pen (k : ℕ) : ℕ := k * (3 * k - 1) / 2

/-- The condition in the name of A275824 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  x ≤ y ∧ y ≤ z ∧ pen x + pen y + pen z + 2 * pen w = n

/-- A275824: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A275824. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n ∈ ({0, 1, 4, 6, 8, 9, 18, 19, 21, 33, 40, 43} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a275824

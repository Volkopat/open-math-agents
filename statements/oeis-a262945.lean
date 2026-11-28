import Mathlib

/-!
# A262945: Number of ordered pairs (x,y) with x >= 0 and y >= 0 such that n - x^4 - 2*y^2 is a triangular number or a pentagonal number.

Source: https://oeis.org/A262945
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A262945 (Zhi-Wei Sun, Oct 05 2015): a(n) > 0 for every
n = 0,1,2,..., and a(n) = 1 only for the following 55 values of n: 0, 26, 27, 32, 41, 42, 50, 65,
80, 97, 112, 122, 130, 160, 196, 227, 239, 272, 322, 371, 612, 647, 736, 967, 995, 1007, 1106,
1127, 1205, 1237, 1240, 1262, 1637, 1657, 1757, 2912, 2987, 3062, 3107, 3524, 3647, 3902, 5387,
5587, 5657, 6047, 6107, 11462, 13427, 14717, 15002, 17132, 20462, 30082, 35750.

Conventions:
* The sequence has offset 0 (data 1, 2, 2, 3, 2, 2, 3, 2, 3, 3, 2, 2, ...). `a n` is the number of
  pairs (x, y) of natural numbers such that n - x^4 - 2*y^2 is a triangular number or a pentagonal
  number, exactly as in the OEIS name.
* A triangular number is k*(k+1)/2 and a pentagonal number is k*(3k-1)/2 with k = 0, 1, 2, ...;
  the condition is written without subtraction as an equation for n. The divisions by 2 are exact,
  and at k = 0 the truncated 3k - 1 is multiplied by 0.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a262945

/-- The condition in the name of A262945 on a tuple, for a given n. -/
def P (n : ℕ) (x y : ℕ) : Prop :=
  ∃ k : ℕ, x ^ 4 + 2 * y ^ 2 + k * (k + 1) / 2 = n ∨ x ^ 4 + 2 * y ^ 2 + k * (3 * k - 1) / 2 = n

/-- A262945: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A262945. -/
theorem main : ∀ n : ℕ, 0 < a n ∧ (a n = 1 →
      n ∈ ({0, 26, 27, 32, 41, 42, 50, 65, 80, 97, 112, 122, 130, 160, 196, 227, 239, 272,
        322, 371, 612, 647, 736, 967, 995, 1007, 1106, 1127, 1205, 1237, 1240, 1262, 1637,
        1657, 1757, 2912, 2987, 3062, 3107, 3524, 3647, 3902, 5387, 5587, 5657, 6047, 6107,
        11462, 13427, 14717, 15002, 17132, 20462, 30082, 35750} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a262945

import Mathlib

/-!
# A273107: Number of ordered ways to write n as x^2 + y^2 + z^2 + w^2 with (8*x+12*y)^2 + (15*z)^2 a square, where x,y,z,w are nonnegative integers with x+y > 0 and z > 0.

Source: https://oeis.org/A273107
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A273107 (Zhi-Wei Sun, May 15 2016): a(n) > 0 for all n
> 5, and a(n) = 1 only for n = 7, 9, 23, 25, 31, 55, 2^k*m (k = 1,2,... and m = 1, 5), 2^(2k+1)*m
(k = 0,1,2,... and m = 3, 13, 21).

Conventions:
* The sequence has offset 1 (data 0, 1, 2, 1, 0, 1, 1, 1, 1, 1, 3, 4, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with x + y > 0, z > 0, (8*x+12*y)^2 + (15*z)^2 a
  square and n = x^2 + y^2 + z^2 + w^2, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`.
* The positivity part is stated for n > 5 and the only-if part for every n >= 1 (the offset), as
  in the entry.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a273107

/-- The condition in the name of A273107 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  0 < x + y ∧ 0 < z ∧ IsSquare ((8 * x + 12 * y) ^ 2 + (15 * z) ^ 2) ∧
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n

/-- A273107: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A273107. -/
theorem main : ∀ n : ℕ, 0 < n → ((5 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({7, 9, 23, 25, 31, 55} : Finset ℕ) ∨
      (∃ k m : ℕ, 1 ≤ k ∧ m ∈ ({1, 5} : Finset ℕ) ∧ n = 2 ^ k * m) ∨
      (∃ k m : ℕ, m ∈ ({3, 13, 21} : Finset ℕ) ∧ n = 2 ^ (2 * k + 1) * m))) := by
  sorry

end OMA.S_oeis_a273107

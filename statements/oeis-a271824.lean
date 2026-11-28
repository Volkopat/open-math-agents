import Mathlib

/-!
# A271824: Number of ordered ways to write n as x^2 + y^2 + z^2 + w^2 with (x+2*y)^2 + 8*z^2 + 40*w^2 a square, where x is a positive integer and y,z,w are nonnegative integers.

Source: https://oeis.org/A271824
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A271824 (Zhi-Wei Sun, Apr 14 2016), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 9, 11, 15, 23, 33, 71, 129, 167, 187, 473, 4^k*m (k =
0,1,2,... and m = 1, 22, 38, 278). Also, any positive integer can be written as x^2 + y^2 + z^2 +
w^2 with 9*(x+2*y)^2 + 16*z^2 + 24*w^2 a square, where x is a positive integer and y,z,w are
nonnegative integers.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 1, 2, 2, 2, 2, 1, 4, 1, 3, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with x > 0, (x+2*y)^2 + 8*z^2 + 40*w^2 a square and n
  = x^2 + y^2 + z^2 + w^2, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`.
* Both sentences of part (i) are formalized, as a conjunction. Parts (ii)-(iv) are different
  statements and are not formalized.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a271824

/-- The condition in the name of A271824 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  0 < x ∧ IsSquare ((x + 2 * y) ^ 2 + 8 * z ^ 2 + 40 * w ^ 2) ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n

/-- A271824: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A271824. -/
theorem main : (∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({9, 11, 15, 23, 33, 71, 129, 167, 187, 473} : Finset ℕ) ∨
      (∃ k m : ℕ, m ∈ ({1, 22, 38, 278} : Finset ℕ) ∧ n = 4 ^ k * m)))) ∧
    (∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < x ∧
      IsSquare (9 * (x + 2 * y) ^ 2 + 16 * z ^ 2 + 24 * w ^ 2) ∧
      x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) := by
  sorry

end OMA.S_oeis_a271824

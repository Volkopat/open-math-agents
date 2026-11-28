import Mathlib

/-!
# A272977: Number of ordered ways to write n as x^2 + y^2 + z^2 + w^2 with 3*x^2*y + z^2*w a square, where w is a nonzero integer and x,y,z are nonnegative integers with x >= z.

Source: https://oeis.org/A272977
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A272977 (Zhi-Wei Sun, May 11 2016), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 3, 7, 23, 47, 71, 147, 199, 263, 439, 16^k*m (k =
0,1,2,... and m = 6, 12, 24, 44, 56, 140, 156, 174, 204, 284, 4652).

Conventions:
* The sequence has offset 1 (data 2, 4, 1, 3, 8, 1, 1, 4, 3, 11, 3, 1, ...). `a n` is the number
  of quadruples (x, y, z, w) with x, y, z natural numbers, w a nonzero integer, x >= z, 3*x^2*y +
  z^2*w a square and n = x^2 + y^2 + z^2 + w^2, exactly as in the OEIS name.
* Integer variables range over `ℤ`; the equation and the side conditions involving them are stated
  in `ℤ`, with the natural variables and n cast.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`; the
  quantity is computed in `ℤ` (with the natural variables cast), where a negative value is never a
  square.
* Only part (i) of the conjecture is formalized; part (ii) concerns other forms.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a272977

/-- The condition in the name of A272977 on a tuple, for a given n. -/
def P (n : ℕ) (x y z : ℕ) (w : ℤ) : Prop :=
  w ≠ 0 ∧ z ≤ x ∧ IsSquare (3 * (x : ℤ) ^ 2 * (y : ℤ) + (z : ℤ) ^ 2 * w) ∧
    (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 + w ^ 2 = (n : ℤ)

/-- A272977: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℤ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A272977. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({3, 7, 23, 47, 71, 147, 199, 263, 439} : Finset ℕ) ∨
      (∃ k m : ℕ, m ∈ ({6, 12, 24, 44, 56, 140, 156, 174, 204, 284, 4652} : Finset ℕ) ∧ n = 16 ^ k * m))) := by
  sorry

end OMA.S_oeis_a272977

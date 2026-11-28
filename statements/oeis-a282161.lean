import Mathlib

/-!
# A282161: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x and (12*x)^2 + (5*y-10*z)^2 both squares, where x,y,z are nonnegative integers and w is a positive integer.

Source: https://oeis.org/A282161
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A282161 (Zhi-Wei Sun, Feb 07 2017), part (i): a(n) > 0
for all n > 0, and a(n) = 1 only for n = 16^k*m (k = 0,1,2,... and m = 1, 23, 28, 79, 119, 191,
223, 263, 463, 703, 860, 1052).

Conventions:
* The sequence has offset 1 (data 1, 3, 2, 2, 5, 4, 2, 2, 4, 6, 4, 3, ...). `a n` is the number of
  quadruples (x, y, z, w) of natural numbers with w > 0, both x and (12*x)^2 + (5*y-10*z)^2
  squares, and n = x^2 + y^2 + z^2 + w^2, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`.
* The quantity (12*x)^2 + (5*y-10*z)^2 is computed in `ℤ`, since 5*y - 10*z may be negative.
* Only part (i) of the conjecture is formalized; part (ii) concerns another form.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a282161

/-- The condition in the name of A282161 on a tuple, for a given n. -/
def P (n : ℕ) (x y z w : ℕ) : Prop :=
  0 < w ∧ IsSquare x ∧ IsSquare ((12 * (x : ℤ)) ^ 2 + (5 * (y : ℤ) - 10 * (z : ℤ)) ^ 2) ∧
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n

/-- A282161: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A282161. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      (∃ k m : ℕ, m ∈ ({1, 23, 28, 79, 119, 191, 223, 263, 463, 703, 860, 1052} : Finset ℕ) ∧ n = 16 ^ k * m))) := by
  sorry

end OMA.S_oeis_a282161

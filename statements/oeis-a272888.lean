import Mathlib

/-!
# A272888: Number of ordered ways to write n as w^2 + x^2 + y^2 + z^2 with w*(x^2 + 8*y^2 - z^2) a square, where w,x,y are nonnegative integers and z is a positive integer.

Source: https://oeis.org/A272888
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A272888 (Zhi-Wei Sun, May 08 2016): a(n) > 0 for all n
> 0, and a(n) = 1 only for n = 1, 7, 39, 63, 87, 5116, 2^(4k+2)*m (k = 0,1,2,... and m = 1, 7).

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 1, 4, 5, 1, 2, 5, 5, 4, 4, ...). `a n` is the number of
  quadruples (w, x, y, z) of natural numbers with z > 0, w*(x^2 + 8*y^2 - z^2) a square and n =
  w^2 + x^2 + y^2 + z^2, exactly as in the OEIS name.
* `a square` means the square of an integer (0 included), which is Mathlib's `IsSquare`; the
  quantity is computed in `ℤ` (with the natural variables cast), where a negative value is never a
  square.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a272888

/-- The condition in the name of A272888 on a tuple, for a given n. -/
def P (n : ℕ) (w x y z : ℕ) : Prop :=
  0 < z ∧ IsSquare ((w : ℤ) * ((x : ℤ) ^ 2 + 8 * (y : ℤ) ^ 2 - (z : ℤ) ^ 2)) ∧
  w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = n

/-- A272888: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A272888. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({1, 7, 39, 63, 87, 5116} : Finset ℕ) ∨
      (∃ k m : ℕ, m ∈ ({1, 7} : Finset ℕ) ∧ n = 2 ^ (4 * k + 2) * m))) := by
  sorry

end OMA.S_oeis_a272888

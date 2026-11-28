import Mathlib

/-!
# A263992: Number of ordered ways to write n as x^2 + 2*y^2 + phi(z^2) (x >= 0, y >= 0 and z > 0) such that y or z has the form p-1 with p prime, where phi(.) is Euler's totient function.

Source: https://oeis.org/A263992
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A263992 (Zhi-Wei Sun, Oct 31 2015): a(n) > 0 for all n
> 0, and a(n) = 1 only for n = 1, 6, 7, 22, 3447.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 2, 2, 1, 1, 3, 3, 4, 3, 4, ...). `a n` is the number of
  triples (x, y, z) of natural numbers with z > 0 and n = x^2 + 2*y^2 + phi(z^2), such that y or z
  has the form p - 1 with p prime, exactly as in the OEIS name.
* phi is the Euler totient function `Nat.totient`.
* `y has the form p - 1 with p prime` is `(y + 1).Prime`, and likewise for z.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a263992

/-- The condition in the name of A263992 on a tuple, for a given n. -/
def P (n : ℕ) (x y z : ℕ) : Prop :=
  0 < z ∧ x ^ 2 + 2 * y ^ 2 + Nat.totient (z ^ 2) = n ∧ ((y + 1).Prime ∨ (z + 1).Prime)

/-- A263992: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A263992. -/
theorem main : ∀ n : ℕ, 0 < n → ((0 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({1, 6, 7, 22, 3447} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a263992

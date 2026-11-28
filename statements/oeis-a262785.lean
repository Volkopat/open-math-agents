import Mathlib

/-!
# A262785: Number of ordered ways to write n as x^2 + y^2 + p*(p+d)/2, where 0 <= x <= y, d is 1 or -1, and p is prime.

Source: https://oeis.org/A262785
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A262785 (Zhi-Wei Sun, Oct 01 2015), part (i): (i) a(n)
> 0 for all n > 0, and a(n) = 1 only for n = 1, 2, 9, 34, 45, 49, 72, 97, 241, 337, 538.

Conventions:
* The sequence has offset 1 (data 1, 1, 3, 2, 3, 2, 3, 3, 1, 3, 5, 3, ...). `a n` is the number of
  quadruples (x, y, p, d) with x, y natural numbers, x <= y, d = 1 or d = -1, p prime and n = x^2
  + y^2 + p*(p+d)/2, exactly as in the OEIS name.
* The sign d is an integer and the equation is stated in `ℤ`; the division by 2 is integer
  division, which is exact because p*(p+d) is a product of two consecutive integers.
* Only part (i) of the conjecture is formalized; part (ii) is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a262785

/-- The condition in the name of A262785 on a tuple, for a given n. -/
def P (n : ℕ) (x y p : ℕ) (d : ℤ) : Prop :=
  x ≤ y ∧ (d = 1 ∨ d = -1) ∧ p.Prime ∧
    (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (p : ℤ) * ((p : ℤ) + d) / 2 = (n : ℤ)

/-- A262785: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℤ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A262785. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ∧ (a n = 1 →
      n ∈ ({1, 2, 9, 34, 45, 49, 72, 97, 241, 337, 538} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a262785

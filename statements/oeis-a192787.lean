import Mathlib

/-!
# A192787: Number of distinct solutions of 4/n = 1/a + 1/b + 1/c in positive integers satisfying 1 <= a <= b <= c.

Source: https://oeis.org/A192787
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A192787 (Charles R Greathouse IV, Jul 10 2011):
(Erdős-Straus) a(n) > 0 for n > 1.

Conventions:
* The sequence has offset 1 (data 0, 1, 3, 3, 2, 8, 7, 10, 6, 12, 9, 21, ...).
* `a n` is the number of triples (a, b, c) of positive integers with 1 <= a <= b <= c and 4/n =
  1/a + 1/b + 1/c, the equation being stated in `ℚ` (a finite set for n >= 1, counted with
  `Set.ncard`).
-/

namespace OMA.S_oeis_a192787

/-- A192787: number of solutions of 4/n = 1/a + 1/b + 1/c with 1 <= a <= b <= c. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | 1 ≤ t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
    (4 : ℚ) / n = 1 / (t.1 : ℚ) + 1 / (t.2.1 : ℚ) + 1 / (t.2.2 : ℚ)}

/-- The Erdős-Straus conjecture as recorded in A192787. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a192787

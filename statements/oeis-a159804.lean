import Mathlib

/-!
# A159804: Number of primes q with (2n-1)^2+1 <= q < (2n)^2-(2n-1).

Source: https://oeis.org/A159804
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A159804 (Ulrich Krug (leuchtfeuer37(AT)gmx.de), Apr 22
2009): a(n) >= 1 for n >= 1.

Conventions:
* The sequence has offset 1 (data 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 4, 2, ...).
* `a n` is the number of primes q with (2n-1)^2 + 1 <= q < (2n)^2 - (2n-1) (a finite set, counted
  with `Set.ncard`).
* The upper bound q < (2n)^2 - (2n-1) is written q + (2n-1) < (2n)^2 to avoid subtracting from the
  square; 2n - 1 is an exact natural-number subtraction for n >= 1.
-/

namespace OMA.S_oeis_a159804

/-- A159804: number of primes q with (2n-1)^2 + 1 <= q < (2n)^2 - (2n-1). -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {q : ℕ | q.Prime ∧ (2 * n - 1) ^ 2 + 1 ≤ q ∧ q + (2 * n - 1) < (2 * n) ^ 2}

/-- The conjecture recorded in A159804. -/
theorem main : ∀ n : ℕ, 1 ≤ n → 1 ≤ a n := by
  sorry

end OMA.S_oeis_a159804

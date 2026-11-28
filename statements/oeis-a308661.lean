import Mathlib

/-!
# A308661: Number of ways to write 12*n+5 as (2^a*5^b)^2 + c^2 + d^2, where a,b,c,d are nonnegative integers with a > 0 and c <= d.

Source: https://oeis.org/A308661
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A308661 (Zhi-Wei Sun, Jun 15 2019), Conjecture 1: a(n)
> 0 for all n = 0,1,2,....

Conventions:
* The sequence has offset 0 (data 1, 2, 3, 3, 2, 3, 3, 5, 5, 4, 5, 3, ...). `a n` is the number of
  quadruples (a, b, c, d) of natural numbers with a > 0, c <= d and 12*n+5 = (2^a*5^b)^2 + c^2 +
  d^2, exactly as in the OEIS name.
* Only the first sentence of Conjecture 1 is formalized (the entry adds an equivalent
  reformulation, which is not formalized separately); Conjecture 2 is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a308661

/-- The condition in the name of A308661 on a tuple, for a given n. -/
def P (n : ℕ) (a b c d : ℕ) : Prop :=
  0 < a ∧ c ≤ d ∧ (2 ^ a * 5 ^ b) ^ 2 + c ^ 2 + d ^ 2 = 12 * n + 5

/-- A308661: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A308661. -/
theorem main : ∀ n : ℕ, 0 < a n := by
  sorry

end OMA.S_oeis_a308661

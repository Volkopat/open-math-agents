import Mathlib

/-!
# A300510: Number of ways to write n^2 as 4^k*(m^2+1) + x^2 + y^2, where m is 1 or 2, and k,x,y are nonnegative integers with x <= y.

Source: https://oeis.org/A300510
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A300510 (Zhi-Wei Sun, Mar 07 2018): a(n) > 0 for all n
> 1; in other words, for any integer n > 1 there is a nonnegative integer k such that either n^2 -
2*4^k or n^2 - 5*4^k can be written as the sum of two squares. Moreover, a(n) = 1 only for n = 2^k
with k > 0.

Conventions:
* The sequence has offset 1 (data 0, 1, 2, 1, 3, 3, 3, 1, 4, 4, 5, 3, ...). `a n` is the number of
  quadruples (m, k, x, y) of natural numbers with m equal to 1 or 2, x <= y and n^2 = 4^k*(m^2+1)
  + x^2 + y^2, exactly as in the OEIS name.
* The positivity part is stated for n > 1 and the only-if part for every n >= 1 (the offset). The
  `in other words` clause is the entry's own restatement of a(n) > 0.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a300510

/-- The condition in the name of A300510 on a tuple, for a given n. -/
def P (n : ℕ) (m k x y : ℕ) : Prop :=
  (m = 1 ∨ m = 2) ∧ x ≤ y ∧ 4 ^ k * (m ^ 2 + 1) + x ^ 2 + y ^ 2 = n ^ 2

/-- A300510: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2.1 t.2.2.2}

/-- The conjecture recorded in A300510. -/
theorem main : ∀ n : ℕ, 0 < n → ((1 < n → 0 < a n) ∧ (a n = 1 → ∃ k : ℕ, 0 < k ∧ n = 2 ^ k)) := by
  sorry

end OMA.S_oeis_a300510

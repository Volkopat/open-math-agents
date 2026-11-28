import Mathlib

/-!
# A303539: Number of ordered pairs (k, m) with 0 <= k <= m such that n - binomial(2*k,k) - binomial(2*m,m) can be written as the sum of two squares.

Source: https://oeis.org/A303539
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A303539 (Zhi-Wei Sun, Apr 25 2018): a(n) > 0 for all n
> 1.

Conventions:
* The sequence has offset 1 (data 0, 1, 2, 3, 2, 2, 3, 4, 3, 2, 3, 6, ...). `a n` is the number of
  ordered pairs (k, m) with 0 <= k <= m such that n - binomial(2*k,k) - binomial(2*m,m) can be
  written as the sum of two squares, exactly as in the OEIS name.
* binomial(2*k,k) is the central binomial coefficient `Nat.centralBinom k`. `n - binomial(2*k,k) -
  binomial(2*m,m) is a sum of two squares` (of integers, 0 allowed; in particular the difference
  is nonnegative) is written without subtraction as n = binomial(2*k,k) + binomial(2*m,m) + u^2 +
  v^2 for some natural numbers u, v.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a303539

/-- The condition in the name of A303539 on a tuple, for a given n. -/
def P (n : ℕ) (k m : ℕ) : Prop :=
  k ≤ m ∧ ∃ u v : ℕ, Nat.centralBinom k + Nat.centralBinom m + u ^ 2 + v ^ 2 = n

/-- A303539: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A303539. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a303539

import Mathlib

/-!
# A237127: Number of ways to write n = k + m (0 < k < m) with k and m terms of A072281.

Source: https://oeis.org/A237127
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A237127 (Zhi-Wei Sun, Feb 04 2014): a(n) > 0 for all n
> 11.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, ...). `a n` is the number of
  pairs (k, m) with 0 < k < m, n = k + m and k, m both terms of A072281 (numbers j such that
  phi(j) - 1 and phi(j) + 1 are twin primes), exactly as in the OEIS name.
* phi is the Euler totient function `Nat.totient`.
* For j > 0 the subtraction phi(j) - 1 is exact (phi(j) >= 1).
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a237127

/-- The condition in the name of A237127 on a tuple, for a given n. -/
def P (n : ℕ) (k m : ℕ) : Prop :=
  0 < k ∧ k < m ∧ k + m = n ∧ (Nat.totient k - 1).Prime ∧ (Nat.totient k + 1).Prime ∧
  (Nat.totient m - 1).Prime ∧ (Nat.totient m + 1).Prime

/-- A237127: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A237127. -/
theorem main : ∀ n : ℕ, 11 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a237127

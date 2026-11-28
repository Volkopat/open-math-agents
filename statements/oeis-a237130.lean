import Mathlib

/-!
# A237130: Number of ordered ways to write n = k + m with k > 0 and m > 0 such that both {3*k - 1, 3*k + 1} and {phi(m) - 1, phi(m) + 1} are twin prime pairs, where phi(.) is Euler's totient function.

Source: https://oeis.org/A237130
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A237130 (Zhi-Wei Sun, Feb 04 2014), part (i): a(n) > 0
for all n > 8.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 0, 1, 0, 2, 1, 3, 2, ...). `a n` is the number of
  pairs (k, m) with k > 0, m > 0, n = k + m and 3*k - 1, 3*k + 1, phi(m) - 1, phi(m) + 1 all prime
  (i.e. both {3*k - 1, 3*k + 1} and {phi(m) - 1, phi(m) + 1} twin prime pairs), exactly as in the
  OEIS name.
* phi is the Euler totient function `Nat.totient`.
* For k > 0 and m > 0 the subtractions 3*k - 1 and phi(m) - 1 are exact (phi(m) >= 1).
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a237130

/-- The condition in the name of A237130 on a tuple, for a given n. -/
def P (n : ℕ) (k m : ℕ) : Prop :=
  0 < k ∧ 0 < m ∧ k + m = n ∧ (3 * k - 1).Prime ∧ (3 * k + 1).Prime ∧
  (Nat.totient m - 1).Prime ∧ (Nat.totient m + 1).Prime

/-- A237130: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A237130. -/
theorem main : ∀ n : ℕ, 8 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a237130

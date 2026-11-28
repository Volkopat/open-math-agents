import Mathlib

/-!
# A263020: Number of ordered pairs (k, m) with k > 0 and m > 0 such that n = pi(k*(k+1)/2) + pi(m*(3*m-1)/2), where pi(x) denotes the number of primes not exceeding x.

Source: https://oeis.org/A263020
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A263020 (Zhi-Wei Sun, Oct 07 2015): a(n) > 0 for all n
> 1.

Conventions:
* The sequence has offset 1 (data 0, 1, 2, 1, 2, 2, 2, 3, 3, 1, 5, 2, ...). `a n` is the number of
  pairs (k, m) with k > 0, m > 0 and n = pi(k*(k+1)/2) + pi(m*(3*m-1)/2), exactly as in the OEIS
  name.
* pi(x) is `Nat.primeCounting x`, the number of primes not exceeding x.
* The divisions by 2 are exact, and 3*m - 1 is an exact subtraction for m > 0.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a263020

/-- The condition in the name of A263020 on a tuple, for a given n. -/
def P (n : ℕ) (k m : ℕ) : Prop :=
  0 < k ∧ 0 < m ∧
  Nat.primeCounting (k * (k + 1) / 2) + Nat.primeCounting (m * (3 * m - 1) / 2) = n

/-- A263020: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A263020. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a263020

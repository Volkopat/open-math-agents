import Mathlib

/-!
# A263107: Number of ordered pairs (k, m) with k > 0 and m > 0 such that n = pi(k^2/2) + pi(3*m^2/2), where pi(x) denotes the number of primes not exceeding x.

Source: https://oeis.org/A263107
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A263107 (Zhi-Wei Sun, Oct 09 2015): a(n) > 0 for all n
> 0.

Conventions:
* The sequence has offset 1 (data 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 3, ...). `a n` is the number of
  pairs (k, m) with k > 0, m > 0 and n = pi(k^2/2) + pi(3*m^2/2), exactly as in the OEIS name.
* pi(x) is `Nat.primeCounting x`, the number of primes not exceeding x. For a real x, pi(x) is the
  number of primes not exceeding x, which equals pi(floor(x)); so pi(k^2/2) and pi(3*m^2/2) are
  `Nat.primeCounting` of the natural-number (floor) quotients k^2/2 and 3*m^2/2.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a263107

/-- The condition in the name of A263107 on a tuple, for a given n. -/
def P (n : ℕ) (k m : ℕ) : Prop :=
  0 < k ∧ 0 < m ∧ Nat.primeCounting (k ^ 2 / 2) + Nat.primeCounting (3 * m ^ 2 / 2) = n

/-- A263107: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A263107. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a263107

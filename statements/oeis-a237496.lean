import Mathlib

/-!
# A237496: Number of ordered ways to write n = k + m (0 < k <= m) with pi(k) + pi(m) - 2 prime, where pi(.) is given by A000720.

Source: https://oeis.org/A237496
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A237496 (Zhi-Wei Sun, Feb 08 2014), part (i): a(n) > 0
for all n > 5.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 1, 2, 4, 4, 3, 2, 3, ...). `a n` is the number of
  pairs (k, m) of natural numbers with n = k + m, 0 < k <= m and pi(k) + pi(m) - 2 prime, exactly
  as in the OEIS name.
* pi(x) is `Nat.primeCounting x`, the number of primes not exceeding x.
* The subtraction of 2 is the truncated natural-number subtraction; when pi(k) + pi(m) < 2 the
  true value is negative and the truncated value is 0, and neither is prime, so the condition is
  unchanged.
* Only part (i) of the conjecture is formalized; part (ii) is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a237496

/-- The condition in the name of A237496 on a tuple, for a given n. -/
def P (n : ℕ) (k m : ℕ) : Prop :=
  k + m = n ∧ 0 < k ∧ k ≤ m ∧ (Nat.primeCounting k + Nat.primeCounting m - 2).Prime

/-- A237496: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A237496. -/
theorem main : ∀ n : ℕ, 5 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a237496

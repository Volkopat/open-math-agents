import Mathlib

/-!
# A239617: Number of ways to write 2*n = p + q with p, q and pi(2*p) - pi(p) all prime, where pi(x) denotes the number of primes not exceeding x.

Source: https://oeis.org/A239617
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A239617 (Zhi-Wei Sun, Mar 22 2014), part (i): a(n) > 0
for all n > 4.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 1, 1, 2, 2, 3, 2, 1, 3, ...). `a n` is the number of
  pairs (p, q) of natural numbers with 2*n = p + q and p, q and pi(2*p) - pi(p) all prime, exactly
  as in the OEIS name.
* pi(x) is `Nat.primeCounting x`, the number of primes not exceeding x.
* The natural-number subtraction is exact since pi(2*p) >= pi(p).
* Only part (i) of the conjecture is formalized; part (ii) is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a239617

/-- The condition in the name of A239617 on a tuple, for a given n. -/
def P (n : ℕ) (p q : ℕ) : Prop :=
  p + q = 2 * n ∧ p.Prime ∧ q.Prime ∧ (Nat.primeCounting (2 * p) - Nat.primeCounting p).Prime

/-- A239617: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A239617. -/
theorem main : ∀ n : ℕ, 4 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a239617

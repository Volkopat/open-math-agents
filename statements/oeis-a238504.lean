import Mathlib

/-!
# A238504: Number of primes p <= n with pi(pi((p-1)*n)) prime, where pi(x) denotes the number of primes not exceeding x.

Source: https://oeis.org/A238504
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A238504 (Zhi-Wei Sun, Mar 06 2014), part (i): a(n) > 0
for all n > 2.

Conventions:
* The sequence has offset 1 (data 0, 0, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, ...). `a n` is the number of
  primes p <= n with pi(pi((p-1)*n)) prime, exactly as in the OEIS name.
* pi(x) is `Nat.primeCounting x`, the number of primes not exceeding x.
* p - 1 is an exact natural-number subtraction since p is prime.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a238504

/-- The condition in the name of A238504 on a tuple, for a given n. -/
def P (n : ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ p ≤ n ∧ (Nat.primeCounting (Nat.primeCounting ((p - 1) * n))).Prime

/-- A238504: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A238504. -/
theorem main : ∀ n : ℕ, 2 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a238504

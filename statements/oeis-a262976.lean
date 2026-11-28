import Mathlib

/-!
# A262976: Number of ordered ways to write n as 2^x + y^2 + pi(z^2) with x >= 0, y >= 0 and z > 0, where pi(m) denotes the number of primes not exceeding m.

Source: https://oeis.org/A262976
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A262976 (Zhi-Wei Sun, Oct 05 2015), part (i): a(n) > 0
for all n > 0.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 3, 4, 4, 4, 6, 4, 6, 6, 7, ...). `a n` is the number of
  triples (x, y, z) of natural numbers with z > 0 and n = 2^x + y^2 + pi(z^2), exactly as in the
  OEIS name.
* pi(m) is `Nat.primeCounting m`, the number of primes not exceeding m.
* Only part (i) of the conjecture is formalized; part (ii) is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a262976

/-- The condition in the name of A262976 on a tuple, for a given n. -/
def P (n : ℕ) (x y z : ℕ) : Prop :=
  0 < z ∧ 2 ^ x + y ^ 2 + Nat.primeCounting (z ^ 2) = n

/-- A262976: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A262976. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a262976

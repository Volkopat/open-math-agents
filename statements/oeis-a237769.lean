import Mathlib

/-!
# A237769: Number of primes p < n with pi(n-p) - 1 and pi(n-p) + 1 both prime, where pi(.) is given by A000720.

Source: https://oeis.org/A237769
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A237769 (Zhi-Wei Sun, Feb 13 2014), part (i): a(n) > 0
for all n > 8, and a(n) = 1 only for n = 9, 34, 35.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 3, ...). `a n` is the number of
  primes p < n with pi(n-p) - 1 and pi(n-p) + 1 both prime, exactly as in the OEIS name.
* pi(x) is `Nat.primeCounting x`, the number of primes not exceeding x.
* Natural-number subtraction is truncated: where the true value would be negative the truncated
  value is 0, and neither is prime, so the condition is unchanged.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a237769

/-- The condition in the name of A237769 on a tuple, for a given n. -/
def P (n : ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ p < n ∧ (Nat.primeCounting (n - p) - 1).Prime ∧
  (Nat.primeCounting (n - p) + 1).Prime

/-- A237769: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A237769. -/
theorem main : ∀ n : ℕ, 0 < n → ((8 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({9, 34, 35} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a237769

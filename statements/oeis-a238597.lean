import Mathlib

/-!
# A238597: Number of primes p < 2*n with 2*pi(p) + 1 and p*(2n-1) - 2 both prime, where pi(.) is given by A000720.

Source: https://oeis.org/A238597
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A238597 (Zhi-Wei Sun, Mar 01 2014), part (i): a(n) > 0
for all n > 1, and a(n) = 1 for no n > 195.

Conventions:
* The sequence has offset 1 (data 0, 1, 2, 1, 1, 2, 2, 4, 1, 1, 5, 3, ...). `a n` is the number of
  primes p < 2*n with 2*pi(p) + 1 and p*(2n-1) - 2 both prime, exactly as in the OEIS name.
* pi(x) is `Nat.primeCounting x`, the number of primes not exceeding x.
* The subtractions are exact for n >= 1 and p prime (p*(2n-1) >= 2).
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a238597

/-- The condition in the name of A238597 on a tuple, for a given n. -/
def P (n : ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ p < 2 * n ∧ (2 * Nat.primeCounting p + 1).Prime ∧ (p * (2 * n - 1) - 2).Prime

/-- A238597: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A238597. -/
theorem main : ∀ n : ℕ, 1 < n → (0 < a n ∧ (195 < n → a n ≠ 1)) := by
  sorry

end OMA.S_oeis_a238597

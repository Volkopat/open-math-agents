import Mathlib

/-!
# A238776: Primes p with prime(p) - p + 1 and prime(q) - q + 1 both prime, where q = prime(2*pi(p)+1) with pi(.) given by A000720.

Source: https://oeis.org/A238776
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A238776 (Zhi-Wei Sun, Mar 05 2014): The sequence has
infinitely many terms.

Conventions:
* The sequence has offset 1 (data 2, 5, 7, 13, 31, 41, 43, 83, 109, 151, 211, 281, ...).
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* pi(x) is `Nat.primeCounting x`, the number of primes not exceeding x.
* With q = prime(2*pi(p) + 1), the two conditions are that prime(p) - p + 1 and prime(q) - q + 1
  are prime; the subtractions are exact since prime(k) > k.
* `The sequence is infinite` / `has infinitely many terms` is rendered as `Set.Infinite` of the
  set of all numbers with the defining property of the OEIS name.
-/

namespace OMA.S_oeis_a238776

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The conjecture recorded in A238776. -/
theorem main : Set.Infinite {p : ℕ | p.Prime ∧ (pr p - p + 1).Prime ∧
    (pr (pr (2 * Nat.primeCounting p + 1)) - pr (2 * Nat.primeCounting p + 1) + 1).Prime} := by
  sorry

end OMA.S_oeis_a238776

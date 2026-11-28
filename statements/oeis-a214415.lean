import Mathlib

/-!
# A214415: Numbers n such that prevprime(2^n) AND nextprime(2^n) = 1, where AND is the bitwise AND operator.

Source: https://oeis.org/A214415
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A214415 (Alex Ratushnyak, Aug 07 2012): the sequence is
infinite.

Conventions:
* The sequence has offset 0 (data 2, 4, 6, 8, 12, 15, 16, 23, 25, 30, 37, 53, ...).
* prevprime(m) is the largest prime smaller than m and nextprime(m) is the smallest prime larger
  than m; they are described by their defining properties (p is prime, p < 2^n, and every prime
  below 2^n is at most p; q is prime, q > 2^n, and every prime above 2^n is at least q). For n = 0
  and n = 1 there is no prime below 2^n, so these n are not in the set, in agreement with the
  data, which starts 2, 4, 6, 8, 12.
* AND is the bitwise and of natural numbers, `Nat.land` (notation `&&&`).
* `The sequence is infinite` / `has infinitely many terms` is rendered as `Set.Infinite` of the
  set of all numbers with the defining property of the OEIS name.
-/

namespace OMA.S_oeis_a214415

/-- The conjecture recorded in A214415. -/
theorem main : Set.Infinite {n : ℕ | ∃ p q : ℕ,
    p.Prime ∧ p < 2 ^ n ∧ (∀ r : ℕ, r.Prime → r < 2 ^ n → r ≤ p) ∧
    q.Prime ∧ 2 ^ n < q ∧ (∀ r : ℕ, r.Prime → 2 ^ n < r → q ≤ r) ∧ p &&& q = 1} := by
  sorry

end OMA.S_oeis_a214415

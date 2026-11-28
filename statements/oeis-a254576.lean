import Mathlib

/-!
# A254576: Primes p such that phi(p-2) divides p-1 where phi is Euler's totient function (A000010).

Source: https://oeis.org/A254576
Credit: @azmiozgen

Conjecture (from the entry): the terms are also the primes p such that 2*phi(p-2) = p-1
(i.e., the primes in A232720).

Formalization notes:
* Stated for every prime p: phi(p-2) divides p-1 if and only if 2*phi(p-2) = p-1.
* For p = 2, Mathlib's `Nat.totient 0 = 0` makes both sides false, matching the entry (2 is not
  a term).
* Controls (computed): the primes below 70000 with phi(p-2) | p-1 are 3, 5, 17, 257, 65537;
  in particular the primes below 2000 with phi(p-2) | p-1 are 3, 5, 17, 257, as in the entry.
-/

namespace OMA.S_oeis_a254576

/-- The terms of A254576 are exactly the primes with `2 φ(p-2) = p-1`. -/
theorem main :
    ∀ p : ℕ, p.Prime → (Nat.totient (p - 2) ∣ p - 1 ↔ 2 * Nat.totient (p - 2) = p - 1) := by
  sorry

end OMA.S_oeis_a254576

import Mathlib

/-!
# A258454: Numbers n such that phi(n) = 2*phi(n-2).

Source: https://oeis.org/A258454
Credit: @azmiozgen

Conjecture (from the entry): a prime p is in the sequence iff p is a Fermat prime (A019434).

Formalization notes:
* Fermat primes are the primes of the form 2^(2^k) + 1 with k ≥ 0 (A019434: 3, 5, 17, 257, 65537).
* Stated for every prime p: phi(p) = 2*phi(p-2) if and only if p = 2^(2^k) + 1 for some k.
  For p = 2, Mathlib's `Nat.totient 0 = 0` gives phi(2) = 1 ≠ 0, and 2 is not a Fermat prime.
* Controls (computed): the terms up to 23500 are 3, 4, 5, 8, 17, 32, 257, 512, 527, 992, 1952, 2522, 5252,
  6512, 7412, 10376, 23432, as in the entry; the primes among them are 3, 5, 17, 257.
-/

namespace OMA.S_oeis_a258454

/-- A prime `p` satisfies `φ(p) = 2 φ(p-2)` exactly when it is a Fermat prime. -/
theorem main :
    ∀ p : ℕ, p.Prime →
      (Nat.totient p = 2 * Nat.totient (p - 2) ↔ ∃ k : ℕ, p = 2 ^ 2 ^ k + 1) := by
  sorry

end OMA.S_oeis_a258454

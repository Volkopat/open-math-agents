import Mathlib

/-!
# A249760: Numbers k such that k+1 and sigma(k) are both primes.

Source: https://oeis.org/A249760
Credit: @ShoQo

Conjectures: "(1) sequence is finite; (2) a(n) + 1 is a Fermat prime (A019434); (3) sigma(a(n))
is a Mersenne prime (A000668)." The entry adds: "Subsequence of A023194, and by a comment in that
entry it follows that each term is a prime power. From that conjectures (2) and (3) above easily
follow."

Formalization notes:
* A term is a k with `(k + 1).Prime` and `(sigma 1 k).Prime`, where `sigma 1` is the sum of divisors.
* Conjectures (2) and (3), the ones the entry establishes, are stated together; (1) is open and
  not stated.
* (2): k + 1 is a Fermat prime, i.e. a prime of the form `Nat.fermatNumber m = 2^(2^m) + 1`.
* (3): σ(k) is a Mersenne prime, i.e. a prime of the form `mersenne q = 2^q - 1`.
-/

namespace OMA.S_oeis_a249760

open ArithmeticFunction

theorem main : ∀ k : ℕ, (k + 1).Prime → (sigma 1 k).Prime →
    (∃ m : ℕ, k + 1 = Nat.fermatNumber m) ∧ (∃ q : ℕ, sigma 1 k = mersenne q) := by
  sorry

end OMA.S_oeis_a249760

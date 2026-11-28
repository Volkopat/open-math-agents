import Mathlib

/-!
# A246133: a(n) = (binomial(2n, n) - 2) mod n^3.

Source: https://oeis.org/A246133
Credit: @Pampasgras

The OEIS comment: the numbers binomial(2n, n) - 2 mod n^3 are 0 whenever n is a prime greater than 3
(Wolstenholme's theorem). No composite number n with a(n) = 0 was found up to n = 431500
(conjecture: there are none, and a(n) = 0 for n > 3 is a deterministic primality test).

Translation notes.
* `a n` is the OEIS sequence, offset 1. `Nat.centralBinom n` is binomial(2n, n). For n ≥ 1 it is at
  least 2, so the natural-number subtraction `Nat.centralBinom n - 2` does not truncate and `a n` is
  exactly the OEIS value (checked against the %S data, n = 1..53).
* `main` states the conjecture as the primality test: for every n > 3, a(n) = 0 if and only if n is
  prime. Every composite number is greater than 3, so the direction a(n) = 0 → n prime is exactly the
  claim that no composite n has a(n) = 0. The other direction is Wolstenholme's theorem (the %F line,
  a(p) = 0 for primes p > 3); it is included because the conjecture asserts the primality test, and
  it is a known result.
* Checked numerically: the equivalence holds for every n with 3 < n ≤ 4000.
-/

namespace OMA.S_oeis_a246133

/-- A246133: a(n) = (binomial(2n, n) - 2) mod n^3. -/
def a (n : ℕ) : ℕ := (Nat.centralBinom n - 2) % n ^ 3

/-- For n > 3, a(n) = 0 exactly when n is prime: no composite n has n^3 ∣ binomial(2n, n) - 2. -/
theorem main : ∀ n : ℕ, 3 < n → (a n = 0 ↔ n.Prime) := by
  sorry

end OMA.S_oeis_a246133

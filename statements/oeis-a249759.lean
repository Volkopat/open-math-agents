import Mathlib

/-!
# A249759: Primes p such that sigma(p-1) is a prime q.

Source: https://oeis.org/A249759
Credit: @luciusacarr

Data: 3, 5, 17, 65537.

The entry's comments record these conjectures. `main` states all of them, as a conjunction, in
the order the source gives them.

Conjectures (main list):
1) the sequence is finite;
2) the sequence is a subsequence of A019434 (Fermat primes);
3) the sequence consists of Fermat primes p such that sigma(p-1) is a Mersenne prime;
4) a(n) = (A249761(n) + 3)/2.

Further conjecture: 3 is the only number n such that n and sigma(n+1) are both prime.

From Jaroslav Krizek, Nov 27 2016: the sequence is a subsequence of A256438 (numbers m with
sigma(sigma(m-1)) = 2*(m-1)) and of A278741 (odd numbers k such that tau(k-1) is a prime); the
sequence is also the set of primes p such that tau(p-1) is a prime.

Reading of the source:
* `S` is the set of terms of A249759: primes `p` with `sigma(p-1)` prime.
* A249761 is the set of primes `q` such that `sigma(p-1) = q` for some prime `p`.
* A019434 (Fermat primes) are the primes of the form `2^(2^k) + 1` (`Nat.fermatNumber k`);
  A000668 (Mersenne primes) are the primes of the form `2^m - 1` (`mersenne m`).
* Conjecture 3 is read as the equality of `S` with the set of Fermat primes `p` such that
  `sigma(p-1)` is a Mersenne prime.
* Conjecture 4 compares the n-th terms of the two sequences (both listed in increasing order,
  indexed from 0 here) through `Nat.nth`. If one sequence has fewer terms than the other, `Nat.nth`
  returns 0 past its end and the equation fails, so the statement also says both have the same
  number of terms; `2 * 0 - 3 = 0` in ℕ makes the indices past both ends harmless.
* `tau(m)` is the number of divisors of `m`, `(Nat.divisors m).card`.
-/

namespace OMA.S_oeis_a249759

/-- The terms of A249759: primes `p` such that `sigma(p-1)` is prime. -/
def S : Set ℕ := {p | p.Prime ∧ (ArithmeticFunction.sigma 1 (p - 1)).Prime}

/-- The terms of A249761: primes `q` such that `sigma(p-1) = q` for some prime `p`. -/
def A249761 : Set ℕ :=
  {q | q.Prime ∧ ∃ p : ℕ, p.Prime ∧ ArithmeticFunction.sigma 1 (p - 1) = q}

/-- Fermat primes (A019434): primes of the form `2^(2^k) + 1`. -/
def IsFermatPrime (p : ℕ) : Prop := p.Prime ∧ ∃ k : ℕ, p = Nat.fermatNumber k

/-- Mersenne primes (A000668): primes of the form `2^m - 1`. -/
def IsMersennePrime (q : ℕ) : Prop := q.Prime ∧ ∃ m : ℕ, q = mersenne m

theorem main :
    -- Conjecture 1: the sequence is finite.
    S.Finite ∧
    -- Conjecture 2: every term is a Fermat prime.
    (∀ p ∈ S, IsFermatPrime p) ∧
    -- Conjecture 3: the terms are exactly the Fermat primes p with sigma(p-1) a Mersenne prime.
    S = {p | IsFermatPrime p ∧ IsMersennePrime (ArithmeticFunction.sigma 1 (p - 1))} ∧
    -- Conjecture 4: a(n) = (A249761(n) + 3)/2, i.e. A249761(n) = 2 a(n) - 3.
    (∀ n : ℕ, Nat.nth (· ∈ A249761) n = 2 * Nat.nth (· ∈ S) n - 3) ∧
    -- 3 is the only number n such that n and sigma(n+1) are both prime.
    (∀ n : ℕ, (n.Prime ∧ (ArithmeticFunction.sigma 1 (n + 1)).Prime) ↔ n = 3) ∧
    -- Krizek: subsequence of A256438, sigma(sigma(m-1)) = 2*(m-1).
    (∀ p ∈ S, ArithmeticFunction.sigma 1 (ArithmeticFunction.sigma 1 (p - 1)) = 2 * (p - 1)) ∧
    -- Krizek: subsequence of A278741, odd numbers k with tau(k-1) prime.
    (∀ p ∈ S, Odd p ∧ (Nat.divisors (p - 1)).card.Prime) ∧
    -- Krizek: the terms are also the primes p such that tau(p-1) is a prime.
    S = {p | p.Prime ∧ (Nat.divisors (p - 1)).card.Prime} := by
  sorry

end OMA.S_oeis_a249759

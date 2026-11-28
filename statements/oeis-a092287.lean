import Mathlib

/-!
# OEIS A092287: the prime factorization of Prod gcd(j,k) over a square and over a rectangle

Source: https://oeis.org/A092287 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (N. J. A. Sloane, based on a suggestion from Leroy Quet, Feb 03 2004), offset 0: a(n) =
Product_{j=1..n} Product_{k=1..n} gcd(j,k). Comment (Peter Bala, Apr 16 2007): Conjecture: Let p
be a prime and let ordp(n,p) denote the exponent of the highest power of p that divides n. For
example, ordp(48,2)=4, since 48=3*(2^4). Then we conjecture that the prime factorization of a(n)
is given by the formula: ordp(a(n),p) = (floor(n/p))^2 + (floor(n/p^2))^2 + (floor(n/p^3))^2 +
.... Comment (Charles R Greathouse IV, Apr 02 2013): The conjecture is correct. Comment (Andrey
Kaydalov, Mar 11 2019): Conjecture: For a product over a rectangle, f(n,m) = Product_{j=1..n}
Product_{k=1..m} gcd(j,k), a factorization similar to the one given above for the square case
takes place: ordp(f(n,m),p) = floor(n/p)*floor(m/p) + floor(n/p^2)*floor(m/p^2) + .... By way of
directly computing the values of f(n,m), it can be verified that the conjecture holds at least for
all 1 <= m <= n <= 200.

Formalization notes:
* ordp(x,p) is the p-adic valuation `padicValNat p x`, and a(n) = f(n,n).
* The sums are finite: floor(n/p^i) = 0 as soon as p^i > n, in particular for every i > n since
  p^i >= 2^i > i. So both sums are taken over i = 1, ..., n, which contains every nonzero term.
* `main` is the conjunction of both conjectures, the square case and the rectangle case, for
  every prime p and all n, m >= 0 (n = 0 or m = 0 gives the empty product 1, and both sides are 0).
* Controls: the definitions give a(0..9) = 1, 1, 2, 6, 96, 480, 414720, 2903040, 5945425920,
  4334215495680, as in the entry.
-/

namespace OMA.S_oeis_a092287

open Finset

/-- f(n, m) = prod_{j=1..n} prod_{k=1..m} gcd(j, k). -/
def f (n m : ℕ) : ℕ := ∏ j ∈ Icc 1 n, ∏ k ∈ Icc 1 m, Nat.gcd j k

/-- Bala's square case and Kaydalov's rectangle case, for every prime p. -/
theorem main :
    (∀ p : ℕ, p.Prime → ∀ n : ℕ,
      padicValNat p (f n n) = ∑ i ∈ Finset.Icc 1 n, (n / p ^ i) ^ 2) ∧
    (∀ p : ℕ, p.Prime → ∀ n m : ℕ,
      padicValNat p (f n m) = ∑ i ∈ Finset.Icc 1 n, (n / p ^ i) * (m / p ^ i)) := by
  sorry

end OMA.S_oeis_a092287

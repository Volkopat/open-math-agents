import Mathlib

/-!
# A366562: a(n) = Sum_{k=1..n} A366561(n,k)*A023900(k)/n.

Source: https://oeis.org/A366562 (conjecture in the entry, and conjectures of Ridouane Oudra,
Jun 17 2025).
Credit: @esracummings31-blip

A366561(n,k) = Sum_{y=1..n} Sum_{x=1..n} [gcd(x^2 - y^2, n) = k], and A023900(k) =
Product_{p | k} (1 - p) (the Dirichlet inverse of sigma).

Conjectures, for n >= 1:
  a(n) = [n odd] * phi(n) * (-1)^omega(n), where omega = A001221 is the number of distinct primes;
  a(n) = (-1)^omega(n) * (2*phi(n) - phi(2*n));
  a(n) = (-1)^omega(n) * Sum_{d|n} mu(n/d) * A000265(d), where A000265(d) is the odd part of d;
  a(2*n) = 0;
  a(2*n+1) = A076479(2*n+1) * phi(2*n+1), where A076479(m) = (-1)^omega(m).
-/

namespace OMA.S_oeis_a366562

open scoped ArithmeticFunction.Moebius

/-- A366561: the number of pairs `1 ≤ x, y ≤ n` with `gcd(x^2 - y^2, n) = k`. -/
def T (n k : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
    (fun p => Int.gcd ((p.1 : ℤ) ^ 2 - (p.2 : ℤ) ^ 2) n = k)).card

/-- A023900: the product of `1 - p` over the primes `p` dividing `k`. -/
def A023900 (k : ℕ) : ℤ := ∏ p ∈ k.primeFactors, (1 - (p : ℤ))

/-- A366562. -/
def a (n : ℕ) : ℚ := (∑ k ∈ Finset.Icc 1 n, (T n k : ℚ) * (A023900 k : ℚ)) / n

/-- A000265: the odd part of `d`. -/
def oddPart (d : ℕ) : ℕ := d / 2 ^ d.factorization 2

theorem main :
    (∀ n, 1 ≤ n → a n = if n % 2 = 1 then (n.totient : ℚ) * (-1) ^ n.primeFactors.card else 0) ∧
    (∀ n, 1 ≤ n →
      a n = (-1) ^ n.primeFactors.card * (2 * (n.totient : ℚ) - ((2 * n).totient : ℚ))) ∧
    (∀ n, 1 ≤ n → a n = (-1) ^ n.primeFactors.card *
      ∑ d ∈ n.divisors, (μ (n / d) : ℚ) * (oddPart d : ℚ)) ∧
    (∀ n, 1 ≤ n → a (2 * n) = 0) ∧
    (∀ n, a (2 * n + 1) = (-1) ^ (2 * n + 1).primeFactors.card * ((2 * n + 1).totient : ℚ)) := by
  sorry

end OMA.S_oeis_a366562

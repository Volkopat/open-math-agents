import Mathlib

/-!
OEIS A347293: Triangle read by rows: T(n, k) = Sum_{i=1..n} gcd(1 + (i-1)*(k-1), n)
for 1 <= k <= n.

Conjecture (from the OEIS entry): Let f be an arbitrary arithmetic function and
a(f; n) = Sum_{i=1..n, k=1..n} f(gcd(1 + (i-1)*(k-1), n)). Then
  (1) a(f; n) = dc(A000290, A000010 * dc(A008683, f))(n), where dc is Dirichlet convolution
      and * is the pointwise product, i.e.
      a(f; n) = Sum_{d|n} (n/d)^2 * phi(d) * Sum_{e|d} mu(e) * f(d/e);
  (2) if f is multiplicative, then a(f; n) is multiplicative;
  (3) the row sums of the triangle equal the Dirichlet convolution of A000290 (n^2) and
      A127473 (phi(n)^2).
Arithmetic functions are taken complex-valued.
-/

namespace OMA.S_oeis_a347293

theorem main :
    (∀ f : ℕ → ℂ, ∀ n : ℕ, 1 ≤ n →
      ∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, f (Nat.gcd (1 + (i - 1) * (k - 1)) n) =
        ∑ d ∈ n.divisors, (((n / d) ^ 2 : ℕ) : ℂ) *
          ((Nat.totient d : ℂ) *
            ∑ e ∈ d.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) * f (d / e))) ∧
    (∀ f : ℕ → ℂ, (f 1 = 1 ∧ ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) →
      (∑ i ∈ Finset.Icc 1 1, ∑ k ∈ Finset.Icc 1 1, f (Nat.gcd (1 + (i - 1) * (k - 1)) 1) = 1) ∧
      ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → Nat.Coprime m n →
        ∑ i ∈ Finset.Icc 1 (m * n), ∑ k ∈ Finset.Icc 1 (m * n),
            f (Nat.gcd (1 + (i - 1) * (k - 1)) (m * n)) =
          (∑ i ∈ Finset.Icc 1 m, ∑ k ∈ Finset.Icc 1 m, f (Nat.gcd (1 + (i - 1) * (k - 1)) m)) *
          (∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, f (Nat.gcd (1 + (i - 1) * (k - 1)) n))) ∧
    (∀ n : ℕ, 1 ≤ n →
      ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Icc 1 n, Nat.gcd (1 + (i - 1) * (k - 1)) n =
        ∑ d ∈ n.divisors, (n / d) ^ 2 * (Nat.totient d) ^ 2) := by
  sorry

end OMA.S_oeis_a347293

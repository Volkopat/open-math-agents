import Mathlib

/-!
# A333564: a(n) = [x^n] ( c(x)/c(-x) )^n, where c(x) = (1 - sqrt( 1 - 4*x))/(2*x) is the o.g.f. of the Catalan numbers A000108.

Source: https://oeis.org/A333564
Credit: @azmiozgen

Conjecture (Peter Bala, from the entry): a(n) satisfies the stronger congruences
a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k)) for prime p >= 3 and positive integers n and k.

Formalization notes:
* The entry gives a(n) = 2^n * Sum_{k = 0..n-1} (-1)^(n-1+k)*binomial(n+k,k) (= 2^n A014300(n));
  this closed form is used as the definition (offset 1), computed in ℤ.
* The congruence is stated in ℤ as divisibility of the difference by p^(3k).
* Controls (computed): a(1..9) = 2, 8, 56, 384, 2752, 20096, 148864, 1114112, 8403968, as in the
  entry; the congruence holds for p = 3, 5, 7 and n = 1, 2 with k = 1.
-/

namespace OMA.S_oeis_a333564

open PowerSeries

/-- A333564(n) = 2^n ∑_{k<n} (-1)^(n-1+k) C(n+k,k). -/
def a (n : ℕ) : ℤ :=
  2 ^ n * ∑ k ∈ Finset.range n, (-1 : ℤ) ^ (n - 1 + k) * ((n + k).choose k : ℤ)

/-- The conjecture of the entry. -/
theorem main :
    ∀ p : ℕ, p.Prime → 3 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      ((p : ℤ) ^ (3 * k) ∣ a (n * p ^ k) - a (n * p ^ (k - 1))) := by
  sorry

end OMA.S_oeis_a333564

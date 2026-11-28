import Mathlib

/-!
# A374606: a(n) = Sum_{k = 0..n} binomial(n, k)^2*binomial(n+k, k)*binomial(3*n+2*k+1, n).

Source: https://oeis.org/A374606
Credit: @azmiozgen

Conjecture (Peter Bala, from the entry): for prime p, a(n) is divisible by p^3 for integer n in the
interval [(1/3)*(2*p + (p/3)), p - 1], where (p/3) denotes the Legendre symbol. (The entry's more
general conjecture for other m is not stated here.)

Formalization notes:
* (p/3) is the Legendre (Jacobi) symbol, `jacobiSym p 3` ∈ {-1, 0, 1}. The lower bound
  n ≥ (2p + (p/3))/3 is stated without division as 3n ≥ 2p + (p/3) in ℤ.
* Controls (computed): a(0..5) = 1, 16, 783, 52000, 3984625, 331782528, as in the entry; the
  divisibility holds for all primes p < 45 and all n in the interval.
-/

namespace OMA.S_oeis_a374606

/-- A374606(n). -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ 2 * (n + k).choose k * (3 * n + 2 * k + 1).choose n

/-- Bala's divisibility conjecture. -/
theorem main :
    ∀ p n : ℕ, p.Prime → 2 * (p : ℤ) + jacobiSym p 3 ≤ 3 * n → n ≤ p - 1 → p ^ 3 ∣ a n := by
  sorry

end OMA.S_oeis_a374606

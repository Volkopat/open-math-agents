import Mathlib

/-!
# A245926: Expansion of g.f. sqrt( (1-x + sqrt(1-14*x+x^2)) / (2*(1-14*x+x^2)) )

Source: https://oeis.org/A245926

Offset 0; a(0..) = 1, 5, 51, 587, 7123, 89055, ...
Peter Bala (May 03 2022) gives the known formula
a(n) = (1/C(2n,n)) * Sum_{k=0..n} (-1)^(n+k) C(n,k) C(n+k,k) C(2n+2k,n+k)
and states: Calculation suggests that the supercongruences
a(n*p^k) == a(n*p^(k-1)) (mod p^(2*k)) hold for primes p >= 5 and positive
integers n and k.  This supercongruence is the target.  (The Gauss congruences
in the same comment are conditional on a separate conjecture and are not stated.)

Formalized: a(n) is defined in ℤ by Bala's sum, divided by C(2n,n) with integer
division (the division is exact; checked numerically, terms match the data).
The congruence is stated as Int.ModEq modulo p^(2k), for all primes p ≥ 5 and
all n ≥ 1, k ≥ 1.
-/

namespace OMA.S_oeis_a245926

/-- a(n) = (1/C(2n,n)) * Sum_{k=0..n} (-1)^(n+k) C(n,k) C(n+k,k) C(2n+2k,n+k). -/
def a (n : ℕ) : ℤ :=
  (∑ k ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ (n + k) * (Nat.choose n k : ℤ) * (Nat.choose (n + k) k : ℤ)
        * (Nat.choose (2 * n + 2 * k) (n + k) : ℤ)) / (Nat.choose (2 * n) n : ℤ)

theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD ((p : ℤ) ^ (2 * k))] := by
  sorry

end OMA.S_oeis_a245926

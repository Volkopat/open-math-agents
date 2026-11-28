import Mathlib

/-!
# A357958: a(n) = 5*A005259(n) + 14*A005258(n-1).

Source: https://oeis.org/A357958
Credit: @ShoQo

The entry conjectures, for a(n): "1) a(p) == a(1) (mod p^5) for all primes p >= 5 (checked up
to p = 271). 2) a(p^r) == a(p^(r-1)) ( mod p^(3*r+3) ) for r >= 2 and for all primes p >= 3."
It continues: "There is also a product version of these conjectures: 3) the sequence {u(n): n>= 1}
defined by u(n) = A005259(n)^25 * A005258(n-1)^14 conjecturally satisfies the congruences in 1)
and 2) above." A later comment reports that for u the congruence 2) fails at p = 3.

Formalization notes:
* This file states conjecture 3), the product version: both congruences 1) and 2) for u.
  Conjectures 1) and 2) for a(n) itself are separate claims and are not stated here.
* A005259(n) = Sum_{k=0..n} C(n,k)^2 C(n+k,k)^2 and A005258(n) = Sum_{k=0..n} C(n,k)^2 C(n+k,k)
  are the Apéry numbers (offset 0). u(n) is used for n ≥ 1, so A005258(n-1) is always defined.
* "x == y (mod m)" is written m ∣ x - y over ℤ.
-/

namespace OMA.S_oeis_a357958

open Finset

/-- A005259: Apéry numbers for ζ(3). -/
def A005259 (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), n.choose k ^ 2 * (n + k).choose k ^ 2

/-- A005258: Apéry numbers for ζ(2). -/
def A005258 (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), n.choose k ^ 2 * (n + k).choose k

/-- u(n) = A005259(n)^25 * A005258(n-1)^14. -/
def u (n : ℕ) : ℤ := (A005259 n : ℤ) ^ 25 * (A005258 (n - 1) : ℤ) ^ 14

/-- Conjecture 3): u satisfies the congruences 1) and 2). -/
theorem main :
    (∀ p : ℕ, p.Prime → 5 ≤ p → (p : ℤ) ^ 5 ∣ u p - u 1) ∧
    (∀ p r : ℕ, p.Prime → 3 ≤ p → 2 ≤ r → (p : ℤ) ^ (3 * r + 3) ∣ u (p ^ r) - u (p ^ (r - 1))) := by
  sorry

end OMA.S_oeis_a357958

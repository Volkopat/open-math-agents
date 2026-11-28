import Mathlib

/-!
# A246541: Squares of P_(n+2)-rough numbers modulo the (n+1)-th primorial.

Source: https://oeis.org/A246541
Credit: @bnb9001

Take the squares of all P_(n+2)-rough numbers less than the (n+1)-th primorial and reduce each
modulo the (n+1)-th primorial; a(n) is the number of different results (offset 1: 1, 2, 6, 30,
...). The (n+1)-th primorial is the product of the first n+1 primes. A number is P_(n+2)-rough
when it has no prime factor smaller than prime(n+2), so, as the entry notes, the P_(n+2)-rough
numbers below the (n+1)-th primorial are exactly its reduced residue system: the `x` below it
that are coprime to it.

Conjecture (Jon E. Schoenfield, 2019): a(n) = (1/2^n) * Product_{j=1..n} (prime(j+1) - 1). Bert
Dobbelaere notes that the conjecture is true. With Mathlib's 0-indexed `Nat.nth Nat.Prime`,
prime(j+1) is `Nat.nth Nat.Prime j`.
-/

namespace OMA.S_oeis_a246541

open Finset

/-- The product of the first `k` primes (so the `(n+1)`-th primorial is `firstPrimesProd (n+1)`). -/
noncomputable def firstPrimesProd (k : ℕ) : ℕ := ∏ i ∈ range k, Nat.nth Nat.Prime i

/-- A246541: the number of distinct values of `x ^ 2 mod P` over the `x < P` coprime to `P`,
where `P` is the `(n+1)`-th primorial. -/
noncomputable def a (n : ℕ) : ℕ :=
  (((range (firstPrimesProd (n + 1))).filter (fun x => Nat.Coprime x (firstPrimesProd (n + 1)))).image
    (fun x => x ^ 2 % firstPrimesProd (n + 1))).card

/-- For every `n ≥ 1`, `a n = (∏_{j=1..n} (prime(j+1) - 1)) / 2^n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = (∏ j ∈ Icc 1 n, (Nat.nth Nat.Prime j - 1)) / 2 ^ n := by
  sorry

end OMA.S_oeis_a246541

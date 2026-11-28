import Mathlib

/-!
# A284759: Sum_{i=1..n-1} i^(n-2) ≡ 0 (mod n^3) exactly for Wolstenholme primes

Source: https://oeis.org/A284759

A284759 (offset 1): `a(n) = (Sum_{i=1..n-1} i^(n-2)) mod n^3`:
0, 1, 3, 14, 100, 115, 196, 500, 189, 333, …

Conjecture (recorded by Felix Fröhlich, Apr 02 2017; cf. Mestrovic, 2012, Conjecture 2.10): for
`n > 1`, `a(n) = 0` if and only if `n` is a term of A088164, i.e., `n` is a Wolstenholme prime.

Conventions:
- `a(n) = 0` means that `n^3` divides `Sum_{i=1..n-1} i^(n-2)`; the sum is taken over
  `Finset.Icc 1 (n - 1)` in `ℕ`, and `n - 2` is an exact subtraction for `n > 1`.
- A Wolstenholme prime (A088164: 16843, 2124679, …) is a prime `p` such that
  `binomial(2p-1, p-1) ≡ 1 (mod p^4)`.
-/

namespace OMA.S_oeis_a284759

/-- A Wolstenholme prime (A088164): a prime `p` with `binomial(2p-1, p-1) ≡ 1 (mod p^4)`. -/
def IsWolstenholmePrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 4]

theorem main :
    ∀ n : ℕ, 1 < n →
      (n ^ 3 ∣ ∑ i ∈ Finset.Icc 1 (n - 1), i ^ (n - 2) ↔ IsWolstenholmePrime n) := by
  sorry

end OMA.S_oeis_a284759

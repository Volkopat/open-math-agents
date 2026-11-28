import Mathlib

/-!
# A189912: Extended Motzkin numbers, Sum_{k>=0} C(n,k)*C(k), where C(k) is the extended Catalan number A057977(k).

Source: https://oeis.org/A189912
Credit: @cj-55m (agent: Claude Code, model claude-opus-5-5)

The entry (offset 0, data 1, 2, 4, 10, 25, 66, 177, 484, 1339, 3742, 10538, ...)
records in its FORMULA section:

  Conjecture: a(n) = Sum_{k=0..floor(n/2)} (n+1-2*k)*A055151(n,k). - Werner Schulte, Oct 23 2016

The entry now links a proof by Per Alexandersson (May 28 2020), so this is a known result.

Conventions:
* The sequence is indexed from `0`, as in the entry.
* `A001405 n = binomial(n, floor(n/2))` (the central binomial coefficients A001405).
* The extended Catalan number `C(k)` is A057977(k), defined in that entry as
  `gcd(A001405(k+1), A001405(k))`; we use exactly this definition (`extCatalan`).
* `a n = Sum_{k=0..n} binomial(n,k) * C(k)`, the definition of A189912 (the terms with `k > n`
  vanish).
* A055151 is the triangle of Motzkin polynomial coefficients,
  `T(n,k) = n!/((n-2k)! k! (k+1)!) = binomial(n,2k) * A000108(k)`; we use the second form, with
  Mathlib's `catalan` for the Catalan numbers A000108.
* For `0 ≤ k ≤ floor(n/2)` the factor `n+1-2k` is positive, so the identity is stated in `ℕ`
  without any truncated subtraction occurring.
-/

namespace OMA.S_oeis_a189912

/-- A001405: `binomial(n, floor(n/2))`. -/
def centralBinomFloor (n : ℕ) : ℕ := Nat.choose n (n / 2)

/-- A057977, the extended Catalan numbers: `gcd(A001405(k+1), A001405(k))`. -/
def extCatalan (k : ℕ) : ℕ := Nat.gcd (centralBinomFloor (k + 1)) (centralBinomFloor k)

/-- A189912, the extended Motzkin numbers: `a(n) = Sum_{k=0..n} binomial(n,k) * C(k)`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), Nat.choose n k * extCatalan k

/-- A055151, the Motzkin polynomial coefficients: `T(n,k) = binomial(n,2k) * Catalan(k)`. -/
def motzkinCoeff (n k : ℕ) : ℕ := Nat.choose n (2 * k) * catalan k

/-- Werner Schulte's conjecture for A189912:
`a(n) = Sum_{k=0..floor(n/2)} (n+1-2k) * A055151(n,k)` for every `n ≥ 0`. -/
theorem main : ∀ n : ℕ,
    a n = ∑ k ∈ Finset.range (n / 2 + 1), (n + 1 - 2 * k) * motzkinCoeff n k := by
  sorry

end OMA.S_oeis_a189912

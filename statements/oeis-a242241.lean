import Mathlib

/-!
# A242241: primitive prime divisors of the second-order harmonic numbers

Source: https://oeis.org/A242241
Credit: @coleman415

The sequence (Zhi-Wei Sun) is: `a(n)` = least prime `p` such that
`H(2,n) = sum_{k=1..n} 1/k^2 == 0 (mod p)` but there is no `0 < k < n` with
`H(2,k) == 0 (mod p)`, or `1` if such a prime `p` does not exist.
The entry records: *Conjecture: (i) a(n) is prime for any n > 1.*

`main` is part (i), the statement listed for this problem: for every `n > 1` such a prime exists.
Part (ii) of the entry (primitive roots) is a different claim and is not stated here.

Conventions:
- A rational number `x` is `≡ 0 (mod p)` when `p` divides the numerator of `x` in lowest terms
  (the denominator is then prime to `p`). Example from the entry: `H(2,4) = 5*41/(2^4*3^2)`
  is `≡ 0 (mod 41)`.
-/

namespace OMA.S_oeis_a242241

/-- The rational number `x` is congruent to 0 modulo `p`: `p` divides its reduced numerator. -/
def RatModZero (x : ℚ) (p : ℕ) : Prop := (p : ℤ) ∣ x.num

/-- The second-order harmonic number `H(2,n) = 1/1^2 + 1/2^2 + ... + 1/n^2`. -/
def H2 (n : ℕ) : ℚ := ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℚ) ^ 2

/-- Part (i) of the conjecture of OEIS A242241. -/
theorem main :
    ∀ n : ℕ, 1 < n → ∃ p : ℕ, p.Prime ∧ RatModZero (H2 n) p ∧
      ∀ k : ℕ, 0 < k → k < n → ¬ RatModZero (H2 k) p := by
  sorry

end OMA.S_oeis_a242241

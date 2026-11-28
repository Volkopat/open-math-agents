import Mathlib

/-!
# A054979: e-perfect numbers: numbers k such that the sum of the e-divisors (exponential divisors) of k equals 2*k.

Source: https://oeis.org/A054979
Credit: @divmxnd0x

Conjecture (Jon Perry, Nov 13 2012, stated in A054979): every e-perfect number is divisible by 36.

Formalization notes:
* The exponential divisors of `k = ∏ p^(e_p)` are the `∏ p^(b_p)` with `b_p ∣ e_p` (and `b_p ≥ 1`);
  their sum is multiplicative: `σ^(e)(k) = ∏_{p ∣ k} ∑_{b ∣ e_p} p^b`, which is the definition used
  here (`Nat.factorization`).
* `k` is e-perfect when `k > 0` and `σ^(e)(k) = 2k` (terms `36, 180, 252, ...`).
-/

namespace OMA.S_oeis_a054979

/-- The sum of the exponential divisors of `k`. -/
def sigmaE (k : ℕ) : ℕ := ∏ p ∈ k.primeFactors, ∑ b ∈ (k.factorization p).divisors, p ^ b

/-- `k` is e-perfect. -/
def IsEPerfect (k : ℕ) : Prop := 0 < k ∧ sigmaE k = 2 * k

/-- Perry's conjecture: every e-perfect number is divisible by 36. -/
theorem main : ∀ k : ℕ, IsEPerfect k → 36 ∣ k := by
  sorry

end OMA.S_oeis_a054979

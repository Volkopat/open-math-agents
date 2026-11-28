import OMAStatements.S_oeis_a054979
import Mathlib

-- Reduction oeis-a054979.R1 of step oeis-a054979
-- Credit: @Ciphore
-- Perry's conjecture separates into its two prime-adic cores. The 2-adic valuation of an
-- e-perfect number is constrained through the binary exponent-divisor sum
-- `\sum_{b \mid a} 2^b`, whose valuation depends on the divisors of the exponent `a`,
-- while the 3-adic valuation is constrained through the ternary analogue. The two
-- analyses are independent; their conjunction gives divisibility by `4 * 9 = 36` since
-- `gcd(4, 9) = 1`.

namespace OMA.R_oeis_a054979_R1

open OMA.S_oeis_a054979

/-- The 2-adic core of Perry's conjecture: every e-perfect number is divisible by `4`. -/
def H1 : Prop := ∀ k : ℕ, IsEPerfect k → 4 ∣ k

/-- The 3-adic core of Perry's conjecture: every e-perfect number is divisible by `9`. -/
def H2 : Prop := ∀ k : ℕ, IsEPerfect k → 9 ∣ k

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a054979.main := by
  intro h4 h9 k hk
  have h4k : 4 ∣ k := h4 k hk
  have h9k : 9 ∣ k := h9 k hk
  have hcop : Nat.Coprime 4 9 := by decide
  have h36 : 4 * 9 ∣ k := hcop.mul_dvd_of_dvd_of_dvd h4k h9k
  exact h36

end OMA.R_oeis_a054979_R1

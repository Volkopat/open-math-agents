import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Ring.Parity

/-!
# A360204: Record gaps between odd prime powers end at primes

Source: https://oeis.org/A360204 (Peter Luschny)
Credit: @Alienchisel

As in OEIS A246655, prime powers have positive exponents. This convention
includes primes and excludes 1, so the first odd prime power is 3.
The gaps are measured between successive odd prime powers.
-/

namespace OMA.S_oeis_a360204

def IsOddPrimePower (n : ℕ) : Prop :=
  Odd n ∧ IsPrimePow n

/-- The endpoints are odd prime powers with no odd prime power strictly between them. -/
def ConsecutiveOddPrimePowers (lower upper : ℕ) : Prop :=
  IsOddPrimePower lower ∧ IsOddPrimePower upper ∧ lower < upper ∧
    ∀ n : ℕ, lower < n → n < upper → ¬ IsOddPrimePower n

/-- The gap ending at this odd prime power is strictly larger than every earlier gap. -/
def IsRecordGapEndpoint (upper : ℕ) : Prop :=
  ∃ lower : ℕ, ConsecutiveOddPrimePowers lower upper ∧
    ∀ a b : ℕ, b < upper → ConsecutiveOddPrimePowers a b → b - a < upper - lower

theorem main : ∀ n : ℕ, IsRecordGapEndpoint n → n.Prime := by
  sorry

end OMA.S_oeis_a360204

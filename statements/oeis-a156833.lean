import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Choose.Basic

/-!
# OEIS A156833

Conjecture attributed to Gary W. Adamson. The first divisor sum is the
action of A156348 on the positive integers. The second applies the
Möbius matrix A054525. The matrix definitions are supported on divisors.

Source: https://oeis.org/A156833
Matrix entries: https://oeis.org/A156348 and https://oeis.org/A054525
Credit: @AShahver
-/

namespace OMA.S_oeis_a156833

open scoped BigOperators

def b (n : ℕ) : ℤ :=
  ∑ k ∈ n.divisors, (k : ℤ) * (Nat.choose (n / k + k - 2) (k - 1) : ℤ)

def a (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, ArithmeticFunction.moebius (n / d) * b d

theorem main : ∀ n : ℕ, 1 < n → (a n = (n : ℤ) ↔ n.Prime) := by
  sorry

end OMA.S_oeis_a156833

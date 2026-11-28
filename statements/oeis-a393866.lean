import Mathlib

/-!
# A393866: G.f. A(x) satisfies [x^n] A(x)^prime(n) = prime(n) * [x^(n-1)] A(x)^prime(n) for n >= 1.

Source: https://oeis.org/A393866

Offset 0, a(0) = 1. The defining relation is [x^n] A(x)^prime(n) * (1 - prime(n)*x) = 0
for n >= 1, which fixes a(n) uniquely (a(n) enters [x^n] A(x)^prime(n) with coefficient prime(n)).
Conjecture (formula (2) of the entry, see A393867): the coefficients of the logarithmic
derivative are divisible by prime(n) for n > 1. The entry writes [x^n] A'(x)/A(x); its example
(A393867 = [1, 3*1, 5*5, 7*41, ...], with A393867(n) divisible by prime(n)) shows that the n-th
term is [x^(n-1)] A'(x)/A(x) = [x^n] x*A'(x)/A(x); the literal reading fails at n = 2
(coefficient 25, prime 3), so the indexing of the example is used.

Formalized: a(n) is a rational sequence with a(0) = 1 satisfying the defining relation in
PowerSeries over the rationals; prime(n) = Nat.nth Nat.Prime (n - 1). The claim is that for every
n >= 2 the coefficient of x^n in x * A'(x) * A(x)^(-1) is an integer multiple of prime(n), which
also asserts it is an integer.
-/

namespace OMA.S_oeis_a393866

open PowerSeries

/-- prime(n), 1-indexed: prime(1) = 2. -/
noncomputable def pr (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The power series with coefficient sequence a. -/
noncomputable def ser (a : ℕ → ℚ) : PowerSeries ℚ := PowerSeries.mk a

theorem main : ∀ a : ℕ → ℚ, a 0 = 1 →
    (∀ n : ℕ, 1 ≤ n →
      coeff n (ser a ^ pr n * (1 - C ((pr n : ℕ) : ℚ) * X)) = 0) →
    ∀ n : ℕ, 2 ≤ n →
      ∃ m : ℤ, coeff n (X * derivative ℚ (ser a) * (ser a)⁻¹) = ((pr n : ℕ) : ℚ) * (m : ℚ) := by
  sorry

end OMA.S_oeis_a393866

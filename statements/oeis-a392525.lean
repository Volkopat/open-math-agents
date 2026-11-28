import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Hanna's parity and last-digit conjectures for OEIS A392525

Source: https://oeis.org/A392525
Credit: @anmolspace

The generating series has zero constant coefficient and linear coefficient one.
Cubing the stated formal cube-root equation avoids choosing a root operation in
the integer power series ring. The entry poses two different assertions.
-/
namespace OMA.S_oeis_a392525
open PowerSeries

def Defines (A : PowerSeries ℤ) : Prop :=
  A.constantCoeff = 0 ∧ coeff 1 A = 1 ∧
    A^3 = A.subst ((X : PowerSeries ℤ)^3 + 15*X*A^3)

/-- Both equivalences cover the entire sequence, including the exceptional
linear term a(1)=1. Existence makes the assertion about integer solutions nonvacuous. -/
theorem main : (∃ A, Defines A) ∧
    ∀ A, Defines A → ∀ n : ℕ, 0 < n →
      (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2^k) ∧
      (coeff n A % 10 = 5 ↔ ∃ k : ℕ, n = 2^(k+1)) := by
  sorry

end OMA.S_oeis_a392525

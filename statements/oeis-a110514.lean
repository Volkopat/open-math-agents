import Mathlib

/-!
# A110514: Expansion of (1 - x + x^2 + x^3)/(1 - x^2 - x^4 + x^6)

Source: https://oeis.org/A110514
Credit: @ivillar

Paul Barry's sequence (offset 0): a(n) is the coefficient of x^n in the power series expansion of
(1 - x + x^2 + x^3)/(1 - x^2 - x^4 + x^6) (taken over ℚ).

Conjecture (in the formula section of A110514):
  a(n) = Sum_{k=0..floor(n/2)} Jacobi(2^(n-2k), 2(n-2k)+1),
where Jacobi(a, b) is the Jacobi symbol, Mathlib's `jacobiSym a b`. The terms are integers and
are compared in ℚ.
-/

namespace OMA.S_oeis_a110514

open PowerSeries

/-- The g.f. (1 - x + x^2 + x^3)/(1 - x^2 - x^4 + x^6), as a power series over ℚ. -/
noncomputable def G : PowerSeries ℚ :=
  (1 - X + X ^ 2 + X ^ 3) * (1 - X ^ 2 - X ^ 4 + X ^ 6)⁻¹

/-- a(n): the coefficient of x^n in the expansion (offset 0). -/
noncomputable def a (n : ℕ) : ℚ := coeff n G

/-- The conjectured formula, with Mathlib's Jacobi symbol `jacobiSym`. -/
theorem main : ∀ n : ℕ,
    a n = ∑ k ∈ Finset.range (n / 2 + 1),
      ((jacobiSym ((2 : ℤ) ^ (n - 2 * k)) (2 * (n - 2 * k) + 1) : ℤ) : ℚ) := by
  sorry

end OMA.S_oeis_a110514

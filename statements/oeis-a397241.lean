import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a397241

/-!
OEIS A397241: G.f. A(x) satisfies n * [x^n] A(x)^n = (n-1) * [x^n] A(x)^(n+1) for n > 1,
with A(0) = 1 and A'(0) = 1.
Conjecture: all terms a(n) are odd.
-/

theorem main : ∀ (A : PowerSeries ℤ),
    PowerSeries.constantCoeff A = 1 →
    PowerSeries.coeff 1 A = 1 →
    (∀ n : ℕ, 1 < n →
      (n : ℤ) * PowerSeries.coeff n (A ^ n) =
      ((n : ℤ) - 1) * PowerSeries.coeff n (A ^ (n + 1))) →
    ∀ n : ℕ, Odd (PowerSeries.coeff n A) := by
  sorry

end OMA.S_oeis_a397241

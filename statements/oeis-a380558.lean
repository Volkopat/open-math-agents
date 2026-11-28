import Mathlib.RingTheory.PowerSeries.Substitution

namespace OMA.S_oeis_a380558

/-- Positive integers whose binary expansion does not begin with `10` (positive terms of
OEIS A004760): `m = 1` or `3 * 2^k ≤ m < 4 * 2^k` for some `k : ℕ`. -/
def isNoLeading10 (m : ℕ) : Prop :=
  m = 1 ∨ ∃ k : ℕ, 3 * 2 ^ k ≤ m ∧ m < 4 * 2 ^ k

/-- Conjecture (OEIS A380558): let `A(x) = ∑_{n≥2} a(n) x^n ∈ ℤ⟦X⟧` satisfy `A(0) = 0`,
`a(1) = 0`, and `(1 - x^2) * A(x - A(x)) = x^2`. Then for all `n ≥ 2`, `a(n)` is odd if
and only if `n = 2 * m` for some `m` whose binary expansion does not begin with `10`. -/
theorem main :
    ∀ A : PowerSeries ℤ,
      PowerSeries.constantCoeff A = 0 →
      PowerSeries.coeff 1 A = 0 →
      (1 - PowerSeries.X ^ 2) * PowerSeries.subst (PowerSeries.X - A) A = PowerSeries.X ^ 2 →
      ∀ n : ℕ, 2 ≤ n →
        (Odd (PowerSeries.coeff n A) ↔ ∃ m : ℕ, n = 2 * m ∧ isNoLeading10 m) := by
  sorry

end OMA.S_oeis_a380558

import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a338632

/-- OEIS A338632: If `A(x) ∈ ℤ[[x]]` with `A(0) = 1` satisfies the continued fraction relation
`1 = A(x) - x/(A(x) - 3*x/(A(x) - 5*x/(A(x) - 7*x/...)))`, i.e., there exists a sequence
`R : ℕ → ℤ[[x]]` such that `A - 1 = x * R 0` and
`R k * (A - (2*k + 3) * x * R (k + 1)) = 1` for all `k ≥ 0`, then `a(n) % 4 = 2` for all `n > 1`. -/
theorem main :
    ∀ (A : PowerSeries ℤ),
      PowerSeries.constantCoeff A = 1 →
      (∃ R : ℕ → PowerSeries ℤ,
        A - 1 = PowerSeries.X * R 0 ∧
        ∀ k : ℕ, R k * (A - ((2 * k + 3 : ℕ) : PowerSeries ℤ) * PowerSeries.X * R (k + 1)) = 1) →
      ∀ n : ℕ, 1 < n → PowerSeries.coeff n A % 4 = 2 := by
  sorry

end OMA.S_oeis_a338632

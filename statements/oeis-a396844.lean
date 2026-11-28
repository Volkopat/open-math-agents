import Mathlib.RingTheory.PowerSeries.Substitution

namespace OMA.S_oeis_a396844

/-- Conjecture (OEIS A396844): If `A(x) = ∑ a(n) x^n ∈ ℤ⟦X⟧` satisfies `a(0) = 0`, `a(1) = 1`,
and `A(x * A(x) - 4 * x * A(x)^2) = x^2`, then for every `n > 8`,
`a(n) ≡ 12 (mod 16)` whenever `n` is of the form `2 * 4^k + 1`, and `16 ∣ a(n)` otherwise. -/
theorem main :
    ∀ A : PowerSeries ℤ,
      PowerSeries.constantCoeff A = 0 →
      PowerSeries.coeff 1 A = 1 →
      PowerSeries.subst (PowerSeries.X * A - 4 * PowerSeries.X * A ^ 2) A = PowerSeries.X ^ 2 →
      ∀ n : ℕ, 8 < n →
        ((∃ k : ℕ, n = 2 * 4 ^ k + 1) → PowerSeries.coeff n A % 16 = 12) ∧
        ((¬ ∃ k : ℕ, n = 2 * 4 ^ k + 1) → (16 : ℤ) ∣ PowerSeries.coeff n A) := by
  sorry

end OMA.S_oeis_a396844

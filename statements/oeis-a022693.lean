import Mathlib

/-!
# A022693: Expansion of Product_{m>=1} 1 / (1 + m * q^m)

Source: https://oeis.org/A022693
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture (Benedict W. J. Irwin, Mar 19 2017):
Let `a(n)` be the coefficient of `q^n` in `∏_{m ≥ 1} 1 / (1 + m * q^m)`.
Then for every `n : ℕ`:
  `a(n) = ∑_{i₁ + 2*i₂ + 3*i₃ + ... = n} (-1)^(i₁ + i₂ + i₃ + ...) * ∏_{k > 0} k^(i_k)`,
equivalently, summing over all integer partitions `P` of `n`,
  `a(n) = ∑ P : Nat.Partition n, (-1)^(P.parts.card) * P.parts.prod`.

Conventions:
- The formal power series `f : PowerSeries ℤ` of `∏_{m ≥ 1} 1 / (1 + m * q^m)` is characterized
  by `coeff N ((∏ m ∈ Finset.Icc 1 N, (1 + C m * X^m)) * f) = if N = 0 then 1 else 0` for all `N`.
-/

namespace OMA.S_oeis_a022693

theorem main :
    ∀ f : PowerSeries ℤ,
      (∀ N : ℕ,
        PowerSeries.coeff N
          ((∏ m ∈ Finset.Icc 1 N,
            (1 + PowerSeries.C (m : ℤ) * PowerSeries.X ^ m : PowerSeries ℤ)) * f) =
          if N = 0 then 1 else 0) →
      ∀ n : ℕ,
        PowerSeries.coeff n f =
          ∑ P : Nat.Partition n, (-1 : ℤ) ^ P.parts.card * (P.parts.prod : ℤ) := by
  sorry

end OMA.S_oeis_a022693

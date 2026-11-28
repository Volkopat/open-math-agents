import Mathlib

namespace OMA.S_arxiv_2610_39051

/-- The denominator `q_{k,m}(z)` of the `[k/m]` Padé approximant to `exp(z)`,
viewed as a formal power series over `ℚ`:
`q_{k,m}(z) = ∑_{j=0}^m ((k + m - j)! * m! / ((k + m)! * (m - j)! * j!)) * (-z)^j`. -/
noncomputable def qPade (k m : ℕ) : PowerSeries ℚ :=
  ∑ j ∈ Finset.range (m + 1),
    PowerSeries.C
      ((((Nat.factorial (k + m - j) * Nat.factorial m : ℕ) : ℚ) /
        ((Nat.factorial (k + m) * Nat.factorial (m - j) * Nat.factorial j : ℕ) : ℚ)) *
        (-1 : ℚ) ^ j) *
      PowerSeries.X ^ j

/-- Fasi–Higham positivity conjecture (SIAM J. Matrix Anal. Appl. 40 (2019), Conjecture 3.2;
disproved in arXiv:2610.39051): for every `k : ℕ` and every odd `m : ℕ`, every Taylor coefficient
of the reciprocal `1 / q_{k,m}(z)` is strictly positive. -/
theorem main :
    ∀ (k m : ℕ), Odd m →
      ∀ (c : PowerSeries ℚ), qPade k m * c = 1 →
        ∀ (n : ℕ), 0 < PowerSeries.coeff n c := by
  sorry

end OMA.S_arxiv_2610_39051

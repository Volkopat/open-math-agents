import Mathlib

namespace OMA.S_oeis_a126617

/-- Bell numbers `B(n)` (OEIS A000110), defined by `B(0) = 1` and
`B(n + 1) = ∑_{k=0}^n C(n, k) * B(k)`. -/
def bellNum : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1), Nat.choose n k.val * bellNum k.val

/-- Sequence with e.g.f. `exp(exp(x) - 1 + p * x)`:
`seqP p n = ∑_{i=0}^n p^(n - i) * B(i) * C(n, i)`. For `p = -2`, this is OEIS A126617. -/
def seqP (p : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (n + 1), p ^ (n - i) * (bellNum i : ℚ) * (Nat.choose n i : ℚ)

/-- Formal power series inverse of `1 - x * f(x)` in `PowerSeries ℚ`. -/
noncomputable def invOneSubAux (f : PowerSeries ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i f * invOneSubAux f (n - i)

noncomputable def invOneSub (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (invOneSubAux f)

/-- Formal power series inverse of any series `f ∈ PowerSeries ℚ` with constant term `1`. -/
noncomputable def invUnit1 (f : PowerSeries ℚ) : PowerSeries ℚ :=
  invOneSub (PowerSeries.mk (fun n => -PowerSeries.coeff (n + 1) f))

/-- Depth-`d` truncation of Sergei N. Gladkovskii's continued fraction (Feb 13 2013):
`G(k) = 2*x + 1 - p*x - x*k + x*(x*k - x - 1 + p*x) / G(k + 1)`. -/
noncomputable def cfFold (p : ℚ) : ℕ → ℕ → PowerSeries ℚ → PowerSeries ℚ
  | _, 0, tail => tail
  | k, d + 1, tail =>
      let g := cfFold p (k + 1) d tail
      1 + PowerSeries.C (2 - p - (k : ℚ)) * PowerSeries.X +
        PowerSeries.X * (PowerSeries.C ((k : ℚ) - 1 + p) * PowerSeries.X - 1) * invUnit1 g

/-- Truncated continued-fraction generating function `(1 + (1 - p)*x) / (G(0) - x)`,
corresponding to `1 + x * A(x)` where `A(x) = (x + 1 - p*x) / x / (G(0) - x) - 1/x`. -/
noncomputable def cfApprox (p : ℚ) (d : ℕ) : PowerSeries ℚ :=
  (1 + PowerSeries.C (1 - p) * PowerSeries.X) * invUnit1 (cfFold p 0 d 1 - PowerSeries.X)

/-- Sergei N. Gladkovskii's conjecture (OEIS A126617, Feb 13 2013):
For every `p : ℚ` (and in particular `p = -2`, which gives A126617), the formal power series
`(1 + (1 - p)*x) / (G(0) - x)` defined by the continued fraction
`G(k) = 2*x + 1 - p*x - x*k + x*(x*k - x - 1 + p*x) / G(k + 1)`
equals `1 + x * ∑_{n ≥ 0} seqP(p, n) * x^n`, i.e., for every `n` and truncation depth `d ≥ n + 1`,
the coefficient of `x^(n + 1)` equals `seqP p n` (and the constant term is `1`). -/
theorem main :
    ∀ (p : ℚ) (n d : ℕ), n + 1 ≤ d →
      PowerSeries.coeff 0 (cfApprox p d) = 1 ∧
      PowerSeries.coeff (n + 1) (cfApprox p d) = seqP p n := by
  sorry

end OMA.S_oeis_a126617

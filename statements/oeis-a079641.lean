import Mathlib

namespace OMA.S_oeis_a079641

/-- Stirling numbers of the second kind `S2(n, k)` (OEIS A008277). -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-- Unsigned Stirling numbers of the first kind `|S1(n, k)|` (OEIS |A008275|). -/
def unsignedStirling1 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => n * unsignedStirling1 n (k + 1) + unsignedStirling1 n k

/-- Row polynomial `P_n(x) = ∑_{j=0}^n (∑_{k=0}^n S2(n, k) * |S1(k, j)|) * x^j` of OEIS A079641. -/
noncomputable def rowPoly (n : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (n + 1),
    Polynomial.C (∑ k ∈ Finset.range (n + 1),
      ((stirling2 n k * unsignedStirling1 k j : ℕ) : ℚ)) * Polynomial.X ^ j

/-- Formal power series inverse `(1 - z * f(z))⁻¹` in `PowerSeries (Polynomial ℚ)`. -/
noncomputable def invOneSubAux (f : PowerSeries (Polynomial ℚ)) : ℕ → Polynomial ℚ
  | 0 => 1
  | n + 1 => ∑ i ∈ Finset.range (n + 1),
      PowerSeries.coeff i f * invOneSubAux f (n - i)

noncomputable def invOneSub (f : PowerSeries (Polynomial ℚ)) : PowerSeries (Polynomial ℚ) :=
  PowerSeries.mk (invOneSubAux f)

/-- Stieltjes continued fraction partial numerators:
`a_0 = x`, `a_1 = 2`, `a_2 = x + 1`, `a_3 = 4`, `a_4 = x + 2`, `a_5 = 6`, ... -/
noncomputable def stieltjesNum (m : ℕ) : Polynomial ℚ :=
  if m % 2 = 0 then
    Polynomial.X + Polynomial.C ((m / 2 : ℕ) : ℚ)
  else
    Polynomial.C (((m + 1 : ℕ) : ℚ))

/-- Finite bottom-up Stieltjes continued fraction evaluator:
`stieltjesFold m 0 tail = tail`,
`stieltjesFold m (d + 1) tail = (1 - a_m * z * stieltjesFold (m + 1) d tail)⁻¹`. -/
noncomputable def stieltjesFold (m : ℕ) : ℕ → PowerSeries (Polynomial ℚ) → PowerSeries (Polynomial ℚ)
  | 0, tail => tail
  | d + 1, tail => invOneSub (PowerSeries.C (stieltjesNum m) * stieltjesFold (m + 1) d tail)

/-- OEIS A079641 (Peter Bala, Dec 12 2024):
The ordinary generating function of the row polynomials of `S2 * |S1|` equals the
Stieltjes continued fraction
`1 / (1 - x*z / (1 - 2*z / (1 - (x + 1)*z / (1 - 4*z / (1 - (x + 2)*z / (1 - 6*z / ...))))))`
in the sense that for every `n : ℕ` and every truncation depth `N ≥ n`, the coefficient of `z^n`
in the `N`-th convergent `stieltjesFold 0 N 1` equals `rowPoly n`. -/
theorem main :
    ∀ n N : ℕ, n ≤ N → PowerSeries.coeff n (stieltjesFold 0 N 1) = rowPoly n := by sorry

end OMA.S_oeis_a079641

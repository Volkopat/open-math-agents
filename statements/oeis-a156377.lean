import Mathlib

namespace OMA.S_oeis_a156377

/-- Value of the `n`-th Euler polynomial `E_n(t)` at `t : ℚ`, uniquely determined by
`E_n(t) + E_n(t + 1) = 2 * t^n`, i.e. `E_n(t) = t^n - (1/2) * ∑_{k=0}^{n-1} C(n, k) * E_k(t)`. -/
def eulerVal (t : ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => t ^ (n + 1) - (1 / 2 : ℚ) * ∑ k : Fin (n + 1),
      ((Nat.choose (n + 1) k.val : ℕ) : ℚ) * eulerVal t k.val

/-- OEIS A156377: Numerator of `Euler(n, 1/16)`. -/
def oeis_a156377Val (n : ℕ) : ℤ :=
  (eulerVal (1 / 16 : ℚ) n).num

/-- Formal power series inverse of `1 - x * f(x)` in `PowerSeries ℚ`. -/
noncomputable def invOneSubAux (f : PowerSeries ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i f * invOneSubAux f (n - i)

noncomputable def invOneSub (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (invOneSubAux f)

/-- Formal power series inverse of any series `f ∈ PowerSeries ℚ` with constant term `1`. -/
noncomputable def invUnit1 (f : PowerSeries ℚ) : PowerSeries ℚ :=
  invOneSub (PowerSeries.mk (fun n => -PowerSeries.coeff (n + 1) f))

/-- One step of Sergei N. Gladkovskii's continued fraction for A156377:
`T(k) = 1 - 64 * x^2 * (k + 1)^2 / (64 * x^2 * (k + 1)^2 + (1 + 7 * x)^2 / T(k + 1))`. -/
noncomputable def gladStep (k : ℕ) (t : PowerSeries ℚ) : PowerSeries ℚ :=
  let a : PowerSeries ℚ := PowerSeries.C ((64 * (k + 1) ^ 2 : ℕ) : ℚ) * PowerSeries.X ^ 2
  let b : PowerSeries ℚ := (1 + PowerSeries.C (7 : ℚ) * PowerSeries.X) ^ 2
  1 - a * invUnit1 (a + b * invUnit1 t)

/-- Finite bottom-up convergent `T_d(k)` of depth `d` starting from tail `t`. -/
noncomputable def gladFold (k : ℕ) : ℕ → PowerSeries ℚ → PowerSeries ℚ
  | 0, t => t
  | d + 1, t => gladStep k (gladFold (k + 1) d t)

/-- `N`-th convergent `T_N(0) / (1 + 7 * x)` of Gladkovskii's conjectured g.f. for A156377. -/
noncomputable def gladGF (N : ℕ) : PowerSeries ℚ :=
  gladFold 0 N 1 * invUnit1 (1 + PowerSeries.C (7 : ℚ) * PowerSeries.X)

/-- OEIS A156377 (Sergei N. Gladkovskii, Nov 12 2013):
The ordinary generating function of `Numerator(Euler(n, 1/16))` equals
`T(0) / (1 + 7 * x)`, where
`T(k) = 1 - 64 * x^2 * (k + 1)^2 / (64 * x^2 * (k + 1)^2 + (1 + 7 * x)^2 / T(k + 1))`,
i.e. for every `n : ℕ` and every depth `N` with `n ≤ 2 * N`, the `n`-th coefficient of
`gladGF N` equals `(oeis_a156377Val n : ℚ)`. -/
theorem main :
    ∀ n N : ℕ, n ≤ 2 * N → PowerSeries.coeff n (gladGF N) = (oeis_a156377Val n : ℚ) := by sorry

end OMA.S_oeis_a156377

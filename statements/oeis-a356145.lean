import Mathlib

namespace OMA.S_oeis_a356145

noncomputable def invFac {K : Type} [CommRing K] [Algebra ℚ K] (n : ℕ) : K :=
  algebraMap ℚ K ((Nat.factorial n : ℚ)⁻¹)

/-- Exponential generating function `A(x) = ∑_{n≥1} a(n-1) * x^n / n!`. -/
noncomputable def A_series {K : Type} [CommRing K] [Algebra ℚ K] (a : ℕ → K) : PowerSeries K :=
  PowerSeries.mk fun n => if n = 0 then 0 else invFac n * a (n - 1)

/-- `U(x) = A(x) / x = ∑_{n≥0} a(n) * x^n / (n+1)!`, with constant term `a(0)`. -/
noncomputable def U_series {K : Type} [CommRing K] [Algebra ℚ K] (a : ℕ → K) : PowerSeries K :=
  PowerSeries.mk fun n => invFac (n + 1) * a n

/-- `x / A(x) = U(x)⁻¹` when `a(0) = 1`. -/
noncomputable def xDivA {K : Type} [CommRing K] [Algebra ℚ K] (a : ℕ → K) (ha : a 0 = 1) :
    PowerSeries K :=
  ↑((PowerSeries.isUnit_iff_constantCoeff (φ := U_series a)).mpr (by
    unfold U_series
    rw [PowerSeries.constantCoeff_mk, invFac, Nat.factorial_one, Nat.cast_one, inv_one,
      map_one, one_mul, ha]
    exact isUnit_one)).unit⁻¹

/-- Mikhail Kurkov's recursive array `R(n, k)` for `n ≥ 1, k ≥ 1`. -/
def kurkovR {K : Type} [CommRing K] (a : ℕ → K) : ℕ → ℕ → K
  | 0, _ => 0
  | 1, k => a k
  | n + 2, k =>
    kurkovR a (n + 1) (k + 1) -
      ∑ j : Fin (n + 1),
        (Nat.choose (n + 1) j.1 : K) * kurkovR a (j.1 + 1) k * kurkovR a (n + 1 - j.1) 1
termination_by n _ => n
decreasing_by
  all_goals simp_wf
  all_goals try (have := j.isLt; omega)

/-- Bell polynomial matrix `S(n, k) = n! * [x^n] A(x)^k / k!`. -/
noncomputable def bellS {K : Type} [CommRing K] [Algebra ℚ K] (a : ℕ → K) (n k : ℕ) : K :=
  (Nat.factorial n : K) * invFac k * PowerSeries.coeff n ((A_series a) ^ k)

/-- Inverse refined Eulerian partition polynomial `E_n^{(-1)} = (n-1)! * [x^(n-1)] A''(x) * (x / A(x))^n`. -/
noncomputable def invEulerian {K : Type} [CommRing K] [Algebra ℚ K]
    (a : ℕ → K) (ha : a 0 = 1) (n : ℕ) : K :=
  (Nat.factorial (n - 1) : K) *
    PowerSeries.coeff (n - 1)
      (PowerSeries.derivative K (PowerSeries.derivative K (A_series a)) * (xDivA a ha) ^ n)

theorem main :
    ∀ (K : Type) [CommRing K] [Algebra ℚ K] (a : ℕ → K) (ha : a 0 = 1),
      (∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
        ∑ j ∈ Finset.range n, bellS a n (j + 1) * kurkovR a (j + 1) k = a (n + k - 1)) ∧
      (∀ n : ℕ, 1 ≤ n → kurkovR a n 1 = invEulerian a ha n) := by
  sorry

end OMA.S_oeis_a356145

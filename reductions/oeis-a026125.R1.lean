import OMAStatements.S_oeis_a026125

-- Reduction of OEIS A026125.
-- Credit: @m-miyawaki-m

namespace OMA.R_oeis_a026125_R1

open PowerSeries

private theorem coeff_shift (f : PowerSeries ℤ) {n k : ℕ} (h : k ≤ n) :
    coeff n (X ^ k * f) = coeff (n - k) f := by
  rw [coeff_X_pow_mul']
  simp [h]

private theorem coeff_shift_one (f : PowerSeries ℤ) {n : ℕ} (h : 1 ≤ n) :
    coeff n (X * f) = coeff (n - 1) f := by
  simpa only [pow_one] using coeff_shift f h

/-- Reflection at height -1 gives the generating function for the walks. -/
def H1 : Prop :=
  ∃ r : PowerSeries ℤ, r = X * (1 + r + r ^ 2) ∧
    ∀ n : ℕ, coeff n (r ^ 3 + (2 : ℤ) • r ^ 5 + r ^ 7) = OMA.S_oeis_a026125.a n

/-- The Euler-operator identity follows by differentiating the implicit equation for r. -/
def H2 : Prop :=
  ∀ r : PowerSeries ℤ, r = X * (1 + r + r ^ 2) →
    let f := r ^ 3 + (2 : ℤ) • r ^ 5 + r ^ 7
    let euler (g : PowerSeries ℤ) := PowerSeries.mk fun n => (n : ℤ) * coeff n g
    let d := euler f
    let dd := euler d
    (-dd - (4 : ℤ) • d + (21 : ℤ) • f) +
      X * ((4 : ℤ) • dd + (13 : ℤ) • d - (42 : ℤ) • f) +
      X ^ 2 * ((-2 : ℤ) • dd + (5 : ℤ) • d + (45 : ℤ) • f) +
      X ^ 3 * ((-4 : ℤ) • dd - (17 : ℤ) • d) +
      X ^ 4 * ((3 : ℤ) • dd + (3 : ℤ) • d) = 0

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a026125.main := by
  rintro ⟨r, hr, ha⟩ hdiff n hn
  have h := congrArg (coeff n) (hdiff r hr)
  dsimp only at h
  set f := r ^ 3 + (2 : ℤ) • r ^ 5 + r ^ 7
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have h4 : 4 ≤ n := by omega
  rw [map_add, map_add, map_add, map_add,
    coeff_shift_one _ h1, coeff_shift _ h2, coeff_shift _ h3, coeff_shift _ h4] at h
  simp only [map_add, map_sub, map_neg, map_zero, map_zsmul, coeff_mk, ha] at h
  simp only [zsmul_eq_mul, Int.natCast_sub h1, Int.natCast_sub h2,
    Int.natCast_sub h3, Int.natCast_sub h4] at h
  linear_combination h

end OMA.R_oeis_a026125_R1

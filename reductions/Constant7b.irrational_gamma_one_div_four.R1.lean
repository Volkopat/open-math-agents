import FormalConjectures.OptimizationConstants.«7b»

/-!
Reduction of `Constant7b.irrational_gamma_one_div_four`

We reduce the irrationality of `Real.Gamma (1 / 4)` to two classical theorems about the
lemniscatic elliptic curve `Y ^ 2 = 4 * X ^ 3 - 4 * X` (`g₂ = 4`, `g₃ = 0`), whose real
half-period is `ω₁ = ∫ x in Set.Ioi (1 : ℝ), 1 / Real.sqrt (4 * x ^ 3 - 4 * x)`:

- `H1`: Existence of the Weierstrass zeta function `ζ_W` and real quasi-period `η₁` for the
  lemniscatic square lattice `Λ = 2 * ω₁ * (ℤ + i ℤ)` together with Legendre's period
  relation `ω₁ * η₁ = Real.pi / 4`.
- `H2`: Chudnovsky's theorem (1976) on the algebraic independence of `ω₁` and `η₁` over `ℚ`.

Inside this file we prove the full analytic and algebraic bridge from `H1` and `H2` to
`Irrational (Real.Gamma (1 / 4))`:
1. Change of variables `x = t ^ (-2)` rewriting the improper Weierstrass integral `ω₁` as the
   lemniscate integral `∫ t in Set.Ioo (0 : ℝ) 1, 1 / Real.sqrt (1 - t ^ 4)`.
2. Quartic change of variables `u = t ^ 4` and Euler's complex Beta-Gamma identity yielding
   `4 * Real.Gamma (3 / 4) * ω₁ = Real.Gamma (1 / 4) * Real.Gamma (1 / 2)`.
3. Euler's reflection formula at `1 / 4` and `Real.Gamma (1 / 2) = Real.sqrt Real.pi` yielding
   Gauss's lemniscate identity `Real.Gamma (1 / 4) ^ 4 = 32 * Real.pi * ω₁ ^ 2`.
4. Substitution of `Real.pi = 4 * ω₁ * η₁` from `H1` giving
   `Real.Gamma (1 / 4) ^ 4 = 128 * ω₁ ^ 3 * η₁`, so rationality of `Real.Gamma (1 / 4)` yields a
   nonzero bivariate rational polynomial annihilating `(ω₁, η₁)`, contradicting `H2`.
-/

namespace OMA.R_Constant7b_irrational_gamma_one_div_four_R1

/-- Existence of the Weierstrass zeta function `ζ_W` and real quasi-period `η₁` of the
lemniscatic elliptic curve `Y ^ 2 = 4 * X ^ 3 - 4 * X` on the square lattice
`Λ = 2 * ω₁ * (ℤ + i ℤ)`, together with Legendre's period relation `ω₁ * η₁ = Real.pi / 4`. -/
def H1 : Prop :=
  let ω₁ : ℝ := ∫ x in Set.Ioi (1 : ℝ), 1 / Real.sqrt (4 * x ^ 3 - 4 * x)
  let Λ : Set ℂ :=
    {w : ℂ | ∃ m n : ℤ, w = (2 * (m : ℂ) + 2 * (n : ℂ) * Complex.I) * (ω₁ : ℂ)}
  ∃ (ζ_W : ℂ → ℂ) (η₁ : ℝ),
    let ℘ : ℂ → ℂ := fun z => -deriv ζ_W z
    (∀ z, z ∉ Λ → DifferentiableAt ℂ ζ_W z) ∧
    Filter.Tendsto (fun z : ℂ => ζ_W z - z⁻¹) (nhdsWithin 0 {0}ᶜ) (nhds 0) ∧
    (∀ z, z ∉ Λ → ζ_W (z + 2 * (ω₁ : ℂ)) = ζ_W z + 2 * (η₁ : ℂ)) ∧
    (∀ z, z ∉ Λ → ζ_W (z + 2 * (ω₁ : ℂ) * Complex.I) = ζ_W z - 2 * (η₁ : ℂ) * Complex.I) ∧
    (∀ z, z ∉ Λ → (deriv ℘ z) ^ 2 = 4 * ℘ z ^ 3 - 4 * ℘ z) ∧
    ω₁ * η₁ = Real.pi / 4

/-- Chudnovsky's theorem (1976) for the lemniscatic elliptic curve `Y ^ 2 = 4 * X ^ 3 - 4 * X`:
the real half-period `ω₁` and associated real quasi-period `η₁` are algebraically independent
over `ℚ`. -/
def H2 : Prop :=
  let ω₁ : ℝ := ∫ x in Set.Ioi (1 : ℝ), 1 / Real.sqrt (4 * x ^ 3 - 4 * x)
  let Λ : Set ℂ :=
    {w : ℂ | ∃ m n : ℤ, w = (2 * (m : ℂ) + 2 * (n : ℂ) * Complex.I) * (ω₁ : ℂ)}
  ∀ (ζ_W : ℂ → ℂ) (η₁ : ℝ),
    let ℘ : ℂ → ℂ := fun z => -deriv ζ_W z
    (∀ z, z ∉ Λ → DifferentiableAt ℂ ζ_W z) →
    Filter.Tendsto (fun z : ℂ => ζ_W z - z⁻¹) (nhdsWithin 0 {0}ᶜ) (nhds 0) →
    (∀ z, z ∉ Λ → ζ_W (z + 2 * (ω₁ : ℂ)) = ζ_W z + 2 * (η₁ : ℂ)) →
    (∀ z, z ∉ Λ → ζ_W (z + 2 * (ω₁ : ℂ) * Complex.I) = ζ_W z - 2 * (η₁ : ℂ) * Complex.I) →
    (∀ z, z ∉ Λ → (deriv ℘ z) ^ 2 = 4 * ℘ z ^ 3 - 4 * ℘ z) →
    AlgebraicIndependent ℚ ![ω₁, η₁]

lemma image_inv_sq_Ioo :
    (fun t : ℝ => (t ^ 2)⁻¹) '' Set.Ioo (0 : ℝ) 1 = Set.Ioi (1 : ℝ) := by
  ext x
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    have ht2_pos : 0 < t ^ 2 := sq_pos_of_pos ht0
    have ht2_lt : t ^ 2 < 1 := by nlinarith
    have hmul : t ^ 2 * (t ^ 2)⁻¹ = 1 := mul_inv_cancel₀ ht2_pos.ne'
    change 1 < (t ^ 2)⁻¹
    nlinarith
  · intro hx
    have hx_pos : 0 < x := by linarith [Set.mem_Ioi.mp hx]
    have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
    have hsqrt_sq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx_pos.le
    have hsqrt_gt : 1 < Real.sqrt x := by
      have hx1 : 1 < x := Set.mem_Ioi.mp hx
      nlinarith
    refine ⟨(Real.sqrt x)⁻¹, ⟨inv_pos.mpr hsqrt_pos, ?_⟩, ?_⟩
    · have hmul : Real.sqrt x * (Real.sqrt x)⁻¹ = 1 := mul_inv_cancel₀ hsqrt_pos.ne'
      nlinarith
    · dsimp only
      rw [inv_pow, hsqrt_sq, inv_inv]

lemma injOn_inv_sq_Ioo :
    Set.InjOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hab' : a ^ 2 = b ^ 2 := by
    simpa only [inv_inv] using congrArg Inv.inv hab
  have ha0 : 0 < a := ha.1
  have hb0 : 0 < b := hb.1
  nlinarith

lemma hasDerivWithinAt_inv_sq :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun x : ℝ => (x ^ 2)⁻¹) (-(2 / t ^ 3)) (Set.Ioo (0 : ℝ) 1) t := by
  intro t ht
  have ht0 : t ≠ 0 := ht.1.ne'
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t ^ (2 - 1)) t := hasDerivAt_pow 2 t
  have h2 : HasDerivAt (fun x : ℝ => (x ^ 2)⁻¹) (-(2 * t ^ (2 - 1)) / (t ^ 2) ^ 2) t :=
    h1.inv (pow_ne_zero 2 ht0)
  have hder : -(2 * t ^ (2 - 1)) / (t ^ 2) ^ 2 = -(2 / t ^ 3) := by
    field_simp
    ring
  rw [hder] at h2
  exact h2.hasDerivWithinAt

lemma weierstrass_integral_eq_lemniscate :
    (∫ x in Set.Ioi (1 : ℝ), 1 / Real.sqrt (4 * x ^ 3 - 4 * x)) =
      ∫ t in Set.Ioo (0 : ℝ) 1, 1 / Real.sqrt (1 - t ^ 4) := by
  rw [← image_inv_sq_Ioo]
  rw [MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    hasDerivWithinAt_inv_sq injOn_inv_sq_Ioo]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
  intro t ht
  have ht0 : 0 < t := ht.1
  have hscale_pos : 0 < 2 / t ^ 3 := div_pos two_pos (pow_pos ht0 3)
  have hrad : 4 * ((t ^ 2)⁻¹) ^ 3 - 4 * (t ^ 2)⁻¹ = (2 / t ^ 3) ^ 2 * (1 - t ^ 4) := by
    have ht_ne : t ≠ 0 := ht0.ne'
    field_simp
    ring
  dsimp only
  rw [smul_eq_mul, abs_neg, abs_of_pos hscale_pos, hrad, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq hscale_pos.le]
  have hscale_ne : 2 / t ^ 3 ≠ 0 := hscale_pos.ne'
  field_simp

lemma image_pow_four_Ioo :
    (fun t : ℝ => t ^ 4) '' Set.Ioo (0 : ℝ) 1 = Set.Ioo (0 : ℝ) 1 := by
  ext u
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    have ht2_lt : t ^ 2 < 1 := by nlinarith
    exact ⟨pow_pos ht0 4, by nlinarith [sq_nonneg t]⟩
  · intro hu
    have hu0 : 0 < u := hu.1
    have hu1 : u < 1 := hu.2
    have hs1_pos : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
    have hs1_sq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
    have hs1_lt : Real.sqrt u < 1 := by nlinarith
    have hs2_pos : 0 < Real.sqrt (Real.sqrt u) := Real.sqrt_pos.mpr hs1_pos
    have hs2_sq : Real.sqrt (Real.sqrt u) ^ 2 = Real.sqrt u := Real.sq_sqrt hs1_pos.le
    have hs2_lt : Real.sqrt (Real.sqrt u) < 1 := by nlinarith
    refine ⟨Real.sqrt (Real.sqrt u), ⟨hs2_pos, hs2_lt⟩, ?_⟩
    calc
      Real.sqrt (Real.sqrt u) ^ 4 = (Real.sqrt (Real.sqrt u) ^ 2) ^ 2 := by ring
      _ = Real.sqrt u ^ 2 := by rw [hs2_sq]
      _ = u := hs1_sq

lemma injOn_pow_four_Ioo :
    Set.InjOn (fun t : ℝ => t ^ 4) (Set.Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  have ha0 : 0 < a := ha.1
  have hb0 : 0 < b := hb.1
  have hsq : a ^ 2 = b ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg b]
  nlinarith

lemma hasDerivWithinAt_pow_four :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun x : ℝ => x ^ 4) (4 * t ^ 3) (Set.Ioo (0 : ℝ) 1) t := by
  intro t _
  have h : HasDerivAt (fun x : ℝ => x ^ 4) (((4 : ℕ) : ℝ) * t ^ (4 - 1)) t := hasDerivAt_pow 4 t
  simpa using h.hasDerivWithinAt

lemma beta_integral_eq_four_mul_lemniscate :
    (∫ u in Set.Ioo (0 : ℝ) 1, u ^ (-(3 : ℝ) / 4) * (1 - u) ^ (-(1 : ℝ) / 2)) =
      4 * ∫ t in Set.Ioo (0 : ℝ) 1, 1 / Real.sqrt (1 - t ^ 4) := by
  conv_lhs => rw [← image_pow_four_Ioo]
  rw [MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    hasDerivWithinAt_pow_four injOn_pow_four_Ioo]
  have hmul4 :
      (4 : ℝ) * ∫ t in Set.Ioo (0 : ℝ) 1, 1 / Real.sqrt (1 - t ^ 4) =
        ∫ t in Set.Ioo (0 : ℝ) 1, (4 : ℝ) * (1 / Real.sqrt (1 - t ^ 4)) := by
    rw [MeasureTheory.integral_const_mul]
  rw [hmul4]
  refine MeasureTheory.setIntegral_congr_fun (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) 1)) ?_
  intro t ht
  dsimp only
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  have ht2_lt : t ^ 2 < 1 := by nlinarith
  have h1m : 0 ≤ 1 - t ^ 4 := by nlinarith [sq_nonneg t]
  have hderiv_pos : 0 < 4 * t ^ 3 := mul_pos (by norm_num) (pow_pos ht0 3)
  have hpow1 : (t ^ 4) ^ (-(3 : ℝ) / 4) = (t ^ 3)⁻¹ := by
    rw [← Real.rpow_natCast t 4, ← Real.rpow_mul ht0.le]
    have hexp : ((4 : ℕ) : ℝ) * (-(3 : ℝ) / 4) = -(3 : ℝ) := by norm_num
    rw [hexp, Real.rpow_neg ht0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hpow2 : (1 - t ^ 4) ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt (1 - t ^ 4) := by
    rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring, Real.rpow_neg h1m, ← Real.sqrt_eq_rpow,
      ← one_div]
  rw [smul_eq_mul, abs_of_pos hderiv_pos, hpow1, hpow2]
  have ht3_ne : t ^ 3 ≠ 0 := (pow_pos ht0 3).ne'
  rw [← mul_assoc, mul_assoc 4 (t ^ 3), mul_inv_cancel₀ ht3_ne, mul_one]

lemma four_mul_gamma_three_fourths_mul_lemniscate :
    4 * Real.Gamma (3 / 4) * (∫ t in Set.Ioo (0 : ℝ) 1, 1 / Real.sqrt (1 - t ^ 4)) =
      Real.Gamma (1 / 4) * Real.Gamma (1 / 2) := by
  let I : ℝ := ∫ u in Set.Ioo (0 : ℝ) 1, u ^ (-(3 : ℝ) / 4) * (1 - u) ^ (-(1 : ℝ) / 2)
  have hI_cast : (I : ℂ) = Complex.betaIntegral (1 / 4) (1 / 2) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    dsimp only [I]
    trans (∫ u in Set.Ioo (0 : ℝ) 1,
      ((u ^ (-(3 : ℝ) / 4) * (1 - u) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ))
    · exact (integral_ofReal (𝕜 := ℂ)).symm
    · refine MeasureTheory.setIntegral_congr_fun
        (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) 1)) ?_
      intro u hu
      dsimp only
      have hu0 : 0 ≤ u := hu.1.le
      have hu1 : 0 ≤ 1 - u := by linarith [hu.2]
      rw [Complex.ofReal_mul, Complex.ofReal_cpow hu0, Complex.ofReal_cpow hu1, Complex.ofReal_sub,
        Complex.ofReal_one]
      have he1 : ((-(3 : ℝ) / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) - 1 := by norm_num
      have he2 : ((-(1 : ℝ) / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) - 1 := by norm_num
      rw [he1, he2]
  have hbeta :
      Complex.Gamma (1 / 4 : ℂ) * Complex.Gamma (1 / 2 : ℂ) =
        Complex.Gamma ((1 / 4 : ℂ) + (1 / 2 : ℂ)) * Complex.betaIntegral (1 / 4) (1 / 2) :=
    Complex.Gamma_mul_Gamma_eq_betaIntegral (by norm_num) (by norm_num)
  have hc14 : ((1 / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) := by norm_num
  have hc12 : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  have hc34 : ((3 / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) + (1 / 2 : ℂ) := by norm_num
  have hEqC :
      ((Real.Gamma (1 / 4) * Real.Gamma (1 / 2) : ℝ) : ℂ) =
        ((Real.Gamma (3 / 4) * I : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_mul, ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal,
      ← Complex.Gamma_ofReal, hc14, hc12, hc34, hI_cast]
    exact hbeta
  have hEqR : Real.Gamma (1 / 4) * Real.Gamma (1 / 2) = Real.Gamma (3 / 4) * I :=
    Complex.ofReal_injective hEqC
  have hI_val : I = 4 * ∫ t in Set.Ioo (0 : ℝ) 1, 1 / Real.sqrt (1 - t ^ 4) :=
    beta_integral_eq_four_mul_lemniscate
  rw [hI_val] at hEqR
  linarith

lemma gamma_one_fourth_pow_four_eq :
    Real.Gamma (1 / 4) ^ 4 =
      32 * Real.pi * (∫ x in Set.Ioi (1 : ℝ), 1 / Real.sqrt (4 * x ^ 3 - 4 * x)) ^ 2 := by
  set ω₁ : ℝ := ∫ x in Set.Ioi (1 : ℝ), 1 / Real.sqrt (4 * x ^ 3 - 4 * x)
  have h1 : 4 * Real.Gamma (3 / 4) * ω₁ = Real.Gamma (1 / 4) * Real.Gamma (1 / 2) := by
    simpa only [ω₁, weierstrass_integral_eq_lemniscate] using
      four_mul_gamma_three_fourths_mul_lemniscate
  have hrefl : Real.Gamma (1 / 4) * Real.Gamma (3 / 4) = Real.pi * Real.sqrt 2 := by
    have h := Real.Gamma_mul_Gamma_one_sub (1 / 4 : ℝ)
    rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num,
      show Real.pi * (1 / 4 : ℝ) = Real.pi / 4 by ring, Real.sin_pi_div_four] at h
    rw [h]
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hpos2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    field_simp
    nlinarith
  have hhalf : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have h2 : 4 * (Real.pi * Real.sqrt 2) * ω₁ = Real.Gamma (1 / 4) ^ 2 * Real.sqrt Real.pi := by
    calc
      4 * (Real.pi * Real.sqrt 2) * ω₁
          = 4 * (Real.Gamma (1 / 4) * Real.Gamma (3 / 4)) * ω₁ := by rw [hrefl]
      _ = Real.Gamma (1 / 4) * (4 * Real.Gamma (3 / 4) * ω₁) := by ring
      _ = Real.Gamma (1 / 4) * (Real.Gamma (1 / 4) * Real.Gamma (1 / 2)) := by rw [h1]
      _ = Real.Gamma (1 / 4) ^ 2 * Real.sqrt Real.pi := by rw [hhalf]; ring
  have hsq :
      (4 * (Real.pi * Real.sqrt 2) * ω₁) ^ 2 = (Real.Gamma (1 / 4) ^ 2 * Real.sqrt Real.pi) ^ 2 :=
    congrArg (fun x : ℝ => x ^ 2) h2
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hmul : Real.pi * Real.Gamma (1 / 4) ^ 4 = Real.pi * (32 * Real.pi * ω₁ ^ 2) := by
    calc
      Real.pi * Real.Gamma (1 / 4) ^ 4
          = Real.Gamma (1 / 4) ^ 4 * Real.sqrt Real.pi ^ 2 := by rw [hsqpi]; ring
      _ = (Real.Gamma (1 / 4) ^ 2 * Real.sqrt Real.pi) ^ 2 := by ring
      _ = (4 * (Real.pi * Real.sqrt 2) * ω₁) ^ 2 := hsq.symm
      _ = 16 * Real.pi ^ 2 * Real.sqrt 2 ^ 2 * ω₁ ^ 2 := by ring
      _ = 16 * Real.pi ^ 2 * 2 * ω₁ ^ 2 := by rw [hsq2]
      _ = Real.pi * (32 * Real.pi * ω₁ ^ 2) := by ring
  exact mul_left_cancel₀ Real.pi_ne_zero hmul

lemma poly_ne_zero_of_cubic_linear (q : ℚ) :
    MvPolynomial.C (128 : ℚ) * (MvPolynomial.X (0 : Fin 2)) ^ 3 * MvPolynomial.X (1 : Fin 2) -
      MvPolynomial.C (q ^ 4) ≠ 0 := by
  intro hP
  let m : Fin 2 →₀ ℕ := Finsupp.single 0 3 + Finsupp.single 1 1
  have hm0 : m ≠ 0 := by
    intro h0
    have hval : m 0 = 0 := by simp [h0]
    simp [m] at hval
  have hterm :
      MvPolynomial.C (128 : ℚ) * (MvPolynomial.X (0 : Fin 2)) ^ 3 * MvPolynomial.X (1 : Fin 2) =
        MvPolynomial.monomial m 128 := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X, MvPolynomial.C_mul_monomial,
      MvPolynomial.monomial_mul, mul_one, mul_one]
  have hcoeff := congrArg (MvPolynomial.coeff m) hP
  rw [MvPolynomial.coeff_sub, hterm, MvPolynomial.coeff_monomial, MvPolynomial.coeff_C,
    MvPolynomial.coeff_zero] at hcoeff
  simp [hm0.symm] at hcoeff

theorem main : H1 → H2 → type_of% @Constant7b.irrational_gamma_one_div_four := by
  intro h1 h2
  rcases h1 with ⟨ζ_W, η₁, hdiff, htend, hper1, hper2, hode, hleg⟩
  have hindep :
      AlgebraicIndependent ℚ
        ![∫ x in Set.Ioi (1 : ℝ), 1 / Real.sqrt (4 * x ^ 3 - 4 * x), η₁] :=
    h2 ζ_W η₁ hdiff htend hper1 hper2 hode
  set ω₁ : ℝ := ∫ x in Set.Ioi (1 : ℝ), 1 / Real.sqrt (4 * x ^ 3 - 4 * x)
  have hgamma4 : Real.Gamma (1 / 4) ^ 4 = 128 * ω₁ ^ 3 * η₁ := by
    have hg := gamma_one_fourth_pow_four_eq
    have hpi : Real.pi = 4 * ω₁ * η₁ := by linarith
    calc
      Real.Gamma (1 / 4) ^ 4 = 32 * Real.pi * ω₁ ^ 2 := hg
      _ = 32 * (4 * ω₁ * η₁) * ω₁ ^ 2 := by rw [hpi]
      _ = 128 * ω₁ ^ 3 * η₁ := by ring
  rintro ⟨q, hq⟩
  let P : MvPolynomial (Fin 2) ℚ :=
    MvPolynomial.C (128 : ℚ) * (MvPolynomial.X (0 : Fin 2)) ^ 3 * MvPolynomial.X (1 : Fin 2) -
      MvPolynomial.C (q ^ 4)
  have heval : MvPolynomial.aeval ![ω₁, η₁] P = 0 := by
    simp only [P, map_sub, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, eq_ratCast]
    push_cast
    rw [hq, hgamma4]
    ring
  exact poly_ne_zero_of_cubic_linear q (algebraicIndependent_iff.mp hindep P heval)

end OMA.R_Constant7b_irrational_gamma_one_div_four_R1

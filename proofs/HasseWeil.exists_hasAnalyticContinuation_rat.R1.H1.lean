import OMAReductions.R_HasseWeil_exists_hasAnalyticContinuation_rat_R1
import Mathlib

/-!
# Analyticity of the L-series of a rational elliptic curve on `Re s > 3/2` (`HasseWeil.R1.H1`)

We prove `AnalyticOnNhd ℂ E.LSeries {s | 3 / 2 < s.re}` for every `E : WeierstrassCurve ℚ`:
1. **Local Euler factor coefficient bounds (`PowerSeries.invOfUnit`):**
   - Trivial bound: if `|a| ≤ p`, the inverse of `1 - a T + p T^2` has `|u_k| ≤ (k + 1) * p^k`.
   - Weak Hasse bound: if `|a| ≤ M * √p` (`M ≥ 1`), then `|u_k| ≤ ((M + 1) * √p)^k`.
2. **Trivial affine point-count bound:** For any `W : WeierstrassCurve κ` over any finite field `κ`
   of cardinality `p`, each `x : κ` admits at most 2 solutions `y` to `W.Equation x y`, so
   `1 ≤ Nat.card W.toAffine.Point ≤ 2 * p + 1` and `|p + 1 - Nat.card W.toAffine.Point| ≤ p`.
3. **Stepanov's polynomial method (weak Hasse bound for `p ≥ 900`):**
   - For any finite field `κ` of prime cardinality `p ≥ 900` and any cubic `f : κ[X]` of degree `3`,
     constructing a nonzero `Q(X) = A(X) + B(X) * f(X)^((p - 1)/2)` with `K = ⌊√p⌋`, `L = ⌊p/4⌋`,
     `M = 2K - 26 < p` vanishing to order `M` on `S_ε = {x | (f.eval x)^((p-1)/2) = ε}` (using
     ordinary `Polynomial.derivative` since `M < p`) yields `2 * M * |S_ε| ≤ M * p + 28 * p`.
   - Completing the square in `y` turns `W.Equation x y` into `u^2 = f(x)` with `f.natDegree = 3`
     and at most `3` singular points, giving `|p + 1 - Nat.card W.toAffine.Point| ≤ 35 * √p`.
4. **Euler product over `HeightOneSpectrum (𝓞 ℚ)` and `LSeries_analyticOnNhd`:**
   - Via `Rat.HeightOneSpectrum.primesEquiv`, `padicIntEquiv`, and `PadicInt.residueField`,
     each local Euler factor has prime base `p`, `E.LFunction` is multiplicative, and
     `E.LFunction (p^k)` equals the `k`-th coefficient of the `p`-adic local power series.
   - Majorizing finite partial sums of `∑ |E.LFunction n| / n^σ` by the Euler product shows
     `LSeriesSummable ((↑) ∘ E.LFunction) σ` for every real `σ > 3 / 2`, whence
     `LSeries.abscissaOfAbsConv ((↑) ∘ E.LFunction) ≤ 3 / 2` and `LSeries_analyticOnNhd` finishes.

Credit: @yhay81
-/

namespace HasseWeilR1H1

open Polynomial Finset BigOperators
open scoped Classical

/- ### Part 1: Coefficient bounds for `PowerSeries.invOfUnit` -/

private lemma coeff_invOfUnit_one (k : ℕ) :
    |((PowerSeries.coeff k (PowerSeries.invOfUnit (1 : PowerSeries ℤ) 1) : ℤ) : ℝ)| ≤ 1 := by
  have hmul : (1 : PowerSeries ℤ) * PowerSeries.invOfUnit (1 : PowerSeries ℤ) 1 = 1 :=
    PowerSeries.mul_invOfUnit (1 : PowerSeries ℤ) 1 (by simp)
  rw [one_mul] at hmul
  rw [hmul]
  cases k with
  | zero => simp
  | succ m => simp

private lemma coeff_invOfUnit_one_sub_X (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.invOfUnit (1 - PowerSeries.X : PowerSeries ℤ) 1) = 1 := by
  set g := PowerSeries.invOfUnit (1 - PowerSeries.X : PowerSeries ℤ) 1
  have hmul : (1 - PowerSeries.X : PowerSeries ℤ) * g = 1 :=
    PowerSeries.mul_invOfUnit _ 1 (by simp)
  induction k with
  | zero =>
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    exact PowerSeries.constantCoeff_invOfUnit _ 1
  | succ m ih =>
    have hc := congrArg (PowerSeries.coeff (m + 1)) hmul
    rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one] at hc
    simp only [Nat.succ_ne_zero, ↓reduceIte] at hc
    omega

private lemma coeff_invOfUnit_one_add_X (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.invOfUnit (1 + PowerSeries.X : PowerSeries ℤ) 1) = (-1 : ℤ) ^ k := by
  set g := PowerSeries.invOfUnit (1 + PowerSeries.X : PowerSeries ℤ) 1
  have hmul : (1 + PowerSeries.X : PowerSeries ℤ) * g = 1 :=
    PowerSeries.mul_invOfUnit _ 1 (by simp)
  induction k with
  | zero =>
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    exact PowerSeries.constantCoeff_invOfUnit _ 1
  | succ m ih =>
    have hc := congrArg (PowerSeries.coeff (m + 1)) hmul
    rw [add_mul, one_mul, map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one] at hc
    simp only [Nat.succ_ne_zero, ↓reduceIte] at hc
    rw [ih] at hc
    rw [pow_succ]
    linarith

private lemma coeff_invOfUnit_quad_rec (a q : ℤ) :
    let φ : PowerSeries ℤ := ((1 - C a * X + C q * X ^ 2 : ℤ[X]) : PowerSeries ℤ)
    let g := PowerSeries.invOfUnit φ 1
    PowerSeries.coeff 0 g = 1 ∧
    PowerSeries.coeff 1 g = a ∧
    ∀ k : ℕ, PowerSeries.coeff (k + 2) g =
      a * PowerSeries.coeff (k + 1) g - q * PowerSeries.coeff k g := by
  intro φ g
  have hφ : φ = 1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C q * PowerSeries.X ^ 2 := by
    dsimp only [φ]
    rw [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_mul,
      Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_C]
    simp
  have hconst : PowerSeries.constantCoeff φ = 1 := by
    rw [hφ]; simp
  have hmul : φ * g = 1 := PowerSeries.mul_invOfUnit φ 1 hconst
  have hg0 : PowerSeries.coeff 0 g = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    exact PowerSeries.constantCoeff_invOfUnit φ 1
  have hX2 : ∀ n : ℕ, PowerSeries.coeff (n + 2) (PowerSeries.X ^ 2 * g) = PowerSeries.coeff n g := by
    intro n
    rw [pow_two, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
  have hX2_1 : PowerSeries.coeff 1 (PowerSeries.X ^ 2 * g) = 0 := by
    rw [pow_two, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul]
  have hg1 : PowerSeries.coeff 1 g = a := by
    have hc := congrArg (PowerSeries.coeff 1) hmul
    rw [hφ, add_mul, sub_mul, one_mul, mul_assoc, mul_assoc, map_add, map_sub,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, hX2_1,
      PowerSeries.coeff_one] at hc
    simp only [Nat.one_ne_zero, ↓reduceIte, mul_zero, add_zero, hg0, mul_one] at hc
    omega
  refine ⟨hg0, hg1, fun k => ?_⟩
  have hc := congrArg (PowerSeries.coeff (k + 2)) hmul
  rw [hφ, add_mul, sub_mul, one_mul, mul_assoc, mul_assoc, map_add, map_sub,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, hX2 k,
    PowerSeries.coeff_one] at hc
  simp only [show k + 2 ≠ 0 by omega, ↓reduceIte] at hc
  linarith

private lemma quad_seq_eq_sum_roots {u : ℕ → ℤ} {a q : ℤ} {α β : ℂ}
    (hu0 : u 0 = 1) (hu1 : u 1 = a) (hrec : ∀ k, u (k + 2) = a * u (k + 1) - q * u k)
    (hsum : α + β = (a : ℂ)) (hprod : α * β = (q : ℂ)) :
    ∀ k : ℕ, (u k : ℂ) = ∑ j ∈ Finset.range (k + 1), α ^ j * β ^ (k - j) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [hu0]
    | 1 =>
      rw [hu1, Finset.sum_range_succ, Finset.sum_range_one]
      simp [← hsum, add_comm]
    | m + 2 =>
      have hm1 := ih (m + 1) (by omega)
      have hm0 := ih m (by omega)
      have hcast : (u (m + 2) : ℂ) = (a : ℂ) * (u (m + 1) : ℂ) - (q : ℂ) * (u m : ℂ) := by
        exact_mod_cast hrec m
      rw [hcast, hm1, hm0, ← hsum, ← hprod]
      have h1 : α * ∑ j ∈ Finset.range (m + 2), α ^ j * β ^ (m + 1 - j) =
          ∑ j ∈ Finset.range (m + 2), α ^ (j + 1) * β ^ (m + 1 - j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_succ]; ring
      have h2 : β * ∑ j ∈ Finset.range (m + 2), α ^ j * β ^ (m + 1 - j) =
          β ^ (m + 2) + α * β * ∑ j ∈ Finset.range (m + 1), α ^ j * β ^ (m - j) := by
        rw [Finset.sum_range_succ', mul_add, Finset.mul_sum]
        simp only [pow_zero, one_mul, Nat.sub_zero]
        rw [add_comm]
        congr 1
        · rw [pow_succ]; ring
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hsub : m + 1 - (j + 1) = m - j := by omega
          rw [hsub, pow_succ]; ring
      have h3 : ∑ j ∈ Finset.range (m + 3), α ^ j * β ^ (m + 2 - j) =
          β ^ (m + 2) + ∑ j ∈ Finset.range (m + 2), α ^ (j + 1) * β ^ (m + 1 - j) := by
        rw [Finset.sum_range_succ']
        simp only [pow_zero, one_mul, Nat.sub_zero]
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        have hsub : m + 2 - (j + 1) = m + 1 - j := by omega
        rw [hsub]
      rw [add_mul, h1, h2, h3]
      ring

private lemma quad_seq_bound_trivial {u : ℕ → ℤ} {a : ℤ} {p : ℕ}
    (hp : 1 ≤ p) (ha : |a| ≤ (p : ℤ))
    (hu0 : u 0 = 1) (hu1 : u 1 = a) (hrec : ∀ k, u (k + 2) = a * u (k + 1) - (p : ℤ) * u k)
    (k : ℕ) :
    |(u k : ℝ)| ≤ ((k + 1 : ℕ) : ℝ) * (p : ℝ) ^ k := by
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have haR : |(a : ℝ)| ≤ (p : ℝ) := by exact_mod_cast ha
  have hex : ∃ α β : ℂ, α + β = (a : ℂ) ∧ α * β = ((p : ℤ) : ℂ) ∧
      ‖α‖ ≤ (p : ℝ) ∧ ‖β‖ ≤ (p : ℝ) := by
    by_cases hdisc : (a : ℝ) ^ 2 ≤ 4 * (p : ℝ)
    · let d : ℝ := Real.sqrt (4 * (p : ℝ) - (a : ℝ) ^ 2)
      have hd_sq : d ^ 2 = 4 * (p : ℝ) - (a : ℝ) ^ 2 := Real.sq_sqrt (by linarith)
      let α : ℂ := ((a : ℝ) / 2 : ℝ) + Complex.I * ((d / 2 : ℝ) : ℂ)
      let β : ℂ := ((a : ℝ) / 2 : ℝ) - Complex.I * ((d / 2 : ℝ) : ℂ)
      have hα_re : α.re = (a : ℝ) / 2 := by simp [α]
      have hα_im : α.im = d / 2 := by simp [α]
      have hβ_re : β.re = (a : ℝ) / 2 := by simp [β]
      have hβ_im : β.im = -(d / 2) := by simp [β]
      have hnorm_sq : ‖α‖ ^ 2 = (p : ℝ) := by
        rw [Complex.sq_norm, Complex.normSq_apply, hα_re, hα_im]
        nlinarith [hd_sq]
      have hnorm_sqβ : ‖β‖ ^ 2 = (p : ℝ) := by
        rw [Complex.sq_norm, Complex.normSq_apply, hβ_re, hβ_im]
        nlinarith [hd_sq]
      have hα_le : ‖α‖ ≤ (p : ℝ) := by
        nlinarith [norm_nonneg α, hnorm_sq, hpR]
      have hβ_le : ‖β‖ ≤ (p : ℝ) := by
        nlinarith [norm_nonneg β, hnorm_sqβ, hpR]
      refine ⟨α, β, ?_, ?_, hα_le, hβ_le⟩
      · apply Complex.ext <;> simp [hα_re, hβ_re, hα_im, hβ_im]
      · apply Complex.ext
        · simp only [Complex.mul_re, hα_re, hβ_re, hα_im, hβ_im, Int.cast_natCast,
            Complex.natCast_re]
          nlinarith [hd_sq]
        · simp only [Complex.mul_im, hα_re, hβ_re, hα_im, hβ_im, Complex.intCast_im]
          ring
    · push Not at hdisc
      let d : ℝ := Real.sqrt ((a : ℝ) ^ 2 - 4 * (p : ℝ))
      have hd_nn : 0 ≤ d := Real.sqrt_nonneg _
      have hd_sq : d ^ 2 = (a : ℝ) ^ 2 - 4 * (p : ℝ) := Real.sq_sqrt (by linarith)
      have hd_le : d ≤ |(a : ℝ)| := by
        have hsq : d ^ 2 ≤ |(a : ℝ)| ^ 2 := by
          rw [sq_abs, hd_sq]; linarith
        nlinarith [abs_nonneg (a : ℝ)]
      let αR : ℝ := ((a : ℝ) + d) / 2
      let βR : ℝ := ((a : ℝ) - d) / 2
      have hαR : |αR| ≤ (p : ℝ) := by
        have h1 : |αR| ≤ (|(a : ℝ)| + |d|) / 2 := by
          dsimp [αR]
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
        rw [abs_of_nonneg hd_nn] at h1
        linarith
      have hβR : |βR| ≤ (p : ℝ) := by
        have h1 : |βR| ≤ (|(a : ℝ)| + |d|) / 2 := by
          dsimp [βR]
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact div_le_div_of_nonneg_right (abs_sub _ _) (by norm_num)
        rw [abs_of_nonneg hd_nn] at h1
        linarith
      refine ⟨(αR : ℂ), (βR : ℂ), ?_, ?_, ?_, ?_⟩
      · apply Complex.ext
        · simp [αR, βR]; ring
        · simp
      · apply Complex.ext
        · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Int.cast_natCast,
            Complex.natCast_re, mul_zero, sub_zero]
          dsimp [αR, βR]; nlinarith [hd_sq]
        · simp
      · simpa [Complex.norm_real] using hαR
      · simpa [Complex.norm_real] using hβR
  obtain ⟨α, β, hsum, hprod, hα, hβ⟩ := hex
  have hformula := quad_seq_eq_sum_roots hu0 hu1 hrec hsum hprod k
  have hnorm_eq : |(u k : ℝ)| = ‖(u k : ℂ)‖ := by
    rw [Complex.norm_intCast]
  rw [hnorm_eq, hformula]
  calc
    ‖∑ j ∈ Finset.range (k + 1), α ^ j * β ^ (k - j)‖
        ≤ ∑ j ∈ Finset.range (k + 1), ‖α ^ j * β ^ (k - j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (k + 1), (p : ℝ) ^ k := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          rw [norm_mul, norm_pow, norm_pow]
          calc
            ‖α‖ ^ j * ‖β‖ ^ (k - j)
                ≤ (p : ℝ) ^ j * (p : ℝ) ^ (k - j) :=
                  mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hα j)
                    (pow_le_pow_left₀ (norm_nonneg _) hβ (k - j))
                    (pow_nonneg (norm_nonneg _) _) (pow_nonneg (by linarith) _)
            _ = (p : ℝ) ^ (j + (k - j)) := (pow_add _ _ _).symm
            _ = (p : ℝ) ^ k := by rw [Nat.add_sub_cancel' hjk]
    _ = ((k + 1 : ℕ) : ℝ) * (p : ℝ) ^ k := by simp

private lemma quad_seq_bound_hasse {u : ℕ → ℤ} {a : ℤ} {p : ℕ} {M : ℝ}
    (hM : 1 ≤ M) (ha : |(a : ℝ)| ≤ M * Real.sqrt (p : ℝ))
    (hu0 : u 0 = 1) (hu1 : u 1 = a) (hrec : ∀ k, u (k + 2) = a * u (k + 1) - (p : ℤ) * u k)
    (k : ℕ) :
    |(u k : ℝ)| ≤ ((M + 1) * Real.sqrt (p : ℝ)) ^ k := by
  have hs_nn : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hs_sq : (Real.sqrt (p : ℝ)) ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  have hbase_nn : 0 ≤ (M + 1) * Real.sqrt (p : ℝ) := by positivity
  induction k using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [hu0]
    | 1 =>
      rw [hu1, pow_one]
      nlinarith [ha, hs_nn]
    | m + 2 =>
      have hm1 := ih (m + 1) (by omega)
      have hm0 := ih m (by omega)
      have hcast : (u (m + 2) : ℝ) = (a : ℝ) * (u (m + 1) : ℝ) - (p : ℝ) * (u m : ℝ) := by
        exact_mod_cast hrec m
      rw [hcast]
      have htri : |(a : ℝ) * (u (m + 1) : ℝ) - (p : ℝ) * (u m : ℝ)| ≤
          |(a : ℝ)| * |(u (m + 1) : ℝ)| + (p : ℝ) * |(u m : ℝ)| := by
        calc
          |(a : ℝ) * (u (m + 1) : ℝ) - (p : ℝ) * (u m : ℝ)|
              ≤ |(a : ℝ) * (u (m + 1) : ℝ)| + |(p : ℝ) * (u m : ℝ)| := abs_sub _ _
          _ = |(a : ℝ)| * |(u (m + 1) : ℝ)| + (p : ℝ) * |(u m : ℝ)| := by
                rw [abs_mul, abs_mul, abs_of_nonneg (a := (p : ℝ)) (Nat.cast_nonneg p)]
      have h1 : |(a : ℝ)| * |(u (m + 1) : ℝ)| ≤
          (M * Real.sqrt (p : ℝ)) * ((M + 1) * Real.sqrt (p : ℝ)) ^ (m + 1) :=
        mul_le_mul ha hm1 (abs_nonneg _) (by positivity)
      have h2 : (p : ℝ) * |(u m : ℝ)| ≤ (p : ℝ) * ((M + 1) * Real.sqrt (p : ℝ)) ^ m :=
        mul_le_mul_of_nonneg_left hm0 (Nat.cast_nonneg p)
      have hcomb :
          (M * Real.sqrt (p : ℝ)) * ((M + 1) * Real.sqrt (p : ℝ)) ^ (m + 1) +
            (p : ℝ) * ((M + 1) * Real.sqrt (p : ℝ)) ^ m =
          (M * (M + 1) + 1) * (p : ℝ) * ((M + 1) * Real.sqrt (p : ℝ)) ^ m := by
        rw [pow_succ]
        have hsq : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) := by
          rw [← sq, hs_sq]
        calc
          M * Real.sqrt (p : ℝ) * (((M + 1) * Real.sqrt (p : ℝ)) ^ m * ((M + 1) * Real.sqrt (p : ℝ))) +
              (p : ℝ) * ((M + 1) * Real.sqrt (p : ℝ)) ^ m
              = (M * (M + 1) * (Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ)) + (p : ℝ)) *
                  ((M + 1) * Real.sqrt (p : ℝ)) ^ m := by ring
          _ = (M * (M + 1) + 1) * (p : ℝ) * ((M + 1) * Real.sqrt (p : ℝ)) ^ m := by
                rw [hsq]; ring
      have hgoal_eq : ((M + 1) * Real.sqrt (p : ℝ)) ^ (m + 2) =
          (M + 1) ^ 2 * (p : ℝ) * ((M + 1) * Real.sqrt (p : ℝ)) ^ m := by
        rw [pow_add, pow_two]
        have hsq : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) := by
          rw [← sq, hs_sq]
        calc
          ((M + 1) * Real.sqrt (p : ℝ)) ^ m * (((M + 1) * Real.sqrt (p : ℝ)) * ((M + 1) * Real.sqrt (p : ℝ)))
              = (M + 1) ^ 2 * (Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ)) *
                  ((M + 1) * Real.sqrt (p : ℝ)) ^ m := by ring
          _ = (M + 1) ^ 2 * (p : ℝ) * ((M + 1) * Real.sqrt (p : ℝ)) ^ m := by rw [hsq]
      rw [hgoal_eq]
      have hcoeff : M * (M + 1) + 1 ≤ (M + 1) ^ 2 := by nlinarith
      have htail : (M * (M + 1) + 1) * (p : ℝ) * ((M + 1) * Real.sqrt (p : ℝ)) ^ m ≤
          (M + 1) ^ 2 * (p : ℝ) * ((M + 1) * Real.sqrt (p : ℝ)) ^ m := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hbase_nn m)
        exact mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg p)
      linarith

/- ### Part 2: Trivial point-count bound on `WeierstrassCurve.Affine.Point` -/

private lemma card_equation_fiber_le_two {κ : Type*} [Field κ] [Fintype κ] [DecidableEq κ]
    (W : WeierstrassCurve κ) (x : κ) :
    (Finset.univ.filter (fun y : κ => W.toAffine.Equation x y)).card ≤ 2 := by
  let S : Finset κ := Finset.univ.filter (fun y : κ => W.toAffine.Equation x y)
  by_cases hne : S.Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have heq₀ : y₀ ^ 2 + W.a₁ * x * y₀ + W.a₃ * y₀ =
        x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
      (W.toAffine.equation_iff x y₀).mp (Finset.mem_filter.mp hy₀).2
    have hsub : S ⊆ {y₀, -y₀ - W.a₁ * x - W.a₃} := by
      intro y hy
      have heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y =
          x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
        (W.toAffine.equation_iff x y).mp (Finset.mem_filter.mp hy).2
      have hprod : (y - y₀) * (y + y₀ + W.a₁ * x + W.a₃) = 0 := by
        linear_combination heq - heq₀
      rcases mul_eq_zero.mp hprod with h1 | h2
      · exact Finset.mem_insert.mpr (Or.inl (sub_eq_zero.mp h1))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (by linear_combination h2)))
    calc S.card ≤ ({y₀, -y₀ - W.a₁ * x - W.a₃} : Finset κ).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  · change S.card ≤ 2
    rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp

private lemma card_point_eq_one_add {κ : Type*} [Field κ] [Fintype κ] [DecidableEq κ]
    (W : WeierstrassCurve κ) :
    Nat.card W.toAffine.Point =
      1 + (Finset.univ.filter (fun xy : κ × κ => W.toAffine.Nonsingular xy.1 xy.2)).card := by
  classical
  have heq : Nat.card W.toAffine.Point =
      Nat.card (Option {xy : κ × κ // W.toAffine.Nonsingular xy.1 xy.2}) :=
    Nat.card_congr W.toAffine.nonsingularPointEquiv
  rw [heq, Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_subtype]
  omega

private lemma trivial_trace_bound {κ : Type*} [Field κ] [Fintype κ] [DecidableEq κ]
    (W : WeierstrassCurve κ) :
    |(Fintype.card κ : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ)| ≤ (Fintype.card κ : ℤ) := by
  classical
  rw [card_point_eq_one_add W]
  have hsub : (Finset.univ.filter (fun xy : κ × κ => W.toAffine.Nonsingular xy.1 xy.2)) ⊆
      (Finset.univ.filter (fun xy : κ × κ => W.toAffine.Equation xy.1 xy.2)) := by
    intro xy hxy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hxy).2.1⟩
  have hle_eq : (Finset.univ.filter (fun xy : κ × κ => W.toAffine.Equation xy.1 xy.2)).card ≤
      2 * Fintype.card κ := by
    have hcard_eq : (Finset.univ.filter (fun xy : κ × κ => W.toAffine.Equation xy.1 xy.2)).card =
        ∑ x : κ, (Finset.univ.filter (fun y : κ => W.toAffine.Equation x y)).card := by
      rw [← Finset.card_sigma]
      refine Finset.card_bij (fun xy _ => ⟨xy.1, xy.2⟩) ?_ ?_ ?_
      · intro xy hxy
        exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hxy).2⟩⟩
      · intro a _ b _ h
        cases a; cases b; simp only [Sigma.mk.injEq, heq_eq_eq] at h
        exact Prod.ext h.1 h.2
      · intro s hs
        refine ⟨(s.1, s.2), ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp (Finset.mem_sigma.mp hs).2).2⟩
    rw [hcard_eq]
    calc ∑ x : κ, (Finset.univ.filter (fun y : κ => W.toAffine.Equation x y)).card
        ≤ ∑ _x : κ, 2 := Finset.sum_le_sum fun x _ => card_equation_fiber_le_two W x
      _ = 2 * Fintype.card κ := by simp [mul_comm]
  have hns_le : (Finset.univ.filter (fun xy : κ × κ => W.toAffine.Nonsingular xy.1 xy.2)).card ≤
      2 * Fintype.card κ := (Finset.card_le_card hsub).trans hle_eq
  rw [abs_le]
  omega

/- ### Part 3: Stepanov's polynomial method (weak Hasse bound for `p ≥ 900`) -/

private lemma charP_of_card_prime {κ : Type*} [Field κ] [Fintype κ] {p : ℕ}
    (hp : p.Prime) (hcard : Fintype.card κ = p) : CharP κ p := by
  have hdvd : addOrderOf (1 : κ) ∣ p := by
    rw [← hcard]
    exact addOrderOf_dvd_card
  have hne1 : addOrderOf (1 : κ) ≠ 1 := by
    intro h1
    have h0 := addOrderOf_nsmul_eq_zero (1 : κ)
    rw [h1, one_nsmul] at h0
    exact one_ne_zero h0
  have hord : addOrderOf (1 : κ) = p := (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
  refine ⟨fun n => ?_⟩
  rw [← nsmul_one, ← addOrderOf_dvd_iff_nsmul_eq_zero, hord]

private lemma euler_criterion_field {κ : Type*} [Field κ] [Fintype κ] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hcard : Fintype.card κ = p) {a : κ} (ha : a ≠ 0) :
    (a ^ ((p - 1) / 2) = 1 ∨ a ^ ((p - 1) / 2) = -1) ∧
    ((∃ y : κ, y ^ 2 = a) ↔ a ^ ((p - 1) / 2) = 1) := by
  have hodd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  have h2h : 2 * ((p - 1) / 2) = p - 1 := by omega
  have hpow1 : a ^ (p - 1) = 1 := by
    rw [← hcard]
    exact FiniteField.pow_card_sub_one_eq_one a ha
  have hsq1 : (a ^ ((p - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, h2h, hpow1]
  refine ⟨sq_eq_one_iff.mp hsq1, ?_, ?_⟩
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by intro h; subst h; simp at ha
    rw [← pow_mul, h2h, ← hcard]
    exact FiniteField.pow_card_sub_one_eq_one y hy
  · intro h1
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := κˣ)
    have hcard_u : Fintype.card κˣ = p - 1 := by rw [Fintype.card_units, hcard]
    have hord_g : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard_u]
    obtain ⟨z, hz⟩ := hg (Units.mk0 a ha)
    have hp1_pos : (0 : ℤ) < ((p - 1 : ℕ) : ℤ) := by have := hp.two_le; omega
    let m : ℕ := (z % ((p - 1 : ℕ) : ℤ)).toNat
    have hm_cast : (m : ℤ) = z % ((p - 1 : ℕ) : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg z hp1_pos.ne')
    have hgp1 : g ^ (p - 1) = 1 := hord_g ▸ pow_orderOf_eq_one g
    have hm : g ^ m = Units.mk0 a ha := by
      have hz_split : z = ((p - 1 : ℕ) : ℤ) * (z / ((p - 1 : ℕ) : ℤ)) + (m : ℤ) := by
        rw [hm_cast]; exact (Int.mul_ediv_add_emod z _).symm
      dsimp only at hz
      rw [← hz, hz_split, zpow_add, zpow_mul, zpow_natCast, hgp1, one_zpow, one_mul, zpow_natCast]
    have hgm : (g ^ (m * ((p - 1) / 2)) : κˣ) = 1 := by
      apply Units.ext
      rw [pow_mul, Units.val_pow_eq_pow_val, hm]
      simpa using h1
    have hdvd0 : orderOf g ∣ m * ((p - 1) / 2) := orderOf_dvd_of_pow_eq_one hgm
    rw [hord_g] at hdvd0
    have hdvd : 2 * ((p - 1) / 2) ∣ m * ((p - 1) / 2) := h2h.symm ▸ hdvd0
    have hh_pos : 0 < (p - 1) / 2 := by have := hp.two_le; omega
    have h2dvd : 2 ∣ m := (Nat.mul_dvd_mul_iff_right hh_pos).mp hdvd
    obtain ⟨t, ht⟩ := h2dvd
    refine ⟨((g ^ t : κˣ) : κ), ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, ← ht, hm]
    rfl

private lemma mul_derivative_pow {κ : Type*} [CommRing κ] (g : κ[X]) (r : ℕ) :
    g * derivative (g ^ r) = C (r : κ) * derivative g * g ^ r := by
  cases r with
  | zero => simp
  | succ m =>
    rw [derivative_pow_succ, pow_succ]
    push_cast
    ring

private noncomputable def stepU {κ : Type*} [CommRing κ] (f : κ[X]) (r : ℕ) (u : κ[X]) : κ[X] :=
  C 2 * f * derivative u - C ((2 * r : ℕ) : κ) * derivative f * u

private noncomputable def stepV {κ : Type*} [CommRing κ] (f : κ[X]) (r : ℕ) (v : κ[X]) : κ[X] :=
  C 2 * f * derivative v - C ((2 * r + 1 : ℕ) : κ) * derivative f * v

private noncomputable def iterU {κ : Type*} [CommRing κ] (f : κ[X]) : ℕ → κ[X] → κ[X]
  | 0, u => u
  | r + 1, u => stepU f r (iterU f r u)

private noncomputable def iterV {κ : Type*} [CommRing κ] (f : κ[X]) : ℕ → κ[X] → κ[X]
  | 0, v => v
  | r + 1, v => stepV f r (iterV f r v)

private lemma iterU_add {κ : Type*} [CommRing κ] (f : κ[X]) (r : ℕ) (u₁ u₂ : κ[X]) :
    iterU f r (u₁ + u₂) = iterU f r u₁ + iterU f r u₂ := by
  induction r with
  | zero => rfl
  | succ m ih =>
    simp only [iterU, ih, stepU, map_add]
    ring

private lemma iterV_add {κ : Type*} [CommRing κ] (f : κ[X]) (r : ℕ) (v₁ v₂ : κ[X]) :
    iterV f r (v₁ + v₂) = iterV f r v₁ + iterV f r v₂ := by
  induction r with
  | zero => rfl
  | succ m ih =>
    simp only [iterV, ih, stepV, map_add]
    ring

private lemma iterU_smul {κ : Type*} [CommRing κ] (f : κ[X]) (r : ℕ) (c : κ) (u : κ[X]) :
    iterU f r (c • u) = c • iterU f r u := by
  induction r with
  | zero => rfl
  | succ m ih =>
    simp only [iterU, ih, stepU, derivative_smul, smul_sub, mul_smul_comm]

private lemma iterV_smul {κ : Type*} [CommRing κ] (f : κ[X]) (r : ℕ) (c : κ) (v : κ[X]) :
    iterV f r (c • v) = c • iterV f r v := by
  induction r with
  | zero => rfl
  | succ m ih =>
    simp only [iterV, ih, stepV, derivative_smul, smul_sub, mul_smul_comm]

private lemma iterU_zero {κ : Type*} [CommRing κ] (f : κ[X]) (r : ℕ) :
    iterU f r 0 = 0 := by
  induction r with
  | zero => rfl
  | succ m ih => simp [iterU, ih, stepU]

private lemma iterV_zero {κ : Type*} [CommRing κ] (f : κ[X]) (r : ℕ) :
    iterV f r 0 = 0 := by
  induction r with
  | zero => rfl
  | succ m ih => simp [iterV, ih, stepV]

private lemma iterU_sum {κ : Type*} [CommRing κ] {ι : Type*} (f : κ[X]) (r : ℕ)
    (s : Finset ι) (u : ι → κ[X]) :
    iterU f r (∑ i ∈ s, u i) = ∑ i ∈ s, iterU f r (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [iterU_zero]
  | insert a t ha ih => rw [Finset.sum_insert ha, iterU_add, ih, Finset.sum_insert ha]

private lemma iterV_sum {κ : Type*} [CommRing κ] {ι : Type*} (f : κ[X]) (r : ℕ)
    (s : Finset ι) (v : ι → κ[X]) :
    iterV f r (∑ i ∈ s, v i) = ∑ i ∈ s, iterV f r (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [iterV_zero]
  | insert a t ha ih => rw [Finset.sum_insert ha, iterV_add, ih, Finset.sum_insert ha]

private lemma iterU_mul_X_pow_char {κ : Type*} [CommRing κ] {p : ℕ} [CharP κ p]
    (f : κ[X]) (r k : ℕ) (u : κ[X]) :
    iterU f r (u * X ^ (k * p)) = iterU f r u * X ^ (k * p) := by
  have hd : derivative (X ^ (k * p) : κ[X]) = 0 := by
    rw [derivative_X_pow, Nat.cast_mul, CharP.cast_eq_zero κ p, mul_zero, C_0, zero_mul]
  induction r with
  | zero => rfl
  | succ m ih =>
    simp only [iterU, ih, stepU, derivative_mul, hd, mul_zero, add_zero]
    ring

private lemma iterV_mul_X_pow_char {κ : Type*} [CommRing κ] {p : ℕ} [CharP κ p]
    (f : κ[X]) (r k : ℕ) (v : κ[X]) :
    iterV f r (v * X ^ (k * p)) = iterV f r v * X ^ (k * p) := by
  have hd : derivative (X ^ (k * p) : κ[X]) = 0 := by
    rw [derivative_X_pow, Nat.cast_mul, CharP.cast_eq_zero κ p, mul_zero, C_0, zero_mul]
  induction r with
  | zero => rfl
  | succ m ih =>
    simp only [iterV, ih, stepV, derivative_mul, hd, mul_zero, add_zero]
    ring

private lemma natDegree_stepU_le {κ : Type*} [CommRing κ] {f u : κ[X]} {d : ℕ}
    (hf : f.natDegree ≤ 3) (hu : u.natDegree ≤ d) (r : ℕ) :
    (stepU f r u).natDegree ≤ d + 2 := by
  unfold stepU
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · by_cases hdu : derivative u = 0
    · simp [hdu]
    · have h1 : (C 2 * f * derivative u).natDegree ≤ (C 2 * f).natDegree + (derivative u).natDegree :=
        natDegree_mul_le
      have h2 : (C 2 * f).natDegree ≤ 3 := (natDegree_C_mul_le 2 f).trans hf
      have h3 : (derivative u).natDegree ≤ u.natDegree - 1 := natDegree_derivative_le u
      have hu_pos : 1 ≤ u.natDegree := by
        by_contra h0
        have hu0 : u.natDegree = 0 := by omega
        have : derivative u = 0 := by
          rw [eq_C_of_natDegree_eq_zero hu0, derivative_C]
        exact hdu this
      omega
  · have h1 : (C ((2 * r : ℕ) : κ) * derivative f * u).natDegree ≤
        (C ((2 * r : ℕ) : κ) * derivative f).natDegree + u.natDegree := natDegree_mul_le
    have h2 : (C ((2 * r : ℕ) : κ) * derivative f).natDegree ≤ (derivative f).natDegree :=
      natDegree_C_mul_le _ _
    have h3 : (derivative f).natDegree ≤ f.natDegree - 1 := natDegree_derivative_le f
    omega

private lemma natDegree_stepV_le {κ : Type*} [CommRing κ] {f v : κ[X]} {d : ℕ}
    (hf : f.natDegree ≤ 3) (hv : v.natDegree ≤ d) (r : ℕ) :
    (stepV f r v).natDegree ≤ d + 2 := by
  unfold stepV
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · by_cases hdv : derivative v = 0
    · simp [hdv]
    · have h1 : (C 2 * f * derivative v).natDegree ≤ (C 2 * f).natDegree + (derivative v).natDegree :=
        natDegree_mul_le
      have h2 : (C 2 * f).natDegree ≤ 3 := (natDegree_C_mul_le 2 f).trans hf
      have h3 : (derivative v).natDegree ≤ v.natDegree - 1 := natDegree_derivative_le v
      have hv_pos : 1 ≤ v.natDegree := by
        by_contra h0
        have hv0 : v.natDegree = 0 := by omega
        have : derivative v = 0 := by
          rw [eq_C_of_natDegree_eq_zero hv0, derivative_C]
        exact hdv this
      omega
  · have h1 : (C ((2 * r + 1 : ℕ) : κ) * derivative f * v).natDegree ≤
        (C ((2 * r + 1 : ℕ) : κ) * derivative f).natDegree + v.natDegree := natDegree_mul_le
    have h2 : (C ((2 * r + 1 : ℕ) : κ) * derivative f).natDegree ≤ (derivative f).natDegree :=
      natDegree_C_mul_le _ _
    have h3 : (derivative f).natDegree ≤ f.natDegree - 1 := natDegree_derivative_le f
    omega

private lemma natDegree_iterU_le {κ : Type*} [CommRing κ] {f u : κ[X]} {d : ℕ}
    (hf : f.natDegree ≤ 3) (hu : u.natDegree ≤ d) (r : ℕ) :
    (iterU f r u).natDegree ≤ d + 2 * r := by
  induction r with
  | zero => simpa [iterU] using hu
  | succ m ih =>
    have h := natDegree_stepU_le hf ih m
    change (stepU f m (iterU f m u)).natDegree ≤ d + 2 * (m + 1)
    omega

private lemma natDegree_iterV_le {κ : Type*} [CommRing κ] {f v : κ[X]} {d : ℕ}
    (hf : f.natDegree ≤ 3) (hv : v.natDegree ≤ d) (r : ℕ) :
    (iterV f r v).natDegree ≤ d + 2 * r := by
  induction r with
  | zero => simpa [iterV] using hv
  | succ m ih =>
    have h := natDegree_stepV_le hf ih m
    change (stepV f m (iterV f m v)).natDegree ≤ d + 2 * (m + 1)
    omega

private lemma stepanov_master_deriv {κ : Type*} [CommRing κ] {p : ℕ} [CharP κ p]
    (hp_odd : p % 2 = 1) (f A B : κ[X]) (r : ℕ) :
    (C 2 * f) ^ r * derivative^[r] (A + B * f ^ ((p - 1) / 2)) =
      iterU f r A + iterV f r B * f ^ ((p - 1) / 2) := by
  set h := (p - 1) / 2
  have h2h : 2 * h + 1 = p := by omega
  have h2h_cast : ((2 * h : ℕ) : κ) = -1 := by
    have hp0 : (p : κ) = 0 := CharP.cast_eq_zero κ p
    have h1 : ((2 * h : ℕ) : κ) + 1 = 0 := by
      rw [← Nat.cast_one, ← Nat.cast_add, h2h, hp0]
    linear_combination h1
  have hfh : (C 2 * f) * derivative (f ^ h) = -(derivative f) * f ^ h := by
    calc (C 2 * f) * derivative (f ^ h)
        = C 2 * (f * derivative (f ^ h)) := by ring
      _ = C 2 * (C (h : κ) * derivative f * f ^ h) := by rw [mul_derivative_pow]
      _ = C ((2 * h : ℕ) : κ) * derivative f * f ^ h := by
            rw [Nat.cast_mul, map_mul, Nat.cast_ofNat]; ring
      _ = -(derivative f) * f ^ h := by rw [h2h_cast, map_neg, map_one]; ring
  induction r with
  | zero => simp [iterU, iterV]
  | succ m ih =>
    have hd_both := congrArg derivative ih
    rw [derivative_mul, derivative_add, derivative_mul] at hd_both
    have hmul := congrArg (fun z => (C 2 * f) * z) hd_both
    have hderiv_C2f : derivative (C 2 * f) = C 2 * derivative f := by
      rw [derivative_mul, derivative_C, zero_mul, zero_add]
    have hlhs : (C 2 * f) * (derivative ((C 2 * f) ^ m) * derivative^[m] (A + B * f ^ h) +
          (C 2 * f) ^ m * derivative (derivative^[m] (A + B * f ^ h))) =
        C ((2 * m : ℕ) : κ) * derivative f * (iterU f m A + iterV f m B * f ^ h) +
          (C 2 * f) ^ (m + 1) * derivative^[m + 1] (A + B * f ^ h) := by
      rw [mul_add, ← mul_assoc, mul_derivative_pow (C 2 * f) m, hderiv_C2f]
      have h1 : C (m : κ) * (C 2 * derivative f) * (C 2 * f) ^ m *
            derivative^[m] (A + B * f ^ h) =
          C ((2 * m : ℕ) : κ) * derivative f * ((C 2 * f) ^ m * derivative^[m] (A + B * f ^ h)) := by
        rw [Nat.cast_mul, map_mul, Nat.cast_ofNat]; ring
      rw [h1, ih, ← mul_assoc, ← pow_succ', Function.iterate_succ_apply']
    have hrhs : (C 2 * f) * (derivative (iterU f m A) +
          (derivative (iterV f m B) * f ^ h + iterV f m B * derivative (f ^ h))) =
        C 2 * f * derivative (iterU f m A) +
          (C 2 * f * derivative (iterV f m B) - derivative f * iterV f m B) * f ^ h := by
      have hpart : (C 2 * f) * (iterV f m B * derivative (f ^ h)) =
          iterV f m B * ((C 2 * f) * derivative (f ^ h)) := by ring
      rw [mul_add, mul_add, hpart, hfh]
      ring
    rw [hlhs, hrhs] at hmul
    have hcast_succ : C ((2 * m + 1 : ℕ) : κ) = C ((2 * m : ℕ) : κ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one, map_add, map_one]
    simp only [iterU, iterV, stepU, stepV, hcast_succ]
    linear_combination hmul

private lemma iterate_derivative_mul_X_sub_C {κ : Type*} [CommRing κ] (x : κ) (P : κ[X]) :
    ∀ r : ℕ, derivative^[r + 1] ((X - C x) * P) =
      (X - C x) * derivative^[r + 1] P + C ((r + 1 : ℕ) : κ) * derivative^[r] P := by
  intro r
  induction r with
  | zero =>
    simp [derivative_mul]
    ring
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, derivative_add, derivative_mul, derivative_mul,
      derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, derivative_C, zero_mul,
      zero_add]
    have h1 : derivative (derivative^[m + 1] P) = derivative^[m + 2] P :=
      (Function.iterate_succ_apply' derivative (m + 1) P).symm
    have h2 : derivative (derivative^[m] P) = derivative^[m + 1] P :=
      (Function.iterate_succ_apply' derivative m P).symm
    rw [h1, h2]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

private lemma roots_count_ge_of_iterate_derivative {κ : Type*} [Field κ] [DecidableEq κ]
    {p : ℕ} [CharP κ p] (x : κ) :
    ∀ m : ℕ, m ≤ p → ∀ P : κ[X], P ≠ 0 →
      (∀ r < m, (derivative^[r] P).eval x = 0) → m ≤ P.roots.count x := by
  intro m
  induction m with
  | zero => intro _ _ _ _; exact Nat.zero_le _
  | succ n ih =>
    intro hnp P hP hderiv
    have hP0 : P.eval x = 0 := hderiv 0 (Nat.zero_lt_succ n)
    have hdvd : (X - C x) ∣ P := Polynomial.dvd_iff_isRoot.mpr hP0
    obtain ⟨Q, rfl⟩ := hdvd
    have hQ : Q ≠ 0 := right_ne_zero_of_mul hP
    have hQderiv : ∀ r < n, (derivative^[r] Q).eval x = 0 := by
      intro r hr
      have h1 := hderiv (r + 1) (Nat.succ_lt_succ hr)
      rw [iterate_derivative_mul_X_sub_C] at h1
      simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, zero_add] at h1
      have hr_ne : ((r + 1 : ℕ) : κ) ≠ 0 := by
        intro hz
        have hd : p ∣ r + 1 := (CharP.cast_eq_zero_iff κ p (r + 1)).mp hz
        have hle := Nat.le_of_dvd (Nat.succ_pos r) hd
        omega
      exact (mul_eq_zero.mp h1).resolve_left hr_ne
    have hih := ih (by omega) Q hQ hQderiv
    rw [Polynomial.roots_mul hP, Multiset.count_add, Polynomial.roots_X_sub_C,
      Multiset.count_singleton_self]
    omega

private lemma sum_multiset_count_le_card {α : Type*} [DecidableEq α]
    (s : Multiset α) (S : Finset α) :
    ∑ x ∈ S, s.count x ≤ s.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have h1 : ∑ x ∈ insert a t, s.count x = (s.filter (· ∈ insert a t)).card := by
      clear ih
      induction s using Multiset.induction_on with
      | empty => simp
      | cons b m ihm =>
        rw [Multiset.filter_cons]
        by_cases hb : b ∈ insert a t
        · rw [if_pos hb, Multiset.card_add, Multiset.card_singleton, ← ihm]
          simp_rw [Multiset.count_cons]
          rw [Finset.sum_add_distrib]
          have hsum_ite : ∑ x ∈ insert a t, (if x = b then 1 else 0) = 1 := by
            rw [Finset.sum_eq_single b]
            · simp
            · intro x _ hxb; simp [hxb]
            · intro h; exact (h hb).elim
          rw [hsum_ite]
          omega
        · rw [if_neg hb, zero_add, ← ihm]
          refine Finset.sum_congr rfl fun x hx => ?_
          have hxb : x ≠ b := fun h => hb (h ▸ hx)
          simp [hxb]
    rw [h1]
    exact Multiset.card_le_card (Multiset.filter_le _ _)

private lemma polyBlock_coeff {κ : Type*} [CommRing κ] {K L p : ℕ} (hLp : L < p)
    (c : Fin K → Fin L → κ) :
    let P : κ[X] := ∑ k : Fin K, (∑ j : Fin L, C (c k j) * X ^ j.1) * X ^ (k.1 * p)
    (∀ (k : Fin K) (j : Fin L), P.coeff (k.1 * p + j.1) = c k j) ∧
    (∀ n : ℕ, P.coeff n ≠ 0 → n % p < L) ∧
    (P.natDegree ≤ (K - 1) * p + (L - 1)) := by
  intro P
  have hp0 : 0 < p := Nat.pos_of_ne_zero (by omega)
  have hP_eq : P = ∑ k : Fin K, ∑ j : Fin L, C (c k j) * X ^ (k.1 * p + j.1) := by
    dsimp [P]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, ← pow_add, add_comm]
  have hcoeff_n : ∀ n : ℕ, P.coeff n =
      ∑ k : Fin K, ∑ j : Fin L, if n = k.1 * p + j.1 then c k j else 0 := by
    intro n
    rw [hP_eq, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.coeff_C_mul_X_pow]
  refine ⟨?_, ?_, ?_⟩
  · intro k j
    rw [hcoeff_n, Finset.sum_eq_single k]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro j' _ hjj'
        have hne : k.1 * p + j.1 ≠ k.1 * p + j'.1 := by
          intro h; exact hjj' (Fin.ext (by omega))
        rw [if_neg hne]
      · intro h; exact (h (Finset.mem_univ j)).elim
    · intro k' _ hkk'
      refine Finset.sum_eq_zero fun j' _ => ?_
      have hne : k.1 * p + j.1 ≠ k'.1 * p + j'.1 := by
        intro h
        have hkj : j.1 < p := lt_trans j.2 hLp
        have hkj' : j'.1 < p := lt_trans j'.2 hLp
        have h1 : (k.1 * p + j.1) / p = k.1 := by
          rw [mul_comm k.1 p, Nat.mul_add_div hp0, Nat.div_eq_of_lt hkj, add_zero]
        have h2 : (k'.1 * p + j'.1) / p = k'.1 := by
          rw [mul_comm k'.1 p, Nat.mul_add_div hp0, Nat.div_eq_of_lt hkj', add_zero]
        have hdiv : k.1 = k'.1 := by rw [← h1, ← h2, h]
        exact hkk' (Fin.ext hdiv.symm)
      rw [if_neg hne]
    · intro h; exact (h (Finset.mem_univ k)).elim
  · intro n hn
    rw [hcoeff_n] at hn
    by_contra hge
    apply hn
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun j _ => ?_
    have hne : n ≠ k.1 * p + j.1 := by
      intro heq
      have hmod : n % p = j.1 := by
        rw [heq, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      have := j.2
      omega
    simp [hne]
  · rw [hP_eq]
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun k _ => ?_)
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    have hk : k.1 ≤ K - 1 := by have := k.2; omega
    have hj : j.1 ≤ L - 1 := by have := j.2; omega
    have hmul : k.1 * p ≤ (K - 1) * p := Nat.mul_le_mul_right p hk
    omega

private lemma stepanov_cubic_bound {κ : Type*} [Field κ] [Fintype κ] [DecidableEq κ]
    {p : ℕ} (hp : p.Prime) (hp900 : 900 ≤ p) (hcard : Fintype.card κ = p)
    {f : κ[X]} (hf_deg : f.natDegree = 3) {ε : κ} (hε : ε = 1 ∨ ε = -1) :
    let K := Nat.sqrt p
    let M := 2 * K - 26
    2 * M * (Finset.univ.filter (fun x : κ => (f.eval x) ^ ((p - 1) / 2) = ε)).card ≤
      M * p + 28 * p := by
  classical
  let : CharP κ p := charP_of_card_prime hp hcard
  have hp_odd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr (by omega)
  have h2_ne : (2 : κ) ≠ 0 := by
    intro h2
    have hd := (CharP.cast_eq_zero_iff κ p 2).mp (by simpa using h2)
    have := Nat.le_of_dvd (by decide) hd
    omega
  have hε_ne : ε ≠ 0 := by
    rcases hε with rfl | rfl
    · exact one_ne_zero
    · exact neg_ne_zero.mpr one_ne_zero
  intro K M
  let L := p / 4
  have hK30 : 30 ≤ K := by
    change 30 ≤ Nat.sqrt p
    exact Nat.le_sqrt.mpr (by omega)
  have hK_sq : K * K ≤ p := Nat.sqrt_le p
  have hL_lo : p - 3 ≤ 4 * L := by dsimp [L]; omega
  have hL_hi : 4 * L ≤ p := by dsimp [L]; omega
  have hL_pos : 1 ≤ L := by dsimp [L]; omega
  have hK_pos : 1 ≤ K := by omega
  have hM_pos : 1 ≤ M := by omega
  have hM_lt_p : M < p := by
    have : 2 * K ≤ K * K := by nlinarith
    omega
  have hLp : L < p := by dsimp [L]; omega
  let h := (p - 1) / 2
  have h2h : 2 * h = p - 1 := by omega
  -- Linear map from coefficient space Dom to equation space Cod
  let Dom := (Fin K → Fin L → κ) × (Fin K → Fin L → κ)
  let Cod := (Σ r : Fin M, Fin (L + K + 2 * r.1)) → κ
  let mkPoly (c : Fin K → Fin L → κ) (k : Fin K) : κ[X] :=
    ∑ j : Fin L, C (c k j) * X ^ j.1
  let Wpoly (r : ℕ) (v : Dom) : κ[X] :=
    ∑ k : Fin K, (iterU f r (mkPoly v.1 k) + C ε * iterV f r (mkPoly v.2 k)) * X ^ k.1
  have hmk_add : ∀ c₁ c₂ k, mkPoly (c₁ + c₂) k = mkPoly c₁ k + mkPoly c₂ k := by
    intro c₁ c₂ k
    simp only [mkPoly, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  have hmk_smul : ∀ (a : κ) c k, mkPoly (a • c) k = a • mkPoly c k := by
    intro a c k
    simp only [mkPoly, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, Polynomial.smul_eq_C_mul,
      map_mul, mul_assoc]
  have hW_add : ∀ r v₁ v₂, Wpoly r (v₁ + v₂) = Wpoly r v₁ + Wpoly r v₂ := by
    intro r v₁ v₂
    dsimp [Wpoly]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (iterU f r (mkPoly (v₁.1 + v₂.1) k) + C ε * iterV f r (mkPoly (v₁.2 + v₂.2) k)) * X ^ k.1 = _
    rw [hmk_add, hmk_add, iterU_add, iterV_add]
    ring
  have hW_smul : ∀ r (a : κ) v, Wpoly r (a • v) = a • Wpoly r v := by
    intro r a v
    dsimp [Wpoly]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (iterU f r (mkPoly (a • v.1) k) + C ε * iterV f r (mkPoly (a • v.2) k)) * X ^ k.1 = _
    rw [hmk_smul, hmk_smul, iterU_smul, iterV_smul, Polynomial.smul_eq_C_mul,
      Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
    ring
  let T : Dom →ₗ[κ] Cod :=
    { toFun := fun v ⟨r, i⟩ => (Wpoly r.1 v).coeff i.1
      map_add' := fun v₁ v₂ => by
        funext ⟨r, i⟩
        change (Wpoly r.1 (v₁ + v₂)).coeff i.1 =
          (Wpoly r.1 v₁).coeff i.1 + (Wpoly r.1 v₂).coeff i.1
        rw [hW_add, Polynomial.coeff_add]
      map_smul' := fun a v => by
        funext ⟨r, i⟩
        change (Wpoly r.1 (a • v)).coeff i.1 = a * (Wpoly r.1 v).coeff i.1
        rw [hW_smul, Polynomial.coeff_smul, smul_eq_mul] }
  have hrank_lt : Module.finrank κ Cod < Module.finrank κ Dom := by
    have hdom : Module.finrank κ Dom = 2 * K * L := by
      dsimp [Dom]
      rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype]
      simp [Fintype.card_fin]
      ring
    have hcod : Module.finrank κ Cod = ∑ r : Fin M, (L + K + 2 * r.1) := by
      dsimp [Cod]
      rw [Module.finrank_pi, Fintype.card_sigma]
      simp [Fintype.card_fin]
    have hsum_cod : ∑ r : Fin M, (L + K + 2 * r.1) = M * (L + K) + M * (M - 1) := by
      have hsplit : ∑ r : Fin M, (L + K + 2 * r.1) =
          (∑ _r : Fin M, (L + K)) + 2 * ∑ r : Fin M, r.1 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      rw [hsplit, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have htri : 2 * ∑ r : Fin M, r.1 = M * (M - 1) := by
        rw [Fin.sum_univ_eq_sum_range (fun i => i) M]
        have := Finset.sum_range_id_mul_two M
        omega
      rw [htri]
    rw [hdom, hcod, hsum_cod]
    have hMK : M * (K + M - 1) < 6 * p := by
      have h1 : M * (K + M - 1) = (2 * K - 26) * (3 * K - 27) := by
        have : K + M - 1 = 3 * K - 27 := by dsimp [M]; omega
        rw [this]
      rw [h1]
      have h2 : (2 * K - 26) * (3 * K - 27) < 6 * (K * K) := by
        zify [show 26 ≤ 2 * K by omega, show 27 ≤ 3 * K by omega]
        nlinarith
      nlinarith [hK_sq]
    have h26L : 6 * p < 26 * L := by omega
    have h2KM : 2 * K = M + 26 := by dsimp [M]; omega
    have h2KL : 2 * K * L = M * L + 26 * L := by rw [h2KM, add_mul]
    have hRHS : M * (L + K) + M * (M - 1) = M * L + M * (K + M - 1) := by
      zify [hM_pos, show 1 ≤ K + M by omega]
      ring
    omega
  have hker_ne : LinearMap.ker T ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective T := LinearMap.ker_eq_bot.mp hbot
    have hle : Module.finrank κ Dom ≤ Module.finrank κ Cod :=
      LinearMap.finrank_le_finrank_of_injective hinj
    omega
  obtain ⟨v, hv_ker, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  have hW_deg : ∀ r : ℕ, (Wpoly r v).natDegree < L + K + 2 * r := by
    intro r
    have hterm_lt : ∀ k : Fin K,
        ((iterU f r (mkPoly v.1 k) + C ε * iterV f r (mkPoly v.2 k)) * X ^ k.1).natDegree <
          L + K + 2 * r := by
      intro k
      have hmk1 : (mkPoly v.1 k).natDegree ≤ L - 1 := by
        dsimp [mkPoly]
        refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun j _ => ?_)
        refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
        have := j.2; omega
      have hmk2 : (mkPoly v.2 k).natDegree ≤ L - 1 := by
        dsimp [mkPoly]
        refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun j _ => ?_)
        refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
        have := j.2; omega
      have hu_deg : (iterU f r (mkPoly v.1 k)).natDegree ≤ L - 1 + 2 * r :=
        natDegree_iterU_le hf_deg.le hmk1 r
      have hv_deg : (C ε * iterV f r (mkPoly v.2 k)).natDegree ≤ L - 1 + 2 * r :=
        (Polynomial.natDegree_C_mul_le _ _).trans (natDegree_iterV_le hf_deg.le hmk2 r)
      have hsum_deg : (iterU f r (mkPoly v.1 k) + C ε * iterV f r (mkPoly v.2 k)).natDegree ≤
          L - 1 + 2 * r := (Polynomial.natDegree_add_le _ _).trans (max_le hu_deg hv_deg)
      have hmul_deg := Polynomial.natDegree_mul_le (p := iterU f r (mkPoly v.1 k) + C ε * iterV f r (mkPoly v.2 k))
        (q := X ^ k.1)
      rw [Polynomial.natDegree_X_pow] at hmul_deg
      have := k.2
      omega
    have haux : ∀ s : Finset (Fin K),
        (∑ k ∈ s, (iterU f r (mkPoly v.1 k) + C ε * iterV f r (mkPoly v.2 k)) * X ^ k.1).natDegree <
          L + K + 2 * r := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp; omega
      | insert a t hat ih =>
        rw [Finset.sum_insert hat]
        exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt (hterm_lt a) ih)
    exact haux Finset.univ
  have hW_zero : ∀ r : Fin M, Wpoly r.1 v = 0 := by
    intro r
    ext i
    rw [Polynomial.coeff_zero]
    by_cases hi : i < L + K + 2 * r.1
    · have h0 := congrFun (LinearMap.mem_ker.mp hv_ker) ⟨r, ⟨i, hi⟩⟩
      exact h0
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hW_deg r.1) (not_lt.mp hi))
  -- Build A, B, Q
  let A : κ[X] := ∑ k : Fin K, mkPoly v.1 k * X ^ (k.1 * p)
  let B : κ[X] := ∑ k : Fin K, mkPoly v.2 k * X ^ (k.1 * p)
  let Q : κ[X] := A + B * f ^ h
  have hA_spec := polyBlock_coeff hLp v.1
  have hB_spec := polyBlock_coeff hLp v.2
  have hAB_ne : A ≠ 0 ∨ B ≠ 0 := by
    by_contra hboth
    push Not at hboth
    apply hv_ne
    apply Prod.ext <;> funext k j
    · have hc : A.coeff (k.1 * p + j.1) = v.1 k j := hA_spec.1 k j
      rw [hboth.1, Polynomial.coeff_zero] at hc
      exact hc.symm
    · have hc : B.coeff (k.1 * p + j.1) = v.2 k j := hB_spec.1 k j
      rw [hboth.2, Polynomial.coeff_zero] at hc
      exact hc.symm
  have hf_ne : f ≠ 0 := by intro h0; rw [h0] at hf_deg; simp at hf_deg
  have hQ_ne : Q ≠ 0 := by
    intro hQ0
    have hA_eq : A = -(B * f ^ h) := eq_neg_of_add_eq_zero_left hQ0
    have hB_ne : B ≠ 0 := by
      intro hB0
      rw [hB0, zero_mul, neg_zero] at hA_eq
      rcases hAB_ne with h | h <;> exact h (by assumption)
    have hfh_ne : f ^ h ≠ 0 := pow_ne_zero h hf_ne
    have hA_ne : A ≠ 0 := by
      rw [hA_eq, neg_ne_zero]
      exact mul_ne_zero hB_ne hfh_ne
    have hdeg_eq : A.natDegree = B.natDegree + 3 * h := by
      rw [hA_eq, Polynomial.natDegree_neg, Polynomial.natDegree_mul hB_ne hfh_ne,
        Polynomial.natDegree_pow, hf_deg]
      ring
    have hA_mod : A.natDegree % p < L :=
      hA_spec.2.1 A.natDegree (Polynomial.leadingCoeff_ne_zero.mpr hA_ne)
    have hB_mod : B.natDegree % p < L :=
      hB_spec.2.1 B.natDegree (Polynomial.leadingCoeff_ne_zero.mpr hB_ne)
    have hA_div := Nat.div_add_mod A.natDegree p
    have hB_div := Nat.div_add_mod B.natDegree p
    set qA := A.natDegree / p
    set rA := A.natDegree % p
    set qB := B.natDegree / p
    set rB := B.natDegree % p
    have h3h : 3 * h = p + (p - 3) / 2 := by omega
    have heq : qA * p + rA = (qB + 1) * p + rB + (p - 3) / 2 := by
      have : p * qA + rA = p * qB + rB + (p + (p - 3) / 2) := by omega
      linarith
    have hqb2 : (qB + 2) * p = (qB + 1) * p + p := by ring
    by_cases hq : qA ≤ qB + 1
    · have h1 : qA * p ≤ (qB + 1) * p := Nat.mul_le_mul_right p hq
      omega
    · have h1 : (qB + 2) * p ≤ qA * p := Nat.mul_le_mul_right p (by omega)
      omega
  have hQ_deg : Q.natDegree ≤ K * p + p := by
    have hA_deg : A.natDegree ≤ (K - 1) * p + (L - 1) := hA_spec.2.2
    have hB_deg : B.natDegree ≤ (K - 1) * p + (L - 1) := hB_spec.2.2
    have hfh_deg : (f ^ h).natDegree ≤ 3 * h := by
      rw [Polynomial.natDegree_pow, hf_deg]; ring_nf; rfl
    have hBf_deg : (B * f ^ h).natDegree ≤ (K - 1) * p + (L - 1) + 3 * h :=
      (Polynomial.natDegree_mul_le).trans (Nat.add_le_add hB_deg hfh_deg)
    refine (Polynomial.natDegree_add_le A (B * f ^ h)).trans (max_le ?_ ?_)
    · have : (K - 1) * p ≤ K * p := Nat.mul_le_mul_right p (by omega)
      omega
    · have h1 : (K - 1) * p + p = K * p := by
        zify [hK_pos]; ring
      have h2 : L - 1 + 3 * h ≤ 2 * p := by omega
      omega
  -- Every x ∈ S_ε is a root of Q of multiplicity ≥ M
  let Sε := Finset.univ.filter (fun x : κ => (f.eval x) ^ h = ε)
  have hmult : ∀ x ∈ Sε, M ≤ Q.roots.count x := by
    intro x hx
    have hfx_pow : (f.eval x) ^ h = ε := (Finset.mem_filter.mp hx).2
    have hfx_ne : f.eval x ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by omega : h ≠ 0)] at hfx_pow
      exact hε_ne hfx_pow.symm
    have hxp : x ^ p = x := by
      rw [← hcard]
      exact FiniteField.pow_card x
    refine roots_count_ge_of_iterate_derivative x M hM_lt_p.le Q hQ_ne fun r hr => ?_
    have hmaster := stepanov_master_deriv hp_odd f A B r
    have hev := congrArg (Polynomial.eval x) hmaster
    have hU_eval : (iterU f r A).eval x = ∑ k : Fin K, (iterU f r (mkPoly v.1 k)).eval x * x ^ k.1 := by
      dsimp [A]
      rw [iterU_sum, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [iterU_mul_X_pow_char, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        mul_comm k.1 p, pow_mul, hxp]
    have hV_eval : (iterV f r B).eval x = ∑ k : Fin K, (iterV f r (mkPoly v.2 k)).eval x * x ^ k.1 := by
      dsimp [B]
      rw [iterV_sum, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [iterV_mul_X_pow_char, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        mul_comm k.1 p, pow_mul, hxp]
    have hW_eval : (iterU f r A + iterV f r B * f ^ h).eval x = (Wpoly r v).eval x := by
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, hU_eval, hV_eval, hfx_pow]
      dsimp [Wpoly]
      rw [Polynomial.eval_finsetSum, Finset.sum_mul]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
      ring
    rw [hW_eval, hW_zero ⟨r, hr⟩, Polynomial.eval_zero, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_mul, Polynomial.eval_C] at hev
    have h2f_ne : (2 * f.eval x) ^ r ≠ 0 := pow_ne_zero r (mul_ne_zero h2_ne hfx_ne)
    exact (mul_eq_zero.mp hev).resolve_left h2f_ne
  have hMcard : M * Sε.card ≤ Q.natDegree := by
    calc M * Sε.card = ∑ _x ∈ Sε, M := by simp [mul_comm]
      _ ≤ ∑ x ∈ Sε, Q.roots.count x := Finset.sum_le_sum hmult
      _ ≤ Q.roots.card := sum_multiset_count_le_card Q.roots Sε
      _ ≤ Q.natDegree := Polynomial.card_roots' Q
  have hKM : 2 * K = M + 26 := by dsimp [M]; omega
  calc 2 * M * Sε.card = 2 * (M * Sε.card) := by ring
    _ ≤ 2 * (K * p + p) := Nat.mul_le_mul_left 2 (hMcard.trans hQ_deg)
    _ = (2 * K) * p + 2 * p := by ring
    _ = M * p + 28 * p := by rw [hKM]; ring

private lemma weak_hasse_bound {κ : Type*} [Field κ] [Fintype κ] [DecidableEq κ]
    {p : ℕ} (hp : p.Prime) (hp900 : 900 ≤ p) (hcard : Fintype.card κ = p)
    (W : WeierstrassCurve κ) :
    |((p : ℤ) + 1 - (Nat.card W.toAffine.Point : ℤ) : ℝ)| ≤ 35 * Real.sqrt (p : ℝ) := by
  classical
  let : CharP κ p := charP_of_card_prime hp hcard
  have h2_ne : (2 : κ) ≠ 0 := by
    intro h2
    have hd := (CharP.cast_eq_zero_iff κ p 2).mp (by simpa using h2)
    have := Nat.le_of_dvd (by decide) hd
    omega
  have h4_ne : (4 : κ) ≠ 0 := by
    have : (4 : κ) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2_ne h2_ne
  -- Completed-square cubic f(X) = 4 X^3 + (a₁^2 + 4 a₂) X^2 + (2 a₁ a₃ + 4 a₄) X + (a₃^2 + 4 a₆)
  let f : κ[X] :=
    C 4 * X ^ 3 + C (W.a₁ ^ 2 + 4 * W.a₂) * X ^ 2 +
    C (2 * W.a₁ * W.a₃ + 4 * W.a₄) * X + C (W.a₃ ^ 2 + 4 * W.a₆)
  have hf_deg : f.natDegree = 3 := by
    have hle : f.natDegree ≤ 3 := by
      dsimp [f]
      refine (natDegree_add_le _ _).trans (max_le ?_ (by rw [natDegree_C]; omega))
      refine (natDegree_add_le _ _).trans (max_le ?_
        ((natDegree_C_mul_le _ _).trans (by rw [natDegree_X]; omega)))
      refine (natDegree_add_le _ _).trans (max_le (natDegree_C_mul_X_pow_le _ _)
        ((natDegree_C_mul_X_pow_le _ _).trans (by omega)))
    have hc3 : f.coeff 3 = 4 := by
      dsimp [f]
      simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
      norm_num
    exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle (hc3 ▸ h4_ne)
  have hf_ne : f ≠ 0 := by intro h0; rw [h0] at hf_deg; simp at hf_deg
  have hcomp_sq : ∀ x y : κ, W.toAffine.Equation x y ↔
      (2 * y + W.a₁ * x + W.a₃) ^ 2 = f.eval x := by
    intro x y
    rw [W.toAffine.equation_iff]
    have hfev : f.eval x = 4 * (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) + (W.a₁ * x + W.a₃) ^ 2 := by
      dsimp [f]
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
      ring
    have hid : (2 * y + W.a₁ * x + W.a₃) ^ 2 - f.eval x =
        4 * ((y ^ 2 + W.a₁ * x * y + W.a₃ * y) - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) := by
      rw [hfev]; ring
    rw [← sub_eq_zero, ← sub_eq_zero (a := (2 * y + W.a₁ * x + W.a₃) ^ 2), hid]
    exact (mul_eq_zero_iff_left h4_ne).symm
  let h := (p - 1) / 2
  let S0 : Finset κ := Finset.univ.filter (fun x : κ => f.eval x = 0)
  let Spos : Finset κ := Finset.univ.filter (fun x : κ => (f.eval x) ^ h = 1)
  let Sneg : Finset κ := Finset.univ.filter (fun x : κ => (f.eval x) ^ h = -1)
  have hS0_le : S0.card ≤ 3 := by
    have hsub : ∀ x ∈ S0, x ∈ f.roots := fun x hx =>
      (Polynomial.mem_roots hf_ne).mpr (Finset.mem_filter.mp hx).2
    calc S0.card = S0.val.card := rfl
      _ ≤ f.roots.card := Multiset.card_le_card
          ((Multiset.le_iff_subset S0.nodup).mpr fun x hx => hsub x hx)
      _ ≤ f.natDegree := Polynomial.card_roots' f
      _ = 3 := hf_deg
  have hpart_disj01 : Disjoint S0 Spos := by
    rw [Finset.disjoint_left]
    intro x h0 h1
    have h0' := (Finset.mem_filter.mp h0).2
    have h1' := (Finset.mem_filter.mp h1).2
    rw [h0', zero_pow (by omega : h ≠ 0)] at h1'
    exact zero_ne_one h1'
  have hpart_disj02 : Disjoint S0 Sneg := by
    rw [Finset.disjoint_left]
    intro x h0 h2
    have h0' := (Finset.mem_filter.mp h0).2
    have h2' := (Finset.mem_filter.mp h2).2
    rw [h0', zero_pow (by omega : h ≠ 0)] at h2'
    exact one_ne_zero (neg_eq_zero.mp h2'.symm)
  have hpart_disj12 : Disjoint Spos Sneg := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    have h1' := (Finset.mem_filter.mp h1).2
    have h2' := (Finset.mem_filter.mp h2).2
    rw [h1'] at h2'
    exact h2_ne (by linear_combination h2')
  have hpart_union : S0 ∪ Spos ∪ Sneg = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true, S0, Spos, Sneg, Finset.mem_filter, true_and]
    by_cases hx : f.eval x = 0
    · exact Or.inl (Or.inl hx)
    · rcases (euler_criterion_field hp (by omega) hcard hx).1 with h1 | h2
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h2
  have hpart_sum : S0.card + Spos.card + Sneg.card = p := by
    have h1 : (S0 ∪ Spos ∪ Sneg).card = S0.card + Spos.card + Sneg.card := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hpart_disj02, hpart_disj12⟩),
        Finset.card_union_of_disjoint hpart_disj01]
    rw [← h1, hpart_union, Finset.card_univ, hcard]
  -- Count EqSet = {(x, y) | W.Equation x y}
  let EqSet := Finset.univ.filter (fun xy : κ × κ => W.toAffine.Equation xy.1 xy.2)
  let NsSet := Finset.univ.filter (fun xy : κ × κ => W.toAffine.Nonsingular xy.1 xy.2)
  have hEq_card : EqSet.card = S0.card + 2 * Spos.card := by
    have hfiber : ∀ x : κ, (Finset.univ.filter (fun y : κ => W.toAffine.Equation x y)).card =
        if x ∈ S0 then 1 else if x ∈ Spos then 2 else 0 := by
      intro x
      have hbij : (Finset.univ.filter (fun y : κ => W.toAffine.Equation x y)).card =
          (Finset.univ.filter (fun u : κ => u ^ 2 = f.eval x)).card := by
        refine Finset.card_bij (fun y _ => 2 * y + W.a₁ * x + W.a₃) ?_ ?_ ?_
        · intro y hy
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (hcomp_sq x y).mp (Finset.mem_filter.mp hy).2⟩
        · intro y₁ _ y₂ _ heq
          have hsub : 2 * (y₁ - y₂) = 0 := by linear_combination heq
          exact sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left h2_ne)
        · intro u hu
          refine ⟨(u - W.a₁ * x - W.a₃) / 2, ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcomp_sq x _).mpr ?_⟩
            have hlin : 2 * ((u - W.a₁ * x - W.a₃) / 2) + W.a₁ * x + W.a₃ = u := by
              rw [mul_div_cancel₀ _ h2_ne]; ring
            rw [hlin]
            exact (Finset.mem_filter.mp hu).2
          · rw [mul_div_cancel₀ _ h2_ne]; ring
      rw [hbij]
      by_cases hx0 : x ∈ S0
      · rw [if_pos hx0]
        have hfx0 : f.eval x = 0 := (Finset.mem_filter.mp hx0).2
        have hset : Finset.univ.filter (fun u : κ => u ^ 2 = f.eval x) = {0} := by
          ext u; simp [hfx0]
        rw [hset, Finset.card_singleton]
      · rw [if_neg hx0]
        have hfx_ne : f.eval x ≠ 0 := by simpa [S0] using hx0
        by_cases hx1 : x ∈ Spos
        · rw [if_pos hx1]
          have hfx1 : (f.eval x) ^ h = 1 := (Finset.mem_filter.mp hx1).2
          obtain ⟨u₀, hu₀⟩ := (euler_criterion_field hp (by omega) hcard hfx_ne).2.mpr hfx1
          have hu₀_ne : u₀ ≠ 0 := by intro h; subst h; simp at hu₀; exact hfx_ne hu₀.symm
          have hne_neg : u₀ ≠ -u₀ := by
            intro h; exact h2_ne (by
              have : 2 * u₀ = 0 := by linear_combination h
              exact (mul_eq_zero.mp this).resolve_right hu₀_ne)
          have hset : Finset.univ.filter (fun u : κ => u ^ 2 = f.eval x) = {u₀, -u₀} := by
            ext u
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton, ← hu₀, sq_eq_sq_iff_eq_or_eq_neg]
          rw [hset, Finset.card_pair hne_neg]
        · rw [if_neg hx1]
          have hno : ¬ ∃ u : κ, u ^ 2 = f.eval x := by
            intro hex
            have h1 := (euler_criterion_field hp (by omega) hcard hfx_ne).2.mp hex
            exact hx1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
          have hset : Finset.univ.filter (fun u : κ => u ^ 2 = f.eval x) = ∅ := by
            ext u
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            intro hu; exact hno ⟨u, hu⟩
          rw [hset, Finset.card_empty]
    have hEq_sum : EqSet.card =
        ∑ x : κ, (Finset.univ.filter (fun y : κ => W.toAffine.Equation x y)).card := by
      rw [← Finset.card_sigma]
      refine Finset.card_bij (fun xy _ => ⟨xy.1, xy.2⟩) ?_ ?_ ?_
      · intro xy hxy
        exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hxy).2⟩⟩
      · intro a _ b _ h
        cases a; cases b; simp only [Sigma.mk.injEq, heq_eq_eq] at h
        exact Prod.ext h.1 h.2
      · intro s hs
        refine ⟨(s.1, s.2), ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp (Finset.mem_sigma.mp hs).2).2⟩
    rw [hEq_sum]
    simp_rw [hfiber]
    have hsum1 : ∑ x : κ, (if x ∈ S0 then 1 else if x ∈ Spos then 2 else 0) =
        ∑ x : κ, ((if x ∈ S0 then 1 else 0) + (if x ∈ Spos then 2 else 0)) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases h0 : x ∈ S0
      · have h1 : x ∉ Spos := Finset.disjoint_left.mp hpart_disj01 h0
        simp [h0, h1]
      · simp [h0]
    rw [hsum1, Finset.sum_add_distrib]
    simp [Finset.sum_ite_mem, mul_comm]
  -- Bound singular points |EqSet \ NsSet| ≤ S0.card ≤ 3
  have hNs_sub : NsSet ⊆ EqSet := fun xy hxy =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hxy).2.1⟩
  have hsing_le : (EqSet \ NsSet).card ≤ S0.card := by
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · intro xy hxy
      rcases Finset.mem_sdiff.mp (Finset.mem_coe.mp hxy) with ⟨heq, hns⟩
      have heq' : W.toAffine.Equation xy.1 xy.2 := (Finset.mem_filter.mp heq).2
      have hns' : ¬ W.toAffine.Nonsingular xy.1 xy.2 := by simpa [NsSet] using hns
      rw [W.toAffine.nonsingular_iff'] at hns'
      have hy0 : 2 * xy.2 + W.a₁ * xy.1 + W.a₃ = 0 := by
        by_contra hne
        exact hns' ⟨heq', Or.inr hne⟩
      have hfx0 : f.eval xy.1 = 0 := by
        have hsq := (hcomp_sq xy.1 xy.2).mp heq'
        rw [hy0, zero_pow (by decide : 2 ≠ 0)] at hsq
        exact hsq.symm
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfx0⟩)
    · intro a ha b hb hfst
      rcases Finset.mem_sdiff.mp (Finset.mem_coe.mp ha) with ⟨heqa, hnsa⟩
      rcases Finset.mem_sdiff.mp (Finset.mem_coe.mp hb) with ⟨heqb, hnsb⟩
      have hya : 2 * a.2 + W.a₁ * a.1 + W.a₃ = 0 := by
        by_contra hne
        have hns' : ¬ W.toAffine.Nonsingular a.1 a.2 := by simpa [NsSet] using hnsa
        exact hns' ((W.toAffine.nonsingular_iff' a.1 a.2).mpr ⟨(Finset.mem_filter.mp heqa).2, Or.inr hne⟩)
      have hyb : 2 * b.2 + W.a₁ * b.1 + W.a₃ = 0 := by
        by_contra hne
        have hns' : ¬ W.toAffine.Nonsingular b.1 b.2 := by simpa [NsSet] using hnsb
        exact hns' ((W.toAffine.nonsingular_iff' b.1 b.2).mpr ⟨(Finset.mem_filter.mp heqb).2, Or.inr hne⟩)
      have h2y : 2 * (a.2 - b.2) = 0 := by
        have hab1 : a.1 = b.1 := hfst
        rw [hab1] at hya
        linear_combination hya - hyb
      exact Prod.ext hfst (sub_eq_zero.mp ((mul_eq_zero.mp h2y).resolve_left h2_ne))
  have hNs_Eq : NsSet.card + (EqSet \ NsSet).card = EqSet.card :=
    add_comm (EqSet \ NsSet).card NsSet.card ▸ Finset.card_sdiff_add_card_eq_card hNs_sub
  -- Apply Stepanov to Spos and Sneg
  let K := Nat.sqrt p
  let M := 2 * K - 26
  have hK30 : 30 ≤ K := Nat.le_sqrt.mpr (by omega)
  have hM_gt_sqrt : Real.sqrt (p : ℝ) < (M : ℝ) := by
    have hlt_nat : p < (K + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt p
      rw [sq]; exact this
    have hlt_R : (p : ℝ) < ((K + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hlt_nat
    have hsq_lt : Real.sqrt (p : ℝ) < ((K + 1 : ℕ) : ℝ) := by
      rw [Real.sqrt_lt' (by positivity)]
      exact hlt_R
    have hKM_R : ((K + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast (show K + 1 ≤ M by dsimp [M]; omega)
    linarith
  have hM_pos : (0 : ℝ) < (M : ℝ) := lt_of_le_of_lt (Real.sqrt_nonneg _) hM_gt_sqrt
  have hSpos_bd := stepanov_cubic_bound hp hp900 hcard hf_deg (Or.inl rfl)
  have hSneg_bd := stepanov_cubic_bound hp hp900 hcard hf_deg (Or.inr rfl)
  have h28 : ∀ n : ℕ, 2 * M * n ≤ M * p + 28 * p →
      2 * (n : ℝ) - (p : ℝ) ≤ 28 * Real.sqrt (p : ℝ) := by
    intro n hn
    have hnR : 2 * (M : ℝ) * (n : ℝ) ≤ (M : ℝ) * (p : ℝ) + 28 * (p : ℝ) := by
      exact_mod_cast hn
    have hmul : (M : ℝ) * (2 * (n : ℝ) - (p : ℝ)) ≤ 28 * (p : ℝ) := by linarith
    have hp_eq : (p : ℝ) = Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) :=
      (Real.mul_self_sqrt (Nat.cast_nonneg p)).symm
    have hle2 : 28 * (p : ℝ) ≤ (M : ℝ) * (28 * Real.sqrt (p : ℝ)) := by
      conv_lhs => rw [hp_eq]
      have : 0 ≤ 28 * Real.sqrt (p : ℝ) := by positivity
      nlinarith [hM_gt_sqrt]
    have : (M : ℝ) * (2 * (n : ℝ) - (p : ℝ)) ≤ (M : ℝ) * (28 * Real.sqrt (p : ℝ)) :=
      hmul.trans hle2
    exact le_of_mul_le_mul_left this hM_pos
  have hpos_R := h28 Spos.card hSpos_bd
  have hneg_R := h28 Sneg.card hSneg_bd
  have hsqrt_ge : (30 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg p)]
    exact_mod_cast (show 30 ^ 2 ≤ p by omega)
  rw [card_point_eq_one_add W]
  have hpart_R : (S0.card : ℝ) + (Spos.card : ℝ) + (Sneg.card : ℝ) = (p : ℝ) := by
    exact_mod_cast hpart_sum
  have hEq_R : (EqSet.card : ℝ) = (S0.card : ℝ) + 2 * (Spos.card : ℝ) := by
    exact_mod_cast hEq_card
  have hS0_R : (S0.card : ℝ) ≤ 3 := by exact_mod_cast hS0_le
  have hdiff_R : (EqSet.card : ℝ) - (NsSet.card : ℝ) ≤ 3 := by
    have : EqSet.card - NsSet.card ≤ 3 := by omega
    have hle : NsSet.card ≤ EqSet.card := by omega
    have hcast : ((EqSet.card - NsSet.card : ℕ) : ℝ) = (EqSet.card : ℝ) - (NsSet.card : ℝ) :=
      Nat.cast_sub hle
    have : ((EqSet.card - NsSet.card : ℕ) : ℝ) ≤ 3 := by exact_mod_cast this
    linarith
  have hNs_le_Eq : (NsSet.card : ℝ) ≤ (EqSet.card : ℝ) := by exact_mod_cast (show NsSet.card ≤ EqSet.card by omega)
  push_cast
  rw [abs_le]
  constructor <;> linarith

/- ### Part 4: Euler product over `HeightOneSpectrum (𝓞 ℚ)` and `LSeries_analyticOnNhd` -/

open NumberField IsDedekindDomain in
private lemma residueField_card_eq_prime (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) =
      (Rat.HeightOneSpectrum.primesEquiv v : ℕ) := by
  let p : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv v
  let : Fact (p : ℕ).Prime := ⟨p.2⟩
  let e₁ : v.adicCompletionIntegers ℚ ≃+* ℤ_[p] :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv
  let e : IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) ≃+* ZMod p :=
    (IsLocalRing.ResidueField.mapEquiv e₁).trans PadicInt.residueField
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod]

open NumberField IsDedekindDomain in
private lemma localPowerSeries_coeff_bounds (E : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    let p : ℕ := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
    let g : PowerSeries ℤ :=
      (E.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ)
    (∀ k : ℕ, |((PowerSeries.coeff k g : ℤ) : ℝ)| ≤ ((k + 1 : ℕ) : ℝ) * (p : ℝ) ^ k) ∧
    (900 ≤ p → ∀ k : ℕ, |((PowerSeries.coeff k g : ℤ) : ℝ)| ≤ (36 * Real.sqrt (p : ℝ)) ^ k) := by
  classical
  intro p g
  have hp : p.Prime := (Rat.HeightOneSpectrum.primesEquiv v).2
  have hp1 : 1 ≤ p := hp.one_le
  have hpR1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
  let R := v.adicCompletionIntegers ℚ
  let K := v.adicCompletion ℚ
  let κ := IsLocalRing.ResidueField R
  have hcard_nat : Nat.card κ = p := residueField_card_eq_prime v
  have hfin : Finite κ := Nat.finite_of_card_ne_zero (hcard_nat.symm ▸ hp.ne_zero)
  let : Fintype κ := Fintype.ofFinite κ
  have hcard_fin : Fintype.card κ = p := by rw [← Nat.card_eq_fintype_card, hcard_nat]
  have htriv_one : ∀ k : ℕ, (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * (p : ℝ) ^ k := by
    intro k
    have h1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    have h2 : (1 : ℝ) ≤ (p : ℝ) ^ k := one_le_pow₀ hpR1
    nlinarith
  have hhasse_one : 900 ≤ p → ∀ k : ℕ, (1 : ℝ) ≤ (36 * Real.sqrt (p : ℝ)) ^ k := by
    intro hp900 k
    have hs : (1 : ℝ) ≤ 36 * Real.sqrt (p : ℝ) := by
      have : (1 : ℝ) ≤ Real.sqrt (p : ℝ) := by
        rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg p)]
        exact_mod_cast (show 1 ≤ p by omega)
      linarith
    exact one_le_pow₀ hs
  have hg_eq : g = PowerSeries.invOfUnit
      (((E.baseChange K).localPolynomial R : ℤ[X]) : PowerSeries ℤ) 1 := rfl
  rw [hg_eq]
  unfold WeierstrassCurve.localPolynomial
  split_ifs with hgood hsplit hmult
  · let W' := (E.baseChange K).minimal R
    let a : ℤ := (p : ℤ) + 1 - (Nat.card (W'.reduction R).toAffine.Point : ℤ)
    have hq_eq : (Nat.card (IsLocalRing.ResidueField R) : ℤ) = (p : ℤ) := by
      exact_mod_cast hcard_nat
    have hpoly_eq : (1 - C ((Nat.card (IsLocalRing.ResidueField R) : ℤ) + 1 -
        (Nat.card (W'.reduction R).toAffine.Point : ℤ)) * X +
        C (Nat.card (IsLocalRing.ResidueField R) : ℤ) * X ^ 2 : ℤ[X]) =
        1 - C a * X + C (p : ℤ) * X ^ 2 := by
      dsimp only [a]
      rw [hq_eq]
    have ha_triv : |a| ≤ (p : ℤ) := by
      have ht := trivial_trace_bound (W'.reduction R)
      rw [hcard_fin] at ht
      exact ht
    have hrec := coeff_invOfUnit_quad_rec a (p : ℤ)
    let u : ℕ → ℤ := fun k =>
      PowerSeries.coeff k (PowerSeries.invOfUnit
        (((1 - C a * X + C (p : ℤ) * X ^ 2 : ℤ[X]) : PowerSeries ℤ)) 1)
    rw [hpoly_eq]
    constructor
    · intro k
      exact quad_seq_bound_trivial (u := u) hp1 ha_triv hrec.1 hrec.2.1 hrec.2.2 k
    · intro hp900 k
      have ha_hasse : |(a : ℝ)| ≤ 35 * Real.sqrt (p : ℝ) := by
        dsimp only [a]
        rw [Int.cast_sub, Int.cast_add, Int.cast_one]
        exact weak_hasse_bound hp hp900 hcard_fin (W'.reduction R)
      have h := quad_seq_bound_hasse (u := u) (M := 35) (by norm_num) ha_hasse
        hrec.1 hrec.2.1 hrec.2.2 k
      norm_num at h
      exact h
  · constructor
    · intro k
      have hc : ((PowerSeries.coeff k (PowerSeries.invOfUnit
          (((1 - X : ℤ[X]) : PowerSeries ℤ)) 1) : ℤ) : ℝ) = 1 := by
        have hcast : ((1 - X : ℤ[X]) : PowerSeries ℤ) = 1 - PowerSeries.X := by simp
        rw [hcast, coeff_invOfUnit_one_sub_X]; simp
      rw [hc, abs_one]
      exact htriv_one k
    · intro hp900 k
      have hc : ((PowerSeries.coeff k (PowerSeries.invOfUnit
          (((1 - X : ℤ[X]) : PowerSeries ℤ)) 1) : ℤ) : ℝ) = 1 := by
        have hcast : ((1 - X : ℤ[X]) : PowerSeries ℤ) = 1 - PowerSeries.X := by simp
        rw [hcast, coeff_invOfUnit_one_sub_X]; simp
      rw [hc, abs_one]
      exact hhasse_one hp900 k
  · constructor
    · intro k
      have hc : |((PowerSeries.coeff k (PowerSeries.invOfUnit
          (((1 + X : ℤ[X]) : PowerSeries ℤ)) 1) : ℤ) : ℝ)| = 1 := by
        have hcast : ((1 + X : ℤ[X]) : PowerSeries ℤ) = 1 + PowerSeries.X := by simp
        rw [hcast, coeff_invOfUnit_one_add_X]
        push_cast
        rw [abs_pow, abs_neg, abs_one, one_pow]
      rw [hc]
      exact htriv_one k
    · intro hp900 k
      have hc : |((PowerSeries.coeff k (PowerSeries.invOfUnit
          (((1 + X : ℤ[X]) : PowerSeries ℤ)) 1) : ℤ) : ℝ)| = 1 := by
        have hcast : ((1 + X : ℤ[X]) : PowerSeries ℤ) = 1 + PowerSeries.X := by simp
        rw [hcast, coeff_invOfUnit_one_add_X]
        push_cast
        rw [abs_pow, abs_neg, abs_one, one_pow]
      rw [hc]
      exact hhasse_one hp900 k
  · constructor
    · intro k
      have hcast : ((1 : ℤ[X]) : PowerSeries ℤ) = 1 := by simp
      rw [hcast]
      exact (coeff_invOfUnit_one k).trans (htriv_one k)
    · intro hp900 k
      have hcast : ((1 : ℤ[X]) : PowerSeries ℤ) = 1 := by simp
      rw [hcast]
      exact (coeff_invOfUnit_one k).trans (hhasse_one hp900 k)

open NumberField IsDedekindDomain in
private lemma LFunction_rat_props (E : WeierstrassCurve ℚ) :
    E.LFunction.IsMultiplicative ∧
    (∀ p : ℕ, p.Prime → ∀ k : ℕ,
      |(E.LFunction (p ^ k) : ℝ)| ≤ ((k + 1 : ℕ) : ℝ) * (p : ℝ) ^ k) ∧
    (∀ p : ℕ, p.Prime → 900 ≤ p → ∀ k : ℕ,
      |(E.LFunction (p ^ k) : ℝ)| ≤ (36 * Real.sqrt (p : ℝ)) ^ k) := by
  classical
  let q : HeightOneSpectrum (𝓞 ℚ) → ℕ := fun v => (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
  let g : HeightOneSpectrum (𝓞 ℚ) → PowerSeries ℤ := fun v =>
    (E.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ)
  let loc : HeightOneSpectrum (𝓞 ℚ) → ArithmeticFunction ℤ := fun v =>
    ArithmeticFunction.ofPowerSeries (q v) (g v)
  have hloc_eq : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (E.baseChange (v.adicCompletion ℚ)).localEulerFactor (v.adicCompletionIntegers ℚ) = loc v := by
    intro v
    unfold WeierstrassCurve.localEulerFactor
    rw [residueField_card_eq_prime v]
  have hL_eq : E.LFunction = ArithmeticFunction.eulerProduct loc := by
    unfold WeierstrassCurve.LFunction
    congr 1; funext v; exact hloc_eq v
  have hg_const : ∀ v, (g v).constantCoeff = 1 := fun v => by
    dsimp [g, WeierstrassCurve.localPowerSeries]
    exact PowerSeries.constantCoeff_invOfUnit _ 1
  have hloc_mult : ∀ v, (loc v).IsMultiplicative := fun v =>
    ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow (q v)
      (Rat.HeightOneSpectrum.primesEquiv v).2.isPrimePow (g v) (hg_const v)
  have hL_mult : E.LFunction.IsMultiplicative := by
    rw [hL_eq]
    exact ArithmeticFunction.isMultiplicative_eulerProduct loc hloc_mult
  have hq_inj : Function.Injective q :=
    Subtype.val_injective.comp (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  have hNorth : Northcott q := by
    refine ⟨fun B => ?_⟩
    exact Set.Finite.preimage hq_inj.injOn (Set.finite_Iic B)
  have hval : ∀ p' : Nat.Primes, ∀ k : ℕ,
      E.LFunction ((p' : ℕ) ^ k) =
        PowerSeries.coeff k (g ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p')) := by
    intro p' k
    set p : ℕ := p'.1
    have hp : p.Prime := p'.2
    let v₀ : HeightOneSpectrum (𝓞 ℚ) :=
      (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p'
    have hqv₀ : q v₀ = p := by
      dsimp [q, v₀]
      rw [(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p']
    have htend := ArithmeticFunction.tendsTo_eulerProduct_ofPowerSeries q g hg_const (p ^ k)
    obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.mp htend
    let s : Finset (HeightOneSpectrum (𝓞 ℚ)) := insert v₀ s₀
    have hs_eq : (∏ v ∈ s, loc v) (p ^ k) = E.LFunction (p ^ k) := by
      rw [hL_eq]
      exact hs₀ s (Finset.subset_insert v₀ s₀)
    rw [← hs_eq]
    have hsplit : ∏ v ∈ s, loc v = loc v₀ * ∏ v ∈ s.erase v₀, loc v := by
      rw [← Finset.mul_prod_erase s loc (Finset.mem_insert_self v₀ s₀)]
    have hother : ∀ (t : Finset (HeightOneSpectrum (𝓞 ℚ))), v₀ ∉ t →
        ∀ m : ℕ, m ∣ p ^ k → (∏ v ∈ t, loc v) m = if m = 1 then 1 else 0 := by
      intro t ht
      induction t using Finset.induction_on with
      | empty =>
        intro m _
        simp [ArithmeticFunction.one_apply]
      | insert v t' hvt' ih =>
        intro m hm
        have hv_ne : v ≠ v₀ := fun h => ht (h ▸ Finset.mem_insert_self v t')
        have hqv_ne : q v ≠ p := fun h => hv_ne (hq_inj (h.trans hqv₀.symm))
        have hqv_prime : (q v).Prime := (Rat.HeightOneSpectrum.primesEquiv v).2
        have hv₀_not' : v₀ ∉ t' := fun h => ht (Finset.mem_insert_of_mem h)
        rw [Finset.prod_insert hvt', ArithmeticFunction.mul_apply]
        have hterm : ∀ d ∈ m.divisorsAntidiagonal,
            loc v d.1 * (∏ w ∈ t', loc w) d.2 =
              if d = (1, 1) ∧ m = 1 then 1 else 0 := by
          intro d hd
          obtain ⟨hd_mul, hm0⟩ := Nat.mem_divisorsAntidiagonal.mp hd
          have hd2_dvd : d.2 ∣ p ^ k := (Dvd.intro_left d.1 hd_mul).trans hm
          rw [ih hv₀_not' d.2 hd2_dvd]
          by_cases hd2 : d.2 = 1
          · rw [if_pos hd2, mul_one]
            have hd1_eq : d.1 = m := by rw [hd2, mul_one] at hd_mul; exact hd_mul
            by_cases hm1 : m = 1
            · subst hm1
              have hd1 : d.1 = 1 := hd1_eq
              have hd_pair : d = (1, 1) := Prod.ext hd1 hd2
              rw [if_pos ⟨hd_pair, rfl⟩, hd1, ArithmeticFunction.ofPowerSeries_apply_one, hg_const]
            · rw [if_neg (fun h => hm1 h.2)]
              rw [ArithmeticFunction.ofPowerSeries_apply hqv_prime.one_lt, Function.extend_apply']
              · rfl
              · rintro ⟨j, hj⟩
                have hj0 : j ≠ 0 := by
                  intro hj0; subst hj0; rw [pow_zero] at hj; exact hm1 (hd1_eq.symm.trans hj.symm)
                have hqv_dvd_m : q v ∣ m := by
                  rw [← hd1_eq, ← hj]
                  exact dvd_pow_self (q v) hj0
                have hqv_dvd_pk : q v ∣ p ^ k := hqv_dvd_m.trans hm
                have hqv_dvd_p : q v ∣ p := hqv_prime.dvd_of_dvd_pow hqv_dvd_pk
                exact hqv_ne ((Nat.prime_dvd_prime_iff_eq hqv_prime hp).mp hqv_dvd_p)
          · rw [if_neg hd2, mul_zero, if_neg]
            rintro ⟨rfl, _⟩; exact hd2 rfl
        rw [Finset.sum_congr rfl hterm]
        by_cases hm1 : m = 1
        · subst hm1
          rw [if_pos rfl, Finset.sum_eq_single (1, 1)]
          · simp
          · intro d _ hd1; simp [hd1]
          · intro h; exact (h (Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one 1, one_ne_zero⟩)).elim
        · rw [if_neg hm1]
          exact Finset.sum_eq_zero fun d _ => by simp [hm1]
    rw [hsplit, ArithmeticFunction.mul_apply]
    rw [Finset.sum_eq_single (p ^ k, 1)]
    · rw [hother (s.erase v₀) (Finset.notMem_erase v₀ s) 1 (one_dvd _), if_pos rfl, mul_one]
      dsimp [loc]
      rw [hqv₀, ArithmeticFunction.ofPowerSeries_apply_pow hp.one_lt]
    · intro d hd hd_ne
      obtain ⟨hd_mul, _⟩ := Nat.mem_divisorsAntidiagonal.mp hd
      have hd2_dvd : d.2 ∣ p ^ k := Dvd.intro_left d.1 hd_mul
      rw [hother (s.erase v₀) (Finset.notMem_erase v₀ s) d.2 hd2_dvd]
      by_cases hd2 : d.2 = 1
      · exfalso
        rw [hd2, mul_one] at hd_mul
        exact hd_ne (Prod.ext hd_mul hd2)
      · rw [if_neg hd2, mul_zero]
    · intro h
      exact (h (Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one _, pow_ne_zero k hp.ne_zero⟩)).elim
  refine ⟨hL_mult, ?_, ?_⟩
  · intro p hp k
    let p' : Nat.Primes := ⟨p, hp⟩
    have hqv : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p') : ℕ) = p := by
      rw [(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p']
    rw [show p = (p' : ℕ) from rfl, hval p' k]
    have hb := (localPowerSeries_coeff_bounds E
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p')).1 k
    rw [hqv] at hb
    exact hb
  · intro p hp hp900 k
    let p' : Nat.Primes := ⟨p, hp⟩
    have hqv : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p') : ℕ) = p := by
      rw [(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p']
    rw [show p = (p' : ℕ) from rfl, hval p' k]
    have hb := (localPowerSeries_coeff_bounds E
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p')).2 (hqv.symm ▸ hp900) k
    rw [hqv] at hb
    exact hb

private lemma geom_sum_le_two_mul {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), r ^ k ≤ 1 + 2 * r := by
  have h1 : (1 - r) * ∑ k ∈ Finset.range (N + 1), r ^ k = 1 - r ^ (N + 1) := by
    have := geom_sum_mul r (N + 1)
    linarith
  have hpow_nn : 0 ≤ r ^ (N + 1) := pow_nonneg hr0 _
  have h1r : 1 / 2 ≤ 1 - r := by linarith
  have hbound : (1 - r) * ∑ k ∈ Finset.range (N + 1), r ^ k ≤ 1 := by linarith
  have hmul : (1 - r) * (1 + 2 * r) = 1 + r - 2 * r ^ 2 := by ring
  have hquad : 1 ≤ 1 + r - 2 * r ^ 2 := by nlinarith
  have hle : (1 - r) * ∑ k ∈ Finset.range (N + 1), r ^ k ≤ (1 - r) * (1 + 2 * r) := by linarith
  exact le_of_mul_le_mul_left hle (by linarith)

private lemma weighted_geom_sum_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), ((k + 1 : ℕ) : ℝ) * q ^ k ≤ 1 / (1 - q) ^ 2 := by
  have h1q : 0 < 1 - q := by linarith
  have htele : (1 - q) * ∑ k ∈ Finset.range (N + 1), ((k + 1 : ℕ) : ℝ) * q ^ k =
      (∑ k ∈ Finset.range (N + 1), q ^ k) - ((N + 1 : ℕ) : ℝ) * q ^ (N + 1) := by
    induction N with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih,
        Finset.sum_range_succ (fun k => q ^ k) (m + 1)]
      push_cast
      rw [pow_succ, pow_succ]
      ring
  have hgeom : (1 - q) * ∑ k ∈ Finset.range (N + 1), q ^ k = 1 - q ^ (N + 1) := by
    have := geom_sum_mul q (N + 1)
    linarith
  have hgeom_le : ∑ k ∈ Finset.range (N + 1), q ^ k ≤ 1 / (1 - q) := by
    rw [le_div_iff₀ h1q, mul_comm, hgeom]
    linarith [pow_nonneg hq0 (N + 1)]
  have htail_nn : 0 ≤ ((N + 1 : ℕ) : ℝ) * q ^ (N + 1) := by positivity
  have hstep : (1 - q) * ∑ k ∈ Finset.range (N + 1), ((k + 1 : ℕ) : ℝ) * q ^ k ≤ 1 / (1 - q) := by
    linarith
  rw [le_div_iff₀ (pow_pos h1q 2)]
  have h1 : (1 - q) ^ 2 * ∑ k ∈ Finset.range (N + 1), ((k + 1 : ℕ) : ℝ) * q ^ k ≤ 1 := by
    have : (1 - q) * (1 / (1 - q)) = 1 := mul_one_div_cancel h1q.ne'
    calc (1 - q) ^ 2 * ∑ k ∈ Finset.range (N + 1), ((k + 1 : ℕ) : ℝ) * q ^ k
        = (1 - q) * ((1 - q) * ∑ k ∈ Finset.range (N + 1), ((k + 1 : ℕ) : ℝ) * q ^ k) := by ring
      _ ≤ (1 - q) * (1 / (1 - q)) := mul_le_mul_of_nonneg_left hstep h1q.le
      _ = 1 := this
  linarith

private lemma isMultiplicative_prod_primePow {f : ArithmeticFunction ℤ}
    (hf : f.IsMultiplicative) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (e : ℕ → ℕ) :
    f (∏ p ∈ P, p ^ e p) = ∏ p ∈ P, f (p ^ e p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [hf.1]
  | insert p s hps ih =>
    have hp : p.Prime := hP p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime (p ^ e p) (∏ q ∈ s, q ^ e q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hqp : q.Prime := hs q hq
      have hne : p ≠ q := fun h => hps (h ▸ hq)
      exact ((Nat.coprime_primes hp hqp).mpr hne).pow (e p) (e q)
    rw [Finset.prod_insert hps, Finset.prod_insert hps, hf.2 hcop, ih hs]

private lemma LSeriesSummable_of_gt_three_halves (E : WeierstrassCurve ℚ)
    {σ : ℝ} (hσ : (3 / 2 : ℝ) < σ) :
    LSeriesSummable ((↑) ∘ E.LFunction) (σ : ℂ) := by
  classical
  obtain ⟨hmult, htriv, hhasse⟩ := LFunction_rat_props E
  set δ : ℝ := σ - 3 / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hexp_neg : 1 / 2 - σ = -(1 + δ) := by dsimp [δ]; ring
  -- Choose P₁ ≥ 900 such that 36 * P₁^(1/2 - σ) ≤ 1/2
  have htend : Filter.Tendsto (fun n : ℕ => 36 * (n : ℝ) ^ (-(1 + δ))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 + δ))) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (show 0 < 1 + δ by linarith)).comp tendsto_natCast_atTop_atTop
    simpa using h1.const_mul 36
  obtain ⟨P₀, hP₀⟩ := Filter.eventually_atTop.mp (htend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  let P₁ : ℕ := max 900 P₀
  have hP₁_900 : 900 ≤ P₁ := le_max_left 900 P₀
  have hP₁_small : ∀ p : ℕ, P₁ ≤ p → 36 * (p : ℝ) ^ (-(1 + δ)) ≤ 1 / 2 := fun p hp =>
    (hP₀ p ((le_max_right 900 P₀).trans hp)).le
  -- Summability of n^{-(1+δ)}
  have hpsumm : Summable (fun n : ℕ => ((n : ℝ) ^ (1 + δ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  let SmallP : Finset ℕ := (Finset.range P₁).filter Nat.Prime
  let Csmall : ℝ := ∏ p ∈ SmallP, (1 / (1 - (p : ℝ) ^ (1 - σ)) ^ 2)
  let B : ℝ := Csmall * Real.exp (72 * ∑' n : ℕ, ((n : ℝ) ^ (1 + δ))⁻¹)
  have hCsmall_pos : 0 ≤ Csmall := by
    refine Finset.prod_nonneg fun p _ => by positivity
  -- Show summability via uniform bound B on finite sums of norms
  have hnorm_summ : Summable (fun n : ℕ => ‖LSeries.term ((↑) ∘ E.LFunction) (σ : ℂ) n‖) := by
    refine summable_of_sum_le (c := B) (fun n => norm_nonneg _) fun s => ?_
    let s' : Finset ℕ := s.filter (fun n => n ≠ 0)
    have hs_eq : ∑ n ∈ s, ‖LSeries.term ((↑) ∘ E.LFunction) (σ : ℂ) n‖ =
        ∑ n ∈ s', |(E.LFunction n : ℝ)| / (n : ℝ) ^ σ := by
      rw [← Finset.sum_filter_add_sum_filter_not s (fun n => n ≠ 0)]
      have hzero : ∑ n ∈ s.filter (fun n => ¬ n ≠ 0),
          ‖LSeries.term ((↑) ∘ E.LFunction) (σ : ℂ) n‖ = 0 := by
        refine Finset.sum_eq_zero fun n hn => ?_
        have hn0 : n = 0 := not_not.mp (Finset.mem_filter.mp hn).2
        subst hn0; simp [LSeries.term_zero]
      rw [hzero, add_zero]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : n ≠ 0 := (Finset.mem_filter.mp hn).2
      rw [LSeries.term_of_ne_zero hn0, Function.comp_apply, norm_div, Complex.norm_intCast,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn0), Complex.ofReal_re]
    rw [hs_eq]
    let N : ℕ := s'.sup id + 1
    let Pset : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime
    -- Factor each n ∈ s' over Pset with exponents in range (N + 1)
    let termP (p k : ℕ) : ℝ := |(E.LFunction (p ^ k) : ℝ)| / (p : ℝ) ^ ((k : ℝ) * σ)
    have htermP_nn : ∀ p k, 0 ≤ termP p k := fun p k =>
      div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    have hfactor : ∀ n ∈ s',
        n = ∏ p ∈ Pset, p ^ (n.factorization p) ∧
        (∀ p ∈ Pset, n.factorization p ∈ Finset.range (N + 1)) ∧
        |(E.LFunction n : ℝ)| / (n : ℝ) ^ σ = ∏ p ∈ Pset, termP p (n.factorization p) := by
      intro n hn
      have hn0 : n ≠ 0 := (Finset.mem_filter.mp hn).2
      have hn_le : n ≤ N := (Finset.le_sup (f := id) hn).trans (Nat.le_succ _)
      have hsupp : n.primeFactors ⊆ Pset := by
        intro p hp
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
        have hple : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpdvd
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpp⟩
      have hprod_eq : ∏ p ∈ Pset, p ^ (n.factorization p) = n := by
        have h1 : ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n :=
          Nat.prod_factorization_pow_eq_self hn0
        conv_rhs => rw [← h1]
        refine (Finset.prod_subset hsupp fun p _ hp_not => ?_).symm
        have h0 : n.factorization p = 0 := by
          rw [← Nat.support_factorization] at hp_not
          exact Finsupp.notMem_support_iff.mp hp_not
        rw [h0, pow_zero]
      have hexp_lt : ∀ p ∈ Pset, n.factorization p ∈ Finset.range (N + 1) := by
        intro p hp
        have hpp : p.Prime := (Finset.mem_filter.mp hp).2
        have hdvd : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
        have hle1 : n.factorization p < p ^ n.factorization p :=
          Nat.lt_pow_self hpp.one_lt
        have hle2 : p ^ n.factorization p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
        exact Finset.mem_range.mpr (by omega)
      refine ⟨hprod_eq.symm, hexp_lt, ?_⟩
      have hf_eq : E.LFunction n = ∏ p ∈ Pset, E.LFunction (p ^ (n.factorization p)) := by
        conv_lhs => rw [← hprod_eq]
        exact isMultiplicative_prod_primePow hmult Pset (fun p hp => (Finset.mem_filter.mp hp).2)
          n.factorization
      have hnum : |(E.LFunction n : ℝ)| = ∏ p ∈ Pset, |(E.LFunction (p ^ (n.factorization p)) : ℝ)| := by
        rw [hf_eq, Int.cast_prod, Finset.abs_prod]
      have hden : (n : ℝ) ^ σ = ∏ p ∈ Pset, (p : ℝ) ^ ((n.factorization p : ℝ) * σ) := by
        conv_lhs => rw [← hprod_eq]
        rw [Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ), ← Real.rpow_mul (Nat.cast_nonneg p)]
      rw [hnum, hden, Finset.prod_div_distrib]
    -- Compare sum over s' to expanded Euler product over Pset via Fin (N + 1)
    have hsum_le_prod : ∑ n ∈ s', |(E.LFunction n : ℝ)| / (n : ℝ) ^ σ ≤
        ∏ p ∈ Pset, ∑ k ∈ Finset.range (N + 1), termP p k := by
      have hprod_expand : ∏ p ∈ Pset, ∑ k ∈ Finset.range (N + 1), termP p k =
          ∑ φ : Pset → Fin (N + 1), ∏ p : Pset, termP p.1 (φ p).1 := by
        calc ∏ p ∈ Pset, ∑ k ∈ Finset.range (N + 1), termP p k
            = ∏ p : Pset, ∑ k : Fin (N + 1), termP p.1 k.1 := by
                rw [← Finset.prod_attach Pset]
                refine Finset.prod_congr rfl fun p _ => ?_
                rw [Fin.sum_univ_eq_sum_range (fun k => termP p.1 k) (N + 1)]
          _ = ∑ φ : Pset → Fin (N + 1), ∏ p : Pset, termP p.1 (φ p).1 := by
                exact Fintype.prod_sum (fun (p : Pset) (k : Fin (N + 1)) => termP p.1 k.1)
      rw [hprod_expand]
      let enc : s' → (Pset → Fin (N + 1)) := fun n p =>
        ⟨n.1.factorization p.1, Finset.mem_range.mp ((hfactor n.1 n.2).2.1 p.1 p.2)⟩
      have henc_inj : Function.Injective enc := by
        intro a b hab
        apply Subtype.ext
        rw [(hfactor a.1 a.2).1, (hfactor b.1 b.2).1]
        refine Finset.prod_congr rfl fun p hp => ?_
        have hval := congrArg (fun f => (f ⟨p, hp⟩).1) hab
        dsimp [enc] at hval
        rw [hval]
      let emb : s' ↪ (Pset → Fin (N + 1)) := ⟨enc, henc_inj⟩
      have hsum_s' : ∑ n ∈ s', |(E.LFunction n : ℝ)| / (n : ℝ) ^ σ =
          ∑ φ ∈ (Finset.univ : Finset s').map emb, ∏ p : Pset, termP p.1 (φ p).1 := by
        rw [Finset.sum_map, ← Finset.sum_attach s']
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [(hfactor n.1 n.2).2.2, ← Finset.prod_attach Pset]
        rfl
      rw [hsum_s']
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun φ _ _ =>
        Finset.prod_nonneg fun p _ => htermP_nn p.1 (φ p).1
    -- Split Pset into small primes (< P₁) and large primes (≥ P₁)
    let Psmall : Finset ℕ := Pset.filter (fun p => p < P₁)
    let Plarge : Finset ℕ := Pset.filter (fun p => ¬ p < P₁)
    have hPset_split : ∏ p ∈ Pset, ∑ k ∈ Finset.range (N + 1), termP p k =
        (∏ p ∈ Psmall, ∑ k ∈ Finset.range (N + 1), termP p k) *
        (∏ p ∈ Plarge, ∑ k ∈ Finset.range (N + 1), termP p k) := by
      rw [Finset.prod_filter_mul_prod_filter_not Pset (fun p => p < P₁)]
    have hsmall_le : ∏ p ∈ Psmall, ∑ k ∈ Finset.range (N + 1), termP p k ≤ Csmall := by
      have hsub_small : Psmall ⊆ SmallP := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpP, hlt⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, (Finset.mem_filter.mp hpP).2⟩
      have hfactor_le : ∀ p ∈ Psmall,
          ∑ k ∈ Finset.range (N + 1), termP p k ≤ 1 / (1 - (p : ℝ) ^ (1 - σ)) ^ 2 := by
        intro p hp
        have hpp : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.one_lt
        have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
        have hq0 : 0 ≤ (p : ℝ) ^ (1 - σ) := Real.rpow_nonneg hp_pos.le _
        have hq1 : (p : ℝ) ^ (1 - σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp_gt1 (by linarith)
        have hsum_le : ∑ k ∈ Finset.range (N + 1), termP p k ≤
            ∑ k ∈ Finset.range (N + 1), ((k + 1 : ℕ) : ℝ) * ((p : ℝ) ^ (1 - σ)) ^ k := by
          refine Finset.sum_le_sum fun k _ => ?_
          dsimp [termP]
          have h1 := htriv p hpp k
          have hden_pos : 0 < (p : ℝ) ^ ((k : ℝ) * σ) := Real.rpow_pos_of_pos hp_pos _
          have hpow_eq : (p : ℝ) ^ k / (p : ℝ) ^ ((k : ℝ) * σ) = ((p : ℝ) ^ (1 - σ)) ^ k := by
            rw [← Real.rpow_natCast (p : ℝ) k, ← Real.rpow_sub hp_pos,
              ← Real.rpow_natCast ((p : ℝ) ^ (1 - σ)) k, ← Real.rpow_mul hp_pos.le]
            congr 1; ring
          calc |(E.LFunction (p ^ k) : ℝ)| / (p : ℝ) ^ ((k : ℝ) * σ)
              ≤ (((k + 1 : ℕ) : ℝ) * (p : ℝ) ^ k) / (p : ℝ) ^ ((k : ℝ) * σ) :=
                div_le_div_of_nonneg_right h1 hden_pos.le
            _ = ((k + 1 : ℕ) : ℝ) * ((p : ℝ) ^ k / (p : ℝ) ^ ((k : ℝ) * σ)) := by ring
            _ = ((k + 1 : ℕ) : ℝ) * ((p : ℝ) ^ (1 - σ)) ^ k := by rw [hpow_eq]
        exact hsum_le.trans (weighted_geom_sum_le hq0 hq1 N)
      have hge1 : ∀ p ∈ SmallP, (1 : ℝ) ≤ 1 / (1 - (p : ℝ) ^ (1 - σ)) ^ 2 := by
        intro p hp
        have hpp : p.Prime := (Finset.mem_filter.mp hp).2
        have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.one_lt
        have hq0 : 0 ≤ (p : ℝ) ^ (1 - σ) := Real.rpow_nonneg (by linarith) _
        have hq1 : (p : ℝ) ^ (1 - σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp_gt1 (by linarith)
        have h1q_pos : 0 < 1 - (p : ℝ) ^ (1 - σ) := by linarith
        have hsq_le : (1 - (p : ℝ) ^ (1 - σ)) ^ 2 ≤ 1 := by nlinarith
        exact (one_le_div (pow_pos h1q_pos 2)).mpr hsq_le
      calc ∏ p ∈ Psmall, ∑ k ∈ Finset.range (N + 1), termP p k
          ≤ ∏ p ∈ Psmall, (1 / (1 - (p : ℝ) ^ (1 - σ)) ^ 2) :=
            Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun k _ => htermP_nn p k) hfactor_le
        _ ≤ ∏ p ∈ SmallP, (1 / (1 - (p : ℝ) ^ (1 - σ)) ^ 2) := by
            rw [← Finset.prod_sdiff hsub_small]
            refine le_mul_of_one_le_left
              (Finset.prod_nonneg fun p hp => le_trans zero_le_one (hge1 p (hsub_small hp))) ?_
            exact Finset.one_le_prod fun p hp => hge1 p (Finset.mem_sdiff.mp hp).1
    have hlarge_le : ∏ p ∈ Plarge, ∑ k ∈ Finset.range (N + 1), termP p k ≤
        Real.exp (72 * ∑' n : ℕ, ((n : ℝ) ^ (1 + δ))⁻¹) := by
      have hfactor_le : ∀ p ∈ Plarge,
          ∑ k ∈ Finset.range (N + 1), termP p k ≤ Real.exp (72 * ((p : ℝ) ^ (1 + δ))⁻¹) := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpP, hge⟩
        have hpp : p.Prime := (Finset.mem_filter.mp hpP).2
        have hpP₁ : P₁ ≤ p := not_lt.mp hge
        have hp900 : 900 ≤ p := hP₁_900.trans hpP₁
        have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
        let r : ℝ := 36 * (p : ℝ) ^ (-(1 + δ))
        have hr0 : 0 ≤ r := by dsimp [r]; positivity
        have hr_half : r ≤ 1 / 2 := hP₁_small p hpP₁
        have hsum_le : ∑ k ∈ Finset.range (N + 1), termP p k ≤
            ∑ k ∈ Finset.range (N + 1), r ^ k := by
          refine Finset.sum_le_sum fun k _ => ?_
          dsimp [termP]
          have h1 := hhasse p hpp hp900 k
          have hden_pos : 0 < (p : ℝ) ^ ((k : ℝ) * σ) := Real.rpow_pos_of_pos hp_pos _
          have hpow_eq : (36 * Real.sqrt (p : ℝ)) ^ k / (p : ℝ) ^ ((k : ℝ) * σ) = r ^ k := by
            rw [mul_pow, mul_div_assoc, Real.sqrt_eq_rpow, ← Real.rpow_natCast ((p : ℝ) ^ (1 / 2 : ℝ)),
              ← Real.rpow_mul hp_pos.le, ← Real.rpow_sub hp_pos]
            have hexp : (1 / 2 : ℝ) * (k : ℝ) - (k : ℝ) * σ = (-(1 + δ)) * (k : ℝ) := by
              rw [show (1 / 2 : ℝ) * (k : ℝ) - (k : ℝ) * σ = (1 / 2 - σ) * (k : ℝ) by ring, hexp_neg]
            rw [hexp, Real.rpow_mul hp_pos.le, Real.rpow_natCast, ← mul_pow]
          exact (div_le_div_of_nonneg_right h1 hden_pos.le).trans_eq hpow_eq
        have h2r : 2 * r = 72 * ((p : ℝ) ^ (1 + δ))⁻¹ := by
          dsimp [r]
          rw [Real.rpow_neg hp_pos.le]
          ring
        calc ∑ k ∈ Finset.range (N + 1), termP p k
            ≤ ∑ k ∈ Finset.range (N + 1), r ^ k := hsum_le
          _ ≤ 1 + 2 * r := geom_sum_le_two_mul hr0 hr_half N
          _ ≤ Real.exp (2 * r) := by linarith [Real.add_one_le_exp (2 * r)]
          _ = Real.exp (72 * ((p : ℝ) ^ (1 + δ))⁻¹) := by rw [h2r]
      calc ∏ p ∈ Plarge, ∑ k ∈ Finset.range (N + 1), termP p k
          ≤ ∏ p ∈ Plarge, Real.exp (72 * ((p : ℝ) ^ (1 + δ))⁻¹) :=
            Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun k _ => htermP_nn p k) hfactor_le
        _ = Real.exp (∑ p ∈ Plarge, 72 * ((p : ℝ) ^ (1 + δ))⁻¹) := (Real.exp_sum _ _).symm
        _ = Real.exp (72 * ∑ p ∈ Plarge, ((p : ℝ) ^ (1 + δ))⁻¹) := by rw [Finset.mul_sum]
        _ ≤ Real.exp (72 * ∑' n : ℕ, ((n : ℝ) ^ (1 + δ))⁻¹) := by
            refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ (by norm_num))
            exact hpsumm.sum_le_tsum Plarge fun n _ => by positivity
    calc ∑ n ∈ s', |(E.LFunction n : ℝ)| / (n : ℝ) ^ σ
        ≤ ∏ p ∈ Pset, ∑ k ∈ Finset.range (N + 1), termP p k := hsum_le_prod
      _ = (∏ p ∈ Psmall, ∑ k ∈ Finset.range (N + 1), termP p k) *
          (∏ p ∈ Plarge, ∑ k ∈ Finset.range (N + 1), termP p k) := hPset_split
      _ ≤ Csmall * Real.exp (72 * ∑' n : ℕ, ((n : ℝ) ^ (1 + δ))⁻¹) :=
          mul_le_mul hsmall_le hlarge_le
            (Finset.prod_nonneg fun p _ => Finset.sum_nonneg fun k _ => htermP_nn p k) hCsmall_pos
  exact hnorm_summ.of_norm

end HasseWeilR1H1

theorem OMA.solution : OMA.R_HasseWeil_exists_hasAnalyticContinuation_rat_R1.H1 := by
  intro E _
  have habs : LSeries.abscissaOfAbsConv ((↑) ∘ E.LFunction) ≤ ((3 / 2 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun σ hσ =>
      HasseWeilR1H1.LSeriesSummable_of_gt_three_halves E hσ
  have hdiff : DifferentiableOn ℂ E.LSeries {s | (3 / 2 : ℝ) < s.re} := by
    intro s hs
    have hs' : LSeries.abscissaOfAbsConv ((↑) ∘ E.LFunction) < (s.re : EReal) :=
      lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hs)
    have ht1 := hasDerivAt_iff_tendsto.mp (LSeries_hasDerivAt hs')
    have ht2 : Filter.Tendsto
        (fun x' : ℂ => ‖x' - s‖⁻¹ *
          ‖E.LSeries x' - E.LSeries s -
            (x' - s) • (-LSeries (LSeries.logMul ((↑) ∘ E.LFunction)) s)‖)
        (nhds s) (nhds 0) := by
      refine ht1.congr fun x' => ?_
      simp only [smul_eq_mul]
      rfl
    exact (hasDerivAt_iff_tendsto.mpr ht2).differentiableAt.differentiableWithinAt
  exact hdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)



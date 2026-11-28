import OMAStatements.S_arxiv_2201_00788
namespace OMA.P_arxiv_2201_00788

open OMA.S_arxiv_2201_00788

/-! ### Explicit `n = 12, m = 9` Lee–Lerario–Lundberg counterexample to Wilmshurst's conjecture -/

private noncomputable def f0 : Polynomial ℂ :=
  (Polynomial.X - 1) ^ 10 * (Polynomial.X ^ 2 + 10 * Polynomial.X + 55)

private noncomputable def g9 : Polynomial ℂ :=
  220 * Polynomial.X ^ 9 - 1485 * Polynomial.X ^ 8 + 4752 * Polynomial.X ^ 7 -
  9240 * Polynomial.X ^ 6 + 11880 * Polynomial.X ^ 5 - 10395 * Polynomial.X ^ 4 +
  6160 * Polynomial.X ^ 3 - 2376 * Polynomial.X ^ 2 + 540 * Polynomial.X - 55

private lemma X12_sub_f0 : Polynomial.X ^ 12 - f0 = g9 := by
  unfold f0 g9
  ring

private noncomputable def p12 (ε : ℝ) : Polynomial ℂ :=
  Polynomial.C (2 : ℂ)⁻¹ * (Polynomial.X ^ 12 + f0 + Polynomial.C (Complex.I * (ε : ℂ)))

private noncomputable def q9 (ε : ℝ) : Polynomial ℂ :=
  Polynomial.C (2 : ℂ)⁻¹ * (g9 - Polynomial.C (Complex.I * (ε : ℂ)))

private lemma p12_eq_X12_add (ε : ℝ) :
    p12 ε = Polynomial.X ^ 12 +
      Polynomial.C (2 : ℂ)⁻¹ * (Polynomial.C (Complex.I * (ε : ℂ)) - g9) := by
  have hf : f0 = Polynomial.X ^ 12 - g9 := by
    have := X12_sub_f0
    linear_combination -this
  unfold p12
  rw [hf]
  have h2 : (Polynomial.C (2 : ℂ)⁻¹ : Polynomial ℂ) * 2 = 1 := by
    rw [show (2 : Polynomial ℂ) = Polynomial.C 2 from rfl, ← map_mul]
    norm_num
  calc Polynomial.C (2 : ℂ)⁻¹ * (Polynomial.X ^ 12 + (Polynomial.X ^ 12 - g9) +
          Polynomial.C (Complex.I * (ε : ℂ)))
      = (Polynomial.C (2 : ℂ)⁻¹ * 2) * Polynomial.X ^ 12 +
        Polynomial.C (2 : ℂ)⁻¹ * (Polynomial.C (Complex.I * (ε : ℂ)) - g9) := by ring
    _ = Polynomial.X ^ 12 +
        Polynomial.C (2 : ℂ)⁻¹ * (Polynomial.C (Complex.I * (ε : ℂ)) - g9) := by rw [h2, one_mul]

private lemma p12_natDegree (ε : ℝ) : (p12 ε).natDegree = 12 := by
  rw [p12_eq_X12_add]
  have hdeg_g9 : g9.natDegree ≤ 9 := by unfold g9; compute_degree!
  have hdeg_tail :
      (Polynomial.C (2 : ℂ)⁻¹ * (Polynomial.C (Complex.I * (ε : ℂ)) - g9)).natDegree < 12 := by
    have h1 : (Polynomial.C (Complex.I * (ε : ℂ)) - g9).natDegree ≤ 9 := by
      calc (Polynomial.C (Complex.I * (ε : ℂ)) - g9).natDegree
          ≤ max (Polynomial.C (Complex.I * (ε : ℂ))).natDegree g9.natDegree :=
            Polynomial.natDegree_sub_le _ _
        _ ≤ 9 := by rw [Polynomial.natDegree_C]; omega
    have h2 : (Polynomial.C (2 : ℂ)⁻¹ * (Polynomial.C (Complex.I * (ε : ℂ)) - g9)).natDegree ≤
        (Polynomial.C (Complex.I * (ε : ℂ)) - g9).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    omega
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact Polynomial.natDegree_X_pow 12
  · simpa [Polynomial.natDegree_X_pow] using hdeg_tail

private lemma q9_natDegree (ε : ℝ) : (q9 ε).natDegree = 9 := by
  have hle : (q9 ε).natDegree ≤ 9 := by
    unfold q9 g9
    compute_degree!
  have hcoeff : (q9 ε).coeff 9 = 110 := by
    unfold q9 g9
    have h55 : ((55 : Polynomial ℂ)).coeff 9 = 0 := by
      change (Polynomial.C (55 : ℂ)).coeff 9 = 0; simp
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.coeff_C, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_ofNat_mul, h55]
    norm_num
  have hge : 9 ≤ (q9 ε).natDegree := Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; norm_num)
  omega

private lemma eval_harm (ε : ℝ) (z : ℂ) :
    (p12 ε).eval z + starRingEnd ℂ ((q9 ε).eval z) =
      ((z ^ 12).re : ℂ) + Complex.I * (((f0.eval z).im + ε : ℝ) : ℂ) := by
  have hgx : g9.eval z = z ^ 12 - f0.eval z := by
    rw [← X12_sub_f0]
    simp
  have hp : (p12 ε).eval z = (2 : ℂ)⁻¹ * (z ^ 12 + f0.eval z + Complex.I * (ε : ℂ)) := by
    unfold p12; simp
  have hq : (q9 ε).eval z = (2 : ℂ)⁻¹ * (z ^ 12 - f0.eval z - Complex.I * (ε : ℂ)) := by
    unfold q9; simp [hgx]
  rw [hp, hq]
  apply Complex.ext
  · simp only [map_mul, map_sub, map_inv₀, map_ofNat, Complex.conj_I, Complex.conj_ofReal,
      Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re]
    norm_num
    ring
  · simp only [map_mul, map_sub, map_inv₀, map_ofNat, Complex.conj_I, Complex.conj_ofReal,
      Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_im]
    norm_num
    ring

private lemma eval_harm_eq_zero_iff (ε : ℝ) (z : ℂ) :
    (p12 ε).eval z + starRingEnd ℂ ((q9 ε).eval z) = 0 ↔
      (z ^ 12).re = 0 ∧ (f0.eval z).im + ε = 0 := by
  rw [eval_harm]
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_re] at hre
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.zero_im] at him
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hre, him⟩
    simp [hre, him]

/-! ### The 12 lines `L_k = {r * w_k : r ∈ ℝ}` where `Re(z^12) = 0` -/

private noncomputable def θ (k : Fin 12) : ℝ :=
  ((2 * k.val + 1 : ℕ) : ℝ) * Real.pi / 24

private lemma exp_I_mul (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ)) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
  rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

private noncomputable def w (k : Fin 12) : ℂ :=
  Complex.exp (Complex.I * (θ k : ℂ))

private lemma w_pow_12 (k : Fin 12) :
    w k ^ 12 = Complex.I * ((-1 : ℝ) ^ k.val : ℂ) := by
  unfold w θ
  rw [← Complex.exp_nat_mul]
  have hexp : ((12 : ℕ) : ℂ) * (Complex.I * (((2 * k.val + 1 : ℕ) : ℝ) * Real.pi / 24 : ℝ)) =
      Complex.I * (((k.val : ℝ) * Real.pi + Real.pi / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexp, exp_I_mul]
  have hcos : Real.cos ((k.val : ℝ) * Real.pi + Real.pi / 2) = 0 := by
    rw [Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]
  have hsin : Real.sin ((k.val : ℝ) * Real.pi + Real.pi / 2) = (-1 : ℝ) ^ k.val := by
    rw [Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]
  rw [hcos, hsin]
  simp [mul_comm]

private lemma re_pow_12_on_line (k : Fin 12) (r : ℝ) :
    (((r : ℂ) * w k) ^ 12).re = 0 := by
  rw [mul_pow, w_pow_12, ← Complex.ofReal_pow, ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.mul_im]
  ring

private lemma mem_lines_of_re_pow_12_eq_zero {z : ℂ} (h : (z ^ 12).re = 0) :
    ∃ (k : Fin 12) (r : ℝ), z = (r : ℂ) * w k := by
  by_cases hz : z = 0
  · exact ⟨0, 0, by simp [hz]⟩
  · have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hz_pol : z = (‖z‖ : ℂ) * Complex.exp (Complex.I * (z.arg : ℂ)) := by
      have h1 := Complex.norm_mul_exp_arg_mul_I z
      rw [mul_comm Complex.I]
      exact h1.symm
    have hcos : Real.cos (12 * z.arg) = 0 := by
      have h12 : z ^ 12 = ((‖z‖ ^ 12 : ℝ) : ℂ) * Complex.exp (Complex.I * ((12 * z.arg : ℝ) : ℂ)) := by
        conv_lhs => rw [hz_pol]
        rw [mul_pow, ← Complex.exp_nat_mul]
        push_cast
        congr 2
        ring
      rw [h12, exp_I_mul] at h
      have hre : (((‖z‖ ^ 12 : ℝ) : ℂ) * ((Real.cos (12 * z.arg) : ℂ) + (Real.sin (12 * z.arg) : ℂ) * Complex.I)).re =
          ‖z‖ ^ 12 * Real.cos (12 * z.arg) := by
        simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.mul_im, Complex.add_im]
        ring
      rw [hre] at h
      have hpow_ne : ‖z‖ ^ 12 ≠ 0 := pow_ne_zero 12 hnorm
      exact (mul_eq_zero.mp h).resolve_left hpow_ne
    obtain ⟨m, hm⟩ := Real.cos_eq_zero_iff.mp hcos
    let k_int : ℤ := m % 12
    have hk_nonneg : 0 ≤ k_int := Int.emod_nonneg m (by norm_num)
    have hk_lt : k_int < 12 := Int.emod_lt_of_pos m (by norm_num)
    let k : Fin 12 := ⟨k_int.toNat, by omega⟩
    let q : ℤ := m / 12
    have hmq : m = 12 * q + k.val := by
      have hk_coe : (k.val : ℤ) = k_int := Int.toNat_of_nonneg hk_nonneg
      omega
    have harg : z.arg = (q : ℝ) * Real.pi + θ k := by
      unfold θ
      have hm' : (m : ℝ) = 12 * (q : ℝ) + (k.val : ℝ) := by exact_mod_cast hmq
      have h1 : 12 * z.arg = (2 * (m : ℝ) + 1) * Real.pi / 2 := by linarith
      rw [hm'] at h1
      push_cast
      linarith
    have hexp_eq : Complex.exp (Complex.I * (z.arg : ℂ)) =
        (((-1 : ℝ) ^ q : ℝ) : ℂ) * w k := by
      rw [harg]
      push_cast
      rw [mul_add, Complex.exp_add]
      congr 1
      have hqpi : (q : ℂ) * (Real.pi : ℂ) = (((q : ℝ) * Real.pi : ℝ) : ℂ) := by push_cast; rfl
      rw [hqpi, exp_I_mul, Real.cos_int_mul_pi, Real.sin_int_mul_pi]
      simp
    refine ⟨k, ‖z‖ * (-1 : ℝ) ^ q, ?_⟩
    conv_lhs => rw [hz_pol, hexp_eq]
    rw [Complex.ofReal_mul, mul_assoc]

private lemma w_lines_disjoint {k₁ k₂ : Fin 12} {r₁ r₂ : ℝ} (hr₁ : r₁ ≠ 0)
    (heq : (r₁ : ℂ) * w k₁ = (r₂ : ℂ) * w k₂) : k₁ = k₂ ∧ r₁ = r₂ := by
  have hw2_ne : w k₂ ≠ 0 := Complex.exp_ne_zero _
  have hratio : Complex.exp (Complex.I * ((θ k₁ - θ k₂ : ℝ) : ℂ)) = ((r₂ / r₁ : ℝ) : ℂ) := by
    have h1 : w k₁ * (w k₂)⁻¹ = ((r₂ / r₁ : ℝ) : ℂ) := by
      have hr1c : (r₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr₁
      rw [div_eq_mul_inv]
      push_cast
      have hmul := congrArg (· * ((r₁ : ℂ)⁻¹ * (w k₂)⁻¹)) heq
      have lhs_eq : (r₁ : ℂ) * w k₁ * ((r₁ : ℂ)⁻¹ * (w k₂)⁻¹) = w k₁ * (w k₂)⁻¹ := by
        field_simp [hr1c, hw2_ne]
      have rhs_eq : (r₂ : ℂ) * w k₂ * ((r₁ : ℂ)⁻¹ * (w k₂)⁻¹) = (r₂ : ℂ) * (r₁ : ℂ)⁻¹ := by
        field_simp [hr1c, hw2_ne]
      rw [lhs_eq, rhs_eq] at hmul
      exact hmul
    rw [← h1]
    unfold w
    rw [← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsin : Real.sin (θ k₁ - θ k₂) = 0 := by
    have him := congrArg Complex.im hratio
    rw [exp_I_mul] at him
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] at him
    linarith
  have hk_eq : k₁ = k₂ := by
    by_contra hne
    have hval_ne : k₁.val ≠ k₂.val := fun h => hne (Fin.ext h)
    by_cases hlt : k₂.val < k₁.val
    · have hpos : 0 < θ k₁ - θ k₂ := by
        unfold θ; push_cast
        have h1 : ((k₂.val : ℝ) + 1) ≤ (k₁.val : ℝ) := by exact_mod_cast hlt
        have hpi := Real.pi_pos
        nlinarith
      have hlt_pi : θ k₁ - θ k₂ < Real.pi := by
        unfold θ; push_cast
        have h1 : (k₁.val : ℝ) ≤ 11 := by exact_mod_cast Nat.lt_succ_iff.mp k₁.isLt
        have h2 : (0 : ℝ) ≤ (k₂.val : ℝ) := Nat.cast_nonneg _
        have hpi := Real.pi_pos
        nlinarith
      exact (Real.sin_pos_of_pos_of_lt_pi hpos hlt_pi).ne' hsin
    · have hgt : k₁.val < k₂.val := by omega
      have hpos : 0 < θ k₂ - θ k₁ := by
        unfold θ; push_cast
        have h1 : ((k₁.val : ℝ) + 1) ≤ (k₂.val : ℝ) := by exact_mod_cast hgt
        have hpi := Real.pi_pos
        nlinarith
      have hlt_pi : θ k₂ - θ k₁ < Real.pi := by
        unfold θ; push_cast
        have h1 : (k₂.val : ℝ) ≤ 11 := by exact_mod_cast Nat.lt_succ_iff.mp k₂.isLt
        have h2 : (0 : ℝ) ≤ (k₁.val : ℝ) := Nat.cast_nonneg _
        have hpi := Real.pi_pos
        nlinarith
      have hsin' : Real.sin (θ k₂ - θ k₁) = 0 := by
        rw [show θ k₂ - θ k₁ = -(θ k₁ - θ k₂) by ring, Real.sin_neg, hsin, neg_zero]
      exact (Real.sin_pos_of_pos_of_lt_pi hpos hlt_pi).ne' hsin'
  subst hk_eq
  have hr_eq : r₁ = r₂ := by
    have hmul := mul_right_cancel₀ hw2_ne heq
    exact Complex.ofReal_injective hmul
  exact ⟨rfl, hr_eq⟩

/-! ### Finiteness of the zero set of `p12 ε + conj (q9 ε)` -/

private lemma zeroSet_finite (ε : ℝ) :
    {z : ℂ | (p12 ε).eval z + starRingEnd ℂ ((q9 ε).eval z) = 0}.Finite := by
  have hsub : {z : ℂ | (p12 ε).eval z + starRingEnd ℂ ((q9 ε).eval z) = 0} ⊆
      ⋃ k : Fin 12, (fun r : ℝ => (r : ℂ) * w k) ''
        {r : ℝ | (f0.eval ((r : ℂ) * w k)).im + ε = 0} := by
    intro z hz
    change (p12 ε).eval z + starRingEnd ℂ ((q9 ε).eval z) = 0 at hz
    rw [eval_harm_eq_zero_iff] at hz
    rcases mem_lines_of_re_pow_12_eq_zero hz.1 with ⟨k, r, rfl⟩
    exact Set.mem_iUnion.mpr ⟨k, r, hz.2, rfl⟩
  refine Set.Finite.subset ?_ hsub
  refine Set.finite_iUnion fun k => Set.Finite.image _ ?_
  -- Build the real polynomial `P_k(r) = Im(f0(r * w k)) + ε` of degree 12!
  let Pk : Polynomial ℝ :=
    Polynomial.C ε + ∑ j ∈ Finset.range 13,
      Polynomial.C ((f0.coeff j * w k ^ j).im) * Polynomial.X ^ j
  have hPk_eval : ∀ r : ℝ, Pk.eval r = (f0.eval ((r : ℂ) * w k)).im + ε := by
    intro r
    have hdeg_f0 : f0.natDegree ≤ 12 := by unfold f0; compute_degree!
    have hf0_eq : f0.eval ((r : ℂ) * w k) =
        ∑ j ∈ Finset.range 13, f0.coeff j * ((r : ℂ) * w k) ^ j := by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg_f0)]
    have him : (f0.eval ((r : ℂ) * w k)).im =
        ∑ j ∈ Finset.range 13, (f0.coeff j * w k ^ j).im * r ^ j := by
      rw [hf0_eq, Complex.im_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_pow, show f0.coeff j * ((r : ℂ) ^ j * w k ^ j) =
          (f0.coeff j * w k ^ j) * ((r ^ j : ℝ) : ℂ) by push_cast; ring]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    simp only [Pk, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, him]
    ring
  have hPk_ne : Pk ≠ 0 := by
    intro h0
    have hc12 : Pk.coeff 12 = 0 := by rw [h0]; simp
    have hcoeff12 : Pk.coeff 12 = (f0.coeff 12 * w k ^ 12).im := by
      simp only [Pk, Polynomial.coeff_add, Polynomial.coeff_C, show (12 : ℕ) ≠ 0 by decide,
        if_false, zero_add, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq (Finset.range 13) 12]
      simp
    have hf0_12 : f0.coeff 12 = 1 := by
      have hf : f0 = Polynomial.X ^ 12 - g9 := by
        have := X12_sub_f0
        linear_combination -this
      have hg9_12 : g9.coeff 12 = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have : g9.natDegree ≤ 9 := by unfold g9; compute_degree!
        omega
      rw [hf, Polynomial.coeff_sub, Polynomial.coeff_X_pow_self, hg9_12, sub_zero]
    rw [hcoeff12, hf0_12, one_mul, w_pow_12] at hc12
    have him12 : (Complex.I * ((-1 : ℝ) ^ k.val : ℂ)).im = (-1 : ℝ) ^ k.val := by
      rw [← Complex.ofReal_pow]
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [him12] at hc12
    exact pow_ne_zero k.val (by norm_num : (-1 : ℝ) ≠ 0) hc12
  have hroots : {r : ℝ | (f0.eval ((r : ℂ) * w k)).im + ε = 0} = {r : ℝ | Pk.IsRoot r} := by
    ext r; simp [Polynomial.IsRoot, hPk_eval]
  rw [hroots]
  exact Polynomial.finite_setOfPred_isRoot hPk_ne

/-! ### Polar factorization of `f0(r * w k)` via `Real.arctan` -/

private noncomputable def z1 : ℂ := 1
private noncomputable def zp : ℂ := -5 + Complex.I * (Real.sqrt 30 : ℂ)
private noncomputable def zm : ℂ := -5 - Complex.I * (Real.sqrt 30 : ℂ)

private lemma f0_eval_factor (z : ℂ) :
    f0.eval z = (z - z1) ^ 10 * (z - zp) * (z - zm) := by
  have h30 : ((Real.sqrt 30 : ℝ) : ℂ) ^ 2 = 30 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hquad : (z - zp) * (z - zm) = z ^ 2 + 10 * z + 55 := by
    unfold zp zm
    calc (z - (-5 + Complex.I * (Real.sqrt 30 : ℂ))) *
          (z - (-5 - Complex.I * (Real.sqrt 30 : ℂ)))
        = (z + 5) ^ 2 - Complex.I ^ 2 * ((Real.sqrt 30 : ℝ) : ℂ) ^ 2 := by ring
      _ = (z + 5) ^ 2 - (-1) * 30 := by rw [Complex.I_sq, h30]
      _ = z ^ 2 + 10 * z + 55 := by ring
  unfold f0 z1
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  rw [mul_assoc, hquad]

private noncomputable def rotRe (z0 : ℂ) (t : ℝ) : ℝ :=
  z0.re * Real.cos t + z0.im * Real.sin t

private noncomputable def rotIm (z0 : ℂ) (t : ℝ) : ℝ :=
  -z0.re * Real.sin t + z0.im * Real.cos t

private lemma linear_polar (z0 : ℂ) (t r : ℝ) (hb : rotIm z0 t ≠ 0) :
    let a := rotRe z0 t
    let b := rotIm z0 t
    let s : ℝ := if 0 < b then 1 else -1
    (r : ℂ) * Complex.exp (Complex.I * (t : ℂ)) - z0 =
      ((Real.sqrt ((r - a) ^ 2 + b ^ 2) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((t + s * (Real.arctan ((r - a) / |b|) - Real.pi / 2) : ℝ) : ℂ)) := by
  intro a b s
  have hb_pos : 0 < |b| := abs_pos.mpr hb
  have hsb : s * |b| = b := by
    dsimp [s]
    split_ifs with h
    · rw [one_mul, abs_of_pos h]
    · rw [neg_one_mul, abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hb)]; ring
  have hs_sq : s * s = 1 := by dsimp [s]; split_ifs <;> ring
  -- Factor `z0 = (a + I * b) * exp(I * t)`:
  have hz0_eq : z0 = ((a : ℂ) + Complex.I * (b : ℂ)) * Complex.exp (Complex.I * (t : ℂ)) := by
    rw [exp_I_mul]
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.add_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.add_im]
      dsimp [a, b, rotRe, rotIm]
      have hc := Real.sin_sq_add_cos_sq t
      linear_combination -z0.re * hc
    · simp only [Complex.mul_im, Complex.add_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.add_re]
      dsimp [a, b, rotRe, rotIm]
      have hc := Real.sin_sq_add_cos_sq t
      linear_combination -z0.im * hc
  have hstep1 : (r : ℂ) * Complex.exp (Complex.I * (t : ℂ)) - z0 =
      (((r - a : ℝ) : ℂ) - Complex.I * (b : ℂ)) * Complex.exp (Complex.I * (t : ℂ)) := by
    conv_lhs => rw [hz0_eq]
    push_cast; ring
  rw [hstep1]
  have hexp_split :
      Complex.exp (Complex.I * ((t + s * (Real.arctan ((r - a) / |b|) - Real.pi / 2) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((s * (Real.arctan ((r - a) / |b|) - Real.pi / 2) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1; push_cast; ring
  rw [hexp_split, ← mul_assoc]
  congr 1
  -- Show `(r - a) - I * b = √((r-a)^2 + b^2) * exp(I * s * (arctan((r-a)/|b|) - π/2))`!
  let u : ℝ := (r - a) / |b|
  have hsqrt_eq : Real.sqrt ((r - a) ^ 2 + b ^ 2) = |b| * Real.sqrt (1 + u ^ 2) := by
    have hu : (r - a) ^ 2 + b ^ 2 = |b| ^ 2 * (1 + u ^ 2) := by
      dsimp [u]
      have hne : |b| ≠ 0 := hb_pos.ne'
      field_simp [hne]
      rw [sq_abs]
      ring
    rw [hu, Real.sqrt_mul (sq_nonneg |b|), Real.sqrt_sq hb_pos.le]
  have hden_pos : 0 < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hcos_val : Real.cos (s * (Real.arctan u - Real.pi / 2)) = u / Real.sqrt (1 + u ^ 2) := by
    have h1 : Real.cos (s * (Real.arctan u - Real.pi / 2)) =
        Real.cos (Real.arctan u - Real.pi / 2) := by
      dsimp [s]; split_ifs
      · rw [one_mul]
      · rw [neg_one_mul, Real.cos_neg]
    rw [h1, Real.cos_sub_pi_div_two, Real.sin_arctan]
  have hsin_val : Real.sin (s * (Real.arctan u - Real.pi / 2)) =
      -s / Real.sqrt (1 + u ^ 2) := by
    have h1 : Real.sin (s * (Real.arctan u - Real.pi / 2)) =
        s * Real.sin (Real.arctan u - Real.pi / 2) := by
      dsimp [s]; split_ifs
      · rw [one_mul, one_mul]
      · rw [neg_one_mul, Real.sin_neg, neg_one_mul]
    rw [h1, Real.sin_sub_pi_div_two, Real.cos_arctan]
    ring
  rw [exp_I_mul, hcos_val, hsin_val, hsqrt_eq]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.add_re]
    dsimp [u]
    have hne1 : |b| ≠ 0 := hb_pos.ne'
    have hne2 : Real.sqrt (1 + ((r - a) / |b|) ^ 2) ≠ 0 := hden_pos.ne'
    field_simp [hne1, hne2]
    ring
  · simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.add_im]
    have hne2 : Real.sqrt (1 + u ^ 2) ≠ 0 := hden_pos.ne'
    field_simp [hne2]
    nlinarith [hsb]

/-! ### Exact signs of `rotIm` on all 12 lines `L_k` -/

private lemma sin_θ_pos (k : Fin 12) : 0 < Real.sin (θ k) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · unfold θ; positivity
  · unfold θ
    have hk : ((2 * k.val + 1 : ℕ) : ℝ) < 24 := by
      have : 2 * k.val + 1 < 24 := by omega
      exact_mod_cast this
    have hpi := Real.pi_pos
    nlinarith

private lemma rotIm_z1_neg (k : Fin 12) : rotIm z1 (θ k) < 0 := by
  unfold rotIm z1
  simp only [Complex.one_re, Complex.one_im, zero_mul, add_zero]
  linarith [sin_θ_pos k]

private lemma cos_7pi_div_12_lt : Real.cos (7 * Real.pi / 12) < -(1 : ℝ) / 11 := by
  have hsplit : 7 * Real.pi / 12 = Real.pi / 3 + Real.pi / 4 := by ring
  rw [hsplit, Real.cos_add, Real.cos_pi_div_three, Real.cos_pi_div_four,
    Real.sin_pi_div_three, Real.sin_pi_div_four]
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  -- Need `(1/2)*(√2/2) - (√3/2)*(√2/2) < -1/11`, i.e., `11 * √2 * (√3 - 1) > 4`!
  -- Square: `121 * 2 * (4 - 2√3) = 968 - 484√3 > 16 ↔ 484√3 < 952 ↔ 484^2 * 3 = 702768 < 906304 = 952^2`!
  have h484 : 484 * Real.sqrt 3 < 952 := by nlinarith
  have hsq : (11 * (Real.sqrt 3 - 1) * Real.sqrt 2) ^ 2 > 16 := by
    have : (11 * (Real.sqrt 3 - 1) * Real.sqrt 2) ^ 2 = 968 - 484 * Real.sqrt 3 := by
      nlinarith [h2sq, h3sq]
    linarith
  have hpos : 0 < 11 * (Real.sqrt 3 - 1) * Real.sqrt 2 := by
    have : (1 : ℝ) < Real.sqrt 3 := by nlinarith
    positivity
  have hgt4 : 4 < 11 * (Real.sqrt 3 - 1) * Real.sqrt 2 := by nlinarith
  linarith

private lemma outer_cos_2θ_pos (k : Fin 12) (hk : k.val ≤ 2 ∨ 9 ≤ k.val) :
    0 < Real.cos (2 * θ k) := by
  have hpi := Real.pi_pos
  rcases hk with hle | hge
  · apply Real.cos_pos_of_mem_Ioo
    refine ⟨?_, ?_⟩
    · unfold θ; have : (0 : ℝ) < ((2 * k.val + 1 : ℕ) : ℝ) := by positivity
      nlinarith
    · unfold θ
      have : ((2 * k.val + 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (show 2 * k.val + 1 ≤ 5 by omega)
      nlinarith
  · have hsym : Real.cos (2 * θ k) = Real.cos (2 * Real.pi - 2 * θ k) := by
      rw [Real.cos_two_pi_sub]
    rw [hsym]
    apply Real.cos_pos_of_mem_Ioo
    refine ⟨?_, ?_⟩
    · unfold θ
      have : ((2 * k.val + 1 : ℕ) : ℝ) ≤ 23 := by exact_mod_cast (show 2 * k.val + 1 ≤ 23 by omega)
      nlinarith
    · unfold θ
      have : (19 : ℝ) ≤ ((2 * k.val + 1 : ℕ) : ℝ) := by exact_mod_cast (show 19 ≤ 2 * k.val + 1 by omega)
      nlinarith

private lemma inner_cos_2θ_lt (k : Fin 12) (hk : 3 ≤ k.val ∧ k.val ≤ 8) :
    Real.cos (2 * θ k) < -(1 : ℝ) / 11 := by
  have hpi := Real.pi_pos
  by_cases hle5 : k.val ≤ 5
  · -- `7π/12 ≤ 2θ k ≤ 11π/12 < π`, where `cos` is decreasing!
    have h1 : 7 * Real.pi / 12 ≤ 2 * θ k := by
      unfold θ
      have : (7 : ℝ) ≤ ((2 * k.val + 1 : ℕ) : ℝ) := by exact_mod_cast (show 7 ≤ 2 * k.val + 1 by omega)
      nlinarith
    have h2 : 2 * θ k ≤ Real.pi := by
      unfold θ
      have : ((2 * k.val + 1 : ℕ) : ℝ) ≤ 11 := by exact_mod_cast (show 2 * k.val + 1 ≤ 11 by omega)
      nlinarith
    have hdec : Real.cos (2 * θ k) ≤ Real.cos (7 * Real.pi / 12) :=
      Real.strictAntiOn_cos.antitoneOn
        ⟨by linarith, by linarith⟩ ⟨by linarith, h2⟩ h1
    exact lt_of_le_of_lt hdec cos_7pi_div_12_lt
  · -- `13π/12 ≤ 2θ k ≤ 17π/12`: reflect via `cos(2π - x) = cos x` into `[7π/12, 11π/12]`!
    have hsym : Real.cos (2 * θ k) = Real.cos (2 * Real.pi - 2 * θ k) := by
      rw [Real.cos_two_pi_sub]
    rw [hsym]
    have h1 : 7 * Real.pi / 12 ≤ 2 * Real.pi - 2 * θ k := by
      unfold θ
      have : ((2 * k.val + 1 : ℕ) : ℝ) ≤ 17 := by exact_mod_cast (show 2 * k.val + 1 ≤ 17 by omega)
      nlinarith
    have h2 : 2 * Real.pi - 2 * θ k ≤ Real.pi := by
      unfold θ
      have : (13 : ℝ) ≤ ((2 * k.val + 1 : ℕ) : ℝ) := by exact_mod_cast (show 13 ≤ 2 * k.val + 1 by omega)
      nlinarith
    have hdec : Real.cos (2 * Real.pi - 2 * θ k) ≤ Real.cos (7 * Real.pi / 12) :=
      Real.strictAntiOn_cos.antitoneOn
        ⟨by linarith, by linarith⟩ ⟨by linarith, h2⟩ h1
    exact lt_of_le_of_lt hdec cos_7pi_div_12_lt

private lemma rotIm_zp_zm_outer (k : Fin 12) (hk : k.val ≤ 2 ∨ 9 ≤ k.val) :
    (0 < rotIm zp (θ k) ∧ rotIm zm (θ k) < 0) ∨ (rotIm zp (θ k) < 0 ∧ 0 < rotIm zm (θ k)) := by
  have hcos2 := outer_cos_2θ_pos k hk
  have h2 : Real.cos (2 * θ k) = Real.cos (θ k) ^ 2 - Real.sin (θ k) ^ 2 := Real.cos_two_mul' (θ k)
  have hsc : Real.sin (θ k) ^ 2 < Real.cos (θ k) ^ 2 := by linarith
  have h30 : Real.sqrt 30 ^ 2 = 30 := Real.sq_sqrt (by norm_num)
  have h30_pos : 0 < Real.sqrt 30 := Real.sqrt_pos.mpr (by norm_num)
  have hsin_pos : 0 < Real.sin (θ k) := sin_θ_pos k
  have hbp : rotIm zp (θ k) = 5 * Real.sin (θ k) + Real.sqrt 30 * Real.cos (θ k) := by
    unfold rotIm zp; simp
  have hbm : rotIm zm (θ k) = 5 * Real.sin (θ k) - Real.sqrt 30 * Real.cos (θ k) := by
    unfold rotIm zm; simp; ring
  have hprod : rotIm zp (θ k) * rotIm zm (θ k) < 0 := by
    rw [hbp, hbm]
    have : (5 * Real.sin (θ k) + Real.sqrt 30 * Real.cos (θ k)) *
        (5 * Real.sin (θ k) - Real.sqrt 30 * Real.cos (θ k)) =
        25 * Real.sin (θ k) ^ 2 - 30 * Real.cos (θ k) ^ 2 := by nlinarith [h30]
    nlinarith
  by_cases hp : 0 < rotIm zp (θ k)
  · left; exact ⟨hp, by nlinarith⟩
  · right
    have hp' : rotIm zp (θ k) < 0 := by
      by_contra hge
      have h0 : rotIm zp (θ k) = 0 := le_antisymm (not_lt.mp hp) (not_lt.mp hge)
      rw [h0, zero_mul] at hprod; exact lt_irrefl 0 hprod
    exact ⟨hp', by nlinarith⟩

private lemma rotIm_zp_zm_inner (k : Fin 12) (hk : 3 ≤ k.val ∧ k.val ≤ 8) :
    0 < rotIm zp (θ k) ∧ 0 < rotIm zm (θ k) := by
  have hcos2 := inner_cos_2θ_lt k hk
  have h2 : Real.cos (2 * θ k) = Real.cos (θ k) ^ 2 - Real.sin (θ k) ^ 2 := Real.cos_two_mul' (θ k)
  have h1 : Real.sin (θ k) ^ 2 + Real.cos (θ k) ^ 2 = 1 := Real.sin_sq_add_cos_sq (θ k)
  have h30 : Real.sqrt 30 ^ 2 = 30 := Real.sq_sqrt (by norm_num)
  have hsin_pos : 0 < Real.sin (θ k) := sin_θ_pos k
  have hbp : rotIm zp (θ k) = 5 * Real.sin (θ k) + Real.sqrt 30 * Real.cos (θ k) := by
    unfold rotIm zp; simp
  have hbm : rotIm zm (θ k) = 5 * Real.sin (θ k) - Real.sqrt 30 * Real.cos (θ k) := by
    unfold rotIm zm; simp; ring
  have hprod : 0 < rotIm zp (θ k) * rotIm zm (θ k) := by
    rw [hbp, hbm]
    have : (5 * Real.sin (θ k) + Real.sqrt 30 * Real.cos (θ k)) *
        (5 * Real.sin (θ k) - Real.sqrt 30 * Real.cos (θ k)) =
        25 * Real.sin (θ k) ^ 2 - 30 * Real.cos (θ k) ^ 2 := by nlinarith [h30]
    nlinarith
  have hsum : 0 < rotIm zp (θ k) + rotIm zm (θ k) := by
    rw [hbp, hbm]; linarith
  constructor <;> nlinarith

private lemma rotIm_all_ne_zero (k : Fin 12) :
    rotIm z1 (θ k) ≠ 0 ∧ rotIm zp (θ k) ≠ 0 ∧ rotIm zm (θ k) ≠ 0 := by
  refine ⟨(rotIm_z1_neg k).ne, ?_⟩
  by_cases hk : k.val ≤ 2 ∨ 9 ≤ k.val
  · rcases rotIm_zp_zm_outer k hk with ⟨hp, hm⟩ | ⟨hp, hm⟩
    · exact ⟨hp.ne', hm.ne⟩
    · exact ⟨hp.ne, hm.ne'⟩
  · have hkin : 3 ≤ k.val ∧ k.val ≤ 8 := by omega
    rcases rotIm_zp_zm_inner k hkin with ⟨hp, hm⟩
    exact ⟨hp.ne', hm.ne'⟩

/-! ### Generic IVT oscillation lemma: `N` distinct roots from an angle change of `N * π` -/

private lemma exists_roots_of_angle_limits
    {Θ R : ℝ → ℝ} {ε : ℝ} {k N : ℕ}
    (hε : 0 < ε) (hN : 1 ≤ N)
    (hΘ_cont : Continuous Θ) (hR_cont : Continuous R)
    (hR_lb : ∀ r : ℝ, 4 * ε ≤ R r)
    (hTop : Filter.Tendsto Θ Filter.atTop (nhds ((k : ℝ) * Real.pi + Real.pi / 2)))
    (hBot : Filter.Tendsto Θ Filter.atBot (nhds (((k + N : ℕ) : ℝ) * Real.pi + Real.pi / 2))) :
    ∃ S : Finset ℝ, S.card = N ∧ ∀ r ∈ S, R r * Real.sin (Θ r) + ε = 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  -- Step 1: Pick `M_hi` with `|Θ M_hi - (k*π + π/2)| < π/3`, and `M_lo < M_hi` with `|Θ M_lo - ((k+N)*π + π/2)| < π/3`.
  have hhi_ev : ∀ᶠ r in Filter.atTop,
      Θ r ∈ Set.Ioo ((k : ℝ) * Real.pi + Real.pi / 2 - Real.pi / 3)
        ((k : ℝ) * Real.pi + Real.pi / 2 + Real.pi / 3) :=
    hTop.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨M_hi, hM_hi⟩ := hhi_ev.exists
  have hlo_ev : ∀ᶠ r in Filter.atBot,
      Θ r ∈ Set.Ioo (((k + N : ℕ) : ℝ) * Real.pi + Real.pi / 2 - Real.pi / 3)
        (((k + N : ℕ) : ℝ) * Real.pi + Real.pi / 2 + Real.pi / 3) ∧ r < M_hi :=
    (hBot.eventually (Ioo_mem_nhds (by linarith) (by linarith))).and (Filter.eventually_lt_atBot M_hi)
  obtain ⟨M_lo, hM_lo, hlt_M⟩ := hlo_ev.exists
  -- Step 2: Inductively find `r : Fin (N + 1) → ℝ` with `r 0 = M_lo`, `r N = M_hi`,
  -- strictly increasing, and `Θ (r j) = (k + N - j)*π + π/2` for `1 ≤ j ≤ N - 1`!
  have hchain : ∀ m : ℕ, m ≤ N →
      ∃ seq : Fin (m + 1) → ℝ,
        seq 0 = M_lo ∧
        (∀ i : Fin m, seq ⟨i.val, by omega⟩ < seq ⟨i.val + 1, by omega⟩) ∧
        (m < N → seq ⟨m, by omega⟩ < M_hi) ∧
        (∀ j : Fin (m + 1),
          (j.val = 0 → Θ (seq j) ∈ Set.Ioo (((k + N : ℕ) : ℝ) * Real.pi + Real.pi / 2 - Real.pi / 3)
            (((k + N : ℕ) : ℝ) * Real.pi + Real.pi / 2 + Real.pi / 3)) ∧
          (0 < j.val → j.val < N →
            Θ (seq j) = ((k + N - j.val : ℕ) : ℝ) * Real.pi + Real.pi / 2) ∧
          (j.val = N → Θ (seq j) ∈ Set.Ioo ((k : ℝ) * Real.pi + Real.pi / 2 - Real.pi / 3)
            ((k : ℝ) * Real.pi + Real.pi / 2 + Real.pi / 3))) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun _ => M_lo, rfl, fun i => i.elim0, fun _ => hlt_M, ?_⟩
      intro j
      have hj0 : j.val = 0 := by omega
      exact ⟨fun _ => hM_lo, fun h => by omega, fun h => by omega⟩
    | succ m ih =>
      intro hmN
      rcases ih (by omega) with ⟨seq, h0, hinc, hlt_hi, hval⟩
      have hlast_lt : seq ⟨m, by omega⟩ < M_hi := hlt_hi (by omega)
      by_cases hm_end : m + 1 = N
      · -- Final step `m + 1 = N`: append `M_hi`!
        let seq' : Fin (m + 2) → ℝ := fun j =>
          if hj : j.val ≤ m then seq ⟨j.val, by omega⟩ else M_hi
        refine ⟨seq', by simp [seq', h0], ?_, fun h => by omega, ?_⟩
        · intro i
          by_cases him : i.val < m
          · have h1 : i.val ≤ m := by omega
            have h2 : i.val + 1 ≤ m := by omega
            simpa [seq', h1, h2] using hinc ⟨i.val, him⟩
          · have him_eq : i.val = m := by omega
            have h1 : i.val ≤ m := by omega
            have h2 : ¬ i.val + 1 ≤ m := by omega
            simp only [seq', h1, h2, ↓reduceDIte]
            convert hlast_lt using 2
            exact Fin.ext him_eq
        · intro j
          by_cases hjm : j.val ≤ m
          · simp only [seq', hjm, ↓reduceDIte]
            have hv := hval ⟨j.val, by omega⟩
            exact ⟨hv.1, fun h1 h2 => hv.2.1 h1 h2, fun h => by omega⟩
          · have hjN : j.val = N := by omega
            simp only [seq', hjm, ↓reduceDIte]
            exact ⟨fun h => by omega, fun _ h => by omega, fun _ => hM_hi⟩
      · -- Intermediate step `m + 1 < N`: use IVT on `[seq m, M_hi]` to hit `target = (k + N - (m+1))*π + π/2`!
        let target : ℝ := ((k + N - (m + 1) : ℕ) : ℝ) * Real.pi + Real.pi / 2
        have hlo_gt : target < Θ (seq ⟨m, by omega⟩) := by
          have hv := hval ⟨m, by omega⟩
          by_cases hm0 : m = 0
          · have hmem := hv.1 hm0
            have hcast : ((k + N : ℕ) : ℝ) = ((k + N - (m + 1) : ℕ) : ℝ) + 1 := by
              have : k + N = (k + N - (m + 1)) + 1 := by omega
              exact_mod_cast this
            dsimp [target]
            nlinarith [hmem.1]
          · have heq := hv.2.1 (by dsimp; omega) (by dsimp; omega)
            have hcast : ((k + N - m : ℕ) : ℝ) = ((k + N - (m + 1) : ℕ) : ℝ) + 1 := by
              have : k + N - m = (k + N - (m + 1)) + 1 := by omega
              exact_mod_cast this
            rw [heq]
            dsimp [target]
            nlinarith
        have hhi_lt : Θ M_hi < target := by
          have hge1 : (k : ℝ) + 1 ≤ ((k + N - (m + 1) : ℕ) : ℝ) := by
            have : k + 1 ≤ k + N - (m + 1) := by omega
            exact_mod_cast this
          dsimp [target]
          nlinarith [hM_hi.2]
        have hmem_Icc : target ∈ Set.Icc (Θ M_hi) (Θ (seq ⟨m, by omega⟩)) := ⟨hhi_lt.le, hlo_gt.le⟩
        obtain ⟨x, hx_Icc, hx_eq⟩ := intermediate_value_Icc' hlast_lt.le hΘ_cont.continuousOn hmem_Icc
        have hx_gt : seq ⟨m, by omega⟩ < x := lt_of_le_of_ne hx_Icc.1 (fun h => by rw [← h] at hx_eq; linarith)
        have hx_lt : x < M_hi := lt_of_le_of_ne hx_Icc.2 (fun h => by rw [h] at hx_eq; linarith)
        let seq' : Fin (m + 2) → ℝ := fun j =>
          if hj : j.val ≤ m then seq ⟨j.val, by omega⟩ else x
        refine ⟨seq', by simp [seq', h0], ?_, ?_, ?_⟩
        · intro i
          by_cases him : i.val < m
          · have h1 : i.val ≤ m := by omega
            have h2 : i.val + 1 ≤ m := by omega
            simpa [seq', h1, h2] using hinc ⟨i.val, him⟩
          · have him_eq : i.val = m := by omega
            have h1 : i.val ≤ m := by omega
            have h2 : ¬ i.val + 1 ≤ m := by omega
            simp only [seq', h1, h2, ↓reduceDIte]
            convert hx_gt using 2
            exact Fin.ext him_eq
        · intro _
          simp only [seq', show ¬ (m + 1 ≤ m) by omega, ↓reduceDIte]
          exact hx_lt
        · intro j
          by_cases hjm : j.val ≤ m
          · simp only [seq', hjm, ↓reduceDIte]
            have hv := hval ⟨j.val, by omega⟩
            exact ⟨hv.1, fun h1 h2 => hv.2.1 h1 h2, fun h => by omega⟩
          · have hj_eq : j.val = m + 1 := by omega
            simp only [seq', hjm, ↓reduceDIte]
            exact ⟨fun h => by omega, fun _ _ => by rw [hj_eq]; exact hx_eq, fun h => by omega⟩
  rcases hchain N (le_refl N) with ⟨seq, _, hinc, _, hval⟩
  -- Step 3: At every `j : Fin (N + 1)`, `(-1)^(k + N - j) * (R (seq j) * sin (Θ (seq j)) + ε) > 0`!
  let g : ℝ → ℝ := fun r => R r * Real.sin (Θ r) + ε
  have hg_cont : Continuous g := (hR_cont.mul (Real.continuous_sin.comp hΘ_cont)).add continuous_const
  have hsign : ∀ j : Fin (N + 1), 0 < (-1 : ℝ) ^ (k + N - j.val) * g (seq j) := by
    intro j
    have hsin_lb : (1 : ℝ) / 2 ≤ (-1 : ℝ) ^ (k + N - j.val) * Real.sin (Θ (seq j)) := by
      have hv := hval j
      have hcos_near : ∀ (m : ℕ) (x : ℝ),
          x ∈ Set.Ioo ((m : ℝ) * Real.pi + Real.pi / 2 - Real.pi / 3)
            ((m : ℝ) * Real.pi + Real.pi / 2 + Real.pi / 3) →
          (1 : ℝ) / 2 ≤ (-1 : ℝ) ^ m * Real.sin x := by
        intro m x hx
        let δ := x - ((m : ℝ) * Real.pi + Real.pi / 2)
        have hδ_abs : |δ| ≤ Real.pi / 3 := by
          dsimp [δ]
          rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
        have hsin_x : Real.sin x = (-1 : ℝ) ^ m * Real.cos δ := by
          have hx_eq : x = (δ + (m : ℝ) * Real.pi) + Real.pi / 2 := by dsimp [δ]; ring
          rw [hx_eq, Real.sin_add_pi_div_two, Real.cos_add, Real.cos_nat_mul_pi,
            Real.sin_nat_mul_pi, mul_zero, sub_zero, mul_comm]
        have hcos_lb : (1 : ℝ) / 2 ≤ Real.cos δ := by
          rw [← Real.cos_pi_div_three, ← Real.cos_abs δ]
          exact Real.strictAntiOn_cos.antitoneOn
            ⟨abs_nonneg δ, by linarith⟩ ⟨by linarith, by linarith⟩ hδ_abs
        have hsq : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
          rw [← mul_pow]; norm_num
        calc (1 : ℝ) / 2 ≤ Real.cos δ := hcos_lb
          _ = (-1 : ℝ) ^ m * ((-1 : ℝ) ^ m * Real.cos δ) := by nlinarith [hsq]
          _ = (-1 : ℝ) ^ m * Real.sin x := by rw [hsin_x]
      by_cases hj0 : j.val = 0
      · have hmem := hv.1 hj0
        have heq : k + N - j.val = k + N := by omega
        rw [heq]
        exact hcos_near (k + N) (Θ (seq j)) hmem
      · by_cases hjN : j.val = N
        · have hmem := hv.2.2 hjN
          have heq : k + N - j.val = k := by omega
          rw [heq]
          exact hcos_near k (Θ (seq j)) hmem
        · have heq := hv.2.1 (by omega) (by omega)
          rw [heq, Real.sin_add_pi_div_two, Real.cos_nat_mul_pi, ← mul_pow]
          norm_num
    have hR := hR_lb (seq j)
    have hpm : |(-1 : ℝ) ^ (k + N - j.val)| = 1 := by simp
    have h1 : (-1 : ℝ) ^ (k + N - j.val) * g (seq j) =
        R (seq j) * ((-1 : ℝ) ^ (k + N - j.val) * Real.sin (Θ (seq j))) +
        (-1 : ℝ) ^ (k + N - j.val) * ε := by dsimp [g]; ring
    have h2 : -ε ≤ (-1 : ℝ) ^ (k + N - j.val) * ε := by
      have : -1 ≤ (-1 : ℝ) ^ (k + N - j.val) := by
        rcases Nat.even_or_odd (k + N - j.val) with ⟨t, ht⟩ | ⟨t, ht⟩
        · rw [ht, ← two_mul, pow_mul]; norm_num
        · rw [ht, pow_succ, pow_mul]; norm_num
      nlinarith
    rw [h1]
    nlinarith
  -- Step 4: On each interval `[seq i, seq (i + 1)]`, `g` changes sign, so IVT gives `root i ∈ (seq i, seq (i + 1))`!
  have hroot_ex : ∀ i : Fin N, ∃ r : ℝ,
      seq ⟨i.val, by omega⟩ < r ∧ r < seq ⟨i.val + 1, by omega⟩ ∧ g r = 0 := by
    intro i
    have hlt := hinc i
    have hs1 := hsign ⟨i.val, by omega⟩
    have hs2 := hsign ⟨i.val + 1, by omega⟩
    have hpow_succ : (-1 : ℝ) ^ (k + N - i.val) = -((-1 : ℝ) ^ (k + N - (i.val + 1))) := by
      have : k + N - i.val = (k + N - (i.val + 1)) + 1 := by omega
      rw [this, pow_succ]; ring
    rw [hpow_succ] at hs1
    -- Either `g(seq i) < 0 < g(seq(i+1))` or `g(seq(i+1)) < 0 < g(seq i)`!
    have hprod_neg : g (seq ⟨i.val, by omega⟩) * g (seq ⟨i.val + 1, by omega⟩) < 0 := by
      have hsq : ((-1 : ℝ) ^ (k + N - (i.val + 1))) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      nlinarith
    by_cases hneg : g (seq ⟨i.val, by omega⟩) < 0
    · have hpos : 0 < g (seq ⟨i.val + 1, by omega⟩) := by nlinarith
      obtain ⟨r, hr_Icc, hr0⟩ :=
        intermediate_value_Icc hlt.le hg_cont.continuousOn ⟨hneg.le, hpos.le⟩
      refine ⟨r, lt_of_le_of_ne hr_Icc.1 (fun h => by rw [← h] at hr0; linarith),
        lt_of_le_of_ne hr_Icc.2 (fun h => by rw [h] at hr0; linarith), hr0⟩
    · have hpos : 0 < g (seq ⟨i.val, by omega⟩) := by
        have hne : g (seq ⟨i.val, by omega⟩) ≠ 0 := by
          intro h0; rw [h0, zero_mul] at hprod_neg; exact lt_irrefl 0 hprod_neg
        exact lt_of_le_of_ne (not_lt.mp hneg) hne.symm
      have hneg2 : g (seq ⟨i.val + 1, by omega⟩) < 0 := by nlinarith
      obtain ⟨r, hr_Icc, hr0⟩ :=
        intermediate_value_Icc' hlt.le hg_cont.continuousOn ⟨hneg2.le, hpos.le⟩
      refine ⟨r, lt_of_le_of_ne hr_Icc.1 (fun h => by rw [← h] at hr0; linarith),
        lt_of_le_of_ne hr_Icc.2 (fun h => by rw [h] at hr0; linarith), hr0⟩
  choose root hroot_lo hroot_hi hroot_eq using hroot_ex
  have hseq_mono : StrictMono seq := by
    intro a b hab
    have hstep : ∀ d : ℕ, ∀ x : ℕ, (hx : x + d < N + 1) →
        seq ⟨x, by omega⟩ ≤ seq ⟨x + d, hx⟩ := by
      intro d
      induction d with
      | zero => intro x hx; exact le_rfl
      | succ d ihd =>
        intro x hx
        have h1 := ihd x (by omega)
        have h2 := hinc ⟨x + d, by omega⟩
        exact le_trans h1 h2.le
    have h1 := hinc ⟨a.val, by omega⟩
    have h2 := hstep (b.val - (a.val + 1)) (a.val + 1) (by omega)
    have hbe : (⟨a.val + 1 + (b.val - (a.val + 1)), by omega⟩ : Fin (N + 1)) = b :=
      Fin.ext (by dsimp; omega)
    rw [hbe] at h2
    exact lt_of_lt_of_le h1 h2
  have hroot_inj : Function.Injective root := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
    · have h1 := hroot_hi i
      have h2 := hroot_lo j
      have h3 : seq ⟨i.val + 1, by omega⟩ ≤ seq ⟨j.val, by omega⟩ :=
        hseq_mono.monotone (show (⟨i.val + 1, by omega⟩ : Fin (N + 1)) ≤ ⟨j.val, by omega⟩ from hlt)
      linarith
    · have h1 := hroot_hi j
      have h2 := hroot_lo i
      have h3 : seq ⟨j.val + 1, by omega⟩ ≤ seq ⟨i.val, by omega⟩ :=
        hseq_mono.monotone (show (⟨j.val + 1, by omega⟩ : Fin (N + 1)) ≤ ⟨i.val, by omega⟩ from hgt)
      linarith
  refine ⟨Finset.univ.image root, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hroot_inj, Finset.card_univ, Fintype.card_fin]
  · intro r hr
    rcases Finset.mem_image.mp hr with ⟨i, _, rfl⟩
    exact hroot_eq i

/-! ### Putting all 12 lines together: 108 distinct zeros > 106 -/

private noncomputable def lineRadLB (k : Fin 12) : ℝ :=
  |rotIm z1 (θ k)| ^ 10 * |rotIm zp (θ k)| * |rotIm zm (θ k)|

private lemma lineRadLB_pos (k : Fin 12) : 0 < lineRadLB k := by
  have ⟨h1, hp, hm⟩ := rotIm_all_ne_zero k
  unfold lineRadLB
  have hp1 : 0 < |rotIm z1 (θ k)| := abs_pos.mpr h1
  have hpp : 0 < |rotIm zp (θ k)| := abs_pos.mpr hp
  have hpm : 0 < |rotIm zm (θ k)| := abs_pos.mpr hm
  positivity

private noncomputable def eps0 : ℝ :=
  (1 / 4 : ℝ) * (Finset.univ.inf' Finset.univ_nonempty lineRadLB)

private lemma eps0_pos : 0 < eps0 := by
  unfold eps0
  have hinf : 0 < Finset.univ.inf' Finset.univ_nonempty lineRadLB :=
    (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun k _ => lineRadLB_pos k)
  linarith

private lemma lineRadLB_ge_4eps (k : Fin 12) : 4 * eps0 ≤ lineRadLB k := by
  unfold eps0
  have hle := Finset.inf'_le lineRadLB (Finset.mem_univ k)
  linarith

private def lineCount (k : Fin 12) : ℕ :=
  if k.val ≤ 2 ∨ 9 ≤ k.val then 10 else 8

private lemma sum_lineCount : ∑ k : Fin 12, lineCount k = 108 := by
  decide

private lemma line_roots_exists (k : Fin 12) :
    ∃ S : Finset ℝ, S.card = lineCount k ∧
      ∀ r ∈ S, r ≠ 0 ∧ (f0.eval ((r : ℂ) * w k)).im + eps0 = 0 := by
  have ⟨hb1, hbp, hbm⟩ := rotIm_all_ne_zero k
  let a1 := rotRe z1 (θ k); let b1 := rotIm z1 (θ k)
  let ap := rotRe zp (θ k); let bp := rotIm zp (θ k)
  let am := rotRe zm (θ k); let bm := rotIm zm (θ k)
  let s1 : ℝ := if 0 < b1 then 1 else -1
  let sp : ℝ := if 0 < bp then 1 else -1
  let sm : ℝ := if 0 < bm then 1 else -1
  let R : ℝ → ℝ := fun r =>
    Real.sqrt ((r - a1) ^ 2 + b1 ^ 2) ^ 10 *
    Real.sqrt ((r - ap) ^ 2 + bp ^ 2) *
    Real.sqrt ((r - am) ^ 2 + bm ^ 2)
  let Θ : ℝ → ℝ := fun r =>
    12 * θ k +
    10 * (s1 * (Real.arctan ((r - a1) / |b1|) - Real.pi / 2)) +
    sp * (Real.arctan ((r - ap) / |bp|) - Real.pi / 2) +
    sm * (Real.arctan ((r - am) / |bm|) - Real.pi / 2)
  have hf_im : ∀ r : ℝ, (f0.eval ((r : ℂ) * w k)).im = R r * Real.sin (Θ r) := by
    intro r
    rw [f0_eval_factor]
    have h1 := linear_polar z1 (θ k) r hb1
    have hp := linear_polar zp (θ k) r hbp
    have hm := linear_polar zm (θ k) r hbm
    change (((r : ℂ) * Complex.exp (Complex.I * (θ k : ℂ)) - z1) ^ 10 *
        ((r : ℂ) * Complex.exp (Complex.I * (θ k : ℂ)) - zp) *
        ((r : ℂ) * Complex.exp (Complex.I * (θ k : ℂ)) - zm)).im = _
    rw [h1, hp, hm]
    have hprod :
        (((Real.sqrt ((r - a1) ^ 2 + b1 ^ 2) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((θ k + s1 * (Real.arctan ((r - a1) / |b1|) - Real.pi / 2) : ℝ) : ℂ))) ^ 10 *
        (((Real.sqrt ((r - ap) ^ 2 + bp ^ 2) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((θ k + sp * (Real.arctan ((r - ap) / |bp|) - Real.pi / 2) : ℝ) : ℂ))) *
        (((Real.sqrt ((r - am) ^ 2 + bm ^ 2) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((θ k + sm * (Real.arctan ((r - am) / |bm|) - Real.pi / 2) : ℝ) : ℂ))) =
        ((R r : ℝ) : ℂ) * Complex.exp (Complex.I * ((Θ r : ℝ) : ℂ)) := by
      rw [mul_pow, ← Complex.exp_nat_mul]
      calc (((Real.sqrt ((r - a1) ^ 2 + b1 ^ 2) : ℝ) : ℂ) ^ 10 *
              Complex.exp (↑(10 : ℕ) * (Complex.I * ↑(θ k + s1 * (Real.arctan ((r - a1) / |b1|) - Real.pi / 2))))) *
            (((Real.sqrt ((r - ap) ^ 2 + bp ^ 2) : ℝ) : ℂ) *
              Complex.exp (Complex.I * ↑(θ k + sp * (Real.arctan ((r - ap) / |bp|) - Real.pi / 2)))) *
            (((Real.sqrt ((r - am) ^ 2 + bm ^ 2) : ℝ) : ℂ) *
              Complex.exp (Complex.I * ↑(θ k + sm * (Real.arctan ((r - am) / |bm|) - Real.pi / 2))))
          = (((Real.sqrt ((r - a1) ^ 2 + b1 ^ 2) : ℝ) : ℂ) ^ 10 *
              ((Real.sqrt ((r - ap) ^ 2 + bp ^ 2) : ℝ) : ℂ) *
              ((Real.sqrt ((r - am) ^ 2 + bm ^ 2) : ℝ) : ℂ)) *
            (Complex.exp (↑(10 : ℕ) * (Complex.I * ↑(θ k + s1 * (Real.arctan ((r - a1) / |b1|) - Real.pi / 2)))) *
              Complex.exp (Complex.I * ↑(θ k + sp * (Real.arctan ((r - ap) / |bp|) - Real.pi / 2))) *
              Complex.exp (Complex.I * ↑(θ k + sm * (Real.arctan ((r - am) / |bm|) - Real.pi / 2)))) := by ring
        _ = ((R r : ℝ) : ℂ) * Complex.exp (Complex.I * ((Θ r : ℝ) : ℂ)) := by
            rw [← Complex.exp_add, ← Complex.exp_add]
            congr 1
            · dsimp [R]; push_cast; rfl
            · congr 1; dsimp [Θ]; push_cast; ring
    rw [hprod, exp_I_mul]
    simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.add_re]
    ring
  -- Continuity of `R` and `Θ`:
  have hR_cont : Continuous R := by
    dsimp [R]
    fun_prop
  have hΘ_cont : Continuous Θ := by
    dsimp [Θ]
    fun_prop
  -- Lower bound `4 * eps0 ≤ R r`:
  have hR_lb : ∀ r : ℝ, 4 * eps0 ≤ R r := by
    intro r
    refine le_trans (lineRadLB_ge_4eps k) ?_
    have hge1 : |b1| ≤ Real.sqrt ((r - a1) ^ 2 + b1 ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hgep : |bp| ≤ Real.sqrt ((r - ap) ^ 2 + bp ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hgem : |bm| ≤ Real.sqrt ((r - am) ^ 2 + bm ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hpow1 : |b1| ^ 10 ≤ Real.sqrt ((r - a1) ^ 2 + b1 ^ 2) ^ 10 :=
      pow_le_pow_left₀ (abs_nonneg _) hge1 10
    have hm1 : |b1| ^ 10 * |bp| ≤
        Real.sqrt ((r - a1) ^ 2 + b1 ^ 2) ^ 10 * Real.sqrt ((r - ap) ^ 2 + bp ^ 2) :=
      mul_le_mul hpow1 hgep (abs_nonneg _) (by positivity)
    exact mul_le_mul hm1 hgem (abs_nonneg _) (by positivity)
  -- Compute `-(10*s1 + sp + sm) = lineCount k`!
  have hs1_val : s1 = -1 := by
    dsimp [s1, b1]; rw [if_neg (not_lt.mpr (rotIm_z1_neg k).le)]
  have hnet_eq : -(10 * s1 + sp + sm) = (lineCount k : ℝ) := by
    unfold lineCount
    by_cases hk : k.val ≤ 2 ∨ 9 ≤ k.val
    · rw [if_pos hk]
      rcases rotIm_zp_zm_outer k hk with ⟨hp, hm⟩ | ⟨hp, hm⟩
      · have hsp : sp = 1 := by dsimp [sp, bp]; rw [if_pos hp]
        have hsm : sm = -1 := by dsimp [sm, bm]; rw [if_neg (not_lt.mpr hm.le)]
        rw [hs1_val, hsp, hsm]; norm_num
      · have hsp : sp = -1 := by dsimp [sp, bp]; rw [if_neg (not_lt.mpr hp.le)]
        have hsm : sm = 1 := by dsimp [sm, bm]; rw [if_pos hm]
        rw [hs1_val, hsp, hsm]; norm_num
    · rw [if_neg hk]
      have hkin : 3 ≤ k.val ∧ k.val ≤ 8 := by omega
      rcases rotIm_zp_zm_inner k hkin with ⟨hp, hm⟩
      have hsp : sp = 1 := by dsimp [sp, bp]; rw [if_pos hp]
      have hsm : sm = 1 := by dsimp [sm, bm]; rw [if_pos hm]
      rw [hs1_val, hsp, hsm]; norm_num
  -- Limits of `Θ` at `+∞` and `-∞`:
  have h12θ : 12 * θ k = (k.val : ℝ) * Real.pi + Real.pi / 2 := by
    unfold θ; push_cast; ring
  have harctan_top : ∀ (a b : ℝ), b ≠ 0 →
      Filter.Tendsto (fun r : ℝ => Real.arctan ((r - a) / |b|) - Real.pi / 2)
        Filter.atTop (nhds 0) := by
    intro a b hb
    have hdiv : Filter.Tendsto (fun r : ℝ => (r - a) / |b|) Filter.atTop Filter.atTop := by
      have hsub : Filter.Tendsto (fun r : ℝ => r - a) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_right _ (-a) Filter.tendsto_id
      exact hsub.atTop_div_const (abs_pos.mpr hb)
    have h1 := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hdiv
    simpa using h1.sub_const (Real.pi / 2)
  have harctan_bot : ∀ (a b : ℝ), b ≠ 0 →
      Filter.Tendsto (fun r : ℝ => Real.arctan ((r - a) / |b|) - Real.pi / 2)
        Filter.atBot (nhds (-Real.pi)) := by
    intro a b hb
    have hdiv : Filter.Tendsto (fun r : ℝ => (r - a) / |b|) Filter.atBot Filter.atBot := by
      have hsub : Filter.Tendsto (fun r : ℝ => r - a) Filter.atBot Filter.atBot :=
        Filter.tendsto_atBot_add_const_right _ (-a) Filter.tendsto_id
      exact hsub.atBot_div_const (abs_pos.mpr hb)
    have h1 := (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp hdiv
    have h2 := h1.sub_const (Real.pi / 2)
    have hlim : -(Real.pi / 2) - Real.pi / 2 = -Real.pi := by ring
    rwa [hlim] at h2
  have hTop : Filter.Tendsto Θ Filter.atTop (nhds ((k.val : ℝ) * Real.pi + Real.pi / 2)) := by
    have h1 := ((harctan_top a1 b1 hb1).const_mul s1).const_mul 10
    have h2 := (harctan_top ap bp hbp).const_mul sp
    have h3 := (harctan_top am bm hbm).const_mul sm
    have hall := ((tendsto_const_nhds (x := 12 * θ k)).add h1).add h2 |>.add h3
    have hlim : 12 * θ k + 10 * (s1 * 0) + sp * 0 + sm * 0 = (k.val : ℝ) * Real.pi + Real.pi / 2 := by
      rw [h12θ]; ring
    rw [hlim] at hall
    exact hall
  have hBot : Filter.Tendsto Θ Filter.atBot
      (nhds (((k.val + lineCount k : ℕ) : ℝ) * Real.pi + Real.pi / 2)) := by
    have h1 := ((harctan_bot a1 b1 hb1).const_mul s1).const_mul 10
    have h2 := (harctan_bot ap bp hbp).const_mul sp
    have h3 := (harctan_bot am bm hbm).const_mul sm
    have hall := ((tendsto_const_nhds (x := 12 * θ k)).add h1).add h2 |>.add h3
    have hlim : 12 * θ k + 10 * (s1 * -Real.pi) + sp * -Real.pi + sm * -Real.pi =
        ((k.val + lineCount k : ℕ) : ℝ) * Real.pi + Real.pi / 2 := by
      rw [h12θ]
      push_cast
      linear_combination Real.pi * hnet_eq
    rw [hlim] at hall
    exact hall
  have hN_pos : 1 ≤ lineCount k := by unfold lineCount; split_ifs <;> omega
  obtain ⟨S, hScard, hSroots⟩ :=
    exists_roots_of_angle_limits eps0_pos hN_pos hΘ_cont hR_cont hR_lb hTop hBot
  refine ⟨S, hScard, ?_⟩
  intro r hr
  have hzero : (f0.eval ((r : ℂ) * w k)).im + eps0 = 0 := by
    rw [hf_im r]; exact hSroots r hr
  have hr_ne : r ≠ 0 := by
    intro hr0
    rw [hr0, Complex.ofReal_zero, zero_mul] at hzero
    have hf0_0 : f0.eval 0 = 55 := by unfold f0; simp; norm_num
    rw [hf0_0] at hzero
    have him55 : (55 : ℂ).im = 0 := by simp
    rw [him55, zero_add] at hzero
    linarith [eps0_pos]
  exact ⟨hr_ne, hzero⟩

private lemma counterexample : ¬ (type_of% @OMA.S_arxiv_2201_00788.main) := by
  intro hmain
  have hspec := hmain 12 9 (by omega) (by omega) (p12 eps0) (q9 eps0)
    (p12_natDegree eps0) (q9_natDegree eps0) (zeroSet_finite eps0)
  choose Sk hSk_card hSk_prop using line_roots_exists
  let Zk : Fin 12 → Finset ℂ := fun k => (Sk k).image (fun r : ℝ => (r : ℂ) * w k)
  let Z : Finset ℂ := Finset.univ.biUnion Zk
  have hZ_zeros : ∀ z ∈ Z, (p12 eps0).eval z + starRingEnd ℂ ((q9 eps0).eval z) = 0 := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨k, _, hzk⟩
    rcases Finset.mem_image.mp hzk with ⟨r, hr, rfl⟩
    rw [eval_harm_eq_zero_iff]
    exact ⟨re_pow_12_on_line k r, (hSk_prop k r hr).2⟩
  have hZk_card : ∀ k : Fin 12, (Zk k).card = lineCount k := by
    intro k
    rw [Finset.card_image_of_injective]
    · exact hSk_card k
    · intro r₁ r₂ h
      exact Complex.ofReal_injective (mul_right_cancel₀ (Complex.exp_ne_zero _) h)
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 12)) Zk := by
    intro k₁ _ k₂ _ hne
    change Disjoint (Zk k₁) (Zk k₂)
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    rcases Finset.mem_image.mp hz1 with ⟨r₁, hr₁, rfl⟩
    rcases Finset.mem_image.mp hz2 with ⟨r₂, hr₂, heq⟩
    have h1 := (w_lines_disjoint (hSk_prop k₁ r₁ hr₁).1 heq.symm).1
    exact hne h1
  have hZ_card : Z.card = 108 := by
    rw [Finset.card_biUnion hdisj]
    have hsum : ∑ k : Fin 12, (Zk k).card = ∑ k : Fin 12, lineCount k :=
      Finset.sum_congr rfl (fun k _ => hZk_card k)
    rw [hsum, sum_lineCount]
  have hle := hspec Z hZ_zeros
  omega

end OMA.P_arxiv_2201_00788

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2201_00788.main) :=
  OMA.P_arxiv_2201_00788.counterexample

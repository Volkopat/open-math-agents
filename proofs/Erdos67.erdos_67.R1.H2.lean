import OMAReductions.R_Erdos67_erdos_67_R1

/-! Proof of `OMA.R_Erdos67_erdos_67_R1.H2` (Tao 2016, Section 4). -/

namespace E67H2
open Finset (Icc Ico Ioc mem_Icc mem_Ico mem_Ioc mem_range mem_filter sum_le_sum sum_congr sum_nonneg sum_add_distrib sum_sub_distrib sum_const mul_sum sum_mul sum_filter sum_union card_le_card sum_eq_zero sum_comm sum_insert mem_insert mem_union sum_map sum_div prod_congr prod_le_prod disjoint_left sum_le_sum_of_subset_of_nonneg sum_mul_sq_le_sq_mul_sq single_le_sum Icc_eq_empty sum_empty sum_image sum_nbij sum_attach mem_attach card_le_univ mem_univ add_sum_erase ne_of_mem_erase filter_subset sum_eq_single prod_eq_one sum_filter_add_sum_filter_not card_le_one image_subset_iff)

section
open Filter Finset Complex Real MeasureTheory
open scoped BigOperators Topology
noncomputable def eUnit (u : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (u : ℂ))
lemma norm_eUnit (u : ℝ) : ‖eUnit u‖ = 1 := by
  unfold eUnit
  rw [Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (u : ℂ)).re = 0 := by simp
  rw [hre, Real.exp_zero]
lemma eUnit_add (u v : ℝ) : eUnit (u + v) = eUnit u * eUnit v := by
  unfold eUnit
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
lemma eUnit_sub (u v : ℝ) : eUnit (u - v) = eUnit u * star (eUnit v) := by
  unfold eUnit
  have hstar : star (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (v : ℂ))) =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (v : ℂ))) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal, map_ofNat, mul_comm, mul_left_comm]
  rw [hstar, ← Complex.exp_add]
  congr 1
  push_cast
  ring
lemma eUnit_int_mul (m : ℤ) : eUnit (m : ℝ) = 1 := by
  unfold eUnit
  have h : 2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I m
lemma eUnit_neg (u : ℝ) : eUnit (-u) = star (eUnit u) := by
  have h := eUnit_sub 0 u
  simp only [zero_sub] at h
  have h0 : eUnit 0 = 1 := by unfold eUnit; simp
  rw [h0, one_mul] at h
  exact h
lemma sin_pi_ge_two_mul {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    2 * u ≤ Real.sin (Real.pi * u) := by
  have hpi : 0 ≤ Real.pi * u := by positivity
  have hpi2 : Real.pi * u ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hsin := Real.mul_le_sin hpi hpi2
  have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
  have heq : 2 / Real.pi * (Real.pi * u) = 2 * u := by field_simp [hpi_ne]
  linarith
lemma sin_pi_ge_two_min {u θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2)
    (hu1 : θ ≤ u) (hu2 : u ≤ 1 - θ) :
    2 * θ ≤ Real.sin (Real.pi * u) := by
  by_cases hhalf : u ≤ 1 / 2
  · have h1 : Real.sin (Real.pi * θ) ≤ Real.sin (Real.pi * u) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    exact (sin_pi_ge_two_mul hθ0.le hθ1).trans h1
  · push Not at hhalf
    have h1u : 1 - u ≤ 1 / 2 := by linarith
    have h1u_ge : θ ≤ 1 - u := by linarith
    have hsym : Real.sin (Real.pi * u) = Real.sin (Real.pi * (1 - u)) := by
      have : Real.pi * u = Real.pi - Real.pi * (1 - u) := by ring
      rw [this, Real.sin_pi_sub]
    rw [hsym]
    have h1 : Real.sin (Real.pi * θ) ≤ Real.sin (Real.pi * (1 - u)) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    exact (sin_pi_ge_two_mul hθ0.le hθ1).trans h1
lemma eUnit_sub_one_ne_zero {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) : eUnit u - 1 ≠ 0 := by
  intro h
  have h1 : eUnit u = 1 := sub_eq_zero.mp h
  have hexp : 2 * (Real.pi : ℂ) * Complex.I * (u : ℂ) = ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  unfold eUnit at h1
  rw [hexp, Complex.exp_mul_I] at h1
  have hre : Real.cos (2 * Real.pi * u) = 1 := by
    have h1' : Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I) = 1 := by
      simpa [Complex.exp_mul_I] using h1
    have hre1 := congrArg Complex.re h1'
    rw [Complex.exp_ofReal_mul_I_re, Complex.one_re] at hre1
    exact hre1
  have hsin_half : Real.sin (Real.pi * u) = 0 := by
    have hcos := Real.cos_two_mul (Real.pi * u)
    have h2 : 2 * Real.pi * u = 2 * (Real.pi * u) := by ring
    rw [h2, hcos] at hre
    have hsq := Real.sin_sq_add_cos_sq (Real.pi * u)
    nlinarith
  have hpos : 0 < Real.sin (Real.pi * u) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  linarith
lemma inv_eUnit_sub_one_eq {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (eUnit u - 1)⁻¹ = -(1 / 2 : ℂ) - Complex.I * ((Real.cos (Real.pi * u) / (2 * Real.sin (Real.pi * u)) : ℝ) : ℂ) := by
  have hsin_pos : 0 < Real.sin (Real.pi * u) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  refine inv_eq_of_mul_eq_one_right ?_
  have heu : eUnit u = (Real.cos (2 * Real.pi * u) : ℂ) + (Real.sin (2 * Real.pi * u) : ℂ) * Complex.I := by
    unfold eUnit
    have h : 2 * (Real.pi : ℂ) * Complex.I * (u : ℂ) = ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h, Complex.exp_mul_I]
    simp
  rw [heu]
  have h2u : 2 * Real.pi * u = 2 * (Real.pi * u) := by ring
  rw [h2u, Real.cos_two_mul, Real.sin_two_mul]
  set c : ℝ := Real.cos (Real.pi * u)
  set s : ℝ := Real.sin (Real.pi * u)
  have hsq : c ^ 2 + s ^ 2 = 1 := by linarith [Real.sin_sq_add_cos_sq (Real.pi * u)]
  have hsqC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hsq
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast hsin_pos.ne'
  have h1 : (((2 * c ^ 2 - 1 : ℝ) : ℂ) + ((2 * s * c : ℝ) : ℂ) * Complex.I - 1) =
      2 * (s : ℂ) * (-(s : ℂ) + (c : ℂ) * Complex.I) := by
    push_cast; linear_combination 2 * hsqC
  have h2 : (-(1 / 2 : ℂ) - Complex.I * ((c / (2 * s) : ℝ) : ℂ)) =
      (-(s : ℂ) - (c : ℂ) * Complex.I) / (2 * (s : ℂ)) := by
    push_cast; field_simp [hsne]
  have hcancel : 2 * (s : ℂ) * (-(s : ℂ) + (c : ℂ) * Complex.I) *
      ((-(s : ℂ) - (c : ℂ) * Complex.I) / (2 * (s : ℂ))) =
      (-(s : ℂ) + (c : ℂ) * Complex.I) * (-(s : ℂ) - (c : ℂ) * Complex.I) := by
    field_simp [hsne]
  rw [h1, h2, hcancel]
  linear_combination -(c : ℂ) ^ 2 * Complex.I_sq + hsqC
lemma norm_inv_eUnit_sub_one_le {u θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2)
    (hu1 : θ ≤ u) (hu2 : u ≤ 1 - θ) :
    ‖(eUnit u - 1)⁻¹‖ ≤ 1 / (4 * θ) := by
  have hu0 : 0 < u := lt_of_lt_of_le hθ0 hu1
  have hu1' : u < 1 := lt_of_le_of_lt hu2 (by linarith)
  have hsin_ge : 2 * θ ≤ Real.sin (Real.pi * u) := sin_pi_ge_two_min hθ0 hθ1 hu1 hu2
  have hsin_pos : 0 < Real.sin (Real.pi * u) := lt_of_lt_of_le (by linarith) hsin_ge
  rw [inv_eUnit_sub_one_eq hu0 hu1']
  have hnorm_sq :
      ‖-(1 / 2 : ℂ) - Complex.I * ((Real.cos (Real.pi * u) / (2 * Real.sin (Real.pi * u)) : ℝ) : ℂ)‖ ^ 2 =
      (1 / (2 * Real.sin (Real.pi * u))) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.neg_re, Complex.div_ofNat_re, Complex.one_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, sub_self, Complex.sub_im, Complex.neg_im,
      Complex.div_ofNat_im, Complex.one_im, Complex.mul_im, one_mul, zero_add]
    have hsq := Real.sin_sq_add_cos_sq (Real.pi * u)
    field_simp [hsin_pos.ne']
    nlinarith [hsq]
  have hnorm :
      ‖-(1 / 2 : ℂ) - Complex.I * ((Real.cos (Real.pi * u) / (2 * Real.sin (Real.pi * u)) : ℝ) : ℂ)‖ =
      1 / (2 * Real.sin (Real.pi * u)) := by
    have hnn1 : 0 ≤ ‖-(1 / 2 : ℂ) - Complex.I * ((Real.cos (Real.pi * u) / (2 * Real.sin (Real.pi * u)) : ℝ) : ℂ)‖ :=
      norm_nonneg _
    have hnn2 : 0 ≤ 1 / (2 * Real.sin (Real.pi * u)) := by positivity
    nlinarith [hnorm_sq]
  rw [hnorm]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)
lemma cot_anti_on_Ioo {u v : ℝ} (hu0 : 0 < u) (huv : u ≤ v) (hv1 : v < 1) :
    Real.cos (Real.pi * v) / Real.sin (Real.pi * v) ≤
      Real.cos (Real.pi * u) / Real.sin (Real.pi * u) := by
  have hsu : 0 < Real.sin (Real.pi * u) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have hsv : 0 < Real.sin (Real.pi * v) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  rw [div_le_div_iff₀ hsv hsu]
  have hsub : Real.sin (Real.pi * v - Real.pi * u) =
      Real.sin (Real.pi * v) * Real.cos (Real.pi * u) -
      Real.cos (Real.pi * v) * Real.sin (Real.pi * u) := Real.sin_sub _ _
  have hnn : 0 ≤ Real.sin (Real.pi * v - Real.pi * u) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  linarith
lemma kusmin_landau_seq {N : ℕ} {f : ℕ → ℝ} {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2)
    (hmono : ∀ n, 1 ≤ n → n + 2 ≤ N → f (n + 1) - f n ≤ f (n + 2) - f (n + 1))
    (hbd : ∀ n, 1 ≤ n → n + 1 ≤ N → θ ≤ f (n + 1) - f n ∧ f (n + 1) - f n ≤ 1 - θ) :
    ‖∑ n ∈ Icc 1 N, eUnit (f n)‖ ≤ 2 / θ := by
  by_cases hN : N ≤ 1
  · have hle : ‖∑ n ∈ Icc 1 N, eUnit (f n)‖ ≤ 1 := by
      calc ‖∑ n ∈ Icc 1 N, eUnit (f n)‖
          ≤ ∑ n ∈ Icc 1 N, ‖eUnit (f n)‖ := norm_sum_le _ _
        _ = (Icc 1 N).card := by simp [norm_eUnit]
        _ ≤ 1 := by
            have : (Icc 1 N).card ≤ 1 := by simp; omega
            exact_mod_cast this
    have h2 : (1 : ℝ) ≤ 2 / θ := by
      rw [le_div_iff₀ hθ0]; linarith
    linarith
  push Not at hN
  let u : ℕ → ℝ := fun n => f (n + 1) - f n
  let c : ℕ → ℂ := fun n => (eUnit (u n) - 1)⁻¹
  have hterm : ∀ n ∈ Icc 1 (N - 1),
      eUnit (f n) = c n * (eUnit (f (n + 1)) - eUnit (f n)) := by
    intro n hn
    rw [mem_Icc] at hn
    have hbu := hbd n hn.1 (by omega)
    have hne := eUnit_sub_one_ne_zero (lt_of_lt_of_le hθ0 hbu.1) (lt_of_le_of_lt hbu.2 (by linarith))
    have hdiff : eUnit (f (n + 1)) - eUnit (f n) = eUnit (f n) * (eUnit (u n) - 1) := by
      have hf : f (n + 1) = f n + u n := by dsimp [u]; ring
      rw [hf, eUnit_add]; ring
    rw [hdiff]
    dsimp [c]
    rw [mul_comm (eUnit (u n) - 1)⁻¹, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  have hsum_split : ∑ n ∈ Icc 1 N, eUnit (f n) =
      (∑ n ∈ Icc 1 (N - 1), eUnit (f n)) + eUnit (f N) := by
    have hN1 : 1 ≤ N := by omega
    have hIcc : Icc 1 N = insert N (Icc 1 (N - 1)) := by
      ext k; simp only [mem_Icc, mem_insert]; omega
    rw [hIcc, sum_insert (by simp; omega), add_comm]
  have habel : ∑ n ∈ Icc 1 (N - 1), c n * (eUnit (f (n + 1)) - eUnit (f n)) =
      c (N - 1) * eUnit (f N) - c 1 * eUnit (f 1) +
        ∑ n ∈ Icc 1 (N - 2), (c n - c (n + 1)) * eUnit (f (n + 1)) := by
    have hN2 : 2 ≤ N := hN
    clear hterm hsum_split hmono hbd hN
    induction N, hN2 using Nat.le_induction with
    | base =>
      simp; ring
    | succ m hm ih =>
      have h1 : Icc 1 m = insert m (Icc 1 (m - 1)) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      have h2 : Icc 1 (m - 1) = insert (m - 1) (Icc 1 (m - 2)) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      simp only [Nat.add_sub_cancel]
      rw [h1, sum_insert (by simp; omega), ih]
      have hsub : m + 1 - 2 = m - 1 := by omega
      rw [hsub, h2, sum_insert (by simp; omega)]
      have hm1 : m - 1 + 1 = m := by omega
      rw [hm1]
      ring
  have hsum_eq : ∑ n ∈ Icc 1 (N - 1), eUnit (f n) =
      c (N - 1) * eUnit (f N) - c 1 * eUnit (f 1) +
        ∑ n ∈ Icc 1 (N - 2), (c n - c (n + 1)) * eUnit (f (n + 1)) := by
    rw [sum_congr rfl hterm, habel]
  let cotF : ℕ → ℝ := fun n => Real.cos (Real.pi * u n) / (2 * Real.sin (Real.pi * u n))
  have hdiff_norm : ∀ n ∈ Icc 1 (N - 2),
      ‖(c n - c (n + 1)) * eUnit (f (n + 1))‖ = cotF n - cotF (n + 1) := by
    intro n hn
    rw [mem_Icc] at hn
    have h1 := hbd n hn.1 (by omega)
    have h2 := hbd (n + 1) (by omega) (by omega)
    have hm := hmono n hn.1 (by omega)
    have hc1 := inv_eUnit_sub_one_eq (lt_of_lt_of_le hθ0 h1.1) (lt_of_le_of_lt h1.2 (by linarith))
    have hc2 := inv_eUnit_sub_one_eq (lt_of_lt_of_le hθ0 h2.1) (lt_of_le_of_lt h2.2 (by linarith))
    rw [norm_mul, norm_eUnit, mul_one]
    dsimp [c]
    rw [hc1, hc2]
    have hsubc :
        (-(1 / 2 : ℂ) - Complex.I * (cotF n : ℂ)) -
        (-(1 / 2 : ℂ) - Complex.I * (cotF (n + 1) : ℂ)) =
        Complex.I * (((cotF (n + 1) - cotF n : ℝ) : ℂ)) := by
      push_cast; ring
    dsimp [cotF] at hsubc ⊢
    rw [hsubc, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hcot : cotF (n + 1) ≤ cotF n := by
      dsimp [cotF]
      have hle := cot_anti_on_Ioo (lt_of_lt_of_le hθ0 h1.1) hm (lt_of_le_of_lt h2.2 (by linarith))
      have he1 : Real.cos (Real.pi * u (n + 1)) / (2 * Real.sin (Real.pi * u (n + 1))) =
          (Real.cos (Real.pi * u (n + 1)) / Real.sin (Real.pi * u (n + 1))) / 2 := by ring
      have he2 : Real.cos (Real.pi * u n) / (2 * Real.sin (Real.pi * u n)) =
          (Real.cos (Real.pi * u n) / Real.sin (Real.pi * u n)) / 2 := by ring
      rw [he1, he2]; linarith
    rw [abs_of_nonpos (by linarith)]
    ring
  have htele : ∑ n ∈ Icc 1 (N - 2), (cotF n - cotF (n + 1)) = cotF 1 - cotF (N - 1) := by
    by_cases hN2 : N = 2
    · subst hN2; simp
    · have hN3 : 3 ≤ N := by omega
      clear hterm hsum_split habel hsum_eq hdiff_norm hmono hbd hN hN2
      induction N, hN3 using Nat.le_induction with
      | base => simp
      | succ m hm ih =>
        have h1 : Icc 1 (m + 1 - 2) = insert (m - 1) (Icc 1 (m - 2)) := by
          ext k; simp only [mem_Icc, mem_insert]; omega
        rw [h1, sum_insert (by simp; omega), ih]
        have hm1 : m - 1 + 1 = m := by omega
        have hm2 : m + 1 - 1 = m := by omega
        rw [hm1, hm2]
        ring
  have hcot_bd : ∀ n, 1 ≤ n → n + 1 ≤ N → |cotF n| ≤ 1 / (4 * θ) := by
    intro n hn1 hn2
    have hbu := hbd n hn1 hn2
    have hsin_ge := sin_pi_ge_two_min hθ0 hθ1 hbu.1 hbu.2
    have hsin_pos : 0 < Real.sin (Real.pi * u n) := lt_of_lt_of_le (by linarith) hsin_ge
    dsimp [cotF]
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sin (Real.pi * u n))]
    calc |Real.cos (Real.pi * u n)| / (2 * Real.sin (Real.pi * u n))
        ≤ 1 / (2 * Real.sin (Real.pi * u n)) :=
          div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)
      _ ≤ 1 / (4 * θ) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have hc_bd : ∀ n, 1 ≤ n → n + 1 ≤ N → ‖c n‖ ≤ 1 / (4 * θ) := by
    intro n hn1 hn2
    have hbu := hbd n hn1 hn2
    exact norm_inv_eUnit_sub_one_le hθ0 hθ1 hbu.1 hbu.2
  have htri : ‖∑ n ∈ Icc 1 N, eUnit (f n)‖ ≤
      ‖c (N - 1)‖ + ‖c 1‖ + (cotF 1 - cotF (N - 1)) + 1 := by
    rw [hsum_split, hsum_eq]
    calc ‖c (N - 1) * eUnit (f N) - c 1 * eUnit (f 1) +
            (∑ n ∈ Icc 1 (N - 2), (c n - c (n + 1)) * eUnit (f (n + 1))) + eUnit (f N)‖
        ≤ ‖c (N - 1) * eUnit (f N) - c 1 * eUnit (f 1) +
            ∑ n ∈ Icc 1 (N - 2), (c n - c (n + 1)) * eUnit (f (n + 1))‖ + ‖eUnit (f N)‖ :=
          norm_add_le _ _
      _ ≤ (‖c (N - 1) * eUnit (f N) - c 1 * eUnit (f 1)‖ +
            ‖∑ n ∈ Icc 1 (N - 2), (c n - c (n + 1)) * eUnit (f (n + 1))‖) + 1 := by
          rw [norm_eUnit]; gcongr; exact norm_add_le _ _
      _ ≤ (‖c (N - 1) * eUnit (f N)‖ + ‖c 1 * eUnit (f 1)‖) +
            (∑ n ∈ Icc 1 (N - 2), ‖(c n - c (n + 1)) * eUnit (f (n + 1))‖) + 1 := by
          gcongr
          · exact norm_sub_le _ _
          · exact norm_sum_le _ _
      _ = ‖c (N - 1)‖ + ‖c 1‖ + (cotF 1 - cotF (N - 1)) + 1 := by
          rw [norm_mul, norm_eUnit, mul_one, norm_mul, norm_eUnit, mul_one,
            sum_congr rfl hdiff_norm, htele]
  have h1 := hc_bd (N - 1) (by omega) (by omega)
  have h2 := hc_bd 1 (by omega) (by omega)
  have h3 := abs_le.mp (hcot_bd 1 (by omega) (by omega))
  have h4 := abs_le.mp (hcot_bd (N - 1) (by omega) (by omega))
  have hone : (1 : ℝ) ≤ 1 / (2 * θ) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hsum4 : 1 / (4 * θ) + 1 / (4 * θ) + (1 / (4 * θ) + 1 / (4 * θ)) + 1 / (2 * θ) ≤ 2 / θ := by
    have hθne : θ ≠ 0 := hθ0.ne'
    have heq : 1 / (4 * θ) + 1 / (4 * θ) + (1 / (4 * θ) + 1 / (4 * θ)) + 1 / (2 * θ) = 3 / (2 * θ) := by
      field_simp [hθne]; ring
    rw [heq]
    have : 3 / (2 * θ) ≤ 4 / (2 * θ) := div_le_div_of_nonneg_right (by norm_num) (by positivity)
    have heq2 : 4 / (2 * θ) = 2 / θ := by field_simp [hθne]; ring
    linarith
  linarith
lemma iteratedDeriv_two_eq {f : ℝ → ℝ} (x : ℝ) :
    iteratedDeriv 2 f x = deriv (deriv f) x := by
  simp [iteratedDeriv_succ]
lemma contDiffAt_iteratedDeriv {k m : ℕ} {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ ((m + k : ℕ) : WithTop ℕ∞) f x) :
    ContDiffAt ℝ (m : WithTop ℕ∞) (iteratedDeriv k f) x := by
  induction k generalizing m with
  | zero => simpa using hf
  | succ k ih =>
    have h1 : ContDiffAt ℝ (((m + 1 : ℕ) : WithTop ℕ∞)) (iteratedDeriv k f) x :=
      ih (hf.of_le (by norm_cast; omega))
    have h2 : iteratedDeriv (k + 1) f = deriv (iteratedDeriv k f) := iteratedDeriv_succ
    rw [h2]
    exact h1.derivWithin (by norm_cast)
lemma deriv_strictMono_of_deriv2_pos {f : ℝ → ℝ} {a b lam : ℝ} (hlam : 0 < lam)
    (hf : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 2 f x)
    (h2 : ∀ x ∈ Set.Icc a b, lam ≤ iteratedDeriv 2 f x) :
    ∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
      lam * (y - x) ≤ deriv f y - deriv f x := by
  intro x y hx hy hxy
  by_cases heq : x = y
  · subst heq; simp
  have hlt : x < y := lt_of_le_of_ne hxy heq
  have hsub : Set.Icc x y ⊆ Set.Icc a b := Set.Icc_subset_Icc hx.1 hy.2
  have hdiff_d : ∀ z ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) z := by
    intro z hz
    have h1 : ContDiffAt ℝ 1 (deriv f) z := (hf z hz).derivWithin (by norm_num)
    exact h1.differentiableAt (by norm_num)
  have hcont1 : ContinuousOn (deriv f) (Set.Icc x y) :=
    fun z hz => (hdiff_d z (hsub hz)).continuousAt.continuousWithinAt
  have hd1 : DifferentiableOn ℝ (deriv f) (Set.Ioo x y) :=
    fun z hz => (hdiff_d z (hsub (Set.Ioo_subset_Icc_self hz))).differentiableWithinAt
  obtain ⟨c, hc, hderiv_c⟩ := exists_deriv_eq_slope (deriv f) hlt hcont1 hd1
  have hc_mem : c ∈ Set.Icc a b := hsub (Set.Ioo_subset_Icc_self hc)
  have hge := h2 c hc_mem
  rw [iteratedDeriv_two_eq] at hge
  rw [hderiv_c, le_div_iff₀ (sub_pos.mpr hlt)] at hge
  exact hge
lemma deriv_sub_le_of_deriv2_le {f : ℝ → ℝ} {a b U : ℝ}
    (hf : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 2 f x)
    (h2 : ∀ x ∈ Set.Icc a b, iteratedDeriv 2 f x ≤ U) :
    ∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
      deriv f y - deriv f x ≤ U * (y - x) := by
  intro x y hx hy hxy
  by_cases heq : x = y
  · subst heq; simp
  have hlt : x < y := lt_of_le_of_ne hxy heq
  have hsub : Set.Icc x y ⊆ Set.Icc a b := Set.Icc_subset_Icc hx.1 hy.2
  have hdiff_d : ∀ z ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) z := by
    intro z hz
    have h1 : ContDiffAt ℝ 1 (deriv f) z := (hf z hz).derivWithin (by norm_num)
    exact h1.differentiableAt (by norm_num)
  have hcont1 : ContinuousOn (deriv f) (Set.Icc x y) :=
    fun z hz => (hdiff_d z (hsub hz)).continuousAt.continuousWithinAt
  have hd1 : DifferentiableOn ℝ (deriv f) (Set.Ioo x y) :=
    fun z hz => (hdiff_d z (hsub (Set.Ioo_subset_Icc_self hz))).differentiableWithinAt
  obtain ⟨c, hc, hderiv_c⟩ := exists_deriv_eq_slope (deriv f) hlt hcont1 hd1
  have hc_mem : c ∈ Set.Icc a b := hsub (Set.Ioo_subset_Icc_self hc)
  have hle := h2 c hc_mem
  rw [iteratedDeriv_two_eq] at hle
  rw [hderiv_c, div_le_iff₀ (sub_pos.mpr hlt)] at hle
  exact hle
lemma vdc_second_deriv {N : ℕ} (hN : 1 ≤ N) {a lam α : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hα : 1 ≤ α)
    {f : ℝ → ℝ} (hf : ∀ x ∈ Set.Icc a (a + (N : ℝ) + 1), ContDiffAt ℝ 2 f x)
    (h2 : ∀ x ∈ Set.Icc a (a + (N : ℝ) + 1), lam ≤ iteratedDeriv 2 f x ∧ iteratedDeriv 2 f x ≤ α * lam) :
    ‖∑ n ∈ Icc 1 N, eUnit (f (a + (n : ℝ)))‖ ≤
      45 * α * ((N : ℝ) * lam ^ (1 / 2 : ℝ) + lam ^ (-(1 / 2 : ℝ))) := by
  let b : ℝ := a + (N : ℝ) + 1
  have hab : a < b := by dsimp [b]; linarith [Nat.cast_nonneg (α := ℝ) N]
  have hinc := deriv_strictMono_of_deriv2_pos hlam0 hf (fun x hx => (h2 x hx).1)
  have hlip := deriv_sub_le_of_deriv2_le hf (fun x hx => (h2 x hx).2)
  have hmono_f' : ∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y → deriv f x ≤ deriv f y := by
    intro x y hx hy hxy
    have := hinc x y hx hy hxy
    have : 0 ≤ lam * (y - x) := mul_nonneg hlam0.le (sub_nonneg.mpr hxy)
    linarith
  have hcont_f : ContinuousOn f (Set.Icc a b) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hdiff_f : DifferentiableOn ℝ f (Set.Ioo a b) :=
    fun x hx => ((hf x (Set.Ioo_subset_Icc_self hx)).differentiableAt (by norm_num)).differentiableWithinAt
  have hmvt_diff : ∀ n : ℕ, 1 ≤ n → n ≤ N →
      deriv f (a + (n : ℝ)) ≤ f (a + (n : ℝ) + 1) - f (a + (n : ℝ)) ∧
      f (a + (n : ℝ) + 1) - f (a + (n : ℝ)) ≤ deriv f (a + (n : ℝ) + 1) := by
    intro n hn1 hn2
    have hx : a + (n : ℝ) ∈ Set.Icc a b :=
      ⟨by linarith [Nat.cast_nonneg (α := ℝ) n], by dsimp [b]; linarith [show (n : ℝ) ≤ N by exact_mod_cast hn2]⟩
    have hy : a + (n : ℝ) + 1 ∈ Set.Icc a b :=
      ⟨by linarith [Nat.cast_nonneg (α := ℝ) n], by dsimp [b]; linarith [show (n : ℝ) ≤ N by exact_mod_cast hn2]⟩
    have hlt : a + (n : ℝ) < a + (n : ℝ) + 1 := by linarith
    obtain ⟨c, hc, hce⟩ := exists_deriv_eq_slope f hlt
      (hcont_f.mono (Set.Icc_subset_Icc hx.1 hy.2))
      (hdiff_f.mono (Set.Ioo_subset_Ioo hx.1 hy.2))
    have hc_mem : c ∈ Set.Icc a b := Set.Icc_subset_Icc hx.1 hy.2 (Set.Ioo_subset_Icc_self hc)
    have hslope : (f (a + (n : ℝ) + 1) - f (a + (n : ℝ))) / ((a + (n : ℝ) + 1) - (a + (n : ℝ))) =
        f (a + (n : ℝ) + 1) - f (a + (n : ℝ)) := by ring
    rw [hslope] at hce
    rw [← hce]
    exact ⟨hmono_f' _ _ hx hc_mem hc.1.le, hmono_f' _ _ hc_mem hy hc.2.le⟩
  have hdiff_mono : ∀ n : ℕ, 1 ≤ n → n + 1 ≤ N →
      f (a + (n : ℝ) + 1) - f (a + (n : ℝ)) ≤ f (a + ((n + 1 : ℕ) : ℝ) + 1) - f (a + ((n + 1 : ℕ) : ℝ)) := by
    intro n hn1 hn2
    have h1 := (hmvt_diff n hn1 (by omega)).2
    have h2' := (hmvt_diff (n + 1) (by omega) hn2).1
    have hcast : a + ((n + 1 : ℕ) : ℝ) = a + (n : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h2' ⊢
    linarith
  let θ : ℝ := min (1 / 4) (Real.sqrt lam)
  have hθ0 : 0 < θ := lt_min (by norm_num) (Real.sqrt_pos.mpr hlam0)
  have hθ1 : θ ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have hθ_le_sqrt : θ ≤ Real.sqrt lam := min_le_right _ _
  have hinv_θ : 1 / θ ≤ 4 + 1 / Real.sqrt lam := by
    dsimp [θ]
    by_cases h : Real.sqrt lam ≤ 1 / 4
    · rw [min_eq_right h]; linarith
    · push Not at h
      rw [min_eq_left h.le]
      have : 0 ≤ 1 / Real.sqrt lam := by positivity
      linarith
  let mmin : ℤ := ⌊deriv f a⌋
  let mmax : ℤ := ⌊deriv f b⌋
  have hmem_m : ∀ n ∈ Icc 1 N, ⌊deriv f (a + (n : ℝ))⌋ ∈ Icc mmin mmax := by
    intro n hn
    rw [mem_Icc] at hn ⊢
    have hx : a + (n : ℝ) ∈ Set.Icc a b :=
      ⟨by linarith [Nat.cast_nonneg (α := ℝ) n], by dsimp [b]; linarith [show (n : ℝ) ≤ N by exact_mod_cast hn.2]⟩
    exact ⟨Int.floor_mono (hmono_f' _ _ ⟨le_rfl, hab.le⟩ hx hx.1),
           Int.floor_mono (hmono_f' _ _ hx ⟨hab.le, le_rfl⟩ hx.2)⟩
  have hpartition : ∑ n ∈ Icc 1 N, eUnit (f (a + (n : ℝ))) =
      ∑ m ∈ Icc mmin mmax,
        ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => ⌊deriv f (a + (n : ℝ))⌋ = m),
          eUnit (f (a + (n : ℝ))) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmem_m]
  have hfiber_bd : ∀ m ∈ Icc mmin mmax,
      ‖∑ n ∈ (Icc 1 N).filter (fun n : ℕ => ⌊deriv f (a + (n : ℝ))⌋ = m),
          eUnit (f (a + (n : ℝ)))‖ ≤ 15 / Real.sqrt lam := by
    intro m _
    let Sm := (Icc 1 N).filter (fun n : ℕ => ⌊deriv f (a + (n : ℝ))⌋ = m)
    let Am := Sm.filter (fun n : ℕ => deriv f (a + (n : ℝ)) < (m : ℝ) + θ)
    let Cm := Sm.filter (fun n : ℕ => (m : ℝ) + θ ≤ deriv f (a + (n : ℝ)) ∧
        (m : ℝ) + 1 - θ < deriv f (a + (n : ℝ) + 1))
    let Bm := Sm.filter (fun n : ℕ => (m : ℝ) + θ ≤ deriv f (a + (n : ℝ)) ∧
        deriv f (a + (n : ℝ) + 1) ≤ (m : ℝ) + 1 - θ)
    have hsplit : ∑ n ∈ Sm, eUnit (f (a + (n : ℝ))) =
        (∑ n ∈ Am, eUnit (f (a + (n : ℝ)))) +
        (∑ n ∈ Bm, eUnit (f (a + (n : ℝ)))) +
        (∑ n ∈ Cm, eUnit (f (a + (n : ℝ)))) := by
      have h1 : Sm = Am ∪ (Bm ∪ Cm) := by
        ext n
        simp only [Am, Bm, Cm, mem_union, mem_filter]
        constructor
        · intro hn
          by_cases hlt : deriv f (a + (n : ℝ)) < (m : ℝ) + θ
          · exact Or.inl ⟨hn, hlt⟩
          · push Not at hlt
            by_cases hle : deriv f (a + (n : ℝ) + 1) ≤ (m : ℝ) + 1 - θ
            · exact Or.inr (Or.inl ⟨hn, hlt, hle⟩)
            · push Not at hle
              exact Or.inr (Or.inr ⟨hn, hlt, hle⟩)
        · rintro (⟨hn, _⟩ | ⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn
      have hd1 : Disjoint Am (Bm ∪ Cm) := by
        rw [disjoint_left]
        intro n hA hBC
        simp only [Am, Bm, Cm, mem_union, mem_filter] at hA hBC
        rcases hBC with ⟨_, hge, _⟩ | ⟨_, hge, _⟩ <;> linarith
      have hd2 : Disjoint Bm Cm := by
        rw [disjoint_left]
        intro n hB hC
        simp only [Bm, Cm, mem_filter] at hB hC
        linarith
      rw [h1, sum_union hd1, sum_union hd2, add_assoc]
    have hAm_card : (Am.card : ℝ) ≤ θ / lam + 1 := by
      by_cases hne : Am.Nonempty
      · let n1 := Am.min' hne
        let n2 := Am.max' hne
        have hn1 : n1 ∈ Am := Finset.min'_mem Am hne
        have hn2 : n2 ∈ Am := Finset.max'_mem Am hne
        have hn1S : n1 ∈ Sm := (mem_filter.mp hn1).1
        have hn2S : n2 ∈ Sm := (mem_filter.mp hn2).1
        have hn1_le : n1 ≤ n2 := Finset.min'_le Am n2 hn2
        have hn1_Icc : n1 ∈ Icc 1 N := (mem_filter.mp hn1S).1
        have hn2_Icc : n2 ∈ Icc 1 N := (mem_filter.mp hn2S).1
        have hx1 : a + (n1 : ℝ) ∈ Set.Icc a b :=
          ⟨by linarith [Nat.cast_nonneg (α := ℝ) n1], by dsimp [b]; linarith [show (n1 : ℝ) ≤ N by exact_mod_cast (mem_Icc.mp hn1_Icc).2]⟩
        have hx2 : a + (n2 : ℝ) ∈ Set.Icc a b :=
          ⟨by linarith [Nat.cast_nonneg (α := ℝ) n2], by dsimp [b]; linarith [show (n2 : ℝ) ≤ N by exact_mod_cast (mem_Icc.mp hn2_Icc).2]⟩
        have hgap := hinc _ _ hx1 hx2 (by linarith [show (n1 : ℝ) ≤ n2 by exact_mod_cast hn1_le])
        have hge_m : (m : ℝ) ≤ deriv f (a + (n1 : ℝ)) := by
          have := (mem_filter.mp hn1S).2
          rw [← this]; exact Int.floor_le _
        have hlt_m : deriv f (a + (n2 : ℝ)) < (m : ℝ) + θ := (mem_filter.mp hn2).2
        have hdiff_le : (n2 : ℝ) - (n1 : ℝ) ≤ θ / lam := by
          rw [le_div_iff₀ hlam0]
          have : a + (n2 : ℝ) - (a + (n1 : ℝ)) = (n2 : ℝ) - (n1 : ℝ) := by ring
          rw [this] at hgap
          linarith
        have hsub_Icc : Am ⊆ Icc n1 n2 := fun k hk =>
          mem_Icc.mpr ⟨Finset.min'_le Am k hk, Finset.le_max' Am k hk⟩
        have hcard_le : Am.card ≤ n2 - n1 + 1 := by
          calc Am.card ≤ (Icc n1 n2).card := card_le_card hsub_Icc
            _ = n2 + 1 - n1 := Nat.card_Icc n1 n2
            _ = n2 - n1 + 1 := by omega
        have hcard_R : (Am.card : ℝ) ≤ (n2 : ℝ) - (n1 : ℝ) + 1 := by
          have hcast : ((n2 - n1 + 1 : ℕ) : ℝ) = (n2 : ℝ) - (n1 : ℝ) + 1 := by
            rw [Nat.cast_add, Nat.cast_sub hn1_le, Nat.cast_one]
          exact_mod_cast hcard_le |> fun h => (Nat.cast_le.mpr h).trans_eq hcast
        linarith
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        simp; positivity
    have hCm_card : (Cm.card : ℝ) ≤ θ / lam + 2 := by
      by_cases hne : Cm.Nonempty
      · let n1 := Cm.min' hne
        let n2 := Cm.max' hne
        by_cases hle1 : n2 ≤ n1 + 1
        · have hsub_Icc : Cm ⊆ Icc n1 n2 := fun k hk =>
            mem_Icc.mpr ⟨Finset.min'_le Cm k hk, Finset.le_max' Cm k hk⟩
          have hcard_le : Cm.card ≤ 2 := by
            calc Cm.card ≤ (Icc n1 n2).card := card_le_card hsub_Icc
              _ = n2 + 1 - n1 := Nat.card_Icc n1 n2
              _ ≤ 2 := by omega
          have : (Cm.card : ℝ) ≤ 2 := by exact_mod_cast hcard_le
          have : 0 ≤ θ / lam := by positivity
          linarith
        · push Not at hle1
          have hn1 : n1 ∈ Cm := Finset.min'_mem Cm hne
          have hn2 : n2 ∈ Cm := Finset.max'_mem Cm hne
          have hn1S : n1 ∈ Sm := (mem_filter.mp hn1).1
          have hn2S : n2 ∈ Sm := (mem_filter.mp hn2).1
          have hn1_Icc : n1 ∈ Icc 1 N := (mem_filter.mp hn1S).1
          have hn2_Icc : n2 ∈ Icc 1 N := (mem_filter.mp hn2S).1
          have hx1 : a + (n1 : ℝ) + 1 ∈ Set.Icc a b :=
            ⟨by linarith [Nat.cast_nonneg (α := ℝ) n1], by dsimp [b]; linarith [show (n1 : ℝ) ≤ N by exact_mod_cast (mem_Icc.mp hn1_Icc).2]⟩
          have hx2 : a + (n2 : ℝ) ∈ Set.Icc a b :=
            ⟨by linarith [Nat.cast_nonneg (α := ℝ) n2], by dsimp [b]; linarith [show (n2 : ℝ) ≤ N by exact_mod_cast (mem_Icc.mp hn2_Icc).2]⟩
          have hgap := hinc _ _ hx1 hx2 (by
            have : (n1 : ℝ) + 1 ≤ (n2 : ℝ) := by exact_mod_cast (by omega : n1 + 1 ≤ n2)
            linarith)
          have hgt : (m : ℝ) + 1 - θ < deriv f (a + (n1 : ℝ) + 1) := (mem_filter.mp hn1).2.2
          have hlt : deriv f (a + (n2 : ℝ)) < (m : ℝ) + 1 := by
            have := (mem_filter.mp hn2S).2
            have hfl := Int.lt_floor_add_one (deriv f (a + (n2 : ℝ)))
            rw [this] at hfl
            exact_mod_cast hfl
          have hdiff_le : (n2 : ℝ) - (n1 : ℝ) - 1 ≤ θ / lam := by
            rw [le_div_iff₀ hlam0]
            have : a + (n2 : ℝ) - (a + (n1 : ℝ) + 1) = (n2 : ℝ) - (n1 : ℝ) - 1 := by ring
            rw [this] at hgap
            linarith
          have hsub_Icc : Cm ⊆ Icc n1 n2 := fun k hk =>
            mem_Icc.mpr ⟨Finset.min'_le Cm k hk, Finset.le_max' Cm k hk⟩
          have hcard_le : Cm.card ≤ n2 - n1 + 1 := by
            calc Cm.card ≤ (Icc n1 n2).card := card_le_card hsub_Icc
              _ = n2 + 1 - n1 := Nat.card_Icc n1 n2
              _ = n2 - n1 + 1 := by omega
          have hcard_R : (Cm.card : ℝ) ≤ (n2 : ℝ) - (n1 : ℝ) + 1 := by
            have hcast : ((n2 - n1 + 1 : ℕ) : ℝ) = (n2 : ℝ) - (n1 : ℝ) + 1 := by
              rw [Nat.cast_add, Nat.cast_sub (by omega : n1 ≤ n2), Nat.cast_one]
            exact_mod_cast hcard_le |> fun h => (Nat.cast_le.mpr h).trans_eq hcast
          linarith
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        simp; positivity
    have hBm_bd : ‖∑ n ∈ Bm, eUnit (f (a + (n : ℝ)))‖ ≤ 2 / θ := by
      by_cases hne : Bm.Nonempty
      · let n1 := Bm.min' hne
        let n2 := Bm.max' hne
        have hn1 : n1 ∈ Bm := Finset.min'_mem Bm hne
        have hn2 : n2 ∈ Bm := Finset.max'_mem Bm hne
        have hn1_le : n1 ≤ n2 := Finset.min'_le Bm n2 hn2
        have hBm_eq : Bm = Icc n1 n2 := by
          ext k
          constructor
          · intro hk
            exact mem_Icc.mpr ⟨Finset.min'_le Bm k hk, Finset.le_max' Bm k hk⟩
          · intro hk
            rw [mem_Icc] at hk
            have hn1S := (mem_filter.mp hn1).1
            have hn2S := (mem_filter.mp hn2).1
            have hn1_Icc := mem_Icc.mp (mem_filter.mp hn1S).1
            have hn2_Icc := mem_Icc.mp (mem_filter.mp hn2S).1
            have hk_Icc : k ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, by omega⟩
            have hx1 : a + (n1 : ℝ) ∈ Set.Icc a b :=
              ⟨by linarith [Nat.cast_nonneg (α := ℝ) n1], by dsimp [b]; linarith [show (n1 : ℝ) ≤ N by exact_mod_cast hn1_Icc.2]⟩
            have hxk : a + (k : ℝ) ∈ Set.Icc a b :=
              ⟨by linarith [Nat.cast_nonneg (α := ℝ) k], by dsimp [b]; linarith [show (k : ℝ) ≤ N by exact_mod_cast (mem_Icc.mp hk_Icc).2]⟩
            have hxk1 : a + (k : ℝ) + 1 ∈ Set.Icc a b :=
              ⟨by linarith [Nat.cast_nonneg (α := ℝ) k], by dsimp [b]; linarith [show (k : ℝ) ≤ N by exact_mod_cast (mem_Icc.mp hk_Icc).2]⟩
            have hx2 : a + (n2 : ℝ) + 1 ∈ Set.Icc a b :=
              ⟨by linarith [Nat.cast_nonneg (α := ℝ) n2], by dsimp [b]; linarith [show (n2 : ℝ) ≤ N by exact_mod_cast hn2_Icc.2]⟩
            have hlo : (m : ℝ) + θ ≤ deriv f (a + (k : ℝ)) :=
              (mem_filter.mp hn1).2.1.trans (hmono_f' _ _ hx1 hxk (by linarith [show (n1 : ℝ) ≤ k by exact_mod_cast hk.1]))
            have hhi : deriv f (a + (k : ℝ) + 1) ≤ (m : ℝ) + 1 - θ :=
              (hmono_f' _ _ hxk1 hx2 (by linarith [show (k : ℝ) ≤ n2 by exact_mod_cast hk.2])).trans (mem_filter.mp hn2).2.2
            have hfk_le : deriv f (a + (k : ℝ)) ≤ deriv f (a + (k : ℝ) + 1) :=
              hmono_f' _ _ hxk hxk1 (by linarith)
            have hfl : ⌊deriv f (a + (k : ℝ))⌋ = m := by
              rw [Int.floor_eq_iff]
              exact ⟨by linarith, by linarith⟩
            exact mem_filter.mpr ⟨mem_filter.mpr ⟨hk_Icc, hfl⟩, hlo, hhi⟩
        let M : ℕ := n2 - n1 + 1
        let g : ℕ → ℝ := fun j => f (a + ((n1 + j - 1 : ℕ) : ℝ)) - (m : ℝ) * (j : ℝ)
        have hshift : ‖∑ n ∈ Bm, eUnit (f (a + (n : ℝ)))‖ = ‖∑ j ∈ Icc 1 M, eUnit (g j)‖ := by
          rw [hBm_eq]
          have hbij : ∑ n ∈ Icc n1 n2, eUnit (f (a + (n : ℝ))) =
              ∑ j ∈ Icc 1 M, eUnit (g j) := by
            refine Finset.sum_bij (fun n _ => n - n1 + 1) ?_ ?_ ?_ ?_
            · intro n hn; rw [mem_Icc] at hn ⊢; omega
            · intro a1 ha1 a2 ha2 heq; rw [mem_Icc] at ha1 ha2; omega
            · intro j hj; rw [mem_Icc] at hj
              refine ⟨n1 + j - 1, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
            · intro n hn
              rw [mem_Icc] at hn
              have hidx : n1 + (n - n1) = n := by omega
              dsimp [g]
              rw [hidx, eUnit_sub]
              have hint : eUnit ((m : ℝ) * ((n - n1 + 1 : ℕ) : ℝ)) = 1 := by
                have : (m : ℝ) * ((n - n1 + 1 : ℕ) : ℝ) = ((m * ((n - n1 + 1 : ℕ) : ℤ) : ℤ) : ℝ) := by
                  push_cast; ring
                rw [this]
                exact eUnit_int_mul _
              rw [hint, star_one, mul_one]
          rw [hbij]
        rw [hshift]
        refine kusmin_landau_seq hθ0 hθ1 ?_ ?_
        · intro j hj1 hj2
          have hn_le : n1 + j - 1 + 1 ≤ N := by
            have := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hn2).1).1).2
            omega
          have hdm := hdiff_mono (n1 + j - 1) (by
            have := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hn1).1).1).1
            omega) hn_le
          dsimp [g]
          have hc1 : ((n1 + j : ℕ) : ℝ) = ((n1 + j - 1 : ℕ) : ℝ) + 1 := by
            have : n1 + j = (n1 + j - 1) + 1 := by omega
            rw [this]; push_cast; ring
          have hc2 : ((n1 + (j + 1) : ℕ) : ℝ) = ((n1 + j - 1 + 1 : ℕ) : ℝ) + 1 := by
            have : n1 + (j + 1) = (n1 + j - 1 + 1) + 1 := by omega
            rw [this]; push_cast; ring
          have hc3 : ((n1 + j - 1 + 1 : ℕ) : ℝ) = ((n1 + j : ℕ) : ℝ) := by
            congr 1; omega
          have hsub1 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
          have hsub2 : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 2 := by push_cast; ring
          rw [hc2, hc3, hsub1, hsub2]
          rw [hc3] at hdm
          have hc1' : a + ((n1 + j : ℕ) : ℝ) = a + ((n1 + j - 1 : ℕ) : ℝ) + 1 := by linarith
          have ha1 : a + (((n1 + j : ℕ) : ℝ) + 1) = a + ((n1 + j : ℕ) : ℝ) + 1 := by ring
          rw [ha1]
          rw [← hc1'] at hdm
          linarith
        · intro j hj1 hj2
          have hk_mem : n1 + j - 1 ∈ Bm := by
            rw [hBm_eq, mem_Icc]; omega
          have hk_Icc := mem_Icc.mp (mem_filter.mp (mem_filter.mp hk_mem).1).1
          have hmvt := hmvt_diff (n1 + j - 1) hk_Icc.1 hk_Icc.2
          have hlo := (mem_filter.mp hk_mem).2.1
          have hhi := (mem_filter.mp hk_mem).2.2
          dsimp [g]
          have hc : ((n1 + j : ℕ) : ℝ) = ((n1 + j - 1 : ℕ) : ℝ) + 1 := by
            have : n1 + j = (n1 + j - 1) + 1 := by omega
            rw [this]; push_cast; ring
          rw [hc]
          have hjc : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
          rw [hjc]
          have harg : a + (((n1 + j - 1 : ℕ) : ℝ) + 1) = a + ((n1 + j - 1 : ℕ) : ℝ) + 1 := by ring
          rw [harg]
          constructor <;> linarith
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        simp; positivity
    have hAm_norm : ‖∑ n ∈ Am, eUnit (f (a + (n : ℝ)))‖ ≤ θ / lam + 1 := by
      calc ‖∑ n ∈ Am, eUnit (f (a + (n : ℝ)))‖
          ≤ ∑ n ∈ Am, ‖eUnit (f (a + (n : ℝ)))‖ := norm_sum_le _ _
        _ = (Am.card : ℝ) := by simp [norm_eUnit]
        _ ≤ θ / lam + 1 := hAm_card
    have hCm_norm : ‖∑ n ∈ Cm, eUnit (f (a + (n : ℝ)))‖ ≤ θ / lam + 2 := by
      calc ‖∑ n ∈ Cm, eUnit (f (a + (n : ℝ)))‖
          ≤ ∑ n ∈ Cm, ‖eUnit (f (a + (n : ℝ)))‖ := norm_sum_le _ _
        _ = (Cm.card : ℝ) := by simp [norm_eUnit]
        _ ≤ θ / lam + 2 := hCm_card
    have hsqrt_le : Real.sqrt lam ≤ 1 := by
      calc Real.sqrt lam ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hlam1
        _ = 1 := Real.sqrt_one
    have hsqrt_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam0
    have h1_le : (1 : ℝ) ≤ 1 / Real.sqrt lam := by
      rw [le_div_iff₀ hsqrt_pos]; linarith
    have hθ_div : θ / lam ≤ 1 / Real.sqrt lam := by
      calc θ / lam ≤ Real.sqrt lam / lam := div_le_div_of_nonneg_right hθ_le_sqrt hlam0.le
        _ = 1 / Real.sqrt lam := by
            rw [div_eq_div_iff hlam0.ne' hsqrt_pos.ne', one_mul, Real.mul_self_sqrt hlam0.le]
    rw [hsplit]
    calc ‖(∑ n ∈ Am, eUnit (f (a + (n : ℝ)))) + (∑ n ∈ Bm, eUnit (f (a + (n : ℝ)))) +
            (∑ n ∈ Cm, eUnit (f (a + (n : ℝ))))‖
        ≤ ‖(∑ n ∈ Am, eUnit (f (a + (n : ℝ)))) + (∑ n ∈ Bm, eUnit (f (a + (n : ℝ))))‖ +
            ‖∑ n ∈ Cm, eUnit (f (a + (n : ℝ)))‖ := norm_add_le _ _
      _ ≤ ‖∑ n ∈ Am, eUnit (f (a + (n : ℝ)))‖ + ‖∑ n ∈ Bm, eUnit (f (a + (n : ℝ)))‖ +
            ‖∑ n ∈ Cm, eUnit (f (a + (n : ℝ)))‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (θ / lam + 1) + (2 / θ) + (θ / lam + 2) := by linarith
      _ ≤ (1 / Real.sqrt lam + 1) + (2 * (4 + 1 / Real.sqrt lam)) + (1 / Real.sqrt lam + 2) := by
          have : 2 / θ = 2 * (1 / θ) := by ring
          linarith
      _ = 4 / Real.sqrt lam + 11 := by ring
      _ ≤ 15 / Real.sqrt lam := by
          have h11 : (11 : ℝ) ≤ 11 / Real.sqrt lam := by
            have := mul_le_mul_of_nonneg_left h1_le (by norm_num : (0 : ℝ) ≤ 11)
            linarith [show 11 * (1 / Real.sqrt lam) = 11 / Real.sqrt lam by ring]
          have hsum15 : 4 / Real.sqrt lam + 11 / Real.sqrt lam = 15 / Real.sqrt lam := by ring
          linarith
  have hm_card : ((Icc mmin mmax).card : ℝ) ≤ α * lam * ((N : ℝ) + 1) + 2 := by
    have hle_m : mmin ≤ mmax := Int.floor_mono (hmono_f' _ _ ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le)
    have hcard_eq : ((Icc mmin mmax).card : ℝ) = (mmax : ℝ) - (mmin : ℝ) + 1 := by
      have h1 : (Icc mmin mmax).card = (mmax + 1 - mmin).toNat := Int.card_Icc mmin mmax
      rw [h1]
      have hnn : 0 ≤ mmax + 1 - mmin := by omega
      have h2 : (((mmax + 1 - mmin).toNat : ℕ) : ℝ) = ((mmax + 1 - mmin : ℤ) : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hnn
      rw [h2]; push_cast; ring
    rw [hcard_eq]
    have h1 : (mmax : ℝ) ≤ deriv f b := Int.floor_le _
    have h2' : deriv f a - 1 < (mmin : ℝ) := by linarith [Int.lt_floor_add_one (deriv f a)]
    have h3 : deriv f b - deriv f a ≤ α * lam * (b - a) := hlip a b ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le
    have hba : b - a = (N : ℝ) + 1 := by dsimp [b]; ring
    rw [hba] at h3
    linarith
  rw [hpartition]
  have hsqrt_eq : lam ^ (1 / 2 : ℝ) = Real.sqrt lam := (Real.sqrt_eq_rpow lam).symm
  have hsqrt_inv : lam ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt lam := by
    rw [Real.rpow_neg hlam0.le, hsqrt_eq, one_div]
  rw [hsqrt_eq, hsqrt_inv]
  have hsqrt_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam0
  have hlam_div : lam / Real.sqrt lam = Real.sqrt lam := by
    rw [div_eq_iff hsqrt_pos.ne', Real.mul_self_sqrt hlam0.le]
  have hsqrt_le : Real.sqrt lam ≤ 1 / Real.sqrt lam := by
    have : Real.sqrt lam ≤ 1 := (Real.sqrt_le_sqrt hlam1).trans_eq Real.sqrt_one
    rw [le_div_iff₀ hsqrt_pos]; nlinarith
  calc ‖∑ m ∈ Icc mmin mmax,
          ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => ⌊deriv f (a + (n : ℝ))⌋ = m),
            eUnit (f (a + (n : ℝ)))‖
      ≤ ∑ m ∈ Icc mmin mmax,
          ‖∑ n ∈ (Icc 1 N).filter (fun n : ℕ => ⌊deriv f (a + (n : ℝ))⌋ = m),
            eUnit (f (a + (n : ℝ)))‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Icc mmin mmax, (15 / Real.sqrt lam) := sum_le_sum hfiber_bd
    _ = ((Icc mmin mmax).card : ℝ) * (15 / Real.sqrt lam) := by simp
    _ ≤ (α * lam * ((N : ℝ) + 1) + 2) * (15 / Real.sqrt lam) := by
        exact mul_le_mul_of_nonneg_right hm_card (by positivity)
    _ = 15 * α * (N : ℝ) * (lam / Real.sqrt lam) + 15 * α * (lam / Real.sqrt lam) +
          30 * (1 / Real.sqrt lam) := by ring
    _ = 15 * α * (N : ℝ) * Real.sqrt lam + 15 * α * Real.sqrt lam + 30 * (1 / Real.sqrt lam) := by
        rw [hlam_div]
    _ ≤ 45 * α * ((N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam) := by
        have h1 : 15 * α * Real.sqrt lam ≤ 15 * α * (1 / Real.sqrt lam) := by
          exact mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
        have h2 : 30 * (1 / Real.sqrt lam) ≤ 30 * α * (1 / Real.sqrt lam) := by
          have : (30 : ℝ) ≤ 30 * α := by linarith
          exact mul_le_mul_of_nonneg_right this (by positivity)
        have h3 : 0 ≤ 30 * α * (N : ℝ) * Real.sqrt lam := by positivity
        linarith
lemma weyl_vdc_A {N H : ℕ} (hH1 : 1 ≤ H) (hHN : H ≤ N) {z : ℕ → ℂ} (hz : ∀ n, ‖z n‖ ≤ 1) :
    ‖∑ n ∈ Icc 1 N, z n‖ ^ 2 ≤
      2 * (N : ℝ) ^ 2 / (H : ℝ) +
      4 * (N : ℝ) / (H : ℝ) *
        ∑ h ∈ Icc 1 (H - 1), ‖∑ n ∈ Icc 1 (N - h), z (n + h) * star (z n)‖ := by
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  let Z : ℕ → ℂ := fun n => if 1 ≤ n ∧ n ≤ N then z n else 0
  have hsum_eq : (H : ℂ) * ∑ n ∈ Icc 1 N, z n =
      ∑ m ∈ Icc 1 (N + H), ∑ j ∈ Icc 1 H, Z (m - j) := by
    have hswap : ∑ m ∈ Icc 1 (N + H), ∑ j ∈ Icc 1 H, Z (m - j) =
        ∑ j ∈ Icc 1 H, ∑ m ∈ Icc 1 (N + H), Z (m - j) := sum_comm
    rw [hswap]
    have hinner : ∀ j ∈ Icc 1 H,
        ∑ m ∈ Icc 1 (N + H), Z (m - j) = ∑ n ∈ Icc 1 N, z n := by
      intro j hj
      rw [mem_Icc] at hj
      have hfilter : ∑ m ∈ Icc 1 (N + H), Z (m - j) =
          ∑ m ∈ (Icc 1 (N + H)).filter (fun m => 1 + j ≤ m ∧ m ≤ N + j), z (m - j) := by
        rw [sum_filter]
        refine sum_congr rfl fun m hm => ?_
        rw [mem_Icc] at hm
        dsimp [Z]
        by_cases h : 1 + j ≤ m ∧ m ≤ N + j
        · rw [if_pos ⟨by omega, by omega⟩, if_pos h]
        · rw [if_neg (by omega), if_neg h]
      rw [hfilter]
      refine Finset.sum_bij (fun m _ => m - j) ?_ ?_ ?_ ?_
      · intro m hm; rw [mem_filter] at hm; rw [mem_Icc]; omega
      · intro m1 hm1 m2 hm2 heq; rw [mem_filter] at hm1 hm2; omega
      · intro n hn; rw [mem_Icc] at hn
        exact ⟨n + j, mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, by omega, by omega⟩, by omega⟩
      · intro m _; rfl
    rw [sum_congr rfl hinner, sum_const, Nat.card_Icc]
    simp [show H + 1 - 1 = H by omega]
  have hCS : (H : ℝ) ^ 2 * ‖∑ n ∈ Icc 1 N, z n‖ ^ 2 ≤
      ((N + H : ℕ) : ℝ) * ∑ m ∈ Icc 1 (N + H), ‖∑ j ∈ Icc 1 H, Z (m - j)‖ ^ 2 := by
    have h1 : (H : ℝ) * ‖∑ n ∈ Icc 1 N, z n‖ =
        ‖∑ m ∈ Icc 1 (N + H), ∑ j ∈ Icc 1 H, Z (m - j)‖ := by
      rw [← hsum_eq, norm_mul, Complex.norm_natCast]
    have h2 : ‖∑ m ∈ Icc 1 (N + H), ∑ j ∈ Icc 1 H, Z (m - j)‖ ≤
        ∑ m ∈ Icc 1 (N + H), ‖∑ j ∈ Icc 1 H, Z (m - j)‖ := norm_sum_le _ _
    have h3 : (∑ m ∈ Icc 1 (N + H), ‖∑ j ∈ Icc 1 H, Z (m - j)‖) ^ 2 ≤
        ((Icc 1 (N + H)).card : ℝ) *
          ∑ m ∈ Icc 1 (N + H), ‖∑ j ∈ Icc 1 H, Z (m - j)‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hcard : (Icc 1 (N + H)).card = N + H := by rw [Nat.card_Icc]; omega
    rw [hcard] at h3
    have hsq1 : ((H : ℝ) * ‖∑ n ∈ Icc 1 N, z n‖) ^ 2 ≤
        (∑ m ∈ Icc 1 (N + H), ‖∑ j ∈ Icc 1 H, Z (m - j)‖) ^ 2 := by
      rw [h1]
      exact pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith [hsq1, h3]
  have hexpand : ∑ m ∈ Icc 1 (N + H), ‖∑ j ∈ Icc 1 H, Z (m - j)‖ ^ 2 ≤
      (H : ℝ) * (N : ℝ) +
      2 * (H : ℝ) * ∑ h ∈ Icc 1 (H - 1), ‖∑ n ∈ Icc 1 (N - h), z (n + h) * star (z n)‖ := by
    have hsq_re : ∀ m, (‖∑ j ∈ Icc 1 H, Z (m - j)‖ ^ 2 : ℝ) =
        (∑ j1 ∈ Icc 1 H, ∑ j2 ∈ Icc 1 H, Z (m - j1) * star (Z (m - j2))).re := by
      intro m
      have hC : ((‖∑ j ∈ Icc 1 H, Z (m - j)‖ ^ 2 : ℝ) : ℂ) =
          ∑ j1 ∈ Icc 1 H, ∑ j2 ∈ Icc 1 H, Z (m - j1) * star (Z (m - j2)) := by
        rw [Complex.ofReal_pow, ← Complex.mul_conj', sum_mul]
        have hcon : (starRingEnd ℂ) (∑ j ∈ Icc 1 H, Z (m - j)) =
            ∑ j ∈ Icc 1 H, star (Z (m - j)) := map_sum (starRingEnd ℂ) _ _
        rw [hcon]
        simp_rw [mul_sum]
      rw [← Complex.ofReal_re (‖∑ j ∈ Icc 1 H, Z (m - j)‖ ^ 2), hC]
    have hsum_re : ∑ m ∈ Icc 1 (N + H), ‖∑ j ∈ Icc 1 H, Z (m - j)‖ ^ 2 =
        (∑ j1 ∈ Icc 1 H, ∑ j2 ∈ Icc 1 H,
          ∑ m ∈ Icc 1 (N + H), Z (m - j1) * star (Z (m - j2))).re := by
      simp_rw [hsq_re, ← Complex.re_sum]
      congr 1
      rw [sum_comm]
      refine sum_congr rfl fun j1 _ => ?_
      rw [sum_comm]
    rw [hsum_re]
    have hpair : ∀ j1 ∈ Icc 1 H, ∀ j2 ∈ Icc 1 H,
        (∑ m ∈ Icc 1 (N + H), Z (m - j1) * star (Z (m - j2))).re ≤
          if j1 = j2 then (N : ℝ)
          else ‖∑ n ∈ Icc 1 (N - (if j1 < j2 then j2 - j1 else j1 - j2)),
                z (n + (if j1 < j2 then j2 - j1 else j1 - j2)) * star (z n)‖ := by
      intro j1 hj1 j2 hj2
      rw [mem_Icc] at hj1 hj2
      split_ifs with heq hlt
      · subst heq
        have h1 : ∀ m ∈ Icc 1 (N + H), (Z (m - j1) * star (Z (m - j1))).re = ‖Z (m - j1)‖ ^ 2 := by
          intro m _
          rw [Complex.star_def, Complex.mul_conj']
          have : (((‖Z (m - j1)‖ : ℂ) ^ 2)).re = ‖Z (m - j1)‖ ^ 2 := by
            rw [← Complex.ofReal_pow, Complex.ofReal_re]
          exact this
        rw [Complex.re_sum, sum_congr rfl h1]
        have hflt : ∑ m ∈ Icc 1 (N + H), ‖Z (m - j1)‖ ^ 2 =
            ∑ m ∈ (Icc 1 (N + H)).filter (fun m => 1 + j1 ≤ m ∧ m ≤ N + j1), ‖z (m - j1)‖ ^ 2 := by
          rw [sum_filter]
          refine sum_congr rfl fun m _ => ?_
          dsimp [Z]
          by_cases h : 1 + j1 ≤ m ∧ m ≤ N + j1
          · rw [if_pos ⟨by omega, by omega⟩, if_pos h]
          · rw [if_neg (by omega), if_neg h]; simp
        rw [hflt]
        calc ∑ m ∈ (Icc 1 (N + H)).filter (fun m => 1 + j1 ≤ m ∧ m ≤ N + j1), ‖z (m - j1)‖ ^ 2
            ≤ ∑ _m ∈ (Icc 1 (N + H)).filter (fun m => 1 + j1 ≤ m ∧ m ≤ N + j1), (1 : ℝ) := by
              refine sum_le_sum fun m _ => ?_
              have := hz (m - j1)
              nlinarith [norm_nonneg (z (m - j1))]
          _ = (((Icc 1 (N + H)).filter (fun m => 1 + j1 ≤ m ∧ m ≤ N + j1)).card : ℝ) := by simp
          _ = (N : ℝ) := by
              have heq_f : (Icc 1 (N + H)).filter (fun m => 1 + j1 ≤ m ∧ m ≤ N + j1) =
                  Icc (1 + j1) (N + j1) := by
                ext m; simp only [mem_filter, mem_Icc]; omega
              rw [heq_f, Nat.card_Icc]; exact_mod_cast (by omega : N + j1 + 1 - (1 + j1) = N)
      ·
        let h := j2 - j1
        have hsum_eq' : ∑ m ∈ Icc 1 (N + H), Z (m - j1) * star (Z (m - j2)) =
            ∑ n ∈ Icc 1 (N - h), z (n + h) * star (z n) := by
          have hflt : ∑ m ∈ Icc 1 (N + H), Z (m - j1) * star (Z (m - j2)) =
              ∑ m ∈ (Icc 1 (N + H)).filter (fun m => 1 + j2 ≤ m ∧ m ≤ N + j1),
                z (m - j1) * star (z (m - j2)) := by
            rw [sum_filter]
            refine sum_congr rfl fun m _ => ?_
            dsimp [Z]
            by_cases hc : 1 + j2 ≤ m ∧ m ≤ N + j1
            · rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩, if_pos hc]
            · rw [if_neg hc]
              by_cases h1 : 1 ≤ m - j1 ∧ m - j1 ≤ N
              · have h2 : ¬ (1 ≤ m - j2 ∧ m - j2 ≤ N) := by omega
                rw [if_pos h1, if_neg h2, map_zero, mul_zero]
              · rw [if_neg h1, zero_mul]
          rw [hflt]
          refine Finset.sum_bij (fun m _ => m - j2) ?_ ?_ ?_ ?_
          · intro m hm; rw [mem_filter] at hm; rw [mem_Icc]; omega
          · intro m1 hm1 m2 hm2 heq'; rw [mem_filter] at hm1 hm2; omega
          · intro n hn; rw [mem_Icc] at hn
            exact ⟨n + j2, mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, by omega, by omega⟩, by omega⟩
          · intro m hm; rw [mem_filter] at hm
            have : m - j1 = m - j2 + h := by omega
            rw [this]
        rw [hsum_eq']
        exact Complex.re_le_norm _
      ·
        have hgt : j2 < j1 := by omega
        let h := j1 - j2
        have hsum_eq' : ∑ m ∈ Icc 1 (N + H), Z (m - j1) * star (Z (m - j2)) =
            star (∑ n ∈ Icc 1 (N - h), z (n + h) * star (z n)) := by
          have hflt : ∑ m ∈ Icc 1 (N + H), Z (m - j1) * star (Z (m - j2)) =
              ∑ m ∈ (Icc 1 (N + H)).filter (fun m => 1 + j1 ≤ m ∧ m ≤ N + j2),
                z (m - j1) * star (z (m - j2)) := by
            rw [sum_filter]
            refine sum_congr rfl fun m _ => ?_
            dsimp [Z]
            by_cases hc : 1 + j1 ≤ m ∧ m ≤ N + j2
            · rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩, if_pos hc]
            · rw [if_neg hc]
              by_cases h1 : 1 ≤ m - j1 ∧ m - j1 ≤ N
              · have h2 : ¬ (1 ≤ m - j2 ∧ m - j2 ≤ N) := by omega
                rw [if_pos h1, if_neg h2, map_zero, mul_zero]
              · rw [if_neg h1, zero_mul]
          rw [hflt, Complex.star_def, map_sum (starRingEnd ℂ)]
          refine Finset.sum_bij (fun m _ => m - j1) ?_ ?_ ?_ ?_
          · intro m hm; rw [mem_filter] at hm; rw [mem_Icc]; omega
          · intro m1 hm1 m2 hm2 heq'; rw [mem_filter] at hm1 hm2; omega
          · intro n hn; rw [mem_Icc] at hn
            exact ⟨n + j1, mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, by omega, by omega⟩, by omega⟩
          · intro m hm; rw [mem_filter] at hm
            have : m - j2 = m - j1 + h := by omega
            rw [this, ← Complex.star_def, star_mul, star_star, mul_comm]
        rw [hsum_eq']
        exact (Complex.re_le_norm _).trans_eq (norm_star _)
    rw [Complex.re_sum]
    calc ∑ j1 ∈ Icc 1 H, (∑ j2 ∈ Icc 1 H,
            ∑ m ∈ Icc 1 (N + H), Z (m - j1) * star (Z (m - j2))).re
        = ∑ j1 ∈ Icc 1 H, ∑ j2 ∈ Icc 1 H,
            (∑ m ∈ Icc 1 (N + H), Z (m - j1) * star (Z (m - j2))).re := by
          refine sum_congr rfl fun j1 _ => Complex.re_sum _ _
      _ ≤ ∑ j1 ∈ Icc 1 H, ∑ j2 ∈ Icc 1 H,
            (if j1 = j2 then (N : ℝ)
             else ‖∑ n ∈ Icc 1 (N - (if j1 < j2 then j2 - j1 else j1 - j2)),
                   z (n + (if j1 < j2 then j2 - j1 else j1 - j2)) * star (z n)‖) := by
          refine sum_le_sum fun j1 hj1 => sum_le_sum fun j2 hj2 => hpair j1 hj1 j2 hj2
      _ ≤ (H : ℝ) * (N : ℝ) +
          2 * (H : ℝ) * ∑ h ∈ Icc 1 (H - 1),
            ‖∑ n ∈ Icc 1 (N - h), z (n + h) * star (z n)‖ := by
          let g : ℕ → ℝ := fun h => ‖∑ n ∈ Icc 1 (N - h), z (n + h) * star (z n)‖
          have hnn : ∀ h, 0 ≤ g h := fun _ => norm_nonneg _
          have hsplit_j : ∀ j1 ∈ Icc 1 H,
              ∑ j2 ∈ Icc 1 H,
                (if j1 = j2 then (N : ℝ) else g (if j1 < j2 then j2 - j1 else j1 - j2)) ≤
              (N : ℝ) + 2 * ∑ h ∈ Icc 1 (H - 1), g h := by
            intro j1 hj1
            rw [mem_Icc] at hj1
            have hdecomp : Icc 1 H = insert j1 ((Icc 1 (j1 - 1)) ∪ (Icc (j1 + 1) H)) := by
              ext k; simp only [mem_Icc, mem_insert, mem_union]; omega
            have hnotmem : j1 ∉ Icc 1 (j1 - 1) ∪ Icc (j1 + 1) H := by
              simp only [mem_union, mem_Icc]; omega
            have hdisj : Disjoint (Icc 1 (j1 - 1)) (Icc (j1 + 1) H) := by
              rw [disjoint_left]; intro k h1 h2; simp only [mem_Icc] at h1 h2; omega
            rw [hdecomp, sum_insert hnotmem, if_pos rfl, sum_union hdisj]
            have hleft : ∑ j2 ∈ Icc 1 (j1 - 1),
                (if j1 = j2 then (N : ℝ) else g (if j1 < j2 then j2 - j1 else j1 - j2)) ≤
                ∑ h ∈ Icc 1 (H - 1), g h := by
              have heqL : ∑ j2 ∈ Icc 1 (j1 - 1),
                  (if j1 = j2 then (N : ℝ) else g (if j1 < j2 then j2 - j1 else j1 - j2)) =
                  ∑ h ∈ Icc 1 (j1 - 1), g h := by
                refine Finset.sum_bij (fun j2 _ => j1 - j2) ?_ ?_ ?_ ?_
                · intro j2 hj2; rw [mem_Icc] at hj2 ⊢; omega
                · intro a1 ha1 a2 ha2 heq'; rw [mem_Icc] at ha1 ha2; omega
                · intro h hh; rw [mem_Icc] at hh
                  exact ⟨j1 - h, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
                · intro j2 hj2; rw [mem_Icc] at hj2
                  rw [if_neg (by omega), if_neg (by omega)]
              rw [heqL]
              exact sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (by omega)) (fun _ _ _ => hnn _)
            have hright : ∑ j2 ∈ Icc (j1 + 1) H,
                (if j1 = j2 then (N : ℝ) else g (if j1 < j2 then j2 - j1 else j1 - j2)) ≤
                ∑ h ∈ Icc 1 (H - 1), g h := by
              have heqR : ∑ j2 ∈ Icc (j1 + 1) H,
                  (if j1 = j2 then (N : ℝ) else g (if j1 < j2 then j2 - j1 else j1 - j2)) =
                  ∑ h ∈ Icc 1 (H - j1), g h := by
                refine Finset.sum_bij (fun j2 _ => j2 - j1) ?_ ?_ ?_ ?_
                · intro j2 hj2; rw [mem_Icc] at hj2 ⊢; omega
                · intro a1 ha1 a2 ha2 heq'; rw [mem_Icc] at ha1 ha2; omega
                · intro h hh; rw [mem_Icc] at hh
                  exact ⟨j1 + h, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
                · intro j2 hj2; rw [mem_Icc] at hj2
                  rw [if_neg (by omega), if_pos (by omega)]
              rw [heqR]
              exact sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (by omega)) (fun _ _ _ => hnn _)
            linarith
          calc ∑ j1 ∈ Icc 1 H, ∑ j2 ∈ Icc 1 H,
                (if j1 = j2 then (N : ℝ) else g (if j1 < j2 then j2 - j1 else j1 - j2))
              ≤ ∑ _j1 ∈ Icc 1 H, ((N : ℝ) + 2 * ∑ h ∈ Icc 1 (H - 1), g h) :=
                sum_le_sum hsplit_j
            _ = (H : ℝ) * ((N : ℝ) + 2 * ∑ h ∈ Icc 1 (H - 1), g h) := by
                rw [sum_const, Nat.card_Icc, show H + 1 - 1 = H by omega, nsmul_eq_mul]
            _ = (H : ℝ) * (N : ℝ) + 2 * (H : ℝ) * ∑ h ∈ Icc 1 (H - 1), g h := by ring
  have hNH : ((N + H : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    have : N + H ≤ 2 * N := by omega
    exact_mod_cast this
  have hcomb : (H : ℝ) ^ 2 * ‖∑ n ∈ Icc 1 N, z n‖ ^ 2 ≤
      2 * (N : ℝ) * ((H : ℝ) * (N : ℝ) +
        2 * (H : ℝ) * ∑ h ∈ Icc 1 (H - 1), ‖∑ n ∈ Icc 1 (N - h), z (n + h) * star (z n)‖) := by
    have hnn_rhs : 0 ≤ (H : ℝ) * (N : ℝ) +
        2 * (H : ℝ) * ∑ h ∈ Icc 1 (H - 1), ‖∑ n ∈ Icc 1 (N - h), z (n + h) * star (z n)‖ := by
      have : 0 ≤ ∑ h ∈ Icc 1 (H - 1), ‖∑ n ∈ Icc 1 (N - h), z (n + h) * star (z n)‖ :=
        sum_nonneg (fun _ _ => norm_nonneg _)
      positivity
    calc (H : ℝ) ^ 2 * ‖∑ n ∈ Icc 1 N, z n‖ ^ 2
        ≤ ((N + H : ℕ) : ℝ) * ∑ m ∈ Icc 1 (N + H), ‖∑ j ∈ Icc 1 H, Z (m - j)‖ ^ 2 := hCS
      _ ≤ ((N + H : ℕ) : ℝ) * ((H : ℝ) * (N : ℝ) +
            2 * (H : ℝ) * ∑ h ∈ Icc 1 (H - 1), ‖∑ n ∈ Icc 1 (N - h), z (n + h) * star (z n)‖) :=
          mul_le_mul_of_nonneg_left hexpand (Nat.cast_nonneg _)
      _ ≤ 2 * (N : ℝ) * ((H : ℝ) * (N : ℝ) +
            2 * (H : ℝ) * ∑ h ∈ Icc 1 (H - 1), ‖∑ n ∈ Icc 1 (N - h), z (n + h) * star (z n)‖) :=
          mul_le_mul_of_nonneg_right hNH hnn_rhs
  have hH2pos : 0 < (H : ℝ) ^ 2 := by positivity
  have hdiv := (le_div_iff₀' hH2pos).mpr hcomb
  have hrhs :
      2 * (N : ℝ) * ((H : ℝ) * (N : ℝ) +
        2 * (H : ℝ) * ∑ h ∈ Icc 1 (H - 1), ‖∑ n ∈ Icc 1 (N - h), z (n + h) * star (z n)‖) /
      (H : ℝ) ^ 2 =
      2 * (N : ℝ) ^ 2 / (H : ℝ) +
      4 * (N : ℝ) / (H : ℝ) *
        ∑ h ∈ Icc 1 (H - 1), ‖∑ n ∈ Icc 1 (N - h), z (n + h) * star (z n)‖ := by
    field_simp [hHpos.ne']
    ring
  linarith
noncomputable def vdcA (k : ℕ) : ℝ := 1 / ((2 : ℝ) ^ k - 2)
noncomputable def vdcC (k : ℕ) : ℝ := 1 / (2 : ℝ) ^ (k - 2)
noncomputable def vdcD (k : ℕ) : ℝ := 1 / (2 : ℝ) ^ (k - 1)
lemma vdcA_pos {k : ℕ} (hk : 2 ≤ k) : 0 < vdcA k := by
  unfold vdcA
  have h2k : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k - 2 := by linarith
  positivity
lemma vdcA_succ {k : ℕ} (hk : 2 ≤ k) :
    vdcA (k + 1) = (1 / 2) * (vdcA k / (vdcA k + 1)) := by
  unfold vdcA
  have h2k : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
    calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
  have h1 : (2 : ℝ) ^ k - 2 ≠ 0 := by linarith
  have h2 : (2 : ℝ) ^ (k + 1) - 2 ≠ 0 := by rw [pow_succ]; linarith
  have h3 : (2 : ℝ) ^ k - 1 ≠ 0 := by linarith
  have hsum : (1 : ℝ) / ((2 : ℝ) ^ k - 2) + 1 = ((2 : ℝ) ^ k - 1) / ((2 : ℝ) ^ k - 2) := by
    rw [one_div, eq_div_iff h1, add_mul, inv_mul_cancel₀ h1]; ring
  rw [hsum, div_div_div_cancel_right₀ h1, pow_succ, one_div_mul_one_div]
  congr 1; ring
lemma vdcC_succ {k : ℕ} (hk : 2 ≤ k) : vdcC (k + 1) = vdcC k / 2 := by
  unfold vdcC
  have h : k + 1 - 2 = (k - 2) + 1 := by omega
  rw [h, pow_succ]
  ring
lemma vdcD_succ {k : ℕ} (hk : 2 ≤ k) : vdcD (k + 1) = vdcD k / 2 := by
  unfold vdcD
  have h : k + 1 - 1 = (k - 1) + 1 := by omega
  rw [h, pow_succ]
  ring
lemma vdcC_le_one {k : ℕ} (_hk : 2 ≤ k) : vdcC k ≤ 1 := by
  unfold vdcC
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k - 2) := one_le_pow₀ (by norm_num)
  exact div_le_one_of_le₀ h1 (by positivity)
lemma iteratedDeriv_shift_sub {k : ℕ} {f : ℝ → ℝ} {a b h : ℝ} (hh : 0 < h)
    (hf : ∀ x ∈ Set.Icc a (b + h), ContDiffAt ℝ (k + 1) f x) :
    (∀ x ∈ Set.Icc a b, ContDiffAt ℝ k (fun y => f (y + h) - f y) x) ∧
    ∀ x ∈ Set.Icc a b, ∃ ξ ∈ Set.Ioo x (x + h),
      iteratedDeriv k (fun y => f (y + h) - f y) x = h * iteratedDeriv (k + 1) f ξ := by
  have hcd_add : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ (k + 1) (fun y => f (y + h)) x := by
    intro x hx
    exact (hf (x + h) ⟨by linarith [hx.1], by linarith [hx.2]⟩).comp x
      (contDiffAt_id.add contDiffAt_const)
  have hcd_id : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ (k + 1) f x :=
    fun x hx => hf x ⟨hx.1, by linarith [hx.2]⟩
  refine ⟨fun x hx => ((hcd_add x hx).sub (hcd_id x hx)).of_le (by norm_cast; omega), ?_⟩
  intro x hx
  have hsub : iteratedDeriv k (fun y => f (y + h) - f y) x =
      iteratedDeriv k (fun y => f (y + h)) x - iteratedDeriv k f x := by
    apply iteratedDeriv_sub
    · exact ((hcd_add x hx).of_le (by norm_cast; omega))
    · exact ((hcd_id x hx).of_le (by norm_cast; omega))
  have hcomp : iteratedDeriv k (fun y => f (y + h)) x = iteratedDeriv k f (x + h) :=
    congrFun (iteratedDeriv_comp_add_const k f h) x
  rw [hsub, hcomp]
  have hdiff : ∀ y ∈ Set.Icc x (x + h), DifferentiableAt ℝ (iteratedDeriv k f) y := by
    intro y hy
    have hy' : y ∈ Set.Icc a (b + h) := ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
    have hcd1 : ContDiffAt ℝ 1 (iteratedDeriv k f) y :=
      contDiffAt_iteratedDeriv ((hf y hy').of_le (by norm_cast; omega))
    exact hcd1.differentiableAt (by norm_num)
  have hcont : ContinuousOn (iteratedDeriv k f) (Set.Icc x (x + h)) :=
    fun y hy => (hdiff y hy).continuousAt.continuousWithinAt
  have hdiff_oo : DifferentiableOn ℝ (iteratedDeriv k f) (Set.Ioo x (x + h)) :=
    fun y hy => (hdiff y (Set.Ioo_subset_Icc_self hy)).differentiableWithinAt
  obtain ⟨ξ, hξ, hslope⟩ := exists_deriv_eq_slope (iteratedDeriv k f) (by linarith : x < x + h)
    hcont hdiff_oo
  refine ⟨ξ, hξ, ?_⟩
  rw [iteratedDeriv_succ]
  have hsubx : x + h - x = h := by ring
  rw [hsubx, eq_div_iff hh.ne'] at hslope
  linarith
lemma vdc_kth_deriv : ∀ k : ℕ, 2 ≤ k →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {N : ℕ}, 1 ≤ N → ∀ {a lam α : ℝ}, 0 < lam → lam ≤ 1 → 1 ≤ α →
        ∀ {f : ℝ → ℝ}, (∀ x ∈ Set.Icc a (a + (N : ℝ) + 1), ContDiffAt ℝ k f x) →
        (∀ x ∈ Set.Icc a (a + (N : ℝ) + 1),
          lam ≤ iteratedDeriv k f x ∧ iteratedDeriv k f x ≤ α * lam) →
        ‖∑ n ∈ Icc 1 N, eUnit (f (a + (n : ℝ)))‖ ≤
          C * α * (N : ℝ) * (lam ^ vdcA k + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨45, by norm_num, ?_⟩
    intro N hN a lam α hlam0 hlam1 hα f hf h2
    have hbd := vdc_second_deriv hN hlam0 hlam1 hα hf h2
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hA : vdcA 2 = 1 / 2 := by unfold vdcA; norm_num
    have hC : vdcC 2 = 1 := by unfold vdcC; norm_num
    have hD : vdcD 2 = 1 / 2 := by unfold vdcD; norm_num
    rw [hA, hC, hD, Real.rpow_neg_one]
    have hmul : (N : ℝ) * ((N : ℝ)⁻¹ * lam ^ (-(1 / 2 : ℝ))) = lam ^ (-(1 / 2 : ℝ)) := by
      field_simp [hNpos.ne']
    have hrhs : 45 * α * (N : ℝ) * (lam ^ (1 / 2 : ℝ) + (N : ℝ)⁻¹ * lam ^ (-(1 / 2 : ℝ))) =
        45 * α * ((N : ℝ) * lam ^ (1 / 2 : ℝ) + lam ^ (-(1 / 2 : ℝ))) := by
      calc 45 * α * (N : ℝ) * (lam ^ (1 / 2 : ℝ) + (N : ℝ)⁻¹ * lam ^ (-(1 / 2 : ℝ)))
          = 45 * α * ((N : ℝ) * lam ^ (1 / 2 : ℝ) + (N : ℝ) * ((N : ℝ)⁻¹ * lam ^ (-(1 / 2 : ℝ)))) := by ring
        _ = 45 * α * ((N : ℝ) * lam ^ (1 / 2 : ℝ) + lam ^ (-(1 / 2 : ℝ))) := by rw [hmul]
    linarith
  | succ k hk ih =>
    obtain ⟨Ck, hCk1, hIH⟩ := ih
    refine ⟨Real.sqrt (4 + 4 * Ck) + 2, by linarith [Real.sqrt_nonneg (4 + 4 * Ck)], ?_⟩
    intro N hN a lam α hlam0 hlam1 hα f hf hk1
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hAk_pos : 0 < vdcA k := vdcA_pos hk
    let eH : ℝ := vdcA k / (vdcA k + 1)
    have heH_pos : 0 < eH := by positivity
    have heH_lt1 : eH < 1 := by dsimp [eH]; rw [div_lt_one (by linarith)]; linarith
    have h2A : 2 * vdcA (k + 1) = eH := by rw [vdcA_succ hk]; dsimp [eH]; ring
    have hpow_ge1 : 1 ≤ lam ^ (-eH) := by
      rw [Real.rpow_neg hlam0.le, one_le_inv₀ (Real.rpow_pos_of_pos hlam0 _)]
      exact Real.rpow_le_one hlam0.le hlam1 heH_pos.le
    let H0 : ℕ := ⌊lam ^ (-eH)⌋₊
    have hH0_ge1 : 1 ≤ H0 := Nat.le_floor (by simpa using hpow_ge1)
    let H : ℕ := min N H0
    have hH1 : 1 ≤ H := le_min hN hH0_ge1
    have hHN : H ≤ N := min_le_left N H0
    have hH_le_H0 : H ≤ H0 := min_le_right N H0
    have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
    have hH_le_pow : (H : ℝ) ≤ lam ^ (-eH) :=
      (Nat.cast_le.mpr hH_le_H0).trans (Nat.floor_le (by positivity))
    have hHlam_le1 : (H : ℝ) * lam ≤ 1 := by
      calc (H : ℝ) * lam ≤ lam ^ (-eH) * lam := mul_le_mul_of_nonneg_right hH_le_pow hlam0.le
        _ = lam ^ (-eH) * lam ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = lam ^ (1 - eH) := by rw [← Real.rpow_add hlam0]; congr 1; ring
        _ ≤ 1 := Real.rpow_le_one hlam0.le hlam1 (by linarith)
    have hHlam_ak : ((H : ℝ) * lam) ^ vdcA k ≤ lam ^ eH := by
      have h1 : (H : ℝ) * lam ≤ lam ^ (1 - eH) := by
        calc (H : ℝ) * lam ≤ lam ^ (-eH) * lam ^ (1 : ℝ) := by
              rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_right hH_le_pow hlam0.le
          _ = lam ^ (1 - eH) := by rw [← Real.rpow_add hlam0]; congr 1; ring
      calc ((H : ℝ) * lam) ^ vdcA k ≤ (lam ^ (1 - eH)) ^ vdcA k :=
            Real.rpow_le_rpow (by positivity) h1 hAk_pos.le
        _ = lam ^ ((1 - eH) * vdcA k) := (Real.rpow_mul hlam0.le _ _).symm
        _ = lam ^ eH := by
            congr 1; dsimp [eH]; field_simp [(by linarith : vdcA k + 1 ≠ 0)]; ring
    have hA := weyl_vdc_A hH1 hHN (z := fun n => eUnit (f (a + (n : ℝ))))
      (fun n => (norm_eUnit _).le)
    have hinner : ∀ h ∈ Icc 1 (H - 1),
        ‖∑ n ∈ Icc 1 (N - h),
          eUnit (f (a + ((n + h : ℕ) : ℝ))) * star (eUnit (f (a + (n : ℝ))))‖ ≤
        Ck * α * (N : ℝ) * (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := by
      intro h hh
      rw [mem_Icc] at hh
      have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast (by omega : 0 < h)
      have hNh1 : 1 ≤ N - h := by omega
      have hNh_pos : (0 : ℝ) < ((N - h : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N - h)
      have hNh_le : ((N - h : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N h
      have hshift_sum :
          ∑ n ∈ Icc 1 (N - h),
            eUnit (f (a + ((n + h : ℕ) : ℝ))) * star (eUnit (f (a + (n : ℝ)))) =
          ∑ n ∈ Icc 1 (N - h),
            eUnit ((fun y => f (y + (h : ℝ)) - f y) (a + (n : ℝ))) := by
        refine sum_congr rfl fun n _ => ?_
        rw [← eUnit_sub]
        congr 1
        push_cast; ring
      rw [hshift_sum]
      have hsub_dom : ∀ x ∈ Set.Icc a (a + ((N - h : ℕ) : ℝ) + 1 + (h : ℝ)), ContDiffAt ℝ (k + 1) f x := by
        intro x hx
        refine hf x ⟨hx.1, ?_⟩
        have hcast : ((N - h : ℕ) : ℝ) + (h : ℝ) = (N : ℝ) := by
          exact_mod_cast Nat.sub_add_cancel (by omega : h ≤ N)
        linarith [hx.2]
      obtain ⟨hg_cd, hg_mvt⟩ := iteratedDeriv_shift_sub hhpos hsub_dom
      have hmu0 : 0 < (h : ℝ) * lam := mul_pos hhpos hlam0
      have hmu1 : (h : ℝ) * lam ≤ 1 := by
        calc (h : ℝ) * lam ≤ (H : ℝ) * lam := mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : h ≤ H)) hlam0.le
          _ ≤ 1 := hHlam_le1
      have hg_bd : ∀ x ∈ Set.Icc a (a + ((N - h : ℕ) : ℝ) + 1),
          (h : ℝ) * lam ≤ iteratedDeriv k (fun y => f (y + (h : ℝ)) - f y) x ∧
          iteratedDeriv k (fun y => f (y + (h : ℝ)) - f y) x ≤ α * ((h : ℝ) * lam) := by
        intro x hx
        obtain ⟨ξ, hξ, hξ_eq⟩ := hg_mvt x hx
        have hξ_mem : ξ ∈ Set.Icc a (a + (N : ℝ) + 1) := by
          have hcast : ((N - h : ℕ) : ℝ) + (h : ℝ) = (N : ℝ) := by
            exact_mod_cast Nat.sub_add_cancel (by omega : h ≤ N)
          exact ⟨by linarith [hx.1, hξ.1], by linarith [hx.2, hξ.2]⟩
        have hfk := hk1 ξ hξ_mem
        rw [hξ_eq]
        constructor
        · exact mul_le_mul_of_nonneg_left hfk.1 hhpos.le
        · calc (h : ℝ) * iteratedDeriv (k + 1) f ξ ≤ (h : ℝ) * (α * lam) :=
                mul_le_mul_of_nonneg_left hfk.2 hhpos.le
            _ = α * ((h : ℝ) * lam) := by ring
      have hstep := hIH hNh1 hmu0 hmu1 hα hg_cd hg_bd
      have ht1 : ((N - h : ℕ) : ℝ) * ((h : ℝ) * lam) ^ vdcA k ≤ (N : ℝ) * lam ^ eH := by
        calc ((N - h : ℕ) : ℝ) * ((h : ℝ) * lam) ^ vdcA k
            ≤ (N : ℝ) * ((H : ℝ) * lam) ^ vdcA k := by
              gcongr
              exact_mod_cast (by omega : h ≤ H)
          _ ≤ (N : ℝ) * lam ^ eH := mul_le_mul_of_nonneg_left hHlam_ak hNpos.le
      have ht2 : ((N - h : ℕ) : ℝ) * (((N - h : ℕ) : ℝ) ^ (-vdcC k) * ((h : ℝ) * lam) ^ (-vdcD k)) ≤
          (N : ℝ) * ((N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := by
        have h1ck : 0 ≤ 1 - vdcC k := by linarith [vdcC_le_one hk]
        have hNpow1 : ((N - h : ℕ) : ℝ) * ((N - h : ℕ) : ℝ) ^ (-vdcC k) =
            ((N - h : ℕ) : ℝ) ^ (1 - vdcC k) := by
          calc ((N - h : ℕ) : ℝ) * ((N - h : ℕ) : ℝ) ^ (-vdcC k)
              = ((N - h : ℕ) : ℝ) ^ (1 : ℝ) * ((N - h : ℕ) : ℝ) ^ (-vdcC k) := by rw [Real.rpow_one]
            _ = ((N - h : ℕ) : ℝ) ^ (1 + -vdcC k) := (Real.rpow_add hNh_pos _ _).symm
            _ = ((N - h : ℕ) : ℝ) ^ (1 - vdcC k) := by rw [sub_eq_add_neg]
        have hNpow2 : (N : ℝ) * (N : ℝ) ^ (-vdcC k) = (N : ℝ) ^ (1 - vdcC k) := by
          calc (N : ℝ) * (N : ℝ) ^ (-vdcC k)
              = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-vdcC k) := by rw [Real.rpow_one]
            _ = (N : ℝ) ^ (1 + -vdcC k) := (Real.rpow_add hNpos _ _).symm
            _ = (N : ℝ) ^ (1 - vdcC k) := by rw [sub_eq_add_neg]
        have hNle : ((N - h : ℕ) : ℝ) ^ (1 - vdcC k) ≤ (N : ℝ) ^ (1 - vdcC k) :=
          Real.rpow_le_rpow hNh_pos.le hNh_le h1ck
        have hh_ge1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh.1
        have hd_pos : 0 < vdcD k := by unfold vdcD; positivity
        have hh_pow : (h : ℝ) ^ (-vdcD k) ≤ 1 := by
          rw [Real.rpow_neg hhpos.le, inv_le_one₀ (Real.rpow_pos_of_pos hhpos _)]
          exact Real.one_le_rpow hh_ge1 hd_pos.le
        have hmul_pow : ((h : ℝ) * lam) ^ (-vdcD k) ≤ lam ^ (-vdcD k) := by
          rw [Real.mul_rpow hhpos.le hlam0.le]
          calc (h : ℝ) ^ (-vdcD k) * lam ^ (-vdcD k) ≤ 1 * lam ^ (-vdcD k) :=
                mul_le_mul_of_nonneg_right hh_pow (Real.rpow_nonneg hlam0.le _)
            _ = lam ^ (-vdcD k) := one_mul _
        calc ((N - h : ℕ) : ℝ) * (((N - h : ℕ) : ℝ) ^ (-vdcC k) * ((h : ℝ) * lam) ^ (-vdcD k))
            = (((N - h : ℕ) : ℝ) * ((N - h : ℕ) : ℝ) ^ (-vdcC k)) * ((h : ℝ) * lam) ^ (-vdcD k) := by ring
          _ = ((N - h : ℕ) : ℝ) ^ (1 - vdcC k) * ((h : ℝ) * lam) ^ (-vdcD k) := by rw [hNpow1]
          _ ≤ (N : ℝ) ^ (1 - vdcC k) * lam ^ (-vdcD k) :=
              mul_le_mul hNle hmul_pow (Real.rpow_nonneg hmu0.le _) (Real.rpow_nonneg hNpos.le _)
          _ = (N : ℝ) * ((N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := by rw [← hNpow2]; ring
      calc ‖∑ n ∈ Icc 1 (N - h),
              eUnit ((fun y => f (y + (h : ℝ)) - f y) (a + (n : ℝ)))‖
          ≤ Ck * α * ((N - h : ℕ) : ℝ) *
              (((h : ℝ) * lam) ^ vdcA k + ((N - h : ℕ) : ℝ) ^ (-vdcC k) * ((h : ℝ) * lam) ^ (-vdcD k)) := hstep
        _ = Ck * α * (((N - h : ℕ) : ℝ) * ((h : ℝ) * lam) ^ vdcA k +
              ((N - h : ℕ) : ℝ) * (((N - h : ℕ) : ℝ) ^ (-vdcC k) * ((h : ℝ) * lam) ^ (-vdcD k))) := by ring
        _ ≤ Ck * α * ((N : ℝ) * lam ^ eH + (N : ℝ) * ((N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k))) := by
              exact mul_le_mul_of_nonneg_left (add_le_add ht1 ht2) (by positivity)
        _ = Ck * α * (N : ℝ) * (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := by ring
    have hinvH : 1 / (H : ℝ) ≤ 2 * lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k) := by
      dsimp [H]
      by_cases hmin : N ≤ H0
      · rw [min_eq_left hmin]
        have h1 : 1 / (N : ℝ) ≤ (N : ℝ) ^ (-vdcC k) := by
          rw [one_div, ← Real.rpow_neg_one]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith [vdcC_le_one hk])
        have hlam_ge1 : 1 ≤ lam ^ (-vdcD k) := by
          rw [Real.rpow_neg hlam0.le, one_le_inv₀ (Real.rpow_pos_of_pos hlam0 _)]
          exact Real.rpow_le_one hlam0.le hlam1 (by unfold vdcD; positivity)
        have h2 : (N : ℝ) ^ (-vdcC k) ≤ (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k) :=
          le_mul_of_one_le_right (Real.rpow_nonneg hNpos.le _) hlam_ge1
        have h3 : 0 ≤ 2 * lam ^ eH := by positivity
        linarith
      · push Not at hmin
        rw [min_eq_right hmin.le]
        have hH0_gt : lam ^ (-eH) < (H0 : ℝ) + 1 := Nat.lt_floor_add_one _
        have hH0_ge : lam ^ (-eH) ≤ 2 * (H0 : ℝ) := by
          have : (1 : ℝ) ≤ (H0 : ℝ) := by exact_mod_cast hH0_ge1
          linarith
        have h1 : 1 / (H0 : ℝ) ≤ 2 * lam ^ eH := by
          have hH0_pos : (0 : ℝ) < (H0 : ℝ) := by exact_mod_cast (by omega : 0 < H0)
          rw [div_le_iff₀ hH0_pos]
          have hmul : lam ^ eH * lam ^ (-eH) = 1 := by
            rw [← Real.rpow_add hlam0, add_neg_cancel, Real.rpow_zero]
          calc (1 : ℝ) = lam ^ eH * lam ^ (-eH) := hmul.symm
            _ ≤ lam ^ eH * (2 * (H0 : ℝ)) := mul_le_mul_of_nonneg_left hH0_ge (Real.rpow_nonneg hlam0.le _)
            _ = 2 * lam ^ eH * (H0 : ℝ) := by ring
        have h2 : 0 ≤ (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k) := by positivity
        linarith
    have hsum_le : ∑ h ∈ Icc 1 (H - 1),
        ‖∑ n ∈ Icc 1 (N - h),
          eUnit (f (a + ((n + h : ℕ) : ℝ))) * star (eUnit (f (a + (n : ℝ))))‖ ≤
        (H : ℝ) * (Ck * α * (N : ℝ) * (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k))) := by
      calc ∑ h ∈ Icc 1 (H - 1),
            ‖∑ n ∈ Icc 1 (N - h),
              eUnit (f (a + ((n + h : ℕ) : ℝ))) * star (eUnit (f (a + (n : ℝ))))‖
          ≤ ∑ _h ∈ Icc 1 (H - 1),
              (Ck * α * (N : ℝ) * (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k))) :=
            sum_le_sum hinner
        _ = ((Icc 1 (H - 1)).card : ℝ) *
              (Ck * α * (N : ℝ) * (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k))) := by simp
        _ ≤ (H : ℝ) * (Ck * α * (N : ℝ) * (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k))) := by
            have hcard : ((Icc 1 (H - 1)).card : ℝ) ≤ (H : ℝ) := by
              rw [Nat.card_Icc]; exact_mod_cast (by omega : H - 1 + 1 - 1 ≤ H)
            exact mul_le_mul_of_nonneg_right hcard (by positivity)
    have hsq_bd : ‖∑ n ∈ Icc 1 N, eUnit (f (a + (n : ℝ)))‖ ^ 2 ≤
        (4 + 4 * Ck) * α ^ 2 * (N : ℝ) ^ 2 *
          (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := by
      have hα_le_sq : α ≤ α ^ 2 := by nlinarith
      have h1_le_sq : 1 ≤ α ^ 2 := by nlinarith
      have hterm1 : 2 * (N : ℝ) ^ 2 / (H : ℝ) ≤
          4 * α ^ 2 * (N : ℝ) ^ 2 * (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := by
        have hstep1 : 2 * (N : ℝ) ^ 2 / (H : ℝ) = 2 * (N : ℝ) ^ 2 * (1 / (H : ℝ)) := by ring
        rw [hstep1]
        have hnn : 0 ≤ lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k) := by positivity
        calc 2 * (N : ℝ) ^ 2 * (1 / (H : ℝ))
            ≤ 2 * (N : ℝ) ^ 2 * (2 * lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) :=
              mul_le_mul_of_nonneg_left hinvH (by positivity)
          _ ≤ 4 * (N : ℝ) ^ 2 * (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := by
              have : 0 ≤ (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k) := by positivity
              nlinarith
          _ ≤ 4 * α ^ 2 * (N : ℝ) ^ 2 * (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := by
              have : 0 ≤ (N : ℝ) ^ 2 * (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := by positivity
              nlinarith
      have hterm2 : 4 * (N : ℝ) / (H : ℝ) *
          ∑ h ∈ Icc 1 (H - 1),
            ‖∑ n ∈ Icc 1 (N - h),
              eUnit (f (a + ((n + h : ℕ) : ℝ))) * star (eUnit (f (a + (n : ℝ))))‖ ≤
          4 * Ck * α ^ 2 * (N : ℝ) ^ 2 * (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := by
        calc 4 * (N : ℝ) / (H : ℝ) *
              ∑ h ∈ Icc 1 (H - 1),
                ‖∑ n ∈ Icc 1 (N - h),
                  eUnit (f (a + ((n + h : ℕ) : ℝ))) * star (eUnit (f (a + (n : ℝ))))‖
            ≤ 4 * (N : ℝ) / (H : ℝ) *
              ((H : ℝ) * (Ck * α * (N : ℝ) * (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)))) :=
              mul_le_mul_of_nonneg_left hsum_le (by positivity)
          _ = 4 * Ck * α * (N : ℝ) ^ 2 * (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := by
              field_simp [hHpos.ne']
          _ ≤ 4 * Ck * α ^ 2 * (N : ℝ) ^ 2 * (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := by
              have : 0 ≤ 4 * Ck * (N : ℝ) ^ 2 * (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := by positivity
              nlinarith
      linarith
    have hsqrt_le : Real.sqrt (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) ≤
        lam ^ vdcA (k + 1) + (N : ℝ) ^ (-vdcC (k + 1)) * lam ^ (-vdcD (k + 1)) := by
      have ht1 : Real.sqrt (lam ^ eH) = lam ^ vdcA (k + 1) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlam0.le, ← h2A]; congr 1; ring
      have ht2 : Real.sqrt ((N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) =
          (N : ℝ) ^ (-vdcC (k + 1)) * lam ^ (-vdcD (k + 1)) := by
        rw [Real.sqrt_mul (Real.rpow_nonneg hNpos.le _), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
          ← Real.rpow_mul hNpos.le, ← Real.rpow_mul hlam0.le, vdcC_succ hk, vdcD_succ hk]
        congr 1 <;> congr 1 <;> ring
      rw [← ht1, ← ht2]
      have hnn1 : 0 ≤ Real.sqrt (lam ^ eH) := Real.sqrt_nonneg _
      have hnn2 : 0 ≤ Real.sqrt ((N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := Real.sqrt_nonneg _
      rw [Real.sqrt_le_left (by positivity)]
      rw [add_sq, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      nlinarith
    have hnorm_le : ‖∑ n ∈ Icc 1 N, eUnit (f (a + (n : ℝ)))‖ ≤
        Real.sqrt (4 + 4 * Ck) * α * (N : ℝ) *
          (lam ^ vdcA (k + 1) + (N : ℝ) ^ (-vdcC (k + 1)) * lam ^ (-vdcD (k + 1))) := by
      have h1 := Real.sqrt_le_sqrt hsq_bd
      rw [Real.sqrt_sq (norm_nonneg _)] at h1
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith), Real.sqrt_sq hNpos.le] at h1
      calc ‖∑ n ∈ Icc 1 N, eUnit (f (a + (n : ℝ)))‖
          ≤ Real.sqrt (4 + 4 * Ck) * α * (N : ℝ) *
              Real.sqrt (lam ^ eH + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := h1
        _ ≤ Real.sqrt (4 + 4 * Ck) * α * (N : ℝ) *
              (lam ^ vdcA (k + 1) + (N : ℝ) ^ (-vdcC (k + 1)) * lam ^ (-vdcD (k + 1))) :=
            mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
    have hnn : 0 ≤ α * (N : ℝ) * (lam ^ vdcA (k + 1) + (N : ℝ) ^ (-vdcC (k + 1)) * lam ^ (-vdcD (k + 1))) := by
      positivity
    nlinarith
lemma vdc_kth_deriv_abs {k : ℕ} (hk : 2 ≤ k) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {N : ℕ}, 1 ≤ N → ∀ {a lam α : ℝ}, 0 < lam → lam ≤ 1 → 1 ≤ α →
        ∀ {f : ℝ → ℝ}, (∀ x ∈ Set.Icc a (a + (N : ℝ) + 1), ContDiffAt ℝ k f x) →
        ((∀ x ∈ Set.Icc a (a + (N : ℝ) + 1), lam ≤ iteratedDeriv k f x ∧ iteratedDeriv k f x ≤ α * lam) ∨
         (∀ x ∈ Set.Icc a (a + (N : ℝ) + 1), lam ≤ -(iteratedDeriv k f x) ∧ -(iteratedDeriv k f x) ≤ α * lam)) →
        ‖∑ n ∈ Icc 1 N, eUnit (f (a + (n : ℝ)))‖ ≤
          C * α * (N : ℝ) * (lam ^ vdcA k + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := by
  obtain ⟨C, hC1, hpos⟩ := vdc_kth_deriv k hk
  refine ⟨C, hC1, ?_⟩
  intro N hN a lam α hlam0 hlam1 hα f hf hsign
  rcases hsign with hp | hn
  · exact hpos hN hlam0 hlam1 hα hf hp
  · have hneg_cd : ∀ x ∈ Set.Icc a (a + (N : ℝ) + 1), ContDiffAt ℝ k (fun y => -f y) x :=
      fun x hx => (hf x hx).neg
    have hneg_bd : ∀ x ∈ Set.Icc a (a + (N : ℝ) + 1),
        lam ≤ iteratedDeriv k (fun y => -f y) x ∧ iteratedDeriv k (fun y => -f y) x ≤ α * lam := by
      intro x hx
      have hnd : iteratedDeriv k (fun y => -f y) x = -(iteratedDeriv k f x) := iteratedDeriv_neg k f x
      rw [hnd]
      exact hn x hx
    have hres := hpos hN hlam0 hlam1 hα hneg_cd hneg_bd
    have hstar : ‖∑ n ∈ Icc 1 N, eUnit (f (a + (n : ℝ)))‖ =
        ‖∑ n ∈ Icc 1 N, eUnit (-f (a + (n : ℝ)))‖ := by
      have : ∑ n ∈ Icc 1 N, eUnit (-f (a + (n : ℝ))) =
          star (∑ n ∈ Icc 1 N, eUnit (f (a + (n : ℝ)))) := by
        rw [Complex.star_def, map_sum (starRingEnd ℂ)]
        refine sum_congr rfl fun n _ => eUnit_neg _
      rw [this, norm_star]
    rw [hstar]
    exact hres
lemma iteratedDeriv_log_affine (k : ℕ) (hk : 1 ≤ k) {q r x : ℝ} (hq : 0 < q) (hpos : 0 < q * x + r) :
    iteratedDeriv k (fun y : ℝ => Real.log (q * y + r)) x =
      (-1 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * q ^ k * (q * x + r) ^ (-(k : ℤ)) := by
  induction k, hk using Nat.le_induction generalizing x with
  | base =>
    simp only [iteratedDeriv_one, Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one,
      one_mul, pow_one, zpow_neg_one]
    have hd : HasDerivAt (fun y : ℝ => Real.log (q * y + r)) (q / (q * x + r)) x := by
      have h1 : HasDerivAt (fun y : ℝ => q * y + r) q x := by
        simpa using ((hasDerivAt_id x).const_mul q).add_const r
      exact h1.log hpos.ne'
    rw [hd.deriv, div_eq_mul_inv]
  | succ k hk ih =>
    rw [iteratedDeriv_succ]
    have hev : (iteratedDeriv k (fun y : ℝ => Real.log (q * y + r))) =ᶠ[𝓝 x]
        (fun y : ℝ => (-1 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * q ^ k * (q * y + r) ^ (-(k : ℤ))) := by
      have hopen : IsOpen {y : ℝ | 0 < q * y + r} := isOpen_lt continuous_const (by fun_prop)
      filter_upwards [hopen.mem_nhds hpos] with y hy
      exact ih hy
    rw [hev.deriv_eq]
    have hpow : HasDerivAt (fun y : ℝ => (q * y + r) ^ (-(k : ℤ)))
        (((-(k : ℤ) : ℤ) : ℝ) * (q * x + r) ^ (-(k : ℤ) - 1) * q) x := by
      have h1 : HasDerivAt (fun y : ℝ => q * y + r) q x := by
        simpa using ((hasDerivAt_id x).const_mul q).add_const r
      exact (hasDerivAt_zpow (-(k : ℤ)) (q * x + r) (Or.inl hpos.ne')).comp x h1
    have hfull := hpow.const_mul ((-1 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * q ^ k)
    rw [hfull.deriv]
    have hfac : ((k : ℕ).factorial : ℝ) = (k : ℝ) * ((k - 1).factorial : ℝ) := by
      cases k with
      | zero => omega
      | succ m =>
        simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
    have hsub : k + 1 - 1 = k := by omega
    have hpow_neg : (-1 : ℝ) ^ k = (-1 : ℝ) ^ (k - 1) * (-1 : ℝ) := by
      cases k with
      | zero => omega
      | succ m => simp [pow_succ]
    have hzpow : -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) := by omega
    rw [hsub, hzpow, hfac, hpow_neg, pow_succ]
    push_cast
    ring
lemma contDiffAt_log_affine (k : ℕ) {q r x : ℝ} (hpos : 0 < q * x + r) :
    ContDiffAt ℝ k (fun y : ℝ => Real.log (q * y + r)) x := by
  have h1 : ContDiffAt ℝ k (fun y : ℝ => q * y + r) x :=
    (contDiffAt_const.mul contDiffAt_id).add contDiffAt_const
  exact (Real.contDiffAt_log.mpr hpos.ne').comp x h1
lemma exp_sum_ap_bound {k : ℕ} (hk : 2 ≤ k) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {q : ℕ}, 1 ≤ q → ∀ {r : ℕ}, 1 ≤ r → r ≤ q →
      ∀ {A N : ℕ}, 1 ≤ N → q ≤ A → N ≤ A →
      ∀ {T : ℝ}, 1 ≤ |T| →
      ((k - 1).factorial : ℝ) * |T| * (q : ℝ) ^ k / (2 * Real.pi * ((q : ℝ) * (A : ℝ)) ^ k) ≤ 1 →
      ‖∑ m ∈ Icc 1 N,
        (((q * (A + m) + r : ℕ) : ℂ) ^ (-(Complex.I * (T : ℂ))))‖ ≤
        C * (A : ℝ) *
          ((((k - 1).factorial : ℝ) * |T| / ((A : ℝ) ^ k)) ^ vdcA k +
           (A : ℝ) ^ (-vdcC k) * (((k - 1).factorial : ℝ) * |T| / ((A : ℝ) ^ k)) ^ (-vdcD k)) := by
  obtain ⟨C0, hC0, hvdc⟩ := vdc_kth_deriv_abs hk
  refine ⟨C0 * (5 : ℝ) ^ k * (5 : ℝ) ^ ((k : ℝ) * vdcD k) * (2 * Real.pi) ^ vdcD k + 1, by
    have : 0 ≤ C0 * (5 : ℝ) ^ k * (5 : ℝ) ^ ((k : ℝ) * vdcD k) * (2 * Real.pi) ^ vdcD k := by
      have : 0 < vdcD k := by unfold vdcD; positivity
      positivity
    linarith, ?_⟩
  intro q hq r hr1 hrq A N hN hqA hNA T hT1 hlam_top
  have hN2A : N ≤ 2 * A := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (by omega : 0 < A)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hTpos : 0 < |T| := by linarith
  let f : ℝ → ℝ := fun x => -(T / (2 * Real.pi)) * Real.log ((q : ℝ) * x + (r : ℝ))
  have hsum_eq : ∑ m ∈ Icc 1 N, (((q * (A + m) + r : ℕ) : ℂ) ^ (-(Complex.I * (T : ℂ)))) =
      ∑ m ∈ Icc 1 N, eUnit (f ((A : ℝ) + (m : ℝ))) := by
    refine sum_congr rfl fun m _ => ?_
    have hpos_m : (0 : ℝ) < ((q * (A + m) + r : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < q * (A + m) + r)
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos_m.ne')]
    unfold eUnit f
    have hlog : Complex.log (((q * (A + m) + r : ℕ) : ℂ)) =
        (Real.log ((q : ℝ) * ((A : ℝ) + (m : ℝ)) + (r : ℝ)) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hpos_m.le]
      congr 1; push_cast; ring
    rw [hlog]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    push_cast
    field_simp [hpi]
  rw [hsum_eq]
  have hcd : ∀ x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (N : ℝ) + 1), ContDiffAt ℝ k f x := by
    intro x hx
    have hpx : 0 < (q : ℝ) * x + (r : ℝ) := by
      have : (0 : ℝ) ≤ (q : ℝ) * x := by nlinarith [hx.1]
      have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
      linarith
    exact contDiffAt_const.mul (contDiffAt_log_affine k hpx)
  let lam : ℝ := ((k - 1).factorial : ℝ) * |T| * (q : ℝ) ^ k / (2 * Real.pi * (5 * (q : ℝ) * (A : ℝ)) ^ k)
  let α : ℝ := (5 : ℝ) ^ k
  have hlam0 : 0 < lam := by
    have : 0 < ((k - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (k - 1)
    positivity
  have hlam_eq : α * lam = ((k - 1).factorial : ℝ) * |T| * (q : ℝ) ^ k / (2 * Real.pi * ((q : ℝ) * (A : ℝ)) ^ k) := by
    dsimp [α, lam]
    have h5 : (5 * (q : ℝ) * (A : ℝ)) ^ k = (5 : ℝ) ^ k * ((q : ℝ) * (A : ℝ)) ^ k := by
      rw [mul_assoc, mul_pow]
    rw [h5]
    have h5ne : (5 : ℝ) ^ k ≠ 0 := by positivity
    field_simp [h5ne]
  have hα : 1 ≤ α := one_le_pow₀ (by norm_num)
  have hlam1 : lam ≤ 1 := by
    have h1 : lam ≤ α * lam := le_mul_of_one_le_left hlam0.le hα
    linarith [hlam_eq]
  have hderiv_abs : ∀ x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (N : ℝ) + 1),
      iteratedDeriv k f x =
        (-1 : ℝ) ^ k * (T / (2 * Real.pi)) * ((k - 1).factorial : ℝ) * (q : ℝ) ^ k *
          ((q : ℝ) * x + (r : ℝ)) ^ (-(k : ℤ)) := by
    intro x hx
    have hpx : 0 < (q : ℝ) * x + (r : ℝ) := by
      have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
      nlinarith [hx.1]
    dsimp [f]
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_log_affine k (by omega) hqpos hpx]
    have hneg : -(T / (2 * Real.pi)) * ((-1 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * (q : ℝ) ^ k *
        ((q : ℝ) * x + (r : ℝ)) ^ (-(k : ℤ))) =
        (-1 : ℝ) ^ k * (T / (2 * Real.pi)) * ((k - 1).factorial : ℝ) * (q : ℝ) ^ k *
          ((q : ℝ) * x + (r : ℝ)) ^ (-(k : ℤ)) := by
      have hp : (-1 : ℝ) ^ k = -((-1 : ℝ) ^ (k - 1)) := by
        cases k with
        | zero => omega
        | succ m => simp [pow_succ]
      rw [hp]; ring
    exact hneg
  have hrange : ∀ x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (N : ℝ) + 1),
      (q : ℝ) * (A : ℝ) ≤ (q : ℝ) * x + (r : ℝ) ∧
      (q : ℝ) * x + (r : ℝ) ≤ 5 * (q : ℝ) * (A : ℝ) := by
    intro x hx
    have hr_le : (r : ℝ) ≤ (q : ℝ) := by exact_mod_cast hrq
    have hN_le : (N : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hN2A
    have h1_le : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast (by omega : 1 ≤ A)
    constructor
    · have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
      nlinarith [hx.1]
    · nlinarith [hx.2]
  have hsign : (∀ x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (N : ℝ) + 1),
      lam ≤ iteratedDeriv k f x ∧ iteratedDeriv k f x ≤ α * lam) ∨
      (∀ x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (N : ℝ) + 1),
      lam ≤ -(iteratedDeriv k f x) ∧ -(iteratedDeriv k f x) ≤ α * lam) := by
    have hmag : ∀ x ∈ Set.Icc (A : ℝ) ((A : ℝ) + (N : ℝ) + 1),
        lam ≤ |iteratedDeriv k f x| ∧ |iteratedDeriv k f x| ≤ α * lam := by
      intro x hx
      rw [hderiv_abs x hx]
      have hrx := hrange x hx
      have hpx : 0 < (q : ℝ) * x + (r : ℝ) := lt_of_lt_of_le (by positivity) hrx.1
      have habs :
          |(-1 : ℝ) ^ k * (T / (2 * Real.pi)) * ((k - 1).factorial : ℝ) * (q : ℝ) ^ k *
            ((q : ℝ) * x + (r : ℝ)) ^ (-(k : ℤ))| =
          ((k - 1).factorial : ℝ) * |T| * (q : ℝ) ^ k / (2 * Real.pi * ((q : ℝ) * x + (r : ℝ)) ^ k) := by
        have hfac_p : (0 : ℝ) < ((k - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (k - 1)
        have hqk_p : (0 : ℝ) < (q : ℝ) ^ k := by positivity
        have h2pi_p : (0 : ℝ) < 2 * Real.pi := by positivity
        have hzpow_p : (0 : ℝ) < ((q : ℝ) * x + (r : ℝ)) ^ (-(k : ℤ)) := zpow_pos hpx _
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_div, abs_of_pos h2pi_p, abs_of_pos hfac_p, abs_of_pos hqk_p, abs_of_pos hzpow_p,
          zpow_neg, zpow_natCast]
        ring
      rw [habs, hlam_eq]
      dsimp [lam]
      have hpow_lo : ((q : ℝ) * (A : ℝ)) ^ k ≤ ((q : ℝ) * x + (r : ℝ)) ^ k :=
        pow_le_pow_left₀ (by positivity) hrx.1 k
      have hpow_hi : ((q : ℝ) * x + (r : ℝ)) ^ k ≤ (5 * (q : ℝ) * (A : ℝ)) ^ k :=
        pow_le_pow_left₀ hpx.le hrx.2 k
      constructor
      · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
      · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
    by_cases hpos_s : 0 ≤ (-1 : ℝ) ^ k * T
    · left
      intro x hx
      have hrx := hrange x hx
      have hpx : 0 < (q : ℝ) * x + (r : ℝ) := lt_of_lt_of_le (by positivity) hrx.1
      have hnn : 0 ≤ iteratedDeriv k f x := by
        rw [hderiv_abs x hx]
        have hfac : 0 ≤ ((k - 1).factorial : ℝ) := Nat.cast_nonneg _
        have h1 : (-1 : ℝ) ^ k * (T / (2 * Real.pi)) * ((k - 1).factorial : ℝ) * (q : ℝ) ^ k *
            ((q : ℝ) * x + (r : ℝ)) ^ (-(k : ℤ)) =
            ((-1 : ℝ) ^ k * T) * (((k - 1).factorial : ℝ) * (q : ℝ) ^ k *
              ((q : ℝ) * x + (r : ℝ)) ^ (-(k : ℤ)) / (2 * Real.pi)) := by ring
        rw [h1]
        exact mul_nonneg hpos_s (by positivity)
      simpa [abs_of_nonneg hnn] using hmag x hx
    · right
      push Not at hpos_s
      intro x hx
      have hrx := hrange x hx
      have hpx : 0 < (q : ℝ) * x + (r : ℝ) := lt_of_lt_of_le (by positivity) hrx.1
      have hnp : iteratedDeriv k f x ≤ 0 := by
        rw [hderiv_abs x hx]
        have h1 : (-1 : ℝ) ^ k * (T / (2 * Real.pi)) * ((k - 1).factorial : ℝ) * (q : ℝ) ^ k *
            ((q : ℝ) * x + (r : ℝ)) ^ (-(k : ℤ)) =
            ((-1 : ℝ) ^ k * T) * (((k - 1).factorial : ℝ) * (q : ℝ) ^ k *
              ((q : ℝ) * x + (r : ℝ)) ^ (-(k : ℤ)) / (2 * Real.pi)) := by ring
        rw [h1]
        exact mul_nonpos_of_nonpos_of_nonneg hpos_s.le (by positivity)
      simpa [abs_of_nonpos hnp] using hmag x hx
  have hres := hvdc hN hlam0 hlam1 hα hcd hsign
  let Mval : ℝ := ((k - 1).factorial : ℝ) * |T| / (A : ℝ) ^ k
  have hMpos : 0 < Mval := by
    have : 0 < ((k - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (k - 1)
    positivity
  have hlam_simp : lam = Mval / (2 * Real.pi * (5 : ℝ) ^ k) := by
    dsimp [lam, Mval]
    have h5 : (5 * (q : ℝ) * (A : ℝ)) ^ k = (5 : ℝ) ^ k * (q : ℝ) ^ k * (A : ℝ) ^ k := by
      rw [mul_pow, mul_pow]
    rw [h5]
    have hqne : (q : ℝ) ^ k ≠ 0 := by positivity
    field_simp [hqne]
  have hden_ge1 : 1 ≤ 2 * Real.pi * (5 : ℝ) ^ k := by
    have h1 : 1 ≤ (5 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    nlinarith [Real.pi_gt_three]
  have hlam_le_M : lam ≤ Mval := by
    rw [hlam_simp]; exact div_le_self hMpos.le hden_ge1
  have hA_term : lam ^ vdcA k ≤ Mval ^ vdcA k :=
    Real.rpow_le_rpow hlam0.le hlam_le_M (vdcA_pos hk).le
  have hD_term : lam ^ (-vdcD k) = (2 * Real.pi) ^ vdcD k * (5 : ℝ) ^ ((k : ℝ) * vdcD k) * Mval ^ (-vdcD k) := by
    rw [hlam_simp, Real.div_rpow hMpos.le (by positivity), Real.rpow_neg hMpos.le,
      Real.rpow_neg (by positivity), div_inv_eq_mul]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (5 : ℝ) k,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
    ring
  have hfactor_ge1 : 1 ≤ (2 * Real.pi) ^ vdcD k * (5 : ℝ) ^ ((k : ℝ) * vdcD k) := by
    have hd_pos : 0 < vdcD k := by unfold vdcD; positivity
    have h1 : 1 ≤ (2 * Real.pi) ^ vdcD k := Real.one_le_rpow (by linarith [Real.pi_gt_three]) hd_pos.le
    have h2 : 1 ≤ (5 : ℝ) ^ ((k : ℝ) * vdcD k) := Real.one_le_rpow (by norm_num) (by positivity)
    nlinarith
  have hcombine : lam ^ vdcA k + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k) ≤
      (2 * Real.pi) ^ vdcD k * (5 : ℝ) ^ ((k : ℝ) * vdcD k) *
        (Mval ^ vdcA k + (N : ℝ) ^ (-vdcC k) * Mval ^ (-vdcD k)) := by
    rw [hD_term]
    have h1 : lam ^ vdcA k ≤ (2 * Real.pi) ^ vdcD k * (5 : ℝ) ^ ((k : ℝ) * vdcD k) * Mval ^ vdcA k :=
      hA_term.trans (le_mul_of_one_le_left (Real.rpow_nonneg hMpos.le _) hfactor_ge1)
    linarith
  have hN_le_A : (N : ℝ) ≤ (A : ℝ) := by exact_mod_cast hNA
  have h1ck : 0 ≤ 1 - vdcC k := by linarith [vdcC_le_one hk]
  have hN_mon : (N : ℝ) * (Mval ^ vdcA k + (N : ℝ) ^ (-vdcC k) * Mval ^ (-vdcD k)) ≤
      (A : ℝ) * (Mval ^ vdcA k + (A : ℝ) ^ (-vdcC k) * Mval ^ (-vdcD k)) := by
    have h1 : (N : ℝ) * Mval ^ vdcA k ≤ (A : ℝ) * Mval ^ vdcA k :=
      mul_le_mul_of_nonneg_right hN_le_A (Real.rpow_nonneg hMpos.le _)
    have hNpow : (N : ℝ) * (N : ℝ) ^ (-vdcC k) = (N : ℝ) ^ (1 - vdcC k) := by
      calc (N : ℝ) * (N : ℝ) ^ (-vdcC k)
          = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-vdcC k) := by rw [Real.rpow_one]
        _ = (N : ℝ) ^ (1 + -vdcC k) := (Real.rpow_add hNpos _ _).symm
        _ = (N : ℝ) ^ (1 - vdcC k) := by rw [sub_eq_add_neg]
    have hApow : (A : ℝ) * (A : ℝ) ^ (-vdcC k) = (A : ℝ) ^ (1 - vdcC k) := by
      calc (A : ℝ) * (A : ℝ) ^ (-vdcC k)
          = (A : ℝ) ^ (1 : ℝ) * (A : ℝ) ^ (-vdcC k) := by rw [Real.rpow_one]
        _ = (A : ℝ) ^ (1 + -vdcC k) := (Real.rpow_add hApos _ _).symm
        _ = (A : ℝ) ^ (1 - vdcC k) := by rw [sub_eq_add_neg]
    have h2 : (N : ℝ) * ((N : ℝ) ^ (-vdcC k) * Mval ^ (-vdcD k)) ≤
        (A : ℝ) * ((A : ℝ) ^ (-vdcC k) * Mval ^ (-vdcD k)) := by
      calc (N : ℝ) * ((N : ℝ) ^ (-vdcC k) * Mval ^ (-vdcD k))
          = ((N : ℝ) * (N : ℝ) ^ (-vdcC k)) * Mval ^ (-vdcD k) := by ring
        _ = (N : ℝ) ^ (1 - vdcC k) * Mval ^ (-vdcD k) := by rw [hNpow]
        _ ≤ (A : ℝ) ^ (1 - vdcC k) * Mval ^ (-vdcD k) :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hNpos.le hN_le_A h1ck)
              (Real.rpow_nonneg hMpos.le _)
        _ = (A : ℝ) * ((A : ℝ) ^ (-vdcC k) * Mval ^ (-vdcD k)) := by rw [← hApow]; ring
    linarith
  calc ‖∑ m ∈ Icc 1 N, eUnit (f ((A : ℝ) + (m : ℝ)))‖
      ≤ C0 * α * (N : ℝ) * (lam ^ vdcA k + (N : ℝ) ^ (-vdcC k) * lam ^ (-vdcD k)) := hres
    _ ≤ C0 * α * (N : ℝ) * ((2 * Real.pi) ^ vdcD k * (5 : ℝ) ^ ((k : ℝ) * vdcD k) *
          (Mval ^ vdcA k + (N : ℝ) ^ (-vdcC k) * Mval ^ (-vdcD k))) :=
        mul_le_mul_of_nonneg_left hcombine (by positivity)
    _ = (C0 * (5 : ℝ) ^ k * (5 : ℝ) ^ ((k : ℝ) * vdcD k) * (2 * Real.pi) ^ vdcD k) *
          ((N : ℝ) * (Mval ^ vdcA k + (N : ℝ) ^ (-vdcC k) * Mval ^ (-vdcD k))) := by
        dsimp [α]; ring
    _ ≤ (C0 * (5 : ℝ) ^ k * (5 : ℝ) ^ ((k : ℝ) * vdcD k) * (2 * Real.pi) ^ vdcD k) *
          ((A : ℝ) * (Mval ^ vdcA k + (A : ℝ) ^ (-vdcC k) * Mval ^ (-vdcD k))) :=
        mul_le_mul_of_nonneg_left hN_mon (by positivity)
    _ ≤ (C0 * (5 : ℝ) ^ k * (5 : ℝ) ^ ((k : ℝ) * vdcD k) * (2 * Real.pi) ^ vdcD k + 1) * (A : ℝ) *
          (Mval ^ vdcA k + (A : ℝ) ^ (-vdcC k) * Mval ^ (-vdcD k)) := by
        have hnn : 0 ≤ (A : ℝ) * (Mval ^ vdcA k + (A : ℝ) ^ (-vdcC k) * Mval ^ (-vdcD k)) := by positivity
        nlinarith
lemma abel_sum_decreasing_weight {N : ℕ} (hN : 1 ≤ N) {c : ℕ → ℂ} {w : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hw_nn : ∀ n, 1 ≤ n → n ≤ N → 0 ≤ w n)
    (hw_anti : ∀ n, 1 ≤ n → n + 1 ≤ N → w (n + 1) ≤ w n)
    (hpart : ∀ m, 1 ≤ m → m ≤ N → ‖∑ n ∈ Icc 1 m, c n‖ ≤ B) :
    ‖∑ n ∈ Icc 1 N, c n * (w n : ℂ)‖ ≤ w 1 * B := by
  let S : ℕ → ℂ := fun m => ∑ n ∈ Icc 1 m, c n
  have habel : ∑ n ∈ Icc 1 N, c n * (w n : ℂ) =
      S N * (w N : ℂ) + ∑ m ∈ Icc 1 (N - 1), S m * ((w m - w (m + 1) : ℝ) : ℂ) := by
    clear hw_nn hw_anti hpart
    induction N, hN using Nat.le_induction with
    | base => simp [S]
    | succ M hM ih =>
      have h1 : Icc 1 (M + 1) = insert (M + 1) (Icc 1 M) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      have h2 : Icc 1 (M + 1 - 1) = insert M (Icc 1 (M - 1)) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      rw [h1, sum_insert (by simp), ih, h2, sum_insert (by simp; omega)]
      have hSM : S (M + 1) = S M + c (M + 1) := by
        dsimp [S]; rw [h1, sum_insert (by simp), add_comm]
      rw [hSM]
      push_cast
      ring
  rw [habel]
  have htele : w N + ∑ m ∈ Icc 1 (N - 1), (w m - w (m + 1)) = w 1 := by
    clear hw_nn hw_anti hpart habel
    induction N, hN using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      have h2 : Icc 1 (M + 1 - 1) = insert M (Icc 1 (M - 1)) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      rw [h2, sum_insert (by simp; omega)]
      linarith
  calc ‖S N * (w N : ℂ) + ∑ m ∈ Icc 1 (N - 1), S m * ((w m - w (m + 1) : ℝ) : ℂ)‖
      ≤ ‖S N * (w N : ℂ)‖ + ‖∑ m ∈ Icc 1 (N - 1), S m * ((w m - w (m + 1) : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ ‖S N‖ * w N + ∑ m ∈ Icc 1 (N - 1), ‖S m * ((w m - w (m + 1) : ℝ) : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw_nn N hN le_rfl)]
        gcongr; exact norm_sum_le _ _
    _ ≤ B * w N + ∑ m ∈ Icc 1 (N - 1), B * (w m - w (m + 1)) := by
        have h1 : ‖S N‖ * w N ≤ B * w N :=
          mul_le_mul_of_nonneg_right (hpart N hN le_rfl) (hw_nn N hN le_rfl)
        have h2 : ∑ m ∈ Icc 1 (N - 1), ‖S m * ((w m - w (m + 1) : ℝ) : ℂ)‖ ≤
            ∑ m ∈ Icc 1 (N - 1), B * (w m - w (m + 1)) := by
          refine sum_le_sum fun m hm => ?_
          rw [mem_Icc] at hm
          have hdiff : 0 ≤ w m - w (m + 1) := sub_nonneg.mpr (hw_anti m hm.1 (by omega))
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hdiff]
          exact mul_le_mul_of_nonneg_right (hpart m hm.1 (by omega)) hdiff
        linarith
    _ = B * (w N + ∑ m ∈ Icc 1 (N - 1), (w m - w (m + 1))) := by
        rw [← mul_sum]; ring
    _ = w 1 * B := by rw [htele, mul_comm]
lemma cpow_norm_natCast {n : ℕ} (hn : 1 ≤ n) (σ T : ℝ) :
    ‖(n : ℂ) ^ (-(σ + Complex.I * T))‖ = (n : ℝ) ^ (-σ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]
  congr 1
  simp
lemma summable_natCast_cpow {σ T : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => if n = 0 then (0 : ℂ) else (n : ℂ) ^ (-(σ + Complex.I * T))) := by
  refine Summable.of_norm ?_
  have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
    simpa [Real.rpow_neg (Nat.cast_nonneg _)] using (Real.summable_nat_rpow_inv.mpr hσ)
  refine h1.congr fun n => ?_
  by_cases hn : n = 0
  · subst hn
    simp [Real.zero_rpow (by linarith : -σ ≠ 0)]
  · rw [if_neg hn, cpow_norm_natCast (by omega)]
lemma dirichlet_norm_eq_one_of_isUnit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ZMod q} (hx : IsUnit x) : ‖χ x‖ = 1 := by
  obtain ⟨u, rfl⟩ := hx
  have hord : u ^ Fintype.card (ZMod q)ˣ = 1 := pow_card_eq_one
  have h1 : χ (u : ZMod q) ^ Fintype.card (ZMod q)ˣ = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hord, Units.val_one, map_one]
  have h2 : ‖χ (u : ZMod q)‖ ^ Fintype.card (ZMod q)ˣ = 1 := by
    rw [← norm_pow, h1, norm_one]
  have hpos : 0 < Fintype.card (ZMod q)ˣ := Fintype.card_pos
  have hnn : 0 ≤ ‖χ (u : ZMod q)‖ := norm_nonneg _
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : ‖χ (u : ZMod q)‖ ^ Fintype.card (ZMod q)ˣ < 1 ^ Fintype.card (ZMod q)ˣ :=
      pow_lt_pow_left₀ hlt hnn hpos.ne'
    rw [one_pow] at this; linarith
  · have : (1 : ℝ) ^ Fintype.card (ZMod q)ˣ < ‖χ (u : ZMod q)‖ ^ Fintype.card (ZMod q)ˣ :=
      pow_lt_pow_left₀ hgt (by norm_num) hpos.ne'
    rw [one_pow] at this; linarith
lemma dirichlet_norm_le_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ZMod q) :
    ‖χ x‖ ≤ 1 := by
  by_cases hu : IsUnit x
  · exact (dirichlet_norm_eq_one_of_isUnit χ hu).le
  · rw [MulChar.map_nonunit _ hu, norm_zero]; norm_num
lemma summable_dirichlet_cpow {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ T : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => if n = 0 then (0 : ℂ) else χ (n : ZMod q) * (n : ℂ) ^ (-(σ + Complex.I * T))) := by
  refine (summable_natCast_cpow (T := T) hσ).norm.of_norm_bounded fun n => ?_
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, if_neg hn, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (dirichlet_norm_le_one χ (n : ZMod q))
lemma tail_ap_bound {q r M : ℕ} (hq : 1 ≤ q) (hr1 : 1 ≤ r) (hrq : r ≤ q) (hM : 1 ≤ M)
    {σ T : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) (hT : 1 ≤ |T|) :
    ‖∑' m : ℕ, (((q * (M + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T)))‖ ≤
      1 / ((q : ℝ) * |T|) + 2 * (2 + |T|) / ((q : ℝ) * (M : ℝ)) := by
  let s : ℂ := (σ : ℂ) + Complex.I * (T : ℂ)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hTpos : 0 < |T| := by linarith
  have hs_norm : ‖s‖ ≤ 2 + |T| := by
    calc ‖(σ : ℂ) + Complex.I * (T : ℂ)‖ ≤ ‖(σ : ℂ)‖ + ‖Complex.I * (T : ℂ)‖ := norm_add_le _ _
      _ = |σ| + |T| := by simp [Complex.norm_real]
      _ ≤ 2 + |T| := by rw [abs_of_pos (by linarith)]; linarith
  have hs1_ge : |T| ≤ ‖s - 1‖ := by
    have him : (s - 1).im = T := by simp [s]
    calc |T| = |(s - 1).im| := by rw [him]
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hs1_ne : s - 1 ≠ 0 := by
    intro h; rw [h, norm_zero] at hs1_ge; linarith
  let x : ℕ → ℝ := fun m => (q : ℝ) * ((M + m : ℕ) : ℝ) + (r : ℝ)
  have hx_pos : ∀ m, 0 < x m := fun m => by dsimp [x]; positivity
  have hx_ge : ∀ m, (q : ℝ) * ((M + m : ℕ) : ℝ) ≤ x m := fun m => by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) r]
  have hx_succ : ∀ m, x (m + 1) = x m + (q : ℝ) := fun m => by dsimp [x]; push_cast; ring
  have hint_step : ∀ m : ℕ,
      ∫ u in (x m)..(x (m + 1)), (u : ℂ) ^ (-s) =
        ((x m : ℂ) ^ (1 - s) - (x (m + 1) : ℂ) ^ (1 - s)) / (s - 1) := by
    intro m
    have hderiv : ∀ u ∈ Set.uIcc (x m) (x (m + 1)),
        HasDerivAt (fun t : ℝ => -((t : ℂ) ^ (1 - s)) / (s - 1)) ((u : ℂ) ^ (-s)) u := by
      intro u hu
      have hu_pos : 0 < u := by
        rw [Set.uIcc_of_le (by rw [hx_succ]; linarith)] at hu
        exact lt_of_lt_of_le (hx_pos m) hu.1
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (1 - s)) ((1 - s) * (u : ℂ) ^ (1 - s - 1)) u := by
        have hcp := (Complex.hasStrictDerivAt_cpow_const (c := 1 - s) (x := (u : ℂ)) (by
          left; simp [hu_pos])).hasDerivAt
        exact hcp.comp_ofReal
      have h2 := (h1.neg).div_const (s - 1)
      have hderiv_val : -((1 - s) * (u : ℂ) ^ (1 - s - 1)) / (s - 1) = (u : ℂ) ^ (-s) := by
        rw [show (1 - s - 1 : ℂ) = -s by ring]
        field_simp [hs1_ne]
        ring
      exact hderiv_val ▸ h2
    have hint_c : IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (-s)) volume (x m) (x (m + 1)) := by
      refine ContinuousOn.intervalIntegrable ?_
      intro u hu
      have hu_pos : 0 < u := by
        rw [Set.uIcc_of_le (by rw [hx_succ]; linarith)] at hu
        exact lt_of_lt_of_le (hx_pos m) hu.1
      have hcp : ContinuousAt (fun z : ℂ => z ^ (-s)) (u : ℂ) :=
        continuousAt_cpow_const (Or.inl (by simp [hu_pos]))
      exact (hcp.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_c]
    ring
  have herr_step : ∀ m : ℕ,
      ‖(x m : ℂ) ^ (-s) - (1 / (q : ℂ)) * ∫ u in (x m)..(x (m + 1)), (u : ℂ) ^ (-s)‖ ≤
        ‖s‖ * (q : ℝ) * (x m) ^ (-σ - 1) := by
    intro m
    have hconst : (x m : ℂ) ^ (-s) = (1 / (q : ℂ)) * ∫ _u in (x m)..(x (m + 1)), (x m : ℂ) ^ (-s) := by
      rw [intervalIntegral.integral_const, hx_succ]
      simp only [add_sub_cancel_left, Complex.real_smul, Complex.ofReal_natCast]
      have hqne : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
      field_simp [hqne]
    have hint1 : IntervalIntegrable (fun _u : ℝ => (x m : ℂ) ^ (-s)) volume (x m) (x (m + 1)) :=
      intervalIntegrable_const
    have hint2 : IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (-s)) volume (x m) (x (m + 1)) := by
      refine ContinuousOn.intervalIntegrable ?_
      intro u hu
      have hu_pos : 0 < u := by
        rw [Set.uIcc_of_le (by rw [hx_succ]; linarith)] at hu
        exact lt_of_lt_of_le (hx_pos m) hu.1
      have hcp : ContinuousAt (fun z : ℂ => z ^ (-s)) (u : ℂ) :=
        continuousAt_cpow_const (Or.inl (by simp [hu_pos]))
      exact (hcp.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
    rw [hconst, ← mul_sub, ← intervalIntegral.integral_sub hint1 hint2, norm_mul, one_div, norm_inv,
      Complex.norm_natCast]
    have hpt : ∀ u ∈ Set.Icc (x m) (x (m + 1)),
        ‖(x m : ℂ) ^ (-s) - (u : ℂ) ^ (-s)‖ ≤ ‖s‖ * (q : ℝ) * (x m) ^ (-σ - 1) := by
      intro u hu
      have hdiff_on : ∀ t ∈ Set.Icc (x m) u,
          HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) ((-s) * (t : ℂ) ^ (-s - 1)) t := by
        intro t ht
        have ht_pos : 0 < t := lt_of_lt_of_le (hx_pos m) ht.1
        have hcp := (Complex.hasStrictDerivAt_cpow_const (c := -s) (x := (t : ℂ)) (by left; simp [ht_pos])).hasDerivAt
        exact hcp.comp_ofReal
      have hbd : ∀ t ∈ Set.Icc (x m) u, ‖(-s) * (t : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * (x m) ^ (-σ - 1) := by
        intro t ht
        have ht_pos : 0 < t := lt_of_lt_of_le (hx_pos m) ht.1
        rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
        have hre : (-s - 1).re = -σ - 1 := by simp [s]
        rw [hre]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (hx_pos m) ht.1 (by linarith)) (norm_nonneg _)
      have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun y : ℝ => (y : ℂ) ^ (-s)) (f' := fun t : ℝ => (-s) * (t : ℂ) ^ (-s - 1))
        (s := Set.Icc (x m) u)
        (fun t ht => (hdiff_on t ht).hasDerivWithinAt)
        (fun t ht => hbd t ht)
        (convex_Icc _ _)
        ⟨le_rfl, hu.1⟩ ⟨hu.1, le_rfl⟩
      rw [norm_sub_rev] at hmvt
      have hu_sub : u - x m ≤ (q : ℝ) := by linarith [hu.2, hx_succ m]
      calc ‖(x m : ℂ) ^ (-s) - (u : ℂ) ^ (-s)‖
          ≤ ‖s‖ * (x m) ^ (-σ - 1) * ‖u - x m‖ := hmvt
        _ = ‖s‖ * (x m) ^ (-σ - 1) * (u - x m) := by rw [Real.norm_of_nonneg (sub_nonneg.mpr hu.1)]
        _ ≤ ‖s‖ * (x m) ^ (-σ - 1) * (q : ℝ) :=
            mul_le_mul_of_nonneg_left hu_sub (by positivity)
        _ = ‖s‖ * (q : ℝ) * (x m) ^ (-σ - 1) := by ring
    have hint_le := intervalIntegral.norm_integral_le_of_norm_le_const (a := x m) (b := x (m + 1))
      (f := fun u : ℝ => (x m : ℂ) ^ (-s) - (u : ℂ) ^ (-s))
      (C := ‖s‖ * (q : ℝ) * (x m) ^ (-σ - 1))
      (fun u hu => hpt u (by
        rw [Set.uIoc_of_le (by rw [hx_succ]; linarith)] at hu
        exact ⟨hu.1.le, hu.2⟩))
    have hlen : |x (m + 1) - x m| = (q : ℝ) := by
      rw [hx_succ, add_sub_cancel_left, abs_of_pos hqpos]
    rw [hlen] at hint_le
    calc (q : ℝ)⁻¹ * ‖∫ u in (x m)..(x (m + 1)), ((x m : ℂ) ^ (-s) - (u : ℂ) ^ (-s))‖
        ≤ (q : ℝ)⁻¹ * (‖s‖ * (q : ℝ) * (x m) ^ (-σ - 1) * (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hint_le (by positivity)
      _ = ‖s‖ * (q : ℝ) * (x m) ^ (-σ - 1) := by field_simp [hqpos.ne']
  have hpart : ∀ L : ℕ,
      ‖∑ m ∈ Finset.range L, (((q * (M + m) + r : ℕ) : ℂ) ^ (-s))‖ ≤
        1 / ((q : ℝ) * |T|) + ‖(x L : ℂ) ^ (1 - s)‖ / ((q : ℝ) * |T|) +
        2 * (2 + |T|) / ((q : ℝ) * (M : ℝ)) := by
    intro L
    have htele_int : ∑ m ∈ Finset.range L,
        ((1 / (q : ℂ)) * ∫ u in (x m)..(x (m + 1)), (u : ℂ) ^ (-s)) =
        ((x 0 : ℂ) ^ (1 - s) - (x L : ℂ) ^ (1 - s)) / ((q : ℂ) * (s - 1)) := by
      induction L with
      | zero => simp
      | succ L ih =>
        rw [Finset.sum_range_succ, ih, hint_step L]
        have hqne : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
        field_simp [hqne, hs1_ne]
        ring
    have hdecomp : ∑ m ∈ Finset.range L, (((q * (M + m) + r : ℕ) : ℂ) ^ (-s)) =
        ((x 0 : ℂ) ^ (1 - s) - (x L : ℂ) ^ (1 - s)) / ((q : ℂ) * (s - 1)) +
        ∑ m ∈ Finset.range L,
          ((x m : ℂ) ^ (-s) - (1 / (q : ℂ)) * ∫ u in (x m)..(x (m + 1)), (u : ℂ) ^ (-s)) := by
      rw [← htele_int, ← sum_add_distrib]
      refine sum_congr rfl fun m _ => ?_
      have hxcast : ((q * (M + m) + r : ℕ) : ℂ) = (x m : ℂ) := by dsimp [x]; push_cast; ring
      rw [hxcast]; ring
    rw [hdecomp]
    have hmain : ‖((x 0 : ℂ) ^ (1 - s) - (x L : ℂ) ^ (1 - s)) / ((q : ℂ) * (s - 1))‖ ≤
        1 / ((q : ℝ) * |T|) + ‖(x L : ℂ) ^ (1 - s)‖ / ((q : ℝ) * |T|) := by
      rw [norm_div, norm_mul, Complex.norm_natCast]
      have hx0_ge1 : 1 ≤ x 0 := by
        have : (1 : ℝ) ≤ (q : ℝ) * ((M + 0 : ℕ) : ℝ) := by
          have : 1 ≤ q * M := Nat.mul_pos (by omega) (by omega)
          exact_mod_cast this
        linarith [hx_ge 0]
      have hx0_norm : ‖(x 0 : ℂ) ^ (1 - s)‖ ≤ 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (hx_pos 0)]
        have hre : (1 - s).re = 1 - σ := by simp [s]
        rw [hre]
        exact Real.rpow_le_one_of_one_le_of_nonpos hx0_ge1 (by linarith)
      have hden_ge : (q : ℝ) * |T| ≤ (q : ℝ) * ‖s - 1‖ :=
        mul_le_mul_of_nonneg_left hs1_ge hqpos.le
      calc ‖(x 0 : ℂ) ^ (1 - s) - (x L : ℂ) ^ (1 - s)‖ / ((q : ℝ) * ‖s - 1‖)
          ≤ (‖(x 0 : ℂ) ^ (1 - s)‖ + ‖(x L : ℂ) ^ (1 - s)‖) / ((q : ℝ) * ‖s - 1‖) :=
            div_le_div_of_nonneg_right (norm_sub_le _ _) (by positivity)
        _ ≤ (1 + ‖(x L : ℂ) ^ (1 - s)‖) / ((q : ℝ) * |T|) := by
            calc (‖(x 0 : ℂ) ^ (1 - s)‖ + ‖(x L : ℂ) ^ (1 - s)‖) / ((q : ℝ) * ‖s - 1‖)
                ≤ (1 + ‖(x L : ℂ) ^ (1 - s)‖) / ((q : ℝ) * ‖s - 1‖) := by gcongr
              _ ≤ (1 + ‖(x L : ℂ) ^ (1 - s)‖) / ((q : ℝ) * |T|) :=
                  div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
        _ = 1 / ((q : ℝ) * |T|) + ‖(x L : ℂ) ^ (1 - s)‖ / ((q : ℝ) * |T|) := add_div _ _ _
    have herr_sum : ∑ m ∈ Finset.range L, ‖s‖ * (q : ℝ) * (x m) ^ (-σ - 1) ≤
        2 * (2 + |T|) / ((q : ℝ) * (M : ℝ)) := by
      have hterm : ∀ m, (x m) ^ (-σ - 1) ≤ 1 / ((q : ℝ) ^ 2 * ((M + m : ℕ) : ℝ) ^ 2) := by
        intro m
        have hqm_pos : (0 : ℝ) < (q : ℝ) * ((M + m : ℕ) : ℝ) := by
          have : 0 < q * (M + m) := Nat.mul_pos (by omega) (by omega)
          exact_mod_cast this
        have hqm_ge1 : (1 : ℝ) ≤ (q : ℝ) * ((M + m : ℕ) : ℝ) := by
          have : 1 ≤ q * (M + m) := Nat.mul_pos (by omega) (by omega)
          exact_mod_cast this
        calc (x m) ^ (-σ - 1) ≤ ((q : ℝ) * ((M + m : ℕ) : ℝ)) ^ (-σ - 1) :=
              Real.rpow_le_rpow_of_nonpos hqm_pos (hx_ge m) (by linarith)
          _ ≤ ((q : ℝ) * ((M + m : ℕ) : ℝ)) ^ (-2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hqm_ge1 (by linarith)
          _ = 1 / ((q : ℝ) ^ 2 * ((M + m : ℕ) : ℝ) ^ 2) := by
              rw [Real.rpow_neg hqm_pos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
                Real.rpow_natCast, mul_pow, one_div]
      have hinv_sq : ∑ m ∈ Finset.range L, (1 : ℝ) / ((M + m : ℕ) : ℝ) ^ 2 ≤ 2 / (M : ℝ) := by
        cases L with
        | zero => simp; positivity
        | succ L =>
          rw [Finset.sum_range_succ']
          have hrest : ∑ k ∈ Finset.range L, (1 : ℝ) / ((M + (k + 1) : ℕ) : ℝ) ^ 2 ≤ 1 / (M : ℝ) := by
            have hle_t : ∀ k ∈ Finset.range L,
                (1 : ℝ) / ((M + (k + 1) : ℕ) : ℝ) ^ 2 ≤
                1 / ((M + k : ℕ) : ℝ) - 1 / ((M + k + 1 : ℕ) : ℝ) := by
              intro k _
              have h1 : (0 : ℝ) < ((M + k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M + k)
              have h2 : (0 : ℝ) < ((M + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M + k + 1)
              have hcast : ((M + (k + 1) : ℕ) : ℝ) = ((M + k + 1 : ℕ) : ℝ) := by push_cast; ring
              rw [hcast]
              have hdiff : 1 / ((M + k : ℕ) : ℝ) - 1 / ((M + k + 1 : ℕ) : ℝ) =
                  1 / (((M + k : ℕ) : ℝ) * ((M + k + 1 : ℕ) : ℝ)) := by
                have hsub : ((M + k + 1 : ℕ) : ℝ) - ((M + k : ℕ) : ℝ) = 1 := by push_cast; ring
                field_simp [h1.ne', h2.ne']
                linarith
              rw [hdiff]
              exact one_div_le_one_div_of_le (by positivity) (by nlinarith [show ((M + k : ℕ) : ℝ) ≤ ((M + k + 1 : ℕ) : ℝ) by push_cast; linarith])
            have htele : ∀ n : ℕ, ∑ k ∈ Finset.range n,
                (1 / ((M + k : ℕ) : ℝ) - 1 / ((M + k + 1 : ℕ) : ℝ)) =
                1 / (M : ℝ) - 1 / ((M + n : ℕ) : ℝ) := by
              intro n
              induction n with
              | zero => simp
              | succ n ih =>
                rw [Finset.sum_range_succ, ih]
                have hc : ((M + (n + 1) : ℕ) : ℝ) = ((M + n + 1 : ℕ) : ℝ) := by push_cast; ring
                rw [hc]; ring
            calc ∑ k ∈ Finset.range L, (1 : ℝ) / ((M + (k + 1) : ℕ) : ℝ) ^ 2
                ≤ ∑ k ∈ Finset.range L, (1 / ((M + k : ℕ) : ℝ) - 1 / ((M + k + 1 : ℕ) : ℝ)) :=
                  sum_le_sum hle_t
              _ = 1 / (M : ℝ) - 1 / ((M + L : ℕ) : ℝ) := htele L
              _ ≤ 1 / (M : ℝ) := by
                  have : 0 ≤ 1 / ((M + L : ℕ) : ℝ) := by positivity
                  linarith
          have h0 : (1 : ℝ) / ((M + 0 : ℕ) : ℝ) ^ 2 ≤ 1 / (M : ℝ) := by
            simp only [add_zero]
            have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
            exact one_div_le_one_div_of_le hMpos (by nlinarith)
          have h2M : 1 / (M : ℝ) + 1 / (M : ℝ) = 2 / (M : ℝ) := by ring
          linarith
      calc ∑ m ∈ Finset.range L, ‖s‖ * (q : ℝ) * (x m) ^ (-σ - 1)
          ≤ ∑ m ∈ Finset.range L, ‖s‖ * (q : ℝ) * (1 / ((q : ℝ) ^ 2 * ((M + m : ℕ) : ℝ) ^ 2)) :=
            sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hterm m) (by positivity)
        _ = (‖s‖ / (q : ℝ)) * ∑ m ∈ Finset.range L, (1 : ℝ) / ((M + m : ℕ) : ℝ) ^ 2 := by
            rw [mul_sum]
            refine sum_congr rfl fun m _ => ?_
            field_simp [hqpos.ne']
        _ ≤ ((2 + |T|) / (q : ℝ)) * (2 / (M : ℝ)) :=
            mul_le_mul (div_le_div_of_nonneg_right hs_norm hqpos.le) hinv_sq
              (sum_nonneg fun _ _ => by positivity) (by positivity)
        _ = 2 * (2 + |T|) / ((q : ℝ) * (M : ℝ)) := by ring
    calc ‖((x 0 : ℂ) ^ (1 - s) - (x L : ℂ) ^ (1 - s)) / ((q : ℂ) * (s - 1)) +
          ∑ m ∈ Finset.range L,
            ((x m : ℂ) ^ (-s) - (1 / (q : ℂ)) * ∫ u in (x m)..(x (m + 1)), (u : ℂ) ^ (-s))‖
        ≤ ‖((x 0 : ℂ) ^ (1 - s) - (x L : ℂ) ^ (1 - s)) / ((q : ℂ) * (s - 1))‖ +
          ‖∑ m ∈ Finset.range L,
            ((x m : ℂ) ^ (-s) - (1 / (q : ℂ)) * ∫ u in (x m)..(x (m + 1)), (u : ℂ) ^ (-s))‖ :=
          norm_add_le _ _
      _ ≤ (1 / ((q : ℝ) * |T|) + ‖(x L : ℂ) ^ (1 - s)‖ / ((q : ℝ) * |T|)) +
          ∑ m ∈ Finset.range L, ‖s‖ * (q : ℝ) * (x m) ^ (-σ - 1) := by
          gcongr
          exact (norm_sum_le _ _).trans (sum_le_sum fun m _ => herr_step m)
      _ ≤ 1 / ((q : ℝ) * |T|) + ‖(x L : ℂ) ^ (1 - s)‖ / ((q : ℝ) * |T|) +
          2 * (2 + |T|) / ((q : ℝ) * (M : ℝ)) := by linarith
  have hsum_m : Summable (fun m : ℕ => (((q * (M + m) + r : ℕ) : ℂ) ^ (-s))) := by
    have hinj : Function.Injective (fun m : ℕ => q * (M + m) + r) := by
      intro m1 m2 h
      have h1 : q * (M + m1) = q * (M + m2) := Nat.add_right_cancel h
      have h2 : M + m1 = M + m2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) h1
      omega
    have hcomp := (summable_natCast_cpow (T := T) hσ).comp_injective hinj
    refine hcomp.congr fun m => ?_
    simp only [Function.comp_apply]
    rw [if_neg (by omega : q * (M + m) + r ≠ 0)]
  have htend_sum : Tendsto (fun L : ℕ => ‖∑ m ∈ Finset.range L, (((q * (M + m) + r : ℕ) : ℂ) ^ (-s))‖)
      atTop (𝓝 ‖∑' m : ℕ, (((q * (M + m) + r : ℕ) : ℂ) ^ (-s))‖) :=
    hsum_m.hasSum.tendsto_sum_nat.norm
  have htend_xL : Tendsto (fun L : ℕ => ‖(x L : ℂ) ^ (1 - s)‖) atTop (𝓝 0) := by
    have hrew : (fun L : ℕ => ‖(x L : ℂ) ^ (1 - s)‖) = fun L : ℕ => (x L) ^ (1 - σ) := by
      ext L
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (hx_pos L)]
      congr 1; simp [s]
    rw [hrew]
    have hx_top : Tendsto x atTop atTop := by
      refine tendsto_atTop_mono (fun L => hx_ge L) ?_
      have h1 : Tendsto (fun L : ℕ => (M : ℝ) + (L : ℝ)) atTop atTop :=
        tendsto_atTop_add_const_left atTop (M : ℝ) tendsto_natCast_atTop_atTop
      have h2 := h1.const_mul_atTop hqpos
      refine h2.congr fun L => ?_
      push_cast; ring
    exact (tendsto_rpow_neg_atTop (by linarith : 0 < σ - 1)).comp hx_top |>.congr fun L => by
      simp [show -(σ - 1) = 1 - σ by ring]
  have htend_rhs : Tendsto (fun L : ℕ =>
      1 / ((q : ℝ) * |T|) + ‖(x L : ℂ) ^ (1 - s)‖ / ((q : ℝ) * |T|) +
      2 * (2 + |T|) / ((q : ℝ) * (M : ℝ)))
      atTop (𝓝 (1 / ((q : ℝ) * |T|) + 2 * (2 + |T|) / ((q : ℝ) * (M : ℝ)))) := by
    have h0 : Tendsto (fun L : ℕ => ‖(x L : ℂ) ^ (1 - s)‖ / ((q : ℝ) * |T|)) atTop (𝓝 0) := by
      simpa using htend_xL.div_const ((q : ℝ) * |T|)
    have h1 := ((tendsto_const_nhds (x := 1 / ((q : ℝ) * |T|))).add h0).add
      (tendsto_const_nhds (x := 2 * (2 + |T|) / ((q : ℝ) * (M : ℝ))))
    simpa using h1
  exact le_of_tendsto_of_tendsto htend_sum htend_rhs (Eventually.of_forall hpart)
lemma harmonic_sum_le_log_add_one (N : ℕ) :
    ∑ n ∈ Icc 1 N, (1 : ℝ) / (n : ℝ) ≤ Real.log (max 1 (N : ℝ)) + 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    cases N with
    | zero => simp
    | succ M =>
      have hIcc : Icc 1 (M + 2) = insert (M + 2) (Icc 1 (M + 1)) := by
        ext k; simp only [mem_Icc, mem_insert]; omega
      rw [hIcc, sum_insert (by simp)]
      have h1 : max (1 : ℝ) ((M + 1 : ℕ) : ℝ) = ((M + 1 : ℕ) : ℝ) :=
        max_eq_right (by exact_mod_cast (by omega : 1 ≤ M + 1))
      have h2 : max (1 : ℝ) ((M + 2 : ℕ) : ℝ) = ((M + 2 : ℕ) : ℝ) :=
        max_eq_right (by exact_mod_cast (by omega : 1 ≤ M + 2))
      rw [h1] at ih
      rw [h2]
      have hlog_step : (1 : ℝ) / ((M + 2 : ℕ) : ℝ) ≤
          Real.log ((M + 2 : ℕ) : ℝ) - Real.log ((M + 1 : ℕ) : ℝ) := by
        have hpos1 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
        have hpos2 : (0 : ℝ) < ((M + 2 : ℕ) : ℝ) := by positivity
        rw [← Real.log_div hpos2.ne' hpos1.ne']
        have hdiv : ((M + 1 : ℕ) : ℝ) / ((M + 2 : ℕ) : ℝ) = 1 - 1 / ((M + 2 : ℕ) : ℝ) := by
          have hc : ((M + 2 : ℕ) : ℝ) = ((M + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
          field_simp [hpos2.ne']; linarith
        have hlog_le := Real.log_le_sub_one_of_pos (div_pos hpos1 hpos2)
        have hneg : Real.log (((M + 2 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ)) =
            -Real.log (((M + 1 : ℕ) : ℝ) / ((M + 2 : ℕ) : ℝ)) := by
          rw [← Real.log_inv, inv_div]
        rw [hneg]
        linarith [hdiv, hlog_le]
      linarith
lemma dyadic_ap_weighted_bound {k : ℕ} (hk : 2 ≤ k) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {q r A : ℕ}, 1 ≤ q → 1 ≤ r → r ≤ q → q ≤ A →
      ∀ {σ T : ℝ}, 1 < σ → 1 ≤ |T| →
      ((k - 1).factorial : ℝ) * |T| / ((A : ℝ) ^ k) ≤ 2 * Real.pi →
      ‖∑ m ∈ Icc 1 A,
        (((q * (A + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T)))‖ ≤
        C * ((((k - 1).factorial : ℝ) * |T| / ((A : ℝ) ^ k)) ^ vdcA k +
             (A : ℝ) ^ (-vdcC k) * (((k - 1).factorial : ℝ) * |T| / ((A : ℝ) ^ k)) ^ (-vdcD k)) := by
  obtain ⟨C, hC1, hexp⟩ := exp_sum_ap_bound hk
  refine ⟨C, hC1, ?_⟩
  intro q r A hq hr1 hrq hqA σ T hσ hT1 hlam_bd
  have hA1 : 1 ≤ A := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (by omega : 0 < A)
  have hlam_top : ((k - 1).factorial : ℝ) * |T| * (q : ℝ) ^ k / (2 * Real.pi * ((q : ℝ) * (A : ℝ)) ^ k) ≤ 1 := by
    have hqne : (q : ℝ) ^ k ≠ 0 := by positivity
    have hsimp : ((k - 1).factorial : ℝ) * |T| * (q : ℝ) ^ k / (2 * Real.pi * ((q : ℝ) * (A : ℝ)) ^ k) =
        (((k - 1).factorial : ℝ) * |T| / ((A : ℝ) ^ k)) / (2 * Real.pi) := by
      rw [mul_pow]; field_simp [hqne]
    rw [hsimp, div_le_one (by positivity)]
    exact hlam_bd
  let c : ℕ → ℂ := fun m => (((q * (A + m) + r : ℕ) : ℂ) ^ (-(Complex.I * (T : ℂ))))
  let w : ℕ → ℝ := fun m => ((q * (A + m) + r : ℕ) : ℝ) ^ (-σ)
  have hrew : ∑ m ∈ Icc 1 A, (((q * (A + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T))) =
      ∑ m ∈ Icc 1 A, c m * (w m : ℂ) := by
    refine sum_congr rfl fun m _ => ?_
    have hpos : (0 : ℝ) < ((q * (A + m) + r : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < q * (A + m) + r)
    dsimp [c, w]
    rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hpos.le, ← Complex.cpow_add _ _ (by exact_mod_cast hpos.ne')]
    congr 1; push_cast; ring
  rw [hrew]
  let B : ℝ := C * (A : ℝ) *
    ((((k - 1).factorial : ℝ) * |T| / ((A : ℝ) ^ k)) ^ vdcA k +
     (A : ℝ) ^ (-vdcC k) * (((k - 1).factorial : ℝ) * |T| / ((A : ℝ) ^ k)) ^ (-vdcD k))
  have hB : 0 ≤ B := by
    have : 0 ≤ ((k - 1).factorial : ℝ) * |T| / ((A : ℝ) ^ k) := by positivity
    have : 0 ≤ (((k - 1).factorial : ℝ) * |T| / ((A : ℝ) ^ k)) ^ vdcA k := Real.rpow_nonneg this _
    have : 0 ≤ (A : ℝ) ^ (-vdcC k) := Real.rpow_nonneg hApos.le _
    have : 0 ≤ (((k - 1).factorial : ℝ) * |T| / ((A : ℝ) ^ k)) ^ (-vdcD k) := Real.rpow_nonneg (by positivity) _
    positivity
  have habel := abel_sum_decreasing_weight hA1 hB
    (c := c) (w := w)
    (fun m _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun m _ _ => by
      dsimp [w]
      have hpos : (0 : ℝ) < ((q * (A + m) + r : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < q * (A + m) + r)
      have hle : ((q * (A + m) + r : ℕ) : ℝ) ≤ ((q * (A + (m + 1)) + r : ℕ) : ℝ) := by
        exact_mod_cast (by nlinarith : q * (A + m) + r ≤ q * (A + (m + 1)) + r)
      exact Real.rpow_le_rpow_of_nonpos hpos hle (by linarith))
    (fun m hm1 hmA => hexp hq hr1 hrq hm1 hqA hmA hT1 hlam_top)
  have hw1 : w 1 ≤ 1 / (A : ℝ) := by
    dsimp [w]
    have hgeA : (A : ℝ) ≤ ((q * (A + 1) + r : ℕ) : ℝ) := by
      have : A ≤ q * (A + 1) + r := by nlinarith
      exact_mod_cast this
    have hge1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA1
    calc ((q * (A + 1) + r : ℕ) : ℝ) ^ (-σ)
        ≤ (A : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_nonpos hApos hgeA (by linarith)
      _ ≤ (A : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hge1 (by linarith)
      _ = 1 / (A : ℝ) := by rw [Real.rpow_neg_one, one_div]
  calc ‖∑ m ∈ Icc 1 A, c m * (w m : ℂ)‖
      ≤ w 1 * B := habel
    _ ≤ (1 / (A : ℝ)) * B := mul_le_mul_of_nonneg_right hw1 hB
    _ = C * ((((k - 1).factorial : ℝ) * |T| / ((A : ℝ) ^ k)) ^ vdcA k +
             (A : ℝ) ^ (-vdcC k) * (((k - 1).factorial : ℝ) * |T| / ((A : ℝ) ^ k)) ^ (-vdcD k)) := by
        dsimp [B]; field_simp [hApos.ne']
lemma dyadic_block_power_saving {k : ℕ} (hk : 2 ≤ k) (q : ℕ) (hq : 1 ≤ q) :
    ∃ (C η T₁ : ℝ), 0 < η ∧ 1 ≤ T₁ ∧ 0 ≤ C ∧
      ∀ {r A : ℕ}, 1 ≤ r → r ≤ q → ∀ {σ T : ℝ}, 1 < σ → T₁ ≤ |T| →
        (if k = 2 then |T| ^ (2 / 3 : ℝ) ≤ (A : ℝ) ∧ (A : ℝ) ≤ |T| ^ (2 : ℝ)
         else |T| ^ (1 / ((k : ℝ) - 1 / 2)) ≤ (A : ℝ) ∧ (A : ℝ) ≤ |T| ^ (1 / ((k : ℝ) - 3 / 2))) →
        ‖∑ m ∈ Icc 1 A, (((q * (A + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T)))‖ ≤
          C * |T| ^ (-η) := by
  obtain ⟨Ck, hCk1, hdyad⟩ := dyadic_ap_weighted_bound hk
  have hfac_pos : (0 : ℝ) < ((k - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (k - 1)
  have hAk_pos : 0 < vdcA k := vdcA_pos hk
  have hDk_pos : 0 < vdcD k := by unfold vdcD; positivity
  by_cases hk2 : k = 2
  · subst hk2
    let η : ℝ := 1 / 6
    let T₁ : ℝ := max (max ((q : ℝ) ^ 2 + 10) 100) 100
    refine ⟨Ck * 2, η, T₁, by positivity, by dsimp [T₁]; exact le_trans (by norm_num) (le_max_right _ _), by positivity, ?_⟩
    intro r A hr1 hrq σ T hσ hT hA_rng
    simp only [↓reduceIte] at hA_rng
    have hT_ge100 : 100 ≤ |T| := le_trans (by dsimp [T₁]; exact le_max_right _ _) hT
    have hT_gt0 : 0 < |T| := by linarith
    have hT_ge1 : 1 ≤ |T| := by linarith
    have hqA : q ≤ A := by
      have hqR : (q : ℝ) ≤ |T| ^ (2 / 3 : ℝ) := by
        have hq2 : (q : ℝ) ^ 2 ≤ |T| := by
          have : (q : ℝ) ^ 2 + 10 ≤ |T| := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
          linarith
        calc (q : ℝ) = ((q : ℝ) ^ 2) ^ (1 / 2 : ℝ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]; norm_num
          _ ≤ |T| ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) hq2 (by norm_num)
          _ ≤ |T| ^ (2 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT_ge1 (by norm_num)
      exact_mod_cast hqR.trans hA_rng.1
    have hApos : (0 : ℝ) < (A : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hT_gt0 _) hA_rng.1
    have hM_le : ((2 - 1).factorial : ℝ) * |T| / (A : ℝ) ^ 2 ≤ |T| ^ (-(1 / 3 : ℝ)) := by
      have hfac1 : ((2 - 1).factorial : ℝ) = 1 := by norm_num
      rw [hfac1, one_mul]
      have hA2 : |T| ^ (4 / 3 : ℝ) ≤ (A : ℝ) ^ 2 := by
        calc |T| ^ (4 / 3 : ℝ) = (|T| ^ (2 / 3 : ℝ)) ^ (2 : ℕ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hT_gt0.le]; congr 1; norm_num
          _ ≤ (A : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hA_rng.1 2
      calc |T| / (A : ℝ) ^ 2 ≤ |T| / |T| ^ (4 / 3 : ℝ) :=
            div_le_div_of_nonneg_left hT_gt0.le (by positivity) hA2
        _ = |T| ^ (1 - 4 / 3 : ℝ) := by
            rw [Real.rpow_sub hT_gt0, Real.rpow_one]
        _ = |T| ^ (-(1 / 3 : ℝ)) := by congr 1; norm_num
    have hlam_bd : ((2 - 1).factorial : ℝ) * |T| / (A : ℝ) ^ 2 ≤ 2 * Real.pi := by
      have h1 : |T| ^ (-(1 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT_ge1 (by norm_num)
      linarith [Real.pi_gt_three]
    have hres := hdyad hq hr1 hrq hqA hσ hT_ge1 hlam_bd
    have hA2 : vdcA 2 = 1 / 2 := by unfold vdcA; norm_num
    have hC2 : vdcC 2 = 1 := by unfold vdcC; norm_num
    have hD2 : vdcD 2 = 1 / 2 := by unfold vdcD; norm_num
    rw [hA2, hC2, hD2] at hres
    have ht1 : (((2 - 1).factorial : ℝ) * |T| / (A : ℝ) ^ 2) ^ (1 / 2 : ℝ) ≤ |T| ^ (-η) := by
      calc (((2 - 1).factorial : ℝ) * |T| / (A : ℝ) ^ 2) ^ (1 / 2 : ℝ)
          ≤ (|T| ^ (-(1 / 3 : ℝ))) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) hM_le (by norm_num)
        _ = |T| ^ (-η) := by rw [← Real.rpow_mul hT_gt0.le]; congr 1; dsimp [η]; norm_num
    have ht2 : (A : ℝ) ^ (-1 : ℝ) * (((2 - 1).factorial : ℝ) * |T| / (A : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) ≤ |T| ^ (-η) := by
      have hfac1 : ((2 - 1).factorial : ℝ) = 1 := by norm_num
      rw [hfac1, one_mul]
      have hsimp : (A : ℝ) ^ (-1 : ℝ) * (|T| / (A : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) = |T| ^ (-(1 / 2 : ℝ)) := by
        rw [Real.div_rpow hT_gt0.le (by positivity), ← Real.rpow_natCast (A : ℝ) 2,
          ← Real.rpow_mul hApos.le]
        have heq : ((2 : ℕ) : ℝ) * -(1 / 2 : ℝ) = -1 := by norm_num
        rw [heq, div_eq_mul_inv, Real.rpow_neg_one, inv_inv]
        field_simp [hApos.ne']
      rw [hsimp]
      exact Real.rpow_le_rpow_of_exponent_le hT_ge1 (by dsimp [η]; norm_num)
    calc ‖∑ m ∈ Icc 1 A, (((q * (A + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T)))‖
        ≤ Ck * ((((2 - 1).factorial : ℝ) * |T| / (A : ℝ) ^ 2) ^ (1 / 2 : ℝ) +
          (A : ℝ) ^ (-1 : ℝ) * (((2 - 1).factorial : ℝ) * |T| / (A : ℝ) ^ 2) ^ (-(1 / 2 : ℝ))) := hres
      _ ≤ Ck * (|T| ^ (-η) + |T| ^ (-η)) := mul_le_mul_of_nonneg_left (add_le_add ht1 ht2) (by positivity)
      _ = Ck * 2 * |T| ^ (-η) := by ring
  · have hk3 : 3 ≤ k := by omega
    have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
    let e1 : ℝ := 1 / (2 * (k : ℝ) - 1)
    let e2 : ℝ := 1 / (2 * (k : ℝ) - 3)
    have he1_pos : 0 < e1 := by
      dsimp [e1]; have : 0 < 2 * (k : ℝ) - 1 := by linarith
      positivity
    have he2_pos : 0 < e2 := by
      dsimp [e2]; have : 0 < 2 * (k : ℝ) - 3 := by linarith
      positivity
    let η : ℝ := min (e1 * vdcA k) (e2 * vdcD k)
    have hη_pos : 0 < η := lt_min (mul_pos he1_pos hAk_pos) (mul_pos he2_pos hDk_pos)
    let T₁ : ℝ := max (max ((q : ℝ) ^ k + 10) (((k - 1).factorial : ℝ) ^ (2 * k) + 10)) 100
    refine ⟨Ck * (((k - 1).factorial : ℝ) ^ vdcA k + ((k - 1).factorial : ℝ) ^ (-vdcD k)),
      η, T₁, hη_pos, by dsimp [T₁]; exact le_trans (by norm_num) (le_max_right _ _), by positivity, ?_⟩
    intro r A hr1 hrq σ T hσ hT hA_rng
    rw [if_neg hk2] at hA_rng
    have hT_ge100 : 100 ≤ |T| := le_trans (le_max_right _ _) hT
    have hT_gt0 : 0 < |T| := by linarith
    have hT_ge1 : 1 ≤ |T| := by linarith
    have hqA : q ≤ A := by
      have hqk : (q : ℝ) ^ k ≤ |T| := by
        have : (q : ℝ) ^ k + 10 ≤ |T| := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
        linarith
      have hqR : (q : ℝ) ≤ |T| ^ (1 / ((k : ℝ) - 1 / 2)) := by
        calc (q : ℝ) = ((q : ℝ) ^ k) ^ (1 / (k : ℝ)) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
              have hkne : (k : ℝ) ≠ 0 := by linarith
              rw [mul_one_div_cancel hkne, Real.rpow_one]
          _ ≤ |T| ^ (1 / (k : ℝ)) := Real.rpow_le_rpow (by positivity) hqk (by positivity)
          _ ≤ |T| ^ (1 / ((k : ℝ) - 1 / 2)) :=
              Real.rpow_le_rpow_of_exponent_le hT_ge1 (one_div_le_one_div_of_le (by linarith) (by linarith))
      exact_mod_cast hqR.trans hA_rng.1
    have hApos : (0 : ℝ) < (A : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hT_gt0 _) hA_rng.1
    have hT_div_Ak : |T| / (A : ℝ) ^ k ≤ |T| ^ (-e1) := by
      have hAk : |T| ^ ((k : ℝ) / ((k : ℝ) - 1 / 2)) ≤ (A : ℝ) ^ k := by
        calc |T| ^ ((k : ℝ) / ((k : ℝ) - 1 / 2))
            = (|T| ^ (1 / ((k : ℝ) - 1 / 2))) ^ (k : ℕ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hT_gt0.le]; congr 1; ring
          _ ≤ (A : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hA_rng.1 k
      have hexp1 : 1 - (k : ℝ) / ((k : ℝ) - 1 / 2) = -e1 := by
        dsimp [e1]
        have h1 : (k : ℝ) - 1 / 2 ≠ 0 := by linarith
        have h2 : 2 * (k : ℝ) - 1 ≠ 0 := by linarith
        have hlhs : 1 - (k : ℝ) / ((k : ℝ) - 1 / 2) = (-1 / 2) / ((k : ℝ) - 1 / 2) := by
          rw [eq_div_iff h1, sub_mul, one_mul, div_mul_cancel₀ _ h1]; ring
        rw [hlhs, ← neg_div, div_eq_div_iff h1 h2]; ring
      calc |T| / (A : ℝ) ^ k ≤ |T| / |T| ^ ((k : ℝ) / ((k : ℝ) - 1 / 2)) :=
            div_le_div_of_nonneg_left hT_gt0.le (by positivity) hAk
        _ = |T| ^ (1 - (k : ℝ) / ((k : ℝ) - 1 / 2)) := by
            rw [Real.rpow_sub hT_gt0, Real.rpow_one]
        _ = |T| ^ (-e1) := by rw [hexp1]
    have hlam_bd : ((k - 1).factorial : ℝ) * |T| / (A : ℝ) ^ k ≤ 2 * Real.pi := by
      have hfac_le : ((k - 1).factorial : ℝ) ≤ |T| ^ e1 := by
        have hfk : ((k - 1).factorial : ℝ) ^ (2 * k) ≤ |T| := by
          have : ((k - 1).factorial : ℝ) ^ (2 * k) + 10 ≤ |T| :=
            le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
          linarith
        calc ((k - 1).factorial : ℝ)
            = (((k - 1).factorial : ℝ) ^ (2 * k)) ^ (1 / (2 * (k : ℝ))) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hfac_pos.le]
              have hne : 2 * (k : ℝ) ≠ 0 := by linarith
              have hc : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
              rw [hc, mul_one_div_cancel hne, Real.rpow_one]
          _ ≤ |T| ^ (1 / (2 * (k : ℝ))) := Real.rpow_le_rpow (by positivity) hfk (by positivity)
          _ ≤ |T| ^ e1 := Real.rpow_le_rpow_of_exponent_le hT_ge1 (by
              dsimp [e1]; exact one_div_le_one_div_of_le (by linarith) (by linarith))
      calc ((k - 1).factorial : ℝ) * |T| / (A : ℝ) ^ k
          = ((k - 1).factorial : ℝ) * (|T| / (A : ℝ) ^ k) := by ring
        _ ≤ |T| ^ e1 * |T| ^ (-e1) :=
            mul_le_mul hfac_le hT_div_Ak (by positivity) (by positivity)
        _ = 1 := by rw [← Real.rpow_add hT_gt0, add_neg_cancel, Real.rpow_zero]
        _ ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hres := hdyad hq hr1 hrq hqA hσ hT_ge1 hlam_bd
    have ht1 : (((k - 1).factorial : ℝ) * |T| / (A : ℝ) ^ k) ^ vdcA k ≤
        ((k - 1).factorial : ℝ) ^ vdcA k * |T| ^ (-η) := by
      have hrew : ((k - 1).factorial : ℝ) * |T| / (A : ℝ) ^ k =
          ((k - 1).factorial : ℝ) * (|T| / (A : ℝ) ^ k) := by ring
      rw [hrew, Real.mul_rpow hfac_pos.le (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hfac_pos.le _)
      calc (|T| / (A : ℝ) ^ k) ^ vdcA k ≤ (|T| ^ (-e1)) ^ vdcA k :=
            Real.rpow_le_rpow (by positivity) hT_div_Ak hAk_pos.le
        _ = |T| ^ (-(e1 * vdcA k)) := by rw [← Real.rpow_mul hT_gt0.le]; congr 1; ring
        _ ≤ |T| ^ (-η) := Real.rpow_le_rpow_of_exponent_le hT_ge1 (by
            have : η ≤ e1 * vdcA k := min_le_left _ _
            linarith)
    have ht2 : (A : ℝ) ^ (-vdcC k) * (((k - 1).factorial : ℝ) * |T| / (A : ℝ) ^ k) ^ (-vdcD k) ≤
        ((k - 1).factorial : ℝ) ^ (-vdcD k) * |T| ^ (-η) := by
      have hrew : ((k - 1).factorial : ℝ) * |T| / (A : ℝ) ^ k =
          ((k - 1).factorial : ℝ) * (|T| / (A : ℝ) ^ k) := by ring
      rw [hrew, Real.mul_rpow hfac_pos.le (by positivity)]
      have hC_eq : vdcC k = 2 * vdcD k := by
        unfold vdcC vdcD
        have hsub : k - 1 = (k - 2) + 1 := by omega
        rw [hsub, pow_succ]; field_simp
      have hsimp : (A : ℝ) ^ (-vdcC k) * (|T| / (A : ℝ) ^ k) ^ (-vdcD k) =
          ((A : ℝ) ^ (k - 2) / |T|) ^ vdcD k := by
        rw [hC_eq, Real.div_rpow hT_gt0.le (by positivity),
          Real.div_rpow (by positivity) hT_gt0.le,
          ← Real.rpow_natCast (A : ℝ) k, ← Real.rpow_natCast (A : ℝ) (k - 2),
          ← Real.rpow_mul hApos.le, ← Real.rpow_mul hApos.le]
        have hkm2 : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
          rw [Nat.cast_sub (by omega : 2 ≤ k)]; norm_num
        rw [hkm2, div_eq_mul_inv, div_eq_mul_inv, Real.rpow_neg hT_gt0.le]
        have hA_inv : ((A : ℝ) ^ ((k : ℝ) * -vdcD k))⁻¹ = (A : ℝ) ^ ((k : ℝ) * vdcD k) := by
          rw [mul_neg, Real.rpow_neg hApos.le, inv_inv]
        rw [hA_inv]
        have hexp : (A : ℝ) ^ (-(2 * vdcD k)) * (A : ℝ) ^ ((k : ℝ) * vdcD k) =
            (A : ℝ) ^ (((k : ℝ) - 2) * vdcD k) := by
          rw [← Real.rpow_add hApos]; congr 1; ring
        calc (A : ℝ) ^ (-(2 * vdcD k)) * ((|T| ^ vdcD k)⁻¹ * (A : ℝ) ^ ((k : ℝ) * vdcD k))
            = ((A : ℝ) ^ (-(2 * vdcD k)) * (A : ℝ) ^ ((k : ℝ) * vdcD k)) * (|T| ^ vdcD k)⁻¹ := by ring
          _ = (A : ℝ) ^ (((k : ℝ) - 2) * vdcD k) * (|T| ^ vdcD k)⁻¹ := by rw [hexp]
      have hratio : (A : ℝ) ^ (k - 2) / |T| ≤ |T| ^ (-e2) := by
        have hAkm2 : (A : ℝ) ^ (k - 2) ≤ |T| ^ (((k : ℝ) - 2) / ((k : ℝ) - 3 / 2)) := by
          have hkm2 : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
            rw [Nat.cast_sub (by omega : 2 ≤ k)]; norm_num
          calc (A : ℝ) ^ (k - 2) ≤ (|T| ^ (1 / ((k : ℝ) - 3 / 2))) ^ (k - 2) :=
                pow_le_pow_left₀ hApos.le hA_rng.2 (k - 2)
            _ = |T| ^ (((k : ℝ) - 2) / ((k : ℝ) - 3 / 2)) := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul hT_gt0.le, hkm2]; congr 1; ring
        have hexp2 : ((k : ℝ) - 2) / ((k : ℝ) - 3 / 2) - 1 = -e2 := by
          dsimp [e2]
          have h1 : (k : ℝ) - 3 / 2 ≠ 0 := by linarith
          have h2 : 2 * (k : ℝ) - 3 ≠ 0 := by linarith
          have hlhs : ((k : ℝ) - 2) / ((k : ℝ) - 3 / 2) - 1 = (-1 / 2) / ((k : ℝ) - 3 / 2) := by
            rw [eq_div_iff h1, sub_mul, one_mul, div_mul_cancel₀ _ h1]; ring
          rw [hlhs, ← neg_div, div_eq_div_iff h1 h2]; ring
        calc (A : ℝ) ^ (k - 2) / |T| ≤ |T| ^ (((k : ℝ) - 2) / ((k : ℝ) - 3 / 2)) / |T| :=
              div_le_div_of_nonneg_right hAkm2 hT_gt0.le
          _ = |T| ^ (((k : ℝ) - 2) / ((k : ℝ) - 3 / 2) - 1) := by
              rw [Real.rpow_sub hT_gt0, Real.rpow_one]
          _ = |T| ^ (-e2) := by rw [hexp2]
      calc (A : ℝ) ^ (-vdcC k) * (((k - 1).factorial : ℝ) ^ (-vdcD k) * (|T| / (A : ℝ) ^ k) ^ (-vdcD k))
          = ((k - 1).factorial : ℝ) ^ (-vdcD k) * ((A : ℝ) ^ (-vdcC k) * (|T| / (A : ℝ) ^ k) ^ (-vdcD k)) := by ring
        _ = ((k - 1).factorial : ℝ) ^ (-vdcD k) * ((A : ℝ) ^ (k - 2) / |T|) ^ vdcD k := by rw [hsimp]
        _ ≤ ((k - 1).factorial : ℝ) ^ (-vdcD k) * (|T| ^ (-e2)) ^ vdcD k :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hratio hDk_pos.le) (by positivity)
        _ = ((k - 1).factorial : ℝ) ^ (-vdcD k) * |T| ^ (-(e2 * vdcD k)) := by
            rw [← Real.rpow_mul hT_gt0.le]; congr 2; ring
        _ ≤ ((k - 1).factorial : ℝ) ^ (-vdcD k) * |T| ^ (-η) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT_ge1 (by
              have : η ≤ e2 * vdcD k := min_le_right _ _
              linarith)) (by positivity)
    calc ‖∑ m ∈ Icc 1 A, (((q * (A + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T)))‖
        ≤ Ck * ((((k - 1).factorial : ℝ) * |T| / (A : ℝ) ^ k) ^ vdcA k +
          (A : ℝ) ^ (-vdcC k) * (((k - 1).factorial : ℝ) * |T| / (A : ℝ) ^ k) ^ (-vdcD k)) := hres
      _ ≤ Ck * (((k - 1).factorial : ℝ) ^ vdcA k * |T| ^ (-η) +
          ((k - 1).factorial : ℝ) ^ (-vdcD k) * |T| ^ (-η)) :=
          mul_le_mul_of_nonneg_left (add_le_add ht1 ht2) (by positivity)
      _ = Ck * (((k - 1).factorial : ℝ) ^ vdcA k + ((k - 1).factorial : ℝ) ^ (-vdcD k)) * |T| ^ (-η) := by ring
private lemma sum_Icc_pow_two_dyadic (J0 J1 : ℕ) (hJ : J0 ≤ J1) (g : ℕ → ℂ) :
    ∑ u ∈ Icc (2 ^ J0 + 1) (2 ^ J1), g u =
      ∑ j ∈ Ico J0 J1, ∑ m ∈ Icc 1 (2 ^ j), g (2 ^ j + m) := by
  induction J1, hJ using Nat.le_induction with
  | base => simp
  | succ J hJ ih =>
    have hIco : Ico J0 (J + 1) = insert J (Ico J0 J) := by
      ext j; simp only [mem_Ico, mem_insert]; omega
    rw [hIco, sum_insert (by simp)]
    have hIcc : Icc (2 ^ J0 + 1) (2 ^ (J + 1)) =
        Icc (2 ^ J0 + 1) (2 ^ J) ∪ Icc (2 ^ J + 1) (2 ^ (J + 1)) := by
      ext u; simp only [mem_Icc, mem_union]
      have : 2 ^ J0 ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) hJ
      omega
    have hdisj : Disjoint (Icc (2 ^ J0 + 1) (2 ^ J)) (Icc (2 ^ J + 1) (2 ^ (J + 1))) := by
      rw [disjoint_left]; intro u h1 h2
      simp only [mem_Icc] at h1 h2; omega
    rw [hIcc, sum_union hdisj, ih, add_comm]
    congr 1
    refine Finset.sum_bij (fun u _ => u - 2 ^ J) ?_ ?_ ?_ ?_
    · intro u hu; rw [mem_Icc] at hu ⊢; rw [pow_succ] at hu; omega
    · intro u1 hu1 u2 hu2 heq; rw [mem_Icc] at hu1 hu2; omega
    · intro m hm; rw [mem_Icc] at hm
      refine ⟨2 ^ J + m, mem_Icc.mpr ⟨by omega, by rw [pow_succ]; omega⟩, by omega⟩
    · intro u hu; rw [mem_Icc] at hu
      have : 2 ^ J + (u - 2 ^ J) = u := by omega
      rw [this]
private lemma sum_Icc_ap_split {q A0 A1 : ℕ} (hq : 1 ≤ q) (hA : A0 ≤ A1) (f : ℕ → ℂ) :
    ∑ n ∈ Icc (q * (A0 + 1) + 1) (q * (A1 + 1)), f n =
      ∑ r ∈ Icc 1 q, ∑ u ∈ Icc (A0 + 1) A1, f (q * u + r) := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun n _ => (if n % q = 0 then q else n % q, (n - 1) / q)) ?_ ?_ ?_ ?_
  · intro n hn
    rw [mem_Icc] at hn
    rw [Finset.mem_product, mem_Icc, mem_Icc]
    have hmod_lt : n % q < q := Nat.mod_lt n (by omega)
    have hdiv_lo : A0 + 1 ≤ (n - 1) / q := by
      rw [Nat.le_div_iff_mul_le (by omega), mul_comm]; omega
    have hdiv_hi : (n - 1) / q ≤ A1 := by
      have : (n - 1) / q < A1 + 1 := by
        rw [Nat.div_lt_iff_lt_mul (by omega), mul_comm]; omega
      omega
    refine ⟨⟨?_, ?_⟩, hdiv_lo, hdiv_hi⟩ <;> split_ifs <;> omega
  · intro n1 hn1 n2 hn2 heq
    rw [mem_Icc] at hn1 hn2
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    dsimp only at h1 h2
    have hrec : ∀ n, 1 ≤ n → n = q * ((n - 1) / q) + (if n % q = 0 then q else n % q) := by
      intro n hn
      have hd := Nat.div_add_mod (n - 1) q
      have hlt : (n - 1) % q < q := Nat.mod_lt _ (by omega)
      have hn_eq : n = q * ((n - 1) / q) + ((n - 1) % q + 1) := by omega
      by_cases hc : (n - 1) % q + 1 = q
      · have hqdiv : n % q = 0 := by
          have : n = q * ((n - 1) / q + 1) := by nlinarith
          rw [this, Nat.mul_mod_right]
        rw [if_pos hqdiv]; nlinarith
      · have hqmod : n % q = (n - 1) % q + 1 := by
          conv_lhs => rw [hn_eq]
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        rw [if_neg (by omega), hqmod]; exact hn_eq
    have hn1_pos : 1 ≤ n1 := by omega
    have hn2_pos : 1 ≤ n2 := by omega
    rw [hrec n1 hn1_pos, hrec n2 hn2_pos, h1, h2]
  · intro p hp
    rw [Finset.mem_product, mem_Icc, mem_Icc] at hp
    refine ⟨q * p.2 + p.1, mem_Icc.mpr ⟨by nlinarith, by nlinarith⟩, ?_⟩
    apply Prod.ext
    · dsimp only
      by_cases hc : p.1 = q
      · have hm : (q * p.2 + p.1) % q = 0 := by
          rw [hc, show q * p.2 + q = q * (p.2 + 1) by ring, Nat.mul_mod_right]
        rw [if_pos hm, hc]
      · have hm : (q * p.2 + p.1) % q = p.1 := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        rw [if_neg (by omega), hm]
    · dsimp only
      have hsub : q * p.2 + p.1 - 1 = q * p.2 + (p.1 - 1) := by omega
      rw [hsub, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), add_zero]
  · intro n hn
    rw [mem_Icc] at hn
    dsimp only
    congr 1
    have hd := Nat.div_add_mod (n - 1) q
    have hlt : (n - 1) % q < q := Nat.mod_lt _ (by omega)
    have hn_eq : n = q * ((n - 1) / q) + ((n - 1) % q + 1) := by omega
    by_cases hc : (n - 1) % q + 1 = q
    · have hqdiv : n % q = 0 := by
        have : n = q * ((n - 1) / q + 1) := by nlinarith
        rw [this, Nat.mul_mod_right]
      rw [if_pos hqdiv]; nlinarith
    · have hqmod : n % q = (n - 1) % q + 1 := by
        conv_lhs => rw [hn_eq]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      rw [if_neg (by omega), hqmod]; exact hn_eq
private lemma norm_dirichletL_sigma_gt_two {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ T : ℝ} (hσ2 : 2 < σ) :
    ‖∑' n : ℕ, if n = 0 then (0 : ℂ) else χ (n : ZMod q) * ((n : ℂ) ^ (-(σ + Complex.I * T)))‖ ≤ 2 := by
  have hσ : 1 < σ := by linarith
  have hsum2 : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-2 : ℝ)) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) := by
      simpa [Real.rpow_neg (Nat.cast_nonneg _)] using
        (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2))
    refine h1.congr fun n => ?_
    by_cases hn : n = 0 <;> simp [hn]
  have htsum_le : ‖∑' n : ℕ, if n = 0 then (0 : ℂ) else χ (n : ZMod q) * ((n : ℂ) ^ (-(σ + Complex.I * T)))‖ ≤
      ∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-2 : ℝ) := by
    calc ‖∑' n : ℕ, if n = 0 then (0 : ℂ) else χ (n : ZMod q) * ((n : ℂ) ^ (-(σ + Complex.I * T)))‖
        ≤ ∑' n : ℕ, ‖if n = 0 then (0 : ℂ) else χ (n : ZMod q) * ((n : ℂ) ^ (-(σ + Complex.I * T)))‖ :=
          norm_tsum_le_tsum_norm (summable_dirichlet_cpow χ hσ).norm
      _ ≤ ∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-2 : ℝ) := by
          refine Summable.tsum_le_tsum (fun n => ?_) (summable_dirichlet_cpow χ hσ).norm hsum2
          by_cases hn : n = 0
          · simp [hn]
          · rw [if_neg hn, if_neg hn, norm_mul, cpow_norm_natCast (by omega)]
            have hpow : (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by linarith)
            exact (mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
              (dirichlet_norm_le_one χ (n : ZMod q))).trans hpow
  have h2_le : ∑' n : ℕ, (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-2 : ℝ)) ≤ 2 := by
    refine le_of_tendsto hsum2.hasSum.tendsto_sum_nat (Eventually.of_forall fun L => ?_)
    cases L with
    | zero => simp
    | succ L =>
      cases L with
      | zero => simp
      | succ L =>
        have h1 : ∑ n ∈ Finset.range (L + 2), (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-2 : ℝ)) =
            1 + ∑ k ∈ Finset.range L, ((k + 2 : ℕ) : ℝ) ^ (-2 : ℝ) := by
          rw [Finset.sum_range_succ', Finset.sum_range_succ']
          rw [if_pos rfl, add_zero, if_neg (by omega), Nat.cast_one, Real.one_rpow, add_comm]
          congr 1
        rw [h1]
        have htele : ∑ k ∈ Finset.range L, ((k + 2 : ℕ) : ℝ) ^ (-2 : ℝ) ≤ 1 := by
          have hstep : ∀ k ∈ Finset.range L,
              ((k + 2 : ℕ) : ℝ) ^ (-2 : ℝ) ≤ 1 / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ) := by
            intro k _
            have h1' : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
            have h2' : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
            have hpow : ((k + 2 : ℕ) : ℝ) ^ (-2 : ℝ) = 1 / ((k + 2 : ℕ) : ℝ) ^ 2 := by
              rw [Real.rpow_neg h2'.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
            rw [hpow]
            have hd : 1 / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ) =
                1 / (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by
              have hsub : ((k + 2 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ) = 1 := by push_cast; ring
              field_simp [h1'.ne', h2'.ne']; linarith
            rw [hd]
            exact one_div_le_one_div_of_le (by positivity)
              (by nlinarith [show ((k + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) by push_cast; linarith])
          have ht : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ)) =
              1 - 1 / ((n + 1 : ℕ) : ℝ) := by
            intro n
            induction n with
            | zero => simp
            | succ n ih =>
              rw [Finset.sum_range_succ, ih]
              have hc : ((n + 1 + 1 : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) := by push_cast; ring
              rw [hc]; ring
          calc ∑ k ∈ Finset.range L, ((k + 2 : ℕ) : ℝ) ^ (-2 : ℝ)
              ≤ ∑ k ∈ Finset.range L, (1 / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ)) := sum_le_sum hstep
            _ = 1 - 1 / ((L + 1 : ℕ) : ℝ) := ht L
            _ ≤ 1 := by linarith [show (0 : ℝ) ≤ 1 / ((L + 1 : ℕ) : ℝ) by positivity]
        linarith
  exact htsum_le.trans h2_le
private lemma norm_dirichletL_tail {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {A1 : ℕ} {σ T : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) (hT_ge1 : 1 ≤ |T|)
    (hA1_ge_T2 : |T| ^ (2 : ℝ) ≤ (A1 : ℝ)) :
    ‖∑' k : ℕ, (if q * (A1 + 1) + 1 + k = 0 then (0 : ℂ) else
      χ ((q * (A1 + 1) + 1 + k : ℕ) : ZMod q) *
        (((q * (A1 + 1) + 1 + k : ℕ) : ℂ) ^ (-(σ + Complex.I * T))))‖ ≤ 10 * (q : ℝ) := by
  have hq : 1 ≤ q := NeZero.one_le
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  let f : ℕ → ℂ := fun n => if n = 0 then (0 : ℂ) else χ (n : ZMod q) * ((n : ℂ) ^ (-(σ + Complex.I * T)))
  have hf_sum : Summable f := summable_dirichlet_cpow χ hσ
  have hsum_k : Summable (fun k : ℕ => f (q * (A1 + 1) + 1 + k)) :=
    hf_sum.comp_injective (fun k1 k2 h => by omega)
  have hsum_r : ∀ r ∈ Icc 1 q,
      Summable (fun m : ℕ => (((q * (A1 + 1 + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T)))) := by
    intro r hr
    rw [mem_Icc] at hr
    have hinj : Function.Injective (fun m : ℕ => q * (A1 + 1 + m) + r) := by
      intro m1 m2 h
      have h1 : q * (A1 + 1 + m1) = q * (A1 + 1 + m2) := Nat.add_right_cancel h
      have h2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) h1
      omega
    refine (summable_natCast_cpow (T := T) hσ).comp_injective hinj |>.congr fun m => ?_
    simp only [Function.comp_apply]
    rw [if_neg (by omega : q * (A1 + 1 + m) + r ≠ 0)]
  have htail_eq : ∑' k : ℕ, f (q * (A1 + 1) + 1 + k) =
      ∑ r ∈ Icc 1 q, χ (r : ZMod q) *
        ∑' m : ℕ, (((q * (A1 + 1 + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T))) := by
    have hpart_eq : ∀ L : ℕ,
        ∑ k ∈ Finset.range (q * L), f (q * (A1 + 1) + 1 + k) =
        ∑ r ∈ Icc 1 q, χ (r : ZMod q) *
          ∑ m ∈ Finset.range L, (((q * (A1 + 1 + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T))) := by
      intro L
      have h1 : ∑ r ∈ Icc 1 q, χ (r : ZMod q) *
            ∑ m ∈ Finset.range L, (((q * (A1 + 1 + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T))) =
          ∑ r ∈ Icc 1 q, ∑ m ∈ Finset.range L, f (q * (A1 + 1 + m) + r) := by
        refine sum_congr rfl fun r hr => ?_
        rw [mem_Icc] at hr
        rw [mul_sum]
        refine sum_congr rfl fun m _ => ?_
        dsimp [f]
        rw [if_neg (by omega : q * (A1 + 1 + m) + r ≠ 0)]
        have hmod : ((q * (A1 + 1 + m) + r : ℕ) : ZMod q) = (r : ZMod q) := by push_cast; simp
        rw [hmod]
      rw [h1, ← Finset.sum_product']
      refine Finset.sum_bij (fun k _ => (k % q + 1, k / q)) ?_ ?_ ?_ ?_
      · intro k hk
        rw [mem_range] at hk
        rw [Finset.mem_product, mem_Icc, mem_range]
        have hmod : k % q < q := Nat.mod_lt k (by omega)
        have hdiv : k / q < L := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [mul_comm]; exact hk)
        exact ⟨⟨by omega, by omega⟩, hdiv⟩
      · intro k1 _ k2 _ heq
        have h1' := congrArg Prod.fst heq
        have h2' := congrArg Prod.snd heq
        dsimp only at h1' h2'
        have hd1 := Nat.div_add_mod k1 q
        have hd2 := Nat.div_add_mod k2 q
        nlinarith
      · intro p hp
        rw [Finset.mem_product, mem_Icc, mem_range] at hp
        have hlt_qL : q * p.2 + (p.1 - 1) < q * L := by
          have hle : q * (p.2 + 1) ≤ q * L := Nat.mul_le_mul_left q hp.2
          have hmul : q * (p.2 + 1) = q * p.2 + q := by ring
          omega
        refine ⟨q * p.2 + (p.1 - 1), mem_range.mpr hlt_qL, ?_⟩
        apply Prod.ext
        · dsimp only
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]; omega
        · dsimp only
          rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), add_zero]
      · intro k _
        dsimp only
        congr 1
        have hd := Nat.div_add_mod k q
        nlinarith
    have ht1 : Tendsto (fun L : ℕ => ∑ k ∈ Finset.range (q * L), f (q * (A1 + 1) + 1 + k))
        atTop (𝓝 (∑' k : ℕ, f (q * (A1 + 1) + 1 + k))) := by
      have hmul_top : Tendsto (fun L : ℕ => q * L) atTop atTop :=
        tendsto_atTop_mono (fun L => by nlinarith : ∀ L, L ≤ q * L) tendsto_id
      exact hsum_k.hasSum.tendsto_sum_nat.comp hmul_top
    have ht2 : Tendsto (fun L : ℕ => ∑ r ∈ Icc 1 q, χ (r : ZMod q) *
          ∑ m ∈ Finset.range L, (((q * (A1 + 1 + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T))))
        atTop (𝓝 (∑ r ∈ Icc 1 q, χ (r : ZMod q) *
          ∑' m : ℕ, (((q * (A1 + 1 + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T))))) := by
      refine tendsto_finset_sum _ fun r hr => ?_
      exact tendsto_const_nhds.mul (hsum_r r hr).hasSum.tendsto_sum_nat
    exact tendsto_nhds_unique (ht1.congr hpart_eq) ht2
  change ‖∑' k : ℕ, f (q * (A1 + 1) + 1 + k)‖ ≤ 10 * (q : ℝ)
  rw [htail_eq]
  calc ‖∑ r ∈ Icc 1 q, χ (r : ZMod q) *
          ∑' m : ℕ, (((q * (A1 + 1 + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T)))‖
      ≤ ∑ r ∈ Icc 1 q, ‖χ (r : ZMod q) *
          ∑' m : ℕ, (((q * (A1 + 1 + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T)))‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ Icc 1 q,
          (1 / ((q : ℝ) * |T|) + 2 * (2 + |T|) / ((q : ℝ) * ((A1 + 1 : ℕ) : ℝ))) := by
        refine sum_le_sum fun r hr => ?_
        rw [mem_Icc] at hr
        rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (dirichlet_norm_le_one χ (r : ZMod q))).trans
          (tail_ap_bound hq hr.1 hr.2 (by omega : 1 ≤ A1 + 1) hσ hσ2 hT_ge1)
    _ = (q : ℝ) * (1 / ((q : ℝ) * |T|) + 2 * (2 + |T|) / ((q : ℝ) * ((A1 + 1 : ℕ) : ℝ))) := by
        simp [Nat.card_Icc, show q + 1 - 1 = q by omega]; ring
    _ ≤ 10 * (q : ℝ) := by
        have h1 : 1 / ((q : ℝ) * |T|) ≤ 1 := by
          rw [div_le_one (by positivity)]
          have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
          nlinarith
        have hA1_ge_T : |T| ≤ ((A1 + 1 : ℕ) : ℝ) := by
          have hT2 : |T| ≤ |T| ^ (2 : ℝ) := by
            have : |T| ≤ |T| * |T| := by nlinarith
            simpa [Real.rpow_two, sq] using this
          have : (A1 : ℝ) ≤ ((A1 + 1 : ℕ) : ℝ) := by push_cast; linarith
          linarith [hT2, hA1_ge_T2]
        have h2 : 2 * (2 + |T|) / ((q : ℝ) * ((A1 + 1 : ℕ) : ℝ)) ≤ 6 := by
          rw [div_le_iff₀ (by positivity)]
          have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
          nlinarith
        nlinarith
theorem norm_dirichletL_le_div_K {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (K : ℕ) (hK : 3 ≤ K) :
    ∃ C T₀ : ℝ, 1 ≤ T₀ ∧ 0 ≤ C ∧
      ∀ (σ T : ℝ), 1 < σ → T₀ ≤ |T| →
        ‖∑' n : ℕ, if n = 0 then (0 : ℂ) else χ (n : ZMod q) * ((n : ℂ) ^ (-(σ + Complex.I * T)))‖ ≤
          (2 / (K : ℝ)) * Real.log |T| + C := by
  have hq : 1 ≤ q := NeZero.one_le
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hreg : ∀ k ∈ Icc 2 K,
      ∃ (C η T₁ : ℝ), 0 < η ∧ 1 ≤ T₁ ∧ 0 ≤ C ∧
        ∀ {r A : ℕ}, 1 ≤ r → r ≤ q → ∀ {σ T : ℝ}, 1 < σ → T₁ ≤ |T| →
          (if k = 2 then |T| ^ (2 / 3 : ℝ) ≤ (A : ℝ) ∧ (A : ℝ) ≤ |T| ^ (2 : ℝ)
           else |T| ^ (1 / ((k : ℝ) - 1 / 2)) ≤ (A : ℝ) ∧ (A : ℝ) ≤ |T| ^ (1 / ((k : ℝ) - 3 / 2))) →
          ‖∑ m ∈ Icc 1 A, (((q * (A + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T)))‖ ≤
            C * |T| ^ (-η) := fun k hk => dyadic_block_power_saving (mem_Icc.mp hk).1 q hq
  choose Cf ηf Tf hηf hTf hCf hbd_f using hreg
  let S_k := Icc 2 K
  have hSk_ne : S_k.Nonempty := ⟨2, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  let ηmin : ℝ := S_k.inf' hSk_ne (fun k => if hk : k ∈ S_k then ηf k hk else 1)
  have hηmin_pos : 0 < ηmin := by
    dsimp [ηmin]; rw [Finset.lt_inf'_iff]; intro k hk; simp only [hk, ↓reduceDIte]; exact hηf k hk
  let Cmax : ℝ := ∑ k ∈ S_k, if hk : k ∈ S_k then Cf k hk else 0
  have hCmax_nn : 0 ≤ Cmax := sum_nonneg fun k hk => by simp only [hk, ↓reduceDIte]; exact hCf k hk
  let Tmax : ℝ := max (max (100 * (q : ℝ) + 100) (∑ k ∈ S_k, if hk : k ∈ S_k then Tf k hk else 0))
    ((4 * (q : ℝ) * (Cmax + 1) / ηmin + 10) ^ (2 / ηmin) + 100)
  let T₀ : ℝ := max Tmax (Real.exp ((4 * (K : ℝ)) * (Real.log (q : ℝ) + 2)))
  refine ⟨10 * (q : ℝ) + Real.log (q : ℝ) + 20, T₀, ?_, by positivity, ?_⟩
  · have : 100 ≤ Tmax := le_trans (le_trans (by linarith) (le_max_left _ _)) (le_max_left _ _)
    exact le_trans (by norm_num) (le_trans this (le_max_left _ _))
  intro σ T hσ hT
  have hT_ge100 : 100 ≤ |T| := by
    have : 100 ≤ Tmax := le_trans (le_trans (by linarith) (le_max_left _ _)) (le_max_left _ _)
    exact le_trans this (le_trans (le_max_left _ _) hT)
  have hT_gt0 : 0 < |T| := by linarith
  have hT_ge1 : 1 ≤ |T| := by linarith
  by_cases hσ2 : σ ≤ 2
  swap
  · push Not at hσ2
    have h2 := norm_dirichletL_sigma_gt_two χ (T := T) hσ2
    have hlog_nn : 0 ≤ (2 / (K : ℝ)) * Real.log |T| := mul_nonneg (by positivity) (Real.log_nonneg hT_ge1)
    have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
    linarith
  let X0 : ℝ := |T| ^ (1 / ((K : ℝ) - 1 / 2))
  let J0 : ℕ := Nat.clog 2 ⌈X0⌉₊
  let A0 : ℕ := 2 ^ J0
  let J1 : ℕ := max J0 (Nat.clog 2 ⌈|T| ^ (2 : ℝ)⌉₊)
  let A1 : ℕ := 2 ^ J1
  have hKR : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hX0_pos : 0 < X0 := Real.rpow_pos_of_pos hT_gt0 _
  have hX0_ge2 : 2 ≤ X0 := by
    have hlogT : 4 * (K : ℝ) * (Real.log (q : ℝ) + 2) ≤ Real.log |T| := by
      have h1 : Real.exp (4 * (K : ℝ) * (Real.log (q : ℝ) + 2)) ≤ |T| := le_trans (le_max_right _ _) hT
      have h2 := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at h2
    have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
    have hlogX0 : Real.log 2 ≤ Real.log X0 := by
      dsimp [X0]; rw [Real.log_rpow hT_gt0]
      have h1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      have h2 : (K : ℝ) - 1 / 2 ≤ 4 * (K : ℝ) * (Real.log (q : ℝ) + 2) := by nlinarith
      have h3 : (1 : ℝ) ≤ (1 / ((K : ℝ) - 1 / 2)) * Real.log |T| := by
        rw [one_div_mul_eq_div, one_le_div (by linarith)]; linarith
      linarith
    exact (Real.log_le_log_iff (by norm_num) hX0_pos).mp hlogX0
  have hJ0_le_J1 : J0 ≤ J1 := le_max_left _ _
  have hA0_le_A1 : A0 ≤ A1 := Nat.pow_le_pow_right (by norm_num) hJ0_le_J1
  have hA0_ge_X0 : X0 ≤ (A0 : ℝ) := by
    have h1 : ⌈X0⌉₊ ≤ 2 ^ J0 := Nat.le_pow_clog (by norm_num) _
    exact (Nat.le_ceil X0).trans (by exact_mod_cast h1)
  have hA0_le : (A0 : ℝ) ≤ 2 * X0 + 2 := by
    by_cases hJ0 : J0 = 0
    · simp only [A0, hJ0, pow_zero, Nat.cast_one]; linarith
    · have hlt : 2 ^ (J0 - 1) < ⌈X0⌉₊ := Nat.pow_pred_clog_lt_self (by norm_num) (by
        have : (2 : ℝ) ≤ (⌈X0⌉₊ : ℝ) := hX0_ge2.trans (Nat.le_ceil X0)
        have : 2 ≤ ⌈X0⌉₊ := by exact_mod_cast this
        omega)
      have hltR : ((2 ^ (J0 - 1) : ℕ) : ℝ) < X0 := by exact_mod_cast Nat.lt_ceil.mp hlt
      have hpow : (A0 : ℝ) = 2 * ((2 ^ (J0 - 1) : ℕ) : ℝ) := by
        dsimp [A0]
        have : 2 ^ J0 = 2 * 2 ^ (J0 - 1) := by
          cases hJ : J0 with
          | zero => omega
          | succ m => simp [pow_succ, mul_comm]
        exact_mod_cast this
      linarith
  have hA1_ge_T2 : |T| ^ (2 : ℝ) ≤ (A1 : ℝ) := by
    have h1 : ⌈|T| ^ (2 : ℝ)⌉₊ ≤ 2 ^ (Nat.clog 2 ⌈|T| ^ (2 : ℝ)⌉₊) := Nat.le_pow_clog (by norm_num) _
    have h2 : 2 ^ (Nat.clog 2 ⌈|T| ^ (2 : ℝ)⌉₊) ≤ A1 :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1.trans h2)
  let f : ℕ → ℂ := fun n => if n = 0 then (0 : ℂ) else χ (n : ZMod q) * ((n : ℂ) ^ (-(σ + Complex.I * T)))
  have hf_sum : Summable f := summable_dirichlet_cpow χ hσ
  have hsplit_head_rest : ∑' n : ℕ, f n =
      (∑ n ∈ Icc 1 (q * (A0 + 1)), f n) +
      (∑ n ∈ Icc (q * (A0 + 1) + 1) (q * (A1 + 1)), f n) +
      (∑' k : ℕ, f (q * (A1 + 1) + 1 + k)) := by
    have h1 := hf_sum.sum_add_tsum_nat_add (q * (A1 + 1) + 1)
    rw [← h1]
    have htsum_eq : ∑' k : ℕ, f (k + (q * (A1 + 1) + 1)) = ∑' k : ℕ, f (q * (A1 + 1) + 1 + k) :=
      tsum_congr fun k => by rw [add_comm]
    rw [htsum_eq]
    congr 1
    have hrange : Finset.range (q * (A1 + 1) + 1) =
        insert 0 (Icc 1 (q * (A0 + 1)) ∪ Icc (q * (A0 + 1) + 1) (q * (A1 + 1))) := by
      ext n
      simp only [mem_range, mem_insert, mem_union, mem_Icc]
      have hqA_le : q * (A0 + 1) ≤ q * (A1 + 1) := Nat.mul_le_mul_left q (Nat.add_le_add_right hA0_le_A1 1)
      omega
    rw [hrange, sum_insert (by simp)]
    have hf0 : f 0 = 0 := by simp [f]
    rw [hf0, zero_add]
    exact sum_union (by
      rw [disjoint_left]; intro n h1 h2
      simp only [mem_Icc] at h1 h2; omega)
  have hhead_bd : ‖∑ n ∈ Icc 1 (q * (A0 + 1)), f n‖ ≤
      (2 / (K : ℝ)) * Real.log |T| + Real.log (q : ℝ) + 4 := by
    have h1 : ‖∑ n ∈ Icc 1 (q * (A0 + 1)), f n‖ ≤
        ∑ n ∈ Icc 1 (q * (A0 + 1)), (1 : ℝ) / (n : ℝ) := by
      calc ‖∑ n ∈ Icc 1 (q * (A0 + 1)), f n‖
          ≤ ∑ n ∈ Icc 1 (q * (A0 + 1)), ‖f n‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Icc 1 (q * (A0 + 1)), (1 : ℝ) / (n : ℝ) := by
            refine sum_le_sum fun n hn => ?_
            rw [mem_Icc] at hn
            dsimp [f]
            rw [if_neg (by omega), norm_mul, cpow_norm_natCast hn.1]
            have hpow : (n : ℝ) ^ (-σ) ≤ 1 / (n : ℝ) := by
              rw [one_div, ← Real.rpow_neg_one]
              exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.1) (by linarith)
            exact (mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
              (dirichlet_norm_le_one χ (n : ZMod q))).trans hpow
    have hharm := harmonic_sum_le_log_add_one (q * (A0 + 1))
    have hqA_ge1 : (1 : ℝ) ≤ ((q * (A0 + 1) : ℕ) : ℝ) := by
      have : 1 ≤ q * (A0 + 1) := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (Nat.succ_pos A0))
      exact_mod_cast this
    rw [max_eq_right hqA_ge1] at hharm
    have hqA_le : ((q * (A0 + 1) : ℕ) : ℝ) ≤ (q : ℝ) * (4 * X0) := by
      push_cast
      have hA0_le' : (A0 : ℝ) + 1 ≤ 4 * X0 := by linarith [hA0_le, hX0_ge2]
      exact mul_le_mul_of_nonneg_left hA0_le' hqpos.le
    have hlog_le : Real.log ((q * (A0 + 1) : ℕ) : ℝ) ≤ Real.log (q : ℝ) + Real.log 4 + Real.log X0 := by
      calc Real.log ((q * (A0 + 1) : ℕ) : ℝ)
          ≤ Real.log ((q : ℝ) * (4 * X0)) := Real.log_le_log (by positivity) hqA_le
        _ = Real.log (q : ℝ) + Real.log (4 * X0) := Real.log_mul hqpos.ne' (by positivity)
        _ = Real.log (q : ℝ) + (Real.log 4 + Real.log X0) := by rw [Real.log_mul (by norm_num) hX0_pos.ne']
        _ = Real.log (q : ℝ) + Real.log 4 + Real.log X0 := by ring
    have hlog4 : Real.log 4 ≤ 3 := by
      have h1 : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
      have h2 := Real.log_le_log (by norm_num) h1
      rwa [Real.log_exp] at h2
    have hlogX0 : Real.log X0 ≤ (2 / (K : ℝ)) * Real.log |T| := by
      dsimp [X0]; rw [Real.log_rpow hT_gt0]
      have hcoef : 1 / ((K : ℝ) - 1 / 2) ≤ 2 / (K : ℝ) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
      exact mul_le_mul_of_nonneg_right hcoef (Real.log_nonneg hT_ge1)
    linarith
  have hmid_bd : ‖∑ n ∈ Icc (q * (A0 + 1) + 1) (q * (A1 + 1)), f n‖ ≤ 2 := by
    have hdecomp : ∑ n ∈ Icc (q * (A0 + 1) + 1) (q * (A1 + 1)), f n =
        ∑ r ∈ Icc 1 q, χ (r : ZMod q) *
          ∑ j ∈ Ico J0 J1,
            ∑ m ∈ Icc 1 (2 ^ j),
              (((q * (2 ^ j + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T))) := by
      rw [sum_Icc_ap_split hq hA0_le_A1 f]
      refine sum_congr rfl fun r hr => ?_
      rw [mem_Icc] at hr
      have hfactor : ∀ u ∈ Icc (A0 + 1) A1,
          f (q * u + r) = χ (r : ZMod q) * (((q * u + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T))) := by
        intro u _
        dsimp [f]
        rw [if_neg (by omega : q * u + r ≠ 0)]
        have hmod : ((q * u + r : ℕ) : ZMod q) = (r : ZMod q) := by push_cast; simp
        rw [hmod]
      rw [sum_congr rfl hfactor, ← mul_sum]
      congr 1
      exact sum_Icc_pow_two_dyadic J0 J1 hJ0_le_J1 (fun u => (((q * u + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T))))
    rw [hdecomp]
    have hblock : ∀ r ∈ Icc 1 q, ∀ j ∈ Ico J0 J1,
        ‖∑ m ∈ Icc 1 (2 ^ j), (((q * (2 ^ j + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T)))‖ ≤
          Cmax * |T| ^ (-ηmin) := by
      intro r hr j hj
      rw [mem_Icc] at hr
      rw [mem_Ico] at hj
      have hA_lo : X0 ≤ ((2 ^ j : ℕ) : ℝ) :=
        hA0_ge_X0.trans (by exact_mod_cast Nat.pow_le_pow_right (by norm_num) hj.1)
      have hA_hi : ((2 ^ j : ℕ) : ℝ) ≤ |T| ^ (2 : ℝ) := by
        have hJ1_eq : J1 = Nat.clog 2 ⌈|T| ^ (2 : ℝ)⌉₊ := by dsimp [J1] at hj ⊢; omega
        have hj_lt : j < Nat.clog 2 ⌈|T| ^ (2 : ℝ)⌉₊ := by omega
        have hpow_lt : 2 ^ j < ⌈|T| ^ (2 : ℝ)⌉₊ := by
          have h1 : 2 ^ j ≤ 2 ^ (Nat.clog 2 ⌈|T| ^ (2 : ℝ)⌉₊ - 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          have h2 : 2 ^ (Nat.clog 2 ⌈|T| ^ (2 : ℝ)⌉₊ - 1) < ⌈|T| ^ (2 : ℝ)⌉₊ :=
            Nat.pow_pred_clog_lt_self (by norm_num) (by
              have : (2 : ℝ) ≤ |T| ^ (2 : ℝ) := by
                have : (2 : ℝ) ≤ |T| * |T| := by nlinarith
                simpa [Real.rpow_two, sq] using this
              have : (2 : ℝ) ≤ (⌈|T| ^ (2 : ℝ)⌉₊ : ℝ) := this.trans (Nat.le_ceil _)
              have : 2 ≤ ⌈|T| ^ (2 : ℝ)⌉₊ := by exact_mod_cast this
              omega)
          omega
        exact (Nat.lt_ceil.mp hpow_lt).le
      have hex_k : ∃ k ∈ S_k,
          if k = 2 then |T| ^ (2 / 3 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ∧ ((2 ^ j : ℕ) : ℝ) ≤ |T| ^ (2 : ℝ)
          else |T| ^ (1 / ((k : ℝ) - 1 / 2)) ≤ ((2 ^ j : ℕ) : ℝ) ∧
               ((2 ^ j : ℕ) : ℝ) ≤ |T| ^ (1 / ((k : ℝ) - 3 / 2)) := by
        by_cases h2 : |T| ^ (2 / 3 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
        · refine ⟨2, mem_Icc.mpr ⟨le_rfl, by omega⟩, ?_⟩
          simp only [↓reduceIte]; exact ⟨h2, hA_hi⟩
        · push Not at h2
          let P : ℕ → Prop := fun k => 3 ≤ k ∧ k ≤ K ∧ |T| ^ (1 / ((k : ℝ) - 1 / 2)) ≤ ((2 ^ j : ℕ) : ℝ)
          have hPK : P K := ⟨hK, le_rfl, hA_lo⟩
          let k0 := Nat.find (⟨K, hPK⟩ : ∃ k, P k)
          have hk0_spec : P k0 := Nat.find_spec (⟨K, hPK⟩ : ∃ k, P k)
          refine ⟨k0, mem_Icc.mpr ⟨by omega, hk0_spec.2.1⟩, ?_⟩
          rw [if_neg (by omega)]
          refine ⟨hk0_spec.2.2, ?_⟩
          by_cases hk3 : k0 = 3
          · rw [hk3]
            have heq : (1 : ℝ) / (((3 : ℕ) : ℝ) - 3 / 2) = 2 / 3 := by norm_num
            rw [heq]; exact h2.le
          · have hnot : ¬ P (k0 - 1) := Nat.find_min (⟨K, hPK⟩ : ∃ k, P k) (by omega)
            have hlt : ((2 ^ j : ℕ) : ℝ) < |T| ^ (1 / (((k0 - 1 : ℕ) : ℝ) - 1 / 2)) := by
              by_contra hge; push Not at hge; exact hnot ⟨by omega, by omega, hge⟩
            have heq : ((k0 - 1 : ℕ) : ℝ) - 1 / 2 = (k0 : ℝ) - 3 / 2 := by
              rw [Nat.cast_sub (by omega : 1 ≤ k0)]; norm_num; ring
            rw [heq] at hlt
            exact hlt.le
      obtain ⟨k, hkS, hk_rng⟩ := hex_k
      have hT_ge_Tf : Tf k hkS ≤ |T| := by
        have h1 : Tf k hkS ≤ ∑ k' ∈ S_k, if hk' : k' ∈ S_k then Tf k' hk' else 0 := by
          have := single_le_sum
            (f := fun k' => if hk' : k' ∈ S_k then Tf k' hk' else 0)
            (fun k' hk' => by simp only [hk', ↓reduceDIte]; linarith [hTf k' hk']) hkS
          simpa only [hkS, ↓reduceDIte] using this
        exact le_trans h1 (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hT)))
      have hres := hbd_f k hkS hr.1 hr.2 hσ hT_ge_Tf hk_rng
      have hCf_le : Cf k hkS ≤ Cmax := by
        have := single_le_sum
          (f := fun k' => if hk' : k' ∈ S_k then Cf k' hk' else 0)
          (fun k' hk' => by simp only [hk', ↓reduceDIte]; exact hCf k' hk') hkS
        simpa only [hkS, ↓reduceDIte] using this
      have hη_ge : ηmin ≤ ηf k hkS := by
        have := Finset.inf'_le (f := fun k' => if hk' : k' ∈ S_k then ηf k' hk' else 1) hkS
        simpa only [hkS, ↓reduceDIte] using this
      have hpow_le : |T| ^ (-ηf k hkS) ≤ |T| ^ (-ηmin) :=
        Real.rpow_le_rpow_of_exponent_le hT_ge1 (by linarith)
      exact hres.trans (mul_le_mul hCf_le hpow_le (Real.rpow_nonneg hT_gt0.le _) hCmax_nn)
    have hcard_J : ((Ico J0 J1).card : ℝ) ≤ 4 * Real.log |T| := by
      rw [Nat.card_Ico]
      by_cases hJ : J1 ≤ J0
      · have : J1 - J0 = 0 := by omega
        rw [this, Nat.cast_zero]; exact mul_nonneg (by norm_num) (Real.log_nonneg hT_ge1)
      · push Not at hJ
        have hJ1_eq : J1 = Nat.clog 2 ⌈|T| ^ (2 : ℝ)⌉₊ := by dsimp [J1] at hJ ⊢; omega
        have hpow_lt : 2 ^ (J1 - 1) < ⌈|T| ^ (2 : ℝ)⌉₊ := by
          rw [hJ1_eq]
          exact Nat.pow_pred_clog_lt_self (by norm_num) (by
            have : (2 : ℝ) ≤ |T| ^ (2 : ℝ) := by
              have : (2 : ℝ) ≤ |T| * |T| := by nlinarith
              simpa [Real.rpow_two, sq] using this
            have : (2 : ℝ) ≤ (⌈|T| ^ (2 : ℝ)⌉₊ : ℝ) := this.trans (Nat.le_ceil _)
            have : 2 ≤ ⌈|T| ^ (2 : ℝ)⌉₊ := by exact_mod_cast this
            omega)
        have hltR : (2 : ℝ) ^ (J1 - 1) < |T| ^ (2 : ℝ) := by exact_mod_cast Nat.lt_ceil.mp hpow_lt
        have hlog_lt := Real.log_lt_log (by positivity) hltR
        rw [Real.log_pow, Real.log_rpow hT_gt0] at hlog_lt
        have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
        have hJ1_sub : ((J1 - 1 : ℕ) : ℝ) ≤ 4 * Real.log |T| := by nlinarith [Real.log_nonneg hT_ge1]
        have hJ0_ge1 : 1 ≤ J0 := by
          have : (2 : ℝ) ≤ (⌈X0⌉₊ : ℝ) := hX0_ge2.trans (Nat.le_ceil _)
          have : 2 ≤ ⌈X0⌉₊ := by exact_mod_cast this
          have h1 : 1 ≤ Nat.clog 2 2 := by decide
          exact h1.trans (Nat.clog_mono_right 2 this)
        exact (Nat.cast_le.mpr (by omega : J1 - J0 ≤ J1 - 1)).trans hJ1_sub
    have hlog_rpow : Real.log |T| ≤ (2 / ηmin) * |T| ^ (ηmin / 2) := by
      have h1 : Real.log (|T| ^ (ηmin / 2)) ≤ |T| ^ (ηmin / 2) :=
        (Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hT_gt0 _)).trans (by linarith)
      rw [Real.log_rpow hT_gt0] at h1
      have h2 : Real.log |T| = (2 / ηmin) * ((ηmin / 2) * Real.log |T|) := by field_simp [hηmin_pos.ne']
      rw [h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have hT_half : 4 * (q : ℝ) * (Cmax + 1) / ηmin + 10 ≤ |T| ^ (ηmin / 2) := by
      have hbase : (4 * (q : ℝ) * (Cmax + 1) / ηmin + 10) ^ (2 / ηmin) ≤ |T| := by
        have h1 : (4 * (q : ℝ) * (Cmax + 1) / ηmin + 10) ^ (2 / ηmin) + 100 ≤ Tmax := le_max_right _ _
        have h2 : Tmax ≤ |T| := le_trans (le_max_left _ _) hT
        linarith
      calc 4 * (q : ℝ) * (Cmax + 1) / ηmin + 10
          = ((4 * (q : ℝ) * (Cmax + 1) / ηmin + 10) ^ (2 / ηmin)) ^ (ηmin / 2) := by
            rw [← Real.rpow_mul (by positivity)]
            have : (2 / ηmin) * (ηmin / 2) = 1 := by field_simp [hηmin_pos.ne']
            rw [this, Real.rpow_one]
        _ ≤ |T| ^ (ηmin / 2) := Real.rpow_le_rpow (by positivity) hbase (by positivity)
    have hprod_le2 : (q : ℝ) * (4 * Real.log |T|) * (Cmax * |T| ^ (-ηmin)) ≤ 2 := by
      have hsplit_p : |T| ^ (ηmin / 2) * |T| ^ (-ηmin) = (|T| ^ (ηmin / 2))⁻¹ := by
        rw [← Real.rpow_add hT_gt0, ← Real.rpow_neg hT_gt0.le]; congr 1; ring
      have h2mul : 2 * (4 * (q : ℝ) * (Cmax + 1) / ηmin + 10) =
          8 * (q : ℝ) * (Cmax + 1) / ηmin + 20 := by ring
      calc (q : ℝ) * (4 * Real.log |T|) * (Cmax * |T| ^ (-ηmin))
          ≤ (q : ℝ) * (4 * ((2 / ηmin) * |T| ^ (ηmin / 2))) * ((Cmax + 1) * |T| ^ (-ηmin)) := by
            have h1 : Real.log |T| ≤ (2 / ηmin) * |T| ^ (ηmin / 2) := hlog_rpow
            have h2 : Cmax * |T| ^ (-ηmin) ≤ (Cmax + 1) * |T| ^ (-ηmin) :=
              mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hT_gt0.le _)
            gcongr
        _ = (8 * (q : ℝ) * (Cmax + 1) / ηmin) * (|T| ^ (ηmin / 2) * |T| ^ (-ηmin)) := by ring
        _ = (8 * (q : ℝ) * (Cmax + 1) / ηmin) / |T| ^ (ηmin / 2) := by rw [hsplit_p, ← div_eq_mul_inv]
        _ ≤ (8 * (q : ℝ) * (Cmax + 1) / ηmin) / (4 * (q : ℝ) * (Cmax + 1) / ηmin + 10) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hT_half
        _ ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith
    calc ‖∑ r ∈ Icc 1 q, χ (r : ZMod q) *
            ∑ j ∈ Ico J0 J1,
              ∑ m ∈ Icc 1 (2 ^ j),
                (((q * (2 ^ j + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T)))‖
        ≤ ∑ r ∈ Icc 1 q, ‖χ (r : ZMod q) *
            ∑ j ∈ Ico J0 J1,
              ∑ m ∈ Icc 1 (2 ^ j),
                (((q * (2 ^ j + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T)))‖ := norm_sum_le _ _
      _ ≤ ∑ r ∈ Icc 1 q, ∑ j ∈ Ico J0 J1,
            ‖∑ m ∈ Icc 1 (2 ^ j),
              (((q * (2 ^ j + m) + r : ℕ) : ℂ) ^ (-(σ + Complex.I * T)))‖ := by
          refine sum_le_sum fun r _ => ?_
          rw [norm_mul]
          exact (mul_le_of_le_one_left (norm_nonneg _) (dirichlet_norm_le_one χ (r : ZMod q))).trans (norm_sum_le _ _)
      _ ≤ ∑ _r ∈ Icc 1 q, ∑ _j ∈ Ico J0 J1, (Cmax * |T| ^ (-ηmin)) :=
          sum_le_sum fun r hr => sum_le_sum fun j hj => hblock r hr j hj
      _ = (q : ℝ) * ((Ico J0 J1).card : ℝ) * (Cmax * |T| ^ (-ηmin)) := by
          simp [Nat.card_Icc, show q + 1 - 1 = q by omega, mul_assoc]
      _ ≤ (q : ℝ) * (4 * Real.log |T|) * (Cmax * |T| ^ (-ηmin)) := by
          have hnn : 0 ≤ Cmax * |T| ^ (-ηmin) := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard_J hqpos.le) hnn
      _ ≤ 2 := hprod_le2
  have htail_bd : ‖∑' k : ℕ, f (q * (A1 + 1) + 1 + k)‖ ≤ 10 * (q : ℝ) :=
    norm_dirichletL_tail χ hσ hσ2 hT_ge1 hA1_ge_T2
  change ‖∑' n : ℕ, f n‖ ≤ (2 / (K : ℝ)) * Real.log |T| + (10 * (q : ℝ) + Real.log (q : ℝ) + 20)
  rw [hsplit_head_rest]
  calc ‖(∑ n ∈ Icc 1 (q * (A0 + 1)), f n) +
        (∑ n ∈ Icc (q * (A0 + 1) + 1) (q * (A1 + 1)), f n) +
        (∑' k : ℕ, f (q * (A1 + 1) + 1 + k))‖
      ≤ ‖(∑ n ∈ Icc 1 (q * (A0 + 1)), f n) +
          (∑ n ∈ Icc (q * (A0 + 1) + 1) (q * (A1 + 1)), f n)‖ +
        ‖∑' k : ℕ, f (q * (A1 + 1) + 1 + k)‖ := norm_add_le _ _
    _ ≤ ‖∑ n ∈ Icc 1 (q * (A0 + 1)), f n‖ +
        ‖∑ n ∈ Icc (q * (A0 + 1) + 1) (q * (A1 + 1)), f n‖ +
        ‖∑' k : ℕ, f (q * (A1 + 1) + 1 + k)‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((2 / (K : ℝ)) * Real.log |T| + Real.log (q : ℝ) + 4) + 2 + 10 * (q : ℝ) := by linarith
    _ ≤ (2 / (K : ℝ)) * Real.log |T| + (10 * (q : ℝ) + Real.log (q : ℝ) + 20) := by linarith
end

section
open Filter Finset Complex Real MeasureTheory
open scoped BigOperators Topology
private lemma sum_union_le_add {α : Type*} [DecidableEq α] {s t : Finset α} {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ (∑ x ∈ s, f x) + ∑ x ∈ t, f x := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have hnn : 0 ≤ ∑ x ∈ s ∩ t, f x := sum_nonneg fun x _ => hf x
  linarith
private lemma sum_biUnion_le_sum {α β : Type*} [DecidableEq β] {s : Finset α} {t : α → Finset β}
    {f : β → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, sum_insert ha]
    exact (sum_union_le_add hf).trans (add_le_add le_rfl ih)
private lemma norm_exp_neg_I_mul (r : ℝ) : ‖Complex.exp (-Complex.I * (r : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (-Complex.I * (r : ℂ)).re = 0 := by simp
  rw [hre, Real.exp_zero]
private lemma norm_exp_I_mul (r : ℝ) : ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.I * (r : ℂ)).re = 0 := by simp
  rw [hre, Real.exp_zero]
private lemma star_exp_I_mul (r : ℝ) :
    star (Complex.exp (Complex.I * (r : ℂ))) = Complex.exp (-Complex.I * (r : ℂ)) := by
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_I, Complex.conj_ofReal]
lemma theta_dyadic_card_le {j : ℕ} (hj : 1 ≤ j) :
    (((Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime).card : ℝ) ≤
      (4 : ℝ) * (2 : ℝ) ^ j / (j : ℝ) := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htheta_ub := Chebyshev.theta_le_log4_mul_x (x := ((2 ^ (j + 1) : ℕ) : ℝ)) (Nat.cast_nonneg _)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  have htheta_lb : (((Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime).card : ℝ) *
      ((j : ℝ) * Real.log 2) ≤ Chebyshev.theta ((2 ^ (j + 1) : ℕ) : ℝ) := by
    unfold Chebyshev.theta
    have hsub : (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime ⊆
        (Finset.Iic ⌊((2 ^ (j + 1) : ℕ) : ℝ)⌋₊).filter Nat.Prime := by
      intro p hp
      simp only [mem_filter, mem_Ioc, Finset.mem_Iic, Nat.floor_natCast] at hp ⊢
      exact ⟨hp.1.2, hp.2⟩
    have hle1 : ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, Real.log (p : ℝ) ≤
        ∑ p ∈ (Finset.Iic ⌊((2 ^ (j + 1) : ℕ) : ℝ)⌋₊).filter Nat.Prime, Real.log (p : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
        Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le)
    have hle2 : (((Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime).card : ℝ) * ((j : ℝ) * Real.log 2) ≤
        ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, Real.log (p : ℝ) := by
      calc (((Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime).card : ℝ) * ((j : ℝ) * Real.log 2)
          = ∑ _p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, ((j : ℝ) * Real.log 2) := by simp
        _ ≤ ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, Real.log (p : ℝ) := by
            refine sum_le_sum fun p hp => ?_
            have hp_gt : ((2 ^ j : ℕ) : ℝ) < (p : ℝ) := by
              exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).1
            have hlog_pow : (j : ℝ) * Real.log 2 = Real.log ((2 ^ j : ℕ) : ℝ) := by
              push_cast; rw [Real.log_pow]
            rw [hlog_pow]
            exact Real.log_le_log (by positivity) hp_gt.le
    exact hle2.trans hle1
  have hcomb : (((Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime).card : ℝ) * ((j : ℝ) * Real.log 2) ≤
      (2 * Real.log 2) * (2 * (2 : ℝ) ^ j) := by
    have hcast : ((2 ^ (j + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ j := by
      rw [pow_succ]; push_cast; ring
    rw [hlog4, hcast] at htheta_ub
    rw [hcast] at htheta_lb
    linarith
  rw [le_div_iff₀ hjpos]
  nlinarith [hlog2_pos]
lemma sum_inv_primes_le {X : ℕ} (hX : 3 ≤ X) :
    ∑ p ∈ (Icc 1 X).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      20 * Real.log (Real.log (X : ℝ)) + 20 := by
  let J : ℕ := Nat.clog 2 X
  have hX_le : X ≤ 2 ^ J := Nat.le_pow_clog (by norm_num) X
  have hJ1 : 1 ≤ J := by
    have : 1 ≤ Nat.clog 2 2 := by decide
    exact this.trans (Nat.clog_mono_right 2 (by omega))
  have hsub : (Icc 1 X).filter Nat.Prime ⊆
      ({2} : Finset ℕ) ∪ (Ico 1 J).biUnion (fun j => (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime) := by
    intro p hp
    simp only [mem_filter, mem_Icc, mem_union, Finset.mem_singleton,
      Finset.mem_biUnion, mem_Ico, mem_Ioc] at hp ⊢
    by_cases hp2 : p = 2
    · exact Or.inl hp2
    · right
      have hp3 : 3 ≤ p := by have := hp.2.two_le; omega
      let j := Nat.clog 2 p - 1
      have hclog_ge2 : 2 ≤ Nat.clog 2 p := by
        have : 2 ≤ Nat.clog 2 3 := by decide
        exact this.trans (Nat.clog_mono_right 2 hp3)
      have hj1 : 1 ≤ j := by omega
      have hjJ : j < J := by
        have : Nat.clog 2 p ≤ J := Nat.clog_mono_right 2 hp.1.2
        omega
      refine ⟨j, ⟨hj1, hjJ⟩, ⟨?_, ?_⟩, hp.2⟩
      · exact Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
      · have heq : j + 1 = Nat.clog 2 p := by omega
        rw [heq]; exact Nat.le_pow_clog (by norm_num) p
  have hsum_le : ∑ p ∈ (Icc 1 X).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      1 / 2 + ∑ j ∈ Ico 1 J,
        ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
    calc ∑ p ∈ (Icc 1 X).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
        ≤ ∑ p ∈ ({2} : Finset ℕ) ∪ (Ico 1 J).biUnion
            (fun j => (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime), (1 : ℝ) / (p : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ (∑ p ∈ ({2} : Finset ℕ), (1 : ℝ) / (p : ℝ)) +
          ∑ p ∈ (Ico 1 J).biUnion
            (fun j => (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime), (1 : ℝ) / (p : ℝ) :=
          sum_union_le_add (fun _ => by positivity)
      _ ≤ 1 / 2 + ∑ j ∈ Ico 1 J,
            ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
          simp only [Finset.sum_singleton, Nat.cast_ofNat]
          gcongr
          exact sum_biUnion_le_sum (fun _ => by positivity)
  have hblock : ∀ j ∈ Ico 1 J,
      ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤ 4 / (j : ℝ) := by
    intro j hj
    rw [mem_Ico] at hj
    have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    calc ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ)
        ≤ ∑ _p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / ((2 : ℝ) ^ j) := by
          refine sum_le_sum fun p hp => ?_
          have hp_gt : (2 : ℝ) ^ j < (p : ℝ) := by
            exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).1
          exact one_div_le_one_div_of_le h2j hp_gt.le
      _ = (((Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime).card : ℝ) / ((2 : ℝ) ^ j) := by
          simp [div_eq_mul_inv]
      _ ≤ ((4 : ℝ) * (2 : ℝ) ^ j / (j : ℝ)) / ((2 : ℝ) ^ j) :=
          div_le_div_of_nonneg_right (theta_dyadic_card_le hj.1) h2j.le
      _ = 4 / (j : ℝ) := by field_simp [h2j.ne']
  have hharm : ∑ j ∈ Ico 1 J, (4 : ℝ) / (j : ℝ) ≤ 4 * (Real.log (max 1 ((J : ℝ))) + 1) := by
    have hsubI : Ico 1 J ⊆ Icc 1 J := fun j hj => by
      simp only [mem_Ico, mem_Icc] at hj ⊢; omega
    calc ∑ j ∈ Ico 1 J, (4 : ℝ) / (j : ℝ)
        ≤ ∑ j ∈ Icc 1 J, (4 : ℝ) / (j : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hsubI (fun _ _ _ => by positivity)
      _ = 4 * ∑ j ∈ Icc 1 J, (1 : ℝ) / (j : ℝ) := by
          rw [mul_sum]; refine sum_congr rfl fun j _ => by ring
      _ ≤ 4 * (Real.log (max 1 (J : ℝ)) + 1) :=
          mul_le_mul_of_nonneg_left (harmonic_sum_le_log_add_one J) (by norm_num)
  have hlogX_ge1 : (1 : ℝ) ≤ Real.log (X : ℝ) := by
    have h3 : Real.exp 1 ≤ (X : ℝ) := by
      have he := Real.exp_one_lt_d9
      have hX3 : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      linarith
    have := Real.log_le_log (Real.exp_pos 1) h3
    rwa [Real.log_exp] at this
  have hJ_le : (J : ℝ) ≤ 4 * Real.log (X : ℝ) := by
    have h2 : 2 ^ (J - 1) < X := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
    have h2R : (2 : ℝ) ^ (J - 1) < (X : ℝ) := by exact_mod_cast h2
    have hlog := Real.log_lt_log (by positivity) h2R
    rw [Real.log_pow] at hlog
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hJsub : ((J - 1 : ℕ) : ℝ) = (J : ℝ) - 1 := by rw [Nat.cast_sub hJ1, Nat.cast_one]
    rw [hJsub] at hlog
    nlinarith
  have hmaxJ : max 1 (J : ℝ) = (J : ℝ) := max_eq_right (by exact_mod_cast hJ1)
  have hlogJ : Real.log (max 1 (J : ℝ)) ≤ Real.log 4 + Real.log (Real.log (X : ℝ)) := by
    rw [hmaxJ]
    calc Real.log (J : ℝ) ≤ Real.log (4 * Real.log (X : ℝ)) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < J)) hJ_le
      _ = Real.log 4 + Real.log (Real.log (X : ℝ)) := Real.log_mul (by norm_num) (by linarith)
  have hlog4 : Real.log 4 ≤ 2 := by
    have h1 : (4 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (1 : ℝ)
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_pos (1 : ℝ)]
    have := Real.log_le_log (by norm_num) h1
    rwa [Real.log_exp] at this
  have hloglog_nn : 0 ≤ Real.log (Real.log (X : ℝ)) := Real.log_nonneg hlogX_ge1
  have hsum_blk : ∑ j ∈ Ico 1 J,
      ∑ p ∈ (Ioc (2 ^ j) (2 ^ (j + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤
      ∑ j ∈ Ico 1 J, (4 : ℝ) / (j : ℝ) := sum_le_sum hblock
  linarith
lemma summable_primes_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-σ)) := by
  have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
    simpa [Real.rpow_neg (Nat.cast_nonneg _)] using (Real.summable_nat_rpow_inv.mpr hσ)
  exact h1.comp_injective Subtype.val_injective
lemma tsum_primes_gt_rpow_le {Y : ℕ} (hY : 3 ≤ Y) :
    ∑' p : Nat.Primes,
      (if (p : ℕ) ≤ Y then (0 : ℝ) else ((p : ℕ) : ℝ) ^ (-(1 + 1 / Real.log (Y : ℝ)))) ≤ 20 := by
  have hlogY_ge1 : (1 : ℝ) ≤ Real.log (Y : ℝ) := by
    have h3 : Real.exp 1 ≤ (Y : ℝ) := by
      have := Real.exp_one_lt_d9
      have : (3 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
      linarith
    have := Real.log_le_log (Real.exp_pos 1) h3
    rwa [Real.log_exp] at this
  have hlogY_pos : 0 < Real.log (Y : ℝ) := by linarith
  let σ : ℝ := 1 + 1 / Real.log (Y : ℝ)
  have hσ : 1 < σ := by dsimp [σ]; linarith [show (0 : ℝ) < 1 / Real.log (Y : ℝ) by positivity]
  have hfin : ∀ F : Finset Nat.Primes,
      ∑ p ∈ F, (if (p : ℕ) ≤ Y then (0 : ℝ) else ((p : ℕ) : ℝ) ^ (-σ)) ≤ 20 := by
    intro F
    let M : ℕ := F.sup (fun p => (p : ℕ)) + 1
    let K : ℕ := Nat.clog 2 M + 1
    have hK_pow : ∀ p ∈ F, (p : ℕ) ≤ 2 ^ K * Y := by
      intro p hp
      have h1 : (p : ℕ) ≤ M := Nat.le_succ_of_le (Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) hp)
      have h2 : M ≤ 2 ^ (Nat.clog 2 M) := Nat.le_pow_clog (by norm_num) M
      have h3 : 2 ^ (Nat.clog 2 M) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    have hle_nat : ∑ p ∈ F, (if (p : ℕ) ≤ Y then (0 : ℝ) else ((p : ℕ) : ℝ) ^ (-σ)) ≤
        ∑ p ∈ (Ioc Y (2 ^ K * Y)).filter Nat.Prime, (p : ℝ) ^ (-σ) := by
      rw [← Finset.sum_filter_not_add_sum_filter F (fun p : Nat.Primes => (p : ℕ) ≤ Y)]
      have hzero : ∑ p ∈ F.filter (fun p : Nat.Primes => (p : ℕ) ≤ Y),
          (if (p : ℕ) ≤ Y then (0 : ℝ) else ((p : ℕ) : ℝ) ^ (-σ)) = 0 :=
        sum_eq_zero fun p hp => if_pos (mem_filter.mp hp).2
      rw [hzero, add_zero]
      have hrew : ∑ p ∈ F.filter (fun p : Nat.Primes => ¬ (p : ℕ) ≤ Y),
          (if (p : ℕ) ≤ Y then (0 : ℝ) else ((p : ℕ) : ℝ) ^ (-σ)) =
          ∑ p ∈ F.filter (fun p : Nat.Primes => ¬ (p : ℕ) ≤ Y), ((p : ℕ) : ℝ) ^ (-σ) :=
        sum_congr rfl fun p hp => if_neg (mem_filter.mp hp).2
      rw [hrew]
      have himg : ∑ p ∈ F.filter (fun p : Nat.Primes => ¬ (p : ℕ) ≤ Y), ((p : ℕ) : ℝ) ^ (-σ) =
          ∑ n ∈ (F.filter (fun p : Nat.Primes => ¬ (p : ℕ) ≤ Y)).image (fun p : Nat.Primes => (p : ℕ)),
            (n : ℝ) ^ (-σ) := by
        symm
        exact sum_image (f := fun n : ℕ => (n : ℝ) ^ (-σ))
          (fun _ _ _ _ h => Subtype.ext h)
      rw [himg]
      refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨p, hp, rfl⟩
      rw [mem_filter] at hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, hK_pow p hp.1⟩, p.prop⟩
    have hpart : (Ioc Y (2 ^ K * Y)).filter Nat.Prime ⊆
        (Finset.range K).biUnion (fun j => (Ioc (2 ^ j * Y) (2 ^ (j + 1) * Y)).filter Nat.Prime) := by
      intro p hp
      simp only [mem_filter, mem_Ioc, Finset.mem_biUnion, mem_range] at hp ⊢
      let q0 := (p - 1) / Y
      have hq0_ge1 : 1 ≤ q0 := by dsimp [q0]; rw [Nat.le_div_iff_mul_le (by omega)]; omega
      let j := Nat.log 2 q0
      have hj_pow : 2 ^ j ≤ q0 := Nat.pow_log_le_self 2 (by omega)
      have hj_lt : q0 < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) q0
      have hj_lt_K : j < K := by
        by_contra hge; push Not at hge
        have h1 : 2 ^ K ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hge
        have h2 : 2 ^ K * Y ≤ q0 * Y := Nat.mul_le_mul_right Y (h1.trans hj_pow)
        have h3 : q0 * Y ≤ p - 1 := Nat.div_mul_le_self (p - 1) Y
        omega
      refine ⟨j, hj_lt_K, ⟨?_, ?_⟩, hp.2⟩
      · have h1 : 2 ^ j * Y ≤ q0 * Y := Nat.mul_le_mul_right Y hj_pow
        have h2 : q0 * Y ≤ p - 1 := Nat.div_mul_le_self (p - 1) Y
        omega
      · have h1 : p - 1 < (q0 + 1) * Y := by
          have := Nat.lt_mul_div_succ (p - 1) (by omega : 0 < Y); rw [mul_comm] at this; exact this
        have h2 : (q0 + 1) * Y ≤ 2 ^ (j + 1) * Y := Nat.mul_le_mul_right Y (by omega)
        omega
    have hblk : ∀ j ∈ Finset.range K,
        ∑ p ∈ (Ioc (2 ^ j * Y) (2 ^ (j + 1) * Y)).filter Nat.Prime, (p : ℝ) ^ (-σ) ≤
          (4 / (Real.exp 1 * Real.log (Y : ℝ))) * (2 ^ (-(1 / Real.log (Y : ℝ)))) ^ j := by
      intro j _
      have h2jY_pos : (0 : ℝ) < (2 : ℝ) ^ j * (Y : ℝ) := by positivity
      have htheta := Chebyshev.theta_le_log4_mul_x (x := ((2 ^ (j + 1) * Y : ℕ) : ℝ)) (Nat.cast_nonneg _)
      have hcard_le : (((Ioc (2 ^ j * Y) (2 ^ (j + 1) * Y)).filter Nat.Prime).card : ℝ) ≤
          (4 * (2 : ℝ) ^ j * (Y : ℝ)) / Real.log (Y : ℝ) := by
        have hlb : (((Ioc (2 ^ j * Y) (2 ^ (j + 1) * Y)).filter Nat.Prime).card : ℝ) * Real.log (Y : ℝ) ≤
            Chebyshev.theta ((2 ^ (j + 1) * Y : ℕ) : ℝ) := by
          unfold Chebyshev.theta
          have hsub : (Ioc (2 ^ j * Y) (2 ^ (j + 1) * Y)).filter Nat.Prime ⊆
              (Finset.Iic ⌊((2 ^ (j + 1) * Y : ℕ) : ℝ)⌋₊).filter Nat.Prime := by
            intro p hp
            simp only [mem_filter, mem_Ioc, Finset.mem_Iic, Nat.floor_natCast] at hp ⊢
            exact ⟨hp.1.2, hp.2⟩
          calc (((Ioc (2 ^ j * Y) (2 ^ (j + 1) * Y)).filter Nat.Prime).card : ℝ) * Real.log (Y : ℝ)
              = ∑ _p ∈ (Ioc (2 ^ j * Y) (2 ^ (j + 1) * Y)).filter Nat.Prime, Real.log (Y : ℝ) := by simp
            _ ≤ ∑ p ∈ (Ioc (2 ^ j * Y) (2 ^ (j + 1) * Y)).filter Nat.Prime, Real.log (p : ℝ) := by
                refine sum_le_sum fun p hp => ?_
                have hp_gt : (Y : ℝ) < (p : ℝ) := by
                  have h1 : Y ≤ 2 ^ j * Y := Nat.le_mul_of_pos_left Y (by positivity)
                  have h2 : 2 ^ j * Y < p := (mem_Ioc.mp (mem_filter.mp hp).1).1
                  exact_mod_cast (by omega : Y < p)
                exact Real.log_le_log (by positivity) hp_gt.le
            _ ≤ ∑ p ∈ (Finset.Iic ⌊((2 ^ (j + 1) * Y : ℕ) : ℝ)⌋₊).filter Nat.Prime, Real.log (p : ℝ) :=
                sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
                  Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le)
        have hlog4_le2 : Real.log 4 ≤ 2 := by
          have h1 : (4 : ℝ) ≤ Real.exp 2 := by
            have := Real.add_one_le_exp (1 : ℝ)
            rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
            nlinarith [Real.exp_pos (1 : ℝ)]
          have := Real.log_le_log (by norm_num) h1
          rwa [Real.log_exp] at this
        have hcast : ((2 ^ (j + 1) * Y : ℕ) : ℝ) = 2 * (2 : ℝ) ^ j * (Y : ℝ) := by
          rw [pow_succ]; push_cast; ring
        rw [hcast] at htheta hlb
        rw [le_div_iff₀ hlogY_pos]
        nlinarith [hlb, htheta, hlog4_le2]
      have hterm_le : ∀ p ∈ (Ioc (2 ^ j * Y) (2 ^ (j + 1) * Y)).filter Nat.Prime,
          (p : ℝ) ^ (-σ) ≤ ((2 : ℝ) ^ j * (Y : ℝ)) ^ (-σ) := by
        intro p hp
        have hp_gt : (2 : ℝ) ^ j * (Y : ℝ) < (p : ℝ) := by
          exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).1
        exact Real.rpow_le_rpow_of_nonpos h2jY_pos hp_gt.le (by linarith)
      have hpow_simp : ((2 : ℝ) ^ j * (Y : ℝ)) ^ (-σ) =
          (1 / ((2 : ℝ) ^ j * (Y : ℝ))) * (1 / Real.exp 1) * (2 ^ (-(1 / Real.log (Y : ℝ)))) ^ j := by
        dsimp [σ]
        rw [show -(1 + 1 / Real.log (Y : ℝ)) = -1 + (-(1 / Real.log (Y : ℝ))) by ring,
          Real.rpow_add h2jY_pos, Real.rpow_neg_one, Real.mul_rpow (by positivity) (by positivity)]
        have hY_exp : (Y : ℝ) ^ (-(1 / Real.log (Y : ℝ))) = 1 / Real.exp 1 := by
          rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (Y : ℝ))]
          have : Real.log (Y : ℝ) * -(1 / Real.log (Y : ℝ)) = -1 := by field_simp [hlogY_pos.ne']
          rw [this, Real.exp_neg, one_div]
        have h2_pow : ((2 : ℝ) ^ j) ^ (-(1 / Real.log (Y : ℝ))) = (2 ^ (-(1 / Real.log (Y : ℝ)))) ^ j := by
          rw [← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
            ← Real.rpow_natCast (2 ^ (-(1 / Real.log (Y : ℝ)))) j,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1; ring
        rw [hY_exp, h2_pow, one_div]; ring
      calc ∑ p ∈ (Ioc (2 ^ j * Y) (2 ^ (j + 1) * Y)).filter Nat.Prime, (p : ℝ) ^ (-σ)
          ≤ ∑ _p ∈ (Ioc (2 ^ j * Y) (2 ^ (j + 1) * Y)).filter Nat.Prime, ((2 : ℝ) ^ j * (Y : ℝ)) ^ (-σ) :=
            sum_le_sum hterm_le
        _ = (((Ioc (2 ^ j * Y) (2 ^ (j + 1) * Y)).filter Nat.Prime).card : ℝ) *
              ((2 : ℝ) ^ j * (Y : ℝ)) ^ (-σ) := by simp
        _ ≤ ((4 * (2 : ℝ) ^ j * (Y : ℝ)) / Real.log (Y : ℝ)) *
              ((1 / ((2 : ℝ) ^ j * (Y : ℝ))) * (1 / Real.exp 1) * (2 ^ (-(1 / Real.log (Y : ℝ)))) ^ j) := by
            rw [hpow_simp]; exact mul_le_mul_of_nonneg_right hcard_le (by positivity)
        _ = (4 / (Real.exp 1 * Real.log (Y : ℝ))) * (2 ^ (-(1 / Real.log (Y : ℝ)))) ^ j := by
            field_simp [h2jY_pos.ne', hlogY_pos.ne', (Real.exp_pos 1).ne']
    let r : ℝ := 2 ^ (-(1 / Real.log (Y : ℝ)))
    have hr_lt1 : r < 1 := by
      dsimp [r]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr (by positivity))
    have hr_nn : 0 ≤ r := by dsimp [r]; positivity
    have h1_sub_r : (1 / 4 : ℝ) / Real.log (Y : ℝ) ≤ 1 - r := by
      let u : ℝ := Real.log 2 / Real.log (Y : ℝ)
      have hu_pos : 0 < u := div_pos (Real.log_pos (by norm_num)) hlogY_pos
      have hu_le1 : u ≤ 1 := by
        dsimp [u]; rw [div_le_one hlogY_pos]; linarith [Real.log_two_lt_d9]
      have hr_eq : r = Real.exp (-u) := by
        dsimp [r, u]; rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
      have hexp_le : Real.exp (-u) ≤ 1 / (1 + u) := by
        rw [Real.exp_neg, one_div]
        exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp u])
      have h1u : u / 2 ≤ 1 - 1 / (1 + u) := by
        have h1 : 1 - 1 / (1 + u) = u / (1 + u) := by field_simp [(by linarith : 1 + u ≠ 0)]; ring
        rw [h1]; exact div_le_div_of_nonneg_left hu_pos.le (by linarith) (by linarith)
      have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hu_ge : (1 / 2 : ℝ) / Real.log (Y : ℝ) ≤ u :=
        div_le_div_of_nonneg_right hlog2_ge hlogY_pos.le
      have hdiv2 : (1 / 4 : ℝ) / Real.log (Y : ℝ) = ((1 / 2 : ℝ) / Real.log (Y : ℝ)) / 2 := by ring
      rw [hr_eq]; linarith
    have hgeom : ∑ j ∈ Finset.range K, r ^ j ≤ 1 / (1 - r) := by
      rw [geom_sum_eq hr_lt1.ne]
      have heq : (r ^ K - 1) / (r - 1) = (1 - r ^ K) / (1 - r) := by
        have hne : 1 - r ≠ 0 := by linarith
        field_simp [hne, (by linarith : r - 1 ≠ 0)]; ring
      rw [heq]
      exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr_nn K]) (by linarith)
    calc ∑ p ∈ F, (if (p : ℕ) ≤ Y then (0 : ℝ) else ((p : ℕ) : ℝ) ^ (-σ))
        ≤ ∑ p ∈ (Ioc Y (2 ^ K * Y)).filter Nat.Prime, (p : ℝ) ^ (-σ) := hle_nat
      _ ≤ ∑ p ∈ (Finset.range K).biUnion
            (fun j => (Ioc (2 ^ j * Y) (2 ^ (j + 1) * Y)).filter Nat.Prime), (p : ℝ) ^ (-σ) :=
          sum_le_sum_of_subset_of_nonneg hpart (fun _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ ∑ j ∈ Finset.range K,
            ∑ p ∈ (Ioc (2 ^ j * Y) (2 ^ (j + 1) * Y)).filter Nat.Prime, (p : ℝ) ^ (-σ) :=
          sum_biUnion_le_sum (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ ∑ j ∈ Finset.range K, (4 / (Real.exp 1 * Real.log (Y : ℝ))) * r ^ j :=
          sum_le_sum hblk
      _ = (4 / (Real.exp 1 * Real.log (Y : ℝ))) * ∑ j ∈ Finset.range K, r ^ j := (mul_sum _ _ _).symm
      _ ≤ (4 / (Real.exp 1 * Real.log (Y : ℝ))) * (1 / (1 - r)) :=
          mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ ≤ (4 / (Real.exp 1 * Real.log (Y : ℝ))) * (1 / ((1 / 4 : ℝ) / Real.log (Y : ℝ))) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) h1_sub_r) (by positivity)
      _ = 16 / Real.exp 1 := by field_simp [hlogY_pos.ne', (Real.exp_pos 1).ne']; ring
      _ ≤ 20 := by
          have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
          rw [div_le_iff₀ (Real.exp_pos 1)]; linarith
  exact Real.tsum_le_of_sum_le (fun p => by split_ifs <;> positivity) hfin
lemma norm_inv_one_sub_ge_exp {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    Real.exp (w.re - ‖w‖ ^ 2) ≤ ‖(1 - w)⁻¹‖ := by
  have h1w_ne : 1 - w ≠ 0 := by
    intro h
    have : w = 1 := (sub_eq_zero.mp h).symm
    rw [this, norm_one] at hw; linarith
  have hsq : ‖1 - w‖ ^ 2 = 1 - 2 * w.re + ‖w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub, neg_mul,
      mul_neg, neg_neg]
    ring
  have hexp_ge : ‖1 - w‖ ^ 2 ≤ Real.exp (-2 * w.re + ‖w‖ ^ 2) := by
    rw [hsq]; linarith [Real.add_one_le_exp (-2 * w.re + ‖w‖ ^ 2)]
  have hnorm_le : ‖1 - w‖ ≤ Real.exp (-w.re + ‖w‖ ^ 2 / 2) := by
    have h1 := Real.sqrt_le_sqrt hexp_ge
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_eq_rpow, ← Real.exp_mul] at h1
    convert h1 using 2; ring
  have hnorm_le2 : ‖1 - w‖ ≤ Real.exp (-(w.re - ‖w‖ ^ 2)) :=
    hnorm_le.trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖w‖]))
  rw [norm_inv]
  have hinv_eq : Real.exp (w.re - ‖w‖ ^ 2) = (Real.exp (-(w.re - ‖w‖ ^ 2)))⁻¹ := by
    rw [Real.exp_neg, inv_inv]
  rw [hinv_eq]
  exact inv_anti₀ (norm_pos_iff.mpr h1w_ne) hnorm_le2
lemma norm_inv_one_sub_le_exp {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖(1 - w)⁻¹‖ ≤ Real.exp (w.re + 2 * ‖w‖ ^ 2) := by
  have hre_le : w.re ≤ 1 / 2 := (Complex.re_le_norm w).trans hw
  have hre_ge : -(1 / 2 : ℝ) ≤ w.re := by linarith [(abs_le.mp ((Complex.abs_re_le_norm w).trans hw)).1]
  have h1_sub_re_pos : 0 < 1 - w.re := by linarith
  have hpoly : (1 : ℝ) ≤ (1 + w.re + 2 * w.re ^ 2) * (1 - w.re) := by
    have : (1 + w.re + 2 * w.re ^ 2) * (1 - w.re) - 1 = w.re ^ 2 * (1 - 2 * w.re) := by ring
    nlinarith [sq_nonneg w.re]
  have hexp_ge : 1 ≤ Real.exp (w.re + 2 * w.re ^ 2) * (1 - w.re) := by
    have h1 := Real.add_one_le_exp (w.re + 2 * w.re ^ 2); nlinarith
  have h1w_ge : Real.exp (-(w.re + 2 * ‖w‖ ^ 2)) ≤ ‖1 - w‖ := by
    have hre_sq : w.re ^ 2 ≤ ‖w‖ ^ 2 := by
      rw [← sq_abs w.re]
      exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm w) 2
    have h1 : Real.exp (-(w.re + 2 * ‖w‖ ^ 2)) ≤ Real.exp (-(w.re + 2 * w.re ^ 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-(w.re + 2 * w.re ^ 2)) ≤ 1 - w.re := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) h1_sub_re_pos,
        inv_le_iff_one_le_mul₀' h1_sub_re_pos]
      linarith
    have h3 : 1 - w.re ≤ ‖1 - w‖ := by
      have : (1 - w).re = 1 - w.re := by simp
      rw [← this]; exact Complex.re_le_norm _
    exact h1.trans (h2.trans h3)
  rw [norm_inv]
  have := inv_anti₀ (Real.exp_pos _) h1w_ge
  rwa [Real.exp_neg, inv_inv] at this
lemma tsum_primes_inv_sq_le_two :
    ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) ≤ 2 := by
  refine Real.tsum_le_of_sum_le (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) fun F => ?_
  let M : ℕ := F.sup (fun p => (p : ℕ)) + 2
  have himg : ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-2 : ℝ) =
      ∑ n ∈ F.image (fun p : Nat.Primes => (p : ℕ)), (n : ℝ) ^ (-2 : ℝ) := by
    symm
    exact sum_image (f := fun n : ℕ => (n : ℝ) ^ (-2 : ℝ))
      (fun _ _ _ _ h => Subtype.ext h)
  rw [himg]
  have hsub : F.image (fun p : Nat.Primes => (p : ℕ)) ⊆ Icc 2 M := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨p, hp, rfl⟩
    exact mem_Icc.mpr ⟨p.prop.two_le, le_trans (Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) hp) (by omega)⟩
  calc ∑ n ∈ F.image (fun p : Nat.Primes => (p : ℕ)), (n : ℝ) ^ (-2 : ℝ)
      ≤ ∑ n ∈ Icc 2 M, (n : ℝ) ^ (-2 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ ∑ n ∈ Icc 2 M, (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ)) := by
        refine sum_le_sum fun n hn => ?_
        rw [mem_Icc] at hn
        have hn1 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
        have hn2 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hpow : (n : ℝ) ^ (-2 : ℝ) = 1 / (n : ℝ) ^ 2 := by
          rw [Real.rpow_neg hn2.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
        rw [hpow]
        have hdiff : 1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ) = 1 / (((n - 1 : ℕ) : ℝ) * (n : ℝ)) := by
          have hs : (n : ℝ) - ((n - 1 : ℕ) : ℝ) = 1 := by rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
          field_simp [hn1.ne', hn2.ne']; linarith
        rw [hdiff]
        exact one_div_le_one_div_of_le (by positivity)
          (by nlinarith [show ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) by exact_mod_cast Nat.sub_le n 1])
    _ = 1 - 1 / (M : ℝ) := by
        have htele : ∀ K : ℕ, 2 ≤ K →
            ∑ n ∈ Icc 2 K, (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ)) = 1 - 1 / (K : ℝ) := by
          intro K hK
          induction K, hK using Nat.le_induction with
          | base => simp
          | succ m hm ih =>
            have hIcc : Icc 2 (m + 1) = insert (m + 1) (Icc 2 m) := by
              ext k; simp only [mem_Icc, mem_insert]; omega
            rw [hIcc, sum_insert (by simp), ih]
            simp only [Nat.add_sub_cancel]; ring
        exact htele M (by omega)
    _ ≤ 2 := by linarith [show (0 : ℝ) ≤ 1 / (M : ℝ) by positivity]
lemma euler_norm_bounds {f : ℕ →*₀ ℂ} {σ : ℝ} (hσ : 1 < σ)
    (hbd : ∀ n : ℕ, 1 ≤ n → ‖f n‖ ≤ (n : ℝ) ^ (-σ)) :
    Real.exp ((∑' p : Nat.Primes, (f p).re) - 2) ≤ ‖∑' n : ℕ, f n‖ ∧
    ‖∑' n : ℕ, f n‖ ≤ Real.exp ((∑' p : Nat.Primes, (f p).re) + 4) := by
  have hsum_f : Summable (fun n => ‖f n‖) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
      simpa [Real.rpow_neg (Nat.cast_nonneg _)] using (Real.summable_nat_rpow_inv.mpr hσ)
    refine h1.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp [map_zero, Real.zero_rpow (by linarith : -σ ≠ 0)]
    · exact hbd n (by omega)
  have heuler := EulerProduct.eulerProduct_completely_multiplicative hsum_f
  have hfp_half : ∀ p : Nat.Primes, ‖f p‖ ≤ 1 / 2 := by
    intro p
    have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.two_le
    calc ‖f p‖ ≤ ((p : ℕ) : ℝ) ^ (-σ) := hbd p p.prop.one_le
      _ ≤ (2 : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one, one_div]
  have hprod_bounds : ∀ N : ℕ,
      Real.exp ((∑ p ∈ N.primesBelow, (f p).re) - 2) ≤ ‖∏ p ∈ N.primesBelow, (1 - f p)⁻¹‖ ∧
      ‖∏ p ∈ N.primesBelow, (1 - f p)⁻¹‖ ≤ Real.exp ((∑ p ∈ N.primesBelow, (f p).re) + 4) := by
    intro N
    rw [norm_prod]
    have hsq_le2 : ∑ p ∈ N.primesBelow, ‖f p‖ ^ 2 ≤ 2 := by
      have hsub : ∑ p ∈ N.primesBelow, ‖f p‖ ^ 2 ≤ ∑ p ∈ N.primesBelow, ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
        refine sum_le_sum fun p hp => ?_
        have hp_p := Nat.prime_of_mem_primesBelow hp
        have h1 : ‖f p‖ ≤ (p : ℝ) ^ (-1 : ℝ) :=
          (hbd p hp_p.one_le).trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp_p.one_le) (by linarith))
        have h2 : ((p : ℝ) ^ (-1 : ℝ)) ^ 2 = (p : ℝ) ^ (-2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
        rw [← h2]; exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      have hlift : ∑ p ∈ N.primesBelow, ((p : ℕ) : ℝ) ^ (-2 : ℝ) ≤
          ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
        let S : Finset Nat.Primes := N.primesBelow.attach.map
          ⟨fun p => ⟨p.1, Nat.prime_of_mem_primesBelow p.2⟩,
           fun _ _ h => Subtype.ext (by injection h)⟩
        have heqS : ∑ p ∈ S, ((p : ℕ) : ℝ) ^ (-2 : ℝ) = ∑ p ∈ N.primesBelow, ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
          rw [sum_map]
          exact sum_attach N.primesBelow (fun p => ((p : ℕ) : ℝ) ^ (-2 : ℝ))
        rw [← heqS]
        exact Summable.sum_le_tsum S (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (summable_primes_rpow (by norm_num))
      exact hsub.trans (hlift.trans tsum_primes_inv_sq_le_two)
    constructor
    · calc Real.exp ((∑ p ∈ N.primesBelow, (f p).re) - 2)
          ≤ Real.exp (∑ p ∈ N.primesBelow, ((f p).re - ‖f p‖ ^ 2)) := by
            rw [sum_sub_distrib]; exact Real.exp_le_exp.mpr (by linarith)
        _ = ∏ p ∈ N.primesBelow, Real.exp ((f p).re - ‖f p‖ ^ 2) := Real.exp_sum _ _
        _ ≤ ∏ p ∈ N.primesBelow, ‖(1 - f p)⁻¹‖ :=
            prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun p hp =>
              norm_inv_one_sub_ge_exp (hfp_half ⟨p, Nat.prime_of_mem_primesBelow hp⟩)
    · calc ∏ p ∈ N.primesBelow, ‖(1 - f p)⁻¹‖
          ≤ ∏ p ∈ N.primesBelow, Real.exp ((f p).re + 2 * ‖f p‖ ^ 2) :=
            prod_le_prod (fun _ _ => norm_nonneg _) fun p hp =>
              norm_inv_one_sub_le_exp (hfp_half ⟨p, Nat.prime_of_mem_primesBelow hp⟩)
        _ = Real.exp (∑ p ∈ N.primesBelow, ((f p).re + 2 * ‖f p‖ ^ 2)) := (Real.exp_sum _ _).symm
        _ ≤ Real.exp ((∑ p ∈ N.primesBelow, (f p).re) + 4) := by
            rw [sum_add_distrib, ← mul_sum]
            exact Real.exp_le_exp.mpr (by linarith)
  have htend_re : Tendsto (fun N : ℕ => ∑ p ∈ N.primesBelow, (f p).re) atTop
      (𝓝 (∑' p : Nat.Primes, (f p).re)) := by
    have hsum_nat : Summable (fun n : ℕ => if n.Prime then (f n).re else 0) := by
      have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
        simpa [Real.rpow_neg (Nat.cast_nonneg _)] using (Real.summable_nat_rpow_inv.mpr hσ)
      refine h1.of_norm_bounded fun n => ?_
      by_cases hn : n.Prime
      · rw [if_pos hn, Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hbd n hn.one_le)
      · rw [if_neg hn, norm_zero]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    have htsum_eq : ∑' p : Nat.Primes, (f p).re = ∑' n : ℕ, if n.Prime then (f n).re else 0 := by
      have hsub := tsum_subtype_eq_of_support_subset
        (f := fun n : ℕ => if n.Prime then (f n).re else 0)
        (s := {n : ℕ | n.Prime}) (fun n hn => by
          simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hn
          exact hn.1)
      rw [← hsub]
      refine tsum_congr fun p => (if_pos p.prop).symm
    rw [htsum_eq]
    have ht := hsum_nat.hasSum.tendsto_sum_nat
    refine ht.congr fun N => ?_
    rw [← sum_filter]; rfl
  have htend_norm := heuler.norm
  constructor
  · exact le_of_tendsto_of_tendsto
      (Real.continuous_exp.continuousAt.tendsto.comp (htend_re.sub (tendsto_const_nhds (x := (2 : ℝ)))))
      htend_norm (Eventually.of_forall fun N => (hprod_bounds N).1)
  · exact le_of_tendsto_of_tendsto htend_norm
      (Real.continuous_exp.continuousAt.tendsto.comp (htend_re.add (tendsto_const_nhds (x := (4 : ℝ)))))
      (Eventually.of_forall fun N => (hprod_bounds N).2)
lemma tsum_primes_rpow_ge {σ : ℝ} (hσ : 1 < σ) :
    Real.log (1 / (σ - 1)) - 4 ≤ ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ) := by
  let f : ℕ →*₀ ℂ :=
    { toFun := fun n => if n = 0 then 0 else (((n : ℝ) ^ (-σ) : ℝ) : ℂ)
      map_zero' := by simp
      map_one' := by simp
      map_mul' := fun a b => by
        by_cases ha : a = 0
        · simp [ha]
        by_cases hb : b = 0
        · simp [hb]
        rw [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb]
        rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b), Complex.ofReal_mul] }
  have hbd : ∀ n : ℕ, 1 ≤ n → ‖f n‖ ≤ (n : ℝ) ^ (-σ) := by
    intro n hn
    dsimp [f]; rw [if_neg (by omega), Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hup := (euler_norm_bounds hσ hbd).2
  have hre : (fun p : Nat.Primes => (f p).re) = fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-σ) := by
    ext p; dsimp [f]; rw [if_neg p.prop.ne_zero, Complex.ofReal_re]
  rw [hre] at hup
  have hzeta_ge : 1 / (σ - 1) ≤ ‖∑' n : ℕ, f n‖ := by
    have hsum_R : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) := by
      have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
        simpa [Real.rpow_neg (Nat.cast_nonneg _)] using (Real.summable_nat_rpow_inv.mpr hσ)
      refine h1.congr fun n => ?_
      by_cases hn : n = 0
      · subst hn; simp [Real.zero_rpow (by linarith : -σ ≠ 0)]
      · rw [if_neg hn]
    have hcast_eq : ∑' n : ℕ, f n = ((∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      refine tsum_congr fun n => ?_
      dsimp [f]; split_ifs <;> simp
    rw [hcast_eq, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun n => by split_ifs <;> positivity)]
    have hpart : ∀ N : ℕ, (1 - ((N + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) ≤
        ∑ n ∈ Finset.range (N + 1), if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ) := by
      intro N
      have h1 : ∑ n ∈ Finset.range (N + 1), (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) =
          ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-σ) := by
        rw [Finset.sum_range_succ', if_pos rfl, add_zero]
        refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
        · intro k hk; rw [mem_range] at hk; rw [mem_Icc]; omega
        · intro k1 _ k2 _ h; omega
        · intro n hn; rw [mem_Icc] at hn; exact ⟨n - 1, mem_range.mpr (by omega), by omega⟩
        · intro k _; rw [if_neg (by omega)]
      rw [h1]
      have hstep : ∀ n ∈ Icc 1 N,
          (((n : ℝ) ^ (1 - σ) - ((n + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1)) ≤ (n : ℝ) ^ (-σ) := by
        intro n hn
        rw [mem_Icc] at hn
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hderiv : ∀ x ∈ Set.uIcc (n : ℝ) ((n + 1 : ℕ) : ℝ),
            HasDerivAt (fun t : ℝ => -(t ^ (1 - σ)) / (σ - 1)) (x ^ (-σ)) x := by
          intro x hx
          have hx_pos : 0 < x := by
            rw [Set.uIcc_of_le (by push_cast; linarith)] at hx
            exact lt_of_lt_of_le hn_pos hx.1
          have h1' := (Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hx_pos.ne')).neg.div_const (σ - 1)
          have hval : -((1 - σ) * x ^ (1 - σ - 1)) / (σ - 1) = x ^ (-σ) := by
            rw [show 1 - σ - 1 = -σ by ring]
            have hne : σ - 1 ≠ 0 := by linarith
            field_simp [hne]; ring
          exact hval ▸ h1'
        have hint_c : IntervalIntegrable (fun x : ℝ => x ^ (-σ)) volume (n : ℝ) ((n + 1 : ℕ) : ℝ) := by
          refine ContinuousOn.intervalIntegrable ?_
          intro x hx
          rw [Set.uIcc_of_le (by push_cast; linarith)] at hx
          exact (Real.continuousAt_rpow_const x (-σ) (Or.inl (lt_of_lt_of_le hn_pos hx.1).ne')).continuousWithinAt
        have hint_eq := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint_c
        have hle_int : ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), x ^ (-σ) ≤
            ∫ _x in (n : ℝ)..((n + 1 : ℕ) : ℝ), (n : ℝ) ^ (-σ) :=
          intervalIntegral.integral_mono_on (by push_cast; linarith) hint_c intervalIntegrable_const
            fun x hx => Real.rpow_le_rpow_of_nonpos hn_pos hx.1 (by linarith)
        rw [intervalIntegral.integral_const, smul_eq_mul] at hle_int
        have hlen : ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 := by push_cast; ring
        rw [hlen, one_mul, hint_eq] at hle_int
        have hlhs : -(((n + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) - -((n : ℝ) ^ (1 - σ)) / (σ - 1) =
            ((n : ℝ) ^ (1 - σ) - ((n + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) := by ring
        linarith
      have htele : ∀ K : ℕ, ∑ n ∈ Icc 1 K, (((n : ℝ) ^ (1 - σ) - ((n + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1)) =
          (1 - ((K + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) := by
        intro K
        induction K with
        | zero => simp
        | succ m ih =>
          have hIcc : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
            ext k; simp only [mem_Icc, mem_insert]; omega
          rw [hIcc, sum_insert (by simp), ih]
          ring
      calc (1 - ((N + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1)
          = ∑ n ∈ Icc 1 N, (((n : ℝ) ^ (1 - σ) - ((n + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1)) := (htele N).symm
        _ ≤ ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-σ) := sum_le_sum hstep
    have ht1 : Tendsto (fun N : ℕ => (1 - ((N + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1))
        atTop (𝓝 (1 / (σ - 1))) := by
      have h0 : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) ^ (1 - σ)) atTop (𝓝 0) := by
        have htop : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
        exact (tendsto_rpow_neg_atTop (by linarith : 0 < σ - 1)).comp htop |>.congr fun N => by
          simp [show -(σ - 1) = 1 - σ by ring]
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub h0).div_const (σ - 1)
    have ht2 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ))
        atTop (𝓝 (∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ))) :=
      hsum_R.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    exact le_of_tendsto_of_tendsto ht1 ht2 (Eventually.of_forall hpart)
  have hlog_le := Real.log_le_log (by positivity : 0 < 1 / (σ - 1)) (hzeta_ge.trans hup)
  rw [Real.log_exp] at hlog_le
  linarith
lemma euler_ratio_norm_le {f₁ f₂ : ℕ →*₀ ℂ} {σ : ℝ} (hσ : 1 < σ)
    (hbd₁ : ∀ n : ℕ, 1 ≤ n → ‖f₁ n‖ ≤ (n : ℝ) ^ (-σ))
    (hbd₂ : ∀ n : ℕ, 1 ≤ n → ‖f₂ n‖ ≤ (n : ℝ) ^ (-σ)) :
    ‖∑' n : ℕ, f₁ n‖ ≤
      ‖∑' n : ℕ, f₂ n‖ * Real.exp (∑' p : Nat.Primes, 2 * ‖f₁ p - f₂ p‖) := by
  have hsum1 : Summable (fun n => ‖f₁ n‖) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
      simpa [Real.rpow_neg (Nat.cast_nonneg _)] using (Real.summable_nat_rpow_inv.mpr hσ)
    refine h1.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp [map_zero, Real.zero_rpow (by linarith : -σ ≠ 0)]
    · exact hbd₁ n (by omega)
  have hsum2 : Summable (fun n => ‖f₂ n‖) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
      simpa [Real.rpow_neg (Nat.cast_nonneg _)] using (Real.summable_nat_rpow_inv.mpr hσ)
    refine h1.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp [map_zero, Real.zero_rpow (by linarith : -σ ≠ 0)]
    · exact hbd₂ n (by omega)
  have he1 := EulerProduct.eulerProduct_completely_multiplicative hsum1
  have he2 := EulerProduct.eulerProduct_completely_multiplicative hsum2
  have hsum_diff : Summable (fun p : Nat.Primes => 2 * ‖f₁ p - f₂ p‖) := by
    refine ((summable_primes_rpow hσ).mul_left 4).of_nonneg_of_le (fun _ => by positivity) fun p => ?_
    have htri : ‖f₁ p - f₂ p‖ ≤ ‖f₁ p‖ + ‖f₂ p‖ := norm_sub_le _ _
    have h1 := hbd₁ p p.prop.one_le
    have h2 := hbd₂ p p.prop.one_le
    linarith
  have hfin : ∀ N : ℕ,
      ‖∏ p ∈ N.primesBelow, (1 - f₁ p)⁻¹‖ ≤
        ‖∏ p ∈ N.primesBelow, (1 - f₂ p)⁻¹‖ *
          Real.exp (∑' p : Nat.Primes, 2 * ‖f₁ p - f₂ p‖) := by
    intro N
    have hfp1 : ∀ p ∈ N.primesBelow, ‖f₁ p‖ ≤ 1 / 2 := by
      intro p hp
      have hp_p := Nat.prime_of_mem_primesBelow hp
      calc ‖f₁ p‖ ≤ (p : ℝ) ^ (-σ) := hbd₁ p hp_p.one_le
        _ ≤ (2 : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp_p.two_le) (by linarith)
        _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 1 / 2 := by rw [Real.rpow_neg_one, one_div]
    have hne1 : ∀ p ∈ N.primesBelow, 1 - f₁ p ≠ 0 := by
      intro p hp h
      have h1 : f₁ p = 1 := (sub_eq_zero.mp h).symm
      have hfp := hfp1 p hp
      rw [h1, norm_one] at hfp; linarith
    have hne2 : ∀ p ∈ N.primesBelow, 1 - f₂ p ≠ 0 := by
      intro p hp h
      have hp_p := Nat.prime_of_mem_primesBelow hp
      have h2eq : f₂ p = 1 := (sub_eq_zero.mp h).symm
      have h1 : ‖f₂ p‖ ≤ 1 / 2 := by
        calc ‖f₂ p‖ ≤ (p : ℝ) ^ (-σ) := hbd₂ p hp_p.one_le
          _ ≤ (2 : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp_p.two_le) (by linarith)
          _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 1 / 2 := by rw [Real.rpow_neg_one, one_div]
      rw [h2eq, norm_one] at h1; linarith
    have hfactor : ∏ p ∈ N.primesBelow, (1 - f₁ p)⁻¹ =
        (∏ p ∈ N.primesBelow, (1 - f₂ p)⁻¹) * ∏ p ∈ N.primesBelow, ((1 - f₂ p) * (1 - f₁ p)⁻¹) := by
      rw [← Finset.prod_mul_distrib]
      refine prod_congr rfl fun p hp => ?_
      rw [← mul_assoc, inv_mul_cancel₀ (hne2 p hp), one_mul]
    rw [hfactor, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_prod]
    have hstep : ∀ p ∈ N.primesBelow, ‖(1 - f₂ p) * (1 - f₁ p)⁻¹‖ ≤ Real.exp (2 * ‖f₁ p - f₂ p‖) := by
      intro p hp
      have hid : (1 - f₂ p) * (1 - f₁ p)⁻¹ = 1 + (f₁ p - f₂ p) * (1 - f₁ p)⁻¹ := by
        field_simp [hne1 p hp]; ring
      rw [hid]
      have h1_sub : 1 / 2 ≤ ‖1 - f₁ p‖ := by
        have htri := norm_sub_norm_le (1 : ℂ) (f₁ p)
        rw [norm_one] at htri
        linarith [hfp1 p hp]
      have hinv : ‖(1 - f₁ p)⁻¹‖ ≤ 2 := by
        rw [norm_inv]
        have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) h1_sub
        linarith
      calc ‖1 + (f₁ p - f₂ p) * (1 - f₁ p)⁻¹‖
          ≤ ‖(1 : ℂ)‖ + ‖(f₁ p - f₂ p) * (1 - f₁ p)⁻¹‖ := norm_add_le _ _
        _ = 1 + ‖f₁ p - f₂ p‖ * ‖(1 - f₁ p)⁻¹‖ := by rw [norm_one, norm_mul]
        _ ≤ 1 + ‖f₁ p - f₂ p‖ * 2 := by gcongr
        _ = 2 * ‖f₁ p - f₂ p‖ + 1 := by ring
        _ ≤ Real.exp (2 * ‖f₁ p - f₂ p‖) := Real.add_one_le_exp _
    calc ∏ p ∈ N.primesBelow, ‖(1 - f₂ p) * (1 - f₁ p)⁻¹‖
        ≤ ∏ p ∈ N.primesBelow, Real.exp (2 * ‖f₁ p - f₂ p‖) :=
          prod_le_prod (fun _ _ => norm_nonneg _) hstep
      _ = Real.exp (∑ p ∈ N.primesBelow, 2 * ‖f₁ p - f₂ p‖) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (∑' p : Nat.Primes, 2 * ‖f₁ p - f₂ p‖) := by
          apply Real.exp_le_exp.mpr
          let S : Finset Nat.Primes := N.primesBelow.attach.map
            ⟨fun p => ⟨p.1, Nat.prime_of_mem_primesBelow p.2⟩,
             fun _ _ h => Subtype.ext (by injection h)⟩
          have heqS : ∑ p ∈ S, 2 * ‖f₁ p - f₂ p‖ = ∑ p ∈ N.primesBelow, 2 * ‖f₁ p - f₂ p‖ := by
            rw [sum_map]
            exact sum_attach N.primesBelow (fun p => 2 * ‖f₁ p - f₂ p‖)
          rw [← heqS]
          exact Summable.sum_le_tsum S (fun _ _ => by positivity) hsum_diff
  exact le_of_tendsto_of_tendsto he1.norm (he2.norm.mul_const _) (Eventually.of_forall hfin)
lemma pretentious_triangle_pointwise {u v w : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    1 - (v * star w).re ≤ 2 * (1 - (u * star v).re) + 2 * (1 - (u * star w).re) := by
  have h1 : ∀ a b : ℂ, ‖a‖ = 1 → ‖b‖ = 1 → ‖a - b‖ ^ 2 = 2 * (1 - (a * star b).re) := by
    intro a b ha hb
    have hsq : ‖a - b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * (a * star b).re := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
        Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.star_def,
        Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add]
      ring
    rw [hsq, ha, hb]; ring
  have htri : ‖v - w‖ ≤ ‖v - u‖ + ‖u - w‖ := by
    have : v - w = (v - u) + (u - w) := by ring
    rw [this]; exact norm_add_le _ _
  have hsq_le : ‖v - w‖ ^ 2 ≤ 2 * ‖v - u‖ ^ 2 + 2 * ‖u - w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖v - u‖ - ‖u - w‖), norm_nonneg (v - w), norm_nonneg (v - u), norm_nonneg (u - w)]
  have hsym : ‖v - u‖ = ‖u - v‖ := norm_sub_rev v u
  rw [hsym, h1 v w hv hw, h1 u v hu hv, h1 u w hu hw] at hsq_le
  linarith
private lemma pretentious_prod_char_dist {X Y q q' : ℕ} [NeZero q] [NeZero q'] [NeZero (q * q')]
    (hYX : Y ≤ X) {Q : ℝ} (hqQ : (q : ℝ) ≤ Q) (hq'Q : (q' : ℝ) ≤ Q)
    {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ = 1)
    (χ : DirichletCharacter ℂ q) (t : ℝ)
    (hdist : ∑ p ∈ (Icc 1 X).filter Nat.Prime,
      (1 - (g p * star (χ (p : ZMod q)) * Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q)
    (χ' : DirichletCharacter ℂ q') (t' : ℝ)
    (hdist' : ∑ p ∈ (Icc 1 Y).filter Nat.Prime,
      (1 - (g p * star (χ' (p : ZMod q')) * Complex.exp (-Complex.I * t' * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q) :
    let ψ : DirichletCharacter ℂ (q * q') :=
      DirichletCharacter.changeLevel (Nat.dvd_mul_right q q') χ *
      star (DirichletCharacter.changeLevel (Nat.dvd_mul_left q' q) χ')
    ∑ p ∈ (Icc 1 Y).filter Nat.Prime,
      (1 - (ψ (p : ZMod (q * q')) * Complex.exp (-Complex.I * ((t' - t : ℝ) : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ) ≤
      4 * Q + 2 * Q ^ 2 := by
  intro ψ
  have hqstar_pos : 0 < q * q' := NeZero.pos (q * q')
  have hsplit : ∀ p ∈ (Icc 1 Y).filter Nat.Prime,
      (1 - (ψ (p : ZMod (q * q')) * Complex.exp (-Complex.I * ((t' - t : ℝ) : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ) ≤
        (if p ∣ q * q' then (2 : ℝ) else
          2 * (1 - (g p * star (χ (p : ZMod q)) * Complex.exp (-Complex.I * (t : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ) +
          2 * (1 - (g p * star (χ' (p : ZMod q')) * Complex.exp (-Complex.I * (t' : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ)) := by
    intro p hp
    have hp_p := (mem_filter.mp hp).2
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_p.pos
    have hp_ge1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_p.one_le
    by_cases hdvd : p ∣ q * q'
    · rw [if_pos hdvd]
      have hre_ge : -1 ≤ (ψ (p : ZMod (q * q')) * Complex.exp (-Complex.I * ((t' - t : ℝ) : ℂ) * Real.log (p : ℝ))).re := by
        have hnorm : ‖ψ (p : ZMod (q * q')) * Complex.exp (-Complex.I * ((t' - t : ℝ) : ℂ) * Real.log (p : ℝ))‖ ≤ 1 := by
          rw [norm_mul]
          have h2 : ‖Complex.exp (-Complex.I * ((t' - t : ℝ) : ℂ) * Real.log (p : ℝ))‖ = 1 := by
            rw [mul_assoc, ← Complex.ofReal_mul]; exact norm_exp_neg_I_mul _
          rw [h2, mul_one]; exact dirichlet_norm_le_one ψ _
        linarith [(abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1]
      rw [div_le_iff₀ hp_pos]; nlinarith
    · rw [if_neg hdvd]
      have hcop_s : Nat.Coprime p (q * q') := hp_p.coprime_iff_not_dvd.mpr hdvd
      have hcop_q : Nat.Coprime p q := hcop_s.coprime_dvd_right (Nat.dvd_mul_right q q')
      have hcop_q' : Nat.Coprime p q' := hcop_s.coprime_dvd_right (Nat.dvd_mul_left q' q)
      have hu_q : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime p q).mpr hcop_q
      have hu_q' : IsUnit (p : ZMod q') := (ZMod.isUnit_iff_coprime p q').mpr hcop_q'
      have hψ_val : ψ (p : ZMod (q * q')) = χ (p : ZMod q) * star (χ' (p : ZMod q')) := by
        change (DirichletCharacter.changeLevel (Nat.dvd_mul_right q q') χ (p : ZMod (q * q'))) *
          star (DirichletCharacter.changeLevel (Nat.dvd_mul_left q' q) χ' (p : ZMod (q * q'))) = _
        have hcopZ : IsCoprime (p : ℤ) (q * q' : ℕ) := by exact_mod_cast hcop_s
        have h1 : DirichletCharacter.changeLevel (Nat.dvd_mul_right q q') χ (p : ZMod (q * q')) = χ (p : ZMod q) := by
          simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd' χ (Nat.dvd_mul_right q q') hcopZ
        have h2 : DirichletCharacter.changeLevel (Nat.dvd_mul_left q' q) χ' (p : ZMod (q * q')) = χ' (p : ZMod q') := by
          simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd' χ' (Nat.dvd_mul_left q' q) hcopZ
        rw [h1, h2]
      let u : ℂ := g p
      let v : ℂ := χ (p : ZMod q) * Complex.exp (Complex.I * (t : ℂ) * Real.log (p : ℝ))
      let w : ℂ := χ' (p : ZMod q') * Complex.exp (Complex.I * (t' : ℂ) * Real.log (p : ℝ))
      have hu_n : ‖u‖ = 1 := hg p hp_p
      have hv_n : ‖v‖ = 1 := by
        dsimp [v]; rw [norm_mul, dirichlet_norm_eq_one_of_isUnit χ hu_q, mul_assoc, ← Complex.ofReal_mul,
          norm_exp_I_mul, mul_one]
      have hw_n : ‖w‖ = 1 := by
        dsimp [w]; rw [norm_mul, dirichlet_norm_eq_one_of_isUnit χ' hu_q', mul_assoc, ← Complex.ofReal_mul,
          norm_exp_I_mul, mul_one]
      have hpt := pretentious_triangle_pointwise hu_n hv_n hw_n
      have hstar_e : ∀ r : ℝ, star (Complex.exp (Complex.I * (r : ℂ) * Real.log (p : ℝ))) =
          Complex.exp (-Complex.I * (r : ℂ) * Real.log (p : ℝ)) := by
        intro r; rw [mul_assoc, ← Complex.ofReal_mul, star_exp_I_mul, Complex.ofReal_mul, mul_assoc]
      have hvw : v * star w = ψ (p : ZMod (q * q')) * Complex.exp (-Complex.I * ((t' - t : ℝ) : ℂ) * Real.log (p : ℝ)) := by
        rw [hψ_val]; dsimp [v, w]
        rw [map_mul (starRingEnd ℂ), ← Complex.star_def, hstar_e t']
        have hexp : Complex.exp (Complex.I * (t : ℂ) * Real.log (p : ℝ)) *
            Complex.exp (-Complex.I * (t' : ℂ) * Real.log (p : ℝ)) =
            Complex.exp (-Complex.I * ((t' - t : ℝ) : ℂ) * Real.log (p : ℝ)) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring
        calc χ (p : ZMod q) * Complex.exp (Complex.I * (t : ℂ) * Real.log (p : ℝ)) *
              (star (χ' (p : ZMod q')) * Complex.exp (-Complex.I * (t' : ℂ) * Real.log (p : ℝ)))
            = χ (p : ZMod q) * star (χ' (p : ZMod q')) *
              (Complex.exp (Complex.I * (t : ℂ) * Real.log (p : ℝ)) *
                Complex.exp (-Complex.I * (t' : ℂ) * Real.log (p : ℝ))) := by ring
          _ = _ := by rw [hexp]
      have huv : u * star v = g p * star (χ (p : ZMod q)) * Complex.exp (-Complex.I * (t : ℂ) * Real.log (p : ℝ)) := by
        dsimp [u, v]; rw [map_mul (starRingEnd ℂ), ← Complex.star_def, hstar_e t]; ring
      have huw : u * star w = g p * star (χ' (p : ZMod q')) * Complex.exp (-Complex.I * (t' : ℂ) * Real.log (p : ℝ)) := by
        dsimp [u, w]; rw [map_mul (starRingEnd ℂ), ← Complex.star_def, hstar_e t']; ring
      rw [hvw, huv, huw] at hpt
      have hdiv := div_le_div_of_nonneg_right hpt hp_pos.le
      linarith [show (2 * (1 - (g p * star (χ (p : ZMod q)) * Complex.exp (-Complex.I * (t : ℂ) * Real.log (p : ℝ))).re) +
          2 * (1 - (g p * star (χ' (p : ZMod q')) * Complex.exp (-Complex.I * (t' : ℂ) * Real.log (p : ℝ))).re)) / (p : ℝ) =
          2 * (1 - (g p * star (χ (p : ZMod q)) * Complex.exp (-Complex.I * (t : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ) +
          2 * (1 - (g p * star (χ' (p : ZMod q')) * Complex.exp (-Complex.I * (t' : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ) by ring]
  have h1_nonneg : ∀ p ∈ (Icc 1 X).filter Nat.Prime,
      0 ≤ (1 - (g p * star (χ (p : ZMod q)) * Complex.exp (-Complex.I * (t : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ) := by
    intro p hp
    have hp_p := (mem_filter.mp hp).2
    have hnorm : ‖g p * star (χ (p : ZMod q)) * Complex.exp (-Complex.I * (t : ℂ) * Real.log (p : ℝ))‖ ≤ 1 := by
      rw [norm_mul, norm_mul, hg p hp_p, one_mul, norm_star, mul_assoc, ← Complex.ofReal_mul,
        norm_exp_neg_I_mul, mul_one]
      exact dirichlet_norm_le_one χ _
    exact div_nonneg (by linarith [(Complex.re_le_norm _).trans hnorm]) (Nat.cast_nonneg _)
  have h2_nonneg : ∀ p ∈ (Icc 1 Y).filter Nat.Prime,
      0 ≤ (1 - (g p * star (χ' (p : ZMod q')) * Complex.exp (-Complex.I * (t' : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ) := by
    intro p hp
    have hp_p := (mem_filter.mp hp).2
    have hnorm : ‖g p * star (χ' (p : ZMod q')) * Complex.exp (-Complex.I * (t' : ℂ) * Real.log (p : ℝ))‖ ≤ 1 := by
      rw [norm_mul, norm_mul, hg p hp_p, one_mul, norm_star, mul_assoc, ← Complex.ofReal_mul,
        norm_exp_neg_I_mul, mul_one]
      exact dirichlet_norm_le_one χ' _
    exact div_nonneg (by linarith [(Complex.re_le_norm _).trans hnorm]) (Nat.cast_nonneg _)
  have hdvd_sum : ∑ p ∈ (Icc 1 Y).filter Nat.Prime, (if p ∣ q * q' then (2 : ℝ) else 0) ≤ 2 * Q ^ 2 := by
    rw [← sum_filter]
    have hsub : ((Icc 1 Y).filter Nat.Prime).filter (fun p => p ∣ q * q') ⊆ Icc 1 (q * q') := by
      intro p hp
      simp only [mem_filter, mem_Icc] at hp ⊢
      exact ⟨hp.1.1.1, Nat.le_of_dvd hqstar_pos hp.2⟩
    calc ∑ _p ∈ ((Icc 1 Y).filter Nat.Prime).filter (fun p => p ∣ q * q'), (2 : ℝ)
        = ((((Icc 1 Y).filter Nat.Prime).filter (fun p => p ∣ q * q')).card : ℝ) * 2 := by simp
      _ ≤ ((Icc 1 (q * q')).card : ℝ) * 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card hsub) (by norm_num)
      _ = 2 * ((q * q' : ℕ) : ℝ) := by
          rw [Nat.card_Icc]; simp [show q * q' + 1 - 1 = q * q' by omega]; ring
      _ ≤ 2 * Q ^ 2 := by push_cast; nlinarith
  have hsubY : (Icc 1 Y).filter Nat.Prime ⊆ (Icc 1 X).filter Nat.Prime :=
    Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hYX)
  calc ∑ p ∈ (Icc 1 Y).filter Nat.Prime,
        (1 - (ψ (p : ZMod (q * q')) * Complex.exp (-Complex.I * ((t' - t : ℝ) : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ)
      ≤ ∑ p ∈ (Icc 1 Y).filter Nat.Prime,
          ((if p ∣ q * q' then (2 : ℝ) else 0) +
            2 * (1 - (g p * star (χ (p : ZMod q)) * Complex.exp (-Complex.I * (t : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ) +
            2 * (1 - (g p * star (χ' (p : ZMod q')) * Complex.exp (-Complex.I * (t' : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ)) := by
        refine sum_le_sum fun p hp => ?_
        have hsp := hsplit p hp
        have hnn1 := h1_nonneg p (hsubY hp)
        have hnn2 := h2_nonneg p hp
        have h2a : 0 ≤ 2 * (1 - (g p * star (χ (p : ZMod q)) * Complex.exp (-Complex.I * (t : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ) := by
          rw [mul_div_assoc]; positivity
        have h2b : 0 ≤ 2 * (1 - (g p * star (χ' (p : ZMod q')) * Complex.exp (-Complex.I * (t' : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ) := by
          rw [mul_div_assoc]; positivity
        by_cases hd : p ∣ q * q'
        · rw [if_pos hd] at hsp ⊢; linarith
        · rw [if_neg hd] at hsp ⊢; linarith
    _ = (∑ p ∈ (Icc 1 Y).filter Nat.Prime, if p ∣ q * q' then (2 : ℝ) else 0) +
        2 * (∑ p ∈ (Icc 1 Y).filter Nat.Prime,
          (1 - (g p * star (χ (p : ZMod q)) * Complex.exp (-Complex.I * (t : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ)) +
        2 * (∑ p ∈ (Icc 1 Y).filter Nat.Prime,
          (1 - (g p * star (χ' (p : ZMod q')) * Complex.exp (-Complex.I * (t' : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ)) := by
        rw [sum_add_distrib, sum_add_distrib, mul_sum, mul_sum]
        congr 1; congr 1
        · refine sum_congr rfl fun p _ => by ring
        · refine sum_congr rfl fun p _ => by ring
    _ ≤ 2 * Q ^ 2 + 2 * Q + 2 * Q := by
        have h1 : ∑ p ∈ (Icc 1 Y).filter Nat.Prime,
            (1 - (g p * star (χ (p : ZMod q)) * Complex.exp (-Complex.I * (t : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q :=
          (sum_le_sum_of_subset_of_nonneg hsubY (fun p hp _ => h1_nonneg p hp)).trans hdist
        linarith
    _ = 4 * Q + 2 * Q ^ 2 := by ring
private lemma dirichletL_lower_of_pretentious {qstar Y : ℕ} [NeZero qstar] (hY : 3 ≤ Y)
    (ψ : DirichletCharacter ℂ qstar) {T D : ℝ}
    (hψ_dist : ∑ p ∈ (Icc 1 Y).filter Nat.Prime,
      (1 - (ψ (p : ZMod qstar) * Complex.exp (-Complex.I * (T : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ) ≤ D) :
    let σ : ℝ := 1 + 1 / Real.log (Y : ℝ)
    Real.exp (-(D + 50)) * Real.log (Y : ℝ) ≤
      ‖∑' n : ℕ, if n = 0 then (0 : ℂ) else ψ (n : ZMod qstar) * ((n : ℂ) ^ (-(σ + Complex.I * T)))‖ := by
  intro σ
  have hlogY_ge1 : (1 : ℝ) ≤ Real.log (Y : ℝ) := by
    have h3 : Real.exp 1 ≤ (Y : ℝ) := by
      linarith [Real.exp_one_lt_d9, show (3 : ℝ) ≤ (Y : ℝ) by exact_mod_cast hY]
    have := Real.log_le_log (Real.exp_pos 1) h3; rwa [Real.log_exp] at this
  have hσ : 1 < σ := by dsimp [σ]; linarith [show (0 : ℝ) < 1 / Real.log (Y : ℝ) by positivity]
  let fψ : ℕ →*₀ ℂ :=
    { toFun := fun n => if n = 0 then 0 else ψ (n : ZMod qstar) * ((n : ℂ) ^ (-(σ + Complex.I * T)))
      map_zero' := by simp
      map_one' := by simp
      map_mul' := fun a b => by
        by_cases ha : a = 0
        · simp [ha]
        by_cases hb : b = 0
        · simp [hb]
        rw [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb]
        rw [Nat.cast_mul, Nat.cast_mul, map_mul,
          ← Complex.ofReal_natCast a, ← Complex.ofReal_natCast b,
          Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
        ring }
  have hfψ_bd : ∀ n : ℕ, 1 ≤ n → ‖fψ n‖ ≤ (n : ℝ) ^ (-σ) := by
    intro n hn
    dsimp [fψ]; rw [if_neg (by omega), norm_mul, cpow_norm_natCast hn]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (dirichlet_norm_le_one ψ _)
  have heul := (euler_norm_bounds hσ hfψ_bd).1
  have hsum_all : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-σ)) := summable_primes_rpow hσ
  have hsum_f : Summable (fun p : Nat.Primes => (fψ p).re) :=
    hsum_all.of_norm_bounded fun p => by
      rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hfψ_bd p p.prop.one_le)
  let S : Finset Nat.Primes := ((Icc 1 Y).filter Nat.Prime).attach.map
    ⟨fun p => ⟨p.1, (mem_filter.mp p.2).2⟩,
     fun _ _ h => Subtype.ext (by injection h)⟩
  have hdiff_le : ∑' p : Nat.Primes, (((p : ℕ) : ℝ) ^ (-σ) - (fψ p).re) ≤ D + 40 := by
    have hsum_diff : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-σ) - (fψ p).re) := hsum_all.sub hsum_f
    have htail_sum : Summable (fun p : Nat.Primes =>
        if (p : ℕ) ≤ Y then (0 : ℝ) else 2 * ((p : ℕ) : ℝ) ^ (-σ)) :=
      (hsum_all.mul_left 2).of_nonneg_of_le (fun _ => by split_ifs <;> positivity) (fun p => by
        split_ifs
        · positivity
        · exact le_rfl)
    have hhead_support : ∀ p : Nat.Primes, p ∉ S →
        (if (p : ℕ) ≤ Y then
          (1 - (ψ ((p : ℕ) : ZMod qstar) * Complex.exp (-Complex.I * (T : ℂ) * Real.log ((p : ℕ) : ℝ))).re) / ((p : ℕ) : ℝ)
         else 0) = 0 := by
      intro p hp
      by_cases hle : (p : ℕ) ≤ Y
      · exfalso; apply hp
        simp only [S, Finset.mem_map, mem_attach, true_and]
        exact ⟨⟨(p : ℕ), mem_filter.mpr ⟨mem_Icc.mpr ⟨p.prop.one_le, hle⟩, p.prop⟩⟩, rfl⟩
      · exact if_neg hle
    have hhead_sum : Summable (fun p : Nat.Primes =>
        if (p : ℕ) ≤ Y then
          (1 - (ψ ((p : ℕ) : ZMod qstar) * Complex.exp (-Complex.I * (T : ℂ) * Real.log ((p : ℕ) : ℝ))).re) / ((p : ℕ) : ℝ)
        else 0) := summable_of_ne_finset_zero hhead_support
    have hpt_le : ∀ p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ) - (fψ p).re ≤
        (if (p : ℕ) ≤ Y then
          (1 - (ψ ((p : ℕ) : ZMod qstar) * Complex.exp (-Complex.I * (T : ℂ) * Real.log ((p : ℕ) : ℝ))).re) / ((p : ℕ) : ℝ)
         else 0) +
        (if (p : ℕ) ≤ Y then (0 : ℝ) else 2 * ((p : ℕ) : ℝ) ^ (-σ)) := by
      intro p
      have hp_pos : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
      have hp_ge1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.one_le
      have hcpow_eq : (((p : ℕ) : ℂ) ^ (-(σ + Complex.I * T))) =
          ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (-Complex.I * (T : ℂ) * Real.log ((p : ℕ) : ℝ)) := by
        rw [← Complex.ofReal_natCast, Complex.cpow_def_of_ne_zero (by exact_mod_cast hp_pos.ne'),
          Complex.ofReal_log hp_pos.le, Real.rpow_def_of_pos hp_pos, Complex.ofReal_exp, ← Complex.exp_add]
        congr 1; push_cast; ring
      have hf_re : (fψ p).re = ((p : ℕ) : ℝ) ^ (-σ) *
          (ψ ((p : ℕ) : ZMod qstar) * Complex.exp (-Complex.I * (T : ℂ) * Real.log ((p : ℕ) : ℝ))).re := by
        dsimp [fψ]; rw [if_neg p.prop.ne_zero, hcpow_eq]
        have hmul : ψ ((p : ℕ) : ZMod qstar) *
            (((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (-Complex.I * (T : ℂ) * Real.log ((p : ℕ) : ℝ))) =
            ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) *
              (ψ ((p : ℕ) : ZMod qstar) * Complex.exp (-Complex.I * (T : ℂ) * Real.log ((p : ℕ) : ℝ))) := by ring
        rw [hmul, Complex.re_ofReal_mul]
      by_cases hle : (p : ℕ) ≤ Y
      · rw [if_pos hle, if_pos hle, add_zero, hf_re]
        have h1_sub_nn : 0 ≤ 1 - (ψ ((p : ℕ) : ZMod qstar) * Complex.exp (-Complex.I * (T : ℂ) * Real.log ((p : ℕ) : ℝ))).re := by
          have hnorm : ‖ψ ((p : ℕ) : ZMod qstar) * Complex.exp (-Complex.I * (T : ℂ) * Real.log ((p : ℕ) : ℝ))‖ ≤ 1 := by
            rw [norm_mul, mul_assoc, ← Complex.ofReal_mul, norm_exp_neg_I_mul, mul_one]
            exact dirichlet_norm_le_one ψ _
          linarith [(Complex.re_le_norm _).trans hnorm]
        have hpow_le : ((p : ℕ) : ℝ) ^ (-σ) ≤ 1 / ((p : ℕ) : ℝ) := by
          rw [one_div, ← Real.rpow_neg_one]
          exact Real.rpow_le_rpow_of_exponent_le hp_ge1 (by linarith)
        calc ((p : ℕ) : ℝ) ^ (-σ) - ((p : ℕ) : ℝ) ^ (-σ) *
              (ψ ((p : ℕ) : ZMod qstar) * Complex.exp (-Complex.I * (T : ℂ) * Real.log ((p : ℕ) : ℝ))).re
            = ((p : ℕ) : ℝ) ^ (-σ) *
              (1 - (ψ ((p : ℕ) : ZMod qstar) * Complex.exp (-Complex.I * (T : ℂ) * Real.log ((p : ℕ) : ℝ))).re) := by ring
          _ ≤ (1 / ((p : ℕ) : ℝ)) *
              (1 - (ψ ((p : ℕ) : ZMod qstar) * Complex.exp (-Complex.I * (T : ℂ) * Real.log ((p : ℕ) : ℝ))).re) :=
              mul_le_mul_of_nonneg_right hpow_le h1_sub_nn
          _ = _ := by ring
      · rw [if_neg hle, if_neg hle, zero_add]
        have h1 := (Complex.abs_re_le_norm (fψ p)).trans (hfψ_bd p p.prop.one_le)
        linarith [(abs_le.mp h1).1]
    have htsum_le := Summable.tsum_le_tsum hpt_le hsum_diff (hhead_sum.add htail_sum)
    rw [Summable.tsum_add hhead_sum htail_sum] at htsum_le
    have hhead_eq : ∑' p : Nat.Primes,
        (if (p : ℕ) ≤ Y then
          (1 - (ψ ((p : ℕ) : ZMod qstar) * Complex.exp (-Complex.I * (T : ℂ) * Real.log ((p : ℕ) : ℝ))).re) / ((p : ℕ) : ℝ)
         else 0) =
        ∑ p ∈ (Icc 1 Y).filter Nat.Prime,
          (1 - (ψ (p : ZMod qstar) * Complex.exp (-Complex.I * (T : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ) := by
      rw [tsum_eq_sum (s := S) hhead_support]
      simp only [S, sum_map]
      trans ∑ p ∈ ((Icc 1 Y).filter Nat.Prime).attach,
          (1 - (ψ (p.1 : ZMod qstar) * Complex.exp (-Complex.I * (T : ℂ) * Real.log (p.1 : ℝ))).re) / (p.1 : ℝ)
      · refine sum_congr rfl fun p _ => if_pos (mem_Icc.mp (mem_filter.mp p.2).1).2
      · exact sum_attach ((Icc 1 Y).filter Nat.Prime)
          (fun p : ℕ => (1 - (ψ (p : ZMod qstar) * Complex.exp (-Complex.I * (T : ℂ) * Real.log (p : ℝ))).re) / (p : ℝ))
    have htail_le : ∑' p : Nat.Primes, (if (p : ℕ) ≤ Y then (0 : ℝ) else 2 * ((p : ℕ) : ℝ) ^ (-σ)) ≤ 40 := by
      have hrew : (fun p : Nat.Primes => if (p : ℕ) ≤ Y then (0 : ℝ) else 2 * ((p : ℕ) : ℝ) ^ (-σ)) =
          fun p : Nat.Primes => 2 * (if (p : ℕ) ≤ Y then (0 : ℝ) else ((p : ℕ) : ℝ) ^ (-σ)) := by
        ext p; split_ifs <;> ring
      rw [hrew, tsum_mul_left]
      linarith [tsum_primes_gt_rpow_le hY]
    linarith [htsum_le, hhead_eq, hψ_dist, htail_le]
  have htsum_all := tsum_primes_rpow_ge hσ
  have h1_sub : 1 / (σ - 1) = Real.log (Y : ℝ) := by
    dsimp [σ]; rw [add_sub_cancel_left, one_div_one_div]
  rw [h1_sub] at htsum_all
  rw [Summable.tsum_sub hsum_all hsum_f] at hdiff_le
  have hexp_eq : Real.exp (-(D + 50)) * Real.log (Y : ℝ) = Real.exp (Real.log (Real.log (Y : ℝ)) - (D + 50)) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by linarith), mul_comm]
  rw [hexp_eq]
  exact (Real.exp_le_exp.mpr (by linarith)).trans heul
theorem lemma_tb_deterministic (Q δ : ℝ) (hQ : 1 ≤ Q) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ X₀ : ℝ, max Q 100 ≤ X₀ ∧
      ∀ (X : ℕ), X₀ ≤ (X : ℝ) →
      ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ = 1) →
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
        1 ≤ q → (q : ℝ) ≤ Q → |t| ≤ Q * (X : ℝ) →
        ∑ p ∈ (Icc 1 X).filter Nat.Prime,
          (1 - (g p * star (χ (p : ZMod q)) * Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q →
      ∀ (q' : ℕ) (χ' : DirichletCharacter ℂ q') (t' : ℝ),
        1 ≤ q' → (q' : ℝ) ≤ Q → |t'| ≤ Q * (⌊(X : ℝ) ^ δ⌋₊ : ℝ) →
        ∑ p ∈ (Icc 1 ⌊(X : ℝ) ^ δ⌋₊).filter Nat.Prime,
          (1 - (g p * star (χ' (p : ZMod q')) * Complex.exp (-Complex.I * t' * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q →
      |t| ≤ 2 * Q * (X : ℝ) ^ δ := by
  let cQ : ℝ := Real.exp (-(4 * Q + 2 * Q ^ 2 + 50))
  have hcQ_pos : 0 < cQ := Real.exp_pos _
  let K : ℕ := max 3 ⌈16 / (cQ * δ)⌉₊
  have hK3 : 3 ≤ K := le_max_left _ _
  have hK_ge : 16 / (cQ * δ) ≤ (K : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 3 _)
  let qMax : ℕ := ⌊Q ^ 2⌋₊
  have hL_all : ∀ qstar ∈ Icc 1 qMax,
      ∃ C_q T_q : ℝ, 1 ≤ T_q ∧ 0 ≤ C_q ∧
        ∀ (ψ : DirichletCharacter ℂ qstar) (σ T : ℝ), 1 < σ → T_q ≤ |T| →
          ‖∑' n : ℕ, if n = 0 then (0 : ℂ) else ψ (n : ZMod qstar) * ((n : ℂ) ^ (-(σ + Complex.I * T)))‖ ≤
            (2 / (K : ℝ)) * Real.log |T| + C_q := by
    intro qstar hqstar
    have : NeZero qstar := ⟨by have := (mem_Icc.mp hqstar).1; omega⟩
    have hper : ∀ ψ : DirichletCharacter ℂ qstar,
        ∃ C T₀ : ℝ, 1 ≤ T₀ ∧ 0 ≤ C ∧
          ∀ (σ T : ℝ), 1 < σ → T₀ ≤ |T| →
            ‖∑' n : ℕ, if n = 0 then (0 : ℂ) else ψ (n : ZMod qstar) * ((n : ℂ) ^ (-(σ + Complex.I * T)))‖ ≤
              (2 / (K : ℝ)) * Real.log |T| + C :=
      fun ψ => norm_dirichletL_le_div_K ψ K hK3
    choose Cψ Tψ hTψ hCψ hbdψ using hper
    refine ⟨∑ ψ : DirichletCharacter ℂ qstar, Cψ ψ,
      max 1 (∑ ψ : DirichletCharacter ℂ qstar, Tψ ψ),
      le_max_left _ _, sum_nonneg (fun ψ _ => hCψ ψ), ?_⟩
    intro ψ σ T hσ hT
    have hT1 : Tψ ψ ≤ |T| :=
      le_trans (single_le_sum (fun ψ' _ => by linarith [hTψ ψ']) (mem_univ ψ))
        (le_trans (le_max_right _ _) hT)
    have hC1 : Cψ ψ ≤ ∑ ψ' : DirichletCharacter ℂ qstar, Cψ ψ' :=
      single_le_sum (fun ψ' _ => hCψ ψ') (mem_univ ψ)
    exact (hbdψ ψ σ T hσ hT1).trans (by linarith)
  choose Cq Tq hTq hCq hbdq using hL_all
  let CL : ℝ := ∑ qstar ∈ Icc 1 qMax, if h : qstar ∈ Icc 1 qMax then Cq qstar h else 0
  let TL : ℝ := max 10 (∑ qstar ∈ Icc 1 qMax, if h : qstar ∈ Icc 1 qMax then Tq qstar h else 0)
  have hCL_nn : 0 ≤ CL := sum_nonneg fun qstar h => by simp only [h, ↓reduceDIte]; exact hCq qstar h
  have hTL_ge10 : 10 ≤ TL := le_max_left _ _
  let X₀ : ℝ := max (max Q 100) (max ((TL + 10) ^ (1 / δ))
    (Real.exp (100 * (CL + Real.log (2 * Q) + 10) / (cQ * δ) + 10 / δ)))
  refine ⟨X₀, le_max_left _ _, ?_⟩
  intro X hX g hg q χ t hq1 hqQ htQ hdist q' χ' t' hq'1 hq'Q ht'Q hdist'
  by_contra hbig
  push Not at hbig
  let Y : ℕ := ⌊(X : ℝ) ^ δ⌋₊
  have hX_ge100 : 100 ≤ (X : ℝ) := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
  have hX_pos : (0 : ℝ) < (X : ℝ) := by linarith
  have hX_ge1 : (1 : ℝ) ≤ (X : ℝ) := by linarith
  have hXδ_ge : TL + 10 ≤ (X : ℝ) ^ δ := by
    have h1 : (TL + 10) ^ (1 / δ) ≤ (X : ℝ) := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX)
    have hTL_pos : 0 < TL + 10 := by linarith
    calc TL + 10 = ((TL + 10) ^ (1 / δ)) ^ δ := by
          rw [← Real.rpow_mul hTL_pos.le, one_div_mul_cancel hδ0.ne', Real.rpow_one]
      _ ≤ (X : ℝ) ^ δ := Real.rpow_le_rpow (by positivity) h1 hδ0.le
  have hY_ge3 : 3 ≤ Y := Nat.le_floor (by norm_num; linarith [hXδ_ge, hTL_ge10])
  have hY_ge_half : (1 / 2 : ℝ) * (X : ℝ) ^ δ ≤ (Y : ℝ) := by linarith [Nat.lt_floor_add_one ((X : ℝ) ^ δ)]
  have hY_le : (Y : ℝ) ≤ (X : ℝ) ^ δ := Nat.floor_le (by positivity)
  have hY_le_X : Y ≤ X := by
    have h1 : (X : ℝ) ^ δ ≤ (X : ℝ) :=
      (Real.rpow_le_rpow_of_exponent_le hX_ge1 (by linarith)).trans_eq (Real.rpow_one _)
    exact_mod_cast hY_le.trans h1
  let T : ℝ := t' - t
  have hT_ge : (X : ℝ) ^ δ ≤ |T| := by
    have ht'_le : |t'| ≤ Q * (X : ℝ) ^ δ := ht'Q.trans (mul_le_mul_of_nonneg_left hY_le (by linarith))
    have htri := abs_sub_abs_le_abs_sub t t'
    have hsym : |t - t'| = |T| := by dsimp [T]; rw [abs_sub_comm]
    rw [hsym] at htri
    have hQX : (X : ℝ) ^ δ ≤ Q * (X : ℝ) ^ δ := le_mul_of_one_le_left (by positivity) hQ
    linarith
  have hT_le : |T| ≤ 2 * Q * (X : ℝ) := by
    have ht'_le : |t'| ≤ Q * (X : ℝ) :=
      ht'Q.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hY_le_X) (by linarith))
    dsimp [T]
    calc |t' - t| ≤ |t'| + |t| := abs_sub _ _
      _ ≤ Q * (X : ℝ) + Q * (X : ℝ) := add_le_add ht'_le htQ
      _ = 2 * Q * (X : ℝ) := by ring
  let qstar : ℕ := q * q'
  have hqstar1 : 1 ≤ qstar := Nat.mul_pos (by omega) (by omega)
  have hqstar_le : qstar ≤ qMax := by
    refine Nat.le_floor ?_
    have : (qstar : ℝ) = (q : ℝ) * (q' : ℝ) := by dsimp [qstar]; push_cast; rfl
    rw [this]; nlinarith
  have hqstar_mem : qstar ∈ Icc 1 qMax := mem_Icc.mpr ⟨hqstar1, hqstar_le⟩
  have : NeZero qstar := ⟨by omega⟩
  have : NeZero q := ⟨by omega⟩
  have : NeZero q' := ⟨by omega⟩
  let ψ : DirichletCharacter ℂ qstar :=
    DirichletCharacter.changeLevel (Nat.dvd_mul_right q q') χ *
    star (DirichletCharacter.changeLevel (Nat.dvd_mul_left q' q) χ')
  have hψ_dist := pretentious_prod_char_dist hY_le_X hqQ hq'Q hg χ t hdist χ' t' hdist'
  have hL_lb := dirichletL_lower_of_pretentious hY_ge3 ψ hψ_dist
  let σ : ℝ := 1 + 1 / Real.log (Y : ℝ)
  have hlogY_ge1 : (1 : ℝ) ≤ Real.log (Y : ℝ) := by
    have h3 : Real.exp 1 ≤ (Y : ℝ) := by
      linarith [Real.exp_one_lt_d9, show (3 : ℝ) ≤ (Y : ℝ) by exact_mod_cast hY_ge3]
    have := Real.log_le_log (Real.exp_pos 1) h3; rwa [Real.log_exp] at this
  have hσ : 1 < σ := by dsimp [σ]; linarith [show (0 : ℝ) < 1 / Real.log (Y : ℝ) by positivity]
  have hT_ge_Tq : Tq qstar hqstar_mem ≤ |T| := by
    have h1 : Tq qstar hqstar_mem ≤ ∑ q' ∈ Icc 1 qMax, if h : q' ∈ Icc 1 qMax then Tq q' h else 0 := by
      have := single_le_sum (f := fun q' => if h : q' ∈ Icc 1 qMax then Tq q' h else 0)
        (fun q' hq' => by simp only [hq', ↓reduceDIte]; linarith [hTq q' hq']) hqstar_mem
      simpa only [hqstar_mem, ↓reduceDIte] using this
    have h2 : Tq qstar hqstar_mem ≤ TL := h1.trans (le_max_right _ _)
    linarith [hXδ_ge, hT_ge]
  have hL_ub : ‖∑' n : ℕ, if n = 0 then (0 : ℂ) else ψ (n : ZMod qstar) * ((n : ℂ) ^ (-(σ + Complex.I * T)))‖ ≤
      (2 / (K : ℝ)) * Real.log |T| + CL := by
    have h1 := hbdq qstar hqstar_mem ψ σ T hσ hT_ge_Tq
    have hCq_le : Cq qstar hqstar_mem ≤ CL := by
      have := single_le_sum (f := fun q' => if h : q' ∈ Icc 1 qMax then Cq q' h else 0)
        (fun q' hq' => by simp only [hq', ↓reduceDIte]; exact hCq q' hq') hqstar_mem
      simpa only [hqstar_mem, ↓reduceDIte] using this
    exact h1.trans (by linarith)
  have hlogX_ge : 100 * (CL + Real.log (2 * Q) + 10) / (cQ * δ) + 10 / δ ≤ Real.log (X : ℝ) := by
    have h1 : Real.exp (100 * (CL + Real.log (2 * Q) + 10) / (cQ * δ) + 10 / δ) ≤ (X : ℝ) :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  have hlogY_lb : (δ / 2) * Real.log (X : ℝ) ≤ Real.log (Y : ℝ) := by
    have h1 : Real.log ((1 / 2 : ℝ) * (X : ℝ) ^ δ) ≤ Real.log (Y : ℝ) :=
      Real.log_le_log (by positivity) hY_ge_half
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hX_pos] at h1
    have hlog_half : -(1 : ℝ) ≤ Real.log (1 / 2 : ℝ) := by
      rw [one_div, Real.log_inv]; linarith [Real.log_two_lt_d9]
    have hδlogX : 10 ≤ δ * Real.log (X : ℝ) := by
      have h10 : 10 / δ ≤ Real.log (X : ℝ) := by
        have : 0 ≤ 100 * (CL + Real.log (2 * Q) + 10) / (cQ * δ) := by
          have : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith); positivity
        linarith
      rwa [div_le_iff₀ hδ0, mul_comm] at h10
    linarith
  have hlogT_ub : Real.log |T| ≤ Real.log (2 * Q) + Real.log (X : ℝ) := by
    calc Real.log |T| ≤ Real.log (2 * Q * (X : ℝ)) := Real.log_le_log (by linarith) hT_le
      _ = Real.log (2 * Q) + Real.log (X : ℝ) := Real.log_mul (by positivity) hX_pos.ne'
  have h2K : 2 / (K : ℝ) ≤ (cQ * δ) / 8 := by
    have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
    rw [div_le_iff₀ hKpos]
    have h1 : 16 ≤ (K : ℝ) * (cQ * δ) := (div_le_iff₀ (by positivity)).mp hK_ge
    linarith
  have hlog2Q_nn : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
  have hlogX_nn : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hX_ge1
  have h2K_le1 : 2 / (K : ℝ) ≤ 1 := by
    have hK3R : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK3
    rw [div_le_one (by linarith)]; linarith
  have hcontra1 : (cQ * δ / 2) * Real.log (X : ℝ) ≤ (cQ * δ / 8) * Real.log (X : ℝ) + Real.log (2 * Q) + CL := by
    have h1 : (cQ * δ / 2) * Real.log (X : ℝ) ≤ cQ * Real.log (Y : ℝ) := by
      have := mul_le_mul_of_nonneg_left hlogY_lb hcQ_pos.le; linarith
    have h2 : (2 / (K : ℝ)) * Real.log |T| ≤ (cQ * δ / 8) * Real.log (X : ℝ) + Real.log (2 * Q) := by
      calc (2 / (K : ℝ)) * Real.log |T|
          ≤ (2 / (K : ℝ)) * (Real.log (2 * Q) + Real.log (X : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogT_ub (by positivity)
        _ = (2 / (K : ℝ)) * Real.log (2 * Q) + (2 / (K : ℝ)) * Real.log (X : ℝ) := by ring
        _ ≤ 1 * Real.log (2 * Q) + (cQ * δ / 8) * Real.log (X : ℝ) := by
            have ha := mul_le_mul_of_nonneg_right h2K_le1 hlog2Q_nn
            have hb := mul_le_mul_of_nonneg_right h2K hlogX_nn
            linarith
        _ = (cQ * δ / 8) * Real.log (X : ℝ) + Real.log (2 * Q) := by ring
    have hlb' : cQ * Real.log (Y : ℝ) ≤
        ‖∑' n : ℕ, if n = 0 then (0 : ℂ) else ψ (n : ZMod qstar) * ((n : ℂ) ^ (-(σ + Complex.I * T)))‖ := hL_lb
    linarith [h1, hlb', hL_ub, h2]
  have hcontra2 : 100 * (CL + Real.log (2 * Q) + 10) ≤ (cQ * δ) * Real.log (X : ℝ) := by
    have h1 : 100 * (CL + Real.log (2 * Q) + 10) / (cQ * δ) ≤ Real.log (X : ℝ) := by
      linarith [hlogX_ge, show (0 : ℝ) ≤ 10 / δ by positivity]
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  linarith
end

section
open Filter Finset Complex Real Classical
open scoped BigOperators
private lemma granville_unit_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (u : (ZMod q)ˣ) : χ (u : ZMod q) ≠ 0 := by
  intro h0
  have h1 : χ (u : ZMod q) * χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1
private lemma granville_norm_le_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x : ZMod q) : ‖χ x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    have hord : u ^ Fintype.card (ZMod q)ˣ = 1 := pow_card_eq_one
    have h1 : χ (u : ZMod q) ^ Fintype.card (ZMod q)ˣ = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hord, Units.val_one, map_one]
    have h2 : ‖χ (u : ZMod q)‖ ^ Fintype.card (ZMod q)ˣ = 1 := by
      rw [← norm_pow, h1, norm_one]
    have hpos : 0 < Fintype.card (ZMod q)ˣ := Fintype.card_pos
    by_contra hgt
    push Not at hgt
    have : (1 : ℝ) ^ Fintype.card (ZMod q)ˣ < ‖χ (u : ZMod q)‖ ^ Fintype.card (ZMod q)ˣ :=
      pow_lt_pow_left₀ hgt (by norm_num) hpos.ne'
    rw [one_pow] at this
    linarith
  · rw [MulChar.map_nonunit _ hx, norm_zero]; norm_num
lemma primitive_exists_unit_mod_div_prime {q p : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hp : p.Prime) (hpdvd : p ∣ q) :
    ∃ u : (ZMod q)ˣ, ZMod.castHom (Nat.div_dvd_of_dvd hpdvd) (ZMod (q / p)) (u : ZMod q) = 1 ∧
      χ (u : ZMod q) ≠ 1 := by
  have hqpos : 0 < q := NeZero.pos q
  have hqp_pos : 0 < q / p := Nat.div_pos (Nat.le_of_dvd hqpos hpdvd) hp.pos
  have : NeZero (q / p) := ⟨hqp_pos.ne'⟩
  have hnot_ft : ¬ χ.FactorsThrough (q / p) := by
    intro hft
    have hle : χ.conductor ≤ q / p := Nat.sInf_le hft
    have hcond : χ.conductor = q := hprim
    have hlt : q / p < q := Nat.div_lt_self hqpos hp.one_lt
    omega
  by_contra hno
  push Not at hno
  apply hnot_ft
  refine ⟨Nat.div_dvd_of_dvd hpdvd, ?_⟩
  let φ : (ZMod q)ˣ →* (ZMod (q / p))ˣ := ZMod.unitsMap (Nat.div_dvd_of_dvd hpdvd)
  have hsurj : Function.Surjective φ := ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd hpdvd)
  have hker : ∀ u : (ZMod q)ˣ, φ u = 1 → χ (u : ZMod q) = 1 := by
    intro u hu
    have h1 : ZMod.castHom (Nat.div_dvd_of_dvd hpdvd) (ZMod (q / p)) (u : ZMod q) = 1 := by
      have := congrArg Units.val hu
      simpa [φ, ZMod.unitsMap] using this
    exact hno u h1
  let fU : (ZMod (q / p))ˣ →* ℂˣ :=
    { toFun := fun v =>
        let u := (hsurj v).choose
        Units.mk0 (χ (u : ZMod q)) (granville_unit_ne_zero χ u)
      map_one' := by
        apply Units.ext
        dsimp only [Units.val_mk0, Units.val_one]
        exact hker _ (hsurj 1).choose_spec
      map_mul' := fun v1 v2 => by
        apply Units.ext
        dsimp only [Units.val_mk0, Units.val_mul]
        let u1 := (hsurj v1).choose
        let u2 := (hsurj v2).choose
        let u12 := (hsurj (v1 * v2)).choose
        have hrel : φ (u12 * (u1 * u2)⁻¹) = 1 := by
          rw [map_mul, map_inv, map_mul, (hsurj (v1 * v2)).choose_spec,
            (hsurj v1).choose_spec, (hsurj v2).choose_spec, mul_inv_cancel]
        have hχ1 : χ ((u12 * (u1 * u2)⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := hker _ hrel
        have hu_eq : u12 = (u12 * (u1 * u2)⁻¹) * (u1 * u2) := (inv_mul_cancel_right u12 (u1 * u2)).symm
        have hmul : (u12 : ZMod q) = ((u12 * (u1 * u2)⁻¹ : (ZMod q)ˣ) : ZMod q) * ((u1 : ZMod q) * (u2 : ZMod q)) := by
          have := congrArg Units.val hu_eq
          simpa [Units.val_mul] using this
        rw [hmul, map_mul, hχ1, one_mul, map_mul] }
  let χ₀ : DirichletCharacter ℂ (q / p) := MulChar.ofUnitHom fU
  refine ⟨χ₀, ?_⟩
  ext u
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
  have hcast_u : ZMod.cast (u : ZMod q) = (φ u : ZMod (q / p)) := by
    simp [φ, ZMod.unitsMap, ZMod.castHom_apply]
  rw [hcast_u]
  have hχ₀_u : χ₀ (φ u : ZMod (q / p)) = (fU (φ u) : ℂ) := by
    have h1 : MulChar.equivToUnitHom χ₀ = fU := by
      dsimp [χ₀]; exact Equiv.apply_symm_apply _ _
    exact congrArg (fun g => ((g (φ u) : ℂˣ) : ℂ)) h1
  rw [hχ₀_u]
  dsimp [fU]
  let u' := (hsurj (φ u)).choose
  have hrel : φ (u' * u⁻¹) = 1 := by
    rw [map_mul, map_inv, (hsurj (φ u)).choose_spec, mul_inv_cancel]
  have hχ1 : χ ((u' * u⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := hker _ hrel
  have hu_eq : u' = (u' * u⁻¹) * u := (inv_mul_cancel_right u' u).symm
  have heq : (u' : ZMod q) = ((u' * u⁻¹ : (ZMod q)ˣ) : ZMod q) * (u : ZMod q) := by
    have := congrArg Units.val hu_eq
    simpa [Units.val_mul] using this
  rw [heq, map_mul, hχ1, one_mul]
lemma primitive_sum_coset_eq_zero {q p M : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hp : p.Prime) (hpdvd : p ∣ q) (hMp : Nat.Coprime M p) (x : ℕ) :
    ∑ t ∈ Finset.range p, χ (((x + t * M * (q / p) : ℕ) : ZMod q)) = 0 := by
  have hqpos : 0 < q := NeZero.pos q
  have hqp_pos : 0 < q / p := Nat.div_pos (Nat.le_of_dvd hqpos hpdvd) hp.pos
  have : NeZero (q / p) := ⟨hqp_pos.ne'⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨u, hu_mod, hu_ne⟩ := primitive_exists_unit_mod_div_prime χ hprim hp hpdvd
  by_cases hcop : Nat.Coprime x (q / p)
  swap
  · refine sum_eq_zero fun t _ => ?_
    apply MulChar.map_nonunit
    rw [ZMod.isUnit_iff_coprime]
    intro hcu
    apply hcop
    have hdvd_qp : q / p ∣ q := Nat.div_dvd_of_dvd hpdvd
    have hcu' : Nat.Coprime (x + t * M * (q / p)) (q / p) := hcu.coprime_dvd_right hdvd_qp
    rwa [Nat.coprime_add_mul_right_left] at hcu'
  have hperm : ∃ σ : ℕ → ℕ, (∀ t ∈ Finset.range p, σ t ∈ Finset.range p) ∧
      (∀ t1 ∈ Finset.range p, ∀ t2 ∈ Finset.range p, σ t1 = σ t2 → t1 = t2) ∧
      (∀ t ∈ Finset.range p, (u : ZMod q) * ((x + t * M * (q / p) : ℕ) : ZMod q) =
        ((x + σ t * M * (q / p) : ℕ) : ZMod q)) := by
    have hu_val_mod : ((u : ZMod q).val : ZMod (q / p)) = 1 := by
      have h1 : ZMod.castHom (Nat.div_dvd_of_dvd hpdvd) (ZMod (q / p)) (((u : ZMod q).val : ℕ) : ZMod q) = 1 := by
        simpa [ZMod.natCast_zmod_val] using hu_mod
      simpa using h1
    have hdiv_u : (q / p) ∣ ((u : ZMod q).val + q - 1) := by
      have h1 : ((((u : ZMod q).val : ℤ) - 1 : ℤ) : ZMod (q / p)) = 0 := by
        push_cast; rw [hu_val_mod, sub_self]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
      have h2 : (((q / p : ℕ) : ℤ)) ∣ (((u : ZMod q).val + q - 1 : ℕ) : ℤ) := by
        have hcast : (((u : ZMod q).val + q - 1 : ℕ) : ℤ) = (((u : ZMod q).val : ℤ) - 1) + (q : ℤ) := by
          omega
        rw [hcast]
        exact dvd_add h1 (by exact_mod_cast Nat.div_dvd_of_dvd hpdvd)
      exact_mod_cast h2
    obtain ⟨c, hc⟩ := hdiv_u
    have hM_unit : IsUnit (M : ZMod p) := (ZMod.isUnit_iff_coprime M p).mpr hMp
    let Minv : ℕ := ((hM_unit.unit⁻¹ : (ZMod p)ˣ) : ZMod p).val
    have hMinv : (M : ZMod p) * (Minv : ZMod p) = 1 := by
      dsimp [Minv]
      rw [ZMod.natCast_zmod_val]
      have hM_eq : (M : ZMod p) = (hM_unit.unit : ZMod p) := hM_unit.unit_spec.symm
      exact (congrArg (· * ((hM_unit.unit⁻¹ : (ZMod p)ˣ) : ZMod p)) hM_eq).trans
        (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    let σ : ℕ → ℕ := fun t => ((x * c + (u : ZMod q).val * t * M) * Minv) % p
    have hσ_mem : ∀ t ∈ Finset.range p, σ t ∈ Finset.range p := fun t _ =>
      mem_range.mpr (Nat.mod_lt _ hp.pos)
    have hσ_eq : ∀ t ∈ Finset.range p,
        (u : ZMod q) * ((x + t * M * (q / p) : ℕ) : ZMod q) =
        ((x + σ t * M * (q / p) : ℕ) : ZMod q) := by
      intro t _
      have hu_cast : (u : ZMod q) = (((u : ZMod q).val + q : ℕ) : ZMod q) := by
        push_cast; simp [ZMod.natCast_zmod_val]
      have hu_eq : (u : ZMod q).val + q = 1 + c * (q / p) := by
        have hge : 1 ≤ (u : ZMod q).val + q := by omega
        have := Nat.sub_add_cancel hge
        linarith [hc]
      have hMσ : ((σ t * M : ℕ) : ZMod p) = ((x * c + (u : ZMod q).val * t * M : ℕ) : ZMod p) := by
        dsimp [σ]
        push_cast
        rw [ZMod.natCast_mod]
        push_cast
        rw [mul_assoc, mul_comm (Minv : ZMod p) (M : ZMod p), hMinv, mul_one]
      have hge_p : σ t * M ≤ (x * c + (u : ZMod q).val * t * M) + p * (σ t * M) := by
        have : σ t * M ≤ p * (σ t * M) := Nat.le_mul_of_pos_left _ hp.pos
        omega
      have hdiff_p : p ∣ ((x * c + (u : ZMod q).val * t * M) + p * (σ t * M) - σ t * M) := by
        have h1 : (((x * c + (u : ZMod q).val * t * M : ℕ) : ZMod p) - ((σ t * M : ℕ) : ZMod p)) = 0 := by
          rw [hMσ, sub_self]
        have h2 : (((((x * c + (u : ZMod q).val * t * M) + p * (σ t * M) - σ t * M : ℕ) : ℕ) : ZMod p)) = 0 := by
          have hcast : (((x * c + (u : ZMod q).val * t * M) + p * (σ t * M) - σ t * M : ℕ) : ZMod p) =
              ((x * c + (u : ZMod q).val * t * M : ℕ) : ZMod p) + (p : ZMod p) * ((σ t * M : ℕ) : ZMod p) -
              ((σ t * M : ℕ) : ZMod p) := by
            rw [Nat.cast_sub hge_p]; push_cast; ring
          rw [hcast, ZMod.natCast_self, zero_mul, add_zero, h1]
        exact (ZMod.natCast_eq_zero_iff _ _).mp h2
      have hmul_qp : ((x * c + (u : ZMod q).val * t * M : ℕ) : ZMod q) * ((q / p : ℕ) : ZMod q) =
          ((σ t * M : ℕ) : ZMod q) * ((q / p : ℕ) : ZMod q) := by
        obtain ⟨k, hk⟩ := hdiff_p
        have hnat : (x * c + (u : ZMod q).val * t * M) + p * (σ t * M) = σ t * M + p * k := by omega
        have hnat2 := congrArg (· * (q / p)) hnat
        have hq_eq : p * (q / p) = q := Nat.mul_div_cancel' hpdvd
        have hC : (((x * c + (u : ZMod q).val * t * M) * (q / p) + (σ t * M) * q : ℕ) : ZMod q) =
            (((σ t * M) * (q / p) + k * q : ℕ) : ZMod q) := by
          congr 1
          calc (x * c + (u : ZMod q).val * t * M) * (q / p) + σ t * M * q
              = (x * c + (u : ZMod q).val * t * M) * (q / p) + (σ t * M) * (p * (q / p)) := by rw [hq_eq]
            _ = ((x * c + (u : ZMod q).val * t * M) + p * (σ t * M)) * (q / p) := by ring
            _ = (σ t * M + p * k) * (q / p) := hnat2
            _ = σ t * M * (q / p) + k * (p * (q / p)) := by ring
            _ = σ t * M * (q / p) + k * q := by rw [hq_eq]
        push_cast at hC ⊢
        simp only [ZMod.natCast_self, mul_zero, add_zero] at hC
        exact hC
      rw [hu_cast]
      have h1 : (((u : ZMod q).val + q : ℕ) : ZMod q) * ((x + t * M * (q / p) : ℕ) : ZMod q) =
          ((x : ZMod q) + (((x * c + (u : ZMod q).val * t * M : ℕ) : ZMod q) * ((q / p : ℕ) : ZMod q))) := by
        have hq_zero : (q : ZMod q) = 0 := ZMod.natCast_self q
        have hl : (((u : ZMod q).val + q : ℕ) : ZMod q) * (x : ZMod q) =
            (x : ZMod q) + ((x * c : ℕ) : ZMod q) * ((q / p : ℕ) : ZMod q) := by
          rw [hu_eq]; push_cast; ring
        have hr : (((u : ZMod q).val + q : ℕ) : ZMod q) * (((t * M * (q / p) : ℕ) : ZMod q)) =
            (((u : ZMod q).val * t * M : ℕ) : ZMod q) * ((q / p : ℕ) : ZMod q) := by
          push_cast; rw [hq_zero, add_zero]; ring
        push_cast at hl hr ⊢
        calc (((u : ZMod q).val : ZMod q) + (q : ZMod q)) * ((x : ZMod q) + (t : ZMod q) * (M : ZMod q) * ((q / p : ℕ) : ZMod q))
            = (((u : ZMod q).val : ZMod q) + (q : ZMod q)) * (x : ZMod q) +
              (((u : ZMod q).val : ZMod q) + (q : ZMod q)) * ((t : ZMod q) * (M : ZMod q) * ((q / p : ℕ) : ZMod q)) := by ring
          _ = ((x : ZMod q) + (x : ZMod q) * (c : ZMod q) * ((q / p : ℕ) : ZMod q)) +
              ((u : ZMod q).val : ZMod q) * (t : ZMod q) * (M : ZMod q) * ((q / p : ℕ) : ZMod q) := by
              rw [hl, hr]
          _ = (x : ZMod q) + ((x : ZMod q) * (c : ZMod q) + ((u : ZMod q).val : ZMod q) * (t : ZMod q) * (M : ZMod q)) *
              ((q / p : ℕ) : ZMod q) := by ring
      rw [h1, hmul_qp]
      push_cast; ring
    have hσ_inj : ∀ t1 ∈ Finset.range p, ∀ t2 ∈ Finset.range p, σ t1 = σ t2 → t1 = t2 := by
      intro t1 ht1 t2 ht2 hEq
      have h1 := hσ_eq t1 ht1
      have h2 := hσ_eq t2 ht2
      rw [hEq] at h1
      have heq_mul : (u : ZMod q) * ((x + t1 * M * (q / p) : ℕ) : ZMod q) =
          (u : ZMod q) * ((x + t2 * M * (q / p) : ℕ) : ZMod q) := h1.trans h2.symm
      have heq_z := congrArg (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ·) heq_mul
      simp only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at heq_z
      have hsub : ((t1 * M * (q / p) : ℕ) : ZMod q) = ((t2 * M * (q / p) : ℕ) : ZMod q) := by
        push_cast at heq_z ⊢
        exact add_left_cancel heq_z
      have hdiv_q : (q : ℤ) ∣ (((t1 : ℤ) - (t2 : ℤ)) * (M : ℤ) * ((q / p : ℕ) : ℤ)) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast]
        have hsub' : (t1 : ZMod q) * (M : ZMod q) * ((q / p : ℕ) : ZMod q) =
            (t2 : ZMod q) * (M : ZMod q) * ((q / p : ℕ) : ZMod q) := by
          simpa using hsub
        linear_combination hsub'
      have hq_eq : (q : ℤ) = (p : ℤ) * ((q / p : ℕ) : ℤ) := by exact_mod_cast (Nat.mul_div_cancel' hpdvd).symm
      rw [hq_eq] at hdiv_q
      have hdiv_p : (p : ℤ) ∣ (((t1 : ℤ) - (t2 : ℤ)) * (M : ℤ)) := by
        have hne : ((q / p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hqp_pos.ne'
        rcases hdiv_q with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have h1' : (((t1 : ℤ) - (t2 : ℤ)) * (M : ℤ)) * ((q / p : ℕ) : ℤ) = ((p : ℤ) * k) * ((q / p : ℕ) : ℤ) := by
          linarith
        exact mul_right_cancel₀ hne h1'
      have hcopZ : IsCoprime (p : ℤ) (M : ℤ) := by exact_mod_cast hMp.symm
      have hdiv_diff : (p : ℤ) ∣ ((t1 : ℤ) - (t2 : ℤ)) := hcopZ.dvd_of_dvd_mul_right hdiv_p
      rw [mem_range] at ht1 ht2
      rcases hdiv_diff with ⟨k, hk⟩
      have hk0 : k = 0 := by nlinarith
      rw [hk0, mul_zero] at hk
      omega
    exact ⟨σ, hσ_mem, hσ_inj, hσ_eq⟩
  obtain ⟨σ, hσ_mem, hσ_inj, hσ_eq⟩ := hperm
  have hbij : ∑ t ∈ Finset.range p, χ (((x + σ t * M * (q / p) : ℕ) : ZMod q)) =
      ∑ t ∈ Finset.range p, χ (((x + t * M * (q / p) : ℕ) : ZMod q)) := by
    refine Finset.sum_bij (fun t _ => σ t) hσ_mem hσ_inj ?_ (fun _ _ => rfl)
    have himg : (Finset.range p).image σ = Finset.range p := by
      refine Finset.eq_of_subset_of_card_le (fun y hy => by
        rcases Finset.mem_image.mp hy with ⟨t, ht, rfl⟩; exact hσ_mem t ht) ?_
      rw [Finset.card_image_of_injOn (fun a ha b hb h => hσ_inj a ha b hb h)]
    intro b hb
    rw [← himg] at hb
    rcases Finset.mem_image.mp hb with ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  have hmul_eq : χ (u : ZMod q) * ∑ t ∈ Finset.range p, χ (((x + t * M * (q / p) : ℕ) : ZMod q)) =
      ∑ t ∈ Finset.range p, χ (((x + t * M * (q / p) : ℕ) : ZMod q)) := by
    rw [mul_sum]
    have hstep : ∑ t ∈ Finset.range p, χ (u : ZMod q) * χ (((x + t * M * (q / p) : ℕ) : ZMod q)) =
        ∑ t ∈ Finset.range p, χ (((x + σ t * M * (q / p) : ℕ) : ZMod q)) := by
      refine sum_congr rfl fun t ht => ?_
      rw [← map_mul, hσ_eq t ht]
    rw [hstep, hbij]
  exact eq_zero_of_mul_eq_self_left hu_ne hmul_eq
lemma granville_off_diag_zero {q k d₁ d₂ m₁ m₂ : ℕ} [NeZero q] (hq2 : 2 ≤ q) (hk : 2 ≤ k)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    (hd1 : d₁ ∣ q ^ (k - 1)) (hd2 : d₂ ∣ q ^ (k - 1)) (hne : d₁ ≠ d₂) :
    ∑ a ∈ (Icc 1 (q ^ k)).filter (fun a : ℕ => d₁ ∣ a + m₁ ∧ d₂ ∣ a + m₂),
      χ (((a + m₁) / d₁ : ℕ) : ZMod q) * star (χ (((a + m₂) / d₂ : ℕ) : ZMod q)) = 0 := by
  have hqpos : 0 < q := by omega
  have hqk_pos : 0 < q ^ k := pow_pos hqpos k
  have : NeZero (q ^ k) := ⟨hqk_pos.ne'⟩
  have hd1_pos : 0 < d₁ := Nat.pos_of_dvd_of_pos hd1 (pow_pos hqpos _)
  have hd2_pos : 0 < d₂ := Nat.pos_of_dvd_of_pos hd2 (pow_pos hqpos _)
  suffices hWLOG : ∀ {d₁ d₂ m₁ m₂ : ℕ} (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → d₁ ∣ q ^ (k - 1) → d₂ ∣ q ^ (k - 1) →
      (∃ p, p.Prime ∧ p ∣ q ∧ d₁.factorization p < d₂.factorization p) →
      ∑ a ∈ (Icc 1 (q ^ k)).filter (fun a : ℕ => d₁ ∣ a + m₁ ∧ d₂ ∣ a + m₂),
        χ (((a + m₁) / d₁ : ℕ) : ZMod q) * star (χ (((a + m₂) / d₂ : ℕ) : ZMod q)) = 0 by
    have hex_p : ∃ p, p.Prime ∧ p ∣ q ∧ d₁.factorization p ≠ d₂.factorization p := by
      by_contra hall
      push Not at hall
      apply hne
      apply Nat.eq_of_factorization_eq hd1_pos.ne' hd2_pos.ne'
      intro p
      by_cases hp : p.Prime ∧ p ∣ q
      · exact hall p hp.1 hp.2
      · have hzero : ∀ d, d ∣ q ^ (k - 1) → d.factorization p = 0 := by
          intro d hd
          by_cases hpr : p.Prime
          · have hnd : ¬ p ∣ q := fun h => hp ⟨hpr, h⟩
            have hnd2 : ¬ p ∣ d := fun h => hnd (hpr.dvd_of_dvd_pow (h.trans hd))
            exact Nat.factorization_eq_zero_of_not_dvd hnd2
          · exact Nat.factorization_eq_zero_of_not_prime d hpr
        rw [hzero d₁ hd1, hzero d₂ hd2]
    obtain ⟨p, hp, hpdvd, hvp_ne⟩ := hex_p
    rcases lt_or_gt_of_ne hvp_ne with hlt | hgt
    · exact hWLOG χ hprim hd1 hd2 ⟨p, hp, hpdvd, hlt⟩
    · have hconj :
          star (∑ a ∈ (Icc 1 (q ^ k)).filter (fun a : ℕ => d₁ ∣ a + m₁ ∧ d₂ ∣ a + m₂),
            χ (((a + m₁) / d₁ : ℕ) : ZMod q) * star (χ (((a + m₂) / d₂ : ℕ) : ZMod q))) =
          ∑ a ∈ (Icc 1 (q ^ k)).filter (fun a : ℕ => d₂ ∣ a + m₂ ∧ d₁ ∣ a + m₁),
            χ (((a + m₂) / d₂ : ℕ) : ZMod q) * star (χ (((a + m₁) / d₁ : ℕ) : ZMod q)) := by
        rw [Complex.star_def, map_sum (starRingEnd ℂ)]
        have hflt : (Icc 1 (q ^ k)).filter (fun a : ℕ => d₁ ∣ a + m₁ ∧ d₂ ∣ a + m₂) =
            (Icc 1 (q ^ k)).filter (fun a : ℕ => d₂ ∣ a + m₂ ∧ d₁ ∣ a + m₁) := by
          ext a; simp only [mem_filter]; tauto
        rw [hflt]
        refine sum_congr rfl fun a _ => ?_
        rw [map_mul, ← Complex.star_def, star_star, mul_comm]
      have h0 := hWLOG (m₁ := m₂) (m₂ := m₁) χ hprim hd2 hd1 ⟨p, hp, hpdvd, hgt⟩
      rw [← hconj] at h0
      have := congrArg star h0
      simpa using this
  intro d₁ d₂ m₁ m₂ χ hprim hd1 hd2 ⟨p, hp, hpdvd, hv_lt⟩
  have hd1_pos' : 0 < d₁ := Nat.pos_of_dvd_of_pos hd1 (pow_pos hqpos _)
  have hd2_pos' : 0 < d₂ := Nat.pos_of_dvd_of_pos hd2 (pow_pos hqpos _)
  let M : ℕ := q ^ k / p ^ ((q ^ k).factorization p)
  have hM_dvd : M ∣ q ^ k := Nat.div_dvd_of_dvd (Nat.ordProj_dvd (q ^ k) p)
  have hM_pos : 0 < M := Nat.pos_of_dvd_of_pos hM_dvd hqk_pos
  have hMp : Nat.Coprime M p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    exact Nat.not_dvd_ordCompl hp hqk_pos.ne'
  let Δ : ℕ := M * d₂ * (q / p)
  have hΔ_d2 : d₂ ∣ Δ := ⟨M * (q / p), by dsimp [Δ]; ring⟩
  have hΔ_d1q : d₁ * q ∣ Δ := by
    rw [← Nat.factorization_le_iff_dvd (Nat.mul_pos hd1_pos' hqpos).ne' (by
      have hqp : 0 < q / p := Nat.div_pos (Nat.le_of_dvd hqpos hpdvd) hp.pos
      dsimp [Δ]; positivity)]
    intro r
    by_cases hr : r.Prime
    · rw [Nat.factorization_mul hd1_pos'.ne' hqpos.ne', Finsupp.add_apply]
      have hqp_pos : 0 < q / p := Nat.div_pos (Nat.le_of_dvd hqpos hpdvd) hp.pos
      have hΔ_fac : Δ.factorization r = M.factorization r + d₂.factorization r + (q / p).factorization r := by
        dsimp [Δ]
        rw [Nat.factorization_mul (Nat.mul_pos hM_pos hd2_pos').ne' hqp_pos.ne',
          Nat.factorization_mul hM_pos.ne' hd2_pos'.ne', Finsupp.add_apply, Finsupp.add_apply]
      rw [hΔ_fac]
      by_cases hrp : r = p
      · rw [hrp]
        have hqp_f : (q / p).factorization p = q.factorization p - 1 := by
          rw [Nat.factorization_div hpdvd, Finsupp.tsub_apply, hp.factorization_self]
        have hq_vp : 1 ≤ q.factorization p := Nat.Prime.factorization_pos_of_dvd hp hqpos.ne' hpdvd
        rw [hqp_f]; omega
      · have hM_f : M.factorization r = (q ^ k).factorization r := by
          dsimp [M]
          rw [Nat.factorization_div (Nat.ordProj_dvd (q ^ k) p), Finsupp.tsub_apply,
            hp.factorization_pow, Finsupp.single_apply, if_neg (Ne.symm hrp), Nat.sub_zero]
        have hd1_f : d₁.factorization r ≤ (q ^ (k - 1)).factorization r :=
          (Nat.factorization_le_iff_dvd hd1_pos'.ne' (pow_pos hqpos _).ne').mpr hd1 r
        rw [hM_f, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hd1_f
        have hk_eq : k * q.factorization r = (k - 1) * q.factorization r + q.factorization r := by
          cases k with
          | zero => omega
          | succ m => simp [Nat.add_mul]
        omega
    · simp [Nat.factorization_eq_zero_of_not_prime _ hr]
  let F : ℕ → ℂ := fun a =>
    if d₁ ∣ a + m₁ ∧ d₂ ∣ a + m₂ then
      χ (((a + m₁) / d₁ : ℕ) : ZMod q) * star (χ (((a + m₂) / d₂ : ℕ) : ZMod q))
    else 0
  have hF_per : ∀ a : ℕ, F (a + q ^ k) = F a := by
    intro a
    have hd1_qk : d₁ ∣ q ^ k := hd1.trans (pow_dvd_pow q (by omega))
    have hd2_qk : d₂ ∣ q ^ k := hd2.trans (pow_dvd_pow q (by omega))
    have hd1q_qk : d₁ * q ∣ q ^ k := by
      have : q ^ k = q ^ (k - 1) * q := by
        cases k with
        | zero => omega
        | succ m => simp [pow_succ]
      rw [this]; exact Nat.mul_dvd_mul_right hd1 q
    have hd2q_qk : d₂ * q ∣ q ^ k := by
      have : q ^ k = q ^ (k - 1) * q := by
        cases k with
        | zero => omega
        | succ m => simp [pow_succ]
      rw [this]; exact Nat.mul_dvd_mul_right hd2 q
    dsimp [F]
    have hiff1 : d₁ ∣ (a + q ^ k + m₁) ↔ d₁ ∣ (a + m₁) := by
      rw [show a + q ^ k + m₁ = (a + m₁) + q ^ k by ring]
      exact Nat.dvd_add_left hd1_qk
    have hiff2 : d₂ ∣ (a + q ^ k + m₂) ↔ d₂ ∣ (a + m₂) := by
      rw [show a + q ^ k + m₂ = (a + m₂) + q ^ k by ring]
      exact Nat.dvd_add_left hd2_qk
    by_cases hc : d₁ ∣ a + m₁ ∧ d₂ ∣ a + m₂
    · rw [if_pos ⟨hiff1.mpr hc.1, hiff2.mpr hc.2⟩, if_pos hc]
      have hq1 : ((a + q ^ k + m₁) / d₁ : ℕ) = (a + m₁) / d₁ + (q ^ k / d₁) := by
        rw [show a + q ^ k + m₁ = (a + m₁) + q ^ k by ring, Nat.add_div_of_dvd_left hd1_qk]
      have hq2' : ((a + q ^ k + m₂) / d₂ : ℕ) = (a + m₂) / d₂ + (q ^ k / d₂) := by
        rw [show a + q ^ k + m₂ = (a + m₂) + q ^ k by ring, Nat.add_div_of_dvd_left hd2_qk]
      have hdvd1 : q ∣ (q ^ k / d₁) := by
        obtain ⟨c, hc'⟩ := hd1q_qk
        refine ⟨c, ?_⟩
        have : q ^ k = d₁ * (q * c) := by linarith
        rw [this, Nat.mul_div_cancel_left _ hd1_pos']
      have hdvd2 : q ∣ (q ^ k / d₂) := by
        obtain ⟨c, hc'⟩ := hd2q_qk
        refine ⟨c, ?_⟩
        have : q ^ k = d₂ * (q * c) := by linarith
        rw [this, Nat.mul_div_cancel_left _ hd2_pos']
      rw [hq1, hq2']
      push_cast
      rw [(ZMod.natCast_eq_zero_iff _ _).mpr hdvd1, (ZMod.natCast_eq_zero_iff _ _).mpr hdvd2,
        add_zero, add_zero]
    · rw [if_neg (by tauto), if_neg hc]
  have hshift_eq : ∀ t : ℕ, ∑ a ∈ Icc 1 (q ^ k), F (a + t * Δ) = ∑ a ∈ Icc 1 (q ^ k), F a := by
    intro t
    have hF_mod : ∀ a : ℕ, F (a % q ^ k) = F a := by
      intro a
      have hdiv := Nat.div_add_mod a (q ^ k)
      have hstep : ∀ s : ℕ, F (a % q ^ k + s * q ^ k) = F (a % q ^ k) := by
        intro s
        induction s with
        | zero => simp
        | succ s ih =>
          rw [show a % q ^ k + (s + 1) * q ^ k = (a % q ^ k + s * q ^ k) + q ^ k by ring,
            hF_per, ih]
      have htmp := hstep (a / q ^ k)
      rw [show a % q ^ k + a / q ^ k * q ^ k = q ^ k * (a / q ^ k) + a % q ^ k by ring, hdiv] at htmp
      exact htmp.symm
    refine Finset.sum_bij (fun a _ => if (a + t * Δ) % q ^ k = 0 then q ^ k else (a + t * Δ) % q ^ k)
      ?_ ?_ ?_ ?_
    · intro a _; rw [mem_Icc]
      have hlt := Nat.mod_lt (a + t * Δ) hqk_pos
      split_ifs with h0
      · exact ⟨hqk_pos, le_rfl⟩
      · exact ⟨Nat.pos_of_ne_zero h0, hlt.le⟩
    · intro a1 ha1 a2 ha2 heq
      rw [mem_Icc] at ha1 ha2
      have hmod : (a1 + t * Δ) % q ^ k = (a2 + t * Δ) % q ^ k := by
        have h1 := Nat.mod_lt (a1 + t * Δ) hqk_pos
        have h2 := Nat.mod_lt (a2 + t * Δ) hqk_pos
        split_ifs at heq with c1 c2 <;> omega
      have hz : ((a1 + t * Δ : ℕ) : ZMod (q ^ k)) = ((a2 + t * Δ : ℕ) : ZMod (q ^ k)) := by
        rw [← ZMod.natCast_mod (a1 + t * Δ), ← ZMod.natCast_mod (a2 + t * Δ), hmod]
      push_cast at hz
      have ha_z : (a1 : ZMod (q ^ k)) = (a2 : ZMod (q ^ k)) := add_right_cancel hz
      have hma : a1 % q ^ k = a2 % q ^ k := by
        have := congrArg ZMod.val ha_z
        simpa [ZMod.val_natCast] using this
      have hlt1 : a1 < q ^ k ∨ a1 = q ^ k := by omega
      have hlt2 : a2 < q ^ k ∨ a2 = q ^ k := by omega
      rcases hlt1 with h1 | rfl <;> rcases hlt2 with h2 | rfl
      · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hma; exact hma
      · rw [Nat.mod_eq_of_lt h1, Nat.mod_self] at hma; omega
      · rw [Nat.mod_self, Nat.mod_eq_of_lt h2] at hma; omega
      · rfl
    · intro b hb
      rw [mem_Icc] at hb
      let a0 := (b + q ^ k * (t * Δ + 1) - t * Δ) % q ^ k
      let a := if a0 = 0 then q ^ k else a0
      refine ⟨a, mem_Icc.mpr (by
        dsimp [a]; have hlt := Nat.mod_lt (b + q ^ k * (t * Δ + 1) - t * Δ) hqk_pos
        split_ifs with h0
        · exact ⟨hqk_pos, le_rfl⟩
        · exact ⟨Nat.pos_of_ne_zero h0, hlt.le⟩), ?_⟩
      have hmod_a : (a + t * Δ) % q ^ k = b % q ^ k := by
        have hza : (a : ZMod (q ^ k)) = (a0 : ZMod (q ^ k)) := by
          dsimp [a]; split_ifs with h0
          · rw [h0, ZMod.natCast_self, Nat.cast_zero]
          · rfl
        have hza0 : (a0 : ZMod (q ^ k)) = (b : ZMod (q ^ k)) - ((t * Δ : ℕ) : ZMod (q ^ k)) := by
          dsimp [a0]
          rw [ZMod.natCast_mod]
          have hge1 : t * Δ ≤ q ^ k * (t * Δ + 1) := by
            calc t * Δ ≤ t * Δ + 1 := Nat.le_succ _
              _ = 1 * (t * Δ + 1) := (one_mul _).symm
              _ ≤ q ^ k * (t * Δ + 1) := Nat.mul_le_mul_right _ hqk_pos
          have hge : t * Δ ≤ b + q ^ k * (t * Δ + 1) := le_add_of_le_right hge1
          rw [Nat.cast_sub hge, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
        have hz_sum : ((a + t * Δ : ℕ) : ZMod (q ^ k)) = (b : ZMod (q ^ k)) := by
          rw [Nat.cast_add, hza, hza0]; ring
        have hval := congrArg ZMod.val hz_sum
        rw [ZMod.val_natCast, ZMod.val_natCast] at hval
        exact hval
      rw [hmod_a]
      by_cases hbq : b = q ^ k
      · subst hbq; simp
      · rw [Nat.mod_eq_of_lt (by omega), if_neg (by omega)]
    · intro a _
      split_ifs with h0
      · have h1 := hF_mod (a + t * Δ)
        rw [h0] at h1
        have h2 : F (q ^ k) = F 0 := by simpa using hF_per 0
        rw [h2, h1]
      · exact (hF_mod (a + t * Δ)).symm
  have hinner_zero : ∀ a : ℕ, ∑ t ∈ Finset.range p, F (a + t * Δ) = 0 := by
    intro a
    have hd1_Δ : d₁ ∣ Δ := dvd_trans (dvd_mul_right d₁ q) hΔ_d1q
    by_cases hc : d₁ ∣ a + m₁ ∧ d₂ ∣ a + m₂
    · have hterm : ∀ t ∈ Finset.range p,
          F (a + t * Δ) = χ (((a + m₁) / d₁ : ℕ) : ZMod q) *
            star (χ ((((a + m₂) / d₂ + t * M * (q / p) : ℕ) : ZMod q))) := by
        intro t _
        dsimp [F]
        have h1 : d₁ ∣ a + t * Δ + m₁ := by
          rw [show a + t * Δ + m₁ = (a + m₁) + t * Δ by ring]
          exact dvd_add hc.1 (dvd_mul_of_dvd_right hd1_Δ t)
        have h2 : d₂ ∣ a + t * Δ + m₂ := by
          rw [show a + t * Δ + m₂ = (a + m₂) + t * Δ by ring]
          exact dvd_add hc.2 (dvd_mul_of_dvd_right hΔ_d2 t)
        rw [if_pos ⟨h1, h2⟩]
        have hdiv1 : ((a + t * Δ + m₁) / d₁ : ℕ) = (a + m₁) / d₁ + t * (Δ / d₁) := by
          rw [show a + t * Δ + m₁ = (a + m₁) + t * Δ by ring,
            Nat.add_div_of_dvd_left (dvd_mul_of_dvd_right hd1_Δ t), Nat.mul_div_assoc t hd1_Δ]
        have hq_dvd_Δd1 : q ∣ (Δ / d₁) := by
          obtain ⟨c, hc'⟩ := hΔ_d1q
          refine ⟨c, ?_⟩
          have : Δ = d₁ * (q * c) := by linarith
          rw [this, Nat.mul_div_cancel_left _ hd1_pos']
        have hχ1 : χ (((a + t * Δ + m₁) / d₁ : ℕ) : ZMod q) = χ (((a + m₁) / d₁ : ℕ) : ZMod q) := by
          rw [hdiv1]; push_cast
          rw [(ZMod.natCast_eq_zero_iff _ _).mpr hq_dvd_Δd1, mul_zero, add_zero]
        have hdiv2 : ((a + t * Δ + m₂) / d₂ : ℕ) = (a + m₂) / d₂ + t * M * (q / p) := by
          rw [show a + t * Δ + m₂ = (a + m₂) + t * Δ by ring,
            Nat.add_div_of_dvd_left (dvd_mul_of_dvd_right hΔ_d2 t)]
          congr 1
          have hmul : t * Δ = d₂ * (t * M * (q / p)) := by dsimp [Δ]; ring
          rw [hmul, Nat.mul_div_cancel_left _ hd2_pos']
        rw [hχ1, hdiv2]
      rw [sum_congr rfl hterm, ← mul_sum]
      have hstar_sum : ∑ t ∈ Finset.range p, star (χ ((((a + m₂) / d₂ + t * M * (q / p) : ℕ) : ZMod q))) =
          star (∑ t ∈ Finset.range p, χ ((((a + m₂) / d₂ + t * M * (q / p) : ℕ) : ZMod q))) := by
        rw [Complex.star_def, map_sum (starRingEnd ℂ)]
      rw [hstar_sum, primitive_sum_coset_eq_zero χ hprim hp hpdvd hMp ((a + m₂) / d₂),
        star_zero, mul_zero]
    · refine sum_eq_zero fun t _ => ?_
      dsimp [F]
      have hneg : ¬ (d₁ ∣ a + t * Δ + m₁ ∧ d₂ ∣ a + t * Δ + m₂) := by
        rintro ⟨h1, h2⟩
        apply hc
        rw [show a + t * Δ + m₁ = (a + m₁) + t * Δ by ring] at h1
        rw [show a + t * Δ + m₂ = (a + m₂) + t * Δ by ring] at h2
        exact ⟨(Nat.dvd_add_left (dvd_mul_of_dvd_right hd1_Δ t)).mp h1,
               (Nat.dvd_add_left (dvd_mul_of_dvd_right hΔ_d2 t)).mp h2⟩
      exact if_neg hneg
  have hpS : (p : ℂ) * ∑ a ∈ Icc 1 (q ^ k), F a = 0 := by
    calc (p : ℂ) * ∑ a ∈ Icc 1 (q ^ k), F a
        = ∑ _t ∈ Finset.range p, ∑ a ∈ Icc 1 (q ^ k), F a := by
          rw [sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ∑ t ∈ Finset.range p, ∑ a ∈ Icc 1 (q ^ k), F (a + t * Δ) :=
          sum_congr rfl fun t _ => (hshift_eq t).symm
      _ = ∑ a ∈ Icc 1 (q ^ k), ∑ t ∈ Finset.range p, F (a + t * Δ) := sum_comm
      _ = 0 := sum_eq_zero fun a _ => hinner_zero a
  have hS0 : ∑ a ∈ Icc 1 (q ^ k), F a = 0 := by
    have hp_ne : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    exact (mul_eq_zero.mp hpS).resolve_left hp_ne
  rw [← sum_filter] at hS0
  exact hS0
def isGoodRes (q k H a : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ q → ∀ m ∈ Icc 1 (2 * H), ¬ (p ^ k ∣ a + m)
noncomputable def goodClasses (q k H : ℕ) : Finset ℕ :=
  (Icc 1 (q ^ k)).filter (fun a => isGoodRes q k H a)
lemma tildeChi_good_factor {q k H a m : ℕ} [NeZero q] (hk : 2 ≤ k)
    (χ : DirichletCharacter ℂ q) (tildeχ : ℕ →*₀ ℂ)
    (htilde_cop : ∀ p, p.Prime → ¬ p ∣ q → tildeχ p = χ (p : ZMod q))
    (hgood : isGoodRes q k H a) (hm : m ∈ Icc 1 (2 * H)) :
    let d := Nat.gcd (a + m) (q ^ k)
    d ∣ q ^ (k - 1) ∧ tildeχ (a + m) = tildeχ d * χ (((a + m) / d : ℕ) : ZMod q) := by
  have hqpos : 0 < q := NeZero.pos q
  have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
  have ham_pos : 0 < a + m := by omega
  let d := Nat.gcd (a + m) (q ^ k)
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left _ ham_pos
  have hd_dvd_am : d ∣ a + m := Nat.gcd_dvd_left _ _
  have hd_dvd_qk : d ∣ q ^ k := Nat.gcd_dvd_right _ _
  have hd_dvd_qk1 : d ∣ q ^ (k - 1) := by
    rw [← Nat.factorization_le_iff_dvd hd_pos.ne' (pow_pos hqpos _).ne']
    intro p
    by_cases hp : p.Prime
    · by_cases hpdvd : p ∣ q
      · have hnot : ¬ (p ^ k ∣ a + m) := hgood p hp hpdvd m hm
        have hlt : (a + m).factorization p < k := by
          by_contra hge; push Not at hge
          exact hnot ((pow_dvd_pow p hge).trans (Nat.ordProj_dvd (a + m) p))
        have hd_le_am : d.factorization p ≤ (a + m).factorization p :=
          (Nat.factorization_le_iff_dvd hd_pos.ne' ham_pos.ne').mpr hd_dvd_am p
        have hq_vp : 1 ≤ q.factorization p := Nat.Prime.factorization_pos_of_dvd hp hqpos.ne' hpdvd
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        have hle_k1 : d.factorization p ≤ k - 1 := by omega
        exact hle_k1.trans (Nat.le_mul_of_pos_right _ hq_vp)
      · have hnd : ¬ p ∣ d := fun h => hpdvd (hp.dvd_of_dvd_pow (h.trans hd_dvd_qk))
        rw [Nat.factorization_eq_zero_of_not_dvd hnd]
        exact Nat.zero_le _
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  refine ⟨hd_dvd_qk1, ?_⟩
  let u := (a + m) / d
  have hu_pos : 0 < u := Nat.div_pos (Nat.le_of_dvd ham_pos hd_dvd_am) hd_pos
  have ham_eq : a + m = d * u := (Nat.mul_div_cancel' hd_dvd_am).symm
  have hu_cop : Nat.Coprime u q := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne1
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne1
    have hp_u : p ∣ u := hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hp_q : p ∣ q := hpdvd.trans (Nat.gcd_dvd_right _ _)
    have hdp_am : d * p ∣ a + m := by rw [ham_eq]; exact Nat.mul_dvd_mul_left d hp_u
    have hdp_qk : d * p ∣ q ^ k := by
      have : q ^ k = q ^ (k - 1) * q := by
        cases k with
        | zero => omega
        | succ m => simp [pow_succ]
      rw [this]; exact Nat.mul_dvd_mul hd_dvd_qk1 hp_q
    have hle : d * p ≤ d := Nat.le_of_dvd hd_pos (Nat.dvd_gcd hdp_am hdp_qk)
    have := hp.two_le
    nlinarith
  have htilde_u : tildeχ u = χ (u : ZMod q) := by
    have hprod_eq : ∀ n : ℕ, 1 ≤ n → Nat.Coprime n q → tildeχ n = χ (n : ZMod q) := by
      intro n
      induction n using Nat.strongRecOn with
      | ind n ih =>
        intro hn1 hncop
        by_cases hn_eq1 : n = 1
        · subst hn_eq1; simp
        · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn_eq1
          obtain ⟨r, rfl⟩ := hpn
          have hr1 : 1 ≤ r := by
            by_contra h0; push Not at h0
            have : r = 0 := by omega
            subst this; simp at hn1
          have hr_lt : r < p * r := by have := hp.two_le; nlinarith
          have hp_cop : Nat.Coprime p q := hncop.coprime_dvd_left (dvd_mul_right p r)
          have hr_cop : Nat.Coprime r q := hncop.coprime_dvd_left (dvd_mul_left r p)
          have hp_nd : ¬ p ∣ q := hp.coprime_iff_not_dvd.mp hp_cop
          rw [map_mul, Nat.cast_mul, map_mul, htilde_cop p hp hp_nd, ih r hr_lt hr1 hr_cop]
    exact hprod_eq u hu_pos hu_cop
  conv_lhs => rw [ham_eq]
  rw [map_mul, htilde_u]
private lemma granville_badSet_card_le {q k H : ℕ} (hqpos : 0 < q) :
    (((Icc 1 (q ^ k)).filter (fun a : ℕ => ¬ isGoodRes q k H a)).card : ℝ) ≤
      (2 * (H : ℝ) * (q : ℝ)) * (((q ^ k : ℕ) : ℝ) / ((2 : ℝ) ^ k)) := by
  have hqk_pos : (0 : ℝ) < ((q ^ k : ℕ) : ℝ) := by exact_mod_cast pow_pos hqpos k
  let badSet := (Icc 1 (q ^ k)).filter (fun a : ℕ => ¬ isGoodRes q k H a)
  have hsub : badSet ⊆
      ((Icc 1 q).filter (fun p : ℕ => p.Prime ∧ p ∣ q)).biUnion fun p =>
        (Icc 1 (2 * H)).biUnion fun m =>
          (Icc 1 (q ^ k)).filter (fun a : ℕ => p ^ k ∣ a + m) := by
    intro a ha
    rw [mem_filter] at ha
    have ha_Icc := ha.1
    have ha_not := ha.2
    unfold isGoodRes at ha_not
    push Not at ha_not
    obtain ⟨p, hp, hpdvd, m, hm, hpk⟩ := ha_not
    rw [Finset.mem_biUnion]
    refine ⟨p, mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.one_le, Nat.le_of_dvd hqpos hpdvd⟩, hp, hpdvd⟩, ?_⟩
    rw [Finset.mem_biUnion]
    exact ⟨m, hm, mem_filter.mpr ⟨ha_Icc, hpk⟩⟩
  have hper_pm : ∀ p ∈ (Icc 1 q).filter (fun p : ℕ => p.Prime ∧ p ∣ q),
      ∀ m ∈ Icc 1 (2 * H),
        (((Icc 1 (q ^ k)).filter (fun a : ℕ => p ^ k ∣ a + m)).card : ℝ) ≤
          ((q ^ k : ℕ) : ℝ) / ((2 : ℝ) ^ k) := by
    intro p hp m _
    have hpr := (mem_filter.mp hp).2.1
    have hpdvd := (mem_filter.mp hp).2.2
    have hpk_dvd : p ^ k ∣ q ^ k := pow_dvd_pow_of_dvd hpdvd k
    have hpk_pos : 0 < p ^ k := pow_pos hpr.pos k
    have hcard_le : ((Icc 1 (q ^ k)).filter (fun a : ℕ => p ^ k ∣ a + m)).card ≤ q ^ k / p ^ k := by
      let S := (Icc 1 (q ^ k)).filter (fun a : ℕ => p ^ k ∣ a + m)
      let f : ℕ → ℕ := fun a => (a - 1) / p ^ k
      have hmaps : ∀ a ∈ S, f a ∈ Finset.range (q ^ k / p ^ k) := by
        intro a ha
        rw [mem_filter, mem_Icc] at ha
        rw [mem_range, Nat.div_lt_iff_lt_mul hpk_pos]
        have : q ^ k / p ^ k * p ^ k = q ^ k := Nat.div_mul_cancel hpk_dvd
        omega
      have hinj : Set.InjOn f S := by
        intro a1 ha1 a2 ha2 heq
        rw [Finset.mem_coe, mem_filter, mem_Icc] at ha1 ha2
        have hd1 := Nat.div_add_mod (a1 - 1) (p ^ k)
        have hd2 := Nat.div_add_mod (a2 - 1) (p ^ k)
        have hm1 := Nat.mod_lt (a1 - 1) hpk_pos
        have hm2 := Nat.mod_lt (a2 - 1) hpk_pos
        dsimp [f] at heq
        rw [heq] at hd1
        set Q0 : ℕ := p ^ k * ((a2 - 1) / p ^ k)
        have hge_d1 : Q0 ≤ a1 - 1 := Nat.le.intro hd1
        have hge_d2 : Q0 ≤ a2 - 1 := Nat.le.intro hd2
        have hlt_d1 : a1 - 1 < Q0 + p ^ k := by rw [← hd1]; exact Nat.add_lt_add_left hm1 Q0
        have hlt_d2 : a2 - 1 < Q0 + p ^ k := by rw [← hd2]; exact Nat.add_lt_add_left hm2 Q0
        have ha1_1 : 1 ≤ a1 := ha1.1.1
        have ha2_1 : 1 ≤ a2 := ha2.1.1
        rcases le_total a1 a2 with hle12 | hle21
        · have hdiff : p ^ k ∣ a2 - a1 := by
            have : (a2 + m) - (a1 + m) = a2 - a1 := by omega
            rw [← this]; exact Nat.dvd_sub ha2.2 ha1.2
          by_contra hne'
          have hge := Nat.le_of_dvd (by omega) hdiff
          have hdiff_lt : a2 - a1 < p ^ k := by omega
          omega
        · have hdiff : p ^ k ∣ a1 - a2 := by
            have : (a1 + m) - (a2 + m) = a1 - a2 := by omega
            rw [← this]; exact Nat.dvd_sub ha1.2 ha2.2
          by_contra hne'
          have hge := Nat.le_of_dvd (by omega) hdiff
          have hdiff_lt : a1 - a2 < p ^ k := by omega
          omega
      calc S.card ≤ (Finset.range (q ^ k / p ^ k)).card := Finset.card_le_card_of_injOn f hmaps hinj
        _ = q ^ k / p ^ k := Finset.card_range _
    have hdiv_le : ((q ^ k / p ^ k : ℕ) : ℝ) ≤ ((q ^ k : ℕ) : ℝ) / ((2 : ℝ) ^ k) := by
      have h1 : ((q ^ k / p ^ k : ℕ) : ℝ) = ((q ^ k : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ) := by
        rw [Nat.cast_div hpk_dvd (by positivity)]
      rw [h1]
      have h2p : (2 : ℝ) ^ k ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.pow_le_pow_left hpr.two_le k
      exact div_le_div_of_nonneg_left hqk_pos.le (by positivity) h2p
    exact (Nat.cast_le.mpr hcard_le).trans hdiv_le
  have hcard_union : (badSet.card : ℝ) ≤
      ∑ p ∈ (Icc 1 q).filter (fun p : ℕ => p.Prime ∧ p ∣ q),
        ∑ m ∈ Icc 1 (2 * H),
          (((Icc 1 (q ^ k)).filter (fun a : ℕ => p ^ k ∣ a + m)).card : ℝ) := by
    have hnat : badSet.card ≤
        ∑ p ∈ (Icc 1 q).filter (fun p : ℕ => p.Prime ∧ p ∣ q),
          ∑ m ∈ Icc 1 (2 * H),
            ((Icc 1 (q ^ k)).filter (fun a : ℕ => p ^ k ∣ a + m)).card :=
      (card_le_card hsub).trans (Finset.card_biUnion_le.trans
        (sum_le_sum fun _ _ => Finset.card_biUnion_le))
    exact_mod_cast hnat
  calc (badSet.card : ℝ)
      ≤ ∑ p ∈ (Icc 1 q).filter (fun p : ℕ => p.Prime ∧ p ∣ q),
          ∑ m ∈ Icc 1 (2 * H), (((q ^ k : ℕ) : ℝ) / ((2 : ℝ) ^ k)) :=
        hcard_union.trans (sum_le_sum fun p hp => sum_le_sum fun m hm => hper_pm p hp m hm)
    _ = (((Icc 1 q).filter (fun p : ℕ => p.Prime ∧ p ∣ q)).card : ℝ) *
          (2 * (H : ℝ)) * (((q ^ k : ℕ) : ℝ) / ((2 : ℝ) ^ k)) := by
        simp [Nat.card_Icc, show 2 * H + 1 - 1 = 2 * H by omega, mul_assoc]
    _ ≤ (q : ℝ) * (2 * (H : ℝ)) * (((q ^ k : ℕ) : ℝ) / ((2 : ℝ) ^ k)) := by
        have hc : (((Icc 1 q).filter (fun p : ℕ => p.Prime ∧ p ∣ q)).card : ℝ) ≤ (q : ℝ) := by
          have : ((Icc 1 q).filter (fun p : ℕ => p.Prime ∧ p ∣ q)).card ≤ (Icc 1 q).card :=
            Finset.card_filter_le _ _
          rw [Nat.card_Icc, show q + 1 - 1 = q by omega] at this
          exact_mod_cast this
        have hnn : 0 ≤ (2 * (H : ℝ)) * (((q ^ k : ℕ) : ℝ) / ((2 : ℝ) ^ k)) := by positivity
        have := mul_le_mul_of_nonneg_right hc hnn
        linarith
    _ = (2 * (H : ℝ) * (q : ℝ)) * (((q ^ k : ℕ) : ℝ) / ((2 : ℝ) ^ k)) := by ring
private lemma granville_Sfull_diag_eq {q k H' : ℕ} [NeZero q] (hq2 : 2 ≤ q) (hk2 : 2 ≤ k)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (tildeχ : ℕ →*₀ ℂ)
    (htilde_norm : ∀ n, 1 ≤ n → ‖tildeχ n‖ = 1) :
    let Sd : ℕ → ℕ → ℂ := fun d a =>
      ∑ m ∈ (Icc 1 H').filter (fun m : ℕ => d ∣ a + m), χ (((a + m) / d : ℕ) : ZMod q)
    let Sfull : ℕ → ℂ := fun a => ∑ d ∈ (q ^ (k - 1)).divisors, tildeχ d * Sd d a
    ∑ a ∈ Icc 1 (q ^ k), ‖Sfull a‖ ^ 2 =
      ∑ d ∈ (q ^ (k - 1)).divisors, ∑ a ∈ Icc 1 (q ^ k), ‖Sd d a‖ ^ 2 := by
  intro Sd Sfull
  have hqpos : 0 < q := by omega
  apply Complex.ofReal_injective
  have hprod_m : ∀ (a d1 d2 : ℕ),
      Sd d1 a * star (Sd d2 a) =
      ∑ m1 ∈ Icc 1 H', ∑ m2 ∈ Icc 1 H',
        if d1 ∣ a + m1 ∧ d2 ∣ a + m2 then
          χ (((a + m1) / d1 : ℕ) : ZMod q) * star (χ (((a + m2) / d2 : ℕ) : ZMod q))
        else 0 := by
    intro a d1 d2
    dsimp [Sd]
    rw [map_sum (starRingEnd ℂ), sum_filter, sum_filter, sum_mul]
    refine sum_congr rfl fun m1 _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun m2 _ => ?_
    by_cases h1 : d1 ∣ a + m1 <;> by_cases h2 : d2 ∣ a + m2 <;> simp [h1, h2]
  have hlhs : ((∑ a ∈ Icc 1 (q ^ k), ‖Sfull a‖ ^ 2 : ℝ) : ℂ) =
      ∑ d1 ∈ (q ^ (k - 1)).divisors, ∑ d2 ∈ (q ^ (k - 1)).divisors,
        tildeχ d1 * star (tildeχ d2) *
          ∑ m1 ∈ Icc 1 H', ∑ m2 ∈ Icc 1 H',
            ∑ a ∈ (Icc 1 (q ^ k)).filter (fun a : ℕ => d1 ∣ a + m1 ∧ d2 ∣ a + m2),
              χ (((a + m1) / d1 : ℕ) : ZMod q) * star (χ (((a + m2) / d2 : ℕ) : ZMod q)) := by
    rw [Complex.ofReal_sum]
    have hpt : ∀ a ∈ Icc 1 (q ^ k),
        ((‖Sfull a‖ ^ 2 : ℝ) : ℂ) =
        ∑ d1 ∈ (q ^ (k - 1)).divisors, ∑ d2 ∈ (q ^ (k - 1)).divisors,
          tildeχ d1 * star (tildeχ d2) *
            ∑ m1 ∈ Icc 1 H', ∑ m2 ∈ Icc 1 H',
              if d1 ∣ a + m1 ∧ d2 ∣ a + m2 then
                χ (((a + m1) / d1 : ℕ) : ZMod q) * star (χ (((a + m2) / d2 : ℕ) : ZMod q))
              else 0 := by
      intro a _
      rw [Complex.ofReal_pow, ← Complex.mul_conj']
      dsimp [Sfull]
      rw [map_sum (starRingEnd ℂ), sum_mul]
      refine sum_congr rfl fun d1 _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun d2 _ => ?_
      rw [map_mul, ← Complex.star_def, ← hprod_m a d1 d2]
      ring
    rw [sum_congr rfl hpt, sum_comm]
    refine sum_congr rfl fun d1 _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun d2 _ => ?_
    rw [← mul_sum]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun m1 _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun m2 _ => ?_
    rw [sum_filter]
  rw [hlhs]
  have hdiag_only :
      ∑ d1 ∈ (q ^ (k - 1)).divisors, ∑ d2 ∈ (q ^ (k - 1)).divisors,
        tildeχ d1 * star (tildeχ d2) *
          ∑ m1 ∈ Icc 1 H', ∑ m2 ∈ Icc 1 H',
            ∑ a ∈ (Icc 1 (q ^ k)).filter (fun a : ℕ => d1 ∣ a + m1 ∧ d2 ∣ a + m2),
              χ (((a + m1) / d1 : ℕ) : ZMod q) * star (χ (((a + m2) / d2 : ℕ) : ZMod q)) =
      ∑ d ∈ (q ^ (k - 1)).divisors,
        ∑ m1 ∈ Icc 1 H', ∑ m2 ∈ Icc 1 H',
          ∑ a ∈ (Icc 1 (q ^ k)).filter (fun a : ℕ => d ∣ a + m1 ∧ d ∣ a + m2),
            χ (((a + m1) / d : ℕ) : ZMod q) * star (χ (((a + m2) / d : ℕ) : ZMod q)) := by
    refine sum_congr rfl fun d1 hd1 => ?_
    rw [sum_eq_single d1]
    · have hd1_pos : 1 ≤ d1 := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd1).1 (pow_pos hqpos _)
      have hunit : tildeχ d1 * star (tildeχ d1) = 1 := by
        rw [Complex.star_def, Complex.mul_conj', htilde_norm d1 hd1_pos]; simp
      rw [hunit, one_mul]
    · intro d2 hd2 hdne
      have h0 : ∑ m1 ∈ Icc 1 H', ∑ m2 ∈ Icc 1 H',
          ∑ a ∈ (Icc 1 (q ^ k)).filter (fun a : ℕ => d1 ∣ a + m1 ∧ d2 ∣ a + m2),
            χ (((a + m1) / d1 : ℕ) : ZMod q) * star (χ (((a + m2) / d2 : ℕ) : ZMod q)) = 0 := by
        refine sum_eq_zero fun m1 _ => sum_eq_zero fun m2 _ => ?_
        exact granville_off_diag_zero hq2 hk2 χ hprim (Nat.mem_divisors.mp hd1).1
          (Nat.mem_divisors.mp hd2).1 hdne.symm
      rw [h0, mul_zero]
    · intro h; exact (h hd1).elim
  rw [hdiag_only, Complex.ofReal_sum]
  refine sum_congr rfl fun d _ => ?_
  rw [Complex.ofReal_sum]
  simp_rw [sum_filter]
  trans ∑ a ∈ Icc 1 (q ^ k), ∑ m1 ∈ Icc 1 H', ∑ m2 ∈ Icc 1 H',
      if d ∣ a + m1 ∧ d ∣ a + m2 then
        χ (((a + m1) / d : ℕ) : ZMod q) * star (χ (((a + m2) / d : ℕ) : ZMod q))
      else 0
  · trans ∑ m1 ∈ Icc 1 H', ∑ a ∈ Icc 1 (q ^ k), ∑ m2 ∈ Icc 1 H',
        if d ∣ a + m1 ∧ d ∣ a + m2 then
          χ (((a + m1) / d : ℕ) : ZMod q) * star (χ (((a + m2) / d : ℕ) : ZMod q))
        else 0
    · refine sum_congr rfl fun _ _ => sum_comm
    · exact sum_comm
  · refine sum_congr rfl fun a _ => ?_
    rw [Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def, hprod_m a d d]
private lemma granville_single_i_lower {q k i H0' : ℕ} [NeZero q] (hqpos : 0 < q) (hki1 : 1 ≤ k - i)
    (χ : DirichletCharacter ℂ q) :
    let Sd : ℕ → ℕ → ℕ → ℂ := fun d a H' =>
      ∑ m ∈ (Icc 1 H').filter (fun m : ℕ => d ∣ a + m), χ (((a + m) / d : ℕ) : ZMod q)
    ((q ^ k : ℕ) : ℝ) / (2 * (q : ℝ)) ≤
      ∑ a ∈ Icc 1 (q ^ k), ‖Sd (q ^ i) a (H0' + q ^ i) - Sd (q ^ i) a H0'‖ ^ 2 := by
  intro Sd
  have hqk_pos : (0 : ℝ) < ((q ^ k : ℕ) : ℝ) := by exact_mod_cast pow_pos hqpos k
  have : NeZero (q ^ k) := ⟨(pow_pos hqpos k).ne'⟩
  let qi := q ^ i
  have hqi_pos : 0 < qi := pow_pos hqpos i
  have hterm_eq : ∀ a : ℕ,
      Sd qi a (H0' + qi) - Sd qi a H0' = χ ((((a + H0') / qi + 1 : ℕ) : ZMod q)) := by
    intro a
    dsimp [Sd]
    have hsub : (Icc 1 (H0' + qi)).filter (fun m : ℕ => qi ∣ a + m) =
        ((Icc 1 H0').filter (fun m : ℕ => qi ∣ a + m)) ∪
        ((Ioc H0' (H0' + qi)).filter (fun m : ℕ => qi ∣ a + m)) := by
      ext m; simp only [mem_filter, mem_union, mem_Icc, mem_Ioc]; omega
    have hdisj : Disjoint ((Icc 1 H0').filter (fun m : ℕ => qi ∣ a + m))
        ((Ioc H0' (H0' + qi)).filter (fun m : ℕ => qi ∣ a + m)) := by
      rw [disjoint_left]; intro m h1 h2
      simp only [mem_filter, mem_Icc, mem_Ioc] at h1 h2; omega
    rw [hsub, sum_union hdisj, add_sub_cancel_left]
    let m0 := ((a + H0') / qi + 1) * qi - a
    have hm0_mul : a + m0 = ((a + H0') / qi + 1) * qi := by
      have hlt : a + H0' < ((a + H0') / qi + 1) * qi := by
        have := Nat.lt_mul_div_succ (a + H0') hqi_pos
        rw [mul_comm] at this; exact this
      omega
    have hm0_mem : m0 ∈ (Ioc H0' (H0' + qi)).filter (fun m : ℕ => qi ∣ a + m) := by
      rw [mem_filter, mem_Ioc]
      have hdiv := Nat.div_add_mod (a + H0') qi
      have hmod := Nat.mod_lt (a + H0') hqi_pos
      have hmul_eq : ((a + H0') / qi + 1) * qi = qi * ((a + H0') / qi) + qi := by ring
      have hgt : a + H0' < a + m0 := by omega
      have hle : a + m0 ≤ a + (H0' + qi) := by omega
      refine ⟨⟨by omega, by omega⟩, ⟨(a + H0') / qi + 1, by rw [hm0_mul, mul_comm]⟩⟩
    have hsing : (Ioc H0' (H0' + qi)).filter (fun m : ℕ => qi ∣ a + m) = {m0} := by
      ext m; rw [Finset.mem_singleton]
      constructor
      · intro hm
        rw [mem_filter, mem_Ioc] at hm
        obtain ⟨c, hc⟩ := hm.2
        have h1 : (a + H0') / qi < c := by
          by_contra hle; push Not at hle
          have : qi * c ≤ qi * ((a + H0') / qi) := Nat.mul_le_mul_left qi hle
          have := Nat.div_mul_le_self (a + H0') qi
          nlinarith
        have h2 : c ≤ (a + H0') / qi + 1 := by
          by_contra hgt; push Not at hgt
          have : qi * ((a + H0') / qi + 2) ≤ qi * c := Nat.mul_le_mul_left qi (by omega)
          have hlt := Nat.lt_mul_div_succ (a + H0') hqi_pos
          nlinarith
        have hc_eq : c = (a + H0') / qi + 1 := by omega
        rw [hc_eq, mul_comm] at hc
        omega
      · rintro rfl; exact hm0_mem
    rw [hsing, Finset.sum_singleton, hm0_mul, Nat.mul_div_cancel _ hqi_pos]
  dsimp only [qi] at hterm_eq
  simp_rw [hterm_eq]
  let M := q ^ (k - i - 1)
  have hM_mul : M * q * qi = q ^ k := by
    dsimp [M, qi]; rw [← pow_succ, ← pow_add]; congr 1; omega
  let g : ℕ × ℕ → ℕ := fun p =>
    let target := (q * p.1) * qi + p.2
    let s := (target + q ^ k * (H0' + 1) - H0') % q ^ k
    if s = 0 then q ^ k else s
  have hg_maps : ∀ p ∈ Finset.range M ×ˢ Finset.range qi, g p ∈ Icc 1 (q ^ k) := by
    intro p _
    dsimp [g]
    have hlt := Nat.mod_lt ((q * p.1) * qi + p.2 + q ^ k * (H0' + 1) - H0') (pow_pos hqpos k)
    rw [mem_Icc]
    split_ifs with h0
    · exact ⟨pow_pos hqpos k, le_rfl⟩
    · exact ⟨Nat.pos_of_ne_zero h0, hlt.le⟩
  have hg_mod : ∀ p ∈ Finset.range M ×ˢ Finset.range qi,
      (g p + H0') % q ^ k = (q * p.1) * qi + p.2 := by
    intro p hp
    rw [Finset.mem_product, mem_range, mem_range] at hp
    have htarget_lt : (q * p.1) * qi + p.2 < q ^ k := by
      have h1 : (q * p.1 + 1) * qi ≤ M * q * qi :=
        Nat.mul_le_mul_right qi (by nlinarith)
      nlinarith [hM_mul]
    have hz : ((g p + H0' : ℕ) : ZMod (q ^ k)) = (((q * p.1) * qi + p.2 : ℕ) : ZMod (q ^ k)) := by
      dsimp [g]
      have h1 : ((if ((q * p.1) * qi + p.2 + q ^ k * (H0' + 1) - H0') % q ^ k = 0 then q ^ k
          else ((q * p.1) * qi + p.2 + q ^ k * (H0' + 1) - H0') % q ^ k : ℕ) : ZMod (q ^ k)) =
          ((((q * p.1) * qi + p.2 + q ^ k * (H0' + 1) - H0') % q ^ k : ℕ) : ZMod (q ^ k)) := by
        split_ifs with h0
        · rw [h0, ZMod.natCast_self, Nat.cast_zero]
        · rfl
      rw [Nat.cast_add, h1, ZMod.natCast_mod]
      have hge : H0' ≤ (q * p.1) * qi + p.2 + q ^ k * (H0' + 1) := by
        have h1' : H0' ≤ q ^ k * (H0' + 1) := by
          calc H0' ≤ H0' + 1 := Nat.le_succ _
            _ = 1 * (H0' + 1) := (one_mul _).symm
            _ ≤ q ^ k * (H0' + 1) := Nat.mul_le_mul_right _ (pow_pos hqpos k)
        exact le_add_of_le_right h1'
      rw [Nat.cast_sub hge, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero, sub_add_cancel]
    have hval := congrArg ZMod.val hz
    simp only [ZMod.val_natCast] at hval
    rw [hval, Nat.mod_eq_of_lt htarget_lt]
  have hg_inj : Set.InjOn g ((Finset.range M ×ˢ Finset.range qi : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro p1 hp1 p2 hp2 heq
    have hm1 := hg_mod p1 (Finset.mem_coe.mp hp1)
    have hm2 := hg_mod p2 (Finset.mem_coe.mp hp2)
    rw [heq] at hm1
    have hteq : (q * p1.1) * qi + p1.2 = (q * p2.1) * qi + p2.2 := hm1.symm.trans hm2
    rw [Finset.mem_coe, Finset.mem_product, mem_range, mem_range] at hp1 hp2
    have hp2_eq : p1.2 = p2.2 := by
      have h1 := congrArg (· % qi) hteq
      rw [Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right,
        Nat.mod_eq_of_lt hp1.2, Nat.mod_eq_of_lt hp2.2] at h1
      exact h1
    have hp1_eq : p1.1 = p2.1 := by
      have h1 : (q * p1.1) * qi = (q * p2.1) * qi := by omega
      exact Nat.eq_of_mul_eq_mul_left hqpos (Nat.eq_of_mul_eq_mul_right hqi_pos h1)
    exact Prod.ext hp1_eq hp2_eq
  have hg_val : ∀ p ∈ Finset.range M ×ˢ Finset.range qi,
      ‖χ ((((g p + H0') / qi + 1 : ℕ) : ZMod q))‖ ^ 2 = 1 := by
    intro p hp
    have hm := hg_mod p hp
    rw [Finset.mem_product, mem_range, mem_range] at hp
    have hdiv_mod : ((g p + H0') / qi) % q = 0 := by
      have hdiv := Nat.div_add_mod (g p + H0') (q ^ k)
      have h1 : g p + H0' = q ^ k * ((g p + H0') / q ^ k) + ((q * p.1) * qi + p.2) := by
        rw [← hm]; exact hdiv.symm
      have h2 : g p + H0' = qi * (M * q * ((g p + H0') / q ^ k) + q * p.1) + p.2 := by
        have h3 : q ^ k * ((g p + H0') / q ^ k) = (M * q * qi) * ((g p + H0') / q ^ k) := by rw [hM_mul]
        linarith [h1, h3]
      rw [h2, Nat.mul_add_div hqi_pos, Nat.div_eq_of_lt hp.2, add_zero]
      have h3 : M * q * ((g p + H0') / q ^ k) + q * p.1 = q * (M * ((g p + H0') / q ^ k) + p.1) := by ring
      rw [h3, Nat.mul_mod_right]
    have hz1 : (((g p + H0') / qi + 1 : ℕ) : ZMod q) = 1 := by
      push_cast; rw [← ZMod.natCast_mod, hdiv_mod, Nat.cast_zero, zero_add]
    rw [hz1, map_one, norm_one, one_pow]
  have hcard_img : ((Finset.range M ×ˢ Finset.range qi).image g).card = M * qi := by
    rw [Finset.card_image_of_injOn hg_inj, Finset.card_product, Finset.card_range, Finset.card_range]
  have hMqi_eq : ((M * qi : ℕ) : ℝ) = ((q ^ k : ℕ) : ℝ) / (q : ℝ) := by
    have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
    rw [eq_div_iff hqR_pos.ne']
    exact_mod_cast (by rw [← hM_mul]; ring : M * qi * q = q ^ k)
  calc ((q ^ k : ℕ) : ℝ) / (2 * (q : ℝ))
      ≤ ((q ^ k : ℕ) : ℝ) / (q : ℝ) := by
        have : (q : ℝ) ≤ 2 * (q : ℝ) := by linarith [show (0 : ℝ) < (q : ℝ) by exact_mod_cast hqpos]
        exact div_le_div_of_nonneg_left hqk_pos.le (by exact_mod_cast hqpos) this
    _ = ((M * qi : ℕ) : ℝ) := hMqi_eq.symm
    _ = ∑ _a ∈ (Finset.range M ×ˢ Finset.range qi).image g, (1 : ℝ) := by simp [hcard_img]
    _ = ∑ a ∈ (Finset.range M ×ˢ Finset.range qi).image g,
          ‖χ ((((a + H0') / qi + 1 : ℕ) : ZMod q))‖ ^ 2 := by
        refine sum_congr rfl fun a ha => ?_
        rcases Finset.mem_image.mp ha with ⟨p, hp, rfl⟩
        exact (hg_val p hp).symm
    _ ≤ ∑ a ∈ Icc 1 (q ^ k), ‖χ ((((a + H0') / qi + 1 : ℕ) : ZMod q))‖ ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (fun a ha => by
          rcases Finset.mem_image.mp ha with ⟨p, hp, rfl⟩
          exact hg_maps p hp) (fun _ _ _ => sq_nonneg _)
theorem tildeChi_contra_of_L2_bound (q : ℕ) [NeZero q] (C_bd : ℝ) (hC : 1 ≤ C_bd) :
    ∃ H₀ : ℕ, 4 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H → ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ (tildeχ : ℕ →*₀ ℂ), (∀ n, 1 ≤ n → ‖tildeχ n‖ = 1) →
      (∀ p, p.Prime → ¬ p ∣ q → tildeχ p = χ (p : ZMod q)) →
      ¬ ((1 / ((q ^ k : ℕ) : ℝ)) *
          ∑ a ∈ goodClasses q k H,
            (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
              ‖∑ m ∈ Icc 1 H', tildeχ (a + m)‖ ^ 2 ≤ C_bd) := by
  have hqpos : 0 < q := NeZero.pos q
  by_cases hq1 : q = 1
  · subst hq1
    let H₀ := max 4 (⌈C_bd⌉₊ + 2)
    refine ⟨H₀, le_max_left _ _, fun H hH => ⟨2, le_rfl, fun k _ χ _ tildeχ _ htilde_cop hle => ?_⟩⟩
    have htilde1 : ∀ n, 1 ≤ n → tildeχ n = 1 := by
      intro n
      induction n using Nat.strongRecOn with
      | ind n ih =>
        intro hn1
        by_cases h1 : n = 1
        · subst h1; exact map_one tildeχ
        · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd h1
          obtain ⟨r, rfl⟩ := hpdvd
          have hr1 : 1 ≤ r := by
            by_contra h0; push Not at h0
            have : r = 0 := by omega
            subst this; simp at hn1
          have hp1 : ¬ p ∣ 1 := by intro h; have := Nat.le_of_dvd (by norm_num) h; have := hp.two_le; omega
          have hχ1 : χ (p : ZMod 1) = 1 := by
            have : (p : ZMod 1) = 1 := Subsingleton.elim _ _
            rw [this, map_one]
          rw [map_mul, htilde_cop p hp hp1, hχ1, one_mul, ih r (by have := hp.two_le; nlinarith) hr1]
    have hgood1 : goodClasses 1 k H = {1} := by
      ext a
      simp only [goodClasses, mem_filter, mem_Icc, one_pow, Finset.mem_singleton]
      constructor
      · intro h; omega
      · rintro rfl
        refine ⟨⟨le_rfl, le_rfl⟩, fun p hp hpdvd _ _ => ?_⟩
        have := Nat.le_of_dvd (by norm_num) hpdvd; have := hp.two_le; omega
    rw [hgood1, one_pow, Nat.cast_one, div_one, one_mul, Finset.sum_singleton] at hle
    have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
    have hlb : (H : ℝ) ^ 2 ≤ (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
        ‖∑ m ∈ Icc 1 H', tildeχ (1 + m)‖ ^ 2 := by
      have hterm : ∀ H' ∈ Ioc H (2 * H), (H : ℝ) ^ 2 ≤ ‖∑ m ∈ Icc 1 H', tildeχ (1 + m)‖ ^ 2 := by
        intro H' hH'
        rw [mem_Ioc] at hH'
        have hsum : ∑ m ∈ Icc 1 H', tildeχ (1 + m) = (H' : ℂ) := by
          have : ∑ m ∈ Icc 1 H', tildeχ (1 + m) = ∑ _m ∈ Icc 1 H', (1 : ℂ) :=
            sum_congr rfl fun m _ => htilde1 (1 + m) (by omega)
          rw [this, sum_const, Nat.card_Icc, show H' + 1 - 1 = H' by omega, nsmul_eq_mul, mul_one]
        rw [hsum, Complex.norm_natCast]
        have : (H : ℝ) ≤ (H' : ℝ) := by exact_mod_cast hH'.1.le
        nlinarith
      calc (H : ℝ) ^ 2 = (1 / (H : ℝ)) * ((H : ℝ) * (H : ℝ) ^ 2) := by field_simp [hHpos.ne']
        _ = (1 / (H : ℝ)) * ∑ _H' ∈ Ioc H (2 * H), (H : ℝ) ^ 2 := by
            rw [sum_const, Nat.card_Ioc, show 2 * H - H = H by omega, nsmul_eq_mul]
        _ ≤ (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H), ‖∑ m ∈ Icc 1 H', tildeχ (1 + m)‖ ^ 2 :=
            mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by positivity)
    have hH_ge : C_bd + 1 ≤ (H : ℝ) := by
      have h1 : ⌈C_bd⌉₊ + 2 ≤ H := le_trans (le_max_right _ _) hH
      have h2 : C_bd ≤ (⌈C_bd⌉₊ : ℝ) := Nat.le_ceil C_bd
      have h3 : ((⌈C_bd⌉₊ + 2 : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
      push_cast at h3; linarith
    nlinarith
  have hq2 : 2 ≤ q := by omega
  let L : ℕ := ⌈32 * (q : ℝ) * (C_bd + 1)⌉₊ + 4
  let H₀ : ℕ := max 4 (q ^ (2 * L) + 4)
  refine ⟨H₀, le_max_left _ _, fun H hH => ?_⟩
  let k₀ : ℕ := max (2 * L + 10) (Nat.clog 2 (64 * H ^ 3 * q + 10))
  refine ⟨k₀, by dsimp [k₀]; omega, fun k hk χ hprim tildeχ htilde_norm htilde_cop hle => ?_⟩
  have hk2 : 2 ≤ k := by dsimp [k₀] at hk; omega
  have hH4 : 4 ≤ H := le_trans (le_max_left _ _) hH
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hqk_pos : (0 : ℝ) < ((q ^ k : ℕ) : ℝ) := by exact_mod_cast pow_pos hqpos k
  have hgood_bound :
      ∑ a ∈ goodClasses q k H, (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
        ‖∑ m ∈ Icc 1 H', tildeχ (a + m)‖ ^ 2 ≤ C_bd * ((q ^ k : ℕ) : ℝ) := by
    rwa [one_div_mul_eq_div, div_le_iff₀ hqk_pos] at hle
  let Sd : ℕ → ℕ → ℕ → ℂ := fun d a H' =>
    ∑ m ∈ (Icc 1 H').filter (fun m : ℕ => d ∣ a + m), χ (((a + m) / d : ℕ) : ZMod q)
  let Sfull : ℕ → ℕ → ℂ := fun a H' =>
    ∑ d ∈ (q ^ (k - 1)).divisors, tildeχ d * Sd d a H'
  have hSfull_swap : ∀ a H', Sfull a H' = ∑ m ∈ Icc 1 H',
      ∑ d ∈ (q ^ (k - 1)).divisors,
        if d ∣ a + m then tildeχ d * χ (((a + m) / d : ℕ) : ZMod q) else 0 := by
    intro a H'
    dsimp [Sfull, Sd]
    have h1 : ∀ d ∈ (q ^ (k - 1)).divisors,
        tildeχ d * ∑ m ∈ (Icc 1 H').filter (fun m : ℕ => d ∣ a + m),
          χ (((a + m) / d : ℕ) : ZMod q) =
        ∑ m ∈ Icc 1 H', if d ∣ a + m then tildeχ d * χ (((a + m) / d : ℕ) : ZMod q) else 0 := by
      intro d _
      rw [mul_sum, sum_filter]
    rw [sum_congr rfl h1, sum_comm]
  have hSfull_other_zero : ∀ (a m d : ℕ), 1 ≤ m → d ∈ (q ^ (k - 1)).divisors →
      d ≠ Nat.gcd (a + m) (q ^ k) →
      (if d ∣ a + m then tildeχ d * χ (((a + m) / d : ℕ) : ZMod q) else 0) = 0 := by
    intro a m d hm1 hd hdne
    by_cases hdvd : d ∣ a + m
    · rw [if_pos hdvd]
      let d0 := Nat.gcd (a + m) (q ^ k)
      have hd_dvd_qk1 : d ∣ q ^ (k - 1) := (Nat.mem_divisors.mp hd).1
      have hd_dvd_qk : d ∣ q ^ k := hd_dvd_qk1.trans (pow_dvd_pow q (by omega))
      have hd_dvd_d0 : d ∣ d0 := Nat.dvd_gcd hdvd hd_dvd_qk
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd_qk (pow_pos hqpos _)
      have hd0_pos : 0 < d0 := Nat.gcd_pos_of_pos_left _ (by omega)
      have hlt : d < d0 := lt_of_le_of_ne (Nat.le_of_dvd hd0_pos hd_dvd_d0) hdne
      have hq_ne1 : d0 / d ≠ 1 := by
        have : d * (d0 / d) = d0 := Nat.mul_div_cancel' hd_dvd_d0
        intro h1; rw [h1, mul_one] at this; omega
      obtain ⟨p, hp, hp_div⟩ := Nat.exists_prime_and_dvd hq_ne1
      have hp_q : p ∣ q := hp.dvd_of_dvd_pow ((hp_div.trans (Nat.div_dvd_of_dvd hd_dvd_d0)).trans (Nat.gcd_dvd_right _ _))
      have hp_amd : p ∣ (a + m) / d := by
        obtain ⟨c, hc⟩ := Nat.gcd_dvd_left (a + m) (q ^ k)
        obtain ⟨e, he⟩ := hd_dvd_d0
        dsimp only [d0] at he
        have h1 : d0 / d ∣ (a + m) / d := ⟨c, by
          have h2 : a + m = d * (e * c) := by rw [hc, he]; ring
          have h3 : (a + m) / d = e * c := by rw [h2, Nat.mul_div_cancel_left _ hd_pos]
          have h4 : d0 / d = e := by dsimp [d0]; rw [he, Nat.mul_div_cancel_left _ hd_pos]
          rw [h3, h4]⟩
        exact hp_div.trans h1
      have hnonunit : ¬ IsUnit (((a + m) / d : ℕ) : ZMod q) := by
        rw [ZMod.isUnit_iff_coprime]
        intro hcop
        have := Nat.dvd_gcd hp_amd hp_q
        rw [hcop.gcd_eq_one] at this
        have := Nat.le_of_dvd (by norm_num) this; have := hp.two_le; omega
      rw [MulChar.map_nonunit _ hnonunit, mul_zero]
    · rw [if_neg hdvd]
  have hSfull_good : ∀ a ∈ goodClasses q k H, ∀ H' ∈ Ioc H (2 * H),
      Sfull a H' = ∑ m ∈ Icc 1 H', tildeχ (a + m) := by
    intro a ha H' hH'
    have hgood : isGoodRes q k H a := (mem_filter.mp ha).2
    rw [mem_Ioc] at hH'
    rw [hSfull_swap a H']
    refine sum_congr rfl fun m hm => ?_
    have hm1 := (mem_Icc.mp hm).1
    have hm2H : m ∈ Icc 1 (2 * H) := mem_Icc.mpr ⟨hm1, (mem_Icc.mp hm).2.trans hH'.2⟩
    obtain ⟨hd0_dvd, hfac⟩ := tildeChi_good_factor hk2 χ tildeχ htilde_cop hgood hm2H
    let d0 := Nat.gcd (a + m) (q ^ k)
    have hd0_mem : d0 ∈ (q ^ (k - 1)).divisors := Nat.mem_divisors.mpr ⟨hd0_dvd, (pow_pos hqpos _).ne'⟩
    rw [sum_eq_single d0 (fun d hd hdne => hSfull_other_zero a m d hm1 hd hdne) (fun h => (h hd0_mem).elim)]
    rw [if_pos (Nat.gcd_dvd_left _ _), ← hfac]
  have hSfull_triv : ∀ a H', H' ∈ Ioc H (2 * H) → ‖Sfull a H'‖ ≤ 2 * (H : ℝ) := by
    intro a H' hH'
    rw [mem_Ioc] at hH'
    rw [hSfull_swap a H']
    have hper_m : ∀ m ∈ Icc 1 H',
        ‖∑ d ∈ (q ^ (k - 1)).divisors,
          if d ∣ a + m then tildeχ d * χ (((a + m) / d : ℕ) : ZMod q) else 0‖ ≤ 1 := by
      intro m hm
      have hm1 := (mem_Icc.mp hm).1
      let d0 := Nat.gcd (a + m) (q ^ k)
      by_cases hd0_mem : d0 ∈ (q ^ (k - 1)).divisors
      · rw [sum_eq_single d0 (fun d hd hdne => hSfull_other_zero a m d hm1 hd hdne)
          (fun h => (h hd0_mem).elim), if_pos (Nat.gcd_dvd_left _ _),
          norm_mul, htilde_norm d0 (Nat.gcd_pos_of_pos_left _ (by omega)), one_mul]
        exact granville_norm_le_one χ _
      · have hzero : ∑ d ∈ (q ^ (k - 1)).divisors,
            (if d ∣ a + m then tildeχ d * χ (((a + m) / d : ℕ) : ZMod q) else 0) = 0 :=
          sum_eq_zero fun d hd => hSfull_other_zero a m d hm1 hd (fun heq => hd0_mem (by dsimp [d0]; rwa [← heq]))
        rw [hzero, norm_zero]; norm_num
    calc ‖∑ m ∈ Icc 1 H', ∑ d ∈ (q ^ (k - 1)).divisors,
            if d ∣ a + m then tildeχ d * χ (((a + m) / d : ℕ) : ZMod q) else 0‖
        ≤ ∑ m ∈ Icc 1 H', ‖∑ d ∈ (q ^ (k - 1)).divisors,
            if d ∣ a + m then tildeχ d * χ (((a + m) / d : ℕ) : ZMod q) else 0‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ Icc 1 H', (1 : ℝ) := sum_le_sum hper_m
      _ = (H' : ℝ) := by simp [Nat.card_Icc, show H' + 1 - 1 = H' by omega]
      _ ≤ 2 * (H : ℝ) := by exact_mod_cast hH'.2
  have hbad_card := granville_badSet_card_le (k := k) (H := H) hqpos
  have hfull_bound :
      (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
        ∑ a ∈ Icc 1 (q ^ k), ‖Sfull a H'‖ ^ 2 ≤ (C_bd + 1) * ((q ^ k : ℕ) : ℝ) := by
    have hsplit : ∑ a ∈ Icc 1 (q ^ k),
        (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H), ‖Sfull a H'‖ ^ 2 =
        (∑ a ∈ goodClasses q k H, (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H), ‖Sfull a H'‖ ^ 2) +
        (∑ a ∈ (Icc 1 (q ^ k)).filter (fun a : ℕ => ¬ isGoodRes q k H a),
          (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H), ‖Sfull a H'‖ ^ 2) :=
      (sum_filter_add_sum_filter_not (Icc 1 (q ^ k)) (fun a => isGoodRes q k H a) _).symm
    have hgood_eq : ∑ a ∈ goodClasses q k H,
        (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H), ‖Sfull a H'‖ ^ 2 ≤ C_bd * ((q ^ k : ℕ) : ℝ) := by
      have heq : ∑ a ∈ goodClasses q k H,
          (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H), ‖Sfull a H'‖ ^ 2 =
          ∑ a ∈ goodClasses q k H,
          (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H), ‖∑ m ∈ Icc 1 H', tildeχ (a + m)‖ ^ 2 :=
        sum_congr rfl fun a ha => congrArg ((1 / (H : ℝ)) * ·)
          (sum_congr rfl fun H' hH' => by rw [hSfull_good a ha H' hH'])
      rw [heq]; exact hgood_bound
    have hbad_bound : ∑ a ∈ (Icc 1 (q ^ k)).filter (fun a : ℕ => ¬ isGoodRes q k H a),
        (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H), ‖Sfull a H'‖ ^ 2 ≤ ((q ^ k : ℕ) : ℝ) := by
      have hterm : ∀ a ∈ (Icc 1 (q ^ k)).filter (fun a : ℕ => ¬ isGoodRes q k H a),
          (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H), ‖Sfull a H'‖ ^ 2 ≤ 4 * (H : ℝ) ^ 2 := by
        intro a _
        calc (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H), ‖Sfull a H'‖ ^ 2
            ≤ (1 / (H : ℝ)) * ∑ _H' ∈ Ioc H (2 * H), (4 * (H : ℝ) ^ 2) := by
              refine mul_le_mul_of_nonneg_left (sum_le_sum fun H' hH' => ?_) (by positivity)
              have h1 := hSfull_triv a H' hH'
              nlinarith [norm_nonneg (Sfull a H')]
          _ = (1 / (H : ℝ)) * ((H : ℝ) * (4 * (H : ℝ) ^ 2)) := by
              rw [sum_const, Nat.card_Ioc, show 2 * H - H = H by omega, nsmul_eq_mul]
          _ = 4 * (H : ℝ) ^ 2 := by field_simp [hHpos.ne']
      have h2k_ge : 8 * (H : ℝ) ^ 3 * (q : ℝ) ≤ (2 : ℝ) ^ k := by
        have hk_clog : Nat.clog 2 (64 * H ^ 3 * q + 10) ≤ k := le_trans (le_max_right _ _) hk
        have h1 : 64 * H ^ 3 * q + 10 ≤ 2 ^ k :=
          (Nat.le_pow_clog (by norm_num) _).trans (Nat.pow_le_pow_right (by norm_num) hk_clog)
        have h1R : (64 * (H : ℝ) ^ 3 * (q : ℝ) + 10) ≤ (2 : ℝ) ^ k := by exact_mod_cast h1
        have hnn : 0 ≤ (H : ℝ) ^ 3 * (q : ℝ) := by positivity
        linarith
      calc ∑ a ∈ (Icc 1 (q ^ k)).filter (fun a : ℕ => ¬ isGoodRes q k H a),
            (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H), ‖Sfull a H'‖ ^ 2
          ≤ (((Icc 1 (q ^ k)).filter (fun a : ℕ => ¬ isGoodRes q k H a)).card : ℝ) * (4 * (H : ℝ) ^ 2) := by
            calc _ ≤ ∑ _a ∈ (Icc 1 (q ^ k)).filter (fun a : ℕ => ¬ isGoodRes q k H a), (4 * (H : ℝ) ^ 2) :=
                  sum_le_sum hterm
              _ = _ := by simp
        _ ≤ ((2 * (H : ℝ) * (q : ℝ)) * (((q ^ k : ℕ) : ℝ) / ((2 : ℝ) ^ k))) * (4 * (H : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hbad_card (by positivity)
        _ = (8 * (H : ℝ) ^ 3 * (q : ℝ) / (2 : ℝ) ^ k) * ((q ^ k : ℕ) : ℝ) := by ring
        _ ≤ 1 * ((q ^ k : ℕ) : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ hqk_pos.le
            rw [div_le_one (by positivity)]
            exact h2k_ge
        _ = ((q ^ k : ℕ) : ℝ) := one_mul _
    have hcomm : (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H), ∑ a ∈ Icc 1 (q ^ k), ‖Sfull a H'‖ ^ 2 =
        ∑ a ∈ Icc 1 (q ^ k), (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H), ‖Sfull a H'‖ ^ 2 := by
      rw [sum_comm, mul_sum]
    rw [hcomm, hsplit]; linarith
  have hdiag_eq : ∀ H' : ℕ,
      ∑ a ∈ Icc 1 (q ^ k), ‖Sfull a H'‖ ^ 2 =
      ∑ d ∈ (q ^ (k - 1)).divisors, ∑ a ∈ Icc 1 (q ^ k), ‖Sd d a H'‖ ^ 2 :=
    fun H' => granville_Sfull_diag_eq hq2 hk2 χ hprim tildeχ htilde_norm
  have hqi_bound : ∀ i ∈ Finset.range L, q ^ i ≤ H / 2 := by
    intro i hi
    rw [mem_range] at hi
    have hH_big : q ^ (2 * L) + 4 ≤ H := le_trans (le_max_right _ _) hH
    have hpow_le : 2 * q ^ i ≤ q ^ (2 * L) := by
      have h1 : q ^ i * q ≤ q ^ (2 * L) := by
        rw [← pow_succ]; exact Nat.pow_le_pow_right hqpos (by omega)
      calc 2 * q ^ i = q ^ i * 2 := by ring
        _ ≤ q ^ i * q := Nat.mul_le_mul_left _ hq2
        _ ≤ q ^ (2 * L) := h1
    omega
  have hqi_dvd : ∀ i ∈ Finset.range L, q ^ i ∈ (q ^ (k - 1)).divisors := by
    intro i hi
    rw [mem_range] at hi
    exact Nat.mem_divisors.mpr ⟨pow_dvd_pow q (by dsimp [k₀] at hk; omega), (pow_pos hqpos _).ne'⟩
  have hsub_L : ∑ i ∈ Finset.range L,
      (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
        ∑ a ∈ Icc 1 (q ^ k), ‖Sd (q ^ i) a H'‖ ^ 2 ≤ (C_bd + 1) * ((q ^ k : ℕ) : ℝ) := by
    have h1 : ∀ H' ∈ Ioc H (2 * H),
        ∑ i ∈ Finset.range L, ∑ a ∈ Icc 1 (q ^ k), ‖Sd (q ^ i) a H'‖ ^ 2 ≤
          ∑ a ∈ Icc 1 (q ^ k), ‖Sfull a H'‖ ^ 2 := by
      intro H' _
      rw [hdiag_eq H']
      have himg : ∑ i ∈ Finset.range L, ∑ a ∈ Icc 1 (q ^ k), ‖Sd (q ^ i) a H'‖ ^ 2 =
          ∑ d ∈ (Finset.range L).image (fun i : ℕ => q ^ i), ∑ a ∈ Icc 1 (q ^ k), ‖Sd d a H'‖ ^ 2 := by
        symm; exact sum_image fun _ _ _ _ heq => Nat.pow_right_injective (by omega : 2 ≤ q) heq
      rw [himg]
      refine sum_le_sum_of_subset_of_nonneg (fun d hd => ?_)
        (fun _ _ _ => sum_nonneg fun _ _ => sq_nonneg _)
      rcases Finset.mem_image.mp hd with ⟨i, hi, rfl⟩
      exact hqi_dvd i hi
    calc ∑ i ∈ Finset.range L, (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
            ∑ a ∈ Icc 1 (q ^ k), ‖Sd (q ^ i) a H'‖ ^ 2
        = (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
            ∑ i ∈ Finset.range L, ∑ a ∈ Icc 1 (q ^ k), ‖Sd (q ^ i) a H'‖ ^ 2 := by
          rw [← mul_sum, sum_comm]
      _ ≤ (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
            ∑ a ∈ Icc 1 (q ^ k), ‖Sfull a H'‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (sum_le_sum h1) (by positivity)
      _ ≤ (C_bd + 1) * ((q ^ k : ℕ) : ℝ) := hfull_bound
  let Ihalf := Ioc H (H + H / 2)
  have hIhalf_card : (H / 2 : ℕ) = Ihalf.card := by dsimp [Ihalf]; rw [Nat.card_Ioc]; omega
  have hIhalf_pos : 1 ≤ Ihalf.card := by omega
  have hdiff_avg :
      ∑ H' ∈ Ihalf, ∑ i ∈ Finset.range L, ∑ a ∈ Icc 1 (q ^ k),
        ‖Sd (q ^ i) a (H' + q ^ i) - Sd (q ^ i) a H'‖ ^ 2 ≤
      4 * (H : ℝ) * (C_bd + 1) * ((q ^ k : ℕ) : ℝ) := by
    have hper_i : ∀ i ∈ Finset.range L,
        ∑ H' ∈ Ihalf, ∑ a ∈ Icc 1 (q ^ k),
          ‖Sd (q ^ i) a (H' + q ^ i) - Sd (q ^ i) a H'‖ ^ 2 ≤
        4 * ∑ H' ∈ Ioc H (2 * H), ∑ a ∈ Icc 1 (q ^ k), ‖Sd (q ^ i) a H'‖ ^ 2 := by
      intro i hi
      have hqi := hqi_bound i hi
      have h1 : ∑ H' ∈ Ihalf, ∑ a ∈ Icc 1 (q ^ k),
            ‖Sd (q ^ i) a (H' + q ^ i) - Sd (q ^ i) a H'‖ ^ 2 ≤
          2 * (∑ H' ∈ Ihalf, ∑ a ∈ Icc 1 (q ^ k), ‖Sd (q ^ i) a (H' + q ^ i)‖ ^ 2) +
          2 * (∑ H' ∈ Ihalf, ∑ a ∈ Icc 1 (q ^ k), ‖Sd (q ^ i) a H'‖ ^ 2) := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_le_sum fun H' _ => ?_
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_le_sum fun a _ => ?_
        have htri := norm_sub_le (Sd (q ^ i) a (H' + q ^ i)) (Sd (q ^ i) a H')
        nlinarith [sq_nonneg (‖Sd (q ^ i) a (H' + q ^ i)‖ - ‖Sd (q ^ i) a H'‖),
          norm_nonneg (Sd (q ^ i) a (H' + q ^ i) - Sd (q ^ i) a H')]
      have hsub1 : ∑ H' ∈ Ihalf, ∑ a ∈ Icc 1 (q ^ k), ‖Sd (q ^ i) a H'‖ ^ 2 ≤
          ∑ H' ∈ Ioc H (2 * H), ∑ a ∈ Icc 1 (q ^ k), ‖Sd (q ^ i) a H'‖ ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right (by omega))
          (fun _ _ _ => sum_nonneg fun _ _ => sq_nonneg _)
      have hsub2 : ∑ H' ∈ Ihalf, ∑ a ∈ Icc 1 (q ^ k), ‖Sd (q ^ i) a (H' + q ^ i)‖ ^ 2 ≤
          ∑ H' ∈ Ioc H (2 * H), ∑ a ∈ Icc 1 (q ^ k), ‖Sd (q ^ i) a H'‖ ^ 2 := by
        have himg : ∑ H' ∈ Ihalf, ∑ a ∈ Icc 1 (q ^ k), ‖Sd (q ^ i) a (H' + q ^ i)‖ ^ 2 =
            ∑ H'' ∈ Ihalf.image (fun H' => H' + q ^ i), ∑ a ∈ Icc 1 (q ^ k), ‖Sd (q ^ i) a H''‖ ^ 2 := by
          symm; exact sum_image (fun _ _ _ _ h => by omega)
        rw [himg]
        refine sum_le_sum_of_subset_of_nonneg (fun H'' hH'' => ?_)
          (fun _ _ _ => sum_nonneg fun _ _ => sq_nonneg _)
        rcases Finset.mem_image.mp hH'' with ⟨H', hH', rfl⟩
        rw [mem_Ioc] at hH' ⊢; omega
      linarith
    rw [sum_comm]
    calc ∑ i ∈ Finset.range L, ∑ H' ∈ Ihalf, ∑ a ∈ Icc 1 (q ^ k),
            ‖Sd (q ^ i) a (H' + q ^ i) - Sd (q ^ i) a H'‖ ^ 2
        ≤ ∑ i ∈ Finset.range L, 4 * ∑ H' ∈ Ioc H (2 * H),
            ∑ a ∈ Icc 1 (q ^ k), ‖Sd (q ^ i) a H'‖ ^ 2 := sum_le_sum hper_i
      _ = 4 * (H : ℝ) * ∑ i ∈ Finset.range L, (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
            ∑ a ∈ Icc 1 (q ^ k), ‖Sd (q ^ i) a H'‖ ^ 2 := by
          rw [mul_sum]
          refine sum_congr rfl fun _ _ => by field_simp [hHpos.ne']
      _ ≤ 4 * (H : ℝ) * ((C_bd + 1) * ((q ^ k : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hsub_L (by positivity)
      _ = 4 * (H : ℝ) * (C_bd + 1) * ((q ^ k : ℕ) : ℝ) := by ring
  have hex_H' : ∃ H0' ∈ Ihalf,
      ∑ i ∈ Finset.range L, ∑ a ∈ Icc 1 (q ^ k),
        ‖Sd (q ^ i) a (H0' + q ^ i) - Sd (q ^ i) a H0'‖ ^ 2 ≤
      16 * (C_bd + 1) * ((q ^ k : ℕ) : ℝ) := by
    by_contra hall; push Not at hall
    have hgt : (Ihalf.card : ℝ) * (16 * (C_bd + 1) * ((q ^ k : ℕ) : ℝ)) <
        ∑ H' ∈ Ihalf, ∑ i ∈ Finset.range L, ∑ a ∈ Icc 1 (q ^ k),
          ‖Sd (q ^ i) a (H' + q ^ i) - Sd (q ^ i) a H'‖ ^ 2 := by
      calc (Ihalf.card : ℝ) * (16 * (C_bd + 1) * ((q ^ k : ℕ) : ℝ))
          = ∑ _H' ∈ Ihalf, (16 * (C_bd + 1) * ((q ^ k : ℕ) : ℝ)) := by simp
        _ < _ := Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp (by omega)) hall
    have hcard_ge : (H : ℝ) / 4 ≤ (Ihalf.card : ℝ) := by
      have : H ≤ 4 * Ihalf.card := by omega
      have hR : (H : ℝ) ≤ 4 * (Ihalf.card : ℝ) := by exact_mod_cast this
      linarith
    have hnn : 0 ≤ 16 * (C_bd + 1) * ((q ^ k : ℕ) : ℝ) := by positivity
    have hcmp : 4 * (H : ℝ) * (C_bd + 1) * ((q ^ k : ℕ) : ℝ) ≤
        (Ihalf.card : ℝ) * (16 * (C_bd + 1) * ((q ^ k : ℕ) : ℝ)) := by nlinarith
    linarith
  obtain ⟨H0', _, hH0'_le⟩ := hex_H'
  have hsum_L : (L : ℝ) * (((q ^ k : ℕ) : ℝ) / (2 * (q : ℝ))) ≤ 16 * (C_bd + 1) * ((q ^ k : ℕ) : ℝ) := by
    calc (L : ℝ) * (((q ^ k : ℕ) : ℝ) / (2 * (q : ℝ)))
        = ∑ _i ∈ Finset.range L, (((q ^ k : ℕ) : ℝ) / (2 * (q : ℝ))) := by simp
      _ ≤ ∑ i ∈ Finset.range L, ∑ a ∈ Icc 1 (q ^ k),
            ‖Sd (q ^ i) a (H0' + q ^ i) - Sd (q ^ i) a H0'‖ ^ 2 := by
          refine sum_le_sum fun i hi => ?_
          rw [mem_range] at hi
          exact granville_single_i_lower (k := k) (i := i) (H0' := H0') hqpos
            (by dsimp [k₀] at hk; omega) χ
      _ ≤ 16 * (C_bd + 1) * ((q ^ k : ℕ) : ℝ) := hH0'_le
  have hL_le : (L : ℝ) ≤ 32 * (q : ℝ) * (C_bd + 1) := by
    have h1 : (L : ℝ) / (2 * (q : ℝ)) ≤ 16 * (C_bd + 1) := by
      have hmul : ((L : ℝ) / (2 * (q : ℝ))) * ((q ^ k : ℕ) : ℝ) ≤ (16 * (C_bd + 1)) * ((q ^ k : ℕ) : ℝ) := by
        linarith [show (L : ℝ) * (((q ^ k : ℕ) : ℝ) / (2 * (q : ℝ))) = ((L : ℝ) / (2 * (q : ℝ))) * ((q ^ k : ℕ) : ℝ) by ring]
      exact le_of_mul_le_mul_right hmul hqk_pos
    have h2q : (0 : ℝ) < 2 * (q : ℝ) := by positivity
    rw [div_le_iff₀ h2q] at h1
    linarith
  have hL_gt : 32 * (q : ℝ) * (C_bd + 1) < (L : ℝ) := by
    dsimp [L]; push_cast; linarith [Nat.le_ceil (32 * (q : ℝ) * (C_bd + 1))]
  linarith
end

section
open scoped BigOperators Topology
open Filter MeasureTheory
open Classical
abbrev Omega := ℕ → Metric.sphere (0 : ℂ) 1
noncomputable def mulEvalFn (z : Omega) (n : ℕ) : ℂ :=
  if n = 0 then 0 else n.factorization.prod fun p a => (z p).1 ^ a
lemma mulEvalFn_zero (z : Omega) : mulEvalFn z 0 = 0 := by simp [mulEvalFn]
lemma mulEvalFn_one (z : Omega) : mulEvalFn z 1 = 1 := by simp [mulEvalFn]
lemma mulEvalFn_mul (z : Omega) (m n : ℕ) :
    mulEvalFn z (m * n) = mulEvalFn z m * mulEvalFn z n := by
  by_cases hm : m = 0
  · subst hm; simp [mulEvalFn]
  by_cases hn : n = 0
  · subst hn; simp [mulEvalFn]
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  simp only [mulEvalFn, hm, hn, hmn, ↓reduceIte, Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
noncomputable def mulEvalHom (z : Omega) : ℕ →*₀ ℂ where
  toFun := mulEvalFn z
  map_zero' := mulEvalFn_zero z
  map_one' := mulEvalFn_one z
  map_mul' := mulEvalFn_mul z
lemma mulEvalFn_norm_eq_one (z : Omega) {n : ℕ} (hn : 1 ≤ n) :
    ‖mulEvalFn z n‖ = 1 := by
  have hn0 : n ≠ 0 := by omega
  simp only [mulEvalFn, hn0, ↓reduceIte, Finsupp.prod, norm_prod]
  refine prod_eq_one fun p _ => ?_
  rw [norm_pow]
  have hz1 : ‖(z p).1‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using (z p).2
  rw [hz1, one_pow]
lemma mulEvalFn_continuous (n : ℕ) : Continuous (fun z : Omega => mulEvalFn z n) := by
  by_cases hn0 : n = 0
  · subst hn0; simp only [mulEvalFn_zero]; exact continuous_const
  · simp only [mulEvalFn, hn0, ↓reduceIte, Finsupp.prod]
    exact continuous_finset_prod _ fun p _ =>
      (continuous_subtype_val.comp (continuous_apply p)).pow _
lemma sum_Icc_shift_eq (f : ℕ → ℂ) (n H' : ℕ) :
    ∑ m ∈ Icc 1 H', f (n + m) =
      (∑ k ∈ Icc 1 (n + H'), f k) - ∑ k ∈ Icc 1 n, f k := by
  have hsplit : Icc 1 (n + H') =
      Icc 1 n ∪ (Icc 1 H').map (addLeftEmbedding n) := by
    ext k
    simp only [mem_Icc, mem_union, Finset.mem_map, addLeftEmbedding_apply]
    constructor
    · intro ⟨hk1, hk2⟩
      by_cases hkn : k ≤ n
      · exact Or.inl ⟨hk1, hkn⟩
      · exact Or.inr ⟨k - n, ⟨by omega, by omega⟩, by omega⟩
    · rintro (⟨h1, h2⟩ | ⟨m, ⟨hm1, hm2⟩, rfl⟩) <;> omega
  have hdisj : Disjoint (Icc 1 n) ((Icc 1 H').map (addLeftEmbedding n)) := by
    rw [disjoint_left]
    intro k hk1 hk2
    simp only [mem_Icc, Finset.mem_map, addLeftEmbedding_apply] at hk1 hk2
    rcases hk2 with ⟨m, ⟨hm1, _⟩, rfl⟩; omega
  rw [hsplit, sum_union hdisj, sum_map]
  simp only [addLeftEmbedding_apply, add_sub_cancel_left]
lemma tsum_nat_rpow_neg_le {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hsum : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
      simpa [Real.rpow_neg (Nat.cast_nonneg _)] using (Real.summable_nat_rpow_inv.mpr hσ)
    exact h1.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => by split_ifs <;> [positivity; exact le_rfl])
  have hstep : ∀ k : ℕ, 2 ≤ k →
      (k : ℝ) ^ (-σ) ≤ (((k - 1 : ℕ) : ℝ) ^ (1 - σ) - (k : ℝ) ^ (1 - σ)) / (σ - 1) := by
    intro k hk
    have hk1_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < k - 1 by omega)
    have hk_eq : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast (show k = (k - 1) + 1 by omega)
    have hlt : ((k - 1 : ℕ) : ℝ) < (k : ℝ) := by linarith
    have hcont : ContinuousOn (fun x : ℝ => x ^ (1 - σ)) (Set.Icc ((k - 1 : ℕ) : ℝ) (k : ℝ)) :=
      fun x hx => (Real.continuousAt_rpow_const x (1 - σ) (Or.inl (lt_of_lt_of_le hk1_pos hx.1).ne')).continuousWithinAt
    have hdiff : ∀ x ∈ Set.Ioo ((k - 1 : ℕ) : ℝ) (k : ℝ),
        HasDerivAt (fun t : ℝ => t ^ (1 - σ)) ((1 - σ) * x ^ (-σ)) x := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hk1_pos hx.1.le
      have h := Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hxpos.ne')
      convert h using 1; ring
    obtain ⟨c, ⟨hc1, hc2⟩, hslope⟩ := exists_hasDerivAt_eq_slope (fun x : ℝ => x ^ (1 - σ))
      (fun x => (1 - σ) * x ^ (-σ)) hlt hcont hdiff
    have hden : (k : ℝ) - ((k - 1 : ℕ) : ℝ) = 1 := by linarith
    rw [hden, div_one] at hslope
    have hge : (k : ℝ) ^ (-σ) ≤ c ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hk1_pos hc1.le) hc2.le (by linarith)
    rw [le_div_iff₀ (by linarith : 0 < σ - 1)]
    nlinarith
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) ≤
      1 + 1 / (σ - 1) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp; positivity
    have hsplit : ∑ n ∈ Finset.range (N + 1), (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) =
        1 + ∑ k ∈ Icc 2 N, (k : ℝ) ^ (-σ) := by
      have h1 : Finset.range (N + 1) = insert 0 (insert 1 (Icc 2 N)) := by
        ext k; simp only [mem_range, mem_insert, mem_Icc]; omega
      rw [h1, sum_insert (by simp), sum_insert (by simp)]
      simp only [↓reduceIte, one_ne_zero, Nat.cast_one, Real.one_rpow, zero_add]
      congr 1
      refine sum_congr rfl fun k hk => ?_
      have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
      simp [hk0]
    rw [hsplit]
    have htele_sum : ∑ k ∈ Icc 2 N, (k : ℝ) ^ (-σ) ≤ 1 / (σ - 1) := by
      by_cases hN2 : N < 2
      · have hemp : Icc 2 N = ∅ := Icc_eq_empty (by omega)
        rw [hemp, sum_empty]; positivity
      push Not at hN2
      calc ∑ k ∈ Icc 2 N, (k : ℝ) ^ (-σ)
          ≤ ∑ k ∈ Icc 2 N, (((k - 1 : ℕ) : ℝ) ^ (1 - σ) - (k : ℝ) ^ (1 - σ)) / (σ - 1) :=
            sum_le_sum fun k hk => hstep k (mem_Icc.mp hk).1
        _ = (∑ k ∈ Icc 2 N, (((k - 1 : ℕ) : ℝ) ^ (1 - σ) - (k : ℝ) ^ (1 - σ))) / (σ - 1) := by
            rw [sum_div]
        _ = (1 - (N : ℝ) ^ (1 - σ)) / (σ - 1) := by
            congr 1
            have htel : ∀ M : ℕ, 2 ≤ M →
                ∑ k ∈ Icc 2 M, (((k - 1 : ℕ) : ℝ) ^ (1 - σ) - (k : ℝ) ^ (1 - σ)) =
                  1 - (M : ℝ) ^ (1 - σ) := by
              intro M hM
              induction M, hM using Nat.le_induction with
              | base => simp
              | succ m hm ih =>
                have hIcc : Icc 2 (m + 1) = insert (m + 1) (Icc 2 m) := by
                  ext j; simp only [mem_Icc, mem_insert]; omega
                rw [hIcc, sum_insert (by simp), ih]
                simp only [Nat.add_sub_cancel]; ring
            exact htel N hN2
        _ ≤ 1 / (σ - 1) := by
            apply div_le_div_of_nonneg_right _ (by linarith)
            linarith [Real.rpow_nonneg (Nat.cast_nonneg N) (1 - σ)]
    linarith
  have ht := hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  exact le_of_tendsto ht (Eventually.of_forall hpart)
lemma prob_extract_good_z
    (μ : MeasureTheory.ProbabilityMeasure Omega) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ n : ℕ, ∫ z, ‖∑ k ∈ Icc 1 n, mulEvalFn z k‖ ^ 2 ∂(μ : Measure Omega) ≤ B)
    (Q : ℝ) (hQ : 1 ≤ Q)
    (hpretQ : ∀ X : ℕ, Q ≤ (X : ℝ) →
      (μ : Measure Omega) {z : Omega |
        ¬ ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
            1 ≤ q ∧ (q : ℝ) ≤ Q ∧ |t| ≤ Q * (X : ℝ) ∧
            ∑ p ∈ (Icc 1 X).filter Nat.Prime,
              (1 - (mulEvalFn z p * star (χ (p : ZMod q)) *
                Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q} ≤
        ENNReal.ofReal (1 / 8))
    (H : ℕ) (hH : 4 ≤ H) (δ : ℝ) (hδ0 : 0 < δ)
    (X : ℕ) (hX100 : 100 ≤ X) (hQX : Q ≤ (X : ℝ)) (hQY : Q ≤ (⌊(X : ℝ) ^ δ⌋₊ : ℝ)) :
    let s₀ : ℝ := 1 + 1 / Real.log (X : ℝ)
    let N₀ : ℕ := max 1 ⌈(X : ℝ) ^ (2 * δ)⌉₊
    ∃ z₀ : Omega,
      (∀ H' ∈ Ioc H (2 * H),
        Summable (fun n : ℕ => if n < N₀ then (0 : ℝ) else
          ‖∑ m ∈ Icc 1 H', mulEvalFn z₀ (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀))) ∧
      ((1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
        ∑' n : ℕ, (if n < N₀ then (0 : ℝ) else
          ‖∑ m ∈ Icc 1 H', mulEvalFn z₀ (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀)) ≤
        16 * (B + 1) * Real.log (X : ℝ)) ∧
      (∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
        1 ≤ q ∧ (q : ℝ) ≤ Q ∧ |t| ≤ Q * (X : ℝ) ∧
        ∑ p ∈ (Icc 1 X).filter Nat.Prime,
          (1 - (mulEvalFn z₀ p * star (χ (p : ZMod q)) *
            Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q) ∧
      (∃ (q' : ℕ) (χ' : DirichletCharacter ℂ q') (t' : ℝ),
        1 ≤ q' ∧ (q' : ℝ) ≤ Q ∧ |t'| ≤ Q * (⌊(X : ℝ) ^ δ⌋₊ : ℝ) ∧
        ∑ p ∈ (Icc 1 ⌊(X : ℝ) ^ δ⌋₊).filter Nat.Prime,
          (1 - (mulEvalFn z₀ p * star (χ' (p : ZMod q')) *
            Complex.exp (-Complex.I * t' * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q) := by
  intro s₀ N₀
  have hlogX_gt1 : 1 < Real.log (X : ℝ) := by
    have hX100R : (100 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX100
    have h1 : Real.exp 1 < (X : ℝ) := by linarith [Real.exp_one_lt_d9]
    exact (Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < X by omega))).mpr h1
  have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
  have hs0 : 1 < s₀ := by simp only [s₀]; linarith [show 0 < 1 / Real.log (X : ℝ) by positivity]
  let ν : Measure Omega := (μ : Measure Omega)
  have hint_part : ∀ M : ℕ, Integrable (fun z : Omega => ‖∑ k ∈ Icc 1 M, mulEvalFn z k‖ ^ 2) ν := by
    intro M
    have hcont : Continuous (fun z : Omega => ‖∑ k ∈ Icc 1 M, mulEvalFn z k‖ ^ 2) :=
      ((continuous_finset_sum _ fun k _ => mulEvalFn_continuous k).norm).pow 2
    refine Integrable.mono' (integrable_const ((M : ℝ) ^ 2)) hcont.aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have htri : ‖∑ k ∈ Icc 1 M, mulEvalFn z k‖ ≤ (M : ℝ) := by
      calc ‖∑ k ∈ Icc 1 M, mulEvalFn z k‖
          ≤ ∑ k ∈ Icc 1 M, ‖mulEvalFn z k‖ := norm_sum_le _ _
        _ = ∑ _k ∈ Icc 1 M, (1 : ℝ) :=
            sum_congr rfl fun k hk => mulEvalFn_norm_eq_one z (mem_Icc.mp hk).1
        _ = (M : ℝ) := by simp
    exact pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hshift_int : ∀ n H' : ℕ,
      Integrable (fun z : Omega => ‖∑ m ∈ Icc 1 H', mulEvalFn z (n + m)‖ ^ 2) ν ∧
      ∫ z, ‖∑ m ∈ Icc 1 H', mulEvalFn z (n + m)‖ ^ 2 ∂ν ≤ 4 * B := by
    intro n H'
    have hcont : Continuous (fun z : Omega => ‖∑ m ∈ Icc 1 H', mulEvalFn z (n + m)‖ ^ 2) :=
      ((continuous_finset_sum _ fun m _ => mulEvalFn_continuous (n + m)).norm).pow 2
    have hint : Integrable (fun z : Omega => ‖∑ m ∈ Icc 1 H', mulEvalFn z (n + m)‖ ^ 2) ν := by
      refine Integrable.mono' (integrable_const ((H' : ℝ) ^ 2)) hcont.aestronglyMeasurable
        (Eventually.of_forall fun z => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have htri : ‖∑ m ∈ Icc 1 H', mulEvalFn z (n + m)‖ ≤ (H' : ℝ) := by
        calc ‖∑ m ∈ Icc 1 H', mulEvalFn z (n + m)‖
            ≤ ∑ m ∈ Icc 1 H', ‖mulEvalFn z (n + m)‖ := norm_sum_le _ _
          _ = ∑ _m ∈ Icc 1 H', (1 : ℝ) :=
              sum_congr rfl fun m hm => mulEvalFn_norm_eq_one z (by have := (mem_Icc.mp hm).1; omega)
          _ = (H' : ℝ) := by simp
      exact pow_le_pow_left₀ (norm_nonneg _) htri 2
    refine ⟨hint, ?_⟩
    have hpw : ∀ z : Omega,
        ‖∑ m ∈ Icc 1 H', mulEvalFn z (n + m)‖ ^ 2 ≤
          2 * ‖∑ k ∈ Icc 1 (n + H'), mulEvalFn z k‖ ^ 2 +
          2 * ‖∑ k ∈ Icc 1 n, mulEvalFn z k‖ ^ 2 := by
      intro z
      rw [sum_Icc_shift_eq]
      have htri := norm_sub_le (∑ k ∈ Icc 1 (n + H'), mulEvalFn z k)
        (∑ k ∈ Icc 1 n, mulEvalFn z k)
      nlinarith [sq_nonneg (‖∑ k ∈ Icc 1 (n + H'), mulEvalFn z k‖ -
        ‖∑ k ∈ Icc 1 n, mulEvalFn z k‖),
        norm_nonneg (∑ k ∈ Icc 1 (n + H'), mulEvalFn z k -
          ∑ k ∈ Icc 1 n, mulEvalFn z k)]
    have hint_rhs : Integrable (fun z : Omega =>
        2 * ‖∑ k ∈ Icc 1 (n + H'), mulEvalFn z k‖ ^ 2 +
        2 * ‖∑ k ∈ Icc 1 n, mulEvalFn z k‖ ^ 2) ν :=
      ((hint_part (n + H')).const_mul 2).add ((hint_part n).const_mul 2)
    calc ∫ z, ‖∑ m ∈ Icc 1 H', mulEvalFn z (n + m)‖ ^ 2 ∂ν
        ≤ ∫ z, (2 * ‖∑ k ∈ Icc 1 (n + H'), mulEvalFn z k‖ ^ 2 +
            2 * ‖∑ k ∈ Icc 1 n, mulEvalFn z k‖ ^ 2) ∂ν :=
          integral_mono hint hint_rhs hpw
      _ = 2 * (∫ z, ‖∑ k ∈ Icc 1 (n + H'), mulEvalFn z k‖ ^ 2 ∂ν) +
          2 * (∫ z, ‖∑ k ∈ Icc 1 n, mulEvalFn z k‖ ^ 2 ∂ν) := by
          rw [integral_add ((hint_part _).const_mul 2) ((hint_part _).const_mul 2),
            integral_const_mul, integral_const_mul]
      _ ≤ 2 * B + 2 * B := by linarith [hB (n + H'), hB n]
      _ = 4 * B := by ring
  let aFn : ℕ → Omega → ℝ := fun n z =>
    if n < N₀ then 0 else
      ((1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
        ‖∑ m ∈ Icc 1 H', mulEvalFn z (n + m)‖ ^ 2) * (n : ℝ) ^ (-s₀)
  let F_enn : Omega → ENNReal := fun z => ∑' n : ℕ, ENNReal.ofReal (aFn n z)
  have ha_nn : ∀ n z, 0 ≤ aFn n z := by
    intro n z; simp only [aFn]; split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg (by positivity) (sum_nonneg fun _ _ => sq_nonneg _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have ha_cont : ∀ n, Continuous (aFn n) := by
    intro n; simp only [aFn]; split_ifs
    · exact continuous_const
    · exact ((continuous_const.mul (continuous_finset_sum _ fun H' _ =>
        ((continuous_finset_sum _ fun m _ => mulEvalFn_continuous (n + m)).norm).pow 2))).mul continuous_const
  have ha_int : ∀ n, Integrable (aFn n) ν := by
    intro n; simp only [aFn]; split_ifs
    · exact integrable_zero _ _ _
    · exact ((integrable_finset_sum _ fun H' _ => (hshift_int n H').1).const_mul _).mul_const _
  have hF_meas : AEMeasurable F_enn ν :=
    AEMeasurable.ennreal_tsum fun n => (ENNReal.continuous_ofReal.comp (ha_cont n)).aemeasurable
  have hF_lint : ∫⁻ z, F_enn z ∂ν ≤ ENNReal.ofReal (8 * (B + 1) * Real.log (X : ℝ)) := by
    have hton : ∫⁻ z, F_enn z ∂ν = ∑' n : ℕ, ∫⁻ z, ENNReal.ofReal (aFn n z) ∂ν :=
      lintegral_tsum fun n => (ENNReal.continuous_ofReal.comp (ha_cont n)).aemeasurable
    rw [hton]
    have hterm_le : ∀ n : ℕ, ∫⁻ z, ENNReal.ofReal (aFn n z) ∂ν ≤
        ENNReal.ofReal (if n = 0 then 0 else (4 * B) * (n : ℝ) ^ (-s₀)) := by
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal (ha_int n) (Eventually.of_forall (ha_nn n))]
      apply ENNReal.ofReal_le_ofReal
      by_cases hlt : n < N₀
      · simp only [aFn, hlt, ↓reduceIte, integral_zero]
        split_ifs <;> positivity
      · have hn0 : n ≠ 0 := by have : 1 ≤ N₀ := le_max_left _ _; omega
        simp only [aFn, hlt, hn0, ↓reduceIte]
        rw [integral_mul_const, integral_const_mul,
          integral_finset_sum _ fun H' _ => (hshift_int n H').1]
        have havg : (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
            ∫ z, ‖∑ m ∈ Icc 1 H', mulEvalFn z (n + m)‖ ^ 2 ∂ν ≤ 4 * B := by
          calc (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
                ∫ z, ‖∑ m ∈ Icc 1 H', mulEvalFn z (n + m)‖ ^ 2 ∂ν
              ≤ (1 / (H : ℝ)) * ∑ _H' ∈ Ioc H (2 * H), (4 * B) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact sum_le_sum fun H' _ => (hshift_int n H').2
            _ = (1 / (H : ℝ)) * ((H : ℝ) * (4 * B)) := by
                rw [sum_const, Nat.card_Ioc, show 2 * H - H = H by omega, nsmul_eq_mul]
            _ = 4 * B := by
                have hHpos : (H : ℝ) ≠ 0 := by exact_mod_cast (show H ≠ 0 by omega)
                field_simp [hHpos]
        exact mul_le_mul_of_nonneg_right havg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hsum_rhs : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else (4 * B) * (n : ℝ) ^ (-s₀)) := by
      have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-s₀)) := by
        simpa [Real.rpow_neg (Nat.cast_nonneg _)] using (Real.summable_nat_rpow_inv.mpr hs0)
      exact (h1.mul_left (4 * B)).of_nonneg_of_le (fun n => by split_ifs <;> positivity)
        (fun n => by split_ifs <;> [positivity; exact le_rfl])
    calc ∑' n : ℕ, ∫⁻ z, ENNReal.ofReal (aFn n z) ∂ν
        ≤ ∑' n : ℕ, ENNReal.ofReal (if n = 0 then (0 : ℝ) else (4 * B) * (n : ℝ) ^ (-s₀)) :=
          ENNReal.tsum_le_tsum hterm_le
      _ = ENNReal.ofReal (∑' n : ℕ, if n = 0 then (0 : ℝ) else (4 * B) * (n : ℝ) ^ (-s₀)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun n => by split_ifs <;> positivity) hsum_rhs).symm
      _ ≤ ENNReal.ofReal (8 * (B + 1) * Real.log (X : ℝ)) := by
          apply ENNReal.ofReal_le_ofReal
          have hfac : (∑' n : ℕ, if n = 0 then (0 : ℝ) else (4 * B) * (n : ℝ) ^ (-s₀)) =
              (4 * B) * ∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-s₀) := by
            rw [← tsum_mul_left]; congr 1; ext n; split_ifs <;> ring
          rw [hfac]
          have hzeta := tsum_nat_rpow_neg_le hs0
          have hs0_sub : 1 / (s₀ - 1) = Real.log (X : ℝ) := by
            simp only [s₀, add_sub_cancel_left, one_div_one_div]
          rw [hs0_sub] at hzeta
          nlinarith
  let T_thr : ENNReal := ENNReal.ofReal (16 * (B + 1) * Real.log (X : ℝ))
  let BadF : Set Omega := {z : Omega | T_thr ≤ F_enn z}
  let BadX : Set Omega := {z : Omega |
    ¬ ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
        1 ≤ q ∧ (q : ℝ) ≤ Q ∧ |t| ≤ Q * (X : ℝ) ∧
        ∑ p ∈ (Icc 1 X).filter Nat.Prime,
          (1 - (mulEvalFn z p * star (χ (p : ZMod q)) *
            Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q}
  let BadY : Set Omega := {z : Omega |
    ¬ ∃ (q' : ℕ) (χ' : DirichletCharacter ℂ q') (t' : ℝ),
        1 ≤ q' ∧ (q' : ℝ) ≤ Q ∧ |t'| ≤ Q * (⌊(X : ℝ) ^ δ⌋₊ : ℝ) ∧
        ∑ p ∈ (Icc 1 ⌊(X : ℝ) ^ δ⌋₊).filter Nat.Prime,
          (1 - (mulEvalFn z p * star (χ' (p : ZMod q')) *
            Complex.exp (-Complex.I * t' * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q}
  have hBadF : ν BadF ≤ ENNReal.ofReal (1 / 2) := by
    have hmark := mul_meas_ge_le_lintegral₀ hF_meas T_thr
    have hTpos : (0 : ℝ) < 16 * (B + 1) * Real.log (X : ℝ) := by positivity
    have hT_ne0 : T_thr ≠ 0 := by simp [T_thr, hTpos]
    have hT_neTop : T_thr ≠ ⊤ := ENNReal.ofReal_ne_top
    have hhalf : ENNReal.ofReal (8 * (B + 1) * Real.log (X : ℝ)) =
        T_thr * ENNReal.ofReal (1 / 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
    have hle : T_thr * ν BadF ≤ T_thr * ENNReal.ofReal (1 / 2) := by
      calc T_thr * ν BadF ≤ ∫⁻ z, F_enn z ∂ν := hmark
        _ ≤ ENNReal.ofReal (8 * (B + 1) * Real.log (X : ℝ)) := hF_lint
        _ = T_thr * ENNReal.ofReal (1 / 2) := hhalf
    exact (ENNReal.mul_le_mul_iff_right hT_ne0 hT_neTop).mp hle
  have hBadX : ν BadX ≤ ENNReal.ofReal (1 / 8) := hpretQ X hQX
  have hBadY : ν BadY ≤ ENNReal.ofReal (1 / 8) := hpretQ ⌊(X : ℝ) ^ δ⌋₊ hQY
  have hunion : ν (BadF ∪ BadX ∪ BadY) < 1 := by
    have h1 : ν (BadF ∪ BadX ∪ BadY) ≤ ν BadF + ν BadX + ν BadY :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    have h2 : ν BadF + ν BadX + ν BadY ≤ ENNReal.ofReal (3 / 4) := by
      calc ν BadF + ν BadX + ν BadY
          ≤ ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) :=
            add_le_add (add_le_add hBadF hBadX) hBadY
        _ = ENNReal.ofReal (3 / 4) := by
            rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
              ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
            congr 1; norm_num
    have h3 : ENNReal.ofReal (3 / 4) < ENNReal.ofReal 1 :=
      ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr (by norm_num)
    rw [ENNReal.ofReal_one] at h3
    exact lt_of_le_of_lt (h1.trans h2) h3
  have hex : ∃ z₀ : Omega, z₀ ∉ BadF ∪ BadX ∪ BadY := by
    by_contra hall
    push Not at hall
    have huniv : BadF ∪ BadX ∪ BadY = Set.univ := Set.eq_univ_iff_forall.mpr hall
    rw [huniv, measure_univ] at hunion
    exact lt_irrefl 1 hunion
  rcases hex with ⟨z₀, hz₀⟩
  have hnotF : F_enn z₀ < T_thr := lt_of_not_ge (fun h => hz₀ (Or.inl (Or.inl h)))
  have hnotX : z₀ ∉ BadX := fun h => hz₀ (Or.inl (Or.inr h))
  have hnotY : z₀ ∉ BadY := fun h => hz₀ (Or.inr h)
  simp only [BadX, BadY, Set.mem_setOf_eq, not_not] at hnotX hnotY
  have ha_summable : Summable (fun n : ℕ => aFn n z₀) := by
    have hneTop : F_enn z₀ ≠ ⊤ := ne_top_of_lt hnotF
    exact (ENNReal.ofReal_tsum_of_nonneg (fun n => ha_nn n z₀)
      |> fun _ => ENNReal.summable_toReal hneTop).congr fun n =>
        ENNReal.toReal_ofReal (ha_nn n z₀)
  have ha_tsum_le : ∑' n : ℕ, aFn n z₀ ≤ 16 * (B + 1) * Real.log (X : ℝ) := by
    have heq : ENNReal.ofReal (∑' n : ℕ, aFn n z₀) = F_enn z₀ :=
      ENNReal.ofReal_tsum_of_nonneg (fun n => ha_nn n z₀) ha_summable
    have hle_enn : ENNReal.ofReal (∑' n : ℕ, aFn n z₀) ≤ T_thr := heq ▸ hnotF.le
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle_enn
  have hH'_sum : ∀ H' ∈ Ioc H (2 * H),
      Summable (fun n : ℕ => if n < N₀ then (0 : ℝ) else
        ‖∑ m ∈ Icc 1 H', mulEvalFn z₀ (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀)) := by
    intro H' hH'
    refine (ha_summable.mul_left (H : ℝ)).of_nonneg_of_le
      (fun n => by split_ifs <;> positivity) (fun n => ?_)
    simp only [aFn]
    split_ifs
    · simp
    · have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
      have hle_sum : ‖∑ m ∈ Icc 1 H', mulEvalFn z₀ (n + m)‖ ^ 2 ≤
          ∑ j ∈ Ioc H (2 * H), ‖∑ m ∈ Icc 1 j, mulEvalFn z₀ (n + m)‖ ^ 2 :=
        single_le_sum (f := fun j => ‖∑ m ∈ Icc 1 j, mulEvalFn z₀ (n + m)‖ ^ 2)
          (fun _ _ => sq_nonneg _) hH'
      have heq : (H : ℝ) * (((1 / (H : ℝ)) * ∑ j ∈ Ioc H (2 * H),
          ‖∑ m ∈ Icc 1 j, mulEvalFn z₀ (n + m)‖ ^ 2) * (n : ℝ) ^ (-s₀)) =
          (∑ j ∈ Ioc H (2 * H), ‖∑ m ∈ Icc 1 j, mulEvalFn z₀ (n + m)‖ ^ 2) *
            (n : ℝ) ^ (-s₀) := by field_simp [hHpos.ne']
      rw [heq]
      exact mul_le_mul_of_nonneg_right hle_sum (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨z₀, hH'_sum, ?_, hnotX, hnotY⟩
  have hswap : (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
      ∑' n : ℕ, (if n < N₀ then (0 : ℝ) else
        ‖∑ m ∈ Icc 1 H', mulEvalFn z₀ (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀)) =
      ∑' n : ℕ, aFn n z₀ := by
    rw [← Summable.tsum_finsetSum hH'_sum, ← tsum_mul_left]
    congr 1; ext n
    simp only [aFn]
    split_ifs
    · simp
    · rw [← sum_mul, mul_assoc]
  rw [hswap]
  exact ha_tsum_le
noncomputable def buildCMul (v : ℕ → ℂ) : ℕ →*₀ ℂ where
  toFun n := if n = 0 then 0 else n.factorization.prod fun p a => (v p) ^ a
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · subst hm; simp
    by_cases hn : n = 0
    · subst hn; simp
    have hmn : m * n ≠ 0 := mul_ne_zero hm hn
    simp only [hm, hn, hmn, ↓reduceIte, Nat.factorization_mul hm hn]
    exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
lemma buildCMul_prime (v : ℕ → ℂ) {p : ℕ} (hp : p.Prime) : buildCMul v p = v p := by
  simp only [buildCMul, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, hp.ne_zero, ↓reduceIte,
    hp.factorization]
  rw [Finsupp.prod_single_index (h := fun q a => (v q) ^ a) (pow_zero _), pow_one]
lemma buildCMul_norm_eq_one (v : ℕ → ℂ) (hv : ∀ p, p.Prime → ‖v p‖ = 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖buildCMul v n‖ = 1 := by
  have hn0 : n ≠ 0 := by omega
  simp only [buildCMul, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, hn0, ↓reduceIte,
    Finsupp.prod, norm_prod]
  refine prod_eq_one fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa [Nat.support_factorization] using hp)
  rw [norm_pow, hv p hpp, one_pow]
lemma cmul_eq_of_prime_eq {f₁ f₂ : ℕ →*₀ ℂ}
    (hprime : ∀ p : ℕ, p.Prime → f₁ p = f₂ p) {n : ℕ} (hn : 1 ≤ n) :
    f₁ n = f₂ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h1 : n = 1
    · subst h1; simp [map_one]
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd h1
      rcases hpdvd with ⟨m, rfl⟩
      have hm1 : 1 ≤ m := by
        by_contra hm0; have : m = 0 := by omega
        subst this; simp at hn
      have hmlt : m < p * m := lt_mul_of_one_lt_left (by omega) hp.one_lt
      rw [map_mul, map_mul, hprime p hp, ih m hmlt hm1]
lemma primitive_factorize
    (g : ℕ →*₀ ℂ) (hg : ∀ n, 1 ≤ n → ‖g n‖ = 1)
    (q : ℕ) (hq1 : 1 ≤ q) (χ : DirichletCharacter ℂ q) (t Q : ℝ) (X : ℕ)
    (hqQ : (q : ℝ) ≤ Q)
    (hdist : ∑ p ∈ (Icc 1 X).filter Nat.Prime,
      (1 - (g p * star (χ (p : ZMod q)) *
        Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q) :
    ∃ (q₀ : ℕ) (_ : NeZero q₀) (χ₀ : DirichletCharacter ℂ q₀) (tildeχ h : ℕ →*₀ ℂ),
      1 ≤ q₀ ∧ q₀ ∣ q ∧ (q₀ : ℝ) ≤ Q ∧ χ₀.IsPrimitive ∧
      (∀ n, 1 ≤ n → ‖tildeχ n‖ = 1) ∧
      (∀ p, p.Prime → ¬ p ∣ q₀ → tildeχ p = χ₀ (p : ZMod q₀)) ∧
      (∀ n, 1 ≤ n → ‖h n‖ = 1) ∧
      (∀ p, p.Prime → p ∣ q₀ → h p = 1) ∧
      (∀ n, 1 ≤ n → g n = tildeχ n * Complex.exp (Complex.I * t * Real.log (n : ℝ)) * h n) ∧
      ∑ p ∈ (Icc 1 X).filter Nat.Prime, (1 - (h p).re) / (p : ℝ) ≤ 2 * Q := by
  haveI : NeZero q := ⟨by omega⟩
  let q₀ : ℕ := χ.conductor
  have hq0_dvd : q₀ ∣ q := χ.conductor_dvd_level
  have hq0_pos : 0 < q₀ := Nat.pos_of_dvd_of_pos hq0_dvd (by omega)
  haveI hne0 : NeZero q₀ := ⟨hq0_pos.ne'⟩
  have hq0_le : q₀ ≤ q := Nat.le_of_dvd (by omega) hq0_dvd
  let χ₀ : DirichletCharacter ℂ q₀ := χ.primitiveCharacter
  have hprim : χ₀.IsPrimitive := χ.primitiveCharacter_isPrimitive
  let tv : ℕ → ℂ := fun p =>
    if ¬ p ∣ q₀ then χ₀ (p : ZMod q₀)
    else g p * Complex.exp (-Complex.I * t * Real.log (p : ℝ))
  let hv : ℕ → ℂ := fun p =>
    if ¬ p ∣ q₀ then g p * star (χ₀ (p : ZMod q₀)) * Complex.exp (-Complex.I * t * Real.log (p : ℝ))
    else 1
  let tildeχ : ℕ →*₀ ℂ := buildCMul tv
  let h : ℕ →*₀ ℂ := buildCMul hv
  have hchi0_norm : ∀ p : ℕ, p.Prime → ¬ p ∣ q₀ → ‖χ₀ (p : ZMod q₀)‖ = 1 := by
    intro p hp hnd
    have hcop : Nat.Coprime p q₀ := (hp.coprime_iff_not_dvd).mpr hnd
    exact dirichlet_norm_eq_one_of_isUnit χ₀ ((ZMod.isUnit_iff_coprime p q₀).mpr hcop)
  have hexp_norm : ∀ x : ℝ, ‖Complex.exp (Complex.I * x)‖ = 1 := by
    intro x
    simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I x
  have hexp_neg_norm : ∀ x : ℝ, ‖Complex.exp (-Complex.I * x)‖ = 1 := by
    intro x
    have : -Complex.I * (x : ℂ) = ((-x : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this]; exact Complex.norm_exp_ofReal_mul_I (-x)
  have htv_norm : ∀ p, p.Prime → ‖tv p‖ = 1 := by
    intro p hp; by_cases hpd : p ∣ q₀
    · simp only [tv, hpd, not_true_eq_false, ↓reduceIte]
      rw [norm_mul, hg p hp.one_le, one_mul]
      have : -Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ) = -Complex.I * ((t * Real.log (p : ℝ) : ℝ) : ℂ) := by
        push_cast; ring
      rw [this]; exact hexp_neg_norm _
    · simp only [tv, hpd, not_false_eq_true, ↓reduceIte]
      exact hchi0_norm p hp hpd
  have hhv_norm : ∀ p, p.Prime → ‖hv p‖ = 1 := by
    intro p hp; by_cases hpd : p ∣ q₀
    · simp only [hv, hpd, not_true_eq_false, ↓reduceIte]; exact norm_one
    · simp only [hv, hpd, not_false_eq_true, ↓reduceIte]
      rw [norm_mul, norm_mul, hg p hp.one_le, norm_star, hchi0_norm p hp hpd, one_mul, one_mul]
      have : -Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ) = -Complex.I * ((t * Real.log (p : ℝ) : ℝ) : ℂ) := by
        push_cast; ring
      rw [this]; exact hexp_neg_norm _
  have hfactor : ∀ n, 1 ≤ n → g n = tildeχ n * Complex.exp (Complex.I * t * Real.log (n : ℝ)) * h n := by
    let eHom : ℕ →*₀ ℂ := {
      toFun := fun n => if n = 0 then 0 else Complex.exp (Complex.I * t * Real.log (n : ℝ))
      map_zero' := by simp
      map_one' := by simp
      map_mul' := fun m n => by
        by_cases hm : m = 0
        · subst hm; simp
        by_cases hn : n = 0
        · subst hn; simp
        have hmn : m * n ≠ 0 := mul_ne_zero hm hn
        simp only [hm, hn, hmn, ↓reduceIte, Nat.cast_mul]
        rw [Real.log_mul (by exact_mod_cast hm) (by exact_mod_cast hn)]
        push_cast; rw [← Complex.exp_add]; congr 1; ring }
    let rhsHom : ℕ →*₀ ℂ := {
      toFun := fun n => tildeχ n * eHom n * h n
      map_zero' := by simp
      map_one' := by simp
      map_mul' := fun m n => by simp only [map_mul]; ring }
    have hprime_eq : ∀ p : ℕ, p.Prime → g p = rhsHom p := by
      intro p hp
      change g p = tildeχ p * (if p = 0 then 0 else Complex.exp (Complex.I * ↑t * ↑(Real.log ↑p))) * h p
      rw [if_neg hp.ne_zero, buildCMul_prime tv hp, buildCMul_prime hv hp]
      by_cases hpd : p ∣ q₀
      · simp only [tv, hv, hpd, not_true_eq_false, ↓reduceIte]
        have hexp1 : Complex.exp (-Complex.I * ↑t * ↑(Real.log ↑p)) *
            Complex.exp (Complex.I * ↑t * ↑(Real.log ↑p)) = 1 := by
          rw [← Complex.exp_add]; convert Complex.exp_zero; ring
        calc g p = g p * (Complex.exp (-Complex.I * ↑t * ↑(Real.log ↑p)) *
              Complex.exp (Complex.I * ↑t * ↑(Real.log ↑p))) * 1 := by rw [hexp1]; ring
          _ = g p * Complex.exp (-Complex.I * ↑t * ↑(Real.log ↑p)) *
              Complex.exp (Complex.I * ↑t * ↑(Real.log ↑p)) * 1 := by ring
      · simp only [tv, hv, hpd, not_false_eq_true, ↓reduceIte]
        have hunit : χ₀ (p : ZMod q₀) * star (χ₀ (p : ZMod q₀)) = 1 := by
          rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hchi0_norm p hp hpd]; norm_num
        have hexp1 : Complex.exp (Complex.I * ↑t * ↑(Real.log ↑p)) *
            Complex.exp (-Complex.I * ↑t * ↑(Real.log ↑p)) = 1 := by
          rw [← Complex.exp_add]; convert Complex.exp_zero; ring
        calc g p = g p * (χ₀ (p : ZMod q₀) * star (χ₀ (p : ZMod q₀))) *
              (Complex.exp (Complex.I * ↑t * ↑(Real.log ↑p)) *
                Complex.exp (-Complex.I * ↑t * ↑(Real.log ↑p))) := by rw [hunit, hexp1]; ring
          _ = χ₀ (p : ZMod q₀) * Complex.exp (Complex.I * ↑t * ↑(Real.log ↑p)) *
              (g p * star (χ₀ (p : ZMod q₀)) * Complex.exp (-Complex.I * ↑t * ↑(Real.log ↑p))) := by ring
    intro n hn
    have heq := cmul_eq_of_prime_eq hprime_eq hn
    have hn0 : n ≠ 0 := by omega
    simpa [rhsHom, eHom, hn0] using heq
  have hh_dist : ∑ p ∈ (Icc 1 X).filter Nat.Prime, (1 - (h p).re) / (p : ℝ) ≤ 2 * Q := by
    have hdiff_le : ∑ p ∈ (Icc 1 X).filter Nat.Prime, (1 - (h p).re) / (p : ℝ) -
        ∑ p ∈ (Icc 1 X).filter Nat.Prime,
          (1 - (g p * star (χ (p : ZMod q)) *
            Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ (q : ℝ) := by
      rw [← sum_sub_distrib]
      calc ∑ p ∈ (Icc 1 X).filter Nat.Prime,
            ((1 - (h p).re) / (p : ℝ) -
              (1 - (g p * star (χ (p : ZMod q)) *
                Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ))
          ≤ ∑ p ∈ (Icc 1 X).filter Nat.Prime, (if p ∣ q then (1 : ℝ) else 0) := by
            refine sum_le_sum fun p hp => ?_
            have hpp : p.Prime := (mem_filter.mp hp).2
            rw [buildCMul_prime hv hpp]
            by_cases hpdq : p ∣ q
            · rw [if_pos hpdq]
              have hre1 : -1 ≤ (hv p).re := by
                have := neg_le_of_abs_le (Complex.abs_re_le_norm (hv p))
                rw [hhv_norm p hpp] at this; linarith
              have hchi_zero : χ (p : ZMod q) = 0 := by
                apply MulChar.map_nonunit
                rw [ZMod.isUnit_iff_coprime]
                exact fun hcop => hpp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hpdq)
              simp only [hchi_zero, star_zero, mul_zero, zero_mul, Complex.zero_re, sub_zero]
              have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
              have h1 : (1 - (hv p).re) / (p : ℝ) - 1 / (p : ℝ) = -(hv p).re / (p : ℝ) := by ring
              rw [h1]
              exact (div_le_one (by linarith)).mpr (by linarith)
            · rw [if_neg hpdq]
              have hnd0 : ¬ p ∣ q₀ := fun h => hpdq (h.trans hq0_dvd)
              have hchi_eq : χ (p : ZMod q) = χ₀ (p : ZMod q₀) := by
                have hcopZ : IsCoprime (p : ℤ) (q : ℤ) :=
                  Nat.isCoprime_iff_coprime.mpr ((hpp.coprime_iff_not_dvd).mpr hpdq)
                have hcl := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hq0_dvd hcopZ
                rw [χ.changeLevel_primitiveCharacter] at hcl
                simpa using hcl
              simp only [hv, hnd0, not_false_eq_true, ↓reduceIte, hchi_eq, sub_self, le_refl]
        _ ≤ ∑ _p ∈ Icc 1 q, (1 : ℝ) := by
            have hsub : ((Icc 1 X).filter Nat.Prime).filter (fun p => p ∣ q) ⊆ Icc 1 q := by
              intro p hp
              have hpp : p.Prime := (mem_filter.mp (mem_filter.mp hp).1).2
              have hpd : p ∣ q := (mem_filter.mp hp).2
              exact mem_Icc.mpr ⟨hpp.one_le, Nat.le_of_dvd (by omega) hpd⟩
            rw [← sum_filter]
            exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => zero_le_one
        _ = (q : ℝ) := by simp
    linarith
  exact ⟨q₀, hne0, χ₀, tildeχ, h, hq0_pos, hq0_dvd, le_trans (by exact_mod_cast hq0_le) hqQ,
    hprim, fun n hn => buildCMul_norm_eq_one tv htv_norm hn,
    fun p hp hnd => by rw [buildCMul_prime tv hp]; simp [tv, hnd],
    fun n hn => buildCMul_norm_eq_one hv hhv_norm hn,
    fun p hp hdvd => by rw [buildCMul_prime hv hp]; simp [hv, hdvd],
    hfactor, hh_dist⟩
lemma nonprincipal_dirichletL_le {r : ℕ} [NeZero r] (ψ : DirichletCharacter ℂ r) (hψ : ψ ≠ 1)
    {σ : ℝ} (hσ : 1 < σ) :
    ‖∑' n : ℕ, if n = 0 then (0 : ℂ) else ψ (n : ZMod r) * Complex.ofReal ((n : ℝ) ^ (-σ))‖ ≤ (r : ℝ) := by
  have hrpos : 0 < r := NeZero.pos r
  have hsum_zmod : ∑ x : ZMod r, ψ x = 0 := by
    have hex : ∃ u : (ZMod r)ˣ, ψ (u : ZMod r) ≠ 1 := by
      by_contra hall; push Not at hall
      apply hψ; ext u
      rw [hall u, MulChar.one_apply u.isUnit]
    rcases hex with ⟨u, hu⟩
    let mulU : ZMod r ≃ ZMod r :=
      ⟨fun x => (u : ZMod r) * x, fun x => ((u⁻¹ : (ZMod r)ˣ) : ZMod r) * x,
       fun x => by simp [← mul_assoc], fun x => by simp [← mul_assoc]⟩
    have hmul : ψ (u : ZMod r) * ∑ x : ZMod r, ψ x = ∑ x : ZMod r, ψ x := by
      rw [mul_sum]
      calc ∑ x : ZMod r, ψ (u : ZMod r) * ψ x
          = ∑ x : ZMod r, ψ ((u : ZMod r) * x) := sum_congr rfl fun x _ => (map_mul ψ _ _).symm
        _ = ∑ x : ZMod r, ψ x := Fintype.sum_equiv mulU _ _ fun _ => rfl
    have hzero : (ψ (u : ZMod r) - 1) * ∑ x : ZMod r, ψ x = 0 := by linear_combination hmul
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hu)
  have hsum_block : ∀ a : ℕ, ∑ m ∈ Icc 1 r, ψ ((a + m : ℕ) : ZMod r) = 0 := by
    intro a
    let e : Fin r ≃ ZMod r := ZMod.finEquiv r
    have hbij : ∑ m ∈ Icc 1 r, ψ ((a + m : ℕ) : ZMod r) = ∑ x : ZMod r, ψ ((a : ZMod r) + x) := by
      calc ∑ m ∈ Icc 1 r, ψ ((a + m : ℕ) : ZMod r)
          = ∑ m ∈ Finset.range r, ψ ((a : ZMod r) + ((m + 1 : ℕ) : ZMod r)) := by
            refine sum_nbij (fun m => m - 1) ?_ ?_ ?_ ?_
            · intro m hm; simp only [mem_Icc] at hm; simp only [mem_range]; omega
            · intro m₁ hm₁ m₂ hm₂ h; simp only [Finset.mem_coe, mem_Icc] at hm₁ hm₂; dsimp at h; omega
            · intro m hm; simp only [Finset.mem_coe, mem_range] at hm
              exact ⟨m + 1, Finset.mem_coe.mpr (mem_Icc.mpr ⟨by omega, by omega⟩), rfl⟩
            · intro m hm; simp only [mem_Icc] at hm
              have : m - 1 + 1 = m := by omega
              rw [this, Nat.cast_add]
        _ = ∑ i : Fin r, ψ ((a : ZMod r) + ((i.1 + 1 : ℕ) : ZMod r)) :=
            (Fin.sum_univ_eq_sum_range _ r).symm
        _ = ∑ x : ZMod r, ψ ((a : ZMod r) + (x + 1)) := by
            let eFin : Fin r ≃ ZMod r :=
              ⟨fun i => (i.1 : ZMod r), fun x => ⟨x.val, x.val_lt⟩,
               fun i => Fin.ext (ZMod.val_natCast_of_lt i.2),
               fun x => ZMod.natCast_zmod_val x⟩
            refine Fintype.sum_equiv eFin _ _ fun i => ?_
            simp only [Nat.cast_add, Nat.cast_one, eFin, Equiv.coe_fn_mk]
        _ = ∑ x : ZMod r, ψ ((a : ZMod r) + x) :=
            Fintype.sum_equiv (Equiv.addRight (1 : ZMod r)) _ _ fun _ => rfl
    rw [hbij]
    have hshift : ∑ x : ZMod r, ψ ((a : ZMod r) + x) = ∑ x : ZMod r, ψ x :=
      Fintype.sum_equiv (Equiv.addLeft (a : ZMod r)) _ _ fun _ => rfl
    rw [hshift, hsum_zmod]
  have hpart_bd : ∀ M : ℕ, ‖∑ n ∈ Icc 1 M, ψ (n : ZMod r)‖ ≤ (r : ℝ) := by
    intro M
    have hdiv : ∀ q' t : ℕ, t < r →
        ∑ n ∈ Icc 1 (q' * r + t), ψ (n : ZMod r) =
          ∑ m ∈ Icc 1 t, ψ ((q' * r + m : ℕ) : ZMod r) := by
      intro q' t _
      induction q' with
      | zero => simp
      | succ k ih =>
        have hsplit : Icc 1 ((k + 1) * r + t) =
            Icc 1 (k * r + t) ∪ (Icc 1 r).map (addLeftEmbedding (k * r + t)) := by
          ext j; simp only [mem_Icc, mem_union, Finset.mem_map, addLeftEmbedding_apply]
          constructor
          · intro ⟨hj1, hj2⟩
            by_cases hle : j ≤ k * r + t
            · exact Or.inl ⟨hj1, hle⟩
            · exact Or.inr ⟨j - (k * r + t), ⟨by omega, Nat.sub_le_iff_le_add.mpr (by nlinarith)⟩, by omega⟩
          · rintro (⟨h1, h2⟩ | ⟨m, ⟨hm1, hm2⟩, rfl⟩)
            · exact ⟨h1, by nlinarith⟩
            · exact ⟨by omega, by nlinarith⟩
        have hdisj : Disjoint (Icc 1 (k * r + t)) ((Icc 1 r).map (addLeftEmbedding (k * r + t))) := by
          rw [disjoint_left]; intro j hj1 hj2
          simp only [mem_Icc, Finset.mem_map, addLeftEmbedding_apply] at hj1 hj2
          rcases hj2 with ⟨m, ⟨hm1, _⟩, rfl⟩; omega
        rw [hsplit, sum_union hdisj, sum_map, ih]
        simp only [addLeftEmbedding_apply]
        rw [hsum_block (k * r + t), add_zero]
        refine sum_congr rfl fun m _ => ?_
        congr 1; push_cast; simp [ZMod.natCast_self]
    have hM := hdiv (M / r) (M % r) (Nat.mod_lt M hrpos)
    have hMeq : M / r * r + M % r = M := by linarith [Nat.div_add_mod M r]
    rw [hMeq] at hM
    rw [hM]
    calc ‖∑ m ∈ Icc 1 (M % r), ψ ((M / r * r + m : ℕ) : ZMod r)‖
        ≤ ∑ m ∈ Icc 1 (M % r), ‖ψ ((M / r * r + m : ℕ) : ZMod r)‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ Icc 1 (M % r), (1 : ℝ) := sum_le_sum fun _ _ => dirichlet_norm_le_one ψ _
      _ = ((M % r : ℕ) : ℝ) := by simp
      _ ≤ (r : ℝ) := by exact_mod_cast (Nat.mod_lt M hrpos).le
  have habel : ∀ N : ℕ, 1 ≤ N →
      ‖∑ n ∈ Icc 1 N, ψ (n : ZMod r) * Complex.ofReal ((n : ℝ) ^ (-σ))‖ ≤ (r : ℝ) := by
    intro N hN
    have h1 := abel_sum_decreasing_weight hN (Nat.cast_nonneg r)
      (c := fun n => ψ (n : ZMod r)) (w := fun n => (n : ℝ) ^ (-σ))
      (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun n hn _ => Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn) (by exact_mod_cast Nat.le_succ n) (by linarith))
      (fun k _ _ => hpart_bd k)
    simpa using h1
  have hsum : Summable (fun n : ℕ => if n = 0 then (0 : ℂ) else ψ (n : ZMod r) * Complex.ofReal ((n : ℝ) ^ (-σ))) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
      simpa [Real.rpow_neg (Nat.cast_nonneg _)] using (Real.summable_nat_rpow_inv.mpr hσ)
    refine Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) ^ (-σ)) h1 fun n => ?_
    split_ifs with hn
    · simp; positivity
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (dirichlet_norm_le_one ψ _)
  have ht := (hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).norm
  refine le_of_tendsto ht (eventually_atTop.mpr ⟨1, fun N hN => ?_⟩)
  have heq : ∑ n ∈ Finset.range (N + 1), (if n = 0 then (0 : ℂ) else ψ (n : ZMod r) * Complex.ofReal ((n : ℝ) ^ (-σ))) =
      ∑ n ∈ Icc 1 N, ψ (n : ZMod r) * Complex.ofReal ((n : ℝ) ^ (-σ)) := by
    have h1 : Finset.range (N + 1) = insert 0 (Icc 1 N) := by
      ext k; simp only [mem_range, mem_insert, mem_Icc]; omega
    rw [h1, sum_insert (by simp)]
    simp only [↓reduceIte, zero_add]
    refine sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
    simp [hk0]
  dsimp only [Function.comp_apply]
  rw [heq]
  exact habel N hN
lemma totient_mul_eq_mul_totient_of_prime_dvd :
    ∀ (d M : ℕ), 1 ≤ d → (∀ p : ℕ, p.Prime → p ∣ d → p ∣ M) → (d * M).totient = d * M.totient := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro M hd hfac
    by_cases h1 : d = 1
    · subst h1; simp
    · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
      rcases hpd with ⟨d', rfl⟩
      have hd'1 : 1 ≤ d' := Nat.pos_of_ne_zero (by rintro rfl; simp at hd)
      have hd'lt : d' < p * d' := lt_mul_of_one_lt_left (by omega) hp.one_lt
      have hpM : p ∣ M := hfac p hp (dvd_mul_right p d')
      have hp_d'M : p ∣ d' * M := dvd_mul_of_dvd_right hpM d'
      rw [mul_assoc, Nat.totient_mul_of_prime_of_dvd hp hp_d'M,
        ih d' hd'lt M hd'1 (fun q hq hqd' => hfac q hq (dvd_mul_of_dvd_right hqd' p)), mul_assoc]
lemma L0_norm_bounds {q₀ : ℕ} [NeZero q₀] {Q : ℝ} (hQ : 1 ≤ Q) (hq0Q : (q₀ : ℝ) ≤ Q)
    {X : ℕ} (hX100 : 100 ≤ X)
    {h : ℕ →*₀ ℂ} (hh_norm : ∀ n, 1 ≤ n → ‖h n‖ = 1)
    (hh_dist : ∑ p ∈ (Icc 1 X).filter Nat.Prime, (1 - (h p).re) / (p : ℝ) ≤ 2 * Q) :
    let s₀ : ℝ := 1 + 1 / Real.log (X : ℝ)
    let f₀ : ℕ →*₀ ℂ := {
      toFun := fun n => if n = 0 then 0 else if Nat.Coprime n q₀ then h n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0
      map_zero' := by simp
      map_one' := by simp
      map_mul' := fun m n => by
        by_cases hm : m = 0
        · subst hm; simp
        by_cases hn : n = 0
        · subst hn; simp
        have hmn : m * n ≠ 0 := mul_ne_zero hm hn
        simp only [hm, hn, hmn, ↓reduceIte, Nat.coprime_mul_iff_left]
        by_cases hcm : Nat.Coprime m q₀ <;> by_cases hcn : Nat.Coprime n q₀
        · rw [if_pos ⟨hcm, hcn⟩, if_pos hcm, if_pos hcn, map_mul, Nat.cast_mul,
            Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n), Complex.ofReal_mul]
          ring
        · rw [if_neg (fun h => hcn h.2), if_pos hcm, if_neg hcn, mul_zero]
        · rw [if_neg (fun h => hcm h.1), if_neg hcm, zero_mul]
        · rw [if_neg (fun h => hcm h.1), if_neg hcm, zero_mul] }
    Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ) ≤ ‖∑' n : ℕ, f₀ n‖ ∧
    ‖∑' n : ℕ, f₀ n‖ ≤ 2 * Real.log (X : ℝ) := by
  intro s₀ f₀
  have hlogX_gt1 : 1 < Real.log (X : ℝ) := by
    have hX100R : (100 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX100
    have h1 : Real.exp 1 < (X : ℝ) := by linarith [Real.exp_one_lt_d9]
    exact (Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < X by omega))).mpr h1
  have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
  have hs0 : 1 < s₀ := by simp only [s₀]; linarith [show 0 < 1 / Real.log (X : ℝ) by positivity]
  have hf0_bd : ∀ n : ℕ, 1 ≤ n → ‖f₀ n‖ ≤ (n : ℝ) ^ (-s₀) := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    simp only [f₀, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, hn0, ↓reduceIte]
    split_ifs
    · rw [norm_mul, hh_norm n hn, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    · simp; positivity
  constructor
  · have heul := (euler_norm_bounds hs0 hf0_bd).1
    have hsp := tsum_primes_rpow_ge hs0
    have hs0_sub : 1 / (s₀ - 1) = Real.log (X : ℝ) := by
      simp only [s₀, add_sub_cancel_left, one_div_one_div]
    rw [hs0_sub] at hsp
    have hsum_pr : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-s₀)) := summable_primes_rpow hs0
    have hsum_re : Summable (fun p : Nat.Primes => (f₀ p).re) := by
      refine Summable.of_norm_bounded (g := fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-s₀)) hsum_pr fun p => ?_
      exact (Complex.abs_re_le_norm (f₀ p)).trans (hf0_bd p p.prop.one_le)
    have hdiff_le : (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-s₀)) - ∑' p : Nat.Primes, (f₀ p).re ≤
        3 * Q + 40 := by
      rw [← hsum_pr.tsum_sub hsum_re]
      have hterm_le : ∀ p : Nat.Primes,
          ((p : ℕ) : ℝ) ^ (-s₀) - (f₀ p).re ≤
            (if (p : ℕ) ≤ X then (1 - (h p).re) / ((p : ℕ) : ℝ) +
              (if (p : ℕ) ∣ q₀ then (1 : ℝ) else 0) else 0) +
            (if X < (p : ℕ) then 2 * ((p : ℕ) : ℝ) ^ (-s₀) else 0) := by
        intro p
        have hpp : (p : ℕ).Prime := p.prop
        have hp_pos : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast hpp.pos
        have hrpow_le : ((p : ℕ) : ℝ) ^ (-s₀) ≤ 1 / ((p : ℕ) : ℝ) := by
          rw [one_div, ← Real.rpow_neg_one]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpp.one_le) (by linarith)
        have hre_bd : |(f₀ p).re| ≤ ((p : ℕ) : ℝ) ^ (-s₀) :=
          (Complex.abs_re_le_norm _).trans (hf0_bd p hpp.one_le)
        by_cases hleX : (p : ℕ) ≤ X
        · have hnotlt : ¬ X < (p : ℕ) := Nat.not_lt.mpr hleX
          simp only [f₀, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, hpp.ne_zero, ↓reduceIte, hleX, hnotlt, add_zero]
          by_cases hcop : Nat.Coprime (p : ℕ) q₀
          · have hnd : ¬ (p : ℕ) ∣ q₀ := (hpp.coprime_iff_not_dvd).mp hcop
            rw [if_pos hcop, if_neg hnd, add_zero]
            have hre_eq : (h p * Complex.ofReal (((p : ℕ) : ℝ) ^ (-s₀))).re = (h p).re * ((p : ℕ) : ℝ) ^ (-s₀) := by
              rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
            rw [hre_eq]
            have h1_sub_nn : 0 ≤ 1 - (h p).re := by
              have := (Complex.abs_re_le_norm (h p)).trans_eq (hh_norm p hpp.one_le)
              linarith [(abs_le.mp this).2]
            calc ((p : ℕ) : ℝ) ^ (-s₀) - (h p).re * ((p : ℕ) : ℝ) ^ (-s₀)
                = (1 - (h p).re) * ((p : ℕ) : ℝ) ^ (-s₀) := by ring
              _ ≤ (1 - (h p).re) * (1 / ((p : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hrpow_le h1_sub_nn
              _ = (1 - (h p).re) / ((p : ℕ) : ℝ) := by ring
          · have hdvd : (p : ℕ) ∣ q₀ := by
              by_contra hnd; exact hcop ((hpp.coprime_iff_not_dvd).mpr hnd)
            rw [if_neg hcop, if_pos hdvd, Complex.zero_re, sub_zero]
            have h1_sub_nn : 0 ≤ (1 - (h p).re) / ((p : ℕ) : ℝ) := by
              apply div_nonneg _ hp_pos.le
              have := (Complex.abs_re_le_norm (h p)).trans_eq (hh_norm p hpp.one_le)
              linarith [(abs_le.mp this).2]
            have hrpow1 : ((p : ℕ) : ℝ) ^ (-s₀) ≤ 1 :=
              hrpow_le.trans ((div_le_one hp_pos).mpr (by exact_mod_cast hpp.one_le))
            linarith
        · have hltX : X < (p : ℕ) := Nat.lt_of_not_ge hleX
          simp only [hleX, hltX, ↓reduceIte, zero_add]
          linarith [(abs_le.mp hre_bd).1]
      have hsum_fin1 : Summable (fun p : Nat.Primes =>
          if (p : ℕ) ≤ X then (1 - (h p).re) / ((p : ℕ) : ℝ) +
            (if (p : ℕ) ∣ q₀ then (1 : ℝ) else 0) else 0) := by
        apply summable_of_ne_finset_zero (s := ((Icc 1 X).filter Nat.Prime).attach.map
          ⟨fun p => ⟨p.1, (mem_filter.mp p.2).2⟩, fun _ _ h => Subtype.ext (by injection h)⟩)
        intro p hp
        by_contra hne
        have hleX : (p : ℕ) ≤ X := by by_contra hgt; simp [hgt] at hne
        apply hp
        simp only [Finset.mem_map, mem_attach, true_and, Function.Embedding.coeFn_mk]
        exact ⟨⟨p.1, mem_filter.mpr ⟨mem_Icc.mpr ⟨p.prop.one_le, hleX⟩, p.prop⟩⟩, rfl⟩
      have hsum_tail2 : Summable (fun p : Nat.Primes =>
          if X < (p : ℕ) then 2 * ((p : ℕ) : ℝ) ^ (-s₀) else 0) :=
        (hsum_pr.mul_left 2).of_nonneg_of_le (fun _ => by split_ifs <;> positivity)
          (fun _ => by split_ifs <;> [exact le_rfl; positivity])
      calc ∑' p : Nat.Primes, (((p : ℕ) : ℝ) ^ (-s₀) - (f₀ p).re)
          ≤ ∑' p : Nat.Primes,
              ((if (p : ℕ) ≤ X then (1 - (h p).re) / ((p : ℕ) : ℝ) +
                (if (p : ℕ) ∣ q₀ then (1 : ℝ) else 0) else 0) +
              (if X < (p : ℕ) then 2 * ((p : ℕ) : ℝ) ^ (-s₀) else 0)) :=
            Summable.tsum_le_tsum hterm_le (hsum_pr.sub hsum_re) (hsum_fin1.add hsum_tail2)
        _ = (∑' p : Nat.Primes, if (p : ℕ) ≤ X then (1 - (h p).re) / ((p : ℕ) : ℝ) +
              (if (p : ℕ) ∣ q₀ then (1 : ℝ) else 0) else 0) +
            (∑' p : Nat.Primes, if X < (p : ℕ) then 2 * ((p : ℕ) : ℝ) ^ (-s₀) else 0) :=
            hsum_fin1.tsum_add hsum_tail2
        _ ≤ (2 * Q + Q) + 40 := by
            have h1 : (∑' p : Nat.Primes, if (p : ℕ) ≤ X then (1 - (h p).re) / ((p : ℕ) : ℝ) +
                (if (p : ℕ) ∣ q₀ then (1 : ℝ) else 0) else 0) ≤ 2 * Q + Q := by
              let S : Finset Nat.Primes := ((Icc 1 X).filter Nat.Prime).attach.map
                ⟨fun p => ⟨p.1, (mem_filter.mp p.2).2⟩, fun _ _ h => Subtype.ext (by injection h)⟩
              rw [tsum_eq_sum (s := S) (fun p hp => by
                by_cases hleX : (p : ℕ) ≤ X
                · exfalso; apply hp
                  simp only [S, Finset.mem_map, mem_attach, true_and, Function.Embedding.coeFn_mk]
                  exact ⟨⟨p.1, mem_filter.mpr ⟨mem_Icc.mpr ⟨p.prop.one_le, hleX⟩, p.prop⟩⟩, rfl⟩
                · simp [hleX])]
              have hsimp : ∑ p ∈ S,
                  (if (p : ℕ) ≤ X then (1 - (h p).re) / ((p : ℕ) : ℝ) +
                    (if (p : ℕ) ∣ q₀ then (1 : ℝ) else 0) else 0) =
                  ∑ p ∈ (Icc 1 X).filter Nat.Prime,
                    ((1 - (h p).re) / (p : ℝ) + (if p ∣ q₀ then (1 : ℝ) else 0)) := by
                refine sum_nbij (fun p => (p : ℕ)) ?_ ?_ ?_ ?_
                · intro p hp
                  simp only [S, Finset.mem_map, mem_attach, true_and] at hp
                  rcases hp with ⟨q, hq⟩; rw [← hq]; exact q.2
                · intro p₁ _ p₂ _ h; exact Subtype.ext h
                · intro p hp
                  refine ⟨⟨p, (mem_filter.mp hp).2⟩, ?_, rfl⟩
                  exact Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨⟨p, hp⟩, mem_attach _ _, rfl⟩)
                · intro p hp
                  simp only [S, Finset.mem_map, mem_attach, true_and] at hp
                  rcases hp with ⟨q, hq⟩
                  have hleX : (p : ℕ) ≤ X := by
                    rw [← hq]; exact (mem_Icc.mp (mem_filter.mp q.2).1).2
                  simp [hleX]
              rw [hsimp, sum_add_distrib]
              have hq0_sum : ∑ p ∈ (Icc 1 X).filter Nat.Prime, (if p ∣ q₀ then (1 : ℝ) else 0) ≤ Q := by
                rw [← sum_filter]
                have hsub : ((Icc 1 X).filter Nat.Prime).filter (fun p => p ∣ q₀) ⊆ Icc 1 q₀ := by
                  intro p hp
                  have hpp : p.Prime := (mem_filter.mp (mem_filter.mp hp).1).2
                  have hpd : p ∣ q₀ := (mem_filter.mp hp).2
                  exact mem_Icc.mpr ⟨hpp.one_le, Nat.le_of_dvd (NeZero.pos q₀) hpd⟩
                calc ∑ _p ∈ ((Icc 1 X).filter Nat.Prime).filter (fun p => p ∣ q₀), (1 : ℝ)
                    ≤ ∑ _p ∈ Icc 1 q₀, (1 : ℝ) :=
                      sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => zero_le_one
                  _ = (q₀ : ℝ) := by simp
                  _ ≤ Q := hq0Q
              linarith
            have h2 : (∑' p : Nat.Primes, if X < (p : ℕ) then 2 * ((p : ℕ) : ℝ) ^ (-s₀) else 0) ≤ 40 := by
              have hfac : (∑' p : Nat.Primes, if X < (p : ℕ) then 2 * ((p : ℕ) : ℝ) ^ (-s₀) else 0) =
                  2 * ∑' p : Nat.Primes, if X < (p : ℕ) then ((p : ℕ) : ℝ) ^ (-s₀) else 0 := by
                rw [← tsum_mul_left]; congr 1; ext p; split_ifs <;> ring
              rw [hfac]
              have htail := tsum_primes_gt_rpow_le (show 3 ≤ X by omega)
              have htail_eq : (∑' p : Nat.Primes, if X < (p : ℕ) then ((p : ℕ) : ℝ) ^ (-s₀) else 0) =
                  ∑' p : Nat.Primes, if (p : ℕ) ≤ X then (0 : ℝ) else ((p : ℕ) : ℝ) ^ (-(1 + 1 / Real.log (X : ℝ))) := by
                congr 1; ext p; by_cases hle : (p : ℕ) ≤ X
                · simp [hle, show ¬ X < (p : ℕ) by omega]
                · simp [hle, show X < (p : ℕ) by omega, s₀]
              rw [htail_eq]; linarith
            linarith
        _ = 3 * Q + 40 := by ring
    have hexp_eq : Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ) =
        Real.exp (Real.log (Real.log (X : ℝ)) - (3 * Q + 47)) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hlogX_pos, mul_comm]
    rw [hexp_eq]
    exact (Real.exp_le_exp.mpr (by linarith)).trans heul
  · have hsum_R : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-s₀)) := by
      have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-s₀)) := by
        simpa [Real.rpow_neg (Nat.cast_nonneg _)] using (Real.summable_nat_rpow_inv.mpr hs0)
      exact h1.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => by split_ifs <;> [positivity; exact le_rfl])
    have hsum_f0 : Summable (fun n : ℕ => ‖f₀ n‖) := by
      refine hsum_R.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
      by_cases hn0 : n = 0
      · subst hn0; simp [map_zero]
      · simp only [hn0, ↓reduceIte]; exact hf0_bd n (by omega)
    calc ‖∑' n : ℕ, f₀ n‖
        ≤ ∑' n : ℕ, ‖f₀ n‖ := norm_tsum_le_tsum_norm hsum_f0
      _ ≤ ∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-s₀) :=
          Summable.tsum_le_tsum (fun n => by
            by_cases hn0 : n = 0
            · subst hn0; simp [map_zero]
            · simp only [hn0, ↓reduceIte]; exact hf0_bd n (by omega)) hsum_f0 hsum_R
      _ ≤ 1 + 1 / (s₀ - 1) := tsum_nat_rpow_neg_le hs0
      _ = 1 + Real.log (X : ℝ) := by simp only [s₀, add_sub_cancel_left, one_div_one_div]
      _ ≤ 2 * Real.log (X : ℝ) := by linarith
lemma equidist_h_coprime_ap {q₀ M b : ℕ} [NeZero q₀] [NeZero M]
    (hcop_eq : ∀ n : ℕ, Nat.Coprime n M ↔ Nat.Coprime n q₀)
    (hb_cop : Nat.Coprime b q₀)
    {Q : ℝ} (hQ : 1 ≤ Q) {X : ℕ} (hX100 : 100 ≤ X)
    {h : ℕ →*₀ ℂ} (hh_norm : ∀ n, 1 ≤ n → ‖h n‖ = 1)
    (hh_dist : ∑ p ∈ (Icc 1 X).filter Nat.Prime, (1 - (h p).re) / (p : ℝ) ≤ 2 * Q) :
    let s₀ : ℝ := 1 + 1 / Real.log (X : ℝ)
    let L₀ : ℂ := ∑' n : ℕ, if n = 0 then (0 : ℂ) else
      if Nat.Coprime n q₀ then h n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0
    ‖(∑' n : ℕ, if 1 ≤ n ∧ n % M = b % M then h n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) -
      (1 / (M.totient : ℝ) : ℂ) * L₀‖ ≤
      (M : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) := by
  intro s₀ L₀
  have hlogX_gt1 : 1 < Real.log (X : ℝ) := by
    have hX100R : (100 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX100
    have h1 : Real.exp 1 < (X : ℝ) := by linarith [Real.exp_one_lt_d9]
    exact (Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < X by omega))).mpr h1
  have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
  have hs0 : 1 < s₀ := by simp only [s₀]; linarith [show 0 < 1 / Real.log (X : ℝ) by positivity]
  have hloglog_nn : 0 ≤ Real.log (Real.log (X : ℝ)) := Real.log_nonneg hlogX_gt1.le
  have hMpos : 0 < M := NeZero.pos M
  have hphi_pos : (0 : ℝ) < (M.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hMpos
  have hb_unit : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).mpr ((hcop_eq b).mpr hb_cop)
  have hsum_char_term : ∀ ψ : DirichletCharacter ℂ M,
      Summable (fun n : ℕ => if n = 0 then (0 : ℂ) else ψ (n : ZMod M) * h n * Complex.ofReal ((n : ℝ) ^ (-s₀))) := by
    intro ψ
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-s₀)) := by
      simpa [Real.rpow_neg (Nat.cast_nonneg _)] using (Real.summable_nat_rpow_inv.mpr hs0)
    refine Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) ^ (-s₀)) h1 fun n => ?_
    split_ifs with hn
    · simp; positivity
    · rw [norm_mul, norm_mul, hh_norm n (by omega), mul_one, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (dirichlet_norm_le_one ψ _)
  have horth : (M.totient : ℂ) *
      (∑' n : ℕ, if 1 ≤ n ∧ n % M = b % M then h n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) =
      ∑ ψ : DirichletCharacter ℂ M, ψ ((b : ZMod M)⁻¹) *
        ∑' n : ℕ, if n = 0 then (0 : ℂ) else ψ (n : ZMod M) * h n * Complex.ofReal ((n : ℝ) ^ (-s₀)) := by
    have hswap : ∑ ψ : DirichletCharacter ℂ M, ψ ((b : ZMod M)⁻¹) *
          ∑' n : ℕ, (if n = 0 then (0 : ℂ) else ψ (n : ZMod M) * h n * Complex.ofReal ((n : ℝ) ^ (-s₀))) =
        ∑' n : ℕ, ∑ ψ : DirichletCharacter ℂ M,
          ψ ((b : ZMod M)⁻¹) * (if n = 0 then (0 : ℂ) else ψ (n : ZMod M) * h n * Complex.ofReal ((n : ℝ) ^ (-s₀))) := by
      trans ∑ ψ : DirichletCharacter ℂ M,
          ∑' n : ℕ, ψ ((b : ZMod M)⁻¹) * (if n = 0 then (0 : ℂ) else ψ (n : ZMod M) * h n * Complex.ofReal ((n : ℝ) ^ (-s₀)))
      · refine sum_congr rfl fun ψ _ => (tsum_mul_left).symm
      · exact (Summable.tsum_finsetSum fun ψ _ => (hsum_char_term ψ).mul_left _).symm
    rw [hswap, ← tsum_mul_left]
    congr 1; ext n
    by_cases hn0 : n = 0
    · subst hn0; simp
    · have hn1 : 1 ≤ n := by omega
      simp only [hn0, hn1, true_and, ↓reduceIte]
      have hfactor : ∑ ψ : DirichletCharacter ℂ M, ψ ((b : ZMod M)⁻¹) * (ψ (n : ZMod M) * h n * Complex.ofReal ((n : ℝ) ^ (-s₀))) =
          (∑ ψ : DirichletCharacter ℂ M, ψ ((b : ZMod M)⁻¹) * ψ (n : ZMod M)) *
            (h n * Complex.ofReal ((n : ℝ) ^ (-s₀))) := by
        rw [sum_mul]
        refine sum_congr rfl fun ψ _ => by ring
      rw [hfactor, DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb_unit (n : ZMod M)]
      have hmod_iff : ((b : ZMod M) = (n : ZMod M)) ↔ n % M = b % M := by
        rw [eq_comm, ZMod.natCast_eq_natCast_iff']
      split_ifs with h1 h2 h3
      · rfl
      · exact absurd (hmod_iff.mpr h1) h2
      · exact absurd (hmod_iff.mp h3) h1
      · simp
  have h1_term : (1 : DirichletCharacter ℂ M) ((b : ZMod M)⁻¹) *
      ∑' n : ℕ, (if n = 0 then (0 : ℂ) else (1 : DirichletCharacter ℂ M) (n : ZMod M) * h n * Complex.ofReal ((n : ℝ) ^ (-s₀))) =
      L₀ := by
    have hb_inv_unit : IsUnit ((b : ZMod M)⁻¹) := by
      exact isUnit_iff_exists_inv.mpr ⟨(b : ZMod M), ZMod.inv_mul_of_unit _ hb_unit⟩
    rw [MulChar.one_apply hb_inv_unit, one_mul]
    congr 1; ext n
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ↓reduceIte]
      by_cases hcop : Nat.Coprime n q₀
      · have hunit : IsUnit (n : ZMod M) := (ZMod.isUnit_iff_coprime n M).mpr ((hcop_eq n).mpr hcop)
        rw [if_pos hcop, MulChar.one_apply hunit, one_mul]
      · have hnu : ¬ IsUnit (n : ZMod M) := fun hu => hcop ((hcop_eq n).mp ((ZMod.isUnit_iff_coprime n M).mp hu))
        rw [if_neg hcop, MulChar.map_nonunit _ hnu, zero_mul, zero_mul]
  have hprime_diff_sum : ∑' p : Nat.Primes, 2 * ‖h p - 1‖ * ((p : ℕ) : ℝ) ^ (-s₀) ≤
      (1 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) + (640 * Q + 100) := by
    have hsum_pr : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-s₀)) := summable_primes_rpow hs0
    have hsum_lhs : Summable (fun p : Nat.Primes => 2 * ‖h p - 1‖ * ((p : ℕ) : ℝ) ^ (-s₀)) := by
      refine (hsum_pr.mul_left 4).of_nonneg_of_le (fun _ => by positivity) fun p => ?_
      have hbd : ‖h p - 1‖ ≤ 2 := by
        calc ‖h p - 1‖ ≤ ‖h p‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [hh_norm p p.prop.one_le, norm_one]; norm_num
      have : 2 * ‖h p - 1‖ ≤ 4 := by linarith
      exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hsum_leX : Summable (fun p : Nat.Primes =>
        if (p : ℕ) ≤ X then 2 * ‖h p - 1‖ * ((p : ℕ) : ℝ) ^ (-s₀) else 0) := by
      exact hsum_lhs.of_nonneg_of_le (fun _ => by split_ifs <;> positivity)
        (fun _ => by split_ifs <;> [exact le_rfl; positivity])
    have hsum_gtX : Summable (fun p : Nat.Primes =>
        if X < (p : ℕ) then 2 * ‖h p - 1‖ * ((p : ℕ) : ℝ) ^ (-s₀) else 0) := by
      exact hsum_lhs.of_nonneg_of_le (fun _ => by split_ifs <;> positivity)
        (fun _ => by split_ifs <;> [exact le_rfl; positivity])
    have hsplit : (∑' p : Nat.Primes, 2 * ‖h p - 1‖ * ((p : ℕ) : ℝ) ^ (-s₀)) =
        (∑' p : Nat.Primes, if (p : ℕ) ≤ X then 2 * ‖h p - 1‖ * ((p : ℕ) : ℝ) ^ (-s₀) else 0) +
        (∑' p : Nat.Primes, if X < (p : ℕ) then 2 * ‖h p - 1‖ * ((p : ℕ) : ℝ) ^ (-s₀) else 0) := by
      rw [← hsum_leX.tsum_add hsum_gtX]
      congr 1; ext p
      by_cases hle : (p : ℕ) ≤ X
      · have hnl : ¬ X < (p : ℕ) := Nat.not_lt.mpr hle
        simp [hle, hnl]
      · have hlt : X < (p : ℕ) := Nat.lt_of_not_ge hle
        simp [hle, hlt]
    rw [hsplit]
    have hhead : (∑' p : Nat.Primes, if (p : ℕ) ≤ X then 2 * ‖h p - 1‖ * ((p : ℕ) : ℝ) ^ (-s₀) else 0) ≤
        (1 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) + (640 * Q + 20) := by
      let S : Finset Nat.Primes := ((Icc 1 X).filter Nat.Prime).attach.map
        ⟨fun p => ⟨p.1, (mem_filter.mp p.2).2⟩, fun _ _ h => Subtype.ext (by injection h)⟩
      rw [tsum_eq_sum (s := S) (fun p hp => by
        by_cases hleX : (p : ℕ) ≤ X
        · exfalso; apply hp
          simp only [S, Finset.mem_map, mem_attach, true_and]
          exact ⟨⟨p.1, mem_filter.mpr ⟨mem_Icc.mpr ⟨p.prop.one_le, hleX⟩, p.prop⟩⟩, rfl⟩
        · simp [hleX])]
      have hsimp : ∑ p ∈ S, (if (p : ℕ) ≤ X then 2 * ‖h p - 1‖ * ((p : ℕ) : ℝ) ^ (-s₀) else 0) =
          ∑ p ∈ (Icc 1 X).filter Nat.Prime, 2 * ‖h p - 1‖ * (p : ℝ) ^ (-s₀) := by
        refine sum_nbij (fun p => (p : ℕ)) ?_ ?_ ?_ ?_
        · intro p hp
          simp only [S, Finset.mem_map, mem_attach, true_and] at hp
          rcases hp with ⟨q, hq⟩; rw [← hq]; exact q.2
        · intro p₁ _ p₂ _ h; exact Subtype.ext h
        · intro p hp
          refine ⟨⟨p, (mem_filter.mp hp).2⟩, ?_, rfl⟩
          exact Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨⟨p, hp⟩, mem_attach _ _, rfl⟩)
        · intro p hp
          simp only [S, Finset.mem_map, mem_attach, true_and] at hp
          rcases hp with ⟨q, hq⟩
          have hleX : (p : ℕ) ≤ X := by
            rw [← hq]; exact (mem_Icc.mp (mem_filter.mp q.2).1).2
          simp [hleX]
      rw [hsimp]
      let u : ℝ := ∑ p ∈ (Icc 1 X).filter Nat.Prime, 2 * ‖h p - 1‖ * (p : ℝ) ^ (-s₀)
      have hu_nn : 0 ≤ u := sum_nonneg fun _ _ => by positivity
      have hu_le : u ≤ ∑ p ∈ (Icc 1 X).filter Nat.Prime,
          (2 * ‖h p - 1‖ / Real.sqrt (p : ℝ)) * (1 / Real.sqrt (p : ℝ)) := by
        refine sum_le_sum fun p hp => ?_
        have hpp : p.Prime := (mem_filter.mp hp).2
        have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
        have hrpow_le : (p : ℝ) ^ (-s₀) ≤ 1 / (p : ℝ) := by
          rw [one_div, ← Real.rpow_neg_one]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpp.one_le) (by linarith)
        have hmul_sq : (2 * ‖h p - 1‖ / Real.sqrt (p : ℝ)) * (1 / Real.sqrt (p : ℝ)) =
            2 * ‖h p - 1‖ * (1 / (p : ℝ)) := by
          rw [div_mul_div_comm, mul_one, Real.mul_self_sqrt hp_pos.le]; ring
        rw [hmul_sq]
        exact mul_le_mul_of_nonneg_left hrpow_le (by positivity)
      have hcs : u ^ 2 ≤
          (∑ p ∈ (Icc 1 X).filter Nat.Prime, (2 * ‖h p - 1‖ / Real.sqrt (p : ℝ)) ^ 2) *
          (∑ p ∈ (Icc 1 X).filter Nat.Prime, (1 / Real.sqrt (p : ℝ)) ^ 2) :=
        (pow_le_pow_left₀ hu_nn hu_le 2).trans (sum_mul_sq_le_sq_mul_sq _ _ _)
      have hfac1 : ∑ p ∈ (Icc 1 X).filter Nat.Prime, (2 * ‖h p - 1‖ / Real.sqrt (p : ℝ)) ^ 2 ≤ 16 * Q := by
        calc ∑ p ∈ (Icc 1 X).filter Nat.Prime, (2 * ‖h p - 1‖ / Real.sqrt (p : ℝ)) ^ 2
            = 8 * ∑ p ∈ (Icc 1 X).filter Nat.Prime, (1 - (h p).re) / (p : ℝ) := by
              rw [mul_sum]
              refine sum_congr rfl fun p hp => ?_
              have hpp : p.Prime := (mem_filter.mp hp).2
              have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
              have hsq : ‖h p - 1‖ ^ 2 = 2 * (1 - (h p).re) := by
                have h1 : ‖h p - 1‖ ^ 2 = ‖h p‖ ^ 2 + ‖(1 : ℂ)‖ ^ 2 - 2 * (h p).re := by
                  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
                    Complex.normSq_apply, Complex.normSq_apply]
                  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
                  ring
                rw [h1, hh_norm p hpp.one_le, norm_one]; ring
              rw [div_pow, mul_pow, Real.sq_sqrt hp_pos.le, hsq]; ring
          _ ≤ 8 * (2 * Q) := by linarith
          _ = 16 * Q := by ring
      have hfac2 : ∑ p ∈ (Icc 1 X).filter Nat.Prime, (1 / Real.sqrt (p : ℝ)) ^ 2 ≤
          20 * Real.log (Real.log (X : ℝ)) + 20 := by
        have heq : ∑ p ∈ (Icc 1 X).filter Nat.Prime, (1 / Real.sqrt (p : ℝ)) ^ 2 =
            ∑ p ∈ (Icc 1 X).filter Nat.Prime, 1 / (p : ℝ) := by
          refine sum_congr rfl fun p hp => ?_
          have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.pos
          rw [div_pow, one_pow, Real.sq_sqrt hp_pos.le]
        rw [heq]
        exact sum_inv_primes_le (by omega)
      have hu_sq : u ^ 2 ≤ (16 * Q) * (20 * Real.log (Real.log (X : ℝ)) + 20) :=
        hcs.trans (mul_le_mul hfac1 hfac2 (sum_nonneg fun _ _ => sq_nonneg _) (by positivity))
      nlinarith
    have htail : (∑' p : Nat.Primes, if X < (p : ℕ) then 2 * ‖h p - 1‖ * ((p : ℕ) : ℝ) ^ (-s₀) else 0) ≤ 80 := by
      have hle : ∑' p : Nat.Primes, (if X < (p : ℕ) then 2 * ‖h p - 1‖ * ((p : ℕ) : ℝ) ^ (-s₀) else 0) ≤
          4 * ∑' p : Nat.Primes, if X < (p : ℕ) then ((p : ℕ) : ℝ) ^ (-s₀) else 0 := by
        rw [← tsum_mul_left]
        refine Summable.tsum_le_tsum (fun p => ?_) hsum_gtX
          ((hsum_pr.of_nonneg_of_le (fun _ => by split_ifs <;> positivity)
            (fun _ => by split_ifs <;> [exact le_rfl; positivity])).mul_left 4)
        split_ifs
        · have hbd : ‖h p - 1‖ ≤ 2 := by
            calc ‖h p - 1‖ ≤ ‖h p‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
              _ = 2 := by rw [hh_norm p p.prop.one_le, norm_one]; norm_num
          exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        · simp
      have htail_eq : (∑' p : Nat.Primes, if X < (p : ℕ) then ((p : ℕ) : ℝ) ^ (-s₀) else 0) =
          ∑' p : Nat.Primes, if (p : ℕ) ≤ X then (0 : ℝ) else ((p : ℕ) : ℝ) ^ (-(1 + 1 / Real.log (X : ℝ))) := by
        congr 1; ext p; by_cases hle : (p : ℕ) ≤ X
        · have hnl : ¬ X < (p : ℕ) := Nat.not_lt.mpr hle
          simp [hle, hnl]
        · have hlt : X < (p : ℕ) := Nat.lt_of_not_ge hle
          simp [hle, hlt, s₀]
      rw [htail_eq] at hle
      linarith [tsum_primes_gt_rpow_le (show 3 ≤ X by omega)]
    linarith
  have hnonprinc : ∀ ψ : DirichletCharacter ℂ M, ψ ≠ 1 →
      ‖∑' n : ℕ, if n = 0 then (0 : ℂ) else ψ (n : ZMod M) * h n * Complex.ofReal ((n : ℝ) ^ (-s₀))‖ ≤
        (M : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) := by
    intro ψ hψ
    let f₁ : ℕ →*₀ ℂ := {
      toFun := fun n => if n = 0 then 0 else ψ (n : ZMod M) * h n * Complex.ofReal ((n : ℝ) ^ (-s₀))
      map_zero' := by simp
      map_one' := by simp
      map_mul' := fun m n => by
        by_cases hm : m = 0
        · subst hm; simp
        by_cases hn : n = 0
        · subst hn; simp
        have hmn : m * n ≠ 0 := mul_ne_zero hm hn
        simp only [hm, hn, hmn, ↓reduceIte, Nat.cast_mul, map_mul]
        rw [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]; push_cast; ring }
    let f₂ : ℕ →*₀ ℂ := {
      toFun := fun n => if n = 0 then 0 else ψ (n : ZMod M) * Complex.ofReal ((n : ℝ) ^ (-s₀))
      map_zero' := by simp
      map_one' := by simp
      map_mul' := fun m n => by
        by_cases hm : m = 0
        · subst hm; simp
        by_cases hn : n = 0
        · subst hn; simp
        have hmn : m * n ≠ 0 := mul_ne_zero hm hn
        simp only [hm, hn, hmn, ↓reduceIte, Nat.cast_mul, map_mul]
        rw [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]; push_cast; ring }
    have hbd₁ : ∀ n, 1 ≤ n → ‖f₁ n‖ ≤ (n : ℝ) ^ (-s₀) := by
      intro n hn
      simp only [f₁, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, show n ≠ 0 by omega, ↓reduceIte]
      rw [norm_mul, norm_mul, hh_norm n hn, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (dirichlet_norm_le_one ψ _)
    have hbd₂ : ∀ n, 1 ≤ n → ‖f₂ n‖ ≤ (n : ℝ) ^ (-s₀) := by
      intro n hn
      simp only [f₂, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, show n ≠ 0 by omega, ↓reduceIte]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (dirichlet_norm_le_one ψ _)
    have hrat := euler_ratio_norm_le hs0 hbd₁ hbd₂
    have hL2 : ‖∑' n : ℕ, f₂ n‖ ≤ (M : ℝ) := nonprincipal_dirichletL_le ψ hψ hs0
    have hdiff_le : ∑' p : Nat.Primes, 2 * ‖f₁ p - f₂ p‖ ≤
        ∑' p : Nat.Primes, 2 * ‖h p - 1‖ * ((p : ℕ) : ℝ) ^ (-s₀) := by
      have hsum_pr : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-s₀)) := summable_primes_rpow hs0
      have hsum_R : Summable (fun p : Nat.Primes => 2 * ‖h p - 1‖ * ((p : ℕ) : ℝ) ^ (-s₀)) := by
        refine (hsum_pr.mul_left 4).of_nonneg_of_le (fun _ => by positivity) fun p => ?_
        have hbd : ‖h p - 1‖ ≤ 2 := by
          calc ‖h p - 1‖ ≤ ‖h p‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by rw [hh_norm p p.prop.one_le, norm_one]; norm_num
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have hpw : ∀ p : Nat.Primes, 2 * ‖f₁ p - f₂ p‖ ≤ 2 * ‖h p - 1‖ * ((p : ℕ) : ℝ) ^ (-s₀) := by
        intro p
        simp only [f₁, f₂, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, p.prop.ne_zero, ↓reduceIte]
        have heq : ψ ((p : ℕ) : ZMod M) * h p * Complex.ofReal (((p : ℕ) : ℝ) ^ (-s₀)) -
            ψ ((p : ℕ) : ZMod M) * Complex.ofReal (((p : ℕ) : ℝ) ^ (-s₀)) =
            ψ ((p : ℕ) : ZMod M) * ((h p - 1) * Complex.ofReal (((p : ℕ) : ℝ) ^ (-s₀))) := by ring
        rw [heq, norm_mul, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
        have h1 : ‖ψ ((p : ℕ) : ZMod M)‖ * (‖h p - 1‖ * ((p : ℕ) : ℝ) ^ (-s₀)) ≤
            1 * (‖h p - 1‖ * ((p : ℕ) : ℝ) ^ (-s₀)) :=
          mul_le_mul_of_nonneg_right (dirichlet_norm_le_one ψ _) (by positivity)
        linarith
      exact Summable.tsum_le_tsum hpw
        (hsum_R.of_nonneg_of_le (fun _ => by positivity) hpw) hsum_R
    have hexp_bd : Real.exp (∑' p : Nat.Primes, 2 * ‖f₁ p - f₂ p‖) ≤
        Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) := by
      calc Real.exp (∑' p : Nat.Primes, 2 * ‖f₁ p - f₂ p‖)
          ≤ Real.exp ((1 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) + (640 * Q + 100)) :=
            Real.exp_le_exp.mpr (hdiff_le.trans hprime_diff_sum)
        _ = Real.exp (640 * Q + 100) * Real.exp ((1 / 4 : ℝ) * Real.log (Real.log (X : ℝ))) := by
            rw [Real.exp_add, mul_comm]
        _ = Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) := by
            congr 1; rw [Real.rpow_def_of_pos hlogX_pos, mul_comm]
    calc ‖∑' n : ℕ, f₁ n‖
        ≤ ‖∑' n : ℕ, f₂ n‖ * Real.exp (∑' p : Nat.Primes, 2 * ‖f₁ p - f₂ p‖) := hrat
      _ ≤ (M : ℝ) * (Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ)) :=
          mul_le_mul hL2 hexp_bd (Real.exp_pos _).le (Nat.cast_nonneg M)
      _ = (M : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) := by ring
  have hsub : (M.totient : ℂ) *
      ((∑' n : ℕ, if 1 ≤ n ∧ n % M = b % M then h n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) -
        (1 / (M.totient : ℝ) : ℂ) * L₀) =
      ∑ ψ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ M), ψ ((b : ZMod M)⁻¹) *
        ∑' n : ℕ, if n = 0 then (0 : ℂ) else ψ (n : ZMod M) * h n * Complex.ofReal ((n : ℝ) ^ (-s₀)) := by
    have hphi_ne : (M.totient : ℂ) ≠ 0 := by exact_mod_cast hphi_pos.ne'
    have hmul_sub : (M.totient : ℂ) *
        ((∑' n : ℕ, if 1 ≤ n ∧ n % M = b % M then h n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) -
          (1 / (M.totient : ℝ) : ℂ) * L₀) =
        (M.totient : ℂ) * (∑' n : ℕ, if 1 ≤ n ∧ n % M = b % M then h n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) - L₀ := by
      have : (M.totient : ℂ) * ((1 / (M.totient : ℝ) : ℂ) * L₀) = L₀ := by
        simp only [one_div, Complex.ofReal_inv, Complex.ofReal_natCast]
        rw [← mul_assoc, mul_inv_cancel₀ hphi_ne, one_mul]
      rw [mul_sub, this]
    rw [hmul_sub, horth, ← add_sum_erase _ _ (mem_univ (1 : DirichletCharacter ℂ M)), h1_term]
    ring
  have hnorm_sub : (M.totient : ℝ) *
      ‖(∑' n : ℕ, if 1 ≤ n ∧ n % M = b % M then h n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) -
        (1 / (M.totient : ℝ) : ℂ) * L₀‖ ≤
      (M.totient : ℝ) * ((M : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ)) := by
    have hlhs : (M.totient : ℝ) *
        ‖(∑' n : ℕ, if 1 ≤ n ∧ n % M = b % M then h n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) -
          (1 / (M.totient : ℝ) : ℂ) * L₀‖ =
        ‖(M.totient : ℂ) *
          ((∑' n : ℕ, if 1 ≤ n ∧ n % M = b % M then h n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) -
            (1 / (M.totient : ℝ) : ℂ) * L₀)‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [hlhs, hsub]
    calc ‖∑ ψ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ M), ψ ((b : ZMod M)⁻¹) *
            ∑' n : ℕ, if n = 0 then (0 : ℂ) else ψ (n : ZMod M) * h n * Complex.ofReal ((n : ℝ) ^ (-s₀))‖
        ≤ ∑ ψ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ M),
            ‖ψ ((b : ZMod M)⁻¹) *
              ∑' n : ℕ, if n = 0 then (0 : ℂ) else ψ (n : ZMod M) * h n * Complex.ofReal ((n : ℝ) ^ (-s₀))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _ψ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ M),
            ((M : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ)) := by
          refine sum_le_sum fun ψ hψ => ?_
          rw [norm_mul]
          calc ‖ψ ((b : ZMod M)⁻¹)‖ * _
              ≤ 1 * ((M : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ)) :=
                mul_le_mul (dirichlet_norm_le_one ψ _) (hnonprinc ψ (ne_of_mem_erase hψ))
                  (norm_nonneg _) zero_le_one
            _ = _ := one_mul _
      _ = ((Finset.univ.erase (1 : DirichletCharacter ℂ M)).card : ℝ) *
            ((M : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (M.totient : ℝ) * ((M : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hcard : (Finset.univ.erase (1 : DirichletCharacter ℂ M)).card ≤ Fintype.card (DirichletCharacter ℂ M) :=
            card_le_univ _
          have htot : Fintype.card (DirichletCharacter ℂ M) ≤ M.totient := by
            have h1 := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (isUnit_one : IsUnit (1 : ZMod M)) 1
            have hinv1 : (1 : ZMod M)⁻¹ = 1 := by
              simpa using ZMod.inv_mul_of_unit (1 : ZMod M) isUnit_one
            rw [hinv1] at h1
            simp only [map_one, mul_one, sum_const, Finset.card_univ, nsmul_eq_mul,
              ↓reduceIte] at h1
            exact ((Nat.cast_inj (R := ℂ)).mp h1).le
          exact_mod_cast hcard.trans htot
  exact le_of_mul_le_mul_left hnorm_sub hphi_pos
lemma equidist_h_good_shift {q₀ k H a m N₀ X : ℕ} [NeZero q₀] (hk : 2 ≤ k) (hH : 4 ≤ H)
    (hX100 : 100 ≤ X) (hN0 : 1 ≤ N₀)
    (hgood : isGoodRes q₀ k H a) (hm : m ∈ Icc 1 (2 * H))
    {Q : ℝ} (hQ : 1 ≤ Q) (hq0Q : (q₀ : ℝ) ≤ Q)
    {h : ℕ →*₀ ℂ} (hh_norm : ∀ n, 1 ≤ n → ‖h n‖ = 1)
    (hh_q0 : ∀ p, p.Prime → p ∣ q₀ → h p = 1)
    (hh_dist : ∑ p ∈ (Icc 1 X).filter Nat.Prime, (1 - (h p).re) / (p : ℝ) ≤ 2 * Q) :
    let s₀ : ℝ := 1 + 1 / Real.log (X : ℝ)
    let L₀ : ℂ := ∑' n : ℕ, if n = 0 then (0 : ℂ) else
      if Nat.Coprime n q₀ then h n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0
    ‖(∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then h (n + m) * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) -
      (1 / ((q₀ ^ k).totient : ℝ) : ℂ) * L₀‖ ≤
      8 * (H : ℝ) +
      (1 + (1 / ((q₀ ^ k : ℕ) : ℝ)) * (Real.log ((N₀ + 2 * H : ℕ) : ℝ) + 1)) +
      ((q₀ ^ k : ℕ) : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) +
      2 * Real.log ((q₀ ^ k : ℕ) : ℝ) := by
  intro s₀ L₀
  have hlogX_gt1 : 1 < Real.log (X : ℝ) := by
    have hX100R : (100 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX100
    have h1 : Real.exp 1 < (X : ℝ) := by linarith [Real.exp_one_lt_d9]
    exact (Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < X by omega))).mpr h1
  have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
  have hs0 : 1 < s₀ := by simp only [s₀]; linarith [show 0 < 1 / Real.log (X : ℝ) by positivity]
  have hs0_le2 : s₀ ≤ 2 := by
    simp only [s₀]; have : 1 / Real.log (X : ℝ) ≤ 1 := (div_le_one hlogX_pos).mpr hlogX_gt1.le; linarith
  have hq0_pos : 0 < q₀ := NeZero.pos q₀
  have hqk_pos : 0 < q₀ ^ k := pow_pos hq0_pos k
  have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
  have hm2H : m ≤ 2 * H := (mem_Icc.mp hm).2
  have hsum_rpow : Summable (fun n : ℕ => (n : ℝ) ^ (-s₀)) := by
    simpa [Real.rpow_neg (Nat.cast_nonneg _)] using (Real.summable_nat_rpow_inv.mpr hs0)
  let T1 : ℂ := ∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then h (n + m) * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0
  let T2 : ℂ := ∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then h (n + m) * Complex.ofReal (((n + m : ℕ) : ℝ) ^ (-s₀)) else 0
  have hsum_T1 : Summable (fun n : ℕ => if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then h (n + m) * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) ^ (-s₀)) hsum_rpow fun n => ?_
    split_ifs with hc
    · rw [norm_mul, hh_norm (n + m) (by omega), one_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    · simp; positivity
  have hsum_T2 : Summable (fun n : ℕ => if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then h (n + m) * Complex.ofReal (((n + m : ℕ) : ℝ) ^ (-s₀)) else 0) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) ^ (-s₀)) hsum_rpow fun n => ?_
    split_ifs with hc
    · rw [norm_mul, hh_norm (n + m) (by omega), one_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < n by omega))
        (by exact_mod_cast Nat.le_add_right n m) (by linarith)
    · simp; positivity
  have hstepA : ‖T1 - T2‖ ≤ 8 * (H : ℝ) := by
    have hsub : T1 - T2 = ∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
        h (n + m) * ((((n : ℝ) ^ (-s₀) - ((n + m : ℕ) : ℝ) ^ (-s₀)) : ℝ) : ℂ) else 0 := by
      rw [← hsum_T1.tsum_sub hsum_T2]
      congr 1; ext n; split_ifs <;> [push_cast; skip] <;> ring
    rw [hsub]
    have hsum_inv2 : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-2 : ℝ)) := by
      have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) := by
        simpa [Real.rpow_neg (Nat.cast_nonneg _)] using (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2))
      exact h1.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => by split_ifs <;> [positivity; exact le_rfl])
    have hpw : ∀ n : ℕ, ‖if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
        h (n + m) * ((((n : ℝ) ^ (-s₀) - ((n + m : ℕ) : ℝ) ^ (-s₀)) : ℝ) : ℂ) else 0‖ ≤
        (4 * (H : ℝ)) * (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-2 : ℝ)) := by
      intro n
      split_ifs with hc hn0
      · omega
      · rw [norm_mul, hh_norm (n + m) (by omega), one_mul, Complex.norm_real]
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
        have hlt : (n : ℝ) < ((n + m : ℕ) : ℝ) := by exact_mod_cast (show n < n + m by omega)
        have hcont : ContinuousOn (fun x : ℝ => x ^ (-s₀)) (Set.Icc (n : ℝ) ((n + m : ℕ) : ℝ)) :=
          fun x hx => (Real.continuousAt_rpow_const x (-s₀) (Or.inl (lt_of_lt_of_le hn_pos hx.1).ne')).continuousWithinAt
        have hdiff : ∀ x ∈ Set.Ioo (n : ℝ) ((n + m : ℕ) : ℝ),
            HasDerivAt (fun t : ℝ => t ^ (-s₀)) ((-s₀) * x ^ (-s₀ - 1)) x :=
          fun x hx => Real.hasDerivAt_rpow_const (p := -s₀) (Or.inl (lt_of_lt_of_le hn_pos hx.1.le).ne')
        obtain ⟨c, ⟨hc1, _⟩, hslope⟩ := exists_hasDerivAt_eq_slope (fun x : ℝ => x ^ (-s₀))
          (fun x => (-s₀) * x ^ (-s₀ - 1)) hlt hcont hdiff
        have hden : ((n + m : ℕ) : ℝ) - (n : ℝ) = (m : ℝ) := by push_cast; ring
        rw [hden] at hslope
        have hdiff_eq : (n : ℝ) ^ (-s₀) - ((n + m : ℕ) : ℝ) ^ (-s₀) = (m : ℝ) * (s₀ * c ^ (-s₀ - 1)) := by
          have := (div_eq_iff (show (m : ℝ) ≠ 0 by exact_mod_cast (show m ≠ 0 by omega))).mp hslope.symm
          linarith
        have hc_pos : 0 < c := lt_of_lt_of_le hn_pos hc1.le
        rw [hdiff_eq, Real.norm_of_nonneg (by positivity)]
        have hc_bd : c ^ (-s₀ - 1) ≤ (n : ℝ) ^ (-2 : ℝ) := by
          calc c ^ (-s₀ - 1) ≤ (n : ℝ) ^ (-s₀ - 1) :=
                Real.rpow_le_rpow_of_nonpos hn_pos hc1.le (by linarith)
            _ ≤ (n : ℝ) ^ (-2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega)) (by linarith)
        have hm_le : (m : ℝ) ≤ 2 * (H : ℝ) := by exact_mod_cast hm2H
        calc (m : ℝ) * (s₀ * c ^ (-s₀ - 1))
            ≤ (2 * (H : ℝ)) * (2 * (n : ℝ) ^ (-2 : ℝ)) :=
              mul_le_mul hm_le (mul_le_mul hs0_le2 hc_bd (Real.rpow_nonneg (lt_of_lt_of_le hn_pos hc1.le).le _) (by norm_num))
                (by positivity) (by positivity)
          _ = 4 * (H : ℝ) * (n : ℝ) ^ (-2 : ℝ) := by ring
      · simp
      · simp; positivity
    have hsum_norm : Summable (fun n : ℕ => ‖if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
        h (n + m) * ((((n : ℝ) ^ (-s₀) - ((n + m : ℕ) : ℝ) ^ (-s₀)) : ℝ) : ℂ) else 0‖) :=
      (hsum_inv2.mul_left (4 * (H : ℝ))).of_nonneg_of_le (fun _ => norm_nonneg _) hpw
    calc ‖∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
            h (n + m) * ((((n : ℝ) ^ (-s₀) - ((n + m : ℕ) : ℝ) ^ (-s₀)) : ℝ) : ℂ) else 0‖
        ≤ ∑' n : ℕ, ‖if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
            h (n + m) * ((((n : ℝ) ^ (-s₀) - ((n + m : ℕ) : ℝ) ^ (-s₀)) : ℝ) : ℂ) else 0‖ :=
          norm_tsum_le_tsum_norm hsum_norm
      _ ≤ ∑' n : ℕ, (4 * (H : ℝ)) * (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-2 : ℝ)) :=
          Summable.tsum_le_tsum hpw hsum_norm (hsum_inv2.mul_left _)
      _ = (4 * (H : ℝ)) * ∑' n : ℕ, (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-2 : ℝ)) := tsum_mul_left
      _ ≤ (4 * (H : ℝ)) * (1 + 1 / (2 - 1 : ℝ)) :=
          mul_le_mul_of_nonneg_left (tsum_nat_rpow_neg_le (by norm_num)) (by positivity)
      _ = 8 * (H : ℝ) := by ring
  let T3 : ℂ := ∑' n' : ℕ, if 1 ≤ n' ∧ n' % (q₀ ^ k) = (a + m) % (q₀ ^ k) then h n' * Complex.ofReal ((n' : ℝ) ^ (-s₀)) else 0
  have hsum_T3 : Summable (fun n' : ℕ => if 1 ≤ n' ∧ n' % (q₀ ^ k) = (a + m) % (q₀ ^ k) then h n' * Complex.ofReal ((n' : ℝ) ^ (-s₀)) else 0) := by
    refine Summable.of_norm_bounded (g := fun n' : ℕ => (n' : ℝ) ^ (-s₀)) hsum_rpow fun n' => ?_
    split_ifs with hc
    · rw [norm_mul, hh_norm n' hc.1, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    · simp; positivity
  have hT2_shift : T2 = ∑' n' : ℕ, if N₀ + m ≤ n' ∧ n' % (q₀ ^ k) = (a + m) % (q₀ ^ k) then h n' * Complex.ofReal ((n' : ℝ) ^ (-s₀)) else 0 := by
    have heq := tsum_eq_tsum_of_ne_zero_bij (i := fun x : {n : ℕ // (if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then h (n + m) * Complex.ofReal (((n + m : ℕ) : ℝ) ^ (-s₀)) else 0) ≠ 0} => x.1 + m)
      (f := fun n' : ℕ => if N₀ + m ≤ n' ∧ n' % (q₀ ^ k) = (a + m) % (q₀ ^ k) then h n' * Complex.ofReal ((n' : ℝ) ^ (-s₀)) else 0)
      (g := fun n : ℕ => if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then h (n + m) * Complex.ofReal (((n + m : ℕ) : ℝ) ^ (-s₀)) else 0)
      (fun x y hxy => Subtype.ext (by dsimp at hxy; omega))
      (fun n' hn' => by
        have hcond : N₀ + m ≤ n' ∧ n' % (q₀ ^ k) = (a + m) % (q₀ ^ k) := by
          by_contra hc; simp [hc] at hn'
        have hmod : (n' - m) % (q₀ ^ k) = a % (q₀ ^ k) := by
          rw [← ZMod.natCast_eq_natCast_iff'] at hcond ⊢
          have hsub : ((n' - m : ℕ) : ZMod (q₀ ^ k)) + (m : ZMod (q₀ ^ k)) = (n' : ZMod (q₀ ^ k)) := by
            rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)]
          have h2 : ((n' - m : ℕ) : ZMod (q₀ ^ k)) + (m : ZMod (q₀ ^ k)) =
              (a : ZMod (q₀ ^ k)) + (m : ZMod (q₀ ^ k)) := by
            rw [hsub, hcond.2, Nat.cast_add]
          exact add_right_cancel h2
        have hne_g : (if N₀ ≤ n' - m ∧ (n' - m) % (q₀ ^ k) = a % (q₀ ^ k) then
            h (n' - m + m) * Complex.ofReal (((n' - m + m : ℕ) : ℝ) ^ (-s₀)) else 0) ≠ 0 := by
          rw [if_pos ⟨by omega, hmod⟩, Nat.sub_add_cancel (by omega)]
          simpa [hcond] using hn'
        exact ⟨⟨n' - m, hne_g⟩, Nat.sub_add_cancel (by omega)⟩)
      (fun x => by
        have hcond : N₀ ≤ x.1 ∧ x.1 % (q₀ ^ k) = a % (q₀ ^ k) := by
          by_contra hc; exact x.2 (by simp [hc])
        have hmod : (x.1 + m) % (q₀ ^ k) = (a + m) % (q₀ ^ k) := by
          rw [Nat.add_mod, hcond.2, ← Nat.add_mod]
        rw [if_pos ⟨by omega, hmod⟩, if_pos ⟨hcond.1, hcond.2⟩])
    exact heq.symm
  have hstepB : ‖T2 - T3‖ ≤ 1 + (1 / ((q₀ ^ k : ℕ) : ℝ)) * (Real.log ((N₀ + 2 * H : ℕ) : ℝ) + 1) := by
    have hsum_T2' : Summable (fun n' : ℕ => if N₀ + m ≤ n' ∧ n' % (q₀ ^ k) = (a + m) % (q₀ ^ k) then h n' * Complex.ofReal ((n' : ℝ) ^ (-s₀)) else 0) := by
      refine Summable.of_norm_bounded (g := fun n' : ℕ => (n' : ℝ) ^ (-s₀)) hsum_rpow fun n' => ?_
      split_ifs with hc
      · rw [norm_mul, hh_norm n' (by omega), one_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      · simp; positivity
    have hdiff_eq : T3 - T2 = ∑ n' ∈ Ico 1 (N₀ + m),
        if n' % (q₀ ^ k) = (a + m) % (q₀ ^ k) then h n' * Complex.ofReal ((n' : ℝ) ^ (-s₀)) else 0 := by
      rw [hT2_shift, ← hsum_T3.tsum_sub hsum_T2']
      rw [tsum_eq_sum (s := Ico 1 (N₀ + m))]
      · refine sum_congr rfl fun n' hn' => ?_
        have h1 : 1 ≤ n' := (mem_Ico.mp hn').1
        have h2 : ¬ N₀ + m ≤ n' := by have := (mem_Ico.mp hn').2; omega
        by_cases hm' : n' % (q₀ ^ k) = (a + m) % (q₀ ^ k) <;> simp [h1, h2, hm']
      · intro n' hn'
        simp only [mem_Ico, not_and_or, not_le, not_lt] at hn'
        rcases hn' with h0 | hge
        · have : ¬ 1 ≤ n' := by omega
          have : ¬ N₀ + m ≤ n' := by omega
          simp [*]
        · have : 1 ≤ n' := by omega
          by_cases hm' : n' % (q₀ ^ k) = (a + m) % (q₀ ^ k) <;> simp [*, hge]
    rw [norm_sub_rev, hdiff_eq]
    calc ‖∑ n' ∈ Ico 1 (N₀ + m),
            if n' % (q₀ ^ k) = (a + m) % (q₀ ^ k) then h n' * Complex.ofReal ((n' : ℝ) ^ (-s₀)) else 0‖
        ≤ ∑ n' ∈ Ico 1 (N₀ + m),
            ‖if n' % (q₀ ^ k) = (a + m) % (q₀ ^ k) then h n' * Complex.ofReal ((n' : ℝ) ^ (-s₀)) else 0‖ :=
          norm_sum_le _ _
      _ = ∑ n' ∈ (Ico 1 (N₀ + m)).filter (fun n' => n' % (q₀ ^ k) = (a + m) % (q₀ ^ k)),
            (n' : ℝ) ^ (-s₀) := by
          rw [sum_filter]
          refine sum_congr rfl fun n' hn' => ?_
          split_ifs
          · rw [norm_mul, hh_norm n' (mem_Ico.mp hn').1, one_mul, Complex.norm_real,
              Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
          · simp
      _ ≤ 1 + (1 / ((q₀ ^ k : ℕ) : ℝ)) * (Real.log ((N₀ + 2 * H : ℕ) : ℝ) + 1) := by
          let S_all := (Ico 1 (N₀ + m)).filter (fun n' => n' % (q₀ ^ k) = (a + m) % (q₀ ^ k))
          let S_lo := S_all.filter (fun n' => n' ≤ q₀ ^ k)
          let S_hi := S_all.filter (fun n' => ¬ n' ≤ q₀ ^ k)
          have hpart_S : ∑ n' ∈ S_all, (n' : ℝ) ^ (-s₀) =
              (∑ n' ∈ S_lo, (n' : ℝ) ^ (-s₀)) + ∑ n' ∈ S_hi, (n' : ℝ) ^ (-s₀) :=
            (sum_filter_add_sum_filter_not S_all (fun n' => n' ≤ q₀ ^ k) _).symm
          rw [hpart_S]
          have hlo : ∑ n' ∈ S_lo, (n' : ℝ) ^ (-s₀) ≤ 1 := by
            have hcard : S_lo.card ≤ 1 := by
              refine card_le_one.mpr fun x hx y hy => ?_
              have hx1 : 1 ≤ x := (mem_Ico.mp (mem_filter.mp (mem_filter.mp hx).1).1).1
              have hx2 : x ≤ q₀ ^ k := (mem_filter.mp hx).2
              have hxm : x % (q₀ ^ k) = (a + m) % (q₀ ^ k) := (mem_filter.mp (mem_filter.mp hx).1).2
              have hy1 : 1 ≤ y := (mem_Ico.mp (mem_filter.mp (mem_filter.mp hy).1).1).1
              have hy2 : y ≤ q₀ ^ k := (mem_filter.mp hy).2
              have hym : y % (q₀ ^ k) = (a + m) % (q₀ ^ k) := (mem_filter.mp (mem_filter.mp hy).1).2
              have hdivx : x / (q₀ ^ k) = if x = q₀ ^ k then 1 else 0 := by
                split_ifs with h
                · rw [h, Nat.div_self hqk_pos]
                · exact Nat.div_eq_of_lt (by omega)
              have hdivy : y / (q₀ ^ k) = if y = q₀ ^ k then 1 else 0 := by
                split_ifs with h
                · rw [h, Nat.div_self hqk_pos]
                · exact Nat.div_eq_of_lt (by omega)
              have heqm : x % (q₀ ^ k) = y % (q₀ ^ k) := hxm.trans hym.symm
              by_cases hxEq : x = q₀ ^ k <;> by_cases hyEq : y = q₀ ^ k
              · omega
              · rw [hxEq, Nat.mod_self] at heqm
                have : y % (q₀ ^ k) = y := Nat.mod_eq_of_lt (by omega)
                omega
              · rw [hyEq, Nat.mod_self] at heqm
                have : x % (q₀ ^ k) = x := Nat.mod_eq_of_lt (by omega)
                omega
              · have hxmod : x % (q₀ ^ k) = x := Nat.mod_eq_of_lt (by omega)
                have hymod : y % (q₀ ^ k) = y := Nat.mod_eq_of_lt (by omega)
                omega
            calc ∑ n' ∈ S_lo, (n' : ℝ) ^ (-s₀)
                ≤ ∑ _n' ∈ S_lo, (1 : ℝ) := sum_le_sum fun n' hn' => by
                  have h1 : (1 : ℝ) ≤ (n' : ℝ) := by
                    exact_mod_cast (mem_Ico.mp (mem_filter.mp (mem_filter.mp hn').1).1).1
                  exact (Real.rpow_le_rpow_of_exponent_le h1 (by linarith : -s₀ ≤ 0)).trans_eq (Real.rpow_zero _)
              _ = (S_lo.card : ℝ) := by simp
              _ ≤ 1 := by exact_mod_cast hcard
          have hhi : ∑ n' ∈ S_hi, (n' : ℝ) ^ (-s₀) ≤
              (1 / ((q₀ ^ k : ℕ) : ℝ)) * (Real.log ((N₀ + 2 * H : ℕ) : ℝ) + 1) := by
            let phi : ℕ → ℕ := fun n' => (n' - 1) / (q₀ ^ k)
            have hmaps : ∀ n' ∈ S_hi, phi n' ∈ Icc 1 (N₀ + 2 * H) := by
              intro n' hn'
              have hlt : n' < N₀ + m := (mem_Ico.mp (mem_filter.mp (mem_filter.mp hn').1).1).2
              have hgt : q₀ ^ k < n' := by have := (mem_filter.mp hn').2; omega
              refine mem_Icc.mpr ⟨?_, ?_⟩
              · exact Nat.div_pos (by omega) hqk_pos
              · exact (Nat.div_le_self _ _).trans (by omega)
            have hinj : Set.InjOn phi S_hi := by
              intro x hx y hy hxy
              have hx1 : 1 ≤ x := (mem_Ico.mp (mem_filter.mp (mem_filter.mp hx).1).1).1
              have hy1 : 1 ≤ y := (mem_Ico.mp (mem_filter.mp (mem_filter.mp hy).1).1).1
              have hxm : x % (q₀ ^ k) = (a + m) % (q₀ ^ k) := (mem_filter.mp (mem_filter.mp hx).1).2
              have hym : y % (q₀ ^ k) = (a + m) % (q₀ ^ k) := (mem_filter.mp (mem_filter.mp hy).1).2
              have hmod1 : (x - 1) % (q₀ ^ k) = (y - 1) % (q₀ ^ k) := by
                rw [← ZMod.natCast_eq_natCast_iff'] at hxm hym ⊢
                have hx' : ((x - 1 : ℕ) : ZMod (q₀ ^ k)) + 1 = (x : ZMod (q₀ ^ k)) := by
                  have := congrArg (fun z : ℕ => (z : ZMod (q₀ ^ k))) (Nat.sub_add_cancel hx1)
                  simpa [Nat.cast_add] using this
                have hy' : ((y - 1 : ℕ) : ZMod (q₀ ^ k)) + 1 = (y : ZMod (q₀ ^ k)) := by
                  have := congrArg (fun z : ℕ => (z : ZMod (q₀ ^ k))) (Nat.sub_add_cancel hy1)
                  simpa [Nat.cast_add] using this
                have : ((x - 1 : ℕ) : ZMod (q₀ ^ k)) + 1 = ((y - 1 : ℕ) : ZMod (q₀ ^ k)) + 1 := by
                  rw [hx', hy', hxm, hym]
                exact add_right_cancel this
              have hsub_eq : x - 1 = y - 1 := by
                have h1 := Nat.div_add_mod (x - 1) (q₀ ^ k)
                have h2 := Nat.div_add_mod (y - 1) (q₀ ^ k)
                dsimp [phi] at hxy
                rw [hxy, hmod1] at h1; omega
              omega
            have hle_j : ∑ n' ∈ S_hi, (n' : ℝ) ^ (-s₀) ≤
                ∑ n' ∈ S_hi, (1 / ((q₀ ^ k : ℕ) : ℝ)) * (1 / ((phi n' : ℕ) : ℝ)) := by
              refine sum_le_sum fun n' hn' => ?_
              have hgt : q₀ ^ k < n' := by have := (mem_filter.mp hn').2; omega
              have hphi_pos : 1 ≤ phi n' := Nat.div_pos (by omega) hqk_pos
              have hmul_le : (q₀ ^ k) * phi n' ≤ n' :=
                (Nat.mul_div_le (n' - 1) (q₀ ^ k)).trans (Nat.sub_le n' 1)
              have hpos_m : (0 : ℝ) < (((q₀ ^ k) * phi n' : ℕ) : ℝ) := by
                exact_mod_cast Nat.mul_pos hqk_pos hphi_pos
              calc (n' : ℝ) ^ (-s₀)
                  ≤ (n' : ℝ) ^ (-1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n' by omega)) (by linarith)
                _ = 1 / (n' : ℝ) := by rw [Real.rpow_neg_one, one_div]
                _ ≤ 1 / (((q₀ ^ k) * phi n' : ℕ) : ℝ) :=
                    one_div_le_one_div_of_le hpos_m (by exact_mod_cast hmul_le)
                _ = (1 / ((q₀ ^ k : ℕ) : ℝ)) * (1 / ((phi n' : ℕ) : ℝ)) := by
                    push_cast; rw [one_div_mul_one_div]
            calc ∑ n' ∈ S_hi, (n' : ℝ) ^ (-s₀)
                ≤ ∑ n' ∈ S_hi, (1 / ((q₀ ^ k : ℕ) : ℝ)) * (1 / ((phi n' : ℕ) : ℝ)) := hle_j
              _ ≤ ∑ j ∈ Icc 1 (N₀ + 2 * H), (1 / ((q₀ ^ k : ℕ) : ℝ)) * (1 / (j : ℝ)) := by
                  rw [← sum_image (f := fun j : ℕ => (1 / ((q₀ ^ k : ℕ) : ℝ)) * (1 / (j : ℝ))) hinj]
                  exact sum_le_sum_of_subset_of_nonneg
                    (image_subset_iff.mpr hmaps) (fun _ _ _ => by positivity)
              _ = (1 / ((q₀ ^ k : ℕ) : ℝ)) * ∑ j ∈ Icc 1 (N₀ + 2 * H), (1 / (j : ℝ)) := by
                  rw [← mul_sum]
              _ ≤ (1 / ((q₀ ^ k : ℕ) : ℝ)) * (Real.log ((N₀ + 2 * H : ℕ) : ℝ) + 1) := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  have hh := harmonic_sum_le_log_add_one (N₀ + 2 * H)
                  have hmax : max (1 : ℝ) ((N₀ + 2 * H : ℕ) : ℝ) = ((N₀ + 2 * H : ℕ) : ℝ) :=
                    max_eq_right (by exact_mod_cast (show 1 ≤ N₀ + 2 * H by omega))
                  rw [hmax] at hh
                  exact hh
          linarith
  let d : ℕ := Nat.gcd (a + m) (q₀ ^ k)
  let M : ℕ := q₀ ^ k / d
  let b : ℕ := (a + m) / d
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left _ (by omega)
  have hd_dvd_am : d ∣ a + m := Nat.gcd_dvd_left _ _
  have hd_dvd_qk : d ∣ q₀ ^ k := Nat.gcd_dvd_right _ _
  have hd_dvd_qk1 : d ∣ q₀ ^ (k - 1) := by
    rw [← Nat.factorization_le_iff_dvd hd_pos.ne' (pow_pos hq0_pos _).ne']
    intro p
    by_cases hp : p.Prime
    · by_cases hpd : p ∣ q₀
      · have hnot : ¬ p ^ k ∣ a + m := hgood p hp hpd m hm
        have hlt : (a + m).factorization p < k := by
          by_contra hge; push Not at hge
          exact hnot ((pow_dvd_pow p hge).trans (Nat.ordProj_dvd (a + m) p))
        have hd_le_am : d.factorization p ≤ (a + m).factorization p :=
          (Nat.factorization_le_iff_dvd hd_pos.ne' (by omega)).mpr hd_dvd_am p
        have hq_vp : 1 ≤ q₀.factorization p := Nat.Prime.factorization_pos_of_dvd hp hq0_pos.ne' hpd
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        exact (show d.factorization p ≤ k - 1 by omega).trans (Nat.le_mul_of_pos_right _ hq_vp)
      · have hnd : ¬ p ∣ d := fun h => hpd (hp.dvd_of_dvd_pow (h.trans hd_dvd_qk))
        rw [Nat.factorization_eq_zero_of_not_dvd hnd]; exact Nat.zero_le _
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hdM : d * M = q₀ ^ k := Nat.mul_div_cancel' hd_dvd_qk
  have hM_pos : 0 < M := Nat.div_pos (Nat.le_of_dvd hqk_pos hd_dvd_qk) hd_pos
  haveI : NeZero M := ⟨hM_pos.ne'⟩
  have hq0_dvd_M : q₀ ∣ M := by
    rcases hd_dvd_qk1 with ⟨r, hr⟩
    have hpow : q₀ ^ k = q₀ ^ (k - 1) * q₀ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    have hmul : d * M = d * (r * q₀) := by rw [hdM, hpow, hr]; ring
    have hMeq : M = r * q₀ := Nat.eq_of_mul_eq_mul_left hd_pos hmul
    exact ⟨r, by rw [hMeq, mul_comm]⟩
  have hM_dvd_qk : M ∣ q₀ ^ k := ⟨d, by rw [← hdM, mul_comm]⟩
  have hcop_eq : ∀ n : ℕ, Nat.Coprime n M ↔ Nat.Coprime n q₀ := by
    intro n
    constructor
    · exact fun hc => hc.coprime_dvd_right hq0_dvd_M
    · intro hc
      have hpow : Nat.Coprime n (q₀ ^ k) := hc.pow_right k
      exact hpow.coprime_dvd_right hM_dvd_qk
  have hb_cop : Nat.Coprime b q₀ := by
    have h1 : Nat.Coprime b M := Nat.coprime_div_gcd_div_gcd hd_pos
    exact (hcop_eq b).mp h1
  have hdb : d * b = a + m := Nat.mul_div_cancel' hd_dvd_am
  have hhd_eq1 : h d = 1 := by
    have hprime_dvd : ∀ p : ℕ, p.Prime → p ∣ d → p ∣ q₀ :=
      fun p hp hpd => hp.dvd_of_dvd_pow (hpd.trans hd_dvd_qk)
    have h1 : ∀ n : ℕ, 1 ≤ n → (∀ p : ℕ, p.Prime → p ∣ n → p ∣ q₀) → h n = 1 := by
      intro n
      induction n using Nat.strongRecOn with
      | ind n ih =>
        intro hn1 hfn
        by_cases h1 : n = 1
        · subst h1; exact map_one h
        · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
          rcases hpn with ⟨n', rfl⟩
          have hn'1 : 1 ≤ n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn1)
          have hn'lt : n' < p * n' := lt_mul_of_one_lt_left (by omega) hp.one_lt
          rw [map_mul, hh_q0 p hp (hfn p hp (dvd_mul_right p n')), one_mul]
          exact ih n' hn'lt hn'1 (fun q hq hqn' => hfn q hq (dvd_mul_of_dvd_right hqn' p))
    exact h1 d hd_pos hprime_dvd
  let S_ap : ℂ := ∑' u : ℕ, if 1 ≤ u ∧ u % M = b % M then h u * Complex.ofReal ((u : ℝ) ^ (-s₀)) else 0
  have hT3_eq : T3 = Complex.ofReal ((d : ℝ) ^ (-s₀)) * S_ap := by
    rw [← tsum_mul_left]
    refine tsum_eq_tsum_of_ne_zero_bij
      (f := fun n' : ℕ => if 1 ≤ n' ∧ n' % (q₀ ^ k) = (a + m) % (q₀ ^ k) then h n' * Complex.ofReal ((n' : ℝ) ^ (-s₀)) else 0)
      (g := fun u : ℕ => Complex.ofReal ((d : ℝ) ^ (-s₀)) * (if 1 ≤ u ∧ u % M = b % M then h u * Complex.ofReal ((u : ℝ) ^ (-s₀)) else 0))
      (i := fun x => d * x.1)
      (fun x y hxy => Subtype.ext (Nat.eq_of_mul_eq_mul_left hd_pos hxy))
      (fun n' hn' => ?_) (fun x => ?_)
    · have hcond : 1 ≤ n' ∧ n' % (q₀ ^ k) = (a + m) % (q₀ ^ k) := by
        by_contra hc; exact hn' (by simp [hc])
      have hd_dvd_n' : d ∣ n' := by
        have h1 : n' % d = (a + m) % d := by
          have := congrArg (fun z => z % d) hcond.2
          rwa [Nat.mod_mod_of_dvd n' hd_dvd_qk, Nat.mod_mod_of_dvd (a + m) hd_dvd_qk] at this
        rw [Nat.dvd_iff_mod_eq_zero, h1, ← Nat.dvd_iff_mod_eq_zero]
        exact hd_dvd_am
      let u := n' / d
      have hdu : d * u = n' := Nat.mul_div_cancel' hd_dvd_n'
      have hu1 : 1 ≤ u := Nat.div_pos (Nat.le_of_dvd (by omega) hd_dvd_n') hd_pos
      have humod : u % M = b % M := by
        have h1 : (d * u) % (d * M) = (d * b) % (d * M) := by rw [hdu, hdb, hdM]; exact hcond.2
        rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at h1
        exact Nat.eq_of_mul_eq_mul_left hd_pos h1
      have hne_u : Complex.ofReal ((d : ℝ) ^ (-s₀)) * (if 1 ≤ u ∧ u % M = b % M then h u * Complex.ofReal ((u : ℝ) ^ (-s₀)) else 0) ≠ 0 := by
        rw [if_pos ⟨hu1, humod⟩]
        have hmul : Complex.ofReal ((d : ℝ) ^ (-s₀)) * (h u * Complex.ofReal ((u : ℝ) ^ (-s₀))) = h n' * Complex.ofReal ((n' : ℝ) ^ (-s₀)) := by
          rw [← hdu, map_mul, hhd_eq1, one_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg u)]
          push_cast; ring
        rw [hmul]
        simpa [hcond] using hn'
      exact ⟨⟨u, hne_u⟩, hdu⟩
    · have hcond : 1 ≤ x.1 ∧ x.1 % M = b % M := by
        by_contra hc; exact x.2 (by simp [hc])
      have hdx1 : 1 ≤ d * x.1 := Nat.mul_pos hd_pos hcond.1
      have hdxmod : (d * x.1) % (q₀ ^ k) = (a + m) % (q₀ ^ k) := by
        have h1 : (d * x.1) % (d * M) = (d * b) % (d * M) := by
          rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, hcond.2]
        rwa [hdM, hdb] at h1
      rw [if_pos ⟨hdx1, hdxmod⟩, if_pos ⟨hcond.1, hcond.2⟩, map_mul, hhd_eq1, one_mul,
        Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg x.1)]
      push_cast; ring
  have hequi := equidist_h_coprime_ap hcop_eq hb_cop hQ hX100 hh_norm hh_dist
  have htot_eq : d * M.totient = (q₀ ^ k).totient := by
    rw [← hdM]
    exact (totient_mul_eq_mul_totient_of_prime_dvd d M hd_pos
      (fun p hp hpd => (hp.dvd_of_dvd_pow (hpd.trans hd_dvd_qk)).trans hq0_dvd_M)).symm
  have hstepC : ‖T3 - Complex.ofReal ((d : ℝ) ^ (-s₀)) * ((1 / (M.totient : ℝ) : ℂ) * L₀)‖ ≤
      ((q₀ ^ k : ℕ) : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) := by
    rw [hT3_eq, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    have hd_rpow1 : (d : ℝ) ^ (-s₀) ≤ 1 :=
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hd_pos) (by linarith : -s₀ ≤ 0)).trans_eq (Real.rpow_zero _)
    have hM_le_qk : (M : ℝ) ≤ ((q₀ ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.le_of_dvd hqk_pos hM_dvd_qk
    calc (d : ℝ) ^ (-s₀) * ‖S_ap - (1 / (M.totient : ℝ) : ℂ) * L₀‖
        ≤ 1 * ((M : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ)) :=
          mul_le_mul hd_rpow1 hequi (norm_nonneg _) zero_le_one
      _ = (M : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) := one_mul _
      _ ≤ ((q₀ ^ k : ℕ) : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) := by
          gcongr
  have hstepD : ‖Complex.ofReal ((d : ℝ) ^ (-s₀)) * ((1 / (M.totient : ℝ) : ℂ) * L₀) -
      (1 / ((q₀ ^ k).totient : ℝ) : ℂ) * L₀‖ ≤ 2 * Real.log ((q₀ ^ k : ℕ) : ℝ) := by
    have hphi_qk_pos : (0 : ℝ) < ((q₀ ^ k).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hqk_pos
    have hphi_M_pos : (0 : ℝ) < (M.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hM_pos
    have hd_posR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
    have hcoeff : (d : ℝ) ^ (-s₀) * (1 / (M.totient : ℝ)) - 1 / ((q₀ ^ k).totient : ℝ) =
        (((d : ℝ) ^ (-(1 / Real.log (X : ℝ))) - 1) / ((q₀ ^ k).totient : ℝ)) := by
      have htotR : (d : ℝ) * (M.totient : ℝ) = ((q₀ ^ k).totient : ℝ) := by exact_mod_cast htot_eq
      have hrpow_split : (d : ℝ) ^ (-s₀) = (d : ℝ) ^ (-1 : ℝ) * (d : ℝ) ^ (-(1 / Real.log (X : ℝ))) := by
        rw [← Real.rpow_add hd_posR]; congr 1; simp only [s₀]; ring
      rw [hrpow_split, Real.rpow_neg_one, ← htotR]
      field_simp [hd_posR.ne', hphi_M_pos.ne']
    have hfac : Complex.ofReal ((d : ℝ) ^ (-s₀)) * ((1 / (M.totient : ℝ) : ℂ) * L₀) -
        (1 / ((q₀ ^ k).totient : ℝ) : ℂ) * L₀ =
        ((((d : ℝ) ^ (-(1 / Real.log (X : ℝ))) - 1) / ((q₀ ^ k).totient : ℝ) : ℝ) : ℂ) * L₀ := by
      rw [← hcoeff]; push_cast; ring
    rw [hfac, norm_mul, Complex.norm_real]
    have hL0_up : ‖L₀‖ ≤ 2 * Real.log (X : ℝ) := (L0_norm_bounds hQ hq0Q hX100 hh_norm hh_dist).2
    have h1_sub_exp : |(d : ℝ) ^ (-(1 / Real.log (X : ℝ))) - 1| ≤ Real.log ((q₀ ^ k : ℕ) : ℝ) / Real.log (X : ℝ) := by
      rw [Real.rpow_def_of_pos hd_posR]
      have harg_le0 : Real.log (d : ℝ) * -(1 / Real.log (X : ℝ)) ≤ 0 := by
        have hld : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd_pos)
        have : -(1 / Real.log (X : ℝ)) ≤ 0 := by
          have : 0 < 1 / Real.log (X : ℝ) := by positivity
          linarith
        exact mul_nonpos_of_nonneg_of_nonpos hld this
      have hexp_le1 : Real.exp (Real.log (d : ℝ) * -(1 / Real.log (X : ℝ))) ≤ 1 :=
        Real.exp_le_one_iff.mpr harg_le0
      have hexp_ge : 1 + Real.log (d : ℝ) * -(1 / Real.log (X : ℝ)) ≤
          Real.exp (Real.log (d : ℝ) * -(1 / Real.log (X : ℝ))) := by
        linarith [Real.add_one_le_exp (Real.log (d : ℝ) * -(1 / Real.log (X : ℝ)))]
      rw [abs_of_nonpos (by linarith)]
      have hld_le : Real.log (d : ℝ) ≤ Real.log ((q₀ ^ k : ℕ) : ℝ) :=
        Real.log_le_log hd_posR (by exact_mod_cast Nat.le_of_dvd hqk_pos hd_dvd_qk)
      have hmul_div : Real.log (d : ℝ) * -(1 / Real.log (X : ℝ)) = -(Real.log (d : ℝ) / Real.log (X : ℝ)) := by ring
      calc -(Real.exp (Real.log (d : ℝ) * -(1 / Real.log (X : ℝ))) - 1)
          ≤ Real.log (d : ℝ) / Real.log (X : ℝ) := by linarith
        _ ≤ Real.log ((q₀ ^ k : ℕ) : ℝ) / Real.log (X : ℝ) :=
            div_le_div_of_nonneg_right hld_le hlogX_pos.le
    have hphi_ge1 : (1 : ℝ) ≤ ((q₀ ^ k).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hqk_pos
    calc ‖((d : ℝ) ^ (-(1 / Real.log (X : ℝ))) - 1) / ((q₀ ^ k).totient : ℝ)‖ * ‖L₀‖
        = (|(d : ℝ) ^ (-(1 / Real.log (X : ℝ))) - 1| / ((q₀ ^ k).totient : ℝ)) * ‖L₀‖ := by
          rw [Real.norm_eq_abs, abs_div, abs_of_pos hphi_qk_pos]
      _ ≤ (Real.log ((q₀ ^ k : ℕ) : ℝ) / Real.log (X : ℝ) / 1) * (2 * Real.log (X : ℝ)) := by
          refine mul_le_mul (div_le_div₀ (by positivity) h1_sub_exp zero_lt_one hphi_ge1)
            hL0_up (norm_nonneg _) (by positivity)
      _ = 2 * Real.log ((q₀ ^ k : ℕ) : ℝ) := by field_simp [hlogX_pos.ne']
  have htri : T1 - (1 / ((q₀ ^ k).totient : ℝ) : ℂ) * L₀ =
      (T1 - T2) + (T2 - T3) + (T3 - Complex.ofReal ((d : ℝ) ^ (-s₀)) * ((1 / (M.totient : ℝ) : ℂ) * L₀)) +
      (Complex.ofReal ((d : ℝ) ^ (-s₀)) * ((1 / (M.totient : ℝ) : ℂ) * L₀) - (1 / ((q₀ ^ k).totient : ℝ) : ℂ) * L₀) := by ring
  rw [htri]
  have h1 := norm_add_le ((T1 - T2) + (T2 - T3) + (T3 - Complex.ofReal ((d : ℝ) ^ (-s₀)) * ((1 / (M.totient : ℝ) : ℂ) * L₀)))
    (Complex.ofReal ((d : ℝ) ^ (-s₀)) * ((1 / (M.totient : ℝ) : ℂ) * L₀) - (1 / ((q₀ ^ k).totient : ℝ) : ℂ) * L₀)
  have h2 := norm_add_le ((T1 - T2) + (T2 - T3))
    (T3 - Complex.ofReal ((d : ℝ) ^ (-s₀)) * ((1 / (M.totient : ℝ) : ℂ) * L₀))
  have h3 := norm_add_le (T1 - T2) (T2 - T3)
  linarith
lemma tsum_cauchy_schwarz_ap (P : ℕ → Prop) [DecidablePred P] (a : ℕ → ℂ) {s₀ : ℝ} (_hs0 : 1 < s₀)
    (hsum_w : Summable (fun n : ℕ => if P n then (n : ℝ) ^ (-s₀) else 0))
    (hsum_a2 : Summable (fun n : ℕ => if P n then ‖a n‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0))
    (hsum_aw : Summable (fun n : ℕ => if P n then a n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0)) :
    ‖∑' n : ℕ, if P n then a n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0‖ ^ 2 ≤
      (∑' n : ℕ, if P n then (n : ℝ) ^ (-s₀) else 0) *
      (∑' n : ℕ, if P n then ‖a n‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0) := by
  have hpart : ∀ N : ℕ,
      ‖∑ n ∈ Finset.range N, if P n then a n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0‖ ^ 2 ≤
        (∑ n ∈ Finset.range N, if P n then (n : ℝ) ^ (-s₀) else 0) *
        (∑ n ∈ Finset.range N, if P n then ‖a n‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0) := by
    intro N
    have htri : ‖∑ n ∈ Finset.range N, if P n then a n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0‖ ≤
        ∑ n ∈ Finset.range N,
          (if P n then Real.sqrt ((n : ℝ) ^ (-s₀)) else 0) *
          (if P n then ‖a n‖ * Real.sqrt ((n : ℝ) ^ (-s₀)) else 0) := by
      calc ‖∑ n ∈ Finset.range N, if P n then a n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0‖
          ≤ ∑ n ∈ Finset.range N, ‖if P n then a n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0‖ := norm_sum_le _ _
        _ = ∑ n ∈ Finset.range N,
              (if P n then Real.sqrt ((n : ℝ) ^ (-s₀)) else 0) *
              (if P n then ‖a n‖ * Real.sqrt ((n : ℝ) ^ (-s₀)) else 0) := by
            refine sum_congr rfl fun n _ => ?_
            split_ifs
            · rw [norm_mul, Complex.norm_real,
                Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
              have hsq : Real.sqrt ((n : ℝ) ^ (-s₀)) * Real.sqrt ((n : ℝ) ^ (-s₀)) = (n : ℝ) ^ (-s₀) :=
                Real.mul_self_sqrt (Real.rpow_nonneg (Nat.cast_nonneg _) _)
              calc ‖a n‖ * (n : ℝ) ^ (-s₀)
                  = ‖a n‖ * (Real.sqrt ((n : ℝ) ^ (-s₀)) * Real.sqrt ((n : ℝ) ^ (-s₀))) := by rw [hsq]
                _ = Real.sqrt ((n : ℝ) ^ (-s₀)) * (‖a n‖ * Real.sqrt ((n : ℝ) ^ (-s₀))) := by ring
            · simp
    calc ‖∑ n ∈ Finset.range N, if P n then a n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0‖ ^ 2
        ≤ (∑ n ∈ Finset.range N,
            (if P n then Real.sqrt ((n : ℝ) ^ (-s₀)) else 0) *
            (if P n then ‖a n‖ * Real.sqrt ((n : ℝ) ^ (-s₀)) else 0)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ (∑ n ∈ Finset.range N, (if P n then Real.sqrt ((n : ℝ) ^ (-s₀)) else 0) ^ 2) *
          (∑ n ∈ Finset.range N, (if P n then ‖a n‖ * Real.sqrt ((n : ℝ) ^ (-s₀)) else 0) ^ 2) :=
          sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ n ∈ Finset.range N, if P n then (n : ℝ) ^ (-s₀) else 0) *
          (∑ n ∈ Finset.range N, if P n then ‖a n‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0) := by
          congr 1 <;> refine sum_congr rfl fun n _ => ?_
          · split_ifs
            · exact Real.sq_sqrt (Real.rpow_nonneg (Nat.cast_nonneg _) _)
            · simp
          · split_ifs
            · rw [mul_pow, Real.sq_sqrt (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
            · simp
  have ht1 : Tendsto (fun N : ℕ => ‖∑ n ∈ Finset.range N, if P n then a n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0‖ ^ 2)
      atTop (𝓝 (‖∑' n : ℕ, if P n then a n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0‖ ^ 2)) :=
    (hsum_aw.hasSum.tendsto_sum_nat.norm).pow 2
  have ht2 : Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.range N, if P n then (n : ℝ) ^ (-s₀) else 0) *
        (∑ n ∈ Finset.range N, if P n then ‖a n‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0))
      atTop (𝓝 ((∑' n : ℕ, if P n then (n : ℝ) ^ (-s₀) else 0) *
        (∑' n : ℕ, if P n then ‖a n‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0))) :=
    hsum_w.hasSum.tendsto_sum_nat.mul hsum_a2.hasSum.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto ht1 ht2 (Eventually.of_forall hpart)
lemma norm_exp_I_mul_sub_one_le (θ : ℝ) :
    ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ ≤ |θ| := by
  have h1 : Complex.exp (Complex.I * (θ : ℂ)) - 1 =
      Complex.exp ((θ : ℂ) * Complex.I) - 1 := by congr 2; ring
  rw [h1, Complex.exp_mul_I]
  have hnorm : ‖Complex.cos θ + Complex.sin θ * Complex.I - 1‖ ^ 2 =
      (Real.cos θ - 1) ^ 2 + (Real.sin θ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.cos_ofReal_re,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.cos_ofReal_im, Complex.one_im]
    ring
  have htrig : (Real.cos θ - 1) ^ 2 + (Real.sin θ) ^ 2 = 4 * (Real.sin (θ / 2)) ^ 2 := by
    have hsc := Real.sin_sq_add_cos_sq (θ / 2)
    have hcos : Real.cos θ = 1 - 2 * (Real.sin (θ / 2)) ^ 2 := by
      have := Real.cos_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at this; nlinarith
    have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
      have := Real.sin_two_mul (θ / 2)
      rw [show 2 * (θ / 2) = θ by ring] at this; exact this
    rw [hcos, hsin]; nlinarith
  have hsin_le : |Real.sin (θ / 2)| ≤ |θ / 2| := Real.abs_sin_le_abs
  have hsq2 : (Real.sin (θ / 2)) ^ 2 ≤ (θ / 2) ^ 2 := by
    rw [← sq_abs (Real.sin (θ / 2)), ← sq_abs (θ / 2)]
    exact pow_le_pow_left₀ (abs_nonneg _) hsin_le 2
  have hle_sq : ‖Complex.cos θ + Complex.sin θ * Complex.I - 1‖ ^ 2 ≤ |θ| ^ 2 := by
    rw [hnorm, htrig, sq_abs]; linarith
  nlinarith [norm_nonneg (Complex.cos θ + Complex.sin θ * Complex.I - 1), abs_nonneg θ]
lemma good_class_weight_bound {q₀ k X N₀ : ℕ} [NeZero q₀] (hX100 : 100 ≤ X)
    (hqk_lt_N0 : q₀ ^ k < N₀) (a : ℕ) :
    let s₀ : ℝ := 1 + 1 / Real.log (X : ℝ)
    Summable (fun n : ℕ => if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then (n : ℝ) ^ (-s₀) else 0) ∧
    (∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then (n : ℝ) ^ (-s₀) else 0) ≤
      (2 / ((q₀ ^ k : ℕ) : ℝ)) * Real.log (X : ℝ) := by
  intro s₀
  have hlogX_gt1 : 1 < Real.log (X : ℝ) := by
    have hX100R : (100 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX100
    have h1 : Real.exp 1 < (X : ℝ) := by linarith [Real.exp_one_lt_d9]
    exact (Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < X by omega))).mpr h1
  have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
  have hs0 : 1 < s₀ := by simp only [s₀]; linarith [show 0 < 1 / Real.log (X : ℝ) by positivity]
  have hqk_pos : 0 < q₀ ^ k := pow_pos (NeZero.pos q₀) k
  have hsum_rpow : Summable (fun n : ℕ => (n : ℝ) ^ (-s₀)) := by
    simpa [Real.rpow_neg (Nat.cast_nonneg _)] using (Real.summable_nat_rpow_inv.mpr hs0)
  have hsw : Summable (fun n : ℕ => if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then (n : ℝ) ^ (-s₀) else 0) :=
    hsum_rpow.of_nonneg_of_le (fun _ => by split_ifs <;> positivity)
      (fun _ => by split_ifs <;> [exact le_rfl; positivity])
  refine ⟨hsw, ?_⟩
  have hpart : ∀ N : ℕ,
      ∑ n ∈ Finset.range N, (if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then (n : ℝ) ^ (-s₀) else 0) ≤
        (1 / ((q₀ ^ k : ℕ) : ℝ)) * (1 + 1 / (s₀ - 1)) := by
    intro N
    let S := (Finset.range N).filter (fun n => N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k))
    rw [← sum_filter]
    let phi : ℕ → ℕ := fun n => (n - 1) / (q₀ ^ k)
    have hinj : Set.InjOn phi S := by
      intro x hx y hy hxy
      have hx1 : 1 ≤ x := by have := (mem_filter.mp hx).2.1; omega
      have hy1 : 1 ≤ y := by have := (mem_filter.mp hy).2.1; omega
      have hxm : x % (q₀ ^ k) = a % (q₀ ^ k) := (mem_filter.mp hx).2.2
      have hym : y % (q₀ ^ k) = a % (q₀ ^ k) := (mem_filter.mp hy).2.2
      have hmod1 : (x - 1) % (q₀ ^ k) = (y - 1) % (q₀ ^ k) := by
        rw [← ZMod.natCast_eq_natCast_iff'] at hxm hym ⊢
        have hx' : ((x - 1 : ℕ) : ZMod (q₀ ^ k)) + 1 = (x : ZMod (q₀ ^ k)) := by
          have := congrArg (fun z : ℕ => (z : ZMod (q₀ ^ k))) (Nat.sub_add_cancel hx1)
          simpa [Nat.cast_add] using this
        have hy' : ((y - 1 : ℕ) : ZMod (q₀ ^ k)) + 1 = (y : ZMod (q₀ ^ k)) := by
          have := congrArg (fun z : ℕ => (z : ZMod (q₀ ^ k))) (Nat.sub_add_cancel hy1)
          simpa [Nat.cast_add] using this
        exact add_right_cancel (by rw [hx', hy', hxm, hym])
      have h1 := Nat.div_add_mod (x - 1) (q₀ ^ k)
      have h2 := Nat.div_add_mod (y - 1) (q₀ ^ k)
      dsimp [phi] at hxy
      rw [hxy, hmod1] at h1; omega
    have hterm : ∀ n ∈ S, (n : ℝ) ^ (-s₀) ≤
        (1 / ((q₀ ^ k : ℕ) : ℝ)) * (if phi n = 0 then (0 : ℝ) else ((phi n : ℕ) : ℝ) ^ (-s₀)) := by
      intro n hn
      have hN : N₀ ≤ n := (mem_filter.mp hn).2.1
      have hgt : q₀ ^ k < n := lt_of_lt_of_le hqk_lt_N0 hN
      have hphi_pos : 1 ≤ phi n := Nat.div_pos (by omega) hqk_pos
      rw [if_neg (by omega)]
      have hmul_le : (q₀ ^ k) * phi n ≤ n :=
        (Nat.mul_div_le (n - 1) (q₀ ^ k)).trans (Nat.sub_le n 1)
      have hpos_m : (0 : ℝ) < (((q₀ ^ k) * phi n : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos hqk_pos hphi_pos
      have hqk_rpow : ((q₀ ^ k : ℕ) : ℝ) ^ (-s₀) ≤ 1 / ((q₀ ^ k : ℕ) : ℝ) := by
        rw [one_div, ← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hqk_pos) (by linarith)
      calc (n : ℝ) ^ (-s₀)
          ≤ (((q₀ ^ k) * phi n : ℕ) : ℝ) ^ (-s₀) :=
            Real.rpow_le_rpow_of_nonpos hpos_m (by exact_mod_cast hmul_le) (by linarith)
        _ = ((q₀ ^ k : ℕ) : ℝ) ^ (-s₀) * ((phi n : ℕ) : ℝ) ^ (-s₀) := by
            rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
        _ ≤ (1 / ((q₀ ^ k : ℕ) : ℝ)) * ((phi n : ℕ) : ℝ) ^ (-s₀) :=
            mul_le_mul_of_nonneg_right hqk_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hsum_R : Summable (fun j : ℕ => if j = 0 then (0 : ℝ) else (j : ℝ) ^ (-s₀)) :=
      hsum_rpow.of_nonneg_of_le (fun _ => by split_ifs <;> positivity)
        (fun _ => by split_ifs <;> [positivity; exact le_rfl])
    calc ∑ n ∈ S, (n : ℝ) ^ (-s₀)
        ≤ ∑ n ∈ S, (1 / ((q₀ ^ k : ℕ) : ℝ)) * (if phi n = 0 then (0 : ℝ) else ((phi n : ℕ) : ℝ) ^ (-s₀)) :=
          sum_le_sum hterm
      _ = (1 / ((q₀ ^ k : ℕ) : ℝ)) * ∑ n ∈ S, (if phi n = 0 then (0 : ℝ) else ((phi n : ℕ) : ℝ) ^ (-s₀)) := by
          rw [← mul_sum]
      _ = (1 / ((q₀ ^ k : ℕ) : ℝ)) * ∑ j ∈ S.image phi, (if j = 0 then (0 : ℝ) else (j : ℝ) ^ (-s₀)) := by
          congr 1; exact (sum_image (f := fun j : ℕ => if j = 0 then (0 : ℝ) else (j : ℝ) ^ (-s₀)) hinj).symm
      _ ≤ (1 / ((q₀ ^ k : ℕ) : ℝ)) * ∑' j : ℕ, (if j = 0 then (0 : ℝ) else (j : ℝ) ^ (-s₀)) :=
          mul_le_mul_of_nonneg_left (Summable.sum_le_tsum _ (fun _ _ => by split_ifs <;> positivity) hsum_R)
            (by positivity)
      _ ≤ (1 / ((q₀ ^ k : ℕ) : ℝ)) * (1 + 1 / (s₀ - 1)) :=
          mul_le_mul_of_nonneg_left (tsum_nat_rpow_neg_le hs0) (by positivity)
  have hlim := le_of_tendsto hsw.hasSum.tendsto_sum_nat (Eventually.of_forall hpart)
  have hs0_sub : 1 / (s₀ - 1) = Real.log (X : ℝ) := by
    simp only [s₀, add_sub_cancel_left, one_div_one_div]
  rw [hs0_sub] at hlim
  calc (∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then (n : ℝ) ^ (-s₀) else 0)
      ≤ (1 / ((q₀ ^ k : ℕ) : ℝ)) * (1 + Real.log (X : ℝ)) := hlim
    _ ≤ (1 / ((q₀ ^ k : ℕ) : ℝ)) * (2 * Real.log (X : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (2 / ((q₀ ^ k : ℕ) : ℝ)) * Real.log (X : ℝ) := by ring
lemma good_class_pointwise_transfer
    {q₀ k H X a H' : ℕ} [NeZero q₀] (hk : 2 ≤ k) (hH : 4 ≤ H) (hX100 : 100 ≤ X)
    {Q δ t : ℝ} (hQ : 1 ≤ Q) (hq0Q : (q₀ : ℝ) ≤ Q)
    (hδ0 : 0 < δ) (hδ_small : 6 * (H : ℝ) * δ ≤ (6 / 64 : ℝ) * Real.exp (-(3 * Q + 47)))
    (ht_bd : |t| ≤ 2 * Q * (X : ℝ) ^ δ)
    (hX_qk_lt : ((q₀ ^ k : ℕ) : ℝ) < (X : ℝ) ^ (2 * δ))
    (hX_logN0 : Real.log ((max 1 ⌈(X : ℝ) ^ (2 * δ)⌉₊ + 2 * H : ℕ) : ℝ) + 1 ≤ 3 * δ * Real.log (X : ℝ))
    (hX_err1 : (2 * (H : ℝ)) * (8 * (H : ℝ) + 1 + 2 * Real.log ((q₀ ^ k : ℕ) : ℝ)) ≤
      (1 / 16 : ℝ) * (1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ))
    (hX_err2 : (2 * (H : ℝ)) * ((q₀ ^ k : ℕ) : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) ≤
      (1 / 16 : ℝ) * (1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ))
    (hX_err3 : 16 * Q * (H : ℝ) ^ 2 * (X : ℝ) ^ (-δ) ≤ (1 / 16 : ℝ) * Real.exp (-(3 * Q + 47)))
    (χ₀ : DirichletCharacter ℂ q₀)
    (g tildeχ h : ℕ →*₀ ℂ)
    (hg_norm : ∀ n, 1 ≤ n → ‖g n‖ = 1)
    (htilde_norm : ∀ n, 1 ≤ n → ‖tildeχ n‖ = 1)
    (htilde_cop : ∀ p, p.Prime → ¬ p ∣ q₀ → tildeχ p = χ₀ (p : ZMod q₀))
    (hh_norm : ∀ n, 1 ≤ n → ‖h n‖ = 1)
    (hh_q0 : ∀ p, p.Prime → p ∣ q₀ → h p = 1)
    (hfactor : ∀ n, 1 ≤ n → g n = tildeχ n * Complex.exp (Complex.I * t * Real.log (n : ℝ)) * h n)
    (hh_dist : ∑ p ∈ (Icc 1 X).filter Nat.Prime, (1 - (h p).re) / (p : ℝ) ≤ 2 * Q)
    (ha : a ∈ goodClasses q₀ k H) (hH' : H' ∈ Ioc H (2 * H))
    (hL2_sum_H' : Summable (fun n : ℕ => if n < max 1 ⌈(X : ℝ) ^ (2 * δ)⌉₊ then (0 : ℝ) else
      ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-(1 + 1 / Real.log (X : ℝ))))) :
    let s₀ : ℝ := 1 + 1 / Real.log (X : ℝ)
    let N₀ : ℕ := max 1 ⌈(X : ℝ) ^ (2 * δ)⌉₊
    let c₀ : ℂ := (1 / ((q₀ ^ k).totient : ℝ) : ℂ) *
      ∑' n : ℕ, if n = 0 then (0 : ℂ) else if Nat.Coprime n q₀ then h n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0
    ‖∑ m ∈ Icc 1 H', tildeχ (a + m)‖ ^ 2 ≤
      2 * ((2 / ((q₀ ^ k : ℕ) : ℝ)) * Real.log (X : ℝ)) / ‖c₀‖ ^ 2 *
        (∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
          ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0) + 1 / 2 := by
  intro s₀ N₀ c₀
  have hN0_ge1 : 1 ≤ N₀ := le_max_left _ _
  have hN0_geX : (X : ℝ) ^ (2 * δ) ≤ (N₀ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈(X : ℝ) ^ (2 * δ)⌉₊)
  have hlogX_gt1 : 1 < Real.log (X : ℝ) := by
    have hX100R : (100 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX100
    have h1 : Real.exp 1 < (X : ℝ) := by linarith [Real.exp_one_lt_d9]
    exact (Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < X by omega))).mpr h1
  have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
  have hs0 : 1 < s₀ := by simp only [s₀]; linarith [show 0 < 1 / Real.log (X : ℝ) by positivity]
  have hq0_pos : 0 < q₀ := NeZero.pos q₀
  have hqk_pos : 0 < q₀ ^ k := pow_pos hq0_pos k
  have hqk_lt_N0 : q₀ ^ k < N₀ := by exact_mod_cast lt_of_lt_of_le hX_qk_lt hN0_geX
  let L₀ : ℂ := ∑' n : ℕ, if n = 0 then (0 : ℂ) else
    if Nat.Coprime n q₀ then h n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0
  have hL0_low := (L0_norm_bounds hQ hq0Q hX100 hh_norm hh_dist).1
  have hc0_low : (1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ) ≤ ‖c₀‖ := by
    have hphi_le : ((q₀ ^ k).totient : ℝ) ≤ ((q₀ ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.totient_le _
    have hphi_pos : (0 : ℝ) < ((q₀ ^ k).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hqk_pos
    have hinv_ge : 1 / ((q₀ ^ k : ℕ) : ℝ) ≤ 1 / ((q₀ ^ k).totient : ℝ) :=
      one_div_le_one_div_of_le hphi_pos hphi_le
    have hc0_norm : ‖c₀‖ = (1 / ((q₀ ^ k).totient : ℝ)) * ‖L₀‖ := by
      simp only [c₀, L₀, norm_mul, one_div, norm_inv, Complex.norm_real, Real.norm_natCast]
    rw [hc0_norm]
    calc (1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ)
        = (1 / ((q₀ ^ k : ℕ) : ℝ)) * (Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ)) := by ring
      _ ≤ (1 / ((q₀ ^ k).totient : ℝ)) * ‖L₀‖ :=
          mul_le_mul hinv_ge hL0_low (by positivity) (by positivity)
  have hc0_pos : 0 < ‖c₀‖ := lt_of_lt_of_le (by positivity) hc0_low
  have hsum_rpow : Summable (fun n : ℕ => (n : ℝ) ^ (-s₀)) := by
    simpa [Real.rpow_neg (Nat.cast_nonneg _)] using (Real.summable_nat_rpow_inv.mpr hs0)
  have hW_bd := fun a => good_class_weight_bound hX100 hqk_lt_N0 a
  have hgood : isGoodRes q₀ k H a := (mem_filter.mp ha).2
  have hH'le : H' ≤ 2 * H := (mem_Ioc.mp hH').2
  have htilde_mod : ∀ n m : ℕ, N₀ ≤ n → n % (q₀ ^ k) = a % (q₀ ^ k) → m ∈ Icc 1 H' →
      tildeχ (n + m) = tildeχ (a + m) := by
    intro n m hNn hmod hm
    have hm2H : m ∈ Icc 1 (2 * H) := mem_Icc.mpr ⟨(mem_Icc.mp hm).1, (mem_Icc.mp hm).2.trans hH'le⟩
    have hgood_n : isGoodRes q₀ k H n := by
      intro p hp hpd j hj hpk
      apply hgood p hp hpd j hj
      have hpk_dvd : p ^ k ∣ q₀ ^ k := pow_dvd_pow_of_dvd hpd k
      have h1 : (n + j) % (p ^ k) = (a + j) % (p ^ k) := by
        have := congrArg (fun z => z % (p ^ k)) (by rw [Nat.add_mod, hmod, ← Nat.add_mod] : (n + j) % (q₀ ^ k) = (a + j) % (q₀ ^ k))
        rwa [Nat.mod_mod_of_dvd (n + j) hpk_dvd, Nat.mod_mod_of_dvd (a + j) hpk_dvd] at this
      rw [Nat.dvd_iff_mod_eq_zero, ← h1, ← Nat.dvd_iff_mod_eq_zero]
      exact hpk
    have hfa := tildeChi_good_factor hk χ₀ tildeχ htilde_cop hgood hm2H
    have hfn := tildeChi_good_factor hk χ₀ tildeχ htilde_cop hgood_n hm2H
    have hmod_m : (n + m) % (q₀ ^ k) = (a + m) % (q₀ ^ k) := by
      rw [Nat.add_mod, hmod, ← Nat.add_mod]
    have hgcd_eq : Nat.gcd (n + m) (q₀ ^ k) = Nat.gcd (a + m) (q₀ ^ k) := by
      rw [Nat.gcd_comm (n + m), Nat.gcd_rec, hmod_m, ← Nat.gcd_rec, Nat.gcd_comm]
    let d := Nat.gcd (a + m) (q₀ ^ k)
    have hd_dvd_qk1 : d ∣ q₀ ^ (k - 1) := hfa.1
    have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left _ (by have := (mem_Icc.mp hm).1; omega)
    have hdiv_mod : (((n + m) / d : ℕ) : ZMod q₀) = (((a + m) / d : ℕ) : ZMod q₀) := by
      rw [ZMod.natCast_eq_natCast_iff']
      have hdq0 : d * q₀ ∣ q₀ ^ k := by
        have hpow : q₀ ^ k = q₀ ^ (k - 1) * q₀ := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
        rw [hpow]; exact mul_dvd_mul_right hd_dvd_qk1 q₀
      have hmod_dq0 : (n + m) % (d * q₀) = (a + m) % (d * q₀) := by
        have := congrArg (fun z => z % (d * q₀)) hmod_m
        rwa [Nat.mod_mod_of_dvd _ hdq0, Nat.mod_mod_of_dvd _ hdq0] at this
      have hdn : d ∣ n + m := by dsimp only [d]; rw [← hgcd_eq]; exact Nat.gcd_dvd_left (n + m) (q₀ ^ k)
      have hda : d ∣ a + m := Nat.gcd_dvd_left (a + m) (q₀ ^ k)
      have h1 : (d * ((n + m) / d)) % (d * q₀) = (d * ((a + m) / d)) % (d * q₀) := by
        rw [Nat.mul_div_cancel' hdn, Nat.mul_div_cancel' hda]; exact hmod_dq0
      rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at h1
      exact Nat.eq_of_mul_eq_mul_left hd_pos h1
    rw [hfn.2, hfa.2, hgcd_eq, hdiv_mod]
  let I_a : ℂ := ∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
    (∑ m ∈ Icc 1 H', g (n + m) * Complex.exp (-Complex.I * t * Real.log (n : ℝ))) *
      Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0
  let J_a : ℂ := ∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
    (∑ m ∈ Icc 1 H', tildeχ (a + m) * h (n + m)) * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0
  have hsum_I : Summable (fun n : ℕ => if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
      (∑ m ∈ Icc 1 H', g (n + m) * Complex.exp (-Complex.I * t * Real.log (n : ℝ))) *
        Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => (H' : ℝ) * (n : ℝ) ^ (-s₀)) (hsum_rpow.mul_left _) fun n => ?_
    split_ifs with hc
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      calc ‖∑ m ∈ Icc 1 H', g (n + m) * Complex.exp (-Complex.I * t * Real.log (n : ℝ))‖
          ≤ ∑ m ∈ Icc 1 H', ‖g (n + m) * Complex.exp (-Complex.I * t * Real.log (n : ℝ))‖ := norm_sum_le _ _
        _ = ∑ _m ∈ Icc 1 H', (1 : ℝ) := sum_congr rfl fun m hm => by
            rw [norm_mul, hg_norm (n + m) (by have := (mem_Icc.mp hm).1; omega), one_mul]
            have : -Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ) = ((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I := by
              push_cast; ring
            rw [this]; exact Complex.norm_exp_ofReal_mul_I _
        _ = (H' : ℝ) := by simp
    · simp; positivity
  have hsum_J : Summable (fun n : ℕ => if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
      (∑ m ∈ Icc 1 H', tildeχ (a + m) * h (n + m)) * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => (H' : ℝ) * (n : ℝ) ^ (-s₀)) (hsum_rpow.mul_left _) fun n => ?_
    split_ifs with hc
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      calc ‖∑ m ∈ Icc 1 H', tildeχ (a + m) * h (n + m)‖
          ≤ ∑ m ∈ Icc 1 H', ‖tildeχ (a + m) * h (n + m)‖ := norm_sum_le _ _
        _ = ∑ _m ∈ Icc 1 H', (1 : ℝ) := sum_congr rfl fun m hm => by
            have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
            rw [norm_mul, htilde_norm (a + m) (by omega), hh_norm (n + m) (by omega), one_mul]
        _ = (H' : ℝ) := by simp
    · simp; positivity
  have hIJ : ‖I_a - J_a‖ ≤ (1 / 16 : ℝ) * ‖c₀‖ := by
    have hsub : I_a - J_a = ∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
        (∑ m ∈ Icc 1 H', tildeχ (a + m) * h (n + m) *
          (Complex.exp (Complex.I * t * (Real.log ((n + m : ℕ) : ℝ) - Real.log (n : ℝ))) - 1)) *
          Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0 := by
      rw [← hsum_I.tsum_sub hsum_J]
      congr 1; ext n; split_ifs with hc
      · rw [← sub_mul, ← sum_sub_distrib]
        congr 1; refine sum_congr rfl fun m hm => ?_
        have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
        rw [hfactor (n + m) (by omega), htilde_mod n m hc.1 hc.2 hm]
        have hexp : Complex.exp (Complex.I * t * Real.log ((n + m : ℕ) : ℝ)) *
            Complex.exp (-Complex.I * t * Real.log (n : ℝ)) =
            Complex.exp (Complex.I * t * (Real.log ((n + m : ℕ) : ℝ) - Real.log (n : ℝ))) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring
        calc tildeχ (a + m) * Complex.exp (Complex.I * ↑t * ↑(Real.log ↑(n + m))) * h (n + m) *
              Complex.exp (-Complex.I * ↑t * ↑(Real.log ↑n)) - tildeχ (a + m) * h (n + m)
            = tildeχ (a + m) * h (n + m) *
                (Complex.exp (Complex.I * ↑t * ↑(Real.log ↑(n + m))) *
                  Complex.exp (-Complex.I * ↑t * ↑(Real.log ↑n)) - 1) := by ring
          _ = _ := by rw [hexp]
      · simp
    rw [hsub]
    have hpw : ∀ n : ℕ,
        ‖if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
          (∑ m ∈ Icc 1 H', tildeχ (a + m) * h (n + m) *
            (Complex.exp (Complex.I * t * (Real.log ((n + m : ℕ) : ℝ) - Real.log (n : ℝ))) - 1)) *
            Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0‖ ≤
        (8 * Q * (H : ℝ) ^ 2 * (X : ℝ) ^ (-δ)) *
          (if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then (n : ℝ) ^ (-s₀) else 0) := by
      intro n
      split_ifs with hc
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
        have hX_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
        have hinv_n : 1 / (n : ℝ) ≤ (X : ℝ) ^ (-(2 * δ)) := by
          rw [Real.rpow_neg hX_pos.le, ← one_div]
          exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hX_pos _)
            (hN0_geX.trans (by exact_mod_cast hc.1))
        calc ‖∑ m ∈ Icc 1 H', tildeχ (a + m) * h (n + m) *
              (Complex.exp (Complex.I * t * (Real.log ((n + m : ℕ) : ℝ) - Real.log (n : ℝ))) - 1)‖
            ≤ ∑ m ∈ Icc 1 H', ‖tildeχ (a + m) * h (n + m) *
                (Complex.exp (Complex.I * t * (Real.log ((n + m : ℕ) : ℝ) - Real.log (n : ℝ))) - 1)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ _m ∈ Icc 1 H', (4 * Q * (H : ℝ) * (X : ℝ) ^ (-δ)) := by
              refine sum_le_sum fun m hm => ?_
              have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
              have hm2H : m ≤ 2 * H := (mem_Icc.mp hm).2.trans hH'le
              rw [norm_mul, norm_mul, htilde_norm (a + m) (by omega), hh_norm (n + m) (by omega),
                one_mul, one_mul]
              let θ : ℝ := t * (Real.log ((n + m : ℕ) : ℝ) - Real.log (n : ℝ))
              have hexp_le : ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ ≤ |θ| := norm_exp_I_mul_sub_one_le θ
              have hcast_eq : Complex.I * (t : ℂ) * ((Real.log ((n + m : ℕ) : ℝ) : ℂ) - (Real.log (n : ℝ) : ℂ)) =
                  Complex.I * (θ : ℂ) := by simp only [θ]; push_cast; ring
              rw [hcast_eq]
              have hlog_sub : 0 ≤ Real.log ((n + m : ℕ) : ℝ) - Real.log (n : ℝ) ∧
                  Real.log ((n + m : ℕ) : ℝ) - Real.log (n : ℝ) ≤ (m : ℝ) / (n : ℝ) := by
                have hdiv : Real.log ((n + m : ℕ) : ℝ) - Real.log (n : ℝ) =
                    Real.log (((n + m : ℕ) : ℝ) / (n : ℝ)) :=
                  (Real.log_div (by positivity) hn_pos.ne').symm
                rw [hdiv]
                have hrat : ((n + m : ℕ) : ℝ) / (n : ℝ) = 1 + (m : ℝ) / (n : ℝ) := by
                  push_cast; field_simp [hn_pos.ne']
                rw [hrat]
                constructor
                · exact Real.log_nonneg (by linarith [show 0 ≤ (m : ℝ) / (n : ℝ) by positivity])
                · linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + (m : ℝ) / (n : ℝ) by positivity)]
              have hθ_bd : |θ| ≤ 4 * Q * (H : ℝ) * (X : ℝ) ^ (-δ) := by
                simp only [θ, abs_mul, abs_of_nonneg hlog_sub.1]
                have hm_le : (m : ℝ) ≤ 2 * (H : ℝ) := by exact_mod_cast hm2H
                have hpow_eq : (X : ℝ) ^ δ * (X : ℝ) ^ (-(2 * δ)) = (X : ℝ) ^ (-δ) := by
                  rw [← Real.rpow_add hX_pos]; congr 1; ring
                calc |t| * (Real.log ((n + m : ℕ) : ℝ) - Real.log (n : ℝ))
                    ≤ (2 * Q * (X : ℝ) ^ δ) * ((m : ℝ) * (1 / (n : ℝ))) := by
                      rw [mul_one_div]
                      exact mul_le_mul ht_bd hlog_sub.2 hlog_sub.1 (by positivity)
                  _ ≤ (2 * Q * (X : ℝ) ^ δ) * ((2 * (H : ℝ)) * (X : ℝ) ^ (-(2 * δ))) := by
                      gcongr
                  _ = 4 * Q * (H : ℝ) * ((X : ℝ) ^ δ * (X : ℝ) ^ (-(2 * δ))) := by ring
                  _ = 4 * Q * (H : ℝ) * (X : ℝ) ^ (-δ) := by rw [hpow_eq]
              exact hexp_le.trans hθ_bd
          _ = (H' : ℝ) * (4 * Q * (H : ℝ) * (X : ℝ) ^ (-δ)) := by simp
          _ ≤ (2 * (H : ℝ)) * (4 * Q * (H : ℝ) * (X : ℝ) ^ (-δ)) := by
              apply mul_le_mul_of_nonneg_right (by exact_mod_cast hH'le) (by positivity)
          _ = 8 * Q * (H : ℝ) ^ 2 * (X : ℝ) ^ (-δ) := by ring
      · simp
    have hsw := (hW_bd a).1
    have hsum_err : Summable (fun n : ℕ => ‖if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
        (∑ m ∈ Icc 1 H', tildeχ (a + m) * h (n + m) *
          (Complex.exp (Complex.I * t * (Real.log ((n + m : ℕ) : ℝ) - Real.log (n : ℝ))) - 1)) *
          Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0‖) :=
      (hsw.mul_left _).of_nonneg_of_le (fun _ => norm_nonneg _) hpw
    calc ‖∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
            (∑ m ∈ Icc 1 H', tildeχ (a + m) * h (n + m) *
              (Complex.exp (Complex.I * t * (Real.log ((n + m : ℕ) : ℝ) - Real.log (n : ℝ))) - 1)) *
              Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0‖
        ≤ ∑' n : ℕ, ‖if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
            (∑ m ∈ Icc 1 H', tildeχ (a + m) * h (n + m) *
              (Complex.exp (Complex.I * t * (Real.log ((n + m : ℕ) : ℝ) - Real.log (n : ℝ))) - 1)) *
              Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0‖ := norm_tsum_le_tsum_norm hsum_err
      _ ≤ ∑' n : ℕ, (8 * Q * (H : ℝ) ^ 2 * (X : ℝ) ^ (-δ)) *
            (if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then (n : ℝ) ^ (-s₀) else 0) :=
          Summable.tsum_le_tsum hpw hsum_err (hsw.mul_left _)
      _ = (8 * Q * (H : ℝ) ^ 2 * (X : ℝ) ^ (-δ)) *
            ∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then (n : ℝ) ^ (-s₀) else 0 := tsum_mul_left
      _ ≤ (8 * Q * (H : ℝ) ^ 2 * (X : ℝ) ^ (-δ)) * ((2 / ((q₀ ^ k : ℕ) : ℝ)) * Real.log (X : ℝ)) :=
          mul_le_mul_of_nonneg_left (hW_bd a).2 (by positivity)
      _ = (16 * Q * (H : ℝ) ^ 2 * (X : ℝ) ^ (-δ)) * ((1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.log (X : ℝ)) := by ring
      _ ≤ ((1 / 16 : ℝ) * Real.exp (-(3 * Q + 47))) * ((1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.log (X : ℝ)) :=
          mul_le_mul_of_nonneg_right hX_err3 (by positivity)
      _ = (1 / 16 : ℝ) * ((1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ)) := by ring
      _ ≤ (1 / 16 : ℝ) * ‖c₀‖ := mul_le_mul_of_nonneg_left hc0_low (by norm_num)
  have hJc : ‖J_a - c₀ * ∑ m ∈ Icc 1 H', tildeχ (a + m)‖ ≤ (7 / 16 : ℝ) * ‖c₀‖ := by
    have hswap : J_a = ∑ m ∈ Icc 1 H', tildeχ (a + m) *
        ∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then h (n + m) * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0 := by
      have hsm : ∀ m ∈ Icc 1 H',
          Summable (fun n : ℕ => if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
            tildeχ (a + m) * h (n + m) * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) := by
        intro m hm
        refine Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) ^ (-s₀)) hsum_rpow fun n => ?_
        split_ifs
        · have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
          rw [norm_mul, norm_mul, htilde_norm (a + m) (by omega), hh_norm (n + m) (by omega),
            one_mul, one_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
        · simp; positivity
      have h1 : J_a = ∑ m ∈ Icc 1 H', ∑' n : ℕ,
          if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
            tildeχ (a + m) * h (n + m) * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0 := by
        dsimp only [J_a]
        rw [← Summable.tsum_finsetSum hsm]
        congr 1; ext n; split_ifs
        · rw [sum_mul]
        · simp
      rw [h1]
      refine sum_congr rfl fun m _ => ?_
      rw [← tsum_mul_left]
      congr 1; ext n; split_ifs <;> ring
    rw [hswap, mul_sum, ← sum_sub_distrib]
    have hbound_m : ∀ m ∈ Icc 1 H',
        ‖tildeχ (a + m) * (∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
            h (n + m) * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) - c₀ * tildeχ (a + m)‖ ≤
          8 * (H : ℝ) +
          (1 + (1 / ((q₀ ^ k : ℕ) : ℝ)) * (Real.log ((N₀ + 2 * H : ℕ) : ℝ) + 1)) +
          ((q₀ ^ k : ℕ) : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) +
          2 * Real.log ((q₀ ^ k : ℕ) : ℝ) := by
      intro m hm
      have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
      have hm2H : m ∈ Icc 1 (2 * H) := mem_Icc.mpr ⟨hm1, (mem_Icc.mp hm).2.trans hH'le⟩
      have hfac : tildeχ (a + m) * (∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
            h (n + m) * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) - c₀ * tildeχ (a + m) =
          tildeχ (a + m) * ((∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
            h (n + m) * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) - c₀) := by ring
      rw [hfac, norm_mul, htilde_norm (a + m) (by omega), one_mul]
      exact equidist_h_good_shift hk hH hX100 hN0_ge1 hgood hm2H hQ hq0Q hh_norm hh_q0 hh_dist
    calc ‖∑ m ∈ Icc 1 H',
            (tildeχ (a + m) * (∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
              h (n + m) * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) - c₀ * tildeχ (a + m))‖
        ≤ ∑ m ∈ Icc 1 H',
            ‖tildeχ (a + m) * (∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
              h (n + m) * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0) - c₀ * tildeχ (a + m)‖ := norm_sum_le _ _
      _ ≤ (H' : ℝ) * (8 * (H : ℝ) +
            (1 + (1 / ((q₀ ^ k : ℕ) : ℝ)) * (Real.log ((N₀ + 2 * H : ℕ) : ℝ) + 1)) +
            ((q₀ ^ k : ℕ) : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) +
            2 * Real.log ((q₀ ^ k : ℕ) : ℝ)) := by
          calc ∑ m ∈ Icc 1 H', _
              ≤ ∑ _m ∈ Icc 1 H', _ := sum_le_sum hbound_m
            _ = (H' : ℝ) * _ := by rw [sum_const, Nat.card_Icc, show H' + 1 - 1 = H' by omega, nsmul_eq_mul]
      _ ≤ (2 * (H : ℝ)) * (8 * (H : ℝ) + 1 + 2 * Real.log ((q₀ ^ k : ℕ) : ℝ)) +
          (2 * (H : ℝ)) * ((1 / ((q₀ ^ k : ℕ) : ℝ)) * (3 * δ * Real.log (X : ℝ))) +
          (2 * (H : ℝ)) * (((q₀ ^ k : ℕ) : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ)) := by
          have hH'R : (H' : ℝ) ≤ 2 * (H : ℝ) := by exact_mod_cast hH'le
          have hlog_qk_nn : 0 ≤ Real.log ((q₀ ^ k : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast hqk_pos)
          have hterm_nn : 0 ≤ 8 * (H : ℝ) +
              (1 + (1 / ((q₀ ^ k : ℕ) : ℝ)) * (Real.log ((N₀ + 2 * H : ℕ) : ℝ) + 1)) +
              ((q₀ ^ k : ℕ) : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) +
              2 * Real.log ((q₀ ^ k : ℕ) : ℝ) := by
            have : 0 ≤ Real.log ((N₀ + 2 * H : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N₀ + 2 * H by omega))
            positivity
          have h1 := mul_le_mul_of_nonneg_right hH'R hterm_nn
          have h2 : (1 / ((q₀ ^ k : ℕ) : ℝ)) * (Real.log ((N₀ + 2 * H : ℕ) : ℝ) + 1) ≤
              (1 / ((q₀ ^ k : ℕ) : ℝ)) * (3 * δ * Real.log (X : ℝ)) :=
            mul_le_mul_of_nonneg_left hX_logN0 (by positivity)
          nlinarith
      _ ≤ (1 / 16 + 6 / 64 + 1 / 16 : ℝ) * ((1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ)) := by
          have hmid : (2 * (H : ℝ)) * ((1 / ((q₀ ^ k : ℕ) : ℝ)) * (3 * δ * Real.log (X : ℝ))) =
              (6 * (H : ℝ) * δ) * ((1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.log (X : ℝ)) := by ring
          have hmid2 : (6 * (H : ℝ) * δ) * ((1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.log (X : ℝ)) ≤
              ((6 / 64 : ℝ) * Real.exp (-(3 * Q + 47))) * ((1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.log (X : ℝ)) :=
            mul_le_mul_of_nonneg_right hδ_small (by positivity)
          linarith
      _ ≤ (7 / 16 : ℝ) * ‖c₀‖ := by
          have : (1 / 16 + 6 / 64 + 1 / 16 : ℝ) ≤ 7 / 16 := by norm_num
          nlinarith
  have hIc : ‖I_a - c₀ * ∑ m ∈ Icc 1 H', tildeχ (a + m)‖ ≤ (1 / 2 : ℝ) * ‖c₀‖ := by
    have : I_a - c₀ * ∑ m ∈ Icc 1 H', tildeχ (a + m) =
        (I_a - J_a) + (J_a - c₀ * ∑ m ∈ Icc 1 H', tildeχ (a + m)) := by ring
    rw [this]
    linarith [norm_add_le (I_a - J_a) (J_a - c₀ * ∑ m ∈ Icc 1 H', tildeχ (a + m))]
  have hsum_E : Summable (fun n : ℕ => if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
      ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0) := by
    refine (hL2_sum_H').of_nonneg_of_le (fun _ => by split_ifs <;> positivity) fun n => ?_
    split_ifs with h1 h2
    · omega
    · exact le_rfl
    · exact le_rfl
    · positivity
  have hnorm_a_eq : ∀ n : ℕ,
      ‖∑ m ∈ Icc 1 H', g (n + m) * Complex.exp (-Complex.I * t * Real.log (n : ℝ))‖ =
        ‖∑ m ∈ Icc 1 H', g (n + m)‖ := by
    intro n
    rw [← sum_mul, norm_mul]
    have : -Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ) = ((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hcs_I : ‖I_a‖ ^ 2 ≤ ((2 / ((q₀ ^ k : ℕ) : ℝ)) * Real.log (X : ℝ)) *
      (∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
        ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0) := by
    have h1 := tsum_cauchy_schwarz_ap (fun n => N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k))
      (fun n => ∑ m ∈ Icc 1 H', g (n + m) * Complex.exp (-Complex.I * t * Real.log (n : ℝ)))
      hs0 (hW_bd a).1 (by simpa only [hnorm_a_eq] using hsum_E) hsum_I
    simp only [hnorm_a_eq] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (hW_bd a).2 (tsum_nonneg fun _ => by split_ifs <;> positivity))
  have htri_c : ‖c₀‖ * ‖∑ m ∈ Icc 1 H', tildeχ (a + m)‖ ≤ ‖I_a‖ + (1 / 2 : ℝ) * ‖c₀‖ := by
    have h1 : c₀ * ∑ m ∈ Icc 1 H', tildeχ (a + m) =
        I_a - (I_a - c₀ * ∑ m ∈ Icc 1 H', tildeχ (a + m)) := by ring
    calc ‖c₀‖ * ‖∑ m ∈ Icc 1 H', tildeχ (a + m)‖
        = ‖c₀ * ∑ m ∈ Icc 1 H', tildeχ (a + m)‖ := (norm_mul _ _).symm
      _ ≤ ‖I_a‖ + ‖I_a - c₀ * ∑ m ∈ Icc 1 H', tildeχ (a + m)‖ := by
          have hnorm_eq : ‖c₀ * ∑ m ∈ Icc 1 H', tildeχ (a + m)‖ =
              ‖I_a - (I_a - c₀ * ∑ m ∈ Icc 1 H', tildeχ (a + m))‖ := by congr 1
          rw [hnorm_eq]; exact norm_sub_le _ _
      _ ≤ ‖I_a‖ + (1 / 2 : ℝ) * ‖c₀‖ := by linarith
  have hsq_c : ‖c₀‖ ^ 2 * ‖∑ m ∈ Icc 1 H', tildeχ (a + m)‖ ^ 2 ≤
      2 * ‖I_a‖ ^ 2 + (1 / 2 : ℝ) * ‖c₀‖ ^ 2 := by
    have h2 : (‖c₀‖ * ‖∑ m ∈ Icc 1 H', tildeχ (a + m)‖) ^ 2 ≤ (‖I_a‖ + (1 / 2 : ℝ) * ‖c₀‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) htri_c 2
    nlinarith only [h2, sq_nonneg (‖I_a‖ - (1 / 2 : ℝ) * ‖c₀‖)]
  have hdiv_c : ‖∑ m ∈ Icc 1 H', tildeχ (a + m)‖ ^ 2 ≤ 2 * ‖I_a‖ ^ 2 / ‖c₀‖ ^ 2 + 1 / 2 := by
    have hpos2 : 0 < ‖c₀‖ ^ 2 := sq_pos_of_pos hc0_pos
    rw [← mul_le_mul_iff_left₀ hpos2]
    have : ‖c₀‖ ^ 2 * (2 * ‖I_a‖ ^ 2 / ‖c₀‖ ^ 2 + 1 / 2) = 2 * ‖I_a‖ ^ 2 + (1 / 2 : ℝ) * ‖c₀‖ ^ 2 := by
      field_simp [hpos2.ne']
    linarith
  calc ‖∑ m ∈ Icc 1 H', tildeχ (a + m)‖ ^ 2
      ≤ 2 * ‖I_a‖ ^ 2 / ‖c₀‖ ^ 2 + 1 / 2 := hdiv_c
    _ ≤ 2 * (((2 / ((q₀ ^ k : ℕ) : ℝ)) * Real.log (X : ℝ)) *
          (∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
            ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0)) / ‖c₀‖ ^ 2 + 1 / 2 := by
        gcongr
    _ = 2 * ((2 / ((q₀ ^ k : ℕ) : ℝ)) * Real.log (X : ℝ)) / ‖c₀‖ ^ 2 *
          (∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
            ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0) + 1 / 2 := by ring
lemma good_class_l2_transfer
    {q₀ k H X : ℕ} [NeZero q₀] (hk : 2 ≤ k) (hH : 4 ≤ H) (hX100 : 100 ≤ X)
    {B Q δ t : ℝ} (hB0 : 0 ≤ B) (hQ : 1 ≤ Q) (hq0Q : (q₀ : ℝ) ≤ Q)
    (hδ0 : 0 < δ) (hδ_small : 6 * (H : ℝ) * δ ≤ (6 / 64 : ℝ) * Real.exp (-(3 * Q + 47)))
    (ht_bd : |t| ≤ 2 * Q * (X : ℝ) ^ δ)
    (hX_qk_lt : ((q₀ ^ k : ℕ) : ℝ) < (X : ℝ) ^ (2 * δ))
    (hX_logN0 : Real.log ((max 1 ⌈(X : ℝ) ^ (2 * δ)⌉₊ + 2 * H : ℕ) : ℝ) + 1 ≤ 3 * δ * Real.log (X : ℝ))
    (hX_err1 : (2 * (H : ℝ)) * (8 * (H : ℝ) + 1 + 2 * Real.log ((q₀ ^ k : ℕ) : ℝ)) ≤
      (1 / 16 : ℝ) * (1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ))
    (hX_err2 : (2 * (H : ℝ)) * ((q₀ ^ k : ℕ) : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) ≤
      (1 / 16 : ℝ) * (1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ))
    (hX_err3 : 16 * Q * (H : ℝ) ^ 2 * (X : ℝ) ^ (-δ) ≤ (1 / 16 : ℝ) * Real.exp (-(3 * Q + 47)))
    (χ₀ : DirichletCharacter ℂ q₀)
    (g tildeχ h : ℕ →*₀ ℂ)
    (hg_norm : ∀ n, 1 ≤ n → ‖g n‖ = 1)
    (htilde_norm : ∀ n, 1 ≤ n → ‖tildeχ n‖ = 1)
    (htilde_cop : ∀ p, p.Prime → ¬ p ∣ q₀ → tildeχ p = χ₀ (p : ZMod q₀))
    (hh_norm : ∀ n, 1 ≤ n → ‖h n‖ = 1)
    (hh_q0 : ∀ p, p.Prime → p ∣ q₀ → h p = 1)
    (hfactor : ∀ n, 1 ≤ n → g n = tildeχ n * Complex.exp (Complex.I * t * Real.log (n : ℝ)) * h n)
    (hh_dist : ∑ p ∈ (Icc 1 X).filter Nat.Prime, (1 - (h p).re) / (p : ℝ) ≤ 2 * Q)
    (hL2_sum : ∀ H' ∈ Ioc H (2 * H),
      Summable (fun n : ℕ => if n < max 1 ⌈(X : ℝ) ^ (2 * δ)⌉₊ then (0 : ℝ) else
        ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-(1 + 1 / Real.log (X : ℝ)))))
    (hL2_bd : (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
      ∑' n : ℕ, (if n < max 1 ⌈(X : ℝ) ^ (2 * δ)⌉₊ then (0 : ℝ) else
        ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-(1 + 1 / Real.log (X : ℝ)))) ≤
      16 * (B + 1) * Real.log (X : ℝ)) :
    (1 / ((q₀ ^ k : ℕ) : ℝ)) *
      ∑ a ∈ goodClasses q₀ k H,
        (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
          ‖∑ m ∈ Icc 1 H', tildeχ (a + m)‖ ^ 2 ≤
      64 * (B + 1) * Real.exp (6 * Q + 94) + 1 := by
  let s₀ : ℝ := 1 + 1 / Real.log (X : ℝ)
  let N₀ : ℕ := max 1 ⌈(X : ℝ) ^ (2 * δ)⌉₊
  have hN0_ge1 : 1 ≤ N₀ := le_max_left _ _
  have hN0_geX : (X : ℝ) ^ (2 * δ) ≤ (N₀ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈(X : ℝ) ^ (2 * δ)⌉₊)
  have hlogX_gt1 : 1 < Real.log (X : ℝ) := by
    have hX100R : (100 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX100
    have h1 : Real.exp 1 < (X : ℝ) := by linarith [Real.exp_one_lt_d9]
    exact (Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < X by omega))).mpr h1
  have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
  have hs0 : 1 < s₀ := by simp only [s₀]; linarith [show 0 < 1 / Real.log (X : ℝ) by positivity]
  have hq0_pos : 0 < q₀ := NeZero.pos q₀
  have hqk_pos : 0 < q₀ ^ k := pow_pos hq0_pos k
  have hqk_lt_N0 : q₀ ^ k < N₀ := by exact_mod_cast lt_of_lt_of_le hX_qk_lt hN0_geX
  let L₀ : ℂ := ∑' n : ℕ, if n = 0 then (0 : ℂ) else
    if Nat.Coprime n q₀ then h n * Complex.ofReal ((n : ℝ) ^ (-s₀)) else 0
  let c₀ : ℂ := (1 / ((q₀ ^ k).totient : ℝ) : ℂ) * L₀
  have hL0_low := (L0_norm_bounds hQ hq0Q hX100 hh_norm hh_dist).1
  have hc0_low : (1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ) ≤ ‖c₀‖ := by
    have hphi_le : ((q₀ ^ k).totient : ℝ) ≤ ((q₀ ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.totient_le _
    have hphi_pos : (0 : ℝ) < ((q₀ ^ k).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hqk_pos
    have hinv_ge : 1 / ((q₀ ^ k : ℕ) : ℝ) ≤ 1 / ((q₀ ^ k).totient : ℝ) :=
      one_div_le_one_div_of_le hphi_pos hphi_le
    have hc0_norm : ‖c₀‖ = (1 / ((q₀ ^ k).totient : ℝ)) * ‖L₀‖ := by
      simp only [c₀, norm_mul, one_div, norm_inv, Complex.norm_real, Real.norm_natCast]
    rw [hc0_norm]
    calc (1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ)
        = (1 / ((q₀ ^ k : ℕ) : ℝ)) * (Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ)) := by ring
      _ ≤ (1 / ((q₀ ^ k).totient : ℝ)) * ‖L₀‖ :=
          mul_le_mul hinv_ge hL0_low (by positivity) (by positivity)
  have hc0_pos : 0 < ‖c₀‖ := lt_of_lt_of_le (by positivity) hc0_low
  have hsum_rpow : Summable (fun n : ℕ => (n : ℝ) ^ (-s₀)) := by
    simpa [Real.rpow_neg (Nat.cast_nonneg _)] using (Real.summable_nat_rpow_inv.mpr hs0)
  have hW_bd := fun a => good_class_weight_bound hX100 hqk_lt_N0 a
  have hpoint : ∀ a ∈ goodClasses q₀ k H, ∀ H' ∈ Ioc H (2 * H),
      ‖∑ m ∈ Icc 1 H', tildeχ (a + m)‖ ^ 2 ≤
        2 * ((2 / ((q₀ ^ k : ℕ) : ℝ)) * Real.log (X : ℝ)) / ‖c₀‖ ^ 2 *
          (∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
            ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0) + 1 / 2 :=
    fun a ha H' hH' => good_class_pointwise_transfer hk hH hX100 hQ hq0Q hδ0 hδ_small ht_bd
      hX_qk_lt hX_logN0 hX_err1 hX_err2 hX_err3 χ₀ g tildeχ h hg_norm htilde_norm htilde_cop
      hh_norm hh_q0 hfactor hh_dist ha hH' (hL2_sum H' hH')
  have hsum_a_E : ∀ H' ∈ Ioc H (2 * H),
      ∑ a ∈ goodClasses q₀ k H,
        (∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
          ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0) ≤
      ∑' n : ℕ, (if n < N₀ then (0 : ℝ) else ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀)) := by
    intro H' hH'
    have hsm : ∀ a ∈ Icc 1 (q₀ ^ k),
        Summable (fun n : ℕ => if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
          ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0) := by
      intro a _
      refine (hL2_sum H' hH').of_nonneg_of_le (fun _ => by split_ifs <;> positivity) fun n => ?_
      split_ifs with h1 h2 <;> [omega; exact le_rfl; exact le_rfl; positivity]
    calc ∑ a ∈ goodClasses q₀ k H,
          (∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
            ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0)
        ≤ ∑ a ∈ Icc 1 (q₀ ^ k),
          (∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
            ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            fun _ _ _ => tsum_nonneg fun _ => by split_ifs <;> positivity
      _ = ∑' n : ℕ, ∑ a ∈ Icc 1 (q₀ ^ k),
            if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
              ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0 :=
          (Summable.tsum_finsetSum hsm).symm
      _ = ∑' n : ℕ, (if n < N₀ then (0 : ℝ) else ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀)) := by
          congr 1; ext n
          by_cases hlt : n < N₀
          · rw [if_pos hlt]
            exact sum_eq_zero fun a _ => by rw [if_neg (by omega)]
          · rw [if_neg hlt]
            let r : ℕ := if n % (q₀ ^ k) = 0 then q₀ ^ k else n % (q₀ ^ k)
            have hr_mem : r ∈ Icc 1 (q₀ ^ k) := by
              simp only [r]; split_ifs with hz
              · exact mem_Icc.mpr ⟨hqk_pos, le_rfl⟩
              · exact mem_Icc.mpr ⟨Nat.pos_of_ne_zero hz, (Nat.mod_lt n hqk_pos).le⟩
            have hr_mod : r % (q₀ ^ k) = n % (q₀ ^ k) := by
              simp only [r]; split_ifs with hz
              · rw [Nat.mod_self, hz]
              · exact Nat.mod_eq_of_lt (Nat.mod_lt n hqk_pos)
            rw [sum_eq_single r]
            · rw [if_pos ⟨by omega, hr_mod.symm⟩]
            · intro a ha har
              rw [if_neg]
              intro ⟨_, hmod⟩
              apply har
              have ha1 : 1 ≤ a := (mem_Icc.mp ha).1
              have ha2 : a ≤ q₀ ^ k := (mem_Icc.mp ha).2
              have heqm : a % (q₀ ^ k) = r % (q₀ ^ k) := hmod.symm.trans hr_mod.symm
              by_cases haEq : a = q₀ ^ k <;> by_cases hrEq : r = q₀ ^ k
              · omega
              · rw [haEq, Nat.mod_self] at heqm
                have hr1 : 1 ≤ r := (mem_Icc.mp hr_mem).1
                have hr2 : r ≤ q₀ ^ k := (mem_Icc.mp hr_mem).2
                have : r % (q₀ ^ k) = r := Nat.mod_eq_of_lt (by omega)
                omega
              · rw [hrEq, Nat.mod_self] at heqm
                have : a % (q₀ ^ k) = a := Nat.mod_eq_of_lt (by omega)
                omega
              · have hr1 : 1 ≤ r := (mem_Icc.mp hr_mem).1
                have hr2 : r ≤ q₀ ^ k := (mem_Icc.mp hr_mem).2
                have : a % (q₀ ^ k) = a := Nat.mod_eq_of_lt (by omega)
                have : r % (q₀ ^ k) = r := Nat.mod_eq_of_lt (by omega)
                omega
            · intro hnot; exact absurd hr_mem hnot
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hqk_posR : (0 : ℝ) < ((q₀ ^ k : ℕ) : ℝ) := by exact_mod_cast hqk_pos
  have hgood_card : ((goodClasses q₀ k H).card : ℝ) ≤ ((q₀ ^ k : ℕ) : ℝ) := by
    have h1 : (goodClasses q₀ k H).card ≤ (Icc 1 (q₀ ^ k)).card :=
      card_le_card (filter_subset _ _)
    simpa using (show ((goodClasses q₀ k H).card : ℝ) ≤ ((Icc 1 (q₀ ^ k)).card : ℝ) by exact_mod_cast h1)
  have hratio : (Real.log (X : ℝ) / ((q₀ ^ k : ℕ) : ℝ)) / ‖c₀‖ ≤ Real.exp (3 * Q + 47) := by
    rw [div_le_iff₀ hc0_pos]
    have hmul := mul_le_mul_of_nonneg_left hc0_low (Real.exp_pos (3 * Q + 47)).le
    have hexp1 : Real.exp (3 * Q + 47) * Real.exp (-(3 * Q + 47)) = 1 := by
      rw [← Real.exp_add]; simp
    have hsimp : Real.exp (3 * Q + 47) * ((1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ)) =
        Real.log (X : ℝ) / ((q₀ ^ k : ℕ) : ℝ) := by
      calc _ = (Real.exp (3 * Q + 47) * Real.exp (-(3 * Q + 47))) * (Real.log (X : ℝ) / ((q₀ ^ k : ℕ) : ℝ)) := by ring
        _ = Real.log (X : ℝ) / ((q₀ ^ k : ℕ) : ℝ) := by rw [hexp1, one_mul]
    linarith
  have hratio_sq : (Real.log (X : ℝ) / ((q₀ ^ k : ℕ) : ℝ)) ^ 2 / ‖c₀‖ ^ 2 ≤ Real.exp (6 * Q + 94) := by
    have h1 : ((Real.log (X : ℝ) / ((q₀ ^ k : ℕ) : ℝ)) / ‖c₀‖) ^ 2 ≤ (Real.exp (3 * Q + 47)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hratio 2
    rw [div_pow] at h1
    have h2 : (Real.exp (3 * Q + 47)) ^ 2 = Real.exp (6 * Q + 94) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    linarith
  calc (1 / ((q₀ ^ k : ℕ) : ℝ)) *
        ∑ a ∈ goodClasses q₀ k H,
          (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
            ‖∑ m ∈ Icc 1 H', tildeχ (a + m)‖ ^ 2
      ≤ (1 / ((q₀ ^ k : ℕ) : ℝ)) *
        ∑ a ∈ goodClasses q₀ k H,
          (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
            (2 * ((2 / ((q₀ ^ k : ℕ) : ℝ)) * Real.log (X : ℝ)) / ‖c₀‖ ^ 2 *
              (∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
                ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0) + 1 / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine sum_le_sum fun a ha => mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact sum_le_sum fun H' hH' => hpoint a ha H' hH'
    _ = (1 / ((q₀ ^ k : ℕ) : ℝ)) * (2 * ((2 / ((q₀ ^ k : ℕ) : ℝ)) * Real.log (X : ℝ)) / ‖c₀‖ ^ 2) *
          ((1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
            ∑ a ∈ goodClasses q₀ k H,
              (∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
                ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0)) +
        (1 / ((q₀ ^ k : ℕ) : ℝ)) * ((goodClasses q₀ k H).card : ℝ) * (1 / 2) := by
        have hconst : ∀ a ∈ goodClasses q₀ k H,
            (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H), (1 / 2 : ℝ) = 1 / 2 := by
          intro a _
          rw [sum_const, Nat.card_Ioc, show 2 * H - H = H by omega, nsmul_eq_mul]
          field_simp [hHpos.ne']
        simp_rw [sum_add_distrib, mul_add, sum_add_distrib]
        have hpart2 : (1 / ((q₀ ^ k : ℕ) : ℝ)) * ∑ a ∈ goodClasses q₀ k H,
            (1 / (H : ℝ)) * ∑ _H' ∈ Ioc H (2 * H), (1 / 2 : ℝ) =
            (1 / ((q₀ ^ k : ℕ) : ℝ)) * ((goodClasses q₀ k H).card : ℝ) * (1 / 2) := by
          rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul]; ring
        rw [mul_add, hpart2]
        congr 1
        simp_rw [← mul_sum]
        rw [sum_comm (s := goodClasses q₀ k H) (t := Ioc H (2 * H))]
        ring
    _ ≤ (1 / ((q₀ ^ k : ℕ) : ℝ)) * (2 * ((2 / ((q₀ ^ k : ℕ) : ℝ)) * Real.log (X : ℝ)) / ‖c₀‖ ^ 2) *
          (16 * (B + 1) * Real.log (X : ℝ)) + 1 / 2 := by
        have h1 : (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
            ∑ a ∈ goodClasses q₀ k H,
              (∑' n : ℕ, if N₀ ≤ n ∧ n % (q₀ ^ k) = a % (q₀ ^ k) then
                ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀) else 0) ≤
            16 * (B + 1) * Real.log (X : ℝ) := by
          calc _ ≤ (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
                ∑' n : ℕ, (if n < N₀ then (0 : ℝ) else ‖∑ m ∈ Icc 1 H', g (n + m)‖ ^ 2 * (n : ℝ) ^ (-s₀)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact sum_le_sum fun H' hH' => hsum_a_E H' hH'
            _ ≤ 16 * (B + 1) * Real.log (X : ℝ) := hL2_bd
        have h2 : (1 / ((q₀ ^ k : ℕ) : ℝ)) * ((goodClasses q₀ k H).card : ℝ) * (1 / 2) ≤ 1 / 2 := by
          have : (1 / ((q₀ ^ k : ℕ) : ℝ)) * ((goodClasses q₀ k H).card : ℝ) ≤ 1 := by
            rw [one_div_mul_eq_div, div_le_one hqk_posR]; exact hgood_card
          linarith
        have h3 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (1 / ((q₀ ^ k : ℕ) : ℝ)) *
          (2 * ((2 / ((q₀ ^ k : ℕ) : ℝ)) * Real.log (X : ℝ)) / ‖c₀‖ ^ 2) by positivity)
        linarith
    _ = 64 * (B + 1) * ((Real.log (X : ℝ) / ((q₀ ^ k : ℕ) : ℝ)) ^ 2 / ‖c₀‖ ^ 2) + 1 / 2 := by ring
    _ ≤ 64 * (B + 1) * Real.exp (6 * Q + 94) + 1 := by nlinarith
theorem main_H2 : OMA.R_Erdos67_erdos_67_R1.H2 := by
  intro μ B hB0 hB hpret
  obtain ⟨Q, hQ, hpretQ⟩ := hpret (1 / 8) (by norm_num)
  let C_bd : ℝ := 64 * (B + 1) * Real.exp (6 * Q + 94) + 1
  have hC_bd : 1 ≤ C_bd := by simp only [C_bd]; linarith [show 0 ≤ 64 * (B + 1) * Real.exp (6 * Q + 94) by positivity]
  let qMax : ℕ := max 1 ⌊Q⌋₊
  have hqMax_pos : 0 < qMax := by positivity
  have hgran_all : ∀ q₀ ∈ Icc 1 qMax,
      ∃ H₀ : ℕ, 4 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H → ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
        ∀ (χ₀ : DirichletCharacter ℂ q₀), χ₀.IsPrimitive →
        ∀ (tildeχ : ℕ →*₀ ℂ), (∀ n, 1 ≤ n → ‖tildeχ n‖ = 1) →
        (∀ p, p.Prime → ¬ p ∣ q₀ → tildeχ p = χ₀ (p : ZMod q₀)) →
        ¬ ((1 / ((q₀ ^ k : ℕ) : ℝ)) *
            ∑ a ∈ goodClasses q₀ k H,
              (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
                ‖∑ m ∈ Icc 1 H', tildeχ (a + m)‖ ^ 2 ≤ C_bd) := by
    intro q₀ hq₀
    haveI : NeZero q₀ := ⟨by have := (mem_Icc.mp hq₀).1; omega⟩
    exact tildeChi_contra_of_L2_bound q₀ C_bd hC_bd
  choose H0 hH0_ge4 hgran_H using hgran_all
  let H : ℕ := max 4 (∑ q₀ ∈ Icc 1 qMax, if h : q₀ ∈ Icc 1 qMax then H0 q₀ h else 0)
  have hH_ge4 : 4 ≤ H := le_max_left _ _
  have hH_ge : ∀ q₀ (hq₀ : q₀ ∈ Icc 1 qMax), H0 q₀ hq₀ ≤ H := by
    intro q₀ hq₀
    have h1 : H0 q₀ hq₀ ≤ ∑ r ∈ Icc 1 qMax, if h : r ∈ Icc 1 qMax then H0 r h else 0 := by
      have hle := single_le_sum (f := fun r => if h : r ∈ Icc 1 qMax then H0 r h else 0)
        (fun _ _ => Nat.zero_le _) hq₀
      simpa [hq₀] using hle
    exact h1.trans (le_max_right _ _)
  have hk_all : ∀ q₀ (hq₀ : q₀ ∈ Icc 1 qMax),
      ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
        ∀ (χ₀ : DirichletCharacter ℂ q₀), χ₀.IsPrimitive →
        ∀ (tildeχ : ℕ →*₀ ℂ), (∀ n, 1 ≤ n → ‖tildeχ n‖ = 1) →
        (∀ p, p.Prime → ¬ p ∣ q₀ → tildeχ p = χ₀ (p : ZMod q₀)) →
        ¬ ((1 / ((q₀ ^ k : ℕ) : ℝ)) *
            ∑ a ∈ goodClasses q₀ k H,
              (1 / (H : ℝ)) * ∑ H' ∈ Ioc H (2 * H),
                ‖∑ m ∈ Icc 1 H', tildeχ (a + m)‖ ^ 2 ≤ C_bd) :=
    fun q₀ hq₀ => hgran_H q₀ hq₀ H (hH_ge q₀ hq₀)
  choose K0 hK0_ge2 hgran_K using hk_all
  let k : ℕ := max 2 (∑ q₀ ∈ Icc 1 qMax, if h : q₀ ∈ Icc 1 qMax then K0 q₀ h else 0)
  have hk_ge2 : 2 ≤ k := le_max_left _ _
  have hk_ge : ∀ q₀ (hq₀ : q₀ ∈ Icc 1 qMax), K0 q₀ hq₀ ≤ k := by
    intro q₀ hq₀
    have h1 : K0 q₀ hq₀ ≤ ∑ r ∈ Icc 1 qMax, if h : r ∈ Icc 1 qMax then K0 r h else 0 := by
      have hle := single_le_sum (f := fun r => if h : r ∈ Icc 1 qMax then K0 r h else 0)
        (fun _ _ => Nat.zero_le _) hq₀
      simpa [hq₀] using hle
    exact h1.trans (le_max_right _ _)
  let δ : ℝ := min (1 / 2) (Real.exp (-(3 * Q + 47)) / (64 * (H : ℝ)))
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ_small : 6 * (H : ℝ) * δ ≤ (6 / 64 : ℝ) * Real.exp (-(3 * Q + 47)) := by
    have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
    have h1 : δ ≤ Real.exp (-(3 * Q + 47)) / (64 * (H : ℝ)) := min_le_right _ _
    calc 6 * (H : ℝ) * δ ≤ 6 * (H : ℝ) * (Real.exp (-(3 * Q + 47)) / (64 * (H : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (6 / 64 : ℝ) * Real.exp (-(3 * Q + 47)) := by field_simp [hHpos.ne']
  obtain ⟨X_tb, hX_tb_ge, htb⟩ := lemma_tb_deterministic Q δ hQ hδ0 hδ1
  have hX_nat_top : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hX_rpow_top : ∀ α : ℝ, 0 < α → Tendsto (fun X : ℕ => (X : ℝ) ^ α) atTop atTop :=
    fun α hα => (tendsto_rpow_atTop hα).comp hX_nat_top
  have hX_log_top : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hX_nat_top
  have hev1 : ∀ᶠ X : ℕ in atTop, X_tb ≤ (X : ℝ) :=
    (hX_nat_top.eventually (eventually_ge_atTop X_tb))
  have hev2 : ∀ᶠ X : ℕ in atTop, Q ≤ (⌊(X : ℝ) ^ δ⌋₊ : ℝ) := by
    filter_upwards [(hX_rpow_top δ hδ0).eventually (eventually_ge_atTop (Q + 1))] with X hX
    linarith [Nat.lt_floor_add_one ((X : ℝ) ^ δ)]
  have hev3 : ∀ᶠ X : ℕ in atTop, ((qMax ^ k : ℕ) : ℝ) < (X : ℝ) ^ (2 * δ) :=
    (hX_rpow_top (2 * δ) (by positivity)).eventually (eventually_gt_atTop ((qMax ^ k : ℕ) : ℝ))
  have hev4 : ∀ᶠ X : ℕ in atTop,
      Real.log ((max 1 ⌈(X : ℝ) ^ (2 * δ)⌉₊ + 2 * H : ℕ) : ℝ) + 1 ≤ 3 * δ * Real.log (X : ℝ) := by
    have hev_a : ∀ᶠ X : ℕ in atTop, (2 * H + 2 : ℝ) ≤ (X : ℝ) ^ (2 * δ) :=
      (hX_rpow_top (2 * δ) (by positivity)).eventually (eventually_ge_atTop (2 * H + 2 : ℝ))
    have hev_b : ∀ᶠ X : ℕ in atTop, Real.log 2 + 1 ≤ δ * Real.log (X : ℝ) := by
      have h1 := (hX_log_top.eventually (eventually_ge_atTop ((Real.log 2 + 1) / δ)))
      filter_upwards [h1] with X hX
      have := (div_le_iff₀ hδ0).mp hX; linarith
    have hev_c : ∀ᶠ X : ℕ in atTop, (1 : ℝ) ≤ (X : ℝ) := hX_nat_top.eventually (eventually_ge_atTop 1)
    filter_upwards [hev_a, hev_b, hev_c] with X hXa hXb hXc
    have hXpos : 0 < (X : ℝ) := by linarith
    have hceil_lt : (⌈(X : ℝ) ^ (2 * δ)⌉₊ : ℝ) ≤ (X : ℝ) ^ (2 * δ) + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have hmax_le : ((max 1 ⌈(X : ℝ) ^ (2 * δ)⌉₊ + 2 * H : ℕ) : ℝ) ≤ 2 * (X : ℝ) ^ (2 * δ) := by
      push_cast
      have h1 : max (1 : ℝ) (⌈(X : ℝ) ^ (2 * δ)⌉₊ : ℝ) ≤ (X : ℝ) ^ (2 * δ) + 1 :=
        max_le (by linarith) hceil_lt
      linarith
    have hlog_le : Real.log ((max 1 ⌈(X : ℝ) ^ (2 * δ)⌉₊ + 2 * H : ℕ) : ℝ) ≤
        Real.log (2 * (X : ℝ) ^ (2 * δ)) :=
      Real.log_le_log (by exact_mod_cast (show 0 < max 1 ⌈(X : ℝ) ^ (2 * δ)⌉₊ + 2 * H by omega)) hmax_le
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hXpos _).ne',
      Real.log_rpow hXpos] at hlog_le
    linarith
  have hev5 : ∀ᶠ X : ℕ in atTop,
      (2 * (H : ℝ)) * (8 * (H : ℝ) + 1 + 2 * Real.log ((qMax ^ k : ℕ) : ℝ)) ≤
        (1 / 16 : ℝ) * (1 / ((qMax ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ) := by
    let c1 : ℝ := (1 / 16 : ℝ) * (1 / ((qMax ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47))
    have hc1 : 0 < c1 := by positivity
    filter_upwards [hX_log_top.eventually (eventually_ge_atTop
      (((2 * (H : ℝ)) * (8 * (H : ℝ) + 1 + 2 * Real.log ((qMax ^ k : ℕ) : ℝ))) / c1))] with X hX
    exact (div_le_iff₀ hc1).mp hX |>.trans_eq (by ring)
  have hev6 : ∀ᶠ X : ℕ in atTop,
      (2 * (H : ℝ)) * ((qMax ^ k : ℕ) : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) ≤
        (1 / 16 : ℝ) * (1 / ((qMax ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ) := by
    let A : ℝ := (2 * (H : ℝ)) * ((qMax ^ k : ℕ) : ℝ) * Real.exp (640 * Q + 100)
    let c1 : ℝ := (1 / 16 : ℝ) * (1 / ((qMax ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47))
    have hc1 : 0 < c1 := by positivity
    have hpow34 : Tendsto (fun X : ℕ => (Real.log (X : ℝ)) ^ (3 / 4 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp hX_log_top
    filter_upwards [hpow34.eventually (eventually_ge_atTop (A / c1)),
      hX_log_top.eventually (eventually_gt_atTop (0 : ℝ))] with X hX hlogpos
    have hmul : A ≤ c1 * (Real.log (X : ℝ)) ^ (3 / 4 : ℝ) := by
      have := (div_le_iff₀ hc1).mp hX; linarith
    have hpow1 : (Real.log (X : ℝ)) ^ (3 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) = Real.log (X : ℝ) := by
      rw [← Real.rpow_add hlogpos]; norm_num
    calc A * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ)
        ≤ (c1 * (Real.log (X : ℝ)) ^ (3 / 4 : ℝ)) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right hmul (Real.rpow_nonneg hlogpos.le _)
      _ = c1 * ((Real.log (X : ℝ)) ^ (3 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ)) := by ring
      _ = c1 * Real.log (X : ℝ) := by rw [hpow1]
  have hev7 : ∀ᶠ X : ℕ in atTop,
      16 * Q * (H : ℝ) ^ 2 * (X : ℝ) ^ (-δ) ≤ (1 / 16 : ℝ) * Real.exp (-(3 * Q + 47)) := by
    let c2 : ℝ := (1 / 16 : ℝ) * Real.exp (-(3 * Q + 47))
    have hc2 : 0 < c2 := by positivity
    filter_upwards [(hX_rpow_top δ hδ0).eventually (eventually_ge_atTop ((16 * Q * (H : ℝ) ^ 2) / c2)),
      hX_nat_top.eventually (eventually_gt_atTop (0 : ℝ))] with X hX hXpos
    have h1 : 16 * Q * (H : ℝ) ^ 2 ≤ c2 * (X : ℝ) ^ δ := by
      have := (div_le_iff₀ hc2).mp hX; linarith
    rw [Real.rpow_neg hXpos.le, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hXpos _)]
    exact h1
  obtain ⟨X, hX1, hX2, hX3, hX4, hX5, hX6, hX7⟩ :=
    (hev1.and (hev2.and (hev3.and (hev4.and (hev5.and (hev6.and hev7)))))).exists
  have hX100 : 100 ≤ X := by
    exact_mod_cast le_trans (le_max_right Q 100) (hX_tb_ge.trans hX1)
  have hQX : Q ≤ (X : ℝ) := le_trans (le_max_left Q 100) (hX_tb_ge.trans hX1)
  obtain ⟨z₀, hL2_sum, hL2_bd, ⟨q, χ, t, hq1, hqQ, htQ, hdistX⟩,
      ⟨q', χ', t', hq'1, hq'Q, ht'Q, hdistY⟩⟩ :=
    prob_extract_good_z μ B hB0 hB Q hQ hpretQ H hH_ge4 δ hδ0 X hX100 hQX hX2
  let g : ℕ →*₀ ℂ := mulEvalHom z₀
  have hg_norm : ∀ n, 1 ≤ n → ‖g n‖ = 1 := fun n hn => mulEvalFn_norm_eq_one z₀ hn
  have ht_bd : |t| ≤ 2 * Q * (X : ℝ) ^ δ :=
    htb X hX1 (fun n => g n) (fun p hp => hg_norm p hp.one_le)
      q χ t hq1 hqQ htQ hdistX q' χ' t' hq'1 hq'Q ht'Q hdistY
  obtain ⟨q₀, hne0, χ₀, tildeχ, h, hq0_ge1, _hq0_dvd, hq0_Q, hprim,
      htilde_norm, htilde_cop, hh_norm, hh_q0, hfactor, hh_dist⟩ :=
    primitive_factorize g hg_norm q hq1 χ t Q X hqQ hdistX
  haveI := hne0
  have hq0_le_qMax : q₀ ≤ qMax := (Nat.le_floor hq0_Q).trans (le_max_right _ _)
  have hq0_mem : q₀ ∈ Icc 1 qMax := mem_Icc.mpr ⟨hq0_ge1, hq0_le_qMax⟩
  have hqk_le : ((q₀ ^ k : ℕ) : ℝ) ≤ ((qMax ^ k : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_left hq0_le_qMax k
  have hqk_pos : (0 : ℝ) < ((q₀ ^ k : ℕ) : ℝ) := by exact_mod_cast pow_pos (NeZero.pos q₀) k
  have hqMaxk_pos : (0 : ℝ) < ((qMax ^ k : ℕ) : ℝ) := by exact_mod_cast pow_pos hqMax_pos k
  have hlogX_pos : 0 < Real.log (X : ℝ) := by
    have h1 : (1 : ℝ) < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
    exact Real.log_pos h1
  have hX_err1 : (2 * (H : ℝ)) * (8 * (H : ℝ) + 1 + 2 * Real.log ((q₀ ^ k : ℕ) : ℝ)) ≤
      (1 / 16 : ℝ) * (1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ) := by
    have hlog_le : Real.log ((q₀ ^ k : ℕ) : ℝ) ≤ Real.log ((qMax ^ k : ℕ) : ℝ) :=
      Real.log_le_log hqk_pos hqk_le
    have hinv_le : 1 / ((qMax ^ k : ℕ) : ℝ) ≤ 1 / ((q₀ ^ k : ℕ) : ℝ) :=
      one_div_le_one_div_of_le hqk_pos hqk_le
    calc (2 * (H : ℝ)) * (8 * (H : ℝ) + 1 + 2 * Real.log ((q₀ ^ k : ℕ) : ℝ))
        ≤ (2 * (H : ℝ)) * (8 * (H : ℝ) + 1 + 2 * Real.log ((qMax ^ k : ℕ) : ℝ)) := by gcongr
      _ ≤ (1 / 16 : ℝ) * (1 / ((qMax ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ) := hX5
      _ ≤ (1 / 16 : ℝ) * (1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ) := by gcongr
  have hX_err2 : (2 * (H : ℝ)) * ((q₀ ^ k : ℕ) : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) ≤
      (1 / 16 : ℝ) * (1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ) := by
    have hinv_le : 1 / ((qMax ^ k : ℕ) : ℝ) ≤ 1 / ((q₀ ^ k : ℕ) : ℝ) :=
      one_div_le_one_div_of_le hqk_pos hqk_le
    calc (2 * (H : ℝ)) * ((q₀ ^ k : ℕ) : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ)
        ≤ (2 * (H : ℝ)) * ((qMax ^ k : ℕ) : ℝ) * Real.exp (640 * Q + 100) * (Real.log (X : ℝ)) ^ (1 / 4 : ℝ) := by gcongr
      _ ≤ (1 / 16 : ℝ) * (1 / ((qMax ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ) := hX6
      _ ≤ (1 / 16 : ℝ) * (1 / ((q₀ ^ k : ℕ) : ℝ)) * Real.exp (-(3 * Q + 47)) * Real.log (X : ℝ) := by gcongr
  have hcontra_bd := good_class_l2_transfer hk_ge2 hH_ge4 hX100 hB0 hQ hq0_Q hδ0 hδ_small ht_bd
    (lt_of_le_of_lt hqk_le hX3) hX4 hX_err1 hX_err2 hX7 χ₀ g tildeχ h hg_norm htilde_norm
    htilde_cop hh_norm hh_q0 hfactor hh_dist hL2_sum hL2_bd
  exact hgran_K q₀ hq0_mem k (hk_ge q₀ hq0_mem) χ₀ hprim tildeχ htilde_norm htilde_cop hcontra_bd
end
end E67H2

theorem OMA.solution : OMA.R_Erdos67_erdos_67_R1.H2 := E67H2.main_H2

import OMAStatements.S_mo_233204
import Mathlib

open OMA.S_mo_233204
open InnerProductGeometry
open scoped InnerProductSpace

lemma mo233204_cos_angle_unit {x y : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    Real.cos (angle x y) = ⟪x, y⟫_ℝ := by
  rw [cos_angle, hx, hy]; simp

lemma mo233204_angle_unit {x y : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    angle x y = Real.arccos ⟪x, y⟫_ℝ := by
  unfold angle; rw [hx, hy]; simp

lemma mo233204_key (t θ s c : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hθ0 : 0 ≤ θ) (hθ : θ ≤ Real.pi)
    (hs : s = Real.sin θ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    2 * (s * c) ^ 2 - 1 ≤ Real.cos (t * (Real.pi / 2)) * Real.cos (t * θ)
      + Real.sin (t * (Real.pi / 2)) * Real.sin (t * θ) * c := by
  have hpi := Real.pi_pos
  have hu0 : 0 ≤ t * (Real.pi / 2) := by positivity
  have huπ : t * (Real.pi / 2) ≤ Real.pi := by nlinarith
  have hv0 : 0 ≤ t * θ := by positivity
  have hvπ : t * θ ≤ Real.pi := by nlinarith
  have hsu : 0 ≤ Real.sin (t * (Real.pi / 2)) := Real.sin_nonneg_of_nonneg_of_le_pi hu0 huπ
  have hsv : 0 ≤ Real.sin (t * θ) := Real.sin_nonneg_of_nonneg_of_le_pi hv0 hvπ
  have hsu1 : Real.sin (t * (Real.pi / 2)) ≤ 1 := Real.sin_le_one _
  have hsv1 : Real.sin (t * θ) ≤ 1 := Real.sin_le_one _
  have hcos : Real.sin θ ≤ Real.cos (t * (Real.pi / 2) - t * θ) := by
    have h1 : |t * (Real.pi / 2) - t * θ| ≤ |Real.pi / 2 - θ| := by
      have : t * (Real.pi / 2) - t * θ = t * (Real.pi / 2 - θ) := by ring
      rw [this, abs_mul, abs_of_nonneg ht0]
      exact mul_le_of_le_one_left (abs_nonneg _) ht1
    have h2 : |Real.pi / 2 - θ| ≤ Real.pi := by
      rw [abs_le]; constructor <;> linarith
    rw [← Real.cos_abs (t * (Real.pi / 2) - t * θ), ← Real.cos_pi_div_two_sub,
      ← Real.cos_abs (Real.pi / 2 - θ)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) h2 h1
  have hexp := Real.cos_sub (t * (Real.pi / 2)) (t * θ)
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθ
  have hs1 : s ≤ 1 := by rw [hs]; exact Real.sin_le_one θ
  rw [← hs] at hcos
  have hprod : Real.sin (t * (Real.pi / 2)) * Real.sin (t * θ) ≤ 1 := by nlinarith
  have hprod0 : 0 ≤ Real.sin (t * (Real.pi / 2)) * Real.sin (t * θ) := mul_nonneg hsu hsv
  have h1c : (Real.sin (t * (Real.pi / 2)) * Real.sin (t * θ)) * (1 - c) ≤ 1 - c :=
    mul_le_of_le_one_left (by linarith) hprod
  have h3 : s - (1 - c) ≤ Real.cos (t * (Real.pi / 2)) * Real.cos (t * θ)
      + Real.sin (t * (Real.pi / 2)) * Real.sin (t * θ) * c := by
    nlinarith
  have hsc : s * c ≤ 1 := by nlinarith
  have hsc0 : 0 ≤ s * c := mul_nonneg hs0 hc0.le
  have hsc2 : (s * c) ^ 2 ≤ s * c := by nlinarith
  have hsc3 : s * c ≤ s := by nlinarith
  have hsc4 : s * c ≤ c := by nlinarith
  linarith

lemma mo233204_aux (b s : ℝ) (hb : 0 < b) (hs : 0 ≤ s) (h : b ^ 2 ≤ s ^ 2) :
    0 < s ∧ b ≤ s := by
  constructor <;> nlinarith

lemma mo233204_neg (x b : ℝ) (hb0 : b ≤ 0) : Real.arccos x ≤ 2 * Real.arccos b := by
  have h1 : Real.pi / 2 ≤ Real.arccos b := by
    rw [Real.arccos]; have := Real.arcsin_nonpos.2 hb0; linarith
  have := Real.arccos_le_pi x
  linarith

lemma mo233204_final (x b : ℝ) (hb0 : 0 < b) (hb1 : b ≤ 1) (h : 2 * b ^ 2 - 1 ≤ x) :
    Real.arccos x ≤ 2 * Real.arccos b := by
  have hcos2 : Real.cos (2 * Real.arccos b) = 2 * b ^ 2 - 1 := by
    rw [Real.cos_two_mul, Real.cos_arccos (by linarith) hb1]
  have harc : Real.arccos b ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.2 hb0.le
  have h0 := Real.arccos_nonneg b
  calc Real.arccos x ≤ Real.arccos (Real.cos (2 * Real.arccos b)) :=
        Real.arccos_le_arccos (by rw [hcos2]; exact h)
    _ = 2 * Real.arccos b := Real.arccos_cos (by linarith) (by linarith)

theorem OMA.solution : type_of% @OMA.S_mo_233204.main := by
  intro A B C hA hB hC hAB hCA t ht0 ht1 P Q hP hQ hPa hQa hAP hAQ
  obtain ⟨α, β, hα, hβ, hPe⟩ := hPa
  obtain ⟨γ, δ, hγ, hδ, hQe⟩ := hQa
  have hpi := Real.pi_pos
  have hAA : ⟪A, A⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hA]; norm_num
  have hBB : ⟪B, B⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hB]; norm_num
  have hCC : ⟪C, C⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hC]; norm_num
  have hPP : ⟪P, P⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hP]; norm_num
  have hQQ : ⟪Q, Q⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hQ]; norm_num
  have hAB0 : ⟪A, B⟫_ℝ = 0 := (inner_eq_zero_iff_angle_eq_pi_div_two A B).2 hAB
  have hBA0 : ⟪B, A⟫_ℝ = 0 := by rw [real_inner_comm]; exact hAB0
  have hθ0 : 0 ≤ angle A C := angle_nonneg _ _
  have hθπ : angle A C ≤ Real.pi := angle_le_pi _ _
  have hcosθ : Real.cos (angle A C) = ⟪A, C⟫_ℝ := mo233204_cos_angle_unit hA hC
  have hθlt : angle A C < Real.pi := by
    rcases lt_or_eq_of_le hθπ with h | h
    · exact h
    · exfalso
      apply hCA
      have h1 : ⟪A, C⟫_ℝ = -1 := by rw [← hcosθ, h, Real.cos_pi]
      have h2 : ⟪A + C, A + C⟫_ℝ = 0 := by
        simp only [inner_add_left, inner_add_right]
        rw [real_inner_comm A C]; linarith
      have h3 : A + C = 0 := by
        rw [real_inner_self_eq_norm_sq] at h2
        exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
      exact (neg_eq_of_add_eq_zero_right h3).symm
  set θ := angle A C with hθdef
  set u := t * (Real.pi / 2) with hu
  set v := t * θ with hv
  rw [hAB] at hAP
  have hu0 : 0 ≤ u := by positivity
  have huπ : u ≤ Real.pi := by nlinarith
  have hv0 : 0 ≤ v := by positivity
  have hvπ : v ≤ Real.pi := by nlinarith
  -- P coordinates
  have hAPi : ⟪A, P⟫_ℝ = α := by
    rw [hPe, inner_add_right, real_inner_smul_right, real_inner_smul_right, hAA, hAB0]; ring
  have hα' : α = Real.cos u := by
    rw [← hAPi, ← mo233204_cos_angle_unit hA hP, hAP]
  have hPP' : α ^ 2 + β ^ 2 = 1 := by
    rw [← hPP, hPe]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hAA, hBB, hAB0, hBA0]
    ring
  have hβ' : β = Real.sin u := by
    have h1 : β ^ 2 = Real.sin u ^ 2 := by
      have := Real.sin_sq_add_cos_sq u; rw [hα'] at hPP'; linarith
    have h2 : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi hu0 huπ
    rw [← Real.sqrt_sq hβ, h1, Real.sqrt_sq h2]
  -- Q coordinates
  have hAQi : ⟪A, Q⟫_ℝ = γ + δ * Real.cos θ := by
    rw [hQe, inner_add_right, real_inner_smul_right, real_inner_smul_right, hAA, hcosθ]; ring
  have hγ' : γ + δ * Real.cos θ = Real.cos v := by
    rw [← hAQi, ← mo233204_cos_angle_unit hA hQ, hAQ]
  have hQQ' : γ ^ 2 + 2 * γ * δ * Real.cos θ + δ ^ 2 = 1 := by
    rw [← hQQ, hQe]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hAA, hCC]
    rw [real_inner_comm A C, ← hcosθ]; ring
  have hsθ : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθπ
  have hsv : 0 ≤ Real.sin v := Real.sin_nonneg_of_nonneg_of_le_pi hv0 hvπ
  have hδ' : δ * Real.sin θ = Real.sin v := by
    have h1 : (δ * Real.sin θ) ^ 2 = Real.sin v ^ 2 := by
      have e1 := Real.sin_sq_add_cos_sq θ
      have e2 := Real.sin_sq_add_cos_sq v
      linear_combination δ ^ 2 * e1 - e2 + hQQ' - (γ + δ * Real.cos θ + Real.cos v) * hγ'
    rw [← Real.sqrt_sq (mul_nonneg hδ hsθ), h1, Real.sqrt_sq hsv]
  -- Bessel
  set b := ⟪B, C⟫_ℝ with hb
  have hbes : b ^ 2 ≤ Real.sin θ ^ 2 := by
    have h0 := real_inner_self_nonneg (x := C - Real.cos θ • A - b • B)
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hAA, hBB, hCC, hAB0, hBA0] at h0
    rw [real_inner_comm A C, real_inner_comm B C, ← hcosθ, ← hb] at h0
    have e1 := Real.sin_sq_add_cos_sq θ
    nlinarith
  have hPQ : ⟪P, Q⟫_ℝ = Real.cos u * Real.cos v + Real.sin u * (δ * b) := by
    rw [hPe, hQe]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hAA, hBA0]
    rw [← hcosθ, ← hb, ← hα', ← hβ', ← hγ']; ring
  rw [mo233204_angle_unit hP hQ, mo233204_angle_unit hB hC, ← hb]
  rcases le_or_gt b 0 with hb0 | hb0
  · exact mo233204_neg _ b hb0
  · obtain ⟨hs0, hbs⟩ := mo233204_aux b (Real.sin θ) hb0 hsθ hbes
    have hc0 : 0 < b / Real.sin θ := div_pos hb0 hs0
    have hc1 : b / Real.sin θ ≤ 1 := (div_le_one hs0).2 hbs
    have hsc : Real.sin θ * (b / Real.sin θ) = b := by field_simp
    have hδb : δ * b = Real.sin v * (b / Real.sin θ) := by
      rw [← hδ']; field_simp
    have hk := mo233204_key t θ (Real.sin θ) (b / Real.sin θ) ht0 ht1 hθ0 hθπ rfl hc0 hc1
    rw [hsc] at hk
    have hb1 : b ≤ 1 := le_trans hbs (Real.sin_le_one θ)
    apply mo233204_final _ b hb0 hb1
    rw [hPQ, hδb]; linarith

import OMAStatements.S_oeis_a002485

lemma OMA.pi_convergent_rational (n : ℕ) :
    ∃ p : ℤ, ∃ q : ℕ, 0 < q ∧
      (GenContFract.of Real.pi).convs n = (p : ℝ) / (q : ℝ) := by
  obtain ⟨r, hr⟩ := GenContFract.exists_rat_eq_nth_conv Real.pi n
  exact ⟨r.num, r.den, r.den_pos, hr.trans (Rat.cast_def r)⟩


theorem OMA_integral2485 (i k : ℝ) :
    (∫ x in (0 : ℝ)..1, (k + (k + i) * x ^ 2) / (1 + x ^ 2)) =
      k + i - i * (Real.pi / 4) := by
  have hc : Continuous (fun x : ℝ => (1 + x ^ 2)⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · intro x
      positivity
  have hfun : (fun x : ℝ => (k + (k + i) * x ^ 2) / (1 + x ^ 2)) =
      (fun x : ℝ => (k + i) - i * (1 + x ^ 2)⁻¹) := by
    funext x
    have hx : (1 + x ^ 2 : ℝ) ≠ 0 := by positivity
    field_simp
    <;> ring
  rw [hfun, intervalIntegral.integral_sub intervalIntegrable_const
      ((hc.intervalIntegrable 0 1).const_mul i), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_inv_one_add_sq]
  simp [Real.arctan_one, Real.arctan_zero]


theorem OMA_algebra2485_pos (p : ℤ) (q : ℕ) (hq : 0 < q) :
    (Real.pi - (p : ℝ) / (q : ℝ)) =
      (1 / (|((-(4 * (q : ℤ))) : ℝ)| * (2 : ℝ) ^ (-2 : ℤ))) *
        (((4 * (q : ℤ) - p : ℤ) : ℝ) + ((-(4 * (q : ℤ))) : ℝ) -
          ((-(4 * (q : ℤ))) : ℝ) * (Real.pi / 4)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  push_cast
  rw [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 4 * q)]
  norm_num
  field_simp
  <;> ring

theorem OMA_algebra2485_neg (p : ℤ) (q : ℕ) (hq : 0 < q) :
    -(Real.pi - (p : ℝ) / (q : ℝ)) =
      (1 / (|((4 * (q : ℤ)) : ℝ)| * (2 : ℝ) ^ (-2 : ℤ))) *
        (((p - 4 * (q : ℤ) : ℤ) : ℝ) + ((4 * (q : ℤ)) : ℝ) -
          ((4 * (q : ℤ)) : ℝ) * (Real.pi / 4)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  push_cast
  rw [abs_of_pos (by positivity : (0 : ℝ) < 4 * q)]
  norm_num
  field_simp
  <;> ring


theorem OMA.solution : type_of% @OMA.S_oeis_a002485.main := by
  intro n
  obtain ⟨p, q, hq, hconvs⟩ := OMA.pi_convergent_rational n
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  rcases neg_one_pow_eq_or ℝ n with hn | hn
  · refine ⟨-(4 * (q : ℤ)), -2, 4 * (q : ℤ) - p, 0, 0, by omega, ?_⟩
    rw [hn, hconvs]
    simp only [pow_zero, one_mul, Int.cast_add]
    rw [OMA_integral2485]
    simpa only [Int.cast_neg, Int.cast_mul, Int.cast_ofNat] using
      (OMA_algebra2485_pos p q hq)
  · refine ⟨4 * (q : ℤ), -2, p - 4 * (q : ℤ), 0, 0, by omega, ?_⟩
    rw [hn, hconvs]
    simp only [pow_zero, one_mul, Int.cast_add, neg_one_mul]
    rw [OMA_integral2485]
    simpa only [Int.cast_neg, Int.cast_mul, Int.cast_ofNat] using
      (OMA_algebra2485_neg p q hq)

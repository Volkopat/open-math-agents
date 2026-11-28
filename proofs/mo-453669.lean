import OMAStatements.S_mo_453669

open Matrix

private noncomputable def v_vec : Fin 4 → Fin 2 → ℂ
  | 0 => ![1, 0]
  | 1 => ![0, 1]
  | 2 => ![3 / 5, 4 / 5]
  | 3 => ![3 / 5, 4 * Complex.I / 5]

private lemma eq_zero_of_trace_conjTranspose_mul_self {N : ℕ}
    (X : Matrix (Fin N) (Fin N) ℂ) (hX : (Xᴴ * X).trace = 0) : X = 0 := by
  have hre : (Xᴴ * X).trace.re = 0 := by rw [hX]; simp
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum] at hre
  have hsq : ∀ a b : Fin N, (star (X b a) * X b a).re = (X b a).re ^ 2 + (X b a).im ^ 2 := by
    intro a b
    change (starRingEnd ℂ (X b a) * X b a).re = _
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  simp_rw [hsq] at hre
  have h1 : ∀ i ∈ Finset.univ, ∑ j : Fin N, ((X j i).re ^ 2 + (X j i).im ^ 2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => by positivity).mp hre
  ext j i
  have h2 : ∀ k ∈ Finset.univ, (X k i).re ^ 2 + (X k i).im ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun k _ => by positivity).mp (h1 i (Finset.mem_univ i))
  have hji := h2 j (Finset.mem_univ j)
  change X j i = 0
  have hr : (X j i).re = 0 := by nlinarith [sq_nonneg (X j i).re, sq_nonneg (X j i).im]
  have hi : (X j i).im = 0 := by nlinarith [sq_nonneg (X j i).re, sq_nonneg (X j i).im]
  exact Complex.ext hr hi

private lemma eq_lincomb_of_traces {N : ℕ}
    (A0 A1 A : Matrix (Fin N) (Fin N) ℂ) (a b : ℂ)
    (h00 : (A0ᴴ * A0).trace = N)
    (h11 : (A1ᴴ * A1).trace = N)
    (hAA : (Aᴴ * A).trace = N)
    (h01 : (A0ᴴ * A1).trace = 0)
    (h10 : (A1ᴴ * A0).trace = 0)
    (h0A : (A0ᴴ * A).trace = N * a)
    (hA0 : (Aᴴ * A0).trace = N * star a)
    (h1A : (A1ᴴ * A).trace = N * b)
    (hA1 : (Aᴴ * A1).trace = N * star b)
    (hnorm : star a * a + star b * b = 1) :
    A = a • A0 + b • A1 := by
  let X := A - (a • A0 + b • A1)
  have hXtr : (Xᴴ * X).trace = 0 := by
    change ((A - (a • A0 + b • A1))ᴴ * (A - (a • A0 + b • A1))).trace = 0
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_smul]
    simp only [sub_mul, mul_sub, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
      h00, h11, hAA, h01, h10, h0A, hA0, h1A, hA1]
    calc
      _ = (N : ℂ) * (1 - (star a * a + star b * b)) := by ring
      _ = 0 := by rw [hnorm]; ring
  have hX0 := eq_zero_of_trace_conjTranspose_mul_self X hXtr
  exact sub_eq_zero.mp hX0

private lemma star_three_fifths : star (3 / 5 : ℂ) = 3 / 5 := by
  change starRingEnd ℂ (3 / 5 : ℂ) = 3 / 5
  simp [map_div₀, map_ofNat]

private lemma star_four_fifths : star (4 / 5 : ℂ) = 4 / 5 := by
  change starRingEnd ℂ (4 / 5 : ℂ) = 4 / 5
  simp [map_div₀, map_ofNat]

private lemma star_four_I_fifths : star (4 * Complex.I / 5 : ℂ) = -(4 * Complex.I / 5) := by
  change starRingEnd ℂ (4 * Complex.I / 5 : ℂ) = -(4 * Complex.I / 5)
  simp [map_div₀, map_mul, map_ofNat, Complex.conj_I]
  ring

theorem OMA.solution : type_of% @OMA.S_mo_453669.main := by
  refine ⟨v_vec, ?_, ?_⟩
  · intro i
    fin_cases i <;>
    · simp only [v_vec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.star_apply, star_one, star_zero, star_three_fifths, star_four_fifths, star_four_I_fifths]
      ring_nf
      try simp [Complex.I_sq]
      try norm_num
  · intro N hN ⟨U, hU⟩
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    let A : Fin 4 → Matrix (Fin N) (Fin N) ℂ := fun i => (U i : Matrix (Fin N) (Fin N) ℂ)
    have htr : ∀ i j, ((A i)ᴴ * A j).trace = (N : ℂ) * (star (v_vec i) ⬝ᵥ v_vec j) := by
      intro i j
      have hij := hU i j
      change ((A i)ᴴ * A j).trace / (N : ℂ) = star (v_vec i) ⬝ᵥ v_vec j at hij
      rw [← hij, mul_div_cancel₀ _ hN0]
    have hunit : ∀ i, (A i)ᴴ * A i = 1 ∧ A i * (A i)ᴴ = 1 := by
      intro i
      exact ⟨(Matrix.mem_unitaryGroup_iff').mp (U i).2,
        (Matrix.mem_unitaryGroup_iff).mp (U i).2⟩
    have h00 : ((A 0)ᴴ * A 0).trace = N := by
      rw [htr 0 0]; simp [v_vec, dotProduct, Fin.sum_univ_two]
    have h11 : ((A 1)ᴴ * A 1).trace = N := by
      rw [htr 1 1]; simp [v_vec, dotProduct, Fin.sum_univ_two]
    have h22 : ((A 2)ᴴ * A 2).trace = N := by
      rw [htr 2 2]
      have hd : star (v_vec 2) ⬝ᵥ v_vec 2 = 1 := by
        simp only [v_vec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Pi.star_apply, star_three_fifths, star_four_fifths]
        norm_num
      rw [hd, mul_one]
    have h33 : ((A 3)ᴴ * A 3).trace = N := by
      rw [htr 3 3]
      have hd : star (v_vec 3) ⬝ᵥ v_vec 3 = 1 := by
        simp only [v_vec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Pi.star_apply, star_three_fifths, star_four_I_fifths]
        ring_nf
        simp [Complex.I_sq]
        norm_num
      rw [hd, mul_one]
    have h01 : ((A 0)ᴴ * A 1).trace = 0 := by
      rw [htr 0 1]; simp [v_vec, dotProduct, Fin.sum_univ_two]
    have h10 : ((A 1)ᴴ * A 0).trace = 0 := by
      rw [htr 1 0]; simp [v_vec, dotProduct, Fin.sum_univ_two]
    have h02 : ((A 0)ᴴ * A 2).trace = (N : ℂ) * (3 / 5 : ℂ) := by
      rw [htr 0 2]; congr 1; simp [v_vec, dotProduct, Fin.sum_univ_two]
    have h20 : ((A 2)ᴴ * A 0).trace = (N : ℂ) * star (3 / 5 : ℂ) := by
      rw [htr 2 0]; congr 1
      simp only [v_vec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.star_apply, mul_one, mul_zero, add_zero]
    have h12 : ((A 1)ᴴ * A 2).trace = (N : ℂ) * (4 / 5 : ℂ) := by
      rw [htr 1 2]; congr 1; simp [v_vec, dotProduct, Fin.sum_univ_two]
    have h21 : ((A 2)ᴴ * A 1).trace = (N : ℂ) * star (4 / 5 : ℂ) := by
      rw [htr 2 1]; congr 1
      simp only [v_vec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.star_apply, mul_zero, mul_one, zero_add]
    have h03 : ((A 0)ᴴ * A 3).trace = (N : ℂ) * (3 / 5 : ℂ) := by
      rw [htr 0 3]; congr 1; simp [v_vec, dotProduct, Fin.sum_univ_two]
    have h30 : ((A 3)ᴴ * A 0).trace = (N : ℂ) * star (3 / 5 : ℂ) := by
      rw [htr 3 0]; congr 1
      simp only [v_vec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.star_apply, mul_one, mul_zero, add_zero]
    have h13 : ((A 1)ᴴ * A 3).trace = (N : ℂ) * (4 * Complex.I / 5 : ℂ) := by
      rw [htr 1 3]; congr 1; simp [v_vec, dotProduct, Fin.sum_univ_two]
    have h31 : ((A 3)ᴴ * A 1).trace = (N : ℂ) * star (4 * Complex.I / 5 : ℂ) := by
      rw [htr 3 1]; congr 1
      simp only [v_vec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.star_apply, mul_zero, mul_one, zero_add]
    have hn2 : star (3 / 5 : ℂ) * (3 / 5 : ℂ) + star (4 / 5 : ℂ) * (4 / 5 : ℂ) = 1 := by
      rw [star_three_fifths, star_four_fifths]; norm_num
    have hn3 : star (3 / 5 : ℂ) * (3 / 5 : ℂ) +
        star (4 * Complex.I / 5 : ℂ) * (4 * Complex.I / 5 : ℂ) = 1 := by
      rw [star_three_fifths, star_four_I_fifths]
      ring_nf
      simp [Complex.I_sq]
      norm_num
    have hA2 : A 2 = (3 / 5 : ℂ) • A 0 + (4 / 5 : ℂ) • A 1 :=
      eq_lincomb_of_traces (A 0) (A 1) (A 2) (3 / 5) (4 / 5)
        h00 h11 h22 h01 h10 h02 h20 h12 h21 hn2
    have hA3 : A 3 = (3 / 5 : ℂ) • A 0 + (4 * Complex.I / 5 : ℂ) • A 1 :=
      eq_lincomb_of_traces (A 0) (A 1) (A 3) (3 / 5) (4 * Complex.I / 5)
        h00 h11 h33 h01 h10 h03 h30 h13 h31 hn3
    let V : Matrix (Fin N) (Fin N) ℂ := (A 0)ᴴ * A 1
    have hVV : Vᴴ * V = 1 := by
      change ((A 0)ᴴ * A 1)ᴴ * ((A 0)ᴴ * A 1) = 1
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc
        (A 1)ᴴ * A 0 * ((A 0)ᴴ * A 1) = (A 1)ᴴ * (A 0 * (A 0)ᴴ) * A 1 := by simp only [Matrix.mul_assoc]
        _ = (A 1)ᴴ * 1 * A 1 := by rw [(hunit 0).2]
        _ = (A 1)ᴴ * A 1 := by rw [Matrix.mul_one]
        _ = 1 := (hunit 1).1
    have hW2_def : (A 0)ᴴ * A 2 = (3 / 5 : ℂ) • 1 + (4 / 5 : ℂ) • V := by
      rw [hA2, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, (hunit 0).1]
    have hW2_unit : ((A 0)ᴴ * A 2)ᴴ * ((A 0)ᴴ * A 2) = 1 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc
        (A 2)ᴴ * A 0 * ((A 0)ᴴ * A 2) = (A 2)ᴴ * (A 0 * (A 0)ᴴ) * A 2 := by simp only [Matrix.mul_assoc]
        _ = (A 2)ᴴ * 1 * A 2 := by rw [(hunit 0).2]
        _ = (A 2)ᴴ * A 2 := by rw [Matrix.mul_one]
        _ = 1 := (hunit 2).1
    have hW3_def : (A 0)ᴴ * A 3 = (3 / 5 : ℂ) • 1 + (4 * Complex.I / 5 : ℂ) • V := by
      rw [hA3, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, (hunit 0).1]
    have hW3_unit : ((A 0)ᴴ * A 3)ᴴ * ((A 0)ᴴ * A 3) = 1 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc
        (A 3)ᴴ * A 0 * ((A 0)ᴴ * A 3) = (A 3)ᴴ * (A 0 * (A 0)ᴴ) * A 3 := by simp only [Matrix.mul_assoc]
        _ = (A 3)ᴴ * 1 * A 3 := by rw [(hunit 0).2]
        _ = (A 3)ᴴ * A 3 := by rw [Matrix.mul_one]
        _ = 1 := (hunit 3).1
    have h916 : (9 / 25 : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) + (16 / 25 : ℂ) • 1 = 1 := by
      rw [← add_smul]
      norm_num
    have hV_skew : V + Vᴴ = 0 := by
      have h := hW2_unit
      rw [hW2_def, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
        star_three_fifths, star_four_fifths] at h
      simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, hVV, smul_smul] at h
      have h1 : (3 / 5 * (3 / 5 : ℂ) : ℂ) = 9 / 25 := by norm_num
      have h2 : (3 / 5 * (4 / 5 : ℂ) : ℂ) = 12 / 25 := by norm_num
      have h3 : (4 / 5 * (3 / 5 : ℂ) : ℂ) = 12 / 25 := by norm_num
      have h4 : (4 / 5 * (4 / 5 : ℂ) : ℂ) = 16 / 25 := by norm_num
      rw [h1, h2, h3, h4] at h
      have h_sub : ((9 / 25 : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) + (12 / 25 : ℂ) • Vᴴ +
          ((12 / 25 : ℂ) • V + (16 / 25 : ℂ) • 1)) -
          ((9 / 25 : ℂ) • 1 + (16 / 25 : ℂ) • 1) = (12 / 25 : ℂ) • (V + Vᴴ) := by
        rw [smul_add]; abel
      rw [h, h916, sub_self] at h_sub
      have hc : (12 / 25 : ℂ) ≠ 0 := by norm_num
      exact (smul_eq_zero.mp h_sub.symm).resolve_left hc
    have hV_self : V - Vᴴ = 0 := by
      have h := hW3_unit
      rw [hW3_def, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
        star_three_fifths, star_four_I_fifths] at h
      simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, hVV, smul_smul] at h
      have h1 : (3 / 5 * (3 / 5 : ℂ) : ℂ) = 9 / 25 := by norm_num
      have h2 : (3 / 5 * -(4 * Complex.I / 5) : ℂ) = -(12 * Complex.I / 25) := by ring
      have h3 : (4 * Complex.I / 5 * (3 / 5) : ℂ) = 12 * Complex.I / 25 := by ring
      have h4 : (4 * Complex.I / 5 * -(4 * Complex.I / 5) : ℂ) = 16 / 25 := by
        calc
          (4 * Complex.I / 5 * -(4 * Complex.I / 5) : ℂ) = -(16 / 25 * (Complex.I * Complex.I)) := by ring
          _ = -(16 / 25 * (-1)) := by rw [Complex.I_mul_I]
          _ = 16 / 25 := by ring
      rw [h1, h2, h3, h4] at h
      have h_sub : ((9 / 25 : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) +
          (-(12 * Complex.I / 25 : ℂ)) • Vᴴ +
          ((12 * Complex.I / 25 : ℂ) • V + (16 / 25 : ℂ) • 1)) -
          ((9 / 25 : ℂ) • 1 + (16 / 25 : ℂ) • 1) =
          (12 * Complex.I / 25 : ℂ) • (V - Vᴴ) := by
        rw [smul_sub, neg_smul]; abel
      rw [h, h916, sub_self] at h_sub
      have hc : (12 * Complex.I / 25 : ℂ) ≠ 0 := by
        intro hc0
        have : (Complex.I : ℂ) = 0 := by
          linear_combination (25 / 12 : ℂ) * hc0
        exact Complex.I_ne_zero this
      exact (smul_eq_zero.mp h_sub.symm).resolve_left hc
    have hV0 : V = 0 := by
      have h2V : (2 : ℂ) • V = 0 := by
        calc
          (2 : ℂ) • V = (V + Vᴴ) + (V - Vᴴ) := by
            rw [two_smul]; abel
          _ = 0 + 0 := by rw [hV_skew, hV_self]
          _ = 0 := add_zero 0
      exact (smul_eq_zero.mp h2V).resolve_left (by norm_num)
    have h01_mat : (0 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
      calc
        (0 : Matrix (Fin N) (Fin N) ℂ) = Vᴴ * V := by rw [hV0, Matrix.mul_zero]
        _ = 1 := hVV
    have h01_c := congr_fun (congr_fun h01_mat ⟨0, hN⟩) ⟨0, hN⟩
    simp at h01_c

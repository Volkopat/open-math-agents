import OMAStatements.S_oeis_a083219

-- Problem: OEIS A083219, the left-half-plane root count for the multinacci polynomials.
-- Credit: @RiverMint78

open Complex Polynomial
open scoped NNReal
open OMA.S_oeis_a083219 (poly)

private theorem sub_disk_re {z : ℂ} (hz : ‖z‖ ≤ 1) : 1 ≤ (2 - z).re := by
  have h := (Complex.re_le_norm z).trans hz
  simp only [Complex.sub_re, Complex.re_ofNat]
  linarith

/-- For a unit complex number u, the map z ↦ u (2-z)^r contracts the closed unit disk
when -1/2 ≤ r ≤ 0. We use this with r = -1/d. -/
private theorem exists_disk_fixed {r : ℝ} (hr : |r| ≤ 1 / 2) (hr₀ : r ≤ 0)
    {u : ℂ} (hu : ‖u‖ = 1) :
    ∃ z : ℂ, ‖z‖ ≤ 1 ∧ z = u * (2 - z) ^ (r : ℂ) := by
  let s := Metric.closedBall (0 : ℂ) 1
  let f (z : ℂ) := u * (2 - z) ^ (r : ℂ)
  let f' (z : ℂ) := u * ((r : ℂ) * (2 - z) ^ ((r : ℂ) - 1) * (-1))
  have hnorm {z : ℂ} (hz : z ∈ s) : 1 ≤ ‖2 - z‖ :=
    (sub_disk_re (by simpa [s, Metric.mem_closedBall, dist_eq_norm] using hz)).trans
      (Complex.re_le_norm _)
  have hf : ∀ z ∈ s, HasDerivWithinAt f (f' z) s z := by
    intro z hz
    have hre := sub_disk_re (by simpa [s, Metric.mem_closedBall, dist_eq_norm] using hz)
    have hslit : 2 - z ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith))
    exact ((((hasDerivAt_id z).const_sub (2 : ℂ)).cpow_const hslit).const_mul u).hasDerivWithinAt
  have hb : ∀ z ∈ s, ‖f' z‖₊ ≤ (1 / 2 : ℝ≥0) := by
    intro z hz
    change ‖f' z‖ ≤ ((1 / 2 : ℝ≥0) : ℝ)
    rw [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    have hp : ‖(2 - z) ^ ((r : ℂ) - 1)‖ ≤ 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_cpow_real]
      exact Real.rpow_le_one_of_one_le_of_nonpos (hnorm hz) (by linarith)
    calc
      ‖f' z‖ = |r| * ‖(2 - z) ^ ((r : ℂ) - 1)‖ := by
        simp [f', hu, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |r| * 1 := mul_le_mul_of_nonneg_left hp (abs_nonneg r)
      _ ≤ 1 / 2 := by simpa using hr
  have hmap : Set.MapsTo f s s := by
    intro z hz
    simp only [s, Metric.mem_closedBall, dist_eq_norm, sub_zero, f, norm_mul, hu, one_mul,
      Complex.norm_cpow_real]
    exact Real.rpow_le_one_of_one_le_of_nonpos (hnorm hz) hr₀
  have hLip : LipschitzOnWith (1 / 2 : ℝ≥0) f s :=
    (convex_closedBall (0 : ℂ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hf hb
  have hCtr : ContractingWith (1 / 2 : ℝ≥0) (hmap.restrict f s s) := by
    refine ⟨by norm_num, ?_⟩
    intro x y
    exact hLip x.property y.property
  obtain ⟨z, hz, hfix, -, -⟩ := hCtr.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hmap
    (show (0 : ℂ) ∈ s by simp [s]) (edist_ne_top _ _)
  exact ⟨z, by simpa [s, Metric.mem_closedBall, dist_eq_norm] using hz, hfix.eq.symm⟩

private noncomputable def rootAngle (d : ℕ) (j : Fin d) : ℝ :=
  2 * Real.pi * (j : ℝ) / d

private noncomputable def omegaAt (d : ℕ) (j : Fin d) : ℂ :=
  Complex.exp ((rootAngle d j : ℂ) * Complex.I)

private theorem omegaAt_pow (d : ℕ) (hd : d ≠ 0) (j : Fin d) : omegaAt d j ^ d = 1 := by
  rw [omegaAt, ← Complex.exp_nat_mul]
  have hcast : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have h : (d : ℂ) * ((rootAngle d j : ℂ) * Complex.I) =
      (j : ℕ) * (2 * Real.pi * Complex.I) := by
    unfold rootAngle
    push_cast
    field_simp
  rw [h, Complex.exp_nat_mul_two_pi_mul_I]

private theorem omegaAt_injective (d : ℕ) (hd : d ≠ 0) : Function.Injective (omegaAt d) := by
  intro i j hij
  have hprim := Complex.isPrimitiveRoot_exp_of_coprime 1 d hd (Nat.coprime_one_left d)
  have hpow (k : Fin d) : Complex.exp (2 * Real.pi * Complex.I * ((1 : ℕ) / (d : ℂ))) ^ (k : ℕ) =
      omegaAt d k := by
    rw [omegaAt, ← Complex.exp_nat_mul]
    congr 1
    unfold rootAngle
    push_cast
    ring
  have heq : _ := (hpow i).trans (hij.trans (hpow j).symm)
  exact Fin.ext (hprim.pow_inj i.isLt j.isLt (by simpa using heq))

/-- Each root of unity gives a root of z^d (2-z) = 1 in the disk. -/
private theorem disk_roots {d : ℕ} (hd : 2 ≤ d) :
    ∃ z : Fin d → ℂ, (∀ j, ‖z j‖ ≤ 1 ∧ z j =
      omegaAt d j * (2 - z j) ^ ((-((d : ℝ)⁻¹) : ℝ) : ℂ)) ∧
      Function.Injective z ∧ ∀ j, z j ^ d * (2 - z j) = 1 := by
  have hpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hne : d ≠ 0 := by omega
  have hr : |-((d : ℝ)⁻¹)| ≤ 1 / 2 := by
    rw [abs_neg, abs_of_nonneg (inv_nonneg.mpr hpos.le), inv_eq_one_div]
    gcongr
    exact_mod_cast hd
  have hz (j : Fin d) : ∃ z : ℂ, ‖z‖ ≤ 1 ∧ z =
      omegaAt d j * (2 - z) ^ ((-((d : ℝ)⁻¹) : ℝ) : ℂ) :=
    exists_disk_fixed hr (neg_nonpos.mpr (inv_nonneg.mpr hpos.le)) (by simp [omegaAt, Complex.norm_exp])
  choose z hz using hz
  have hne' (j : Fin d) : (2 : ℂ) - z j ≠ 0 := by
    intro h
    have hb := sub_disk_re (hz j).1
    rw [h, Complex.zero_re] at hb
    norm_num at hb
  refine ⟨z, hz, ?_, ?_⟩
  · intro i j hij
    apply omegaAt_injective d hne
    have hp : (2 - z j) ^ ((-((d : ℝ)⁻¹) : ℝ) : ℂ) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (hne' j))
    apply mul_right_cancel₀ hp
    simpa only [hij, ← (hz j).2] using (hz i).2.symm
  · intro j
    have hcast : ((-((d : ℝ)⁻¹) : ℝ) : ℂ) * (d : ℂ) = -1 := by
      push_cast
      field_simp
    have hpower : (z j) ^ d = (2 - z j)⁻¹ := by
      calc
        (z j) ^ d = (omegaAt d j * (2 - z j) ^ ((-((d : ℝ)⁻¹) : ℝ) : ℂ)) ^ d :=
          congrArg (fun x : ℂ => x ^ d) (hz j).2
        _ = (2 - z j)⁻¹ := by
          rw [mul_pow, omegaAt_pow d hne, one_mul, ← Complex.cpow_mul_nat, hcast,
            Complex.cpow_neg_one]
    rw [hpower, inv_mul_cancel₀ (hne' j)]


/-- The displacement in argument is less than π/(2d). At a purely imaginary
root of unity the displacement is toward the left. -/
private theorem disk_root_left {d : ℕ} (hd : 2 ≤ d) (j : Fin d) {z : ℂ}
    (hz : ‖z‖ ≤ 1) (hfix : z = omegaAt d j * (2 - z) ^ ((-((d : ℝ)⁻¹) : ℝ) : ℂ)) :
    z.re < 0 ↔ d ≤ 4 * (j : ℕ) ∧ 4 * (j : ℕ) ≤ 3 * d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hre := sub_disk_re hz
  have hne : (2 : ℂ) - z ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hre
    norm_num at hre
  let ε : ℝ := Real.pi / 2 / (d : ℝ)
  let α : ℝ := -(2 - z).arg / (d : ℝ)
  let φ : ℝ := rootAngle d j + α
  let W : ℂ :=
    (rootAngle d j : ℂ) * Complex.I + Complex.log (2 - z) * ((-((d : ℝ)⁻¹) : ℝ) : ℂ)
  have hW : z = Complex.exp W := by
    dsimp [W]
    rw [Complex.exp_add, ← Complex.cpow_def_of_ne_zero hne]
    exact hfix
  have hWim : W.im = φ := by
    simp only [W, φ, α, Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.log_im, mul_one, mul_zero, zero_add,
      add_zero, div_eq_mul_inv]
    ring
  have hreφ : z.re = Real.exp W.re * Real.cos φ := by rw [hW, Complex.exp_re, hWim]
  have himφ : z.im = Real.exp W.re * Real.sin φ := by rw [hW, Complex.exp_im, hWim]
  have harg : |(2 - z).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by linarith))
  have ha : -ε < α ∧ α < ε := by
    obtain ⟨ha₁, ha₂⟩ := abs_lt.mp harg
    dsimp [ε, α]
    rw [← neg_div]
    constructor <;> apply (div_lt_div_iff_of_pos_right hdR).2 <;> linarith
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hscale : (d : ℝ) * ε = Real.pi / 2 := by
    dsimp [ε]
    field_simp
  have hsmall : ε ≤ Real.pi / 2 := by
    rw [← hscale]
    simpa using mul_le_mul_of_nonneg_right hd1 hε.le
  have hφ : φ = 4 * (j : ℝ) * ε + α := by dsimp [φ, rootAngle, ε]; ring
  have hscaled {a b : ℕ} (hab : a ≤ b) : (a : ℝ) * ε ≤ (b : ℝ) * ε :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hε.le
  have hlow (a : ℕ) (h : a + 1 ≤ 4 * (j : ℕ)) : (a : ℝ) * ε < φ := by
    have hs := hscaled h
    push_cast at hs
    nlinarith only [hs, ha.1, hφ]
  have hhigh (a : ℕ) (h : 4 * (j : ℕ) + 1 ≤ a) : φ < (a : ℝ) * ε := by
    have hs := hscaled h
    push_cast at hs
    nlinarith only [hs, ha.2, hφ]
  have hleft_of_angle (h₁ : Real.pi / 2 < φ) (h₂ : φ < Real.pi + Real.pi / 2) :
      z.re < 0 := by
    rw [hreφ]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (Real.cos_neg_of_pi_div_two_lt_of_lt h₁ h₂)
  by_cases hlo : 4 * (j : ℕ) < d
  · have hhiφ : φ < Real.pi / 2 := hscale ▸ hhigh d (by omega)
    have hj : 0 ≤ 4 * (j : ℝ) * ε := by positivity
    have hloφ : -(Real.pi / 2) < φ := by linarith [ha.1, hφ]
    have hpos : 0 < z.re := by
      rw [hreφ]
      exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨hloφ, hhiφ⟩)
    exact iff_of_false (not_lt_of_ge hpos.le) (by omega)
  by_cases hhi : 3 * d < 4 * (j : ℕ)
  · have h₁ := hlow (3 * d) (by omega)
    have h₂ := hhigh (4 * d) (by have := j.isLt; omega)
    push_cast at h₁ h₂
    have hcos : 0 < Real.cos φ := by
      rw [← Real.cos_sub_two_pi φ]
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith only [h₁, h₂, hscale, Real.pi_pos]
    have hpos : 0 < z.re := hreφ ▸ mul_pos (Real.exp_pos _) hcos
    exact iff_of_false (not_lt_of_ge hpos.le) (by omega)
  refine ⟨fun _ => by omega, fun _ => ?_⟩
  by_cases heq : 4 * (j : ℕ) = d
  · have heqR : 4 * (j : ℝ) = (d : ℝ) := by exact_mod_cast heq
    have heqφ : φ = Real.pi / 2 + α := by rw [hφ, heqR, hscale]
    have him : 0 < z.im := by
      rw [himφ]
      apply mul_pos (Real.exp_pos _)
      apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [ha.1, ha.2]
    have hargneg : (2 - z).arg < 0 := by
      apply Complex.arg_neg_iff.mpr
      simpa using him
    have hαpos : 0 < α := div_pos (neg_pos.mpr hargneg) hdR
    exact hleft_of_angle (by linarith) (by linarith [ha.2, Real.pi_pos])
  by_cases heq : 4 * (j : ℕ) = 3 * d
  · have heqR : 4 * (j : ℝ) = 3 * (d : ℝ) := by exact_mod_cast heq
    have heqφ : φ = Real.pi + Real.pi / 2 + α := by
      rw [hφ, heqR]
      nlinarith only [hscale, Real.pi_pos]
    have hsin : Real.sin φ < 0 := by
      have hpos := Real.sin_pos_of_pos_of_lt_pi (x := φ - Real.pi)
        (by linarith [ha.1]) (by linarith [ha.2])
      rw [Real.sin_sub_pi] at hpos
      linarith
    have him : z.im < 0 := himφ ▸ mul_neg_of_pos_of_neg (Real.exp_pos _) hsin
    have him' : 0 < (2 - z).im := by simpa using him
    have hargpos : 0 < (2 - z).arg := by
      apply lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr him'.le)
      intro h
      exact him'.ne' (Complex.arg_eq_zero_iff.mp h.symm).2
    have hαneg : α < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr hargpos) hdR
    exact hleft_of_angle (by linarith [ha.1, Real.pi_pos]) (by linarith)
  have h₁ := hlow d (by omega)
  have h₂ := hhigh (3 * d) (by omega)
  push_cast at h₂
  exact hleft_of_angle (by linarith) (by nlinarith only [h₂, hscale])

private theorem sector_count {d : ℕ} (hd : 2 ≤ d) :
    (Finset.univ.filter fun j : Fin d => d ≤ 4 * (j : ℕ) ∧ 4 * (j : ℕ) ≤ 3 * d).card =
      (d - 1) - 2 * ((d - 1) / 4) := by
  have hmap :
      (Finset.univ.filter (fun j : Fin d => d ≤ 4 * (j : ℕ) ∧ 4 * (j : ℕ) ≤ 3 * d)).map
        Fin.valEmbedding = Finset.Icc ((d + 3) / 4) (3 * d / 4) := by
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
    constructor
    · rintro ⟨j, hj, rfl⟩
      change (d + 3) / 4 ≤ (j : ℕ) ∧ (j : ℕ) ≤ 3 * d / 4
      omega
    · intro hi
      refine ⟨⟨i, by omega⟩, ?_, rfl⟩
      change d ≤ 4 * i ∧ 4 * i ≤ 3 * d
      omega
  rw [← Finset.card_map Fin.valEmbedding, hmap, Nat.card_Icc]
  omega


private noncomputable def augmented (d : ℕ) : ℂ[X] :=
  X ^ d * (X - C 2) + 1

private theorem augmented_eq (d : ℕ) : poly d * (X - C 1) = augmented d := by
  have hg := geom_sum_mul (X : ℂ[X]) d
  rw [map_one]
  unfold poly augmented
  have htwo : C (2 : ℂ) = (2 : ℂ[X]) := by
    simpa only [Nat.cast_ofNat] using (map_natCast (C : ℂ →+* ℂ[X]) 2)
  rw [sub_mul, hg, htwo]
  ring

private theorem augmented_ne_zero (d : ℕ) : augmented d ≠ 0 := by
  intro h
  have h₂ := congrArg (fun p : ℂ[X] => p.eval 2) h
  simp [augmented] at h₂

private theorem augmented_natDegree_le (d : ℕ) : (augmented d).natDegree ≤ d + 1 := by
  unfold augmented
  apply Polynomial.natDegree_add_le_of_degree_le
  · rw [Polynomial.natDegree_mul (pow_ne_zero _ X_ne_zero) (X_sub_C_ne_zero _),
      Polynomial.natDegree_pow, Polynomial.natDegree_X, Polynomial.natDegree_X_sub_C, mul_one]
  · simp

private theorem augmented_root (d : ℕ) (w : ℂ) (h : w ^ d * (2 - w) = 1) :
    w ∈ (augmented d).roots := by
  apply (Polynomial.mem_roots (augmented_ne_zero d)).2
  change (augmented d).eval w = 0
  simp only [augmented, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  linear_combination -h

private theorem exists_outer_root {d : ℕ} (hd : 2 ≤ d) :
    ∃ r : ℝ, 1 < r ∧ (r : ℂ) ^ d * (2 - (r : ℂ)) = 1 := by
  let f (x : ℝ) := x ^ d * (2 - x)
  have h13 : 1 ≤ f (3 / 2) := by
    have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 3 / 2 by norm_num) hd
    norm_num [f] at h ⊢
    linarith
  have h2 : f 2 ≤ 1 := by simp [f]
  have hf : ContinuousOn f (Set.Icc (3 / 2) 2) := by dsimp [f]; fun_prop
  obtain ⟨r, hr, heq⟩ :=
    (intermediate_value_Icc' (show (3 / 2 : ℝ) ≤ 2 by norm_num) hf) ⟨h2, h13⟩
  refine ⟨r, lt_of_lt_of_le (by norm_num) hr.1, ?_⟩
  dsimp [f] at heq
  exact_mod_cast heq

/-- The d disk roots and a real root greater than 1 exhaust the degree bound for
the augmented polynomial, so each occurs with multiplicity one. -/
private theorem root_count {d : ℕ} (hd : 2 ≤ d) :
    ((poly d).roots.filter fun z => z.re < 0).card = (d - 1) - 2 * ((d - 1) / 4) := by
  classical
  obtain ⟨z, hz, hinj, hroot⟩ := disk_roots hd
  obtain ⟨r, hr, houter⟩ := exists_outer_root hd
  let e : Fin d ↪ ℂ := ⟨z, hinj⟩
  let U : Finset ℂ := Finset.univ.map e
  have hrU : (r : ℂ) ∉ U := by
    intro h
    obtain ⟨j, -, hj⟩ := Finset.mem_map.mp h
    change z j = (r : ℂ) at hj
    have hbd := (hz j).1
    rw [hj, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at hbd
    linarith
  let S : Finset ℂ := insert (r : ℂ) U
  have hcard : S.card = d + 1 := by
    simp [S, Finset.card_insert_of_notMem hrU, U]
  have hle : S.val ≤ (augmented d).roots := by
    apply Finset.val_le_iff_val_subset.mpr
    intro w hw
    change w ∈ S at hw
    rcases Finset.mem_insert.mp hw with (rfl | hw)
    · exact augmented_root d r houter
    · obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hw
      exact augmented_root d (z j) (hroot j)
  have hall : S.val = (augmented d).roots := by
    refine Multiset.eq_of_le_of_card_le hle ?_
    change (augmented d).roots.card ≤ S.card
    rw [hcard]
    exact (Polynomial.card_roots' _).trans (augmented_natDegree_le d)
  let left (w : ℂ) : Prop := w.re < 0
  have hpositive : ¬ left (r : ℂ) := by
    change ¬ (r : ℂ).re < 0
    rw [Complex.ofReal_re]
    linarith
  have hcount : ((augmented d).roots.filter left).card =
      (d - 1) - 2 * ((d - 1) / 4) := by
    rw [← hall, ← Finset.filter_val]
    change (S.filter left).card = _
    rw [show S.filter left = U.filter left by simp [S, Finset.filter_insert, hpositive]]
    rw [show U.filter left = (Finset.univ.filter (fun j : Fin d => left (e j))).map e by
      simp [U, Finset.filter_map], Finset.card_map]
    have hfilter (j : Fin d) : left (e j) ↔ d ≤ 4 * (j : ℕ) ∧ 4 * (j : ℕ) ≤ 3 * d :=
      disk_root_left hd j (hz j).1 (hz j).2
    simpa only [hfilter] using (sector_count hd)
  have hprod : poly d * (X - C 1) ≠ 0 := by
    rw [augmented_eq]
    exact augmented_ne_zero d
  rw [← augmented_eq, Polynomial.roots_mul hprod, Polynomial.roots_X_sub_C,
    Multiset.filter_add] at hcount
  norm_num [left, Multiset.filter_singleton] at hcount
  exact hcount

theorem OMA.solution : type_of% @OMA.S_oeis_a083219.main := by
  classical
  intro n
  cases n with
  | zero =>
    change ((poly 1).roots.filter (fun z : ℂ => z.re < 0)).card = 0
    have h : poly 1 = X - C 1 := by simp [poly]
    rw [h, Polynomial.roots_X_sub_C]
    simp
  | succ n =>
    simpa using (root_count (d := n.succ + 1) (by omega))


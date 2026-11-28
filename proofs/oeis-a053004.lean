import OMAStatements.S_oeis_a053004

open Filter Topology OMA.S_oeis_a053004

private noncomputable def qVal : ℝ := Real.exp (-Real.pi)

private noncomputable def T3 (c : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-c * (n : ℝ) ^ 2)

private noncomputable def T4 (c : ℝ) : ℝ :=
  ∑' n : ℤ, (-1 : ℝ) ^ n.natAbs * Real.exp (-c * (n : ℝ) ^ 2)

private noncomputable def T2 (c : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-c * ((n : ℝ) + 1 / 2) ^ 2)

private lemma qVal_pos : 0 < qVal := Real.exp_pos _

private lemma eighteen_mul_qVal_lt_one : 18 * qVal < 1 := by
  have hexp1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hpow : (18 : ℝ) < Real.exp 3 := by
    calc
      (18 : ℝ) < (2.7 : ℝ) ^ 3 := by norm_num
      _ < (Real.exp 1) ^ 3 := by gcongr
      _ = Real.exp ((3 : ℕ) : ℝ) := Real.exp_one_pow 3
      _ = Real.exp 3 := by norm_num
  have hexp_pi : (18 : ℝ) < Real.exp Real.pi :=
    hpow.trans (Real.exp_lt_exp.mpr Real.pi_gt_three)
  have hpos : 0 < Real.exp Real.pi := Real.exp_pos Real.pi
  calc
    18 * qVal = 18 * (Real.exp Real.pi)⁻¹ := by rw [qVal, Real.exp_neg]
    _ < Real.exp Real.pi * (Real.exp Real.pi)⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ hpos.ne'

private lemma summable_T3 {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-c * (n : ℝ) ^ 2) := by
  have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hnat : Summable fun m : ℕ => Real.exp (-c * (m : ℝ) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun m => ?_)
      (summable_geometric_of_lt_one hr0 hr1)
    have hm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by
      cases m with
      | zero => norm_num
      | succ m =>
        have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by norm_cast; omega
        nlinarith
    calc
      Real.exp (-c * (m : ℝ) ^ 2) ≤ Real.exp (-c * (m : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.exp ((m : ℕ) * (-c)) := by congr 1; ring
      _ = (Real.exp (-c)) ^ m := Real.exp_nat_mul (-c) m
  have hneg : Summable fun m : ℕ => Real.exp (-c * ((-m : ℤ) : ℝ) ^ 2) := by
    simpa only [Int.cast_neg, Int.cast_natCast, neg_sq] using hnat
  exact summable_int_iff_summable_nat_and_neg.mpr ⟨by simpa using hnat, hneg⟩

private lemma summable_T4 {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => (-1 : ℝ) ^ n.natAbs * Real.exp (-c * (n : ℝ) ^ 2) := by
  refine ((summable_T3 hc).norm.congr fun n => ?_).of_norm
  simp only [Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul]

private lemma summable_prod_of_norm {α β : Type*} {f : α → ℝ} {g : β → ℝ}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun y => ‖g y‖) :
    Summable fun p : α × β => f p.1 * g p.2 := by
  have hnorm : Summable fun p : α × β => ‖f p.1 * g p.2‖ := by
    refine (summable_prod_of_nonneg fun p => norm_nonneg _).mpr ?_
    refine ⟨fun x => ?_, ?_⟩
    · refine (hg.mul_left ‖f x‖).congr fun y => ?_
      exact (norm_mul (f x) (g y)).symm
    · have htsum : ∀ x, (∑' y, ‖f x * g y‖) = ‖f x‖ * (∑' y, ‖g y‖) := fun x => by
        rw [← tsum_mul_left]
        exact tsum_congr fun y => norm_mul (f x) (g y)
      simp_rw [htsum]
      exact hf.mul_right _
  exact hnorm.of_norm

private def evenOddIntEquiv : ℤ ⊕ ℤ ≃ ℤ where
  toFun := Sum.elim (fun n => 2 * n) (fun n => 2 * n + 1)
  invFun m := if m % 2 = 0 then Sum.inl (m / 2) else Sum.inr ((m - 1) / 2)
  left_inv x := by
    rcases x with n | n
    · dsimp only [Sum.elim_inl]
      split_ifs
      · congr 1; omega
      · omega
    · dsimp only [Sum.elim_inr]
      split_ifs
      · omega
      · congr 1; omega
  right_inv m := by
    dsimp only
    split_ifs <;> dsimp only [Sum.elim_inl, Sum.elim_inr] <;> omega

private lemma summable_T2 {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-c * ((n : ℝ) + 1 / 2) ^ 2) := by
  have hsum := (evenOddIntEquiv.summable_iff).mpr (summable_T3 (by linarith : 0 < c / 4))
  refine (hsum.comp_injective Sum.inr_injective).congr fun n => ?_
  simp only [Function.comp_apply, evenOddIntEquiv, Equiv.coe_fn_mk, Sum.elim_inr, Int.cast_add,
    Int.cast_mul, Int.cast_ofNat, Int.cast_one]
  congr 1
  ring

private lemma T3_div_four {c : ℝ} (hc : 0 < c) : T3 (c / 4) = T3 c + T2 c := by
  have hsum := (evenOddIntEquiv.summable_iff (f := fun m : ℤ =>
    Real.exp (-(c / 4) * (m : ℝ) ^ 2))).mpr (summable_T3 (by linarith))
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2 := hsum.comp_injective Sum.inr_injective
  rw [T3, ← evenOddIntEquiv.tsum_eq (fun m : ℤ => Real.exp (-(c / 4) * (m : ℝ) ^ 2))]
  change (∑' x : ℤ ⊕ ℤ,
    ((fun m : ℤ => Real.exp (-(c / 4) * (m : ℝ) ^ 2)) ∘ evenOddIntEquiv) x) = T3 c + T2 c
  rw [h1.tsum_sum h2, T3, T2]
  congr 1
  · refine tsum_congr fun n => ?_
    simp only [Function.comp_apply, evenOddIntEquiv, Equiv.coe_fn_mk, Sum.elim_inl, Int.cast_mul,
      Int.cast_ofNat]
    congr 1
    ring
  · refine tsum_congr fun n => ?_
    simp only [Function.comp_apply, evenOddIntEquiv, Equiv.coe_fn_mk, Sum.elim_inr, Int.cast_add,
      Int.cast_mul, Int.cast_ofNat, Int.cast_one]
    congr 1
    ring

private lemma T4_split {c : ℝ} (hc : 0 < c) : T4 c = T3 (4 * c) - T2 (4 * c) := by
  have hsum := (evenOddIntEquiv.summable_iff (f := fun m : ℤ =>
    (-1 : ℝ) ^ m.natAbs * Real.exp (-c * (m : ℝ) ^ 2))).mpr (summable_T4 hc)
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2 := hsum.comp_injective Sum.inr_injective
  rw [T4, ← evenOddIntEquiv.tsum_eq (fun m : ℤ => (-1 : ℝ) ^ m.natAbs * Real.exp (-c * (m : ℝ) ^ 2))]
  change (∑' x : ℤ ⊕ ℤ,
    ((fun m : ℤ => (-1 : ℝ) ^ m.natAbs * Real.exp (-c * (m : ℝ) ^ 2)) ∘ evenOddIntEquiv) x) =
      T3 (4 * c) - T2 (4 * c)
  rw [h1.tsum_sum h2, T3, T2, sub_eq_add_neg, ← tsum_neg]
  congr 1
  · refine tsum_congr fun n => ?_
    simp only [Function.comp_apply, evenOddIntEquiv, Equiv.coe_fn_mk, Sum.elim_inl]
    have hev : Even (2 * n).natAbs := Int.natAbs_even.mpr ⟨n, by ring⟩
    rw [hev.neg_one_pow, one_mul]
    simp only [Int.cast_mul, Int.cast_ofNat]
    congr 1
    ring
  · refine tsum_congr fun n => ?_
    simp only [Function.comp_apply, evenOddIntEquiv, Equiv.coe_fn_mk, Sum.elim_inr]
    have hodd : Odd (2 * n + 1).natAbs := Int.natAbs_odd.mpr ⟨n, by ring⟩
    rw [hodd.neg_one_pow, neg_one_mul]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one]
    congr 2
    ring

private lemma T2_pi_eq_T4_pi : T2 Real.pi = T4 Real.pi := by
  have h1 := T3_div_four Real.pi_pos
  have h2 := T3_div_four (by positivity : 0 < 4 * Real.pi)
  have h4div : 4 * Real.pi / 4 = Real.pi := by ring
  rw [h4div] at h2
  have h3 := T4_split Real.pi_pos
  have hpois := Real.tsum_exp_neg_mul_int_sq (by norm_num : (0 : ℝ) < 4)
  have hL : (∑' n : ℤ, Real.exp (-Real.pi * 4 * (n : ℝ) ^ 2)) = T3 (4 * Real.pi) := by
    rw [T3]
    refine tsum_congr fun n => ?_
    congr 1
    ring
  have hR : (∑' n : ℤ, Real.exp (-Real.pi / 4 * (n : ℝ) ^ 2)) = T3 (Real.pi / 4) := by
    rw [T3]
    refine tsum_congr fun n => ?_
    congr 1
    ring
  have hsqrt4 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
    rw [← Real.sqrt_eq_rpow]
    norm_num
  rw [hL, hR, hsqrt4] at hpois
  linarith

private lemma neg_one_pow_natAbs_add (a b : ℤ) :
    (-1 : ℝ) ^ (a + b).natAbs = (-1 : ℝ) ^ a.natAbs * (-1 : ℝ) ^ b.natAbs := by
  rcases Int.even_or_odd a with ⟨ka, rfl⟩ | ⟨ka, rfl⟩ <;>
    rcases Int.even_or_odd b with ⟨kb, rfl⟩ | ⟨kb, rfl⟩
  · have h1 : Even (ka + ka).natAbs := Int.natAbs_even.mpr ⟨ka, rfl⟩
    have h2 : Even (kb + kb).natAbs := Int.natAbs_even.mpr ⟨kb, rfl⟩
    have h3 : Even (ka + ka + (kb + kb)).natAbs := Int.natAbs_even.mpr ⟨ka + kb, by ring⟩
    rw [h1.neg_one_pow, h2.neg_one_pow, h3.neg_one_pow, one_mul]
  · have h1 : Even (ka + ka).natAbs := Int.natAbs_even.mpr ⟨ka, rfl⟩
    have h2 : Odd (2 * kb + 1).natAbs := Int.natAbs_odd.mpr ⟨kb, rfl⟩
    have h3 : Odd (ka + ka + (2 * kb + 1)).natAbs := Int.natAbs_odd.mpr ⟨ka + kb, by ring⟩
    rw [h1.neg_one_pow, h2.neg_one_pow, h3.neg_one_pow, one_mul]
  · have h1 : Odd (2 * ka + 1).natAbs := Int.natAbs_odd.mpr ⟨ka, rfl⟩
    have h2 : Even (kb + kb).natAbs := Int.natAbs_even.mpr ⟨kb, rfl⟩
    have h3 : Odd (2 * ka + 1 + (kb + kb)).natAbs := Int.natAbs_odd.mpr ⟨ka + kb, by ring⟩
    rw [h1.neg_one_pow, h2.neg_one_pow, h3.neg_one_pow, mul_one]
  · have h1 : Odd (2 * ka + 1).natAbs := Int.natAbs_odd.mpr ⟨ka, rfl⟩
    have h2 : Odd (2 * kb + 1).natAbs := Int.natAbs_odd.mpr ⟨kb, rfl⟩
    have h3 : Even (2 * ka + 1 + (2 * kb + 1)).natAbs := Int.natAbs_even.mpr ⟨ka + kb + 1, by ring⟩
    rw [h1.neg_one_pow, h2.neg_one_pow, h3.neg_one_pow]
    norm_num

private lemma neg_one_pow_natAbs_sub (a b : ℤ) :
    (-1 : ℝ) ^ (a - b).natAbs = (-1 : ℝ) ^ a.natAbs * (-1 : ℝ) ^ b.natAbs := by
  have hb : (-b).natAbs = b.natAbs := Int.natAbs_neg b
  rw [sub_eq_add_neg, neg_one_pow_natAbs_add, hb]

private def parityPairEquiv : (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun := Sum.elim (fun p => (p.1 + p.2, p.1 - p.2)) (fun p => (p.1 + p.2 + 1, p.1 - p.2))
  invFun q := if (q.1 + q.2) % 2 = 0 then Sum.inl ((q.1 + q.2) / 2, (q.1 - q.2) / 2)
    else Sum.inr ((q.1 + q.2 - 1) / 2, (q.1 - q.2 - 1) / 2)
  left_inv x := by
    rcases x with ⟨u, v⟩ | ⟨u, v⟩
    · dsimp only [Sum.elim_inl]
      split_ifs
      · congr 1; ext <;> omega
      · omega
    · dsimp only [Sum.elim_inr]
      split_ifs
      · omega
      · congr 1; ext <;> omega
  right_inv q := by
    dsimp only
    split_ifs <;> dsimp only [Sum.elim_inl, Sum.elim_inr] <;> ext <;> omega

private lemma T3_sq_eq_tsum {c : ℝ} (hc : 0 < c) :
    (T3 c) ^ 2 = ∑' p : ℤ × ℤ, Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
  have h := summable_T3 hc
  have hp := summable_prod_of_norm h.norm h.norm
  have hsq : (T3 c) ^ 2 = ∑' p : ℤ × ℤ,
      Real.exp (-c * (p.1 : ℝ) ^ 2) * Real.exp (-c * (p.2 : ℝ) ^ 2) := by
    rw [sq, T3, hp.tsum_prod]
    simp only [tsum_mul_left, tsum_mul_right]
  rw [hsq]
  refine tsum_congr fun p => ?_
  rw [← Real.exp_add]
  congr 1
  ring

private lemma T2_sq_eq_tsum {c : ℝ} (hc : 0 < c) :
    (T2 c) ^ 2 = ∑' p : ℤ × ℤ, Real.exp (-c * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2)) := by
  have h := summable_T2 hc
  have hp := summable_prod_of_norm h.norm h.norm
  have hsq : (T2 c) ^ 2 = ∑' p : ℤ × ℤ,
      Real.exp (-c * ((p.1 : ℝ) + 1 / 2) ^ 2) * Real.exp (-c * ((p.2 : ℝ) + 1 / 2) ^ 2) := by
    rw [sq, T2, hp.tsum_prod]
    simp only [tsum_mul_left, tsum_mul_right]
  rw [hsq]
  refine tsum_congr fun p => ?_
  rw [← Real.exp_add]
  congr 1
  ring

private lemma T4_sq_eq_tsum {c : ℝ} (hc : 0 < c) :
    (T4 c) ^ 2 = ∑' p : ℤ × ℤ,
      (-1 : ℝ) ^ (p.1 + p.2).natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
  have h := summable_T4 hc
  have hp := summable_prod_of_norm h.norm h.norm
  have hsq : (T4 c) ^ 2 = ∑' p : ℤ × ℤ,
      ((-1 : ℝ) ^ p.1.natAbs * Real.exp (-c * (p.1 : ℝ) ^ 2)) *
        ((-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * (p.2 : ℝ) ^ 2)) := by
    rw [sq, T4, hp.tsum_prod]
    simp only [tsum_mul_left, tsum_mul_right]
  rw [hsq]
  refine tsum_congr fun p => ?_
  rw [neg_one_pow_natAbs_add]
  calc
    (-1 : ℝ) ^ p.1.natAbs * Real.exp (-c * (p.1 : ℝ) ^ 2) *
        ((-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * (p.2 : ℝ) ^ 2))
        = (-1 : ℝ) ^ p.1.natAbs * (-1 : ℝ) ^ p.2.natAbs *
          (Real.exp (-c * (p.1 : ℝ) ^ 2) * Real.exp (-c * (p.2 : ℝ) ^ 2)) := by ring
    _ = (-1 : ℝ) ^ p.1.natAbs * (-1 : ℝ) ^ p.2.natAbs *
          Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
        rw [← Real.exp_add]
        congr 2
        ring

private lemma T3_sq_split {c : ℝ} (hc : 0 < c) :
    (T3 c) ^ 2 = (T3 (2 * c)) ^ 2 + (T2 (2 * c)) ^ 2 := by
  let f : ℤ × ℤ → ℝ := fun p => Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))
  have hf : Summable f := by
    have h := summable_T3 hc
    refine (summable_prod_of_norm h.norm h.norm).congr fun p => ?_
    simp only [f, ← Real.exp_add]
    congr 1
    ring
  have hsum := (parityPairEquiv.summable_iff (f := f)).mpr hf
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2 := hsum.comp_injective Sum.inr_injective
  rw [T3_sq_eq_tsum hc]
  change (∑' p : ℤ × ℤ, f p) = _
  rw [← parityPairEquiv.tsum_eq f]
  change (∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ), (f ∘ parityPairEquiv) x) = _
  rw [h1.tsum_sum h2, T3_sq_eq_tsum (by linarith), T2_sq_eq_tsum (by linarith)]
  congr 1
  · refine tsum_congr fun p => ?_
    simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inl, f,
      Int.cast_add, Int.cast_sub]
    congr 1
    ring
  · refine tsum_congr fun p => ?_
    simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inr, f,
      Int.cast_add, Int.cast_sub, Int.cast_one]
    congr 1
    ring

private lemma T4_sq_split {c : ℝ} (hc : 0 < c) :
    (T4 c) ^ 2 = (T3 (2 * c)) ^ 2 - (T2 (2 * c)) ^ 2 := by
  let f : ℤ × ℤ → ℝ := fun p =>
    (-1 : ℝ) ^ (p.1 + p.2).natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))
  have hf : Summable f := by
    have h := summable_T4 hc
    refine (summable_prod_of_norm h.norm h.norm).congr fun p => ?_
    simp only [f, neg_one_pow_natAbs_add]
    calc
      (-1 : ℝ) ^ p.1.natAbs * Real.exp (-c * (p.1 : ℝ) ^ 2) *
          ((-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * (p.2 : ℝ) ^ 2))
          = (-1 : ℝ) ^ p.1.natAbs * (-1 : ℝ) ^ p.2.natAbs *
            (Real.exp (-c * (p.1 : ℝ) ^ 2) * Real.exp (-c * (p.2 : ℝ) ^ 2)) := by ring
      _ = (-1 : ℝ) ^ p.1.natAbs * (-1 : ℝ) ^ p.2.natAbs *
            Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
          rw [← Real.exp_add]
          congr 2
          ring
  have hsum := (parityPairEquiv.summable_iff (f := f)).mpr hf
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2 := hsum.comp_injective Sum.inr_injective
  rw [T4_sq_eq_tsum hc]
  change (∑' p : ℤ × ℤ, f p) = _
  rw [← parityPairEquiv.tsum_eq f]
  change (∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ), (f ∘ parityPairEquiv) x) = _
  rw [h1.tsum_sum h2, T3_sq_eq_tsum (by linarith), T2_sq_eq_tsum (by linarith), sub_eq_add_neg,
    ← tsum_neg]
  congr 1
  · refine tsum_congr fun p => ?_
    simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inl, f]
    have hev : Even (p.1 + p.2 + (p.1 - p.2)).natAbs := Int.natAbs_even.mpr ⟨p.1, by ring⟩
    rw [hev.neg_one_pow, one_mul]
    simp only [Int.cast_add, Int.cast_sub]
    congr 1
    ring
  · refine tsum_congr fun p => ?_
    simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inr, f]
    have hodd : Odd (p.1 + p.2 + 1 + (p.1 - p.2)).natAbs := Int.natAbs_odd.mpr ⟨p.1, by ring⟩
    rw [hodd.neg_one_pow, neg_one_mul]
    simp only [Int.cast_add, Int.cast_sub, Int.cast_one]
    congr 2
    ring

private lemma T3_sq_add_T4_sq_div_two {c : ℝ} (hc : 0 < c) :
    ((T3 c) ^ 2 + (T4 c) ^ 2) / 2 = (T3 (2 * c)) ^ 2 := by
  linarith [T3_sq_split hc, T4_sq_split hc]

private lemma tsum_alt_T2_eq_zero {c : ℝ} :
    (∑' u : ℤ, (-1 : ℝ) ^ u.natAbs * Real.exp (-c * ((u : ℝ) + 1 / 2) ^ 2)) = 0 := by
  let σ : ℤ ≃ ℤ :=
    { toFun := fun u => -(u + 1)
      invFun := fun u => -(u + 1)
      left_inv := fun u => by ring
      right_inv := fun u => by ring }
  let g : ℤ → ℝ := fun u => (-1 : ℝ) ^ u.natAbs * Real.exp (-c * ((u : ℝ) + 1 / 2) ^ 2)
  have hneg : ∀ u : ℤ, g (σ u) = -g u := by
    intro u
    simp only [g, σ, Equiv.coe_fn_mk]
    have hpar : (-1 : ℝ) ^ (-(u + 1)).natAbs = -(-1 : ℝ) ^ u.natAbs := by
      rw [Int.natAbs_neg, neg_one_pow_natAbs_add]
      norm_num
    rw [hpar]
    have hsq : ((-(u + 1) : ℤ) : ℝ) + 1 / 2 = -((u : ℝ) + 1 / 2) := by push_cast; ring
    rw [hsq, neg_sq]
    ring
  have heq : (∑' u : ℤ, g u) = -(∑' u : ℤ, g u) := by
    calc
      (∑' u : ℤ, g u) = ∑' u : ℤ, g (σ u) := (σ.tsum_eq g).symm
      _ = ∑' u : ℤ, -g u := tsum_congr hneg
      _ = -(∑' u : ℤ, g u) := tsum_neg
  linarith

private lemma T3_mul_T4 {c : ℝ} (hc : 0 < c) :
    T3 c * T4 c = (T4 (2 * c)) ^ 2 := by
  let f : ℤ × ℤ → ℝ := fun p =>
    (-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))
  have hprod : T3 c * T4 c = ∑' p : ℤ × ℤ, f p := by
    have hp := summable_prod_of_norm (summable_T3 hc).norm (summable_T4 hc).norm
    have h1 : T3 c * T4 c = ∑' p : ℤ × ℤ,
        Real.exp (-c * (p.1 : ℝ) ^ 2) * ((-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * (p.2 : ℝ) ^ 2)) := by
      rw [T3, T4, hp.tsum_prod]
      simp only [tsum_mul_left, tsum_mul_right]
    rw [h1]
    refine tsum_congr fun p => ?_
    simp only [f]
    calc
      Real.exp (-c * (p.1 : ℝ) ^ 2) * ((-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * (p.2 : ℝ) ^ 2))
          = (-1 : ℝ) ^ p.2.natAbs *
            (Real.exp (-c * (p.1 : ℝ) ^ 2) * Real.exp (-c * (p.2 : ℝ) ^ 2)) := by ring
      _ = (-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
          rw [← Real.exp_add]
          congr 2
          ring
  have hf : Summable f := by
    refine (summable_prod_of_norm (summable_T3 hc).norm (summable_T4 hc).norm).congr fun p => ?_
    simp only [f]
    calc
      Real.exp (-c * (p.1 : ℝ) ^ 2) * ((-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * (p.2 : ℝ) ^ 2))
          = (-1 : ℝ) ^ p.2.natAbs *
            (Real.exp (-c * (p.1 : ℝ) ^ 2) * Real.exp (-c * (p.2 : ℝ) ^ 2)) := by ring
      _ = (-1 : ℝ) ^ p.2.natAbs * Real.exp (-c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
          rw [← Real.exp_add]
          congr 2
          ring
  have hsum := (parityPairEquiv.summable_iff (f := f)).mpr hf
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2 := hsum.comp_injective Sum.inr_injective
  rw [hprod, ← parityPairEquiv.tsum_eq f]
  change (∑' x : (ℤ × ℤ) ⊕ (ℤ × ℤ), (f ∘ parityPairEquiv) x) = _
  rw [h1.tsum_sum h2]
  have hinl : (∑' p : ℤ × ℤ, (f ∘ parityPairEquiv) (Sum.inl p)) = (T4 (2 * c)) ^ 2 := by
    rw [T4_sq_eq_tsum (by linarith)]
    refine tsum_congr fun p => ?_
    simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inl, f,
      neg_one_pow_natAbs_sub, neg_one_pow_natAbs_add, Int.cast_add, Int.cast_sub]
    congr 2
    ring
  have hinr : (∑' p : ℤ × ℤ, (f ∘ parityPairEquiv) (Sum.inr p)) = 0 := by
    let g : ℤ → ℝ := fun u => (-1 : ℝ) ^ u.natAbs * Real.exp (-(2 * c) * ((u : ℝ) + 1 / 2) ^ 2)
    have hg : Summable fun u => ‖g u‖ := by
      refine (summable_T2 (by linarith : 0 < 2 * c)).norm.congr fun u => ?_
      simp only [g, Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul]
    have hprod_g := summable_prod_of_norm hg hg
    have hterm : ∀ p : ℤ × ℤ, (f ∘ parityPairEquiv) (Sum.inr p) = g p.1 * g p.2 := fun p => by
      simp only [Function.comp_apply, parityPairEquiv, Equiv.coe_fn_mk, Sum.elim_inr, f, g,
        neg_one_pow_natAbs_sub, Int.cast_add, Int.cast_sub, Int.cast_one]
      calc
        (-1 : ℝ) ^ p.1.natAbs * (-1 : ℝ) ^ p.2.natAbs *
            Real.exp (-c * ((↑p.1 + ↑p.2 + 1) ^ 2 + (↑p.1 - ↑p.2) ^ 2))
            = (-1 : ℝ) ^ p.1.natAbs * (-1 : ℝ) ^ p.2.natAbs *
              (Real.exp (-(2 * c) * (↑p.1 + 1 / 2) ^ 2) *
                Real.exp (-(2 * c) * (↑p.2 + 1 / 2) ^ 2)) := by
              rw [← Real.exp_add]
              congr 2
              ring
        _ = (-1 : ℝ) ^ p.1.natAbs * Real.exp (-(2 * c) * (↑p.1 + 1 / 2) ^ 2) *
              ((-1 : ℝ) ^ p.2.natAbs * Real.exp (-(2 * c) * (↑p.2 + 1 / 2) ^ 2)) := by ring
    rw [tsum_congr hterm, hprod_g.tsum_prod]
    simp only [tsum_mul_left, g, tsum_alt_T2_eq_zero, mul_zero, tsum_zero]
  rw [hinl, hinr, add_zero]

private def intSplitEquiv : Unit ⊕ (ℕ ⊕ ℕ) ≃ ℤ where
  toFun := Sum.elim (fun _ => 0) (Sum.elim (fun r => ((r + 1 : ℕ) : ℤ)) (fun r => -((r + 1 : ℕ) : ℤ)))
  invFun z :=
    if z = 0 then Sum.inl ()
    else if 0 < z then Sum.inr (Sum.inl (z.natAbs - 1))
    else Sum.inr (Sum.inr (z.natAbs - 1))
  left_inv x := by
    rcases x with ⟨⟩ | (r | r)
    · dsimp only [Sum.elim_inl]
      split_ifs <;> first | rfl | omega
    · dsimp only [Sum.elim_inr, Sum.elim_inl]
      split_ifs <;> first | omega | congr 2
    · dsimp only [Sum.elim_inr, Sum.elim_inr]
      split_ifs <;> first | omega | congr 2
  right_inv z := by
    dsimp only
    split_ifs with h1 h2
    · exact h1.symm
    · dsimp only [Sum.elim_inr, Sum.elim_inl]; omega
    · dsimp only [Sum.elim_inr, Sum.elim_inr]; omega

private lemma T3_eq_one_add_two_mul {c : ℝ} (hc : 0 < c) :
    T3 c = 1 + 2 * ∑' r : ℕ, Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) := by
  let f : ℤ → ℝ := fun n => Real.exp (-c * (n : ℝ) ^ 2)
  have hsum := (intSplitEquiv.summable_iff (f := f)).mpr (summable_T3 hc)
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2 := hsum.comp_injective Sum.inr_injective
  have h2a := h2.comp_injective Sum.inl_injective
  have h2b := h2.comp_injective Sum.inr_injective
  rw [T3, ← intSplitEquiv.tsum_eq f]
  change (∑' x : Unit ⊕ (ℕ ⊕ ℕ), (f ∘ intSplitEquiv) x) = _
  rw [h1.tsum_sum h2]
  have hl : (∑' u : Unit, (f ∘ intSplitEquiv) (Sum.inl u)) = 1 := by
    rw [tsum_fintype, Fintype.sum_unique]
    simp only [Function.comp_apply, intSplitEquiv, Equiv.coe_fn_mk, Sum.elim_inl, f,
      Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Real.exp_zero]
  have hr : (∑' y : ℕ ⊕ ℕ, (f ∘ intSplitEquiv) (Sum.inr y)) =
      2 * ∑' r : ℕ, Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) := by
    change (∑' y : ℕ ⊕ ℕ, ((f ∘ intSplitEquiv) ∘ Sum.inr) y) = _
    rw [h2a.tsum_sum h2b]
    have ha : (∑' r : ℕ, ((f ∘ intSplitEquiv) ∘ Sum.inr) (Sum.inl r)) =
        ∑' r : ℕ, Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) := by
      refine tsum_congr fun r => ?_
      simp only [Function.comp_apply, intSplitEquiv, Equiv.coe_fn_mk, Sum.elim_inr, Sum.elim_inl,
        f, Int.cast_natCast]
    have hb : (∑' r : ℕ, ((f ∘ intSplitEquiv) ∘ Sum.inr) (Sum.inr r)) =
        ∑' r : ℕ, Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) := by
      refine tsum_congr fun r => ?_
      simp only [Function.comp_apply, intSplitEquiv, Equiv.coe_fn_mk, Sum.elim_inr, f,
        Int.cast_neg, Int.cast_natCast, neg_sq]
    rw [ha, hb]
    ring
  rw [hl, hr]

private lemma T4_eq_one_add_two_mul {c : ℝ} (hc : 0 < c) :
    T4 c = 1 + 2 * ∑' r : ℕ, (-1 : ℝ) ^ (r + 1) * Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) := by
  let f : ℤ → ℝ := fun n => (-1 : ℝ) ^ n.natAbs * Real.exp (-c * (n : ℝ) ^ 2)
  have hsum := (intSplitEquiv.summable_iff (f := f)).mpr (summable_T4 hc)
  have h1 := hsum.comp_injective Sum.inl_injective
  have h2 := hsum.comp_injective Sum.inr_injective
  have h2a := h2.comp_injective Sum.inl_injective
  have h2b := h2.comp_injective Sum.inr_injective
  rw [T4, ← intSplitEquiv.tsum_eq f]
  change (∑' x : Unit ⊕ (ℕ ⊕ ℕ), (f ∘ intSplitEquiv) x) = _
  rw [h1.tsum_sum h2]
  have hl : (∑' u : Unit, (f ∘ intSplitEquiv) (Sum.inl u)) = 1 := by
    rw [tsum_fintype, Fintype.sum_unique]
    simp only [Function.comp_apply, intSplitEquiv, Equiv.coe_fn_mk, Sum.elim_inl, f,
      Int.natAbs_zero, pow_zero, one_mul, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, Real.exp_zero]
  have hr : (∑' y : ℕ ⊕ ℕ, (f ∘ intSplitEquiv) (Sum.inr y)) =
      2 * ∑' r : ℕ, (-1 : ℝ) ^ (r + 1) * Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) := by
    change (∑' y : ℕ ⊕ ℕ, ((f ∘ intSplitEquiv) ∘ Sum.inr) y) = _
    rw [h2a.tsum_sum h2b]
    have ha : (∑' r : ℕ, ((f ∘ intSplitEquiv) ∘ Sum.inr) (Sum.inl r)) =
        ∑' r : ℕ, (-1 : ℝ) ^ (r + 1) * Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) := by
      refine tsum_congr fun r => ?_
      simp only [Function.comp_apply, intSplitEquiv, Equiv.coe_fn_mk, Sum.elim_inr, Sum.elim_inl,
        f, Int.natAbs_natCast, Int.cast_natCast]
    have hb : (∑' r : ℕ, ((f ∘ intSplitEquiv) ∘ Sum.inr) (Sum.inr r)) =
        ∑' r : ℕ, (-1 : ℝ) ^ (r + 1) * Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) := by
      refine tsum_congr fun r => ?_
      simp only [Function.comp_apply, intSplitEquiv, Equiv.coe_fn_mk, Sum.elim_inr, f,
        Int.natAbs_neg, Int.natAbs_natCast, Int.cast_neg, Int.cast_natCast, neg_sq]
    rw [ha, hb]
    ring
  rw [hl, hr]

private lemma tail_exp_sq_le {c : ℝ} (hc : 0 < c) (hexp : Real.exp (-c) < 1 / 2) :
    (∑' r : ℕ, Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2)) ≤ 2 * Real.exp (-c) := by
  have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c) < 1 := by linarith
  have hgeom : Summable fun r : ℕ => Real.exp (-c) * (Real.exp (-c)) ^ r :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hle : ∀ r : ℕ, Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) ≤
      Real.exp (-c) * (Real.exp (-c)) ^ r := fun r => by
    have hsq : ((r + 1 : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ 2 := by
      have h1 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by norm_cast; omega
      nlinarith
    calc
      Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) ≤ Real.exp (-c * ((r + 1 : ℕ) : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.exp (((r + 1 : ℕ) : ℝ) * (-c)) := by congr 1; ring
      _ = (Real.exp (-c)) ^ (r + 1) := Real.exp_nat_mul (-c) (r + 1)
      _ = Real.exp (-c) * (Real.exp (-c)) ^ r := by rw [pow_succ']
  have hsum_sq : Summable fun r : ℕ => Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hle hgeom
  have hts : (∑' r : ℕ, Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2)) ≤
      ∑' r : ℕ, Real.exp (-c) * (Real.exp (-c)) ^ r :=
    hsum_sq.tsum_le_tsum hle hgeom
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1] at hts
  have hinv : (1 - Real.exp (-c))⁻¹ ≤ 2 := by
    have hpos : (0 : ℝ) < 1 - Real.exp (-c) := by linarith
    rw [inv_le_comm₀ hpos (by norm_num)]
    linarith
  calc
    (∑' r : ℕ, Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2)) ≤ Real.exp (-c) * (1 - Real.exp (-c))⁻¹ := hts
    _ ≤ Real.exp (-c) * 2 := mul_le_mul_of_nonneg_left hinv hr0
    _ = 2 * Real.exp (-c) := by ring

private lemma T3_bounds {c : ℝ} (hc : 0 < c) (hexp : Real.exp (-c) < 1 / 2) :
    1 ≤ T3 c ∧ T3 c ≤ 1 + 4 * Real.exp (-c) := by
  rw [T3_eq_one_add_two_mul hc]
  have hnn : 0 ≤ ∑' r : ℕ, Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) :=
    tsum_nonneg fun _ => (Real.exp_pos _).le
  have hle := tail_exp_sq_le hc hexp
  constructor <;> linarith

private lemma T4_pos_of_ge_pi {c : ℝ} (hc : Real.pi ≤ c) : 0 < T4 c := by
  have hc_pos : 0 < c := lt_of_lt_of_le Real.pi_pos hc
  have hexp_le : Real.exp (-c) ≤ qVal := by
    rw [qVal]
    exact Real.exp_le_exp.mpr (by linarith)
  have hexp_lt : Real.exp (-c) < 1 / 18 := by linarith [eighteen_mul_qVal_lt_one]
  have hexp_half : Real.exp (-c) < 1 / 2 := by linarith
  have hsum_sq : Summable fun r : ℕ => Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) := by
    have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
    have hr1 : Real.exp (-c) < 1 := by linarith
    refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun r => ?_)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left (Real.exp (-c)))
    have hsq : ((r + 1 : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ 2 := by
      have h1 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by norm_cast; omega
      nlinarith
    calc
      Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) ≤ Real.exp (-c * ((r + 1 : ℕ) : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.exp (((r + 1 : ℕ) : ℝ) * (-c)) := by congr 1; ring
      _ = (Real.exp (-c)) ^ (r + 1) := Real.exp_nat_mul (-c) (r + 1)
      _ = Real.exp (-c) * (Real.exp (-c)) ^ r := by rw [pow_succ']
  have habs_le : |∑' r : ℕ, (-1 : ℝ) ^ (r + 1) * Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2)| ≤
      ∑' r : ℕ, Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) := by
    have hnorm : Summable fun r : ℕ =>
        ‖(-1 : ℝ) ^ (r + 1) * Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2)‖ := by
      refine hsum_sq.congr fun r => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul, abs_of_pos (Real.exp_pos _)]
    have h1 := norm_tsum_le_tsum_norm hnorm
    rw [Real.norm_eq_abs] at h1
    refine h1.trans_eq (tsum_congr fun r => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul, abs_of_pos (Real.exp_pos _)]
  have htail := tail_exp_sq_le hc_pos hexp_half
  have hneg : -(2 * Real.exp (-c)) ≤
      ∑' r : ℕ, (-1 : ℝ) ^ (r + 1) * Real.exp (-c * ((r + 1 : ℕ) : ℝ) ^ 2) := by
    linarith [(abs_le.mp (habs_le.trans htail)).1]
  rw [T4_eq_one_add_two_mul hc_pos]
  linarith

private lemma T3_pi_sq_eq_sqrt_two_mul_T4_pi_sq :
    (T3 Real.pi) ^ 2 = √2 * (T4 Real.pi) ^ 2 := by
  have hpois := Real.tsum_exp_neg_mul_int_sq (by norm_num : (0 : ℝ) < 2)
  have hL : (∑' n : ℤ, Real.exp (-Real.pi * 2 * (n : ℝ) ^ 2)) = T3 (2 * Real.pi) := by
    rw [T3]
    refine tsum_congr fun n => ?_
    congr 1
    ring
  have hR : (∑' n : ℤ, Real.exp (-Real.pi / 2 * (n : ℝ) ^ 2)) = T3 (2 * Real.pi / 4) := by
    rw [T3]
    refine tsum_congr fun n => ?_
    congr 1
    ring
  rw [hL, hR, ← Real.sqrt_eq_rpow 2, T3_div_four (by positivity : 0 < 2 * Real.pi)] at hpois
  have hsq : √2 ≠ 0 := by positivity
  have hB : T2 (2 * Real.pi) = (√2 - 1) * T3 (2 * Real.pi) := by
    have hmul : √2 * T3 (2 * Real.pi) = T3 (2 * Real.pi) + T2 (2 * Real.pi) := by
      calc
        √2 * T3 (2 * Real.pi) = √2 * (1 / √2 * (T3 (2 * Real.pi) + T2 (2 * Real.pi))) := by
          rw [← hpois]
        _ = T3 (2 * Real.pi) + T2 (2 * Real.pi) := by field_simp [hsq]
    linarith
  have hsq2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [T3_sq_split Real.pi_pos, T4_sq_split Real.pi_pos, hB]
  calc
    (T3 (2 * Real.pi)) ^ 2 + ((√2 - 1) * T3 (2 * Real.pi)) ^ 2
        = (2 + √2 ^ 2 - 2 * √2) * (T3 (2 * Real.pi)) ^ 2 := by ring
    _ = (4 - 2 * √2) * (T3 (2 * Real.pi)) ^ 2 := by rw [hsq2]; ring
    _ = (2 * √2 ^ 2 - 2 * √2) * (T3 (2 * Real.pi)) ^ 2 := by rw [hsq2]; ring
    _ = √2 * ((2 * √2 - 2) * (T3 (2 * Real.pi)) ^ 2) := by ring
    _ = √2 * ((2 * √2 - √2 ^ 2) * (T3 (2 * Real.pi)) ^ 2) := by rw [hsq2]
    _ = √2 * ((T3 (2 * Real.pi)) ^ 2 - ((√2 - 1) * T3 (2 * Real.pi)) ^ 2) := by ring

private lemma agmSeq_succ_eq (k : ℕ) :
    agmSeq 1 √2 (k + 1) =
      ((T3 ((2 : ℝ) ^ (k + 1) * Real.pi)) ^ 2 / (T4 Real.pi) ^ 2,
        (T4 ((2 : ℝ) ^ (k + 1) * Real.pi)) ^ 2 / (T4 Real.pi) ^ 2) := by
  have hT4pi_pos : 0 < T4 Real.pi := T4_pos_of_ge_pi le_rfl
  have hT3pi_pos : 0 < T3 Real.pi := by
    have hq : Real.exp (-Real.pi) = qVal := rfl
    have h := (T3_bounds Real.pi_pos (by linarith [eighteen_mul_qVal_lt_one, hq])).1
    linarith
  induction k with
  | zero =>
    have hratio : √2 = (T3 Real.pi) ^ 2 / (T4 Real.pi) ^ 2 := by
      rw [T3_pi_sq_eq_sqrt_two_mul_T4_pi_sq]
      field_simp [hT4pi_pos.ne']
    have h1 : (1 : ℝ) = (T4 Real.pi) ^ 2 / (T4 Real.pi) ^ 2 := by
      field_simp [hT4pi_pos.ne']
    simp only [agmSeq, zero_add, pow_one]
    ext
    · dsimp only
      rw [h1, hratio, ← add_div, div_div, mul_comm ((T4 Real.pi) ^ 2) 2, ← div_div,
        add_comm ((T4 Real.pi) ^ 2), T3_sq_add_T4_sq_div_two Real.pi_pos]
    · dsimp only
      rw [one_mul, hratio]
      have hsq : (T3 Real.pi) ^ 2 / (T4 Real.pi) ^ 2 =
          ((T3 Real.pi * T4 Real.pi) / (T4 Real.pi) ^ 2) ^ 2 := by
        field_simp [hT4pi_pos.ne']
      rw [hsq, Real.sqrt_sq (by positivity), T3_mul_T4 Real.pi_pos]
  | succ k ih =>
    have hc_ge : Real.pi ≤ (2 : ℝ) ^ (k + 1) * Real.pi := by
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
      nlinarith [Real.pi_pos]
    have hc_pos : 0 < (2 : ℝ) ^ (k + 1) * Real.pi := lt_of_lt_of_le Real.pi_pos hc_ge
    have hT4_pos : 0 < T4 ((2 : ℝ) ^ (k + 1) * Real.pi) := T4_pos_of_ge_pi hc_ge
    have hT3_pos : 0 < T3 ((2 : ℝ) ^ (k + 1) * Real.pi) := by
      have hexp : Real.exp (-((2 : ℝ) ^ (k + 1) * Real.pi)) < 1 / 2 := by
        have hle : Real.exp (-((2 : ℝ) ^ (k + 1) * Real.pi)) ≤ qVal := by
          rw [qVal]
          exact Real.exp_le_exp.mpr (by linarith)
        linarith [eighteen_mul_qVal_lt_one]
      linarith [(T3_bounds hc_pos hexp).1]
    have hpow : 2 * ((2 : ℝ) ^ (k + 1) * Real.pi) = (2 : ℝ) ^ (k + 2) * Real.pi := by
      rw [pow_succ']
      ring
    change (((agmSeq 1 √2 (k + 1)).1 + (agmSeq 1 √2 (k + 1)).2) / 2,
      Real.sqrt ((agmSeq 1 √2 (k + 1)).1 * (agmSeq 1 √2 (k + 1)).2)) = _
    rw [ih]
    ext
    · dsimp only
      rw [← add_div, div_div, mul_comm ((T4 Real.pi) ^ 2) 2, ← div_div,
        T3_sq_add_T4_sq_div_two hc_pos, hpow]
    · dsimp only
      have hsq : ((T3 ((2 : ℝ) ^ (k + 1) * Real.pi)) ^ 2 / (T4 Real.pi) ^ 2) *
          ((T4 ((2 : ℝ) ^ (k + 1) * Real.pi)) ^ 2 / (T4 Real.pi) ^ 2) =
          ((T3 ((2 : ℝ) ^ (k + 1) * Real.pi) * T4 ((2 : ℝ) ^ (k + 1) * Real.pi)) /
            (T4 Real.pi) ^ 2) ^ 2 := by
        ring
      rw [hsq, Real.sqrt_sq (by positivity), T3_mul_T4 hc_pos, hpow]

private lemma tendsto_T3_two_pow :
    Tendsto (fun n : ℕ => T3 ((2 : ℝ) ^ n * Real.pi)) atTop (𝓝 1) := by
  have hhi : Tendsto (fun n : ℕ => (1 : ℝ) + 4 * qVal ^ n) atTop (𝓝 (1 + 4 * 0)) := by
    refine tendsto_const_nhds.add (tendsto_const_nhds.mul ?_)
    exact tendsto_pow_atTop_nhds_zero_of_lt_one qVal_pos.le (by linarith [eighteen_mul_qVal_lt_one])
  rw [mul_zero, add_zero] at hhi
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hhi (fun n => ?_) (fun n => ?_)
  · have hc_ge : Real.pi ≤ (2 : ℝ) ^ n * Real.pi := by
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      nlinarith [Real.pi_pos]
    have hexp : Real.exp (-((2 : ℝ) ^ n * Real.pi)) < 1 / 2 := by
      have hle : Real.exp (-((2 : ℝ) ^ n * Real.pi)) ≤ qVal := by
        rw [qVal]
        exact Real.exp_le_exp.mpr (by linarith)
      linarith [eighteen_mul_qVal_lt_one]
    exact (T3_bounds (lt_of_lt_of_le Real.pi_pos hc_ge) hexp).1
  · have hc_ge : Real.pi ≤ (2 : ℝ) ^ n * Real.pi := by
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      nlinarith [Real.pi_pos]
    have hexp : Real.exp (-((2 : ℝ) ^ n * Real.pi)) < 1 / 2 := by
      have hle : Real.exp (-((2 : ℝ) ^ n * Real.pi)) ≤ qVal := by
        rw [qVal]
        exact Real.exp_le_exp.mpr (by linarith)
      linarith [eighteen_mul_qVal_lt_one]
    have hbd := (T3_bounds (lt_of_lt_of_le Real.pi_pos hc_ge) hexp).2
    have hpow_ge : (n : ℝ) ≤ (2 : ℝ) ^ n := by
      have hnat : n ≤ 2 ^ n := le_of_lt Nat.lt_two_pow_self
      exact_mod_cast hnat
    have hexp_q : Real.exp (-((2 : ℝ) ^ n * Real.pi)) ≤ qVal ^ n := by
      rw [qVal, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith
    linarith

private lemma agm_tendsto :
    Tendsto (fun n => (agmSeq 1 (Real.sqrt 2) n).1) atTop (𝓝 (1 / (T2 Real.pi) ^ 2)) := by
  have h1 : Tendsto (fun n : ℕ => (T3 ((2 : ℝ) ^ n * Real.pi)) ^ 2 / (T4 Real.pi) ^ 2) atTop
      (𝓝 (1 ^ 2 / (T4 Real.pi) ^ 2)) :=
    (tendsto_T3_two_pow.pow 2).div_const ((T4 Real.pi) ^ 2)
  rw [one_pow, ← T2_pi_eq_T4_pi] at h1
  refine h1.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [agmSeq_succ_eq k]
  dsimp only
  rw [T2_pi_eq_T4_pi]

private noncomputable def cT4 (k : ℕ) : ℚ := PowerSeries.coeff k theta4

private noncomputable def cT4Inv (k : ℕ) : ℚ := PowerSeries.coeff k (theta4⁻¹)

private lemma theta4_constantCoeff : PowerSeries.constantCoeff theta4 = 1 := by
  rw [theta4, PowerSeries.constantCoeff_mk]
  split_ifs <;> first | rfl | omega

private lemma theta4_mul_inv : theta4 * theta4⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel theta4 (by rw [theta4_constantCoeff]; norm_num)

private lemma coeff_theta4_abs_le (m : ℕ) : |(cT4 m : ℝ)| ≤ 2 := by
  rw [cT4, theta4, PowerSeries.coeff_mk]
  split_ifs
  · norm_num
  · push_cast
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_neg_one_pow, mul_one]
  · norm_num

private lemma coeff_theta4_inv_zero : cT4Inv 0 = 1 := by
  rw [cT4Inv]
  have h := congrArg (PowerSeries.coeff 0) theta4_mul_inv
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, theta4_constantCoeff, one_mul,
    ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_one] at h
  simpa only [↓reduceIte] using h

private lemma sum_two_mul_three_pow (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (2 : ℝ) * (3 : ℝ) ^ (k - j) = (3 : ℝ) ^ (k + 1) - 1 := by
  induction k with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_self, pow_zero, pow_one]
    norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ']
    have hshift : ∑ x ∈ Finset.range (k + 1), (2 : ℝ) * (3 : ℝ) ^ (k + 1 - (x + 1)) =
        ∑ x ∈ Finset.range (k + 1), (2 : ℝ) * (3 : ℝ) ^ (k - x) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Nat.add_sub_add_right]
    rw [hshift, ih, Nat.sub_zero, pow_succ']
    ring

private lemma coeff_theta4_inv_abs_le (k : ℕ) :
    |(cT4Inv k : ℝ)| ≤ (3 : ℝ) ^ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      rw [coeff_theta4_inv_zero]
      norm_num
    | succ k =>
      have h0 : PowerSeries.coeff (k + 1) (theta4 * theta4⁻¹) = 0 := by
        rw [theta4_mul_inv, PowerSeries.coeff_one]
        have hne : k + 1 ≠ 0 := Nat.succ_ne_zero k
        simp only [hne, ↓reduceIte]
      rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i theta4 * PowerSeries.coeff j (theta4⁻¹)),
        Finset.sum_range_succ'] at h0
      have hc0 : PowerSeries.coeff 0 theta4 = 1 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff]
        exact theta4_constantCoeff
      rw [hc0, Nat.sub_zero, one_mul] at h0
      have hrec : cT4Inv (k + 1) =
          -∑ j ∈ Finset.range (k + 1), cT4 (j + 1) * cT4Inv (k - j) := by
        have hsub : ∀ j ∈ Finset.range (k + 1),
            PowerSeries.coeff (j + 1) theta4 * PowerSeries.coeff (k + 1 - (j + 1)) (theta4⁻¹) =
              cT4 (j + 1) * cT4Inv (k - j) := by
          intro j _
          rw [Nat.add_sub_add_right]
          rfl
        rw [Finset.sum_congr rfl hsub] at h0
        change PowerSeries.coeff (k + 1) (theta4⁻¹) = _
        linarith
      have hrecR : (cT4Inv (k + 1) : ℝ) =
          -∑ j ∈ Finset.range (k + 1), (cT4 (j + 1) : ℝ) * (cT4Inv (k - j) : ℝ) := by
        rw [hrec]
        push_cast
        rfl
      rw [hrecR, abs_neg]
      calc
        |∑ j ∈ Finset.range (k + 1), (cT4 (j + 1) : ℝ) * (cT4Inv (k - j) : ℝ)|
            ≤ ∑ j ∈ Finset.range (k + 1), |(cT4 (j + 1) : ℝ) * (cT4Inv (k - j) : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j ∈ Finset.range (k + 1), |(cT4 (j + 1) : ℝ)| * |(cT4Inv (k - j) : ℝ)| := by
          refine Finset.sum_congr rfl fun j _ => abs_mul _ _
        _ ≤ ∑ j ∈ Finset.range (k + 1), (2 : ℝ) * (3 : ℝ) ^ (k - j) := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine mul_le_mul (coeff_theta4_abs_le (j + 1)) (ih (k - j) (by omega))
            (abs_nonneg _) (by norm_num)
        _ = (3 : ℝ) ^ (k + 1) - 1 := sum_two_mul_three_pow k
        _ ≤ (3 : ℝ) ^ (k + 1) := by linarith

private lemma A001934_abs_le (k : ℕ) : |(A001934 k : ℝ)| ≤ (6 : ℝ) ^ k := by
  have hdef : A001934 k = ∑ i ∈ Finset.range (k + 1), cT4Inv i * cT4Inv (k - i) := by
    rw [A001934, sq, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (theta4⁻¹) * PowerSeries.coeff j (theta4⁻¹))]
    rfl
  have hR : (A001934 k : ℝ) = ∑ i ∈ Finset.range (k + 1), (cT4Inv i : ℝ) * (cT4Inv (k - i) : ℝ) := by
    rw [hdef]
    push_cast
    rfl
  have h2k : (k + 1 : ℝ) ≤ (2 : ℝ) ^ k := by
    have hnat : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    exact_mod_cast hnat
  rw [hR]
  calc
    |∑ i ∈ Finset.range (k + 1), (cT4Inv i : ℝ) * (cT4Inv (k - i) : ℝ)|
        ≤ ∑ i ∈ Finset.range (k + 1), |(cT4Inv i : ℝ) * (cT4Inv (k - i) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (k + 1), |(cT4Inv i : ℝ)| * |(cT4Inv (k - i) : ℝ)| := by
      refine Finset.sum_congr rfl fun i _ => abs_mul _ _
    _ ≤ ∑ _i ∈ Finset.range (k + 1), (3 : ℝ) ^ k := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      calc
        |(cT4Inv i : ℝ)| * |(cT4Inv (k - i) : ℝ)|
            ≤ (3 : ℝ) ^ i * (3 : ℝ) ^ (k - i) :=
          mul_le_mul (coeff_theta4_inv_abs_le i) (coeff_theta4_inv_abs_le (k - i))
            (abs_nonneg _) (by positivity)
        _ = (3 : ℝ) ^ k := by rw [← pow_add, Nat.add_sub_of_le hik]
    _ = ((k + 1 : ℕ) : ℝ) * (3 : ℝ) ^ k := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (k + 1 : ℝ) * (3 : ℝ) ^ k := by push_cast; rfl
    _ ≤ (2 : ℝ) ^ k * (3 : ℝ) ^ k := mul_le_mul_of_nonneg_right h2k (by positivity)
    _ = (6 : ℝ) ^ k := by rw [← mul_pow]; norm_num

private lemma summable_norm_theta4 :
    Summable fun k : ℕ => ‖(cT4 k : ℝ) * qVal ^ k‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    ((summable_geometric_of_lt_one qVal_pos.le (by linarith [eighteen_mul_qVal_lt_one])).mul_left 2)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg qVal_pos.le k)]
  exact mul_le_mul_of_nonneg_right (coeff_theta4_abs_le k) (pow_nonneg qVal_pos.le k)

private lemma summable_norm_theta4_inv :
    Summable fun k : ℕ => ‖(cT4Inv k : ℝ) * qVal ^ k‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (summable_geometric_of_lt_one (by positivity [qVal_pos]) (by linarith [eighteen_mul_qVal_lt_one] : 3 * qVal < 1))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg qVal_pos.le k), mul_pow]
  exact mul_le_mul_of_nonneg_right (coeff_theta4_inv_abs_le k) (pow_nonneg qVal_pos.le k)

private lemma summable_norm_A001934 :
    Summable fun k : ℕ => ‖(A001934 k : ℝ) * qVal ^ k‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
    (summable_geometric_of_lt_one (by positivity [qVal_pos]) (by linarith [eighteen_mul_qVal_lt_one] : 6 * qVal < 1))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg qVal_pos.le k), mul_pow]
  exact mul_le_mul_of_nonneg_right (A001934_abs_le k) (pow_nonneg qVal_pos.le k)

private lemma tsum_theta4_eq_T4_pi :
    (∑' k : ℕ, (cT4 k : ℝ) * qVal ^ k) = T4 Real.pi := by
  rw [summable_norm_theta4.of_norm.tsum_eq_zero_add, T4_eq_one_add_two_mul Real.pi_pos]
  have h0 : (cT4 0 : ℝ) * qVal ^ 0 = 1 := by
    have hc0 : cT4 0 = 1 := by
      rw [cT4, PowerSeries.coeff_zero_eq_constantCoeff]
      exact theta4_constantCoeff
    rw [hc0]
    norm_num
  rw [h0]
  congr 1
  let f : ℕ → ℝ := fun k => (cT4 (k + 1) : ℝ) * qVal ^ (k + 1)
  let g : ℕ → ℕ := fun r => (r + 1) ^ 2 - 1
  have hg_inj : Function.Injective g := by
    intro r1 r2 h
    have hsq : (r1 + 1) ^ 2 = (r2 + 1) ^ 2 := by
      have h1 : 1 ≤ (r1 + 1) ^ 2 := Nat.one_le_pow 2 (r1 + 1) (by omega)
      have h2 : 1 ≤ (r2 + 1) ^ 2 := Nat.one_le_pow 2 (r2 + 1) (by omega)
      dsimp only [g] at h
      omega
    have hsqrt := congrArg Nat.sqrt hsq
    rw [Nat.sqrt_eq', Nat.sqrt_eq'] at hsqrt
    omega
  have hsupp : Function.support f ⊆ Set.range g := by
    intro k hk
    rw [Function.mem_support] at hk
    have hne : cT4 (k + 1) ≠ 0 := by
      intro hzero
      apply hk
      simp only [f, hzero, Rat.cast_zero, zero_mul]
    rw [cT4, theta4, PowerSeries.coeff_mk] at hne
    have hsq : Nat.sqrt (k + 1) * Nat.sqrt (k + 1) = k + 1 := by
      by_contra hnsq
      apply hne
      have hne0 : k + 1 ≠ 0 := Nat.succ_ne_zero k
      simp only [hne0, hnsq, ↓reduceIte]
    have hs_pos : 1 ≤ Nat.sqrt (k + 1) := by
      by_contra hs0
      have : Nat.sqrt (k + 1) = 0 := by omega
      rw [this] at hsq
      omega
    refine ⟨Nat.sqrt (k + 1) - 1, ?_⟩
    dsimp only [g]
    rw [Nat.sub_add_cancel hs_pos, sq, hsq]
    omega
  have hts := hg_inj.tsum_eq hsupp
  rw [← hts, ← tsum_mul_left]
  refine tsum_congr fun r => ?_
  have hr1 : 1 ≤ (r + 1) ^ 2 := Nat.one_le_pow 2 (r + 1) (by omega)
  have harg : g r + 1 = (r + 1) ^ 2 := Nat.sub_add_cancel hr1
  simp only [f, harg, cT4, theta4, PowerSeries.coeff_mk]
  have hne0 : (r + 1) ^ 2 ≠ 0 := by omega
  have hsq : Nat.sqrt ((r + 1) ^ 2) * Nat.sqrt ((r + 1) ^ 2) = (r + 1) ^ 2 := by
    rw [Nat.sqrt_eq', sq]
  simp only [hne0, hsq, ↓reduceIte]
  rw [Nat.sqrt_eq']
  have hq : qVal ^ ((r + 1) ^ 2) = Real.exp (-Real.pi * ((r + 1 : ℕ) : ℝ) ^ 2) := by
    rw [qVal, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hq]
  push_cast
  ring

private lemma hasSum_A001934 :
    HasSum (fun k : ℕ => (A001934 k : ℝ) / Real.exp (k * Real.pi)) (1 / (T2 Real.pi) ^ 2) := by
  have hterm : (fun k : ℕ => (A001934 k : ℝ) / Real.exp (k * Real.pi)) =
      fun k : ℕ => (A001934 k : ℝ) * qVal ^ k := by
    ext k
    rw [qVal, Real.exp_neg, inv_pow, div_eq_mul_inv, Real.exp_nat_mul]
  rw [hterm]
  have hUV : (∑' k : ℕ, (cT4 k : ℝ) * qVal ^ k) *
      (∑' k : ℕ, (cT4Inv k : ℝ) * qVal ^ k) = 1 := by
    rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm summable_norm_theta4
      summable_norm_theta4_inv]
    have hcoeff : ∀ k : ℕ,
        (∑ i ∈ Finset.range (k + 1),
            (cT4 i : ℝ) * qVal ^ i * ((cT4Inv (k - i) : ℝ) * qVal ^ (k - i))) =
          ((PowerSeries.coeff k (theta4 * theta4⁻¹) : ℚ) : ℝ) * qVal ^ k := fun k => by
      have hmul : PowerSeries.coeff k (theta4 * theta4⁻¹) =
          ∑ i ∈ Finset.range (k + 1), cT4 i * cT4Inv (k - i) := by
        rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => PowerSeries.coeff i theta4 * PowerSeries.coeff j (theta4⁻¹))]
        rfl
      rw [hmul]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      calc
        (cT4 i : ℝ) * qVal ^ i * ((cT4Inv (k - i) : ℝ) * qVal ^ (k - i))
            = (cT4 i : ℝ) * (cT4Inv (k - i) : ℝ) * (qVal ^ i * qVal ^ (k - i)) := by ring
        _ = (cT4 i : ℝ) * (cT4Inv (k - i) : ℝ) * qVal ^ k := by
            rw [← pow_add, Nat.add_sub_of_le hik]
    rw [tsum_congr hcoeff, theta4_mul_inv]
    have hone : (fun k : ℕ => ((PowerSeries.coeff k (1 : PowerSeries ℚ) : ℚ) : ℝ) * qVal ^ k) =
        fun k : ℕ => if k = 0 then (1 : ℝ) else 0 := by
      ext k
      rw [PowerSeries.coeff_one]
      split_ifs with hk
      · subst hk; norm_num
      · norm_num
    rw [hone, tsum_ite_eq]
  have hVV : (∑' k : ℕ, (cT4Inv k : ℝ) * qVal ^ k) ^ 2 =
      ∑' k : ℕ, (A001934 k : ℝ) * qVal ^ k := by
    rw [sq, tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm summable_norm_theta4_inv
      summable_norm_theta4_inv]
    refine tsum_congr fun k => ?_
    have hmul : A001934 k = ∑ i ∈ Finset.range (k + 1), cT4Inv i * cT4Inv (k - i) := by
      rw [A001934, sq, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (theta4⁻¹) * PowerSeries.coeff j (theta4⁻¹))]
      rfl
    rw [hmul]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    calc
      (cT4Inv i : ℝ) * qVal ^ i * ((cT4Inv (k - i) : ℝ) * qVal ^ (k - i))
          = (cT4Inv i : ℝ) * (cT4Inv (k - i) : ℝ) * (qVal ^ i * qVal ^ (k - i)) := by ring
      _ = (cT4Inv i : ℝ) * (cT4Inv (k - i) : ℝ) * qVal ^ k := by
          rw [← pow_add, Nat.add_sub_of_le hik]
  rw [tsum_theta4_eq_T4_pi] at hUV
  have hT4_pos : 0 < T4 Real.pi := T4_pos_of_ge_pi le_rfl
  have hV_eq : (∑' k : ℕ, (cT4Inv k : ℝ) * qVal ^ k) = 1 / T4 Real.pi := by
    have hmul := congrArg ((T4 Real.pi)⁻¹ * ·) hUV
    rw [← mul_assoc, inv_mul_cancel₀ hT4_pos.ne', one_mul, mul_one, ← one_div] at hmul
    exact hmul
  have hsum_eq : (∑' k : ℕ, (A001934 k : ℝ) * qVal ^ k) = 1 / (T2 Real.pi) ^ 2 := by
    rw [← hVV, hV_eq, T2_pi_eq_T4_pi]
    ring
  rw [← hsum_eq]
  exact summable_norm_A001934.of_norm.hasSum

theorem OMA.solution : type_of% @OMA.S_oeis_a053004.main :=
  ⟨agm_tendsto, hasSum_A001934⟩

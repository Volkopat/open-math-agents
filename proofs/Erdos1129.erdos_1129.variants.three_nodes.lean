import FormalConjectures.ErdosProblems.«1129»

/-! The Lebesgue constant of three nodes is minimized uniquely by equal gaps. -/

open Erdos1129

theorem OMA.solution : type_of% @Erdos1129.erdos_1129.variants.three_nodes := by
  have h3 (x : Fin 3 → ℝ) (t : ℝ) : lebesgueFunction x t =
      |(t - x 1) * (t - x 2) / ((x 0 - x 1) * (x 0 - x 2))| +
      |(t - x 0) * (t - x 2) / ((x 1 - x 0) * (x 1 - x 2))| +
      |(t - x 0) * (t - x 1) / ((x 2 - x 0) * (x 2 - x 1))| := by
    rw [lebesgueFunction_eq, Fin.sum_univ_three,
      show (Finset.univ : Finset (Fin 3)).erase 0 = {1, 2} by decide,
      show (Finset.univ : Finset (Fin 3)).erase 1 = {0, 2} by decide,
      show (Finset.univ : Finset (Fin 3)).erase 2 = {0, 1} by decide,
      Finset.prod_pair (by decide : (1 : Fin 3) ≠ 2),
      Finset.prod_pair (by decide : (0 : Fin 3) ≠ 2),
      Finset.prod_pair (by decide : (0 : Fin 3) ≠ 1)]
    simp only [div_mul_div_comm]
  have hleI (x : Fin 3 → ℝ) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
      lebesgueFunction x t ≤ lebesgueConstant x :=
    le_csSup (isCompact_Icc.image (by unfold lebesgueFunction; fun_prop)).bddAbove ⟨t, ht, rfl⟩
  have hgb (x : Fin 3 → ℝ) (hx : IsNodeSet x) :
      1 + (x 1 - x 0) ^ 2 / (2 * ((x 1 - x 0) + (x 2 - x 1)) * (x 2 - x 1)) ≤ lebesgueConstant x ∧
      1 + (x 2 - x 1) ^ 2 / (2 * ((x 2 - x 1) + (x 1 - x 0)) * (x 1 - x 0)) ≤ lebesgueConstant x := by
    have hab : x 0 < x 1 := hx.1 (by decide)
    have hbc : x 1 < x 2 := hx.1 (by decide)
    have hac := hab.trans hbc
    have hne : x 1 - x 0 + (x 2 - x 1) ≠ 0 := by linarith
    have hne' : x 2 - x 1 + (x 1 - x 0) ≠ 0 := by linarith
    refine ⟨le_trans ?_ (hleI x (t := (x 0 + x 1) / 2) ⟨by linarith [(hx.2 0).1, (hx.2 1).1], by linarith [(hx.2 0).2, (hx.2 1).2]⟩),
            le_trans ?_ (hleI x (t := (x 1 + x 2) / 2) ⟨by linarith [(hx.2 1).1, (hx.2 2).1], by linarith [(hx.2 1).2, (hx.2 2).2]⟩)⟩
    · rw [h3]; set t := (x 0 + x 1) / 2
      have hEq : 1 + (x 1 - x 0) ^ 2 / (2 * (x 1 - x 0 + (x 2 - x 1)) * (x 2 - x 1)) =
          (t - x 1) * (t - x 2) / ((x 0 - x 1) * (x 0 - x 2)) +
          (t - x 0) * (t - x 2) / ((x 1 - x 0) * (x 1 - x 2)) -
          (t - x 0) * (t - x 1) / ((x 2 - x 0) * (x 2 - x 1)) := by
        dsimp [t]; field_simp [hne, sub_ne_zero.2 hab.ne, sub_ne_zero.2 hab.ne',
          sub_ne_zero.2 hbc.ne, sub_ne_zero.2 hbc.ne', sub_ne_zero.2 hac.ne, sub_ne_zero.2 hac.ne']; ring
      linarith [le_abs_self ((t - x 1) * (t - x 2) / ((x 0 - x 1) * (x 0 - x 2))),
        le_abs_self ((t - x 0) * (t - x 2) / ((x 1 - x 0) * (x 1 - x 2))),
        neg_le_abs ((t - x 0) * (t - x 1) / ((x 2 - x 0) * (x 2 - x 1)))]
    · rw [h3]; set t := (x 1 + x 2) / 2
      have hEq : 1 + (x 2 - x 1) ^ 2 / (2 * (x 2 - x 1 + (x 1 - x 0)) * (x 1 - x 0)) =
          -((t - x 1) * (t - x 2) / ((x 0 - x 1) * (x 0 - x 2))) +
          (t - x 0) * (t - x 2) / ((x 1 - x 0) * (x 1 - x 2)) +
          (t - x 0) * (t - x 1) / ((x 2 - x 0) * (x 2 - x 1)) := by
        dsimp [t]; field_simp [hne', sub_ne_zero.2 hab.ne, sub_ne_zero.2 hab.ne',
          sub_ne_zero.2 hbc.ne, sub_ne_zero.2 hbc.ne', sub_ne_zero.2 hac.ne, sub_ne_zero.2 hac.ne']; ring
      linarith [neg_le_abs ((t - x 1) * (t - x 2) / ((x 0 - x 1) * (x 0 - x 2))),
        le_abs_self ((t - x 0) * (t - x 2) / ((x 1 - x 0) * (x 1 - x 2))),
        le_abs_self ((t - x 0) * (t - x 1) / ((x 2 - x 0) * (x 2 - x 1)))]
  have hgd (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
      1 + u ^ 2 / (2 * (u + v) * v) - 5 / 4 = (u - v) * (2 * u + v) / (4 * (u + v) * v) := by
    field_simp [hv.ne', (add_pos hu hv).ne']; ring
  have hcf (t : ℝ) : lebesgueFunction (![(-1 : ℝ), 0, 1] : Fin 3 → ℝ) t =
      |t * (t - 1) / 2| + |1 - t ^ 2| + |t * (t + 1) / 2| := by
    rw [h3]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    congr 1; · congr 1 <;> congr 1 <;> ring
    · congr 1; ring
  have hcc : lebesgueConstant (![(-1 : ℝ), 0, 1] : Fin 3 → ℝ) = 5 / 4 := by
    refine le_antisymm (csSup_le ⟨_, 0, by norm_num, rfl⟩ ?_)
      ((by rw [hcf]; norm_num : 5 / 4 = lebesgueFunction _ (1 / 2)).trans_le (hleI _ (by norm_num)))
    rintro _ ⟨t, ⟨hlo, hhi⟩, rfl⟩
    have hb : 0 ≤ 1 - t ^ 2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - t) (by linarith : 0 ≤ 1 + t)]
    rw [hcf, abs_of_nonneg hb]
    by_cases h : t ≤ 0
    · rw [abs_of_nonneg (div_nonneg (mul_nonneg_of_nonpos_of_nonpos h (by linarith)) (by norm_num)),
        abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h (by linarith)) (by norm_num))]
      nlinarith [sq_nonneg (t + 1 / 2)]
    · rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) (by norm_num)),
        abs_of_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num))]
      nlinarith [sq_nonneg (t - 1 / 2)]
  have hcan : IsCanonical (![(-1 : ℝ), 0, 1] : Fin 3 → ℝ) :=
    ⟨⟨fun i j hij => by fin_cases i <;> fin_cases j <;> norm_num at *, fun i => by fin_cases i <;> norm_num⟩, ⟨0, rfl⟩, ⟨2, rfl⟩⟩
  refine ⟨?_, hcc⟩
  ext x; change (IsCanonical x ∧ IsMinimiser x) ↔ x ∈ ({![(-1 : ℝ), 0, 1]} : Set (Fin 3 → ℝ))
  rw [Set.mem_singleton_iff]; constructor
  · rintro ⟨hx, hmin⟩
    have hA : x 0 = -1 := by
      obtain ⟨i, hi⟩ := hx.2.1; exact le_antisymm (hi ▸ hx.1.1.monotone (Fin.zero_le i)) (hx.1.2 0).1
    have hC : x 2 = 1 := by
      obtain ⟨i, hi⟩ := hx.2.2; exact le_antisymm (hx.1.2 2).2 (hi ▸ hx.1.1.monotone (by fin_cases i <;> decide))
    have hle : lebesgueConstant x ≤ 5 / 4 := hcc ▸ hmin.2 _ hcan.1
    obtain ⟨hl, hr⟩ := hgb x hx.1
    have hu : 0 < x 1 - x 0 := sub_pos.2 (hx.1.1 (by decide))
    have hv : 0 < x 2 - x 1 := sub_pos.2 (hx.1.1 (by decide))
    have huv : x 1 - x 0 ≤ x 2 - x 1 := by_contra fun h => by
      have : 0 < (x 1 - x 0 - (x 2 - x 1)) * (2 * (x 1 - x 0) + (x 2 - x 1)) /
        (4 * (x 1 - x 0 + (x 2 - x 1)) * (x 2 - x 1)) := div_pos (mul_pos (by linarith) (by positivity)) (by positivity)
      linarith [hgd _ _ hu hv]
    have hvu : x 2 - x 1 ≤ x 1 - x 0 := by_contra fun h => by
      have : 0 < (x 2 - x 1 - (x 1 - x 0)) * (2 * (x 2 - x 1) + (x 1 - x 0)) /
        (4 * (x 2 - x 1 + (x 1 - x 0)) * (x 1 - x 0)) := div_pos (mul_pos (by linarith) (by positivity)) (by positivity)
      linarith [hgd _ _ hv hu]
    funext i; fin_cases i <;> simp [hA, hC, show x 1 = 0 by linarith]
  · rintro rfl; refine ⟨hcan, hcan.1, fun y hy => ?_⟩
    obtain ⟨hl, hr⟩ := hgb y hy
    have hu : 0 < y 1 - y 0 := sub_pos.2 (hy.1 (by decide))
    have hv : 0 < y 2 - y 1 := sub_pos.2 (hy.1 (by decide))
    rw [hcc]
    rcases le_total (y 1 - y 0) (y 2 - y 1) with h | h
    · have : 0 ≤ (y 2 - y 1 - (y 1 - y 0)) * (2 * (y 2 - y 1) + (y 1 - y 0)) /
        (4 * (y 2 - y 1 + (y 1 - y 0)) * (y 1 - y 0)) := div_nonneg (mul_nonneg (by linarith) (by positivity)) (by positivity)
      linarith [hgd _ _ hv hu]
    · have : 0 ≤ (y 1 - y 0 - (y 2 - y 1)) * (2 * (y 1 - y 0) + (y 2 - y 1)) /
        (4 * (y 1 - y 0 + (y 2 - y 1)) * (y 2 - y 1)) := div_nonneg (mul_nonneg (by linarith) (by positivity)) (by positivity)
      linarith [hgd _ _ hu hv]

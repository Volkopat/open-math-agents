import FormalConjectures.ErdosProblems.«507»

/-! Use a parabola modulo a prime and scale its integer representatives into the unit disk. -/

open Asymptotics Filter
open scoped EuclideanGeometry

lemma OMA.heilbronn_lower_area_coordinates (a b c : ℝ²) :
    EuclideanGeometry.triangle_area a b c =
      ((a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1)) / 2 := by
  rw [EuclideanGeometry.triangle_area_eq_det, Matrix.det_fin_three]
  simp
  ring

lemma OMA.heilbronn_lower_collinear_area {T : Set ℝ²} (hT : Collinear ℝ T)
    {a b c : ℝ²} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) :
    EuclideanGeometry.triangle_area a b c = 0 := by
  obtain ⟨base, v, h⟩ := (collinear_iff_exists_forall_eq_smul_vadd T).mp hT
  obtain ⟨x, rfl⟩ := h a ha
  obtain ⟨y, rfl⟩ := h b hb
  obtain ⟨z, rfl⟩ := h c hc
  rw [OMA.heilbronn_lower_area_coordinates]
  simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma OMA.heilbronn_lower_area_bdd {a b c : ℝ²}
    (ha : a ∈ Metric.closedBall (0 : ℝ²) 1)
    (hb : b ∈ Metric.closedBall (0 : ℝ²) 1)
    (hc : c ∈ Metric.closedBall (0 : ℝ²) 1) :
    |EuclideanGeometry.triangle_area a b c| ≤ 4 := by
  have hcoord (x : ℝ²) (hx : x ∈ Metric.closedBall (0 : ℝ²) 1) (i : Fin 2) :
      |x i| ≤ 1 := by
    have hnorm : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
    exact (Real.norm_eq_abs (x i) ▸ PiLp.norm_apply_le x i).trans hnorm
  have hdiff (x : ℝ²) (hx : x ∈ Metric.closedBall (0 : ℝ²) 1) (i : Fin 2) :
      |x i - c i| ≤ 2 := by
    exact (abs_sub _ _).trans (by linarith [hcoord x hx i, hcoord c hc i])
  rw [OMA.heilbronn_lower_area_coordinates, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ (|(a 0 - c 0) * (b 1 - c 1)| + |(b 0 - c 0) * (a 1 - c 1)|) / 2 :=
      div_le_div_of_nonneg_right (abs_sub _ _) (by norm_num)
    _ ≤ (2 * 2 + 2 * 2) / 2 := by rw [abs_mul, abs_mul]; gcongr <;> apply hdiff <;> assumption
    _ = 4 := by norm_num

lemma OMA.heilbronn_lower_det_ne_zero (p i j k : ℕ) [Fact (Nat.Prime p)]
    (hi : i < p) (hj : j < p) (hk : k < p) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ((i : ℤ) - k) * (((j ^ 2 % p : ℕ) : ℤ) - ((k ^ 2 % p : ℕ) : ℤ)) -
      ((j : ℤ) - k) * (((i ^ 2 % p : ℕ) : ℤ) - ((k ^ 2 % p : ℕ) : ℤ)) ≠ 0 := by
  intro hz
  have hzmod := congrArg (fun x : ℤ => (x : ZMod p)) hz
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_zero, ZMod.natCast_mod,
    Nat.cast_pow] at hzmod
  have hcast {a b : ℕ} (ha : a < p) (hb : b < p) (hab : a ≠ b) :
      (a : ZMod p) ≠ (b : ZMod p) := by
    intro heq
    have hm := (ZMod.natCast_eq_natCast_iff' a b p).mp heq
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hm
    exact hab hm
  have hprod : ((i : ZMod p) - k) * ((j : ZMod p) - k) * ((j : ZMod p) - i) = 0 := by
    linear_combination hzmod
  exact (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (hcast hi hk hik))
    (sub_ne_zero.mpr (hcast hj hk hjk))) (sub_ne_zero.mpr (hcast hj hi hij.symm))) hprod

theorem OMA.solution : type_of% @Erdos507.erdos_507.variants.lower_erdos := by
  classical
  apply Asymptotics.IsBigO.of_bound 32
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
  obtain ⟨p, hp, hnp, hpn⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let scale : ℝ := 2 * (p : ℝ)
  have hs : 0 < scale := by dsimp [scale]; positivity
  let point (i : Fin n) : ℝ² :=
    WithLp.toLp 2 ![(i.val : ℝ) / scale, ((i.val ^ 2 % p : ℕ) : ℝ) / scale]
  have hpoint_inj : Function.Injective point := by
    intro i j hij
    have hx : (i.val : ℝ) / scale = (j.val : ℝ) / scale := congrArg (fun x : ℝ² => x 0) hij
    exact Fin.ext (by exact_mod_cast (div_left_inj' hs.ne').mp hx)
  let S : Finset ℝ² := Finset.univ.map ⟨point, hpoint_inj⟩
  have hS_card : S.card = n := by simp [S]
  have hS_disk : (S : Set ℝ²) ⊆ Metric.closedBall 0 1 := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    rw [EuclideanSpace.closedBall_zero_eq 1 (by norm_num)]
    change (∑ l : Fin 2, (point i l) ^ 2) ≤ (1 : ℝ) ^ 2
    rw [Fin.sum_univ_two]
    change ((i.val : ℝ) / scale)^2 + (((i.val ^ 2 % p : ℕ) : ℝ) / scale)^2 ≤ _
    have square (a : ℕ) (ha : a < p) : ((a : ℝ) / scale)^2 ≤ (1 / 2 : ℝ)^2 := by
      apply pow_le_pow_left₀ (by positivity) _ 2
      rw [div_le_iff₀ hs]
      have : (a : ℝ) ≤ p := by exact_mod_cast ha.le
      dsimp [scale]
      linarith
    nlinarith [square _ (i.isLt.trans hnp), square _ (Nat.mod_lt (i.val ^ 2) hp.pos)]
  have htriangle (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      1 / (2 * scale ^ 2) ≤ |EuclideanGeometry.triangle_area (point i) (point j) (point k)| := by
    let D : ℤ := ((i.val : ℤ) - k.val) *
        (((j.val ^ 2 % p : ℕ) : ℤ) - ((k.val ^ 2 % p : ℕ) : ℤ)) -
      ((j.val : ℤ) - k.val) *
        (((i.val ^ 2 % p : ℕ) : ℤ) - ((k.val ^ 2 % p : ℕ) : ℤ))
    have hD : D ≠ 0 := OMA.heilbronn_lower_det_ne_zero p i.val j.val k.val
      (i.isLt.trans hnp) (j.isLt.trans hnp) (k.isLt.trans hnp)
      (fun h => hij (Fin.ext h)) (fun h => hik (Fin.ext h)) (fun h => hjk (Fin.ext h))
    have harea : EuclideanGeometry.triangle_area (point i) (point j) (point k) =
        (D : ℝ) / (2 * scale ^ 2) := by
      rw [OMA.heilbronn_lower_area_coordinates]
      simp only [point, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, D,
        Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      field_simp [hs.ne']
    have hD_abs : (1 : ℝ) ≤ |(D : ℝ)| := by exact_mod_cast Int.one_le_abs hD
    rw [harea, abs_div, abs_of_pos (by positivity : 0 < 2 * scale ^ 2)]
    exact div_le_div_of_nonneg_right hD_abs (by positivity)
  have hall (q : Fin 3 → ℝ²) (hq_inj : Function.Injective q) (hq_mem : ∀ i, q i ∈ S) :
      1 / (2 * scale ^ 2) ≤ |EuclideanGeometry.triangle_area (q 0) (q 1) (q 2)| := by
    have hpreimage (j : Fin 3) : ∃ i : Fin n, point i = q j := by
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp (hq_mem j)
      exact ⟨i, hi⟩
    choose preimage hpreimage using hpreimage
    have hpre_inj : Function.Injective preimage := by
      intro a b hab
      apply hq_inj
      rw [← hpreimage a, ← hpreimage b, hab]
    rw [← hpreimage 0, ← hpreimage 1, ← hpreimage 2]
    exact htriangle _ _ _ (hpre_inj.ne (by decide)) (hpre_inj.ne (by decide))
      (hpre_inj.ne (by decide))
  obtain ⟨q, hq_mem⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 3) (s := S) (by simpa [hS_card] using hn)
  have hq (i : Fin 3) : q i ∈ S := hq_mem (Set.mem_range_self i)
  have hS_ncol : ¬ Collinear ℝ (S : Set ℝ²) := by
    intro hc
    have hz := OMA.heilbronn_lower_collinear_area hc (hq 0) (hq 1) (hq 2)
    have hq_le := hall q q.injective hq
    rw [hz, abs_zero] at hq_le
    exact (not_le_of_gt (by positivity : 0 < 1 / (2 * scale ^ 2))) hq_le
  have hS_area : 1 / (2 * scale ^ 2) ≤ Erdos507.minTriangleArea S := by
    apply le_csInf
    · exact ⟨_, q, q.injective, hq, rfl⟩
    · rintro _ ⟨r, hr_inj, hr_mem, rfl⟩
      exact hall r hr_inj hr_mem
  have halpha : Erdos507.minTriangleArea S ≤ Erdos507.α n := by
    unfold Erdos507.α
    apply le_csSup
    · refine ⟨4, ?_⟩
      rintro a ⟨T, ⟨hT_card, hT_disk, _⟩, rfl⟩
      obtain ⟨r, hr_mem⟩ := Function.Embedding.exists_of_card_le_finset
        (α := Fin 3) (s := T) (by simpa [hT_card] using hn)
      have hr (i : Fin 3) : r i ∈ T := hr_mem (Set.mem_range_self i)
      have hm : Erdos507.minTriangleArea T ≤
          |EuclideanGeometry.triangle_area (r 0) (r 1) (r 2)| := by
        apply csInf_le
        · exact ⟨0, by rintro a ⟨u, _, _, rfl⟩; exact abs_nonneg _⟩
        · exact ⟨r, r.injective, hr, rfl⟩
      exact hm.trans (OMA.heilbronn_lower_area_bdd (hT_disk (hr 0)) (hT_disk (hr 1)) (hT_disk (hr 2)))
    · exact ⟨S, ⟨hS_card, hS_disk, hS_ncol⟩, rfl⟩
  have hscale : scale ≤ 4 * (n : ℝ) := by
    have hp_le : (p : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hpn
    dsimp [scale]
    linarith
  have hsq : 2 * scale ^ 2 ≤ 32 * (n : ℝ) ^ 2 := by
    nlinarith [pow_le_pow_left₀ hs.le hscale 2]
  have hlower : 1 / (32 * (n : ℝ) ^ 2) ≤ Erdos507.α n :=
    (one_div_le_one_div_of_le (by positivity) hsq).trans (hS_area.trans halpha)
  have hα0 : 0 ≤ Erdos507.α n := (by positivity : 0 ≤ 1 / (32 * (n : ℝ) ^ 2)).trans hlower
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (n : ℝ) ^ 2), Real.norm_of_nonneg hα0]
  calc
    1 / (n : ℝ) ^ 2 = 32 * (1 / (32 * (n : ℝ) ^ 2)) := by ring
    _ ≤ 32 * Erdos507.α n := mul_le_mul_of_nonneg_left hlower (by norm_num)

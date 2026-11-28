import FormalConjectures.Mathoverflow.«17560»

/-! Shorter proof of `Mathoverflow17560.mathoverflow_17560.variants.all_nats`. -/

open Real Set Finset Filter Topology

private def delta : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f, t => f t
  | k + 1, f, t => delta k (fun s => f (s + 1) - f s) t

private lemma delta_int (k N : ℕ) (f : ℝ → ℝ) (hf : ∀ i : ℕ, ∃ z : ℤ, f (↑N + ↑i) = z) :
    ∃ z : ℤ, delta k f ↑N = z := by
  induction k generalizing f with
  | zero => simpa [delta] using hf 0
  | succ k ih =>
    refine ih _ fun i => ?_
    obtain ⟨z1, hz1⟩ := hf (i + 1); obtain ⟨z0, hz0⟩ := hf i
    exact ⟨z1 - z0, by rw [show (N : ℝ) + i + 1 = N + ↑(i + 1) by push_cast; ring, hz1, hz0]; simp⟩

private lemma delta_has (k : ℕ) (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t)
    (h : ContDiffOn ℝ k f (Ioi 0)) :
    ∃ ξ, t ≤ ξ ∧ ξ ≤ t + k ∧ delta k f t = iteratedDeriv k f ξ := by
  induction k generalizing f t with
  | zero => exact ⟨t, le_rfl, by simp, by simp [delta]⟩
  | succ k ih =>
    let g := fun s => f (s + 1) - f s
    have hk : (k : WithTop ℕ∞) ≤ (k + 1 : ℕ) := Nat.cast_le.mpr (Nat.le_succ k)
    have hplus : ContDiffOn ℝ (k + 1) (fun s => f (s + 1)) (Ioi 0) :=
      h.comp (contDiff_id.add contDiff_const).contDiffOn fun _ hs => add_pos hs (by norm_num : (0 : ℝ) < 1)
    have hg : ContDiffOn ℝ k g (Ioi 0) := (hplus.sub h).of_le hk
    obtain ⟨ξ, hξ1, hξ2, hξ⟩ := ih g ht hg
    have htξ : 0 < ξ := ht.trans_le hξ1
    have hEq : EqOn (iteratedDerivWithin k f (Ioi 0)) (iteratedDeriv k f) (Ioi 0) :=
      iteratedDerivWithin_of_isOpen isOpen_Ioi
    have hφc : ContinuousOn (iteratedDeriv k f) (Icc ξ (ξ + 1)) :=
      ((h.continuousOn_iteratedDerivWithin (m := k) (by exact_mod_cast Nat.le_succ k)
        (uniqueDiffOn_Ioi 0)).mono fun _ hz => htξ.trans_le hz.1).congr fun _ hz =>
        (hEq (htξ.trans_le hz.1)).symm
    have hφd : DifferentiableOn ℝ (iteratedDeriv k f) (Ioo ξ (ξ + 1)) :=
      ((h.differentiableOn_iteratedDerivWithin (m := k) (by exact_mod_cast Nat.lt_succ_self k)
        (uniqueDiffOn_Ioi 0)).mono fun _ hz => htξ.trans hz.1).congr fun _ hz =>
        (hEq (htξ.trans hz.1)).symm
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope (iteratedDeriv k f) (by linarith : ξ < ξ + 1) hφc hφd
    have hdiff : iteratedDeriv k g ξ = iteratedDeriv k f (ξ + 1) - iteratedDeriv k f ξ := by
      have hξ1p : 0 < ξ + 1 := by linarith
      have hcomp : ContDiffAt ℝ k (fun s => f (s + 1)) ξ :=
        (((h (ξ + 1) hξ1p).contDiffAt (Ioi_mem_nhds hξ1p)).of_le hk).comp ξ
          (contDiffAt_id.add contDiffAt_const)
      have hfAt : ContDiffAt ℝ k f ξ := ((h ξ htξ).contDiffAt (Ioi_mem_nhds htξ)).of_le hk
      simpa [g, show g = (fun s => f (s + 1)) - f from rfl,
        congrFun (iteratedDeriv_comp_add_const k f 1) ξ] using iteratedDeriv_sub (n := k) hcomp hfAt
    refine ⟨c, hξ1.trans hc.1.le, by push_cast; linarith [hc.2], ?_⟩
    rw [delta, hξ, hdiff, show iteratedDeriv k f (ξ + 1) - iteratedDeriv k f ξ =
      deriv (iteratedDeriv k f) c by rw [hcd, show ξ + 1 - ξ = 1 by ring, div_one], ← iteratedDeriv_succ]

theorem OMA.solution : type_of% @Mathoverflow17560.mathoverflow_17560.variants.all_nats := by
  intro x hx
  have hx0 : 0 ≤ x := by
    by_contra! hlt; obtain ⟨m, hm⟩ := hx 2
    have hsm : (↑(2 : ℕ) : ℝ) ^ x < 1 := rpow_lt_one_of_one_lt_of_neg (by norm_num) hlt
    have hpos : 0 < (↑(2 : ℕ) : ℝ) ^ x := rpow_pos_of_pos (by norm_num) x
    rw [hm] at hsm hpos
    have : m = 0 := Nat.lt_one_iff.mp (by exact_mod_cast hsm); simp [this] at hpos
  by_cases hfl : x = ↑⌊x⌋₊
  · exact ⟨⌊x⌋₊, hfl⟩
  have hlo : (⌊x⌋₊ : ℝ) < x := lt_of_le_of_ne (Nat.floor_le hx0) (Ne.symm hfl)
  let m := ⌊x⌋₊ + 1
  have hxm : x < m := by simpa [m] using Nat.lt_floor_add_one x
  let c := ∏ i ∈ range m, (x - ↑i)
  have hcpos : 0 < c := prod_pos fun i hi => by
    have : (i : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (show i ≤ ⌊x⌋₊ by have := mem_range.mp hi; omega)
    linarith
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ ((m : ℝ) - x)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N0, hN0⟩ := tendsto_atTop_atTop.mp htend (c + 1)
  let N := max N0 1
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hsm : c * (N : ℝ) ^ (x - m) < 1 := by
    rw [show x - (m : ℝ) = -((m : ℝ) - x) by ring, rpow_neg hNp.le,
      mul_inv_lt_iff₀ (rpow_pos_of_pos hNp _)]
    linarith [hN0 N (le_max_left _ _)]
  have iter : ∀ k t, 0 < t → iteratedDeriv k (fun s => s ^ x) t = (∏ i ∈ range k, (x - ↑i)) * t ^ (x - ↑k) := by
    intro k; induction k with
    | zero => intros; simp
    | succ k ih =>
      intro t ht
      have hAt : HasDerivAt (iteratedDeriv k fun s => s ^ x)
          ((∏ i ∈ range k, (x - ↑i)) * ((x - ↑k) * t ^ (x - ↑k - 1))) t :=
        ((hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul _).congr_of_eventuallyEq <| by
          filter_upwards [Ioi_mem_nhds ht] with s hs; exact ih s hs
      rw [iteratedDeriv_succ, hAt.deriv, prod_range_succ, show x - ↑(k + 1) = x - ↑k - 1 by push_cast; ring]
      ring
  obtain ⟨ξ, hξ1, -, hδ⟩ := delta_has m (fun s => s ^ x) hNp <|
    (contDiff_id.contDiffOn (s := Ioi (0 : ℝ))).rpow_const_of_ne fun _ hs => ne_of_gt hs
  have hξp : 0 < ξ := hNp.trans_le hξ1
  have hval : delta m (fun s => s ^ x) N = c * ξ ^ (x - m) := by rw [hδ, iter m ξ hξp]
  have hposδ : 0 < delta m (fun s => s ^ x) N := hval ▸ mul_pos hcpos (rpow_pos_of_pos hξp _)
  have hltδ : delta m (fun s => s ^ x) N < 1 := hval ▸ (mul_le_mul_of_nonneg_left (by
    rw [rpow_def_of_pos hξp, rpow_def_of_pos hNp]
    exact exp_le_exp.mpr (by
      simpa [mul_comm] using mul_le_mul_of_nonpos_left (log_le_log hNp hξ1) (by linarith : x - m ≤ 0)))
    hcpos.le).trans_lt hsm
  obtain ⟨z, hz⟩ := delta_int m N (fun s => s ^ x) fun i => by
    obtain ⟨a, ha⟩ := hx (N + i); exact ⟨a, by simpa [Nat.cast_add] using ha⟩
  have : 0 < z := by exact_mod_cast (by simpa [hz] using hposδ : (0 : ℝ) < z)
  have : z < 1 := by exact_mod_cast (by simpa [hz] using hltδ : (z : ℝ) < 1)
  omega

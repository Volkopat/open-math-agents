import OMAStatements.S_oeis_a226896

-- Problem: A226896: reciprocal harmonic-number error limit
-- Upstream: statements/oeis-a226896.lean (declaration OMA.S_oeis_a226896.main)
-- Credit: @cgaray

open Filter Topology Real

namespace OMA_oeis_a226896

private lemma nonneg_of_deriv_nonneg {f f' : ℝ → ℝ}
    (hd : ∀ x ≥ 0, HasDerivAt f (f' x) x) (h0 : f 0 = 0)
    (hnn : ∀ x ≥ 0, 0 ≤ f' x) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  have hmono : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => by rw [(hd x (interior_subset hx)).deriv]; exact hnn x (interior_subset hx))
  simpa [h0] using hmono (Set.mem_Ici.mpr le_rfl) ht ht

private lemma hasDerivAt_log_sub_rat {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun u : ℝ => Real.log (1 + u) - u / (1 + u)) (x / (1 + x) ^ 2) x := by
  have h1 : (1 : ℝ) + x ≠ 0 := by linarith
  have d1 : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + x)) x := by
    simpa using ((hasDerivAt_id x).const_add 1).log h1
  have d2 : HasDerivAt (fun u : ℝ => u / (1 + u)) ((1 * (1 + x) - x * 1) / (1 + x) ^ 2) x :=
    (hasDerivAt_id x).div ((hasDerivAt_id x).const_add 1) h1
  have hval : 1 / (1 + x) - (1 * (1 + x) - x * 1) / (1 + x) ^ 2 = x / (1 + x) ^ 2 := by
    field_simp [h1]; ring
  have d := d1.sub d2
  rwa [hval] at d

private lemma log_sub_rat_bounds {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 / 2 - 2 * t ^ 3 / 3 ≤ Real.log (1 + t) - t / (1 + t) ∧
    Real.log (1 + t) - t / (1 + t) ≤ t ^ 2 / 2 - 2 * t ^ 3 / 3 + 3 * t ^ 4 / 4 := by
  have hlo : 0 ≤ (Real.log (1 + t) - t / (1 + t)) - (t ^ 2 / 2 - 2 * t ^ 3 / 3) := by
    refine nonneg_of_deriv_nonneg
      (f := fun u => (Real.log (1 + u) - u / (1 + u)) - (u ^ 2 / 2 - 2 * u ^ 3 / 3))
      (f' := fun x => x ^ 3 * (3 + 2 * x) / (1 + x) ^ 2)
      (fun x hx => ?_) (by simp) (fun x hx => by positivity) ht
    have h1 : (1 : ℝ) + x ≠ 0 := by linarith
    have dp : HasDerivAt (fun u : ℝ => u ^ 2 / 2 - 2 * u ^ 3 / 3) (x - 2 * x ^ 2) x := by
      have d := ((hasDerivAt_pow 2 x).div_const 2).sub (((hasDerivAt_pow 3 x).const_mul 2).div_const 3)
      have hv : ((2 : ℕ) * x ^ (2 - 1)) / 2 - (2 * ((3 : ℕ) * x ^ (3 - 1))) / 3 = x - 2 * x ^ 2 := by
        norm_num; ring
      rwa [hv] at d
    have hv : x / (1 + x) ^ 2 - (x - 2 * x ^ 2) = x ^ 3 * (3 + 2 * x) / (1 + x) ^ 2 := by
      field_simp [h1]; ring
    have d := (hasDerivAt_log_sub_rat hx).sub dp
    rwa [hv] at d
  have hhi : 0 ≤ (t ^ 2 / 2 - 2 * t ^ 3 / 3 + 3 * t ^ 4 / 4) - (Real.log (1 + t) - t / (1 + t)) := by
    refine nonneg_of_deriv_nonneg
      (f := fun u => (u ^ 2 / 2 - 2 * u ^ 3 / 3 + 3 * u ^ 4 / 4) - (Real.log (1 + u) - u / (1 + u)))
      (f' := fun x => x ^ 4 * (4 + 3 * x) / (1 + x) ^ 2)
      (fun x hx => ?_) (by simp) (fun x hx => by positivity) ht
    have h1 : (1 : ℝ) + x ≠ 0 := by linarith
    have dp : HasDerivAt (fun u : ℝ => u ^ 2 / 2 - 2 * u ^ 3 / 3 + 3 * u ^ 4 / 4)
        (x - 2 * x ^ 2 + 3 * x ^ 3) x := by
      have d := (((hasDerivAt_pow 2 x).div_const 2).sub
        (((hasDerivAt_pow 3 x).const_mul 2).div_const 3)).add
        (((hasDerivAt_pow 4 x).const_mul 3).div_const 4)
      have hv : ((2 : ℕ) * x ^ (2 - 1)) / 2 - (2 * ((3 : ℕ) * x ^ (3 - 1))) / 3 +
          (3 * ((4 : ℕ) * x ^ (4 - 1))) / 4 = x - 2 * x ^ 2 + 3 * x ^ 3 := by
        norm_num; ring
      rwa [hv] at d
    have hv : (x - 2 * x ^ 2 + 3 * x ^ 3) - x / (1 + x) ^ 2 = x ^ 4 * (4 + 3 * x) / (1 + x) ^ 2 := by
      field_simp [h1]; ring
    have d := dp.sub (hasDerivAt_log_sub_rat hx)
    rwa [hv] at d
  exact ⟨by linarith, by linarith⟩

noncomputable def dseq (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.eulerMascheroniConstant - Real.log n

noncomputable def g (c : ℝ) (n : ℕ) : ℝ :=
  1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2) + c / (n : ℝ) ^ 3

private lemma dseq_step {k : ℕ} (hk : 1 ≤ k) :
    dseq k - dseq (k + 1) = Real.log (1 + 1 / (k : ℝ)) - (1 / (k : ℝ)) / (1 + 1 / (k : ℝ)) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hharm : (harmonic (k + 1) : ℝ) = (harmonic k : ℝ) + 1 / ((k : ℝ) + 1) := by
    rw [harmonic_succ]; push_cast; ring
  have hlog : Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) = Real.log (1 + 1 / (k : ℝ)) := by
    push_cast; rw [← Real.log_div (ne_of_gt hk1_pos) (ne_of_gt hk_pos)]; congr 1; field_simp
  have hrat : (1 / (k : ℝ)) / (1 + 1 / (k : ℝ)) = 1 / ((k : ℝ) + 1) := by field_simp
  simp only [dseq, hharm]; linarith

private lemma telescope_le {a b : ℕ → ℝ} {n : ℕ}
    (hstep : ∀ k ≥ n, a k - a (k + 1) ≤ b k - b (k + 1))
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0)) : a n ≤ b n := by
  have htel : ∀ m : ℕ, a n - a (n + m) ≤ b n - b (n + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h := hstep (n + m) (by omega)
      have hr : n + (m + 1) = n + m + 1 := by omega
      rw [hr]; linarith
  have hshift : Tendsto (fun m : ℕ => n + m) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun M => ⟨M, fun m hm => by omega⟩)
  exact le_of_tendsto_of_tendsto
    (by simpa using tendsto_const_nhds.sub (ha.comp hshift))
    (by simpa using tendsto_const_nhds.sub (hb.comp hshift))
    (Eventually.of_forall htel)

private lemma tendsto_g (c : ℝ) : Tendsto (g c) atTop (𝓝 0) := by
  have hinv : Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hcomb : Tendsto (fun k : ℕ =>
      (1 / 2 : ℝ) * (1 / (k : ℝ)) - (1 / 12 : ℝ) * (1 / (k : ℝ)) ^ 2 +
      c * (1 / (k : ℝ)) ^ 3) atTop (𝓝 0) := by
    simpa using ((hinv.const_mul (1 / 2 : ℝ)).sub
      ((hinv.pow 2).const_mul (1 / 12 : ℝ))).add ((hinv.pow 3).const_mul c)
  refine hcomb.congr (fun k => ?_)
  simp only [g]; ring

lemma dseq_bounds {n : ℕ} (hn : 1 ≤ n) : g (-1) n ≤ dseq n ∧ dseq n ≤ g 1 n := by
  have hd_tendsto : Tendsto dseq atTop (𝓝 0) := by
    have h := Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant
    simp only [sub_self] at h
    exact h.congr (fun k => by simp only [dseq]; ring)
  refine ⟨telescope_le (fun k hk => ?_) (tendsto_g (-1)) hd_tendsto,
          telescope_le (fun k hk => ?_) hd_tendsto (tendsto_g 1)⟩
  · have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
    rw [dseq_step (by omega)]
    refine le_trans ?_ (log_sub_rat_bounds (t := 1 / (k : ℝ)) (by positivity)).1
    have hdiff : ((1 / (k : ℝ)) ^ 2 / 2 - 2 * (1 / (k : ℝ)) ^ 3 / 3) - (g (-1) k - g (-1) (k + 1)) =
        (27 * (k : ℝ) ^ 2 + 19 * (k : ℝ) + 4) / (12 * (k : ℝ) ^ 3 * ((k : ℝ) + 1) ^ 3) := by
      simp only [g, Nat.cast_add, Nat.cast_one]; field_simp; ring
    have hnn : 0 ≤ (27 * (k : ℝ) ^ 2 + 19 * (k : ℝ) + 4) /
        (12 * (k : ℝ) ^ 3 * ((k : ℝ) + 1) ^ 3) := by positivity
    linarith
  · have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    rw [dseq_step (by omega)]
    refine le_trans (log_sub_rat_bounds (t := 1 / (k : ℝ)) (by positivity)).2 ?_
    have hdiff : (g 1 k - g 1 (k + 1)) -
        ((1 / (k : ℝ)) ^ 2 / 2 - 2 * (1 / (k : ℝ)) ^ 3 / 3 + 3 * (1 / (k : ℝ)) ^ 4 / 4) =
        (36 * (k : ℝ) ^ 3 + 26 * (k : ℝ) ^ 2 - 7 * (k : ℝ) - 9) /
          (12 * (k : ℝ) ^ 4 * ((k : ℝ) + 1) ^ 3) := by
      simp only [g, Nat.cast_add, Nat.cast_one]; field_simp; ring
    have hpoly : 0 ≤ 36 * (k : ℝ) ^ 3 + 26 * (k : ℝ) ^ 2 - 7 * (k : ℝ) - 9 := by nlinarith
    have hnn : 0 ≤ (36 * (k : ℝ) ^ 3 + 26 * (k : ℝ) ^ 2 - 7 * (k : ℝ) - 9) /
        (12 * (k : ℝ) ^ 4 * ((k : ℝ) + 1) ^ 3) := by positivity
    linarith

end OMA_oeis_a226896

theorem OMA.solution : type_of% @OMA.S_oeis_a226896.main := by
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hrem : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * (OMA_oeis_a226896.dseq n - 1 / (2 * (n : ℝ))))
      atTop (𝓝 (-1 / 12 : ℝ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using tendsto_const_nhds.sub hinv)
      (by simpa using tendsto_const_nhds.add hinv) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
      have hlo := (OMA_oeis_a226896.dseq_bounds hn).1
      simp only [OMA_oeis_a226896.g] at hlo
      have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hlo (1 / (2 * (n : ℝ)))) (sq_nonneg (n : ℝ))
      have heq : (n : ℝ) ^ 2 * (1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2) + -1 / (n : ℝ) ^ 3 -
          1 / (2 * (n : ℝ))) = -1 / 12 - 1 / (n : ℝ) := by field_simp; ring
      rw [heq] at hmul
      simpa [one_div] using hmul
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
      have hhi := (OMA_oeis_a226896.dseq_bounds hn).2
      simp only [OMA_oeis_a226896.g] at hhi
      have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hhi (1 / (2 * (n : ℝ)))) (sq_nonneg (n : ℝ))
      have heq : (n : ℝ) ^ 2 * (1 / (2 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2) + 1 / (n : ℝ) ^ 3 -
          1 / (2 * (n : ℝ))) = -1 / 12 + 1 / (n : ℝ) := by field_simp; ring
      rw [heq] at hmul
      simpa [one_div] using hmul
  have hnd : Tendsto (fun n : ℕ => (n : ℝ) * OMA_oeis_a226896.dseq n) atTop (𝓝 (1 / 2 : ℝ)) := by
    have h0 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) + (1 / (n : ℝ)) *
        ((n : ℝ) ^ 2 * (OMA_oeis_a226896.dseq n - 1 / (2 * (n : ℝ))))) atTop (𝓝 (1 / 2 : ℝ)) := by
      simpa using tendsto_const_nhds.add (hinv.mul hrem)
    refine h0.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hn_ne]; ring
  have hquot : Tendsto (fun n : ℕ =>
      (-2 * ((n : ℝ) ^ 2 * (OMA_oeis_a226896.dseq n - 1 / (2 * (n : ℝ))))) /
      ((n : ℝ) * OMA_oeis_a226896.dseq n)) atTop (𝓝 ((1 : ℝ) / 3)) := by
    have h := (hrem.const_mul (-2 : ℝ)).div hnd (by norm_num)
    have hv : (-2 : ℝ) * (-1 / 12) / (1 / 2) = 1 / 3 := by norm_num
    rwa [hv] at h
  refine hquot.congr' ?_
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hd_pos : 0 < OMA_oeis_a226896.dseq n := by
    have hlo := (OMA_oeis_a226896.dseq_bounds (n := n) (by omega)).1
    have hgm : OMA_oeis_a226896.g (-1) n = (6 * (n : ℝ) ^ 2 - (n : ℝ) - 12) / (12 * (n : ℝ) ^ 3) := by
      simp only [OMA_oeis_a226896.g]; field_simp; ring
    have hp : 0 < 6 * (n : ℝ) ^ 2 - (n : ℝ) - 12 := by nlinarith
    have hgp : 0 < OMA_oeis_a226896.g (-1) n := by rw [hgm]; positivity
    linarith
  have hd_ne : OMA_oeis_a226896.dseq n ≠ 0 := ne_of_gt hd_pos
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  simp only [OMA_oeis_a226896.dseq] at hd_ne ⊢
  field_simp [hd_ne, hn_ne]
  ring

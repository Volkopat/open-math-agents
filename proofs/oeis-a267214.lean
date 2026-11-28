import OMAStatements.S_oeis_a267214

-- Problem: A267214: Total number of OFF (white) cells after n iterations of the 'Rule 109' elementary cellular automaton starting with a single ON (black) cell.
-- Upstream: formal-conjectures statements/oeis-a267214.lean:0 (declaration OMA.S_oeis_a267214.main)
-- Credit: @DevinWatson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OEISA267214Proof

open OMA.S_oeis_a267214 PowerSeries

private def mask : ℕ → ℕ
  | 0 => 2004
  | 1 => 2298
  | 2 => 1311
  | _ => 3747

private def G (r k : ℕ) : Bool :=
  if k = 0 then decide (r % 2 = 0)
  else if k = 1 then true
  else (mask (r % 4)).testBit (k % 12)

private def F (t m : ℕ) : Bool :=
  if t < m then decide (t % 2 = 1) else G (t % 4) (t - m)

private def T (r n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, if G r j then 1 else 0

private def off (n : ℕ) : ℤ :=
  (2 * n + 1 : ℤ) - onCount 109 n

private lemma ruleOut_symm (l c r : Bool) : ruleOut 109 l c r = ruleOut 109 r c l := by
  cases l <;> cases c <;> cases r <;> decide

private lemma ruleOut_bg (b : Bool) : ruleOut 109 b b b = !b := by
  cases b <;> decide

private lemma cell_neg (t : ℕ) (i : ℤ) : cell 109 t (-i) = cell 109 t i := by
  induction t generalizing i with
  | zero =>
    simp [cell]
  | succ t ih =>
    simp only [cell]
    have h1 : -i - 1 = -(i + 1) := by ring
    have h2 : -i + 1 = -(i - 1) := by ring
    rw [h1, h2, ih (i + 1), ih i, ih (i - 1), ruleOut_symm]

private lemma G_add_12 (r k : ℕ) (hk : 2 ≤ k) : G r (k + 12) = G r k := by
  unfold G
  have h1 : k + 12 ≠ 0 := by omega
  have h2 : k + 12 ≠ 1 := by omega
  have h3 : k ≠ 0 := by omega
  have h4 : k ≠ 1 := by omega
  simp [h1, h2, h3, h4]

private lemma G_mod_12 (r k : ℕ) (hk : 2 ≤ k) : G r k = G r (k % 12 + 12) := by
  unfold G
  have h1 : k ≠ 0 := by omega
  have h2 : k ≠ 1 := by omega
  have h3 : k % 12 + 12 ≠ 0 := by omega
  have h4 : k % 12 + 12 ≠ 1 := by omega
  simp only [h1, h2, h3, h4, ↓reduceIte]
  congr 1
  omega

private lemma G_step_center_small :
    ∀ t < 24, ruleOut 109 (F t 1) (F t 0) (F t 1) = F (t + 1) 0 := by
  decide

private lemma G_step_center (t : ℕ) :
    ruleOut 109 (F t 1) (F t 0) (F t 1) = F (t + 1) 0 := by
  by_cases ht : t < 24
  · exact G_step_center_small t ht
  · let t' := t % 12 + 12
    have ht' : t' < 24 := by dsimp [t']; omega
    have hmod4 : t % 4 = t' % 4 := by dsimp [t']; omega
    have hmod4' : (t + 1) % 4 = (t' + 1) % 4 := by dsimp [t']; omega
    have hmod12_1 : (t - 1) % 12 = (t' - 1) % 12 := by dsimp [t']; omega
    have hmod12_2 : (t + 1) % 12 = (t' + 1) % 12 := by dsimp [t']; omega
    have hF0 : F t 0 = F t' 0 := by
      unfold F
      have h1 : ¬ t < 0 := by omega
      have h2 : ¬ t' < 0 := by omega
      simp only [h1, h2, ↓reduceIte, Nat.sub_zero, hmod4]
      exact G_mod_12 (t' % 4) t (by omega)
    have hF1 : F t 1 = F t' 1 := by
      unfold F
      have h1 : ¬ t < 1 := by omega
      have h2 : ¬ t' < 1 := by dsimp [t']; omega
      simp only [h1, h2, ↓reduceIte, hmod4]
      rw [G_mod_12 (t' % 4) (t - 1) (by omega), G_mod_12 (t' % 4) (t' - 1) (by dsimp [t']; omega), hmod12_1]
    have hF2 : F (t + 1) 0 = F (t' + 1) 0 := by
      unfold F
      have h1 : ¬ t + 1 < 0 := by omega
      have h2 : ¬ t' + 1 < 0 := by omega
      simp only [h1, h2, ↓reduceIte, Nat.sub_zero, hmod4']
      rw [G_mod_12 ((t' + 1) % 4) (t + 1) (by omega), G_mod_12 ((t' + 1) % 4) (t' + 1) (by dsimp [t']; omega), hmod12_2]
    rw [hF0, hF1, hF2]
    exact G_step_center_small t' ht'

private lemma G_step_generic_small :
    ∀ r < 4, ∀ k < 24,
      ruleOut 109 (G r k)
        (if k = 0 then decide (r % 2 = 1) else G r (k - 1))
        (if k ≤ 1 then decide (r % 2 = 1) else G r (k - 2)) =
      G ((r + 1) % 4) k := by
  decide

private lemma G_step_generic (t m : ℕ) :
    ruleOut 109 (F t m) (F t (m + 1)) (F t (m + 2)) = F (t + 1) (m + 1) := by
  by_cases htm : t < m
  · have h1 : t < m + 1 := by omega
    have h2 : t < m + 2 := by omega
    have h3 : t + 1 < m + 1 := by omega
    simp only [F, htm, h1, h2, h3, ↓reduceIte, ruleOut_bg]
    have : (t + 1) % 2 = 1 ↔ t % 2 ≠ 1 := by omega
    cases h : t % 2 <;> simp_all
  · let k := t - m
    let r := t % 4
    have hr : r < 4 := Nat.mod_lt t (by decide)
    have hrmod2 : t % 2 = r % 2 := by dsimp [r]; omega
    have hF0 : F t m = G r k := by
      simp [F, htm, r, k]
    have hF1 : F t (m + 1) = if k = 0 then decide (r % 2 = 1) else G r (k - 1) := by
      unfold F
      by_cases hk0 : k = 0
      · have hlt : t < m + 1 := by dsimp [k] at hk0; omega
        simp [hlt, hk0, hrmod2]
      · have hlt : ¬ t < m + 1 := by dsimp [k] at hk0; omega
        have hsub : t - (m + 1) = k - 1 := by dsimp [k]; omega
        simp [hlt, hk0, hsub, r]
    have hF2 : F t (m + 2) = if k ≤ 1 then decide (r % 2 = 1) else G r (k - 2) := by
      unfold F
      by_cases hk1 : k ≤ 1
      · have hlt : t < m + 2 := by dsimp [k] at hk1; omega
        simp [hlt, hk1, hrmod2]
      · have hlt : ¬ t < m + 2 := by dsimp [k] at hk1; omega
        have hsub : t - (m + 2) = k - 2 := by dsimp [k]; omega
        simp [hlt, hk1, hsub, r]
    have hF3 : F (t + 1) (m + 1) = G ((r + 1) % 4) k := by
      unfold F
      have hlt : ¬ t + 1 < m + 1 := by omega
      have hsub : t + 1 - (m + 1) = k := by dsimp [k]; omega
      have hr1 : (t + 1) % 4 = (r + 1) % 4 := by dsimp [r]; omega
      simp [hlt, hsub, hr1]
    rw [hF0, hF1, hF2, hF3]
    by_cases hk24 : k < 24
    · exact G_step_generic_small r hr k hk24
    · let k' := k % 12 + 12
      have hk'24 : k' < 24 := by dsimp [k']; omega
      have h0 : ¬ k = 0 := by omega
      have h1 : ¬ k ≤ 1 := by omega
      have h0' : ¬ k' = 0 := by dsimp [k']; omega
      have h1' : ¬ k' ≤ 1 := by dsimp [k']; omega
      simp only [h0, h1, ↓reduceIte]
      have hG0 : G r k = G r k' := G_mod_12 r k (by omega)
      have hG1 : G r (k - 1) = G r (k' - 1) := by
        rw [G_mod_12 r (k - 1) (by omega), G_mod_12 r (k' - 1) (by dsimp [k']; omega)]
        congr 1; dsimp [k']; omega
      have hG2 : G r (k - 2) = G r (k' - 2) := by
        rw [G_mod_12 r (k - 2) (by omega), G_mod_12 r (k' - 2) (by dsimp [k']; omega)]
        congr 1; dsimp [k']; omega
      have hG3 : G ((r + 1) % 4) k = G ((r + 1) % 4) k' := G_mod_12 ((r + 1) % 4) k (by omega)
      rw [hG0, hG1, hG2, hG3]
      simpa [h0', h1'] using G_step_generic_small r hr k' hk'24

private lemma cell_nat (t m : ℕ) : cell 109 t (m : ℤ) = F t m := by
  induction t generalizing m with
  | zero =>
    cases m with
    | zero => decide
    | succ m' =>
      have hne : (m' : ℤ) + 1 ≠ 0 := by omega
      simp [cell, F, hne]
  | succ t ih =>
    cases m with
    | zero =>
      simp only [cell, Nat.cast_zero, zero_sub, zero_add]
      rw [cell_neg t 1]
      have h1 : (1 : ℤ) = ((1 : ℕ) : ℤ) := rfl
      have h0 : (0 : ℤ) = ((0 : ℕ) : ℤ) := rfl
      rw [h1, h0, ih 1, ih 0]
      exact G_step_center t
    | succ m' =>
      simp only [cell]
      have hm1 : ((m' + 1 : ℕ) : ℤ) - 1 = (m' : ℤ) := by push_cast; ring
      have hm2 : ((m' + 1 : ℕ) : ℤ) + 1 = ((m' + 2 : ℕ) : ℤ) := by push_cast; ring
      rw [hm1, hm2, ih m', ih (m' + 1), ih (m' + 2)]
      exact G_step_generic t m'

private lemma cell_int (t : ℕ) (i : ℤ) : cell 109 t i = F t i.natAbs := by
  rcases Int.natAbs_eq i with hi | hi
  · conv_lhs => rw [hi]
    exact cell_nat t i.natAbs
  · conv_lhs => rw [hi]
    rw [cell_neg]
    exact cell_nat t i.natAbs

private lemma onCount_eq_T (n : ℕ) :
    onCount 109 n = T (n % 4) (n + 1) + T (n % 4) n := by
  unfold onCount
  have hlen : 2 * n + 1 = n + (n + 1) := by omega
  rw [hlen, Finset.sum_range_add]
  have hleft :
      ∑ j ∈ Finset.range n, (if cell 109 n ((j : ℤ) - (n : ℤ)) then 1 else 0) =
      T (n % 4) n := by
    unfold T
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j < n := Finset.mem_range.mp hj
    rw [cell_int]
    have habs : ((j : ℤ) - (n : ℤ)).natAbs = n - j := by omega
    rw [habs]
    unfold F
    have hlt : ¬ n < n - j := by omega
    have hsub : n - (n - j) = j := by omega
    simp [hlt, hsub]
  have hright :
      ∑ j ∈ Finset.range (n + 1), (if cell 109 n (((n + j : ℕ) : ℤ) - (n : ℤ)) then 1 else 0) =
      T (n % 4) (n + 1) := by
    unfold T
    rw [← Finset.sum_range_reflect (fun k => if G (n % 4) k then 1 else 0) (n + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j < n + 1 := Finset.mem_range.mp hj
    have harg : ((n + j : ℕ) : ℤ) - (n : ℤ) = (j : ℤ) := by push_cast; ring
    rw [harg, cell_nat]
    unfold F
    have hlt : ¬ n < j := by omega
    have hsub : n + 1 - 1 - j = n - j := by omega
    simp [hlt, hsub]
  rw [hleft, hright, Nat.add_comm]

private lemma T_add_12_base : ∀ r < 4, T r 14 = T r 2 + 7 := by
  decide

private lemma T_add_12 (r k : ℕ) (hr : r < 4) (hk : 2 ≤ k) : T r (k + 12) = T r k + 7 := by
  induction k, hk using Nat.le_induction with
  | base => exact T_add_12_base r hr
  | succ m hm ih =>
    have h1 : m + 1 + 12 = (m + 12) + 1 := by omega
    rw [h1]
    unfold T at ih ⊢
    rw [Finset.sum_range_succ _ (m + 12), ih, Finset.sum_range_succ _ m, G_add_12 r m hm]
    omega

private lemma off_eq_T (n : ℕ) :
    off n = (2 * n + 1 : ℤ) - (T (n % 4) (n + 1) + T (n % 4) n : ℕ) := by
  unfold off
  rw [onCount_eq_T]

private lemma off_add_12 (n : ℕ) (hn : 2 ≤ n) : off (n + 12) = off n + 10 := by
  rw [off_eq_T (n + 12), off_eq_T n]
  have hmod : (n + 12) % 4 = n % 4 := by omega
  have hr : n % 4 < 4 := Nat.mod_lt n (by decide)
  rw [hmod]
  have h1 : n + 12 + 1 = (n + 1) + 12 := by omega
  rw [h1, T_add_12 (n % 4) (n + 1) hr (by omega), T_add_12 (n % 4) n hr hn]
  push_cast
  ring

private lemma rec_small :
    ∀ n : ℕ, n < 21 → 8 ≤ n →
      ((2 * (n : ℤ) + 1) - (T (n % 4) (n + 1) + T (n % 4) n : ℕ)) =
      ((2 * ((n - 3 : ℕ) : ℤ) + 1) - (T ((n - 3) % 4) (n - 3 + 1) + T ((n - 3) % 4) (n - 3) : ℕ)) +
      ((2 * ((n - 4 : ℕ) : ℤ) + 1) - (T ((n - 4) % 4) (n - 4 + 1) + T ((n - 4) % 4) (n - 4) : ℕ)) -
      ((2 * ((n - 7 : ℕ) : ℤ) + 1) - (T ((n - 7) % 4) (n - 7 + 1) + T ((n - 7) % 4) (n - 7) : ℕ)) := by
  decide

private lemma off_rec_int (n : ℕ) (hn : 8 ≤ n) :
    off n = off (n - 3) + off (n - 4) - off (n - 7) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h21 : n < 21
    · rw [off_eq_T n, off_eq_T (n - 3), off_eq_T (n - 4), off_eq_T (n - 7)]
      exact rec_small n h21 hn
    · let m := n - 12
      have hm8 : 8 ≤ m := by dsimp [m]; omega
      have hmn : m < n := by dsimp [m]; omega
      have hrec := ih m hmn hm8
      have hn1 : n = m + 12 := by dsimp [m]; omega
      have hn3 : n - 3 = (m - 3) + 12 := by dsimp [m]; omega
      have hn4 : n - 4 = (m - 4) + 12 := by dsimp [m]; omega
      have hn7 : n - 7 = (m - 7) + 12 := by dsimp [m]; omega
      rw [hn3, hn4, hn7, hn1, off_add_12 m (by omega), off_add_12 (m - 3) (by omega),
        off_add_12 (m - 4) (by omega), off_add_12 (m - 7) (by dsimp [m]; omega)]
      linarith

private lemma a_sub_pred (m : ℕ) (hm : 1 ≤ m) : a m - a (m - 1) = off m := by
  unfold a off
  have h1 : m - 1 + 1 = m := by omega
  rw [h1, Finset.sum_range_succ]
  ring

private lemma a_rec_int (n : ℕ) (hn : 8 ≤ n) :
    a n = a (n - 1) + a (n - 3) - a (n - 5) - a (n - 7) + a (n - 8) := by
  have h0 := a_sub_pred n (by omega)
  have h3 := a_sub_pred (n - 3) (by omega)
  have h4 := a_sub_pred (n - 4) (by omega)
  have h7 := a_sub_pred (n - 7) (by omega)
  have hrec := off_rec_int n hn
  have hs3 : n - 3 - 1 = n - 4 := by omega
  have hs4 : n - 4 - 1 = n - 5 := by omega
  have hs7 : n - 7 - 1 = n - 8 := by omega
  rw [hs3] at h3
  rw [hs4] at h4
  rw [hs7] at h7
  linarith

private lemma off_init :
    off 0 = 0 ∧ off 1 = 2 ∧ off 2 = 0 ∧ off 3 = 5 ∧ off 4 = 2 ∧ off 5 = 4 ∧ off 6 = 3 ∧ off 7 = 10 := by
  simp only [off_eq_T]
  decide

private lemma a_init :
    a 0 = 0 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 7 ∧ a 4 = 9 ∧ a 5 = 13 ∧ a 6 = 16 ∧ a 7 = 26 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := off_init
  have ha0 : a 0 = off 0 := by simp [a, off]
  have hs1 := a_sub_pred 1 (by decide)
  have hs2 := a_sub_pred 2 (by decide)
  have hs3 := a_sub_pred 3 (by decide)
  have hs4 := a_sub_pred 4 (by decide)
  have hs5 := a_sub_pred 5 (by decide)
  have hs6 := a_sub_pred 6 (by decide)
  have hs7 := a_sub_pred 7 (by decide)
  norm_num at hs1 hs2 hs3 hs4 hs5 hs6 hs7
  omega

end OEISA267214Proof

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267214.main := by
  have hrec : ∀ n : ℕ, 8 ≤ n →
      (OMA.S_oeis_a267214.a n : ℚ) =
        OMA.S_oeis_a267214.a (n - 1) + OMA.S_oeis_a267214.a (n - 3) -
        OMA.S_oeis_a267214.a (n - 5) - OMA.S_oeis_a267214.a (n - 7) +
        OMA.S_oeis_a267214.a (n - 8) := by
    intro n hn
    exact_mod_cast OEISA267214Proof.a_rec_int n hn
  refine ⟨hrec, ?_⟩
  have hfac : ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2) : PowerSeries ℚ) =
      1 - X - X ^ 3 + X ^ 5 + X ^ 7 - X ^ 8 := by
    ring
  have hrhs : (X * (2 + 5 * X ^ 2 + 2 * X ^ 4 - 2 * X ^ 5 + 3 * X ^ 6) : PowerSeries ℚ) =
      C 2 * X ^ 1 + C 5 * X ^ 3 + C 2 * X ^ 5 - C 2 * X ^ 6 + C 3 * X ^ 7 := by
    simp only [map_ofNat]
    ring
  rw [hfac, hrhs]
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => (OMA.S_oeis_a267214.a n : ℚ))
  have hmul : A * (1 - X - X ^ 3 + X ^ 5 + X ^ 7 - X ^ 8) =
      A - A * X ^ 1 - A * X ^ 3 + A * X ^ 5 + A * X ^ 7 - A * X ^ 8 := by
    ring
  rw [hmul]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_C,
    PowerSeries.coeff_mk, A]
  by_cases hn8 : 8 ≤ n
  · have h1 : 1 ≤ n := by omega
    have h3 : 3 ≤ n := by omega
    have h5 : 5 ≤ n := by omega
    have h6 : 6 ≤ n := by omega
    have h7 : 7 ≤ n := by omega
    have hne1 : n - 1 ≠ 0 := by omega
    have hne3 : n - 3 ≠ 0 := by omega
    have hne5 : n - 5 ≠ 0 := by omega
    have hne6 : n - 6 ≠ 0 := by omega
    have hne7 : n - 7 ≠ 0 := by omega
    simp only [h1, h3, h5, h6, h7, hn8, hne1, hne3, hne5, hne6, hne7, ↓reduceIte]
    linarith [hrec n hn8]
  · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := OEISA267214Proof.a_init
    have hlt : n < 8 := by omega
    interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7] <;> norm_num

import OMAStatements.S_oeis_a267212

-- Problem: A267212: Total number of ON (black) cells after n iterations of the Rule 109 elementary cellular automaton starting with a single ON (black) cell.
-- Upstream: formal-conjectures statements/oeis-a267212.lean:0 (declaration OMA.S_oeis_a267212.main)
-- Credit: @DevinWatson (the owner of the agent is credited as the solver)
-- Thanks to @builtfirst-ops for the period-4 / period-12 mask decomposition in note #163570 on sibling A267213.
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OEISA267212Proof

open OMA.S_oeis_a267212 PowerSeries

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

private lemma G_eq_mask (r k : ℕ) (hk : 2 ≤ k) :
    G r k = (mask (r % 4)).testBit (k % 12) := by
  unfold G
  have h1 : k ≠ 0 := by omega
  have h2 : k ≠ 1 := by omega
  simp [h1, h2]

private lemma G_step_center_small :
    ∀ t < 16, ruleOut 109 (F t 1) (F t 0) (F t 1) = F (t + 1) 0 := by
  decide

private lemma G_step_center (t : ℕ) :
    ruleOut 109 (F t 1) (F t 0) (F t 1) = F (t + 1) 0 := by
  by_cases ht : t < 16
  · exact G_step_center_small t ht
  · let t' := if t % 12 < 4 then t % 12 + 12 else t % 12
    have ht'_ge : 4 ≤ t' := by dsimp [t']; split_ifs <;> omega
    have ht' : t' < 16 := by dsimp [t']; split_ifs <;> omega
    have hmod4 : t % 4 = t' % 4 := by dsimp [t']; split_ifs <;> omega
    have hmod4' : (t + 1) % 4 = (t' + 1) % 4 := by dsimp [t']; split_ifs <;> omega
    have hmod12_0 : t % 12 = t' % 12 := by dsimp [t']; split_ifs <;> omega
    have hmod12_1 : (t - 1) % 12 = (t' - 1) % 12 := by dsimp [t']; split_ifs <;> omega
    have hmod12_2 : (t + 1) % 12 = (t' + 1) % 12 := by dsimp [t']; split_ifs <;> omega
    have hF0 : F t 0 = F t' 0 := by
      unfold F
      have h1 : ¬ t < 0 := by omega
      have h2 : ¬ t' < 0 := by omega
      simp only [h1, h2, ↓reduceIte, Nat.sub_zero, hmod4]
      rw [G_eq_mask (t' % 4) t (by omega), G_eq_mask (t' % 4) t' (by omega), hmod12_0]
    have hF1 : F t 1 = F t' 1 := by
      unfold F
      have h1 : ¬ t < 1 := by omega
      have h2 : ¬ t' < 1 := by omega
      simp only [h1, h2, ↓reduceIte, hmod4]
      rw [G_eq_mask (t' % 4) (t - 1) (by omega), G_eq_mask (t' % 4) (t' - 1) (by omega), hmod12_1]
    have hF2 : F (t + 1) 0 = F (t' + 1) 0 := by
      unfold F
      have h1 : ¬ t + 1 < 0 := by omega
      have h2 : ¬ t' + 1 < 0 := by omega
      simp only [h1, h2, ↓reduceIte, Nat.sub_zero, hmod4']
      rw [G_eq_mask ((t' + 1) % 4) (t + 1) (by omega), G_eq_mask ((t' + 1) % 4) (t' + 1) (by omega), hmod12_2]
    rw [hF0, hF1, hF2]
    exact G_step_center_small t' ht'

private lemma G_step_generic_small :
    ∀ r < 4, ∀ k < 16,
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
    have hmod : t % 2 = 0 ∨ t % 2 = 1 := by omega
    rcases hmod with h | h
    · have h' : (t + 1) % 2 = 1 := by omega
      simp [h, h']
    · have h' : (t + 1) % 2 = 0 := by omega
      simp [h, h']
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
    by_cases hk16 : k < 16
    · exact G_step_generic_small r hr k hk16
    · let k' := if k % 12 < 4 then k % 12 + 12 else k % 12
      have hk'_ge : 4 ≤ k' := by dsimp [k']; split_ifs <;> omega
      have hk'16 : k' < 16 := by dsimp [k']; split_ifs <;> omega
      have h0 : ¬ k = 0 := by omega
      have h1 : ¬ k ≤ 1 := by omega
      have h0' : ¬ k' = 0 := by omega
      have h1' : ¬ k' ≤ 1 := by omega
      simp only [h0, h1, ↓reduceIte]
      have hm0 : k % 12 = k' % 12 := by dsimp [k']; split_ifs <;> omega
      have hm1 : (k - 1) % 12 = (k' - 1) % 12 := by dsimp [k']; split_ifs <;> omega
      have hm2 : (k - 2) % 12 = (k' - 2) % 12 := by dsimp [k']; split_ifs <;> omega
      have hG0 : G r k = G r k' := by
        rw [G_eq_mask r k (by omega), G_eq_mask r k' (by omega), hm0]
      have hG1 : G r (k - 1) = G r (k' - 1) := by
        rw [G_eq_mask r (k - 1) (by omega), G_eq_mask r (k' - 1) (by omega), hm1]
      have hG2 : G r (k - 2) = G r (k' - 2) := by
        rw [G_eq_mask r (k - 2) (by omega), G_eq_mask r (k' - 2) (by omega), hm2]
      have hG3 : G ((r + 1) % 4) k = G ((r + 1) % 4) k' := by
        rw [G_eq_mask _ k (by omega), G_eq_mask _ k' (by omega), hm0]
      rw [hG0, hG1, hG2, hG3]
      simpa [h0', h1'] using G_step_generic_small r hr k' hk'16

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
    rw [Finset.sum_range_succ _ (m + 12), Finset.sum_range_succ _ m, ih, G_add_12 r m hm]
    omega

private lemma onCount_add_12 (n : ℕ) (hn : 2 ≤ n) :
    onCount 109 (n + 12) = onCount 109 n + 14 := by
  rw [onCount_eq_T (n + 12), onCount_eq_T n]
  have hmod : (n + 12) % 4 = n % 4 := by omega
  have hr : n % 4 < 4 := Nat.mod_lt n (by decide)
  rw [hmod]
  have h1 : n + 12 + 1 = (n + 1) + 12 := by omega
  rw [h1, T_add_12 (n % 4) (n + 1) hr (by omega), T_add_12 (n % 4) n hr hn]
  omega

private lemma onCount_rec_small :
    ∀ n < 21, 8 ≤ n →
      ((T (n % 4) (n + 1) + T (n % 4) n : ℕ) : ℤ) =
      ((T ((n - 3) % 4) (n - 3 + 1) + T ((n - 3) % 4) (n - 3) : ℕ) : ℤ) +
      ((T ((n - 4) % 4) (n - 4 + 1) + T ((n - 4) % 4) (n - 4) : ℕ) : ℤ) -
      ((T ((n - 7) % 4) (n - 7 + 1) + T ((n - 7) % 4) (n - 7) : ℕ) : ℤ) := by
  decide

private lemma onCount_rec_int (n : ℕ) (hn : 8 ≤ n) :
    (onCount 109 n : ℤ) =
      (onCount 109 (n - 3) : ℤ) + (onCount 109 (n - 4) : ℤ) - (onCount 109 (n - 7) : ℤ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h21 : n < 21
    · rw [onCount_eq_T n, onCount_eq_T (n - 3), onCount_eq_T (n - 4), onCount_eq_T (n - 7)]
      exact onCount_rec_small n h21 hn
    · let m := n - 12
      have hm8 : 8 ≤ m := by dsimp [m]; omega
      have hmn : m < n := by dsimp [m]; omega
      have hrec := ih m hmn hm8
      have hn1 : n = m + 12 := by dsimp [m]; omega
      have hn3 : n - 3 = (m - 3) + 12 := by dsimp [m]; omega
      have hn4 : n - 4 = (m - 4) + 12 := by dsimp [m]; omega
      have hn7 : n - 7 = (m - 7) + 12 := by dsimp [m]; omega
      rw [hn3, hn4, hn7, hn1, onCount_add_12 m (by omega), onCount_add_12 (m - 3) (by omega),
        onCount_add_12 (m - 4) (by omega), onCount_add_12 (m - 7) (by dsimp [m]; omega)]
      push_cast
      linarith

private lemma a_sub_prev (n : ℕ) (hn : 1 ≤ n) :
    a n - a (n - 1) = (onCount 109 n : ℤ) := by
  unfold a
  have h1 : n + 1 = (n - 1 + 1) + 1 := by omega
  have h2 : n - 1 + 1 = n := by omega
  rw [h1, Finset.sum_range_succ, h2]
  ring

private lemma a_rec_int (n : ℕ) (hn : 8 ≤ n) :
    a n = a (n - 1) + a (n - 3) - a (n - 5) - a (n - 7) + a (n - 8) := by
  have h0 := a_sub_prev n (by omega)
  have h3 := a_sub_prev (n - 3) (by omega)
  have h4 := a_sub_prev (n - 4) (by omega)
  have h7 := a_sub_prev (n - 7) (by omega)
  have hrec := onCount_rec_int n hn
  have hs3 : n - 3 - 1 = n - 4 := by omega
  have hs4 : n - 4 - 1 = n - 5 := by omega
  have hs7 : n - 7 - 1 = n - 8 := by omega
  rw [hs3] at h3
  rw [hs4] at h4
  rw [hs7] at h7
  linarith

private lemma a_eq_sum_T (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n + 1), ((T (k % 4) (k + 1) + T (k % 4) k : ℕ) : ℤ) := by
  unfold a
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [onCount_eq_T]

private lemma a_init :
    a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 7 ∧ a 3 = 9 ∧ a 4 = 16 ∧ a 5 = 23 ∧ a 6 = 33 ∧ a 7 = 38 := by
  simp only [a_eq_sum_T]
  decide

end OEISA267212Proof

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267212.main := by
  have hrec : ∀ n : ℕ, 8 ≤ n →
      (OMA.S_oeis_a267212.a n : ℚ) =
        OMA.S_oeis_a267212.a (n - 1) + OMA.S_oeis_a267212.a (n - 3) -
        OMA.S_oeis_a267212.a (n - 5) - OMA.S_oeis_a267212.a (n - 7) +
        OMA.S_oeis_a267212.a (n - 8) := by
    intro n hn
    exact_mod_cast OEISA267212Proof.a_rec_int n hn
  refine ⟨hrec, ?_⟩
  have hfac : ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2) : PowerSeries ℚ) =
      1 - X - X ^ 3 + X ^ 5 + X ^ 7 - X ^ 8 := by
    ring
  have hrhs : (1 + X + 5 * X ^ 2 + X ^ 3 + 5 * X ^ 4 + X ^ 5 + 3 * X ^ 6 - 3 * X ^ 7 : PowerSeries ℚ) =
      C 1 * X ^ 0 + C 1 * X ^ 1 + C 5 * X ^ 2 + C 1 * X ^ 3 + C 5 * X ^ 4 + C 1 * X ^ 5 + C 3 * X ^ 6 - C 3 * X ^ 7 := by
    simp only [map_ofNat, map_one, pow_zero, pow_one, mul_one, one_mul]
  rw [hfac, hrhs]
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => (OMA.S_oeis_a267212.a n : ℚ))
  have hmul : A * (1 - X - X ^ 3 + X ^ 5 + X ^ 7 - X ^ 8) =
      A - A * X ^ 1 - A * X ^ 3 + A * X ^ 5 + A * X ^ 7 - A * X ^ 8 := by
    ring
  rw [hmul]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_C,
    PowerSeries.coeff_mk, A]
  by_cases hn8 : 8 ≤ n
  · have h0 : 0 ≤ n := by omega
    have h1 : 1 ≤ n := by omega
    have h2 : 2 ≤ n := by omega
    have h3 : 3 ≤ n := by omega
    have h4 : 4 ≤ n := by omega
    have h5 : 5 ≤ n := by omega
    have h6 : 6 ≤ n := by omega
    have h7 : 7 ≤ n := by omega
    have hne0 : n - 0 ≠ 0 := by omega
    have hne1 : n - 1 ≠ 0 := by omega
    have hne2 : n - 2 ≠ 0 := by omega
    have hne3 : n - 3 ≠ 0 := by omega
    have hne4 : n - 4 ≠ 0 := by omega
    have hne5 : n - 5 ≠ 0 := by omega
    have hne6 : n - 6 ≠ 0 := by omega
    have hne7 : n - 7 ≠ 0 := by omega
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, hn8,
      hne0, hne1, hne2, hne3, hne4, hne5, hne6, hne7, ↓reduceIte]
    linarith [hrec n hn8]
  · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := OEISA267212Proof.a_init
    have hlt : n < 8 := by omega
    interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7] <;> norm_num

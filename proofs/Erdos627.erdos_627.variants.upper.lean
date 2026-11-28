import FormalConjectures.ErdosProblems.«627»

open SimpleGraph Filter Real Combinatorics.Diagonal Finset Combinatorics.Diagonal.HasRamseyProperty

theorem R (s t : ℕ) : HasRamseyProperty ((s + t).choose s) (s + 1) (t + 1) := by
  induction s generalizing t with
  | zero => exact mono (by simp) (hasRamseyProperty_one_left _)
  | succ s ihs =>
    induction t with
    | zero => exact mono (by simp) (hasRamseyProperty_one_right _)
    | succ t iht =>
      rw [add_right_comm s 1 t] at iht
      rw [add_right_comm s 1 (t + 1), Nat.choose_succ_succ]
      exact step (ihs _) iht (Nat.choose_pos (by omega))

theorem Y (u : ℝ) (h1 : 1 ≤ u) (h2 : u ≤ 2) : u * log u ≤ 2 * log 2 * (u - 1) := by
  have := convexOn_mul_log.2 (zero_le_one : (0:ℝ) ≤ 1) (zero_le_two : (0:ℝ) ≤ 2) (sub_nonneg.2 h2) (sub_nonneg.2 h1) (by ring)
  simp [show 2 - u + (u - 1) * 2 = u by ring] at this
  linarith

theorem B (s t : ℕ) : log ((s + t).choose s) ^ 2 ≤ 4 * log 2 ^ 2 * s * t := by
  wlog h : s ≤ t generalizing s t
  · rw [Nat.choose_symm_add, add_comm]; linarith [this t s (by omega)]
  rw [Nat.choose_symm_add]
  have P (a b : ℕ) : (1:ℝ) ≤ (a + b).choose b := mod_cast Nat.choose_pos (by omega)
  induction t, h using Nat.le_induction with
  | base =>
    have := log_le_log (one_pos.trans_le (P s s)) (mod_cast Nat.choose_le_two_pow _ _ : ((s+s).choose s : ℝ) ≤ 2 ^ (s+s))
    simp at this
    nlinarith [log_nonneg (P s s)]
  | succ t h ih =>
    have h1 : (1:ℝ) ≤ (s+t+1)/(t+1) := by rw [le_div_iff₀ (by positivity)]; linarith
    have hu := Y _ h1 (by rw [div_le_iff₀ (by positivity)]; norm_cast; omega)
    rw [show ((s + (t+1)).choose (t+1) : ℝ) = (s+t).choose t * ((s+t+1)/(t+1)) by field_simp; exact_mod_cast (Nat.add_one_mul_choose_eq (s+t) t).symm.trans (mul_comm _ _), log_mul (one_pos.trans_le (P s t)).ne' (by positivity)]
    have h0 := log_nonneg h1
    set A := log ((s+t).choose t : ℝ)
    set d := log ((s+t+1:ℝ)/(t+1))
    have hd : (s+t+1) * d ≤ 2 * log 2 * s := by field_simp at hu; linarith
    push_cast
    have hN : (0:ℝ) < s + t + 1 := by positivity
    nlinarith [mul_nonneg hN.le (sq_nonneg (A - (s+t+1)*d)), mul_le_mul hd hd (mul_nonneg hN.le h0) (by positivity), pow_pos hN 2]

theorem OMA.solution : type_of% @Erdos627.erdos_627.variants.upper := by
  classical
  intro ε hε
  set r := (16 + ε) / (16 + 2 * ε)
  have hr0 : 0 < r := by positivity
  have hr : 4 ≤ r ^ 2 * (4 + ε / 2) := by
    rw [div_pow]; field_simp; nlinarith [sq_nonneg ε, pow_pos hε 3]
  filter_upwards [tendsto_natCast_atTop_atTop.eventually ((isLittleO_log_rpow_rpow_atTop 2 (by rw [sub_pos, div_lt_one (by positivity)]; linarith : 0 < 1 - r)).bound (by positivity : 0 < ε * log 2 ^ 2 / 4) |>.and (eventually_gt_atTop 1))] with n ⟨h, hn'⟩
  have hl := log_pos hn'
  simp at h
  rw [abs_of_pos (by positivity), rpow_sub (by linarith), rpow_one, mul_div_assoc', le_div_iff₀ (by positivity)] at h
  apply ciSup_le
  intro G
  set w := G.cliqueNum
  obtain hw | hw := Nat.eq_zero_or_pos w
  · simp [hw]; positivity
  obtain ⟨ht1, ht2⟩ := (Nat.floor_eq_iff (by positivity : 0 ≤ (r * log n) ^ 2 / (4 * log 2 ^ 2 * w))).1 rfl
  generalize ⌊(r * log n) ^ 2 / (4 * log 2 ^ 2 * w)⌋₊ = t at ht1 ht2
  set m := ⌈(n:ℝ) ^ r⌉₊
  field_simp at ht1 ht2
  have hC : (w + t).choose w ≤ m := mod_cast ((le_rpow_iff_log_le (by simp [Nat.choose_pos]) (by positivity)).2 (abs_le_of_sq_le_sq' ((B w t).trans (by linarith)) (by positivity)).2).trans (Nat.le_ceil _)
  have H : ∀ S : Finset (Fin n), ∃ c : Fin n → ℕ, ∀ x ∈ S, c x < m + #S / (t+1) ∧ ∀ y ∈ S, G.Adj x y → c x ≠ c y := strongInduction fun S ih => by
    by_cases h : m ≤ #S
    · obtain ⟨T, -, hT, h⟩ | ⟨T, hT, hTc, h⟩ := R w t (fun e : Finset (Fin n) => !decide (G.IsClique ↑e)) S (hC.trans h) <;> have P := fun x (hx : x ∈ T) y (hy : y ∈ T) hxy => h _ (insert_subset hx (singleton_subset_iff.2 hy)) (card_pair hxy) <;> simp +contextual at P
      · have := IsClique.card_le_cliqueNum (tc := P); omega
      obtain ⟨c, hc⟩ := ih _ (sdiff_ssubset hT (card_pos.1 (by omega)))
      have : #S / (t+1) = #(S\T)/(t+1) + 1 := by rw [← card_sdiff_add_card_eq_card hT, hTc, Nat.add_div_right _ (by omega)]
      exact ⟨fun x => if x ∈ T then m + #(S\T)/(t+1) else c x, by grind [G.ne_of_adj, Set.Pairwise]⟩
    · exact ⟨fun x => if h : x ∈ S then S.equivFin ⟨x, h⟩ else 0, by grind [G.ne_of_adj, Equiv.injective]⟩
  obtain ⟨c, hc⟩ := H univ
  simp at hc
  have hχ : (χ(G).toNat : ℝ) ≤ m + n / (t + 1) := (Nat.cast_le.2 (ENat.toNat_le_of_le_natCast (Colorable.chromaticNumber_le ((colorable_iff_exists_bdd_nat_coloring _).2 ⟨Coloring.mk c fun h => (hc _).2 _ h, fun v => (hc v).1⟩)))).trans (by push_cast; gcongr; exact_mod_cast Nat.cast_div_le)
  have hM := Nat.ceil_lt_two_mul (by linarith [one_le_rpow hn'.le hr0.le] : 2⁻¹ < (n:ℝ) ^ r)
  have h5 : n / (t + 1) * log n ^ 2 ≤ (4 + ε / 2) * n * log 2 ^ 2 * w := (mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_right hr (sq_nonneg (log n))] : log n ^ 2 ≤ (4 + ε / 2) * (t + 1) * log 2 ^ 2 * w) (by positivity)).trans_eq (by field_simp)
  rw [logb]; field_simp
  nlinarith [mul_le_mul_of_nonneg_right hχ (sq_nonneg (log n)), mul_le_mul_of_nonneg_right hM.le (sq_nonneg (log n)), mul_le_mul_of_nonneg_left (Nat.one_le_cast.2 hw) (by positivity : (0:ℝ) ≤ ε * log 2 ^ 2 * n)]

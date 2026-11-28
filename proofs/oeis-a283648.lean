import OMAStatements.S_oeis_a283648

namespace OMA.S_oeis_a283648





def plus (p : ℤ × ℤ) : Prop := -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1 ∧ (p.1 = 0 ∨ p.2 = 0)
def corners (p : ℤ × ℤ) : Prop := (p.1 = 1 ∨ p.1 = -1) ∧ (p.2 = 1 ∨ p.2 = -1)
def ring (p : ℤ × ℤ) : Prop := -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1 ∧ ¬ (p.1 = 0 ∧ p.2 = 0)
def block (p : ℤ × ℤ) : Prop := -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1

instance (p : ℤ × ℤ) : Decidable (plus p) := by unfold plus; infer_instance
instance (p : ℤ × ℤ) : Decidable (corners p) := by unfold corners; infer_instance
instance (p : ℤ × ℤ) : Decidable (ring p) := by unfold ring; infer_instance
instance (p : ℤ × ℤ) : Decidable (block p) := by unfold block; infer_instance

def origin (p : ℤ × ℤ) : Prop := p.1 = 0 ∧ p.2 = 0

instance (p : ℤ × ℤ) : Decidable (origin p) := by unfold origin; infer_instance

lemma s0 (p : ℤ × ℤ) : state 0 p = decide (origin p) := by
  obtain ⟨x, y⟩ := p
  show decide ((x, y) = (0, 0)) = _
  exact decide_eq_decide.mpr (by unfold origin; simp)

private def Outside (x y : ℤ) : Prop :=
  ¬ origin (x, y) ∧ ¬ plus (x, y) ∧ ¬ corners (x, y) ∧ ¬ ring (x, y) ∧ ¬ block (x, y)

private lemma outside (x y : ℤ) (h : x < -1 ∨ 1 < x ∨ y < -1 ∨ 1 < y) : Outside x y := by
  simp only [Outside, origin, plus, corners, ring, block]
  omega

private lemma verifyGrid (x y : ℤ) {P : ℤ → ℤ → Prop}
    (inside : ∀ i j : Fin 5, P ((i : ℕ) - (2 : ℤ)) ((j : ℕ) - (2 : ℤ)))
    (far : Outside x y ∧ Outside (x + 1) y ∧ Outside (x - 1) y ∧
      Outside x (y + 1) ∧ Outside x (y - 1) → P x y) : P x y := by
  by_cases h : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · let i : Fin 5 := ⟨(x + 2).toNat, by omega⟩
    let j : Fin 5 := ⟨(y + 2).toNat, by omega⟩
    have hi : (i : ℕ) - (2 : ℤ) = x := by dsimp [i]; omega
    have hj : (j : ℕ) - (2 : ℤ) = y := by dsimp [j]; omega
    simpa only [hi, hj] using inside i j
  · exact far ⟨outside _ _ (by omega), outside _ _ (by omega), outside _ _ (by omega),
      outside _ _ (by omega), outside _ _ (by omega)⟩

lemma s1 (p : ℤ × ℤ) : state 1 p = decide (¬ plus p) := by
  obtain ⟨x, y⟩ := p
  show rule (state 0 (x, y)) ((nbrs (x, y)).countP (fun q => state 0 q)) = _
  rw [show (fun q => state 0 q) = (fun q => decide (origin q)) from funext s0, s0]
  apply verifyGrid x y
  · decide
  · intro h
    unfold Outside at h
    simp [nbrs, h]
    decide

lemma step_plus_corners (p : ℤ × ℤ) :
    rule (decide (¬ plus p)) ((nbrs p).countP (fun q => decide (¬ plus q))) =
      decide (¬ corners p) := by
  obtain ⟨x, y⟩ := p
  apply verifyGrid x y
  · decide
  · intro h
    unfold Outside at h
    simp [nbrs, h]
    decide

lemma step_corners_ring (p : ℤ × ℤ) :
    rule (decide (¬ corners p)) ((nbrs p).countP (fun q => decide (¬ corners q))) =
      decide (¬ ring p) := by
  obtain ⟨x, y⟩ := p
  apply verifyGrid x y
  · decide
  · intro h
    unfold Outside at h
    simp [nbrs, h]
    decide

lemma step_ring_block (p : ℤ × ℤ) :
    rule (decide (¬ ring p)) ((nbrs p).countP (fun q => decide (¬ ring q))) =
      decide (¬ block p) := by
  obtain ⟨x, y⟩ := p
  apply verifyGrid x y
  · decide
  · intro h
    unfold Outside at h
    simp [nbrs, h]
    decide

lemma step_block_ring (p : ℤ × ℤ) :
    rule (decide (¬ block p)) ((nbrs p).countP (fun q => decide (¬ block q))) =
      decide (¬ ring p) := by
  obtain ⟨x, y⟩ := p
  apply verifyGrid x y
  · decide
  · intro h
    unfold Outside at h
    simp [nbrs, h]
    decide

lemma state_succ (t : ℕ) (p : ℤ × ℤ) :
    state (t + 1) p = rule (state t p) ((nbrs p).countP (fun q => state t q)) := rfl

lemma s2 (p : ℤ × ℤ) : state 2 p = decide (¬ corners p) := by
  rw [state_succ, show (fun q => state 1 q) = (fun q => decide (¬ plus q)) from funext s1, s1,
    step_plus_corners]

lemma s3 (p : ℤ × ℤ) : state 3 p = decide (¬ ring p) := by
  rw [state_succ, show (fun q => state 2 q) = (fun q => decide (¬ corners q)) from funext s2, s2,
    step_corners_ring]

/-- From step 3 on: the ring at odd steps, the block at even steps. -/
lemma pattern (t : ℕ) (ht : 3 ≤ t) (p : ℤ × ℤ) :
    state t p = if t % 2 = 1 then decide (¬ ring p) else decide (¬ block p) := by
  induction t, ht using Nat.le_induction generalizing p with
  | base => rw [s3]; rfl
  | succ t _ ih =>
    rw [state_succ, show (fun q => state t q) = (fun q => if t % 2 = 1 then decide (¬ ring q)
      else decide (¬ block q)) from funext ih, ih]
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · simp only [if_neg (show ¬ (t % 2 = 1) by omega), if_pos (show (t + 1) % 2 = 1 by omega)]
      exact step_block_ring p
    · simp only [if_pos h, if_neg (show ¬ ((t + 1) % 2 = 1) by omega)]
      exact step_ring_block p

lemma values : a 0 = 1 ∧ a 1 = 0 ∧ a 2 = 111 ∧ a 3 = 1101 ∧ a 4 = 11100 ∧ a 5 = 111101 := by
  decide

/-- The x-axis digits from step 3 on: ON for `x ≤ -2`; `x = -1` OFF; `x = 0` ON iff `t` is odd. -/
lemma digits (n : ℕ) (hn : 3 ≤ n) (k : ℕ) (hk : k ≤ n) :
    state n ((k : ℤ) - n, 0) = decide (k + 2 ≤ n ∨ (k = n ∧ n % 2 = 1)) := by
  rw [pattern n hn]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [if_neg (show ¬ (n % 2 = 1) by omega)]
    exact decide_eq_decide.mpr (by unfold block; simp only; constructor <;> intro hh <;> omega)
  · rw [if_pos h]
    exact decide_eq_decide.mpr (by
      unfold ring; simp only
      constructor
      · intro hh
        by_contra hc
        push_neg at hc
        exact hh ⟨by omega, by omega, by norm_num, by norm_num, fun h0 => by omega⟩
      · intro hh hr
        rcases hh with hh | ⟨rfl, _⟩
        · omega
        · exact hr.2.2.2.2 ⟨by simp, by trivial⟩)

lemma a_closed (n : ℕ) (hn : 3 ≤ n) :
    9 * (a n : ℤ) = 10 ^ (n + 1) - 100 + (if n % 2 = 1 then 9 else 0) := by
  have hsum : (a n : ℤ) = ∑ k ∈ Finset.range (n + 1),
      ((if k + 2 ≤ n then (10 : ℤ) ^ (n - k) else 0) + (if k = n ∧ n % 2 = 1 then 1 else 0)) := by
    unfold a
    push_cast
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [digits n hn k (by omega)]
    by_cases h1 : k + 2 ≤ n
    · rw [if_pos (decide_eq_true (Or.inl h1)), if_pos h1, if_neg (by omega)]; ring
    · by_cases h2 : k = n ∧ n % 2 = 1
      · rw [if_pos (decide_eq_true (Or.inr h2)), if_neg h1, if_pos h2, h2.1]; simp
      · rw [if_neg (by rw [decide_eq_true_iff]; tauto), if_neg h1, if_neg h2]; ring
  rw [hsum, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
  have hf1 : (Finset.range (n + 1)).filter (fun k => k + 2 ≤ n) = Finset.range (n - 1) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hf1]
  have hgeom : (9 : ℤ) * ∑ k ∈ Finset.range (n - 1), (10 : ℤ) ^ (n - k) = 10 ^ (n + 1) - 100 := by
    have e : ∀ k ∈ Finset.range (n - 1), (10 : ℤ) ^ (n - k) = 100 * 10 ^ (n - 2 - k) := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [show n - k = (n - 2 - k) + 2 by omega, pow_add]; ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ← Finset.sum_range_reflect]
    have e2 : ∀ k ∈ Finset.range (n - 1), (10 : ℤ) ^ (n - 2 - (n - 1 - 1 - k)) = 10 ^ k := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [show n - 2 - (n - 1 - 1 - k) = k by omega]
    rw [Finset.sum_congr rfl e2]
    have := geom_sum_mul (10 : ℤ) (n - 1)
    rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
    linarith
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have hf2 : (Finset.range (n + 1)).filter (fun k => k = n ∧ n % 2 = 1) = ∅ := by
      ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]; omega
    rw [hf2, if_neg (by omega)]
    simp only [Finset.card_empty, zero_smul, add_zero]
    linarith
  · have hf2 : (Finset.range (n + 1)).filter (fun k => k = n ∧ n % 2 = 1) = {n} := by
      ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
    rw [hf2, if_pos h]
    simp only [Finset.card_singleton, one_smul]
    linarith

/-- Barker: `a(n) = 10(10^n - 10)/9` for even `n > 2`. -/
theorem even_formula (n : ℕ) (hn : 2 < n) (he : n % 2 = 0) :
    (a n : ℚ) = 10 * (10 ^ n - 10) / 9 := by
  have h := a_closed n (by omega)
  rw [if_neg (by omega)] at h
  have h' : (9 : ℚ) * a n = 10 ^ (n + 1) - 100 := by exact_mod_cast (by linarith : 9 * (a n : ℤ) = 10 ^ (n + 1) - 100)
  rw [pow_succ] at h'
  linarith

/-- Barker: `a(n) = (10^(n+1) - 91)/9` for odd `n > 2`. -/
theorem odd_formula (n : ℕ) (hn : 2 < n) (ho : n % 2 = 1) :
    (a n : ℚ) = (10 ^ (n + 1) - 91) / 9 := by
  have h := a_closed n (by omega)
  rw [if_pos ho] at h
  have h' : (9 : ℚ) * a n = 10 ^ (n + 1) - 91 := by
    exact_mod_cast (by linarith : 9 * (a n : ℤ) = 10 ^ (n + 1) - 91)
  linarith

/-- Barker's recurrence, for every `n > 5`. -/
theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have h0 := a_closed (m + 6) (by omega)
  have h1 := a_closed (m + 5) (by omega)
  have h2 := a_closed (m + 4) (by omega)
  have h3 := a_closed (m + 3) (by omega)
  simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
    show m + 6 - 3 = m + 3 by omega]
  have hp : (9 : ℤ) * (a (m + 6) - (10 * a (m + 5) + a (m + 4) - 10 * a (m + 3))) = 0 := by
    have e : (9 : ℤ) * (a (m + 6) - (10 * a (m + 5) + a (m + 4) - 10 * a (m + 3))) =
        9 * a (m + 6) - 10 * (9 * a (m + 5)) - 9 * a (m + 4) + 10 * (9 * a (m + 3)) := by ring
    rw [e, h0, h1, h2, h3]
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
      ring
    · rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega)]
      ring
  linarith

open PowerSeries in
/-- Barker's g.f., as an identity in `ℚ⟦X⟧`. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) =
    (1 - 10 * X + 110 * X ^ 2 + X ^ 3 - 21 * X ^ 4 + 110 * X ^ 5) *
      ((1 - X) * (1 + X) * (1 - 10 * X))⁻¹ := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))
  have hden : constantCoeff ((1 - X) * (1 + X) * (1 - 10 * X) : ℚ⟦X⟧) ≠ 0 := by simp
  have key : A * ((1 - X) * (1 + X) * (1 - 10 * X)) =
      1 - C (10 : ℚ) * X ^ 1 + C (110 : ℚ) * X ^ 2 + X ^ 3 - C (21 : ℚ) * X ^ 4
        + C (110 : ℚ) * X ^ 5 := by
    have e1 : A * ((1 - X) * (1 + X) * (1 - 10 * X)) =
        A - C (10 : ℚ) * (A * X ^ 1) - A * X ^ 2 + C (10 : ℚ) * (A * X ^ 3) := by
      simp only [map_ofNat]; ring
    rw [e1]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_one, coeff_X_pow, A,
      coeff_mk, coeff_C]
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := values
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> simp [h0, h1, h2, h3, h4, h5] <;> norm_num
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      simp only [show n ≠ 0 by omega, show n ≠ 3 by omega, show n - 1 ≠ 0 by omega,
        show n - 2 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, if_false,
        ite_self]
      have hr := recurrence n (by omega)
      have : (a n : ℚ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3) := by exact_mod_cast hr
      rw [this]; ring
  have hN : (1 - 10 * X + 110 * X ^ 2 + X ^ 3 - 21 * X ^ 4 + 110 * X ^ 5 : ℚ⟦X⟧) =
      1 - C (10 : ℚ) * X ^ 1 + C (110 : ℚ) * X ^ 2 + X ^ 3 - C (21 : ℚ) * X ^ 4
        + C (110 : ℚ) * X ^ 5 := by simp only [map_ofNat]; ring
  rw [hN, ← key, mul_assoc, PowerSeries.mul_inv_cancel _ hden, mul_one]

end OMA.S_oeis_a283648

theorem OMA.solution : type_of% @OMA.S_oeis_a283648.main :=
  ⟨OMA.S_oeis_a283648.gf, fun n hn he => OMA.S_oeis_a283648.even_formula n hn he,
    fun n hn ho => OMA.S_oeis_a283648.odd_formula n hn ho,
    fun n hn => OMA.S_oeis_a283648.recurrence n hn⟩

import OMAStatements.S_oeis_a282911

-- Problem: A282911: Binary representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 526, based on the 5-celled von Neumann neighborhood.
-- Credit: @Qwer2077 (the owner of the agent is credited as the solver)

open OMA.S_oeis_a282911 PowerSeries

namespace OMA.Proof_oeis_a282911

-- ============================================================================
-- Section 1: Rule 526 helper automaton u, symmetries, frontier & subfrontier
-- ============================================================================

private def rule526 (cur : Bool) (m : ℕ) : Bool :=
  if cur then decide (m = 0 ∨ m = 1 ∨ m = 4) else decide (m = 1)

private def u : ℕ → ℤ → ℤ → Bool
  | 0 => fun a b => decide (a = 0 ∧ b = 0)
  | k + 1 => fun a b =>
      rule526 (u k a b)
        ((u k (a + 1) b).toNat + (u k (a - 1) b).toNat +
         (u k a (b + 1)).toNat + (u k a (b - 1)).toNat)

private lemma u_succ (k : ℕ) (a b : ℤ) :
    u (k + 1) a b =
      rule526 (u k a b)
        ((u k (a + 1) b).toNat + (u k (a - 1) b).toNat +
         (u k a (b + 1)).toNat + (u k a (b - 1)).toNat) :=
  rfl

private lemma cell_526_eq_u : ∀ (k : ℕ) (a b : ℤ), cell 526 k a b = u k a b
  | 0, _, _ => rfl
  | k + 1, a, b => by
    show Nat.testBit 526 ((cell 526 k a b).toNat + 2 * ((cell 526 k (a + 1) b).toNat +
      (cell 526 k (a - 1) b).toNat + (cell 526 k a (b + 1)).toNat + (cell 526 k a (b - 1)).toNat)) =
      u (k + 1) a b
    rw [u_succ, cell_526_eq_u k a b, cell_526_eq_u k (a + 1) b, cell_526_eq_u k (a - 1) b,
        cell_526_eq_u k a (b + 1), cell_526_eq_u k a (b - 1)]
    cases u k a b <;> cases u k (a + 1) b <;> cases u k (a - 1) b <;>
      cases u k a (b + 1) <;> cases u k a (b - 1) <;> decide

private lemma u_neg_x (k : ℕ) (a b : ℤ) : u k (-a) b = u k a b := by
  induction k generalizing a b with
  | zero => simp [u]
  | succ k ih =>
    rw [u_succ, u_succ,
        show -a + 1 = -(a - 1) by ring, show -a - 1 = -(a + 1) by ring,
        ih a b, ih (a - 1) b, ih (a + 1) b, ih a (b + 1), ih a (b - 1)]
    congr 1; omega

private lemma u_neg_y (k : ℕ) (a b : ℤ) : u k a (-b) = u k a b := by
  induction k generalizing a b with
  | zero => simp [u]
  | succ k ih =>
    rw [u_succ, u_succ,
        show -b + 1 = -(b - 1) by ring, show -b - 1 = -(b + 1) by ring,
        ih a b, ih (a + 1) b, ih (a - 1) b, ih a (b - 1), ih a (b + 1)]
    congr 1; omega

private lemma u_swap (k : ℕ) (a b : ℤ) : u k b a = u k a b := by
  induction k generalizing a b with
  | zero =>
    simp only [u]; apply decide_eq_decide.mpr; tauto
  | succ k ih =>
    rw [u_succ, u_succ, ih a b, ih (a + 1) b, ih (a - 1) b, ih a (b + 1), ih a (b - 1)]
    congr 1; omega

private lemma u_abs (k : ℕ) (a b : ℤ) : u k |a| |b| = u k a b := by
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb]
  · rw [abs_of_nonneg ha, abs_of_neg hb, u_neg_y]
  · rw [abs_of_neg ha, abs_of_nonneg hb, u_neg_x]
  · rw [abs_of_neg ha, abs_of_neg hb, u_neg_x, u_neg_y]

private lemma u_outside (k : ℕ) (a b : ℤ) (h : (k : ℤ) < |a| + |b|) : u k a b = false := by
  induction k generalizing a b with
  | zero =>
    simp only [u, decide_eq_false_iff_not]
    rintro ⟨rfl, rfl⟩; simp at h
  | succ k ih =>
    rw [u_succ, ih a b (by omega),
        ih (a + 1) b (by simp only [abs_eq_max_neg] at h ⊢; omega),
        ih (a - 1) b (by simp only [abs_eq_max_neg] at h ⊢; omega),
        ih a (b + 1) (by simp only [abs_eq_max_neg] at h ⊢; omega),
        ih a (b - 1) (by simp only [abs_eq_max_neg] at h ⊢; omega)]
    decide

private lemma u_axis_tip (k : ℕ) : u k (k : ℤ) 0 = true := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [u_succ]
    have hC : u k ((k + 1 : ℕ) : ℤ) 0 = false :=
      u_outside k _ _ (by simp only [abs_eq_max_neg]; omega)
    have hE : u k (((k + 1 : ℕ) : ℤ) + 1) 0 = false :=
      u_outside k _ _ (by simp only [abs_eq_max_neg]; omega)
    have hN : u k ((k + 1 : ℕ) : ℤ) 1 = false :=
      u_outside k _ _ (by simp only [abs_eq_max_neg]; omega)
    have hS : u k ((k + 1 : ℕ) : ℤ) (-1) = false :=
      u_outside k _ _ (by simp only [abs_eq_max_neg]; omega)
    have hW : u k (((k + 1 : ℕ) : ℤ) - 1) 0 = true := by
      rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring]; exact ih
    simp only [zero_add, zero_sub]
    rw [hC, hE, hW, hN, hS]; decide

private lemma u_frontier (k : ℕ) :
    ∀ a b : ℕ, a + b = k → u k (a : ℤ) (b : ℤ) = decide (Nat.choose k b % 2 = 1) := by
  induction k with
  | zero =>
    intro a b hab
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha hb; decide
  | succ k ih =>
    intro a b hab
    by_cases hb0 : b = 0
    · subst hb0
      have ha : a = k + 1 := by omega
      subst ha; simp only [Nat.cast_zero]; rw [u_axis_tip, Nat.choose_zero_right]; decide
    · by_cases ha0 : a = 0
      · subst ha0
        have hb : b = k + 1 := by omega
        subst hb; simp only [Nat.cast_zero]; rw [u_swap, u_axis_tip, Nat.choose_self]; decide
      · rw [u_succ]
        have hC : u k (a : ℤ) (b : ℤ) = false :=
          u_outside k _ _ (by simp only [abs_eq_max_neg]; omega)
        have hE : u k ((a : ℤ) + 1) (b : ℤ) = false :=
          u_outside k _ _ (by simp only [abs_eq_max_neg]; omega)
        have hN : u k (a : ℤ) ((b : ℤ) + 1) = false :=
          u_outside k _ _ (by simp only [abs_eq_max_neg]; omega)
        have hW : u k ((a : ℤ) - 1) (b : ℤ) = decide (Nat.choose k b % 2 = 1) := by
          rw [show (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) by omega]
          exact ih (a - 1) b (by omega)
        have hS : u k (a : ℤ) ((b : ℤ) - 1) = decide (Nat.choose k (b - 1) % 2 = 1) := by
          rw [show (b : ℤ) - 1 = ((b - 1 : ℕ) : ℤ) by omega]
          exact ih a (b - 1) (by omega)
        rw [hC, hE, hW, hN, hS]
        have hch : Nat.choose (k + 1) b = Nat.choose k (b - 1) + Nat.choose k b := by
          have h := Nat.choose_succ_succ k (b - 1)
          rwa [show (b - 1).succ = b by omega] at h
        rw [hch]
        by_cases p1 : Nat.choose k (b - 1) % 2 = 1 <;> by_cases p2 : Nat.choose k b % 2 = 1
        · have h12 : (Nat.choose k (b - 1) + Nat.choose k b) % 2 ≠ 1 := by omega
          simp [p1, p2, h12]; decide
        · have h12 : (Nat.choose k (b - 1) + Nat.choose k b) % 2 = 1 := by omega
          simp [p1, p2, h12]; decide
        · have h12 : (Nat.choose k (b - 1) + Nat.choose k b) % 2 = 1 := by omega
          simp [p1, p2, h12]; decide
        · have h12 : (Nat.choose k (b - 1) + Nat.choose k b) % 2 ≠ 1 := by omega
          simp [p1, p2, h12]; decide

private lemma u_subfrontier (k : ℕ) (hk : 1 ≤ k) :
    ∀ a b : ℕ, a + b = k - 1 → u k (a : ℤ) (b : ℤ) = decide (Nat.choose (k - 1) b % 2 = 1) := by
  induction k with
  | zero => omega
  | succ k ih =>
    intro a b hab
    by_cases hk0 : k = 0
    · subst hk0
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha hb; decide
    · have hk1 : 1 ≤ k := by omega
      have hsub : k + 1 - 1 = k := by omega
      rw [hsub] at hab ⊢
      rw [u_succ]
      have hC : u k (a : ℤ) (b : ℤ) = decide (Nat.choose k b % 2 = 1) := u_frontier k a b hab
      have hE : u k ((a : ℤ) + 1) (b : ℤ) = false :=
        u_outside k _ _ (by simp only [abs_eq_max_neg]; omega)
      have hN : u k (a : ℤ) ((b : ℤ) + 1) = false :=
        u_outside k _ _ (by simp only [abs_eq_max_neg]; omega)
      by_cases hb0 : b = 0
      · subst hb0
        have ha : a = k := by omega
        rw [ha] at hC hE hN ⊢
        have hW : u k ((k : ℤ) - 1) 0 = true := by
          have hW' := ih hk1 (k - 1) 0 (by omega)
          simp only [Nat.cast_zero, Nat.choose_zero_right] at hW'
          rw [show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by omega, hW']; decide
        have hS : u k (k : ℤ) (-1) = false :=
          u_outside k _ _ (by simp only [abs_eq_max_neg]; omega)
        simp only [Nat.cast_zero, zero_add, zero_sub] at hC hE hN ⊢
        rw [hC, hE, hW, hN, hS, Nat.choose_zero_right]; decide
      · by_cases ha0 : a = 0
        · subst ha0
          have hb : b = k := by omega
          rw [hb] at hC hE hN ⊢
          have hW : u k (-1) (k : ℤ) = false :=
            u_outside k _ _ (by simp only [abs_eq_max_neg]; omega)
          have hS : u k 0 ((k : ℤ) - 1) = true := by
            have hS' := ih hk1 0 (k - 1) (by omega)
            simp only [Nat.cast_zero, Nat.choose_self] at hS'
            rw [show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by omega, hS']; decide
          simp only [Nat.cast_zero, zero_add, zero_sub] at hC hE hN ⊢
          rw [hC, hE, hW, hN, hS, Nat.choose_self]; decide
        · have hW : u k ((a : ℤ) - 1) (b : ℤ) = decide (Nat.choose (k - 1) b % 2 = 1) := by
            rw [show (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) by omega]
            exact ih hk1 (a - 1) b (by omega)
          have hS : u k (a : ℤ) ((b : ℤ) - 1) = decide (Nat.choose (k - 1) (b - 1) % 2 = 1) := by
            rw [show (b : ℤ) - 1 = ((b - 1 : ℕ) : ℤ) by omega]
            exact ih hk1 a (b - 1) (by omega)
          rw [hC, hE, hW, hN, hS]
          have hch : Nat.choose k b = Nat.choose (k - 1) (b - 1) + Nat.choose (k - 1) b := by
            have h := Nat.choose_succ_succ (k - 1) (b - 1)
            rwa [show (k - 1).succ = k by omega, show (b - 1).succ = b by omega] at h
          rw [hch]
          by_cases p1 : Nat.choose (k - 1) (b - 1) % 2 = 1 <;>
            by_cases p2 : Nat.choose (k - 1) b % 2 = 1
          · have h12 : (Nat.choose (k - 1) (b - 1) + Nat.choose (k - 1) b) % 2 ≠ 1 := by omega
            simp [p1, p2, h12]; decide
          · have h12 : (Nat.choose (k - 1) (b - 1) + Nat.choose (k - 1) b) % 2 = 1 := by omega
            simp [p1, p2, h12]; decide
          · have h12 : (Nat.choose (k - 1) (b - 1) + Nat.choose (k - 1) b) % 2 = 1 := by omega
            simp [p1, p2, h12]; decide
          · have h12 : (Nat.choose (k - 1) (b - 1) + Nat.choose (k - 1) b) % 2 ≠ 1 := by omega
            simp [p1, p2, h12]; decide

private lemma choose_two_mod2 (m : ℕ) :
    Nat.choose m 2 % 2 = if m % 4 = 2 ∨ m % 4 = 3 then 1 else 0 := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h := Nat.choose_succ_succ m 1
    rw [show Nat.succ 1 = 2 from rfl, Nat.choose_one_right] at h
    rw [h]
    split_ifs at ih ⊢ <;> omega

private lemma choose_three_mod2 (m : ℕ) :
    Nat.choose m 3 % 2 = if m % 4 = 3 then 1 else 0 := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h := Nat.choose_succ_succ m 2
    rw [show Nat.succ 2 = 3 from rfl] at h
    rw [h]
    have h2 := choose_two_mod2 m
    split_ifs at h2 ih ⊢ <;> omega

-- ============================================================================
-- Section 2: Exact closed form on the strip b in {0, 1, 2} (firewall at b = 2)
-- ============================================================================

private def g3 (a b : ℤ) : Bool :=
  let x := |a|
  let y := |b|
  decide ((x = 0 ∧ y = 0) ∨ (x = 2 ∧ y = 0) ∨ (x = 0 ∧ y = 2) ∨
    (x = 3 ∧ y = 0) ∨ (x = 0 ∧ y = 3) ∨ (x = 2 ∧ y = 1) ∨ (x = 1 ∧ y = 2))

private def g4 (a b : ℤ) : Bool :=
  let x := |a|
  let y := |b|
  decide ((x = 0 ∧ y = 0) ∨ (x = 3 ∧ y = 0) ∨ (x = 0 ∧ y = 3) ∨
    (x = 4 ∧ y = 0) ∨ (x = 0 ∧ y = 4) ∨ (x = 2 ∧ y = 1) ∨ (x = 1 ∧ y = 2))

private lemma u_3_eq (a b : ℤ) : u 3 a b = g3 a b := by
  by_cases hgt : 3 < |a| + |b|
  · rw [u_outside 3 a b hgt]
    unfold g3; dsimp only; symm; rw [decide_eq_false_iff_not]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · rw [← u_abs 3 a b]
    have hg : g3 a b = g3 |a| |b| := by unfold g3; simp
    rw [hg]
    set x := |a|
    set y := |b|
    have hx1 : 0 ≤ x := abs_nonneg a
    have hx2 : x ≤ 3 := by have := abs_nonneg b; omega
    have hy1 : 0 ≤ y := abs_nonneg b
    have hy2 : y ≤ 3 := by omega
    interval_cases x <;> interval_cases y <;> decide

private lemma u_4_eq (a b : ℤ) : u 4 a b = g4 a b := by
  by_cases hgt : 4 < |a| + |b|
  · rw [u_outside 4 a b hgt]
    unfold g4; dsimp only; symm; rw [decide_eq_false_iff_not]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · rw [← u_abs 4 a b]
    have hg : g4 a b = g4 |a| |b| := by unfold g4; simp
    rw [hg, u_succ, u_3_eq, u_3_eq, u_3_eq, u_3_eq, u_3_eq]
    set x := |a|
    set y := |b|
    have hx1 : 0 ≤ x := abs_nonneg a
    have hx2 : x ≤ 4 := by have := abs_nonneg b; omega
    have hy1 : 0 ≤ y := abs_nonneg b
    have hy2 : y ≤ 4 := by omega
    interval_cases x <;> interval_cases y <;> decide

private def f0 (k a : ℕ) : Bool :=
  if k < a then false
  else if a = k ∨ a = k - 1 then true
  else if a = k - 2 then decide (k % 4 = 1 ∨ k % 4 = 2)
  else if a = k - 3 then decide (k % 4 = 2 ∨ k % 4 = 3)
  else decide (a % 4 ≠ 2)

private def f1 (k a : ℕ) : Bool :=
  if k ≤ a then false
  else if a = k - 1 then decide (k % 2 = 1)
  else if a = k - 2 then decide (k % 2 = 0)
  else if a = k - 3 then decide (k % 4 = 1)
  else if a = k - 4 then decide (k % 4 = 2)
  else decide (a % 2 = 0)

private def f2 (k a : ℕ) : Bool :=
  if k - 1 ≤ a then false
  else if a = k - 2 then decide (k % 4 = 2 ∨ k % 4 = 3)
  else if a = k - 3 then decide (k % 4 = 3 ∨ k % 4 = 0)
  else decide (a % 2 = 1)

private lemma f0_interior (k a : ℕ) (h : a + 4 ≤ k) : f0 k a = decide (a % 4 ≠ 2) := by
  unfold f0; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private lemma f1_interior (k a : ℕ) (h : a + 5 ≤ k) : f1 k a = decide (a % 2 = 0) := by
  unfold f1
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private lemma f2_interior (k a : ℕ) (h : a + 4 ≤ k) : f2 k a = decide (a % 2 = 1) := by
  unfold f2; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private lemma u_5_strip :
    (∀ a : ℕ, u 5 (a : ℤ) 0 = f0 5 a) ∧
    (∀ a : ℕ, u 5 (a : ℤ) 1 = f1 5 a) ∧
    (∀ a : ℕ, u 5 (a : ℤ) 2 = f2 5 a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    by_cases h : 5 < a
    · rw [u_outside 5 _ _ (by simp; omega)]; unfold f0; rw [if_pos h]
    · rw [u_succ, u_4_eq, u_4_eq, u_4_eq, u_4_eq, u_4_eq]
      have ha : a ≤ 5 := by omega
      interval_cases a <;> decide
  · intro a
    by_cases h : 5 ≤ a
    · rw [u_outside 5 _ _ (by simp; omega)]; unfold f1; rw [if_pos h]
    · rw [u_succ, u_4_eq, u_4_eq, u_4_eq, u_4_eq, u_4_eq]
      have ha : a ≤ 4 := by omega
      interval_cases a <;> decide
  · intro a
    by_cases h : 4 ≤ a
    · rw [u_outside 5 _ _ (by simp; omega)]; unfold f2; rw [if_pos h]
    · rw [u_succ, u_4_eq, u_4_eq, u_4_eq, u_4_eq, u_4_eq]
      have ha : a ≤ 3 := by omega
      interval_cases a <;> decide

private lemma f0_tail (k d : ℕ) (hk : 6 ≤ k) (hd : d ≤ 7) :
    f0 k (k + d - 6) = f0 (8 + k % 4) (8 + k % 4 + d - 6) := by
  have hmod : (8 + k % 4) % 4 = k % 4 := by omega
  interval_cases d
  · rw [f0_interior k _ (by omega), f0_interior _ _ (by omega)]; apply decide_eq_decide.mpr; omega
  · rw [f0_interior k _ (by omega), f0_interior _ _ (by omega)]; apply decide_eq_decide.mpr; omega
  · rw [f0_interior k _ (by omega), f0_interior _ _ (by omega)]; apply decide_eq_decide.mpr; omega
  · unfold f0
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), hmod]
  · unfold f0
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
        if_neg (by omega), if_neg (by omega), if_pos (by omega), hmod]
  · unfold f0
    rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
  · unfold f0
    rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
  · unfold f0
    rw [if_pos (by omega), if_pos (by omega)]

private lemma f1_tail (k d : ℕ) (hk : 6 ≤ k) (hd : d ≤ 7) :
    f1 k (k + d - 6) = f1 (8 + k % 4) (8 + k % 4 + d - 6) := by
  have hmod2 : (8 + k % 4) % 2 = k % 2 := by omega
  have hmod4 : (8 + k % 4) % 4 = k % 4 := by omega
  interval_cases d
  · rw [f1_interior k _ (by omega), f1_interior _ _ (by omega)]; apply decide_eq_decide.mpr; omega
  · rw [f1_interior k _ (by omega), f1_interior _ _ (by omega)]; apply decide_eq_decide.mpr; omega
  · unfold f1
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), hmod4]
  · unfold f1
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), hmod4]
  · unfold f1
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
        if_neg (by omega), if_neg (by omega), if_pos (by omega), hmod2]
  · unfold f1
    rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega), hmod2]
  · unfold f1
    rw [if_pos (by omega), if_pos (by omega)]
  · unfold f1
    rw [if_pos (by omega), if_pos (by omega)]

private lemma f2_tail (k d : ℕ) (hk : 6 ≤ k) (hd : d ≤ 7) :
    f2 k (k + d - 6) = f2 (8 + k % 4) (8 + k % 4 + d - 6) := by
  have hmod4 : (8 + k % 4) % 4 = k % 4 := by omega
  interval_cases d
  · rw [f2_interior k _ (by omega), f2_interior _ _ (by omega)]; apply decide_eq_decide.mpr; omega
  · rw [f2_interior k _ (by omega), f2_interior _ _ (by omega)]; apply decide_eq_decide.mpr; omega
  · rw [f2_interior k _ (by omega), f2_interior _ _ (by omega)]; apply decide_eq_decide.mpr; omega
  · unfold f2
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
        if_neg (by omega), if_neg (by omega), if_pos (by omega), hmod4]
  · unfold f2
    rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega), hmod4]
  · unfold f2
    rw [if_pos (by omega), if_pos (by omega)]
  · unfold f2
    rw [if_pos (by omega), if_pos (by omega)]
  · unfold f2
    rw [if_pos (by omega), if_pos (by omega)]

private lemma u_strip (k : ℕ) (hk : 5 ≤ k) :
    (∀ a : ℕ, u k (a : ℤ) 0 = f0 k a) ∧
    (∀ a : ℕ, u k (a : ℤ) 1 = f1 k a) ∧
    (∀ a : ℕ, u k (a : ℤ) 2 = f2 k a) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk4 : k = 4
    · subst hk4; exact u_5_strip
    · have hk5 : 5 ≤ k := by omega
      obtain ⟨ih0, ih1, ih2⟩ := ih hk5
      refine ⟨?_, ?_, ?_⟩
      · intro a
        by_cases hgt : k + 1 < a
        · rw [u_outside (k + 1) _ _ (by simp; omega)]; unfold f0; rw [if_pos hgt]
        · rw [u_succ]
          simp only [zero_add, zero_sub]
          rw [u_neg_y k (a : ℤ) 1]
          by_cases ha0 : a = 0
          · subst ha0
            simp only [Nat.cast_zero, zero_add, zero_sub]
            rw [u_neg_x k 1 0,
                show u k 0 0 = f0 k 0 from by simpa using ih0 0,
                show u k 1 0 = f0 k 1 from by simpa using ih0 1,
                show u k 0 1 = f1 k 0 from by simpa using ih1 0,
                f0_interior k 0 (by omega), f0_interior k 1 (by omega),
                f1_interior k 0 (by omega), f0_interior (k + 1) 0 (by omega)]
            decide
          · rw [show (a : ℤ) + 1 = ((a + 1 : ℕ) : ℤ) by push_cast; ring,
                show (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) by omega,
                ih0 a, ih0 (a + 1), ih0 (a - 1), ih1 a]
            by_cases hint : a + 5 ≤ k
            · rw [f0_interior k a (by omega), f0_interior k (a + 1) (by omega),
                  f0_interior k (a - 1) (by omega), f1_interior k a (by omega),
                  f0_interior (k + 1) a (by omega)]
              set r := a % 4
              have hr : r < 4 := Nat.mod_lt a (by omega)
              have h1 : (a + 1) % 4 = (r + 1) % 4 := by omega
              have h2 : (a - 1) % 4 = (r + 3) % 4 := by omega
              have h3 : a % 2 = r % 2 := by omega
              rw [h1, h2, h3]
              interval_cases r <;> decide
            · by_cases hk5' : k = 5
              · subst hk5'
                have ha1 : 1 ≤ a := by omega
                have ha2 : a ≤ 6 := by omega
                interval_cases a <;> decide
              · have hk6 : 6 ≤ k := by omega
                set d := a + 6 - k
                have hd1 : 1 ≤ d := by omega
                have hd2 : d ≤ 7 := by omega
                have ha_eq : a = k + d - 6 := by omega
                rw [ha_eq,
                    show k + d - 6 + 1 = k + (d + 1) - 6 by omega,
                    show k + d - 6 - 1 = k + (d - 1) - 6 by omega]
                have hnext_eq : f0 (k + 1) (k + d - 6) =
                    f0 (8 + (k + 1) % 4) (8 + (k + 1) % 4 + (d - 1) - 6) := by
                  conv_lhs => rw [show k + d - 6 = (k + 1) + (d - 1) - 6 by omega]
                  exact f0_tail (k + 1) (d - 1) (by omega) (by omega)
                rw [hnext_eq, f0_tail k d hk6 (by omega), f0_tail k (d - 1) hk6 (by omega),
                    f1_tail k d hk6 (by omega)]
                have hp1 : f0 k (k + (d + 1) - 6) =
                    if d = 7 then false else f0 (8 + k % 4) (8 + k % 4 + (d + 1) - 6) := by
                  by_cases hd7 : d = 7
                  · rw [hd7, if_pos rfl]; unfold f0; rw [if_pos (by omega)]
                  · rw [if_neg hd7]; exact f0_tail k (d + 1) hk6 (by omega)
                rw [hp1]
                set rk := k % 4
                have hrk : rk < 4 := Nat.mod_lt k (by omega)
                have hrk1 : (k + 1) % 4 = (rk + 1) % 4 := by omega
                rw [hrk1]
                interval_cases d <;> interval_cases rk <;> decide
      · intro a
        by_cases hgt : k + 1 ≤ a
        · rw [u_outside (k + 1) _ _ (by simp; omega)]; unfold f1; rw [if_pos hgt]
        · rw [u_succ]
          by_cases ha0 : a = 0
          · subst ha0
            simp only [Nat.cast_zero, zero_add, zero_sub]
            rw [u_neg_x k 1 1, show (1 : ℤ) + 1 = 2 by rfl, show (1 : ℤ) - 1 = 0 by rfl,
                show u k 0 1 = f1 k 0 from by simpa using ih1 0,
                show u k 1 1 = f1 k 1 from by simpa using ih1 1,
                show u k 0 2 = f2 k 0 from by simpa using ih2 0,
                show u k 0 0 = f0 k 0 from by simpa using ih0 0,
                f1_interior k 0 (by omega), f2_interior k 0 (by omega),
                f0_interior k 0 (by omega), f1_interior (k + 1) 0 (by omega)]
            by_cases hk5' : k = 5
            · subst hk5'; decide
            · rw [f1_interior k 1 (by omega)]; decide
          · rw [show (a : ℤ) + 1 = ((a + 1 : ℕ) : ℤ) by push_cast; ring,
                show (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) by omega,
                show (1 : ℤ) + 1 = 2 by rfl, show (1 : ℤ) - 1 = 0 by rfl,
                ih1 a, ih1 (a + 1), ih1 (a - 1), ih2 a, ih0 a]
            by_cases hint : a + 6 ≤ k
            · rw [f1_interior k a (by omega), f1_interior k (a + 1) (by omega),
                  f1_interior k (a - 1) (by omega), f2_interior k a (by omega),
                  f0_interior k a (by omega), f1_interior (k + 1) a (by omega)]
              set r := a % 4
              have hr : r < 4 := Nat.mod_lt a (by omega)
              have h1 : (a + 1) % 2 = (r + 1) % 2 := by omega
              have h2 : (a - 1) % 2 = (r + 1) % 2 := by omega
              have h3 : a % 2 = r % 2 := by omega
              rw [h1, h2, h3]
              interval_cases r <;> decide
            · by_cases hk5' : k = 5
              · subst hk5'
                have ha1 : 1 ≤ a := by omega
                have ha2 : a ≤ 5 := by omega
                interval_cases a <;> decide
              · have hk6 : 6 ≤ k := by omega
                set d := a + 6 - k
                have hd1 : 1 ≤ d := by omega
                have hd2 : d ≤ 6 := by omega
                have ha_eq : a = k + d - 6 := by omega
                rw [ha_eq,
                    show k + d - 6 + 1 = k + (d + 1) - 6 by omega,
                    show k + d - 6 - 1 = k + (d - 1) - 6 by omega]
                have hnext_eq : f1 (k + 1) (k + d - 6) =
                    f1 (8 + (k + 1) % 4) (8 + (k + 1) % 4 + (d - 1) - 6) := by
                  conv_lhs => rw [show k + d - 6 = (k + 1) + (d - 1) - 6 by omega]
                  exact f1_tail (k + 1) (d - 1) (by omega) (by omega)
                rw [hnext_eq, f1_tail k d hk6 (by omega), f1_tail k (d + 1) hk6 (by omega),
                    f1_tail k (d - 1) hk6 (by omega), f2_tail k d hk6 (by omega),
                    f0_tail k d hk6 (by omega)]
                set rk := k % 4
                have hrk : rk < 4 := Nat.mod_lt k (by omega)
                have hrk1 : (k + 1) % 4 = (rk + 1) % 4 := by omega
                rw [hrk1]
                interval_cases d <;> interval_cases rk <;> decide
      · intro a
        by_cases hgt : k ≤ a
        · rw [u_outside (k + 1) _ _ (by simp; omega)]; unfold f2; rw [if_pos (by omega)]
        · rw [u_succ]
          by_cases ha0 : a = 0
          · subst ha0
            simp only [Nat.cast_zero, zero_add, zero_sub]
            rw [u_neg_x k 1 2, show (2 : ℤ) + 1 = 3 by rfl, show (2 : ℤ) - 1 = 1 by rfl,
                show u k 0 2 = f2 k 0 from by simpa using ih2 0,
                show u k 1 2 = f2 k 1 from by simpa using ih2 1,
                show u k 0 1 = f1 k 0 from by simpa using ih1 0,
                f2_interior k 0 (by omega), f2_interior k 1 (by omega),
                f1_interior k 0 (by omega), f2_interior (k + 1) 0 (by omega)]
            cases u k 0 3 <;> decide
          · rw [show (a : ℤ) + 1 = ((a + 1 : ℕ) : ℤ) by push_cast; ring,
                show (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) by omega,
                show (2 : ℤ) + 1 = 3 by rfl, show (2 : ℤ) - 1 = 1 by rfl,
                ih2 a, ih2 (a + 1), ih2 (a - 1), ih1 a]
            by_cases hint : a + 5 ≤ k
            · rw [f2_interior k a (by omega), f2_interior k (a + 1) (by omega),
                  f2_interior k (a - 1) (by omega), f1_interior k a (by omega),
                  f2_interior (k + 1) a (by omega)]
              set r := a % 2
              have hr : r < 2 := Nat.mod_lt a (by omega)
              have h1 : (a + 1) % 2 = (r + 1) % 2 := by omega
              have h2 : (a - 1) % 2 = (r + 1) % 2 := by omega
              rw [h1, h2]
              interval_cases r <;> (cases u k (a : ℤ) 3 <;> decide)
            · by_cases hk5' : k = 5
              · subst hk5'
                have ha1 : 1 ≤ a := by omega
                have ha2 : a ≤ 4 := by omega
                have h3 : u 5 (a : ℤ) 3 = false := by
                  by_cases ha1' : a = 1
                  · subst ha1'
                    have := u_subfrontier 5 (by omega) 1 3 (by omega)
                    simpa using this
                  · by_cases ha2' : a = 2
                    · subst ha2'
                      have h := u_frontier 5 2 3 (by omega)
                      simp only [Nat.cast_ofNat] at h ⊢
                      rw [h]; decide
                    · exact u_outside 5 _ _ (by simp; omega)
                rw [h3]
                interval_cases a <;> decide
              · have hk6 : 6 ≤ k := by omega
                set d := a + 6 - k
                have hd1 : 2 ≤ d := by omega
                have hd2 : d ≤ 5 := by omega
                have ha_eq : a = k + d - 6 := by omega
                have h3 : u k (a : ℤ) 3 =
                    if d = 2 then decide ((k - 1) % 4 = 3)
                    else if d = 3 then decide (k % 4 = 3)
                    else false := by
                  by_cases hd2' : d = 2
                  · rw [if_pos hd2', show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl,
                        u_subfrontier k (by omega) a 3 (by omega), choose_three_mod2]
                    split_ifs with h <;> simp [h]
                  · rw [if_neg hd2']
                    by_cases hd3' : d = 3
                    · rw [if_pos hd3', show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl,
                          u_frontier k a 3 (by omega), choose_three_mod2]
                      split_ifs with h <;> simp [h]
                    · rw [if_neg hd3', u_outside k _ _ (by simp; omega)]
                rw [h3, ha_eq,
                    show k + d - 6 + 1 = k + (d + 1) - 6 by omega,
                    show k + d - 6 - 1 = k + (d - 1) - 6 by omega]
                have hnext_eq : f2 (k + 1) (k + d - 6) =
                    f2 (8 + (k + 1) % 4) (8 + (k + 1) % 4 + (d - 1) - 6) := by
                  conv_lhs => rw [show k + d - 6 = (k + 1) + (d - 1) - 6 by omega]
                  exact f2_tail (k + 1) (d - 1) (by omega) (by omega)
                rw [hnext_eq, f2_tail k d hk6 (by omega), f2_tail k (d + 1) hk6 (by omega),
                    f2_tail k (d - 1) hk6 (by omega), f1_tail k d hk6 (by omega)]
                set rk := k % 4
                have hrk : rk < 4 := Nat.mod_lt k (by omega)
                have hrk1 : (k + 1) % 4 = (rk + 1) % 4 := by omega
                have hrkm1 : (k - 1) % 4 = (rk + 3) % 4 := by omega
                rw [hrk1, hrkm1]
                interval_cases d <;> interval_cases rk <;> decide

-- ============================================================================
-- Section 3: Fast x-axis formula, shift identity, recurrence & G.f.
-- ============================================================================

private def uFast (k r : ℕ) : Bool :=
  match k with
  | 0 => decide (r = 0)
  | 1 => decide (r ≤ 1)
  | 2 => decide (r ≤ 2)
  | 3 => decide (r = 0 ∨ r = 2 ∨ r = 3)
  | 4 => decide (r = 0 ∨ r = 3 ∨ r = 4)
  | k => f0 k r

private lemma u_x_eq_uFast (k r : ℕ) : u k (r : ℤ) 0 = uFast k r := by
  match k with
  | 0 => simp [u, uFast]
  | 1 =>
    by_cases h : 1 < r
    · rw [u_outside 1 _ _ (by simp; omega)]; unfold uFast; simp [show ¬ r ≤ 1 by omega]
    · have hr : r ≤ 1 := by omega
      interval_cases r <;> decide
  | 2 =>
    by_cases h : 2 < r
    · rw [u_outside 2 _ _ (by simp; omega)]; unfold uFast; simp [show ¬ r ≤ 2 by omega]
    · have hr : r ≤ 2 := by omega
      interval_cases r <;> decide
  | 3 =>
    rw [u_3_eq]
    unfold g3 uFast; dsimp only
    rw [abs_of_nonneg (Int.natCast_nonneg r), abs_zero]
    apply decide_eq_decide.mpr; omega
  | 4 =>
    rw [u_4_eq]
    unfold g4 uFast; dsimp only
    rw [abs_of_nonneg (Int.natCast_nonneg r), abs_zero]
    apply decide_eq_decide.mpr; omega
  | k + 5 =>
    exact (u_strip (k + 5) (by omega)).1 r

private lemma a_eq_sum_uFast (n : ℕ) :
    a n = ∑ j ∈ Finset.range (n + 1), if uFast n j then (10 : ℤ) ^ j else 0 := by
  unfold a
  rw [← Finset.sum_range_reflect (fun k => if cell 526 n ((k : ℤ) - n) 0 then (10 : ℤ) ^ (n - k) else 0) (n + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjle : j ≤ n := by simp [Finset.mem_range] at hj; omega
  have h1 : n + 1 - 1 - j = n - j := by omega
  have h2 : n - (n - j) = j := by omega
  have h3 : (((n - j : ℕ) : ℤ) - (n : ℤ)) = -(j : ℤ) := by omega
  rw [h1, h2, h3, cell_526_eq_u, u_neg_x, u_x_eq_uFast]

private lemma uFast_shift4 (n j : ℕ) (hn : 1 ≤ n) :
    uFast (n + 4) (j + 4) = uFast n j := by
  match n with
  | 0 => omega
  | 1 =>
    by_cases hj : j ≤ 1
    · interval_cases j <;> decide
    · change f0 5 (j + 4) = decide (j ≤ 1)
      unfold f0; rw [if_pos (by omega)]; simp [show ¬ j ≤ 1 by omega]
  | 2 =>
    by_cases hj : j ≤ 2
    · interval_cases j <;> decide
    · change f0 6 (j + 4) = decide (j ≤ 2)
      unfold f0; rw [if_pos (by omega)]; simp [show ¬ j ≤ 2 by omega]
  | 3 =>
    by_cases hj : j ≤ 3
    · interval_cases j <;> decide
    · change f0 7 (j + 4) = decide (j = 0 ∨ j = 2 ∨ j = 3)
      unfold f0; rw [if_pos (by omega)]; symm; rw [decide_eq_false_iff_not]; omega
  | 4 =>
    by_cases hj : j ≤ 4
    · interval_cases j <;> decide
    · change f0 8 (j + 4) = decide (j = 0 ∨ j = 3 ∨ j = 4)
      unfold f0; rw [if_pos (by omega)]; symm; rw [decide_eq_false_iff_not]; omega
  | m + 5 =>
    change f0 (m + 5 + 4) (j + 4) = f0 (m + 5) j
    unfold f0
    by_cases h1 : m + 5 < j
    · rw [if_pos (by omega), if_pos h1]
    · rw [if_neg (by omega), if_neg h1]
      by_cases h2 : j = m + 5 ∨ j = m + 5 - 1
      · rw [if_pos (by omega), if_pos h2]
      · rw [if_neg (by omega), if_neg h2]
        by_cases h3 : j = m + 5 - 2
        · rw [if_pos (by omega), if_pos h3]; apply decide_eq_decide.mpr; omega
        · rw [if_neg (by omega), if_neg h3]
          by_cases h4 : j = m + 5 - 3
          · rw [if_pos (by omega), if_pos h4]; apply decide_eq_decide.mpr; omega
          · rw [if_neg (by omega), if_neg h4]; apply decide_eq_decide.mpr; omega

private lemma uFast_low (n : ℕ) (hn : 1 ≤ n) :
    uFast (n + 4) 0 = true ∧ uFast (n + 4) 1 = true ∧
    uFast (n + 4) 2 = false ∧ uFast (n + 4) 3 = true := by
  have hge5 : 5 ≤ n + 4 := by omega
  obtain ⟨m, hm⟩ : ∃ m, n + 4 = m + 5 := ⟨n - 1, by omega⟩
  rw [hm]
  change f0 (m + 5) 0 = true ∧ f0 (m + 5) 1 = true ∧ f0 (m + 5) 2 = false ∧ f0 (m + 5) 3 = true
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [f0_interior (m + 5) 0 (by omega)]; decide
  · rw [f0_interior (m + 5) 1 (by omega)]; decide
  · rcases m with _ | m'
    · decide
    · rw [f0_interior (m' + 1 + 5) 2 (by omega)]; decide
  · rcases m with _ | _ | m'
    · decide
    · decide
    · rw [f0_interior (m' + 2 + 5) 3 (by omega)]; decide

private lemma a_shift4 (n : ℕ) (hn : 1 ≤ n) :
    a (n + 4) = 10000 * a n + 1011 := by
  rw [a_eq_sum_uFast (n + 4), a_eq_sum_uFast n]
  rw [show n + 4 + 1 = 4 + (n + 1) by omega, Finset.sum_range_add]
  obtain ⟨h0, h1, h2, h3⟩ := uFast_low n hn
  have hhead : (∑ j ∈ Finset.range 4, if uFast (n + 4) j then (10 : ℤ) ^ j else 0) = 1011 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    rw [h0, h1, h2, h3]
    norm_num
  have htail : (∑ j ∈ Finset.range (n + 1), if uFast (n + 4) (4 + j) then (10 : ℤ) ^ (4 + j) else 0) =
      10000 * ∑ j ∈ Finset.range (n + 1), if uFast n j then (10 : ℤ) ^ j else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 4 + j = j + 4 by omega, uFast_shift4 n j hn]
    cases uFast n j
    · simp
    · simp only [ite_true, pow_add]; ring
  rw [hhead, htail]
  ring

private lemma a_rec_int (n : ℕ) (hn : 6 ≤ n) :
    a n = a (n - 1) + 10000 * a (n - 4) - 10000 * a (n - 5) := by
  have h1 := a_shift4 (n - 4) (by omega)
  have h2 := a_shift4 (n - 5) (by omega)
  rw [show n - 4 + 4 = n by omega] at h1
  rw [show n - 5 + 4 = n - 1 by omega] at h2
  omega

private lemma a_rec (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℚ) = a (n - 1) + 10000 * a (n - 4) - 10000 * a (n - 5) := by
  exact_mod_cast a_rec_int n hn

private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - X) * (1 - 10 * X) * (1 + 10 * X) * (1 + 100 * X ^ 2) : PowerSeries ℚ) =
      1 + 10 * X + 100 * X ^ 2 + 990 * X ^ 3 - 100 * X ^ 4 + 10 * X ^ 5 := by
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hlhs : A * ((1 - X) * (1 - 10 * X) * (1 + 10 * X) * (1 + 100 * X ^ 2) : PowerSeries ℚ) =
      A - A * X ^ 1 - PowerSeries.C (10000 : ℚ) * (A * X ^ 4) +
        PowerSeries.C (10000 : ℚ) * (A * X ^ 5) := by
    simp only [map_ofNat]
    ring
  have hrhs : (1 + 10 * X + 100 * X ^ 2 + 990 * X ^ 3 - 100 * X ^ 4 + 10 * X ^ 5 : PowerSeries ℚ) =
      PowerSeries.C (1 : ℚ) + PowerSeries.C (10 : ℚ) * X +
        PowerSeries.C (100 : ℚ) * X ^ 2 + PowerSeries.C (990 : ℚ) * X ^ 3 -
        PowerSeries.C (100 : ℚ) * X ^ 4 + PowerSeries.C (10 : ℚ) * X ^ 5 := by
    simp only [map_one, map_ofNat]
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_C, PowerSeries.coeff_X, PowerSeries.coeff_mk, A]
  by_cases hn : 6 ≤ n
  · have hrec := a_rec n hn
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n - 2 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega,
      ite_true, ite_false]
    linarith
  · have h0 : (a 0 : ℚ) = 1 := by exact_mod_cast (by rw [a_eq_sum_uFast]; decide : a 0 = 1)
    have h1 : (a 1 : ℚ) = 11 := by exact_mod_cast (by rw [a_eq_sum_uFast]; decide : a 1 = 11)
    have h2 : (a 2 : ℚ) = 111 := by exact_mod_cast (by rw [a_eq_sum_uFast]; decide : a 2 = 111)
    have h3 : (a 3 : ℚ) = 1101 := by exact_mod_cast (by rw [a_eq_sum_uFast]; decide : a 3 = 1101)
    have h4 : (a 4 : ℚ) = 11001 := by exact_mod_cast (by rw [a_eq_sum_uFast]; decide : a 4 = 11001)
    have h5 : (a 5 : ℚ) = 111011 := by exact_mod_cast (by rw [a_eq_sum_uFast]; decide : a 5 = 111011)
    have hs21 : (2 - 1 : ℕ) = 1 := rfl
    have hs31 : (3 - 1 : ℕ) = 2 := rfl
    have hs41 : (4 - 1 : ℕ) = 3 := rfl
    have hs51 : (5 - 1 : ℕ) = 4 := rfl
    interval_cases n <;>
      simp only [Nat.sub_self, hs21, hs31, hs41, hs51, h0, h1, h2, h3, h4, h5] <;>
      norm_num

end OMA.Proof_oeis_a282911

theorem OMA.solution : type_of% @OMA.S_oeis_a282911.main :=
  ⟨OMA.Proof_oeis_a282911.a_rec, OMA.Proof_oeis_a282911.gf_eq⟩

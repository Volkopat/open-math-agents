import OMAStatements.S_oeis_a269708

-- Problem: A269708: Number of active (ON, black) cells at stage 2^n-1 of the two-dimensional cellular automaton defined by Rule 14, based on the 5-celled von Neumann neighborhood.
-- Credit: @Qwer2077 (the owner of the agent is credited as the solver)

open OMA.S_oeis_a269708 PowerSeries

namespace OMA.Proof_oeis_a269708

private abbrev c (t : ℕ) (x y : ℤ) : Bool := cell 14 t x y

private def rule14 (cur : Bool) (s : ℕ) : Bool :=
  (14 : ℕ).testBit (cur.toNat + 2 * s)

private lemma cell_succ (t : ℕ) (x y : ℤ) :
    c (t + 1) x y =
      rule14 (c t x y)
        ((c t (x + 1) y).toNat + (c t (x - 1) y).toNat +
          (c t x (y + 1)).toNat + (c t x (y - 1)).toNat) :=
  rfl

private lemma rule14_ge2 (cur : Bool) (s : ℕ) (h1 : 2 ≤ s) (h2 : s ≤ 4) :
    rule14 cur s = false := by
  cases cur <;> interval_cases s <;> decide

private lemma rule14_false_even (k : ℕ) (hk : k ≤ 2) :
    rule14 false (2 * k) = false := by
  interval_cases k <;> decide

private lemma rule14_true_le1 (s : ℕ) (hs : s ≤ 1) :
    rule14 true s = true := by
  interval_cases s <;> decide

-- ============================================================================
-- Section 1: D4 symmetry, light cone, and zero diagonals
-- ============================================================================

private lemma cell_neg_x (t : ℕ) (x y : ℤ) : c t (-x) y = c t x y := by
  induction t generalizing x y with
  | zero => simp [c, cell]
  | succ t ih =>
    rw [cell_succ, cell_succ]
    have h1 : -x + 1 = -(x - 1) := by ring
    have h2 : -x - 1 = -(x + 1) := by ring
    rw [h1, h2, ih x y, ih (x - 1) y, ih (x + 1) y, ih x (y + 1), ih x (y - 1)]
    congr 1; omega

private lemma cell_neg_y (t : ℕ) (x y : ℤ) : c t x (-y) = c t x y := by
  induction t generalizing x y with
  | zero => simp [c, cell]
  | succ t ih =>
    rw [cell_succ, cell_succ]
    have h1 : -y + 1 = -(y - 1) := by ring
    have h2 : -y - 1 = -(y + 1) := by ring
    rw [h1, h2, ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y - 1), ih x (y + 1)]
    congr 1; omega

private lemma cell_swap (t : ℕ) (x y : ℤ) : c t y x = c t x y := by
  induction t generalizing x y with
  | zero =>
    simp only [c, cell]
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]
  | succ t ih =>
    rw [cell_succ, cell_succ]
    rw [ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y + 1), ih x (y - 1)]
    congr 1; omega

private lemma cell_abs (t : ℕ) (x y : ℤ) : c t |x| |y| = c t x y := by
  rcases le_or_gt 0 x with hx | hx <;> rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]
  · rw [abs_of_nonneg hx, abs_of_neg hy, cell_neg_y]
  · rw [abs_of_neg hx, abs_of_nonneg hy, cell_neg_x]
  · rw [abs_of_neg hx, abs_of_neg hy, cell_neg_x, cell_neg_y]

private lemma cell_outside (t : ℕ) (x y : ℤ) (h : (t : ℤ) < |x| + |y|) :
    c t x y = false := by
  induction t generalizing x y with
  | zero =>
    simp only [c, cell, decide_eq_false_iff_not]
    rintro ⟨rfl, rfl⟩
    simp at h
  | succ t ih =>
    rw [cell_succ]
    have hc : c t x y = false := ih x y (by omega)
    have h1 : c t (x + 1) y = false := ih (x + 1) y (by simp only [abs_eq_max_neg] at h ⊢; omega)
    have h2 : c t (x - 1) y = false := ih (x - 1) y (by simp only [abs_eq_max_neg] at h ⊢; omega)
    have h3 : c t x (y + 1) = false := ih x (y + 1) (by simp only [abs_eq_max_neg] at h ⊢; omega)
    have h4 : c t x (y - 1) = false := ih x (y - 1) (by simp only [abs_eq_max_neg] at h ⊢; omega)
    rw [hc, h1, h2, h3, h4]
    decide

private lemma cell_diag (t : ℕ) (x y : ℤ) (heq : |x| = |y|) (hne : x ≠ 0) :
    c t x y = false := by
  induction t generalizing x y with
  | zero =>
    simp only [c, cell, decide_eq_false_iff_not]
    rintro ⟨rfl, _⟩
    exact hne rfl
  | succ t ih =>
    rw [← cell_abs, heq]
    set u := |y|
    have hu : u ≠ 0 := by
      intro h0
      have : |x| = 0 := by rw [heq]; exact h0
      exact hne (abs_eq_zero.mp this)
    rw [cell_succ]
    have hc : c t u u = false := ih u u rfl hu
    have h1 : c t u (u + 1) = c t (u + 1) u := cell_swap t (u + 1) u
    have h2 : c t u (u - 1) = c t (u - 1) u := cell_swap t (u - 1) u
    rw [hc, h1, h2]
    set k := (c t (u + 1) u).toNat + (c t (u - 1) u).toNat
    have hk : k ≤ 2 := by
      have a1 := Bool.toNat_le (c t (u + 1) u)
      have a2 := Bool.toNat_le (c t (u - 1) u)
      omega
    have hsum : (c t (u + 1) u).toNat + (c t (u - 1) u).toNat +
        (c t (u + 1) u).toNat + (c t (u - 1) u).toNat = 2 * k := by omega
    rw [hsum]
    exact rule14_false_even k hk

-- ============================================================================
-- Section 2: Exact 2^k self-similarity decomposition
-- ============================================================================

private def stagePow2 (M : ℕ) (x y : ℤ) : Bool :=
  if |x| + |y| < (M : ℤ) then decide ((|x| + |y|) % 2 = 1)
  else decide ((|x| = (M : ℤ) ∧ y = 0) ∨ (x = 0 ∧ |y| = (M : ℤ)))

private lemma stagePow2_neg_x (M : ℕ) (x y : ℤ) :
    stagePow2 M (-x) y = stagePow2 M x y := by
  simp [stagePow2]

private lemma stagePow2_neg_y (M : ℕ) (x y : ℤ) :
    stagePow2 M x (-y) = stagePow2 M x y := by
  simp [stagePow2]

private lemma abs_add_abs_mod2 (a b : ℤ) : (|a| + |b|) % 2 = (a + b) % 2 := by
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb]
  · rw [abs_of_nonneg ha, abs_of_neg hb]; omega
  · rw [abs_of_neg ha, abs_of_nonneg hb]; omega
  · rw [abs_of_neg ha, abs_of_neg hb]; omega

private lemma stagePow2_swap (M : ℕ) (x y : ℤ) :
    stagePow2 M y x = stagePow2 M x y := by
  simp only [stagePow2, add_comm |y| |x|]
  split_ifs
  · rfl
  · apply decide_eq_decide.mpr; tauto

private def decomp (M r : ℕ) (x y : ℤ) : Bool :=
  if |x| + |y| < (M : ℤ) then decide ((|x| + |y|) % 2 = 1)
  else if |x| = |y| then false
  else if |y| < x then c r (x - (M : ℤ)) y
  else if |y| < -x then c r (x + (M : ℤ)) y
  else if |x| < y then c r x (y - (M : ℤ))
  else c r x (y + (M : ℤ))

private lemma decomp_neg_x (M r : ℕ) (x y : ℤ) :
    decomp M r (-x) y = decomp M r x y := by
  unfold decomp
  simp only [abs_neg, neg_neg]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  all_goals try rfl
  all_goals try (simp only [abs_eq_max_neg] at *; omega)
  · rw [show -x - (M : ℤ) = -(x + (M : ℤ)) by ring, cell_neg_x]
  · rw [show -x + (M : ℤ) = -(x - (M : ℤ)) by ring, cell_neg_x]
  · rw [cell_neg_x]
  · rw [cell_neg_x]

private lemma decomp_neg_y (M r : ℕ) (x y : ℤ) :
    decomp M r x (-y) = decomp M r x y := by
  unfold decomp
  simp only [abs_neg]
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  all_goals try rfl
  all_goals try (simp only [abs_eq_max_neg] at *; omega)
  · rw [cell_neg_y]
  · rw [cell_neg_y]
  · rw [show -y - (M : ℤ) = -(y + (M : ℤ)) by ring, cell_neg_y]
  · rw [show -y + (M : ℤ) = -(y - (M : ℤ)) by ring, cell_neg_y]

private lemma decomp_swap (M r : ℕ) (x y : ℤ) :
    decomp M r y x = decomp M r x y := by
  unfold decomp
  simp only [add_comm |y| |x|]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  all_goals try rfl
  all_goals try (simp only [abs_eq_max_neg] at *; omega)
  · rw [cell_swap]
  · rw [cell_swap]
  · rw [cell_swap]
  · rw [cell_swap]

private lemma decomp_zero (M : ℕ) (hM : 2 ≤ M) (x y : ℤ) :
    decomp M 0 x y = stagePow2 M x y := by
  unfold decomp stagePow2
  split_ifs with h1 h2 h3 h4 h5
  · rfl
  · symm
    simp only [decide_eq_false_iff_not, not_or]
    constructor <;> (rintro ⟨ha, hb⟩; simp only [abs_eq_max_neg] at *; omega)
  · simp only [c, cell]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨hx, hy⟩; left; exact ⟨by simp only [abs_eq_max_neg] at *; omega, hy⟩
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩) <;> (simp only [abs_eq_max_neg] at *; omega)
  · simp only [c, cell]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨hx, hy⟩; left; exact ⟨by simp only [abs_eq_max_neg] at *; omega, hy⟩
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩) <;> (simp only [abs_eq_max_neg] at *; omega)
  · simp only [c, cell]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨hx, hy⟩; right; exact ⟨hx, by simp only [abs_eq_max_neg] at *; omega⟩
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩) <;> (simp only [abs_eq_max_neg] at *; omega)
  · simp only [c, cell]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨hx, hy⟩; right; exact ⟨hx, by simp only [abs_eq_max_neg] at *; omega⟩
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩) <;> (simp only [abs_eq_max_neg] at *; omega)

private lemma decomp_east (M r : ℕ) (x y : ℤ) (hsum : (M : ℤ) ≤ |x| + |y|) (he : |y| < x) :
    decomp M r x y = c r (x - (M : ℤ)) y := by
  unfold decomp
  rw [if_neg (by omega)]
  have hne : |x| ≠ |y| := by simp only [abs_eq_max_neg] at *; omega
  rw [if_neg hne, if_pos he]

private lemma decomp_inner (M r : ℕ) (x y : ℤ) (hsum : |x| + |y| < (M : ℤ)) :
    decomp M r x y = decide ((|x| + |y|) % 2 = 1) := by
  unfold decomp
  rw [if_pos hsum]

private lemma decomp_diag_outer (M r : ℕ) (x y : ℤ) (hsum : (M : ℤ) ≤ |x| + |y|) (heq : |x| = |y|) :
    decomp M r x y = false := by
  unfold decomp
  rw [if_neg (by omega), if_pos heq]

private lemma decomp_step_octant (M r : ℕ) (hM2 : 2 ≤ M) (hMeven : M % 2 = 0)
    (hr : r < M)
    (h10 : ∀ r', 1 ≤ r' → r' ≤ M → c r' 1 0 = true)
    (hcur : ∀ x y : ℤ, c (M + r) x y = decomp M r x y)
    (x y : ℤ) (hy0 : 0 ≤ y) (hyx : y ≤ x) :
    c (M + (r + 1)) x y = decomp M (r + 1) x y := by
  have hx0 : 0 ≤ x := by omega
  have hax : |x| = x := abs_of_nonneg hx0
  have hay : |y| = y := abs_of_nonneg hy0
  by_cases h_in : x + y < (M : ℤ)
  · -- Case 1: Inner diamond |x| + |y| < M
    rw [decomp_inner M (r + 1) x y (by rw [hax, hay]; exact h_in)]
    rw [show M + (r + 1) = (M + r) + 1 by omega, cell_succ]
    rw [hcur x y, hcur (x + 1) y, hcur (x - 1) y, hcur x (y + 1), hcur x (y - 1)]
    by_cases hpar : (x + y) % 2 = 0
    · -- Subcase 1a: even sum => x + y <= M - 2, all 4 neighbors are inside and odd (true)
      have hle : x + y ≤ (M : ℤ) - 2 := by omega
      have h1 : decomp M r (x + 1) y = true := by
        rw [decomp_inner M r (x + 1) y (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
        simp only [decide_eq_true_eq]; omega
      have h2 : decomp M r (x - 1) y = true := by
        rw [decomp_inner M r (x - 1) y (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
        simp only [decide_eq_true_eq]; omega
      have h3 : decomp M r x (y + 1) = true := by
        rw [decomp_inner M r x (y + 1) (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
        simp only [decide_eq_true_eq]; omega
      have h4 : decomp M r x (y - 1) = true := by
        rw [decomp_inner M r x (y - 1) (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
        simp only [decide_eq_true_eq]; omega
      rw [h1, h2, h3, h4]
      have h0 : decide ((|x| + |y|) % 2 = 1) = false := by
        rw [hax, hay]; simp only [decide_eq_false_iff_not]; omega
      rw [h0]
      exact rule14_ge2 _ 4 (by omega) (by omega)
    · -- Subcase 1b/1c: odd sum => cur = true
      have hodd : (x + y) % 2 = 1 := by omega
      have hc : decomp M r x y = true := by
        rw [decomp_inner M r x y (by rw [hax, hay]; exact h_in), hax, hay]
        simp [hodd]
      have htarget : decide ((|x| + |y|) % 2 = 1) = true := by
        rw [hax, hay]; simp [hodd]
      rw [hc, htarget]
      by_cases hbd : x + y = (M : ℤ) - 1
      · -- Boundary x + y = M - 1
        by_cases hypos : 0 < y
        · -- y > 0: all 4 neighbors are false
          have hW : decomp M r (x - 1) y = false := by
            rw [decomp_inner M r (x - 1) y (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
            simp only [decide_eq_false_iff_not]; omega
          have hS : decomp M r x (y - 1) = false := by
            rw [decomp_inner M r x (y - 1) (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
            simp only [decide_eq_false_iff_not]; omega
          have hE : decomp M r (x + 1) y = false := by
            rw [decomp_east M r (x + 1) y (by simp only [abs_eq_max_neg]; omega)
              (by simp only [abs_eq_max_neg]; omega)]
            exact cell_diag r (x + 1 - M) y (by simp only [abs_eq_max_neg]; omega) (by omega)
          have hN : decomp M r x (y + 1) = false := by
            by_cases hxy1 : x = y + 1
            · exact decomp_diag_outer M r x (y + 1)
                (by simp only [abs_eq_max_neg]; omega) (by simp only [abs_eq_max_neg]; omega)
            · rw [decomp_east M r x (y + 1)
                (by simp only [abs_eq_max_neg]; omega) (by simp only [abs_eq_max_neg]; omega)]
              exact cell_diag r (x - M) (y + 1) (by simp only [abs_eq_max_neg]; omega) (by omega)
          rw [hE, hW, hN, hS]
          decide
        · -- y = 0, x = M - 1: W, N, S are false; E is anything => s <= 1 => true
          have hyz : y = 0 := by omega
          subst hyz
          have hxm : x = (M : ℤ) - 1 := by omega
          have hW : decomp M r (x - 1) 0 = false := by
            rw [decomp_inner M r (x - 1) 0 (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
            simp only [decide_eq_false_iff_not]; omega
          have hN : decomp M r x 1 = false := by
            by_cases hm2 : M = 2
            · exact decomp_diag_outer M r x 1
                (by simp only [abs_eq_max_neg]; omega) (by simp only [abs_eq_max_neg]; omega)
            · rw [decomp_east M r x 1
                (by simp only [abs_eq_max_neg]; omega) (by simp only [abs_eq_max_neg]; omega)]
              exact cell_diag r (x - M) 1 (by simp only [abs_eq_max_neg]; omega) (by omega)
          have hS : decomp M r x (-1) = false := by
            rw [decomp_neg_y]; exact hN
          simp only [zero_add, zero_sub]
          rw [hW, hN, hS]
          have hs : (decomp M r (x + 1) 0).toNat + (false).toNat + (false).toNat + (false).toNat ≤ 1 := by
            have := Bool.toNat_le (decomp M r (x + 1) 0)
            simp; omega
          exact rule14_true_le1 _ hs
      · -- Strictly inside: x + y <= M - 3, all 4 neighbors are inside and even (false)
        have h1 : decomp M r (x + 1) y = false := by
          rw [decomp_inner M r (x + 1) y (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
          simp only [decide_eq_false_iff_not]; omega
        have h2 : decomp M r (x - 1) y = false := by
          rw [decomp_inner M r (x - 1) y (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
          simp only [decide_eq_false_iff_not]; omega
        have h3 : decomp M r x (y + 1) = false := by
          rw [decomp_inner M r x (y + 1) (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
          simp only [decide_eq_false_iff_not]; omega
        have h4 : decomp M r x (y - 1) = false := by
          rw [decomp_inner M r x (y - 1) (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
          simp only [decide_eq_false_iff_not]; omega
        rw [h1, h2, h3, h4]
        decide
  · -- Outer region: x + y >= M
    by_cases hdiag : x = y
    · -- Case 2: Diagonal x = y, x + y >= M => x != 0 => both false
      rw [decomp_diag_outer M (r + 1) x y (by rw [hax, hay]; omega) (by rw [hax, hay]; exact hdiag)]
      exact cell_diag (M + (r + 1)) x y (by rw [hax, hay]; exact hdiag) (by omega)
    · -- East sector: y < x and x + y >= M
      rw [decomp_east M (r + 1) x y (by rw [hax, hay]; omega) (by rw [hay]; omega)]
      by_cases hbd : x + y = (M : ℤ)
      · by_cases hypos : 0 < y
        · -- Case 3: x + y = M, 0 < y < x => target is on diagonal (false), W & S are true => s >= 2 => false
          rw [cell_diag (r + 1) (x - M) y (by simp only [abs_eq_max_neg]; omega) (by omega)]
          rw [show M + (r + 1) = (M + r) + 1 by omega, cell_succ]
          rw [hcur (x - 1) y, hcur x (y - 1)]
          have hW : decomp M r (x - 1) y = true := by
            rw [decomp_inner M r (x - 1) y (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
            simp only [decide_eq_true_eq]; omega
          have hS : decomp M r x (y - 1) = true := by
            rw [decomp_inner M r x (y - 1) (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
            simp only [decide_eq_true_eq]; omega
          rw [hW, hS]
          have h1 : 2 ≤ (c (M + r) (x + 1) y).toNat + (true).toNat +
              (c (M + r) x (y + 1)).toNat + (true).toNat := by simp; omega
          have h2 : (c (M + r) (x + 1) y).toNat + (true).toNat +
              (c (M + r) x (y + 1)).toNat + (true).toNat ≤ 4 := by
            have a1 := Bool.toNat_le (c (M + r) (x + 1) y)
            have a2 := Bool.toNat_le (c (M + r) x (y + 1))
            simp; omega
          exact rule14_ge2 _ _ h1 h2
        · -- Case 4: Tip (M, 0)
          have hyz : y = 0 := by omega
          subst hyz
          have hxm : x = (M : ℤ) := by omega
          subst hxm
          rw [show (M : ℤ) - (M : ℤ) = 0 by ring]
          rw [show M + (r + 1) = (M + r) + 1 by omega, cell_succ]
          simp only [zero_add, zero_sub]
          rw [hcur M 0, hcur (M + 1) 0, hcur (M - 1) 0, hcur M 1, hcur M (-1)]
          have hC : decomp M r M 0 = c r 0 0 := by
            rw [decomp_east M r M 0 (by simp only [abs_eq_max_neg]; omega)
              (by simp only [abs_eq_max_neg]; omega), sub_self]
          have hE : decomp M r (M + 1) 0 = c r 1 0 := by
            rw [decomp_east M r (M + 1) 0 (by simp only [abs_eq_max_neg]; omega)
              (by simp only [abs_eq_max_neg]; omega)]
            congr 1; ring
          have hN : decomp M r M 1 = c r 0 1 := by
            rw [decomp_east M r M 1 (by simp only [abs_eq_max_neg]; omega)
              (by simp only [abs_eq_max_neg]; omega), sub_self]
          have hS : decomp M r M (-1) = c r 0 (-1) := by
            rw [decomp_east M r M (-1) (by simp only [abs_eq_max_neg]; omega)
              (by simp only [abs_eq_max_neg]; omega), sub_self]
          have hW : decomp M r (M - 1) 0 = true := by
            rw [decomp_inner M r (M - 1) 0 (by simp only [abs_eq_max_neg]; omega), abs_add_abs_mod2]
            simp only [decide_eq_true_eq]; omega
          rw [hC, hE, hN, hS, hW]
          cases r with
          | zero => decide
          | succ r' =>
            conv_rhs => rw [cell_succ]
            simp only [zero_add, zero_sub]
            have hw' : c (r' + 1) (-1) 0 = true := by
              rw [show (-1 : ℤ) = -(1 : ℤ) by ring, cell_neg_x]
              exact h10 (r' + 1) (by omega) (by omega)
            rw [hw']
      · -- Case 5: Strictly outside inner diamond, x + y > M and 0 <= y < x
        rw [show M + (r + 1) = (M + r) + 1 by omega, cell_succ, cell_succ]
        rw [hcur x y, hcur (x + 1) y, hcur (x - 1) y, hcur x (y + 1), hcur x (y - 1)]
        have match_pt : ∀ a b : ℤ, (M : ℤ) ≤ |a| + |b| → |b| ≤ a →
            decomp M r a b = c r (a - M) b := by
          intro a b hs hba
          by_cases hlt : |b| < a
          · exact decomp_east M r a b hs hlt
          · have heq : |a| = |b| := by simp only [abs_eq_max_neg] at *; omega
            rw [decomp_diag_outer M r a b hs heq]
            symm
            by_cases h2 : |a| + |b| = (M : ℤ)
            · exact cell_diag r (a - M) b (by simp only [abs_eq_max_neg] at *; omega)
                (by simp only [abs_eq_max_neg] at *; omega)
            · exact cell_outside r (a - M) b (by simp only [abs_eq_max_neg] at *; omega)
        have hC := match_pt x y (by simp only [abs_eq_max_neg]; omega) (by simp only [abs_eq_max_neg]; omega)
        have hE := match_pt (x + 1) y (by simp only [abs_eq_max_neg]; omega) (by simp only [abs_eq_max_neg]; omega)
        have hW := match_pt (x - 1) y (by simp only [abs_eq_max_neg]; omega) (by simp only [abs_eq_max_neg]; omega)
        have hN := match_pt x (y + 1) (by simp only [abs_eq_max_neg]; omega) (by simp only [abs_eq_max_neg]; omega)
        have hS := match_pt x (y - 1) (by simp only [abs_eq_max_neg]; omega) (by simp only [abs_eq_max_neg]; omega)
        rw [hC, hE, hW, hN, hS]
        have he1 : x + 1 - (M : ℤ) = (x - (M : ℤ)) + 1 := by ring
        have hw1 : x - 1 - (M : ℤ) = (x - (M : ℤ)) - 1 := by ring
        rw [he1, hw1]

private lemma decomp_step (M r : ℕ) (hM2 : 2 ≤ M) (hMeven : M % 2 = 0)
    (hr : r < M)
    (h10 : ∀ r', 1 ≤ r' → r' ≤ M → c r' 1 0 = true)
    (hcur : ∀ x y : ℤ, c (M + r) x y = decomp M r x y) :
    ∀ x y : ℤ, c (M + (r + 1)) x y = decomp M (r + 1) x y := by
  intro x y
  have hs : ∀ u v : ℤ, 0 ≤ u → 0 ≤ v → c (M + (r + 1)) u v = decomp M (r + 1) u v := by
    intro u v hu hv
    rcases le_or_gt v u with hvu | huv
    · exact decomp_step_octant M r hM2 hMeven hr h10 hcur u v hv hvu
    · rw [← cell_swap, ← decomp_swap]
      exact decomp_step_octant M r hM2 hMeven hr h10 hcur v u hu (by omega)
  rw [← cell_abs]
  have hd : decomp M (r + 1) |x| |y| = decomp M (r + 1) x y := by
    rcases le_or_gt 0 x with hx | hx <;> rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hx, abs_of_nonneg hy]
    · rw [abs_of_nonneg hx, abs_of_neg hy, decomp_neg_y]
    · rw [abs_of_neg hx, abs_of_nonneg hy, decomp_neg_x]
    · rw [abs_of_neg hx, abs_of_neg hy, decomp_neg_x, decomp_neg_y]
  rw [← hd]
  exact hs |x| |y| (abs_nonneg x) (abs_nonneg y)

private lemma cell_base_2 (x y : ℤ) : c 2 x y = stagePow2 2 x y := by
  have hs : ∀ u v : ℤ, 0 ≤ u → 0 ≤ v → c 2 u v = stagePow2 2 u v := by
    intro u v hu hv
    by_cases h : 2 < u + v
    · rw [cell_outside 2 u v (by rw [abs_of_nonneg hu, abs_of_nonneg hv]; exact h)]
      unfold stagePow2
      rw [abs_of_nonneg hu, abs_of_nonneg hv, if_neg (by omega)]
      symm
      simp only [decide_eq_false_iff_not, not_or]
      constructor <;> (rintro ⟨h1, h2⟩; omega)
    · have hu2 : u ≤ 2 := by omega
      have hv2 : v ≤ 2 := by omega
      interval_cases u <;> interval_cases v <;> decide
  rw [← cell_abs]
  have hd : stagePow2 2 |x| |y| = stagePow2 2 x y := by
    rcases le_or_gt 0 x with hx | hx <;> rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hx, abs_of_nonneg hy]
    · rw [abs_of_nonneg hx, abs_of_neg hy, stagePow2_neg_y]
    · rw [abs_of_neg hx, abs_of_nonneg hy, stagePow2_neg_x]
    · rw [abs_of_neg hx, abs_of_neg hy, stagePow2_neg_x, stagePow2_neg_y]
  rw [← hd]
  exact hs |x| |y| (abs_nonneg x) (abs_nonneg y)

private lemma stagePow2_double (M : ℕ) (hM2 : 2 ≤ M) (hMeven : M % 2 = 0)
    (hM : ∀ x y : ℤ, c M x y = stagePow2 M x y) :
    ∀ x y : ℤ, decomp M M x y = stagePow2 (2 * M) x y := by
  intro x y
  have hs : ∀ u v : ℤ, 0 ≤ v → v ≤ u → decomp M M u v = stagePow2 (2 * M) u v := by
    intro u v hv hvu
    have hu : 0 ≤ u := by omega
    by_cases hin : u + v < (M : ℤ)
    · rw [decomp_inner M M u v (by rw [abs_of_nonneg hu, abs_of_nonneg hv]; exact hin)]
      unfold stagePow2
      rw [abs_of_nonneg hu, abs_of_nonneg hv, if_pos (by omega)]
    · by_cases heq : u = v
      · rw [decomp_diag_outer M M u v (by rw [abs_of_nonneg hu, abs_of_nonneg hv]; omega)
          (by rw [abs_of_nonneg hu, abs_of_nonneg hv]; exact heq)]
        unfold stagePow2
        rw [abs_of_nonneg hu, abs_of_nonneg hv]
        split_ifs
        · symm; simp only [decide_eq_false_iff_not]; omega
        · symm; simp only [decide_eq_false_iff_not, not_or]
          constructor <;> (rintro ⟨h1, h2⟩; omega)
      · rw [decomp_east M M u v (by rw [abs_of_nonneg hu, abs_of_nonneg hv]; omega)
          (by rw [abs_of_nonneg hv]; omega), hM]
        unfold stagePow2
        rw [abs_of_nonneg hu, abs_of_nonneg hv]
        by_cases hge : (M : ℤ) ≤ u
        · rw [abs_of_nonneg (by omega : 0 ≤ u - (M : ℤ))]
          split_ifs with h1 h2 h3
          · apply decide_eq_decide.mpr; omega
          · omega
          · omega
          · apply decide_eq_decide.mpr
            constructor
            · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
              · left; exact ⟨by omega, hb⟩
              · omega
            · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
              · left; exact ⟨by omega, hb⟩
              · omega
        · rw [abs_of_neg (by omega : u - (M : ℤ) < 0)]
          rw [if_pos (by omega), if_pos (by omega)]
          apply decide_eq_decide.mpr; omega
  have hsym : ∀ u v : ℤ, 0 ≤ u → 0 ≤ v → decomp M M u v = stagePow2 (2 * M) u v := by
    intro u v hu hv
    rcases le_or_gt v u with hvu | huv
    · exact hs u v hv hvu
    · rw [← decomp_swap, ← stagePow2_swap]
      exact hs v u hu (by omega)
  have hd1 : decomp M M |x| |y| = decomp M M x y := by
    rcases le_or_gt 0 x with hx | hx <;> rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hx, abs_of_nonneg hy]
    · rw [abs_of_nonneg hx, abs_of_neg hy, decomp_neg_y]
    · rw [abs_of_neg hx, abs_of_nonneg hy, decomp_neg_x]
    · rw [abs_of_neg hx, abs_of_neg hy, decomp_neg_x, decomp_neg_y]
  have hd2 : stagePow2 (2 * M) |x| |y| = stagePow2 (2 * M) x y := by
    rcases le_or_gt 0 x with hx | hx <;> rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hx, abs_of_nonneg hy]
    · rw [abs_of_nonneg hx, abs_of_neg hy, stagePow2_neg_y]
    · rw [abs_of_neg hx, abs_of_nonneg hy, stagePow2_neg_x]
    · rw [abs_of_neg hx, abs_of_neg hy, stagePow2_neg_x, stagePow2_neg_y]
  rw [← hd1, ← hd2]
  exact hsym |x| |y| (abs_nonneg x) (abs_nonneg y)

private lemma pow2_invariant (k : ℕ) (hk : 1 ≤ k) :
    (∀ x y : ℤ, c (2 ^ k) x y = stagePow2 (2 ^ k) x y) ∧
    (∀ r : ℕ, 1 ≤ r → r ≤ 2 ^ k → c r 1 0 = true) ∧
    (∀ r : ℕ, r ≤ 2 ^ k → ∀ x y : ℤ, c (2 ^ k + r) x y = decomp (2 ^ k) r x y) := by
  have hmain : ∀ k : ℕ, 1 ≤ k →
      (∀ x y : ℤ, c (2 ^ k) x y = stagePow2 (2 ^ k) x y) ∧
      (∀ r : ℕ, 1 ≤ r → r ≤ 2 ^ k → c r 1 0 = true) := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases hk0 : k = 0
      · subst hk0
        refine ⟨cell_base_2, ?_⟩
        intro r hr1 hr2
        have : r ≤ 2 := by simpa using hr2
        interval_cases r <;> decide
      · obtain ⟨hM, h10⟩ := ih (by omega)
        set M := 2 ^ k
        have hM2 : 2 ≤ M := by
          have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
          simpa using this
        have hMeven : M % 2 = 0 := by
          have hpow : M = 2 * 2 ^ (k - 1) := by
            show 2 ^ k = 2 * 2 ^ (k - 1)
            conv_lhs => rw [show k = (k - 1) + 1 by omega]
            rw [pow_succ']
          omega
        have hdecomp : ∀ r : ℕ, r ≤ M → ∀ x y : ℤ, c (M + r) x y = decomp M r x y := by
          intro r
          induction r with
          | zero =>
            intro _ x y
            rw [Nat.add_zero, hM x y, decomp_zero M hM2 x y]
          | succ r ihr =>
            intro hr x y
            exact decomp_step M r hM2 hMeven (by omega) h10 (ihr (by omega)) x y
        have h2M : 2 ^ (k + 1) = 2 * M := by rw [pow_succ']
        have hMadd : M + M = 2 * M := by omega
        refine ⟨?_, ?_⟩
        · intro x y
          rw [h2M, ← hMadd, hdecomp M le_rfl x y, stagePow2_double M hM2 hMeven hM x y, hMadd]
        · intro r hr1 hr2
          rw [h2M] at hr2
          by_cases hle : r ≤ M
          · exact h10 r hr1 hle
          · have hrm : r = M + (r - M) := by omega
            rw [hrm, hdecomp (r - M) (by omega) 1 0]
            rw [decomp_inner M (r - M) 1 0 (by simp; omega)]
            decide
  obtain ⟨hM, h10⟩ := hmain k hk
  set M := 2 ^ k
  have hM2 : 2 ≤ M := by
    have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    simpa using this
  have hMeven : M % 2 = 0 := by
    have hpow : M = 2 * 2 ^ (k - 1) := by
      show 2 ^ k = 2 * 2 ^ (k - 1)
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [pow_succ']
    omega
  refine ⟨hM, h10, ?_⟩
  intro r
  induction r with
  | zero =>
    intro _ x y
    rw [Nat.add_zero, hM x y, decomp_zero M hM2 x y]
  | succ r ihr =>
    intro hr x y
    exact decomp_step M r hM2 hMeven (by omega) h10 (ihr (by omega)) x y

private lemma cell_origin_false (n : ℕ) (hn : 2 ≤ n) : c (2 ^ n - 1) 0 0 = false := by
  have hk : 1 ≤ n - 1 := by omega
  have hinv := (pow2_invariant (n - 1) hk).2.2
  have hpow : 2 ^ n - 1 = 2 ^ (n - 1) + (2 ^ (n - 1) - 1) := by
    have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by omega)
    have h2 : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ']; omega
    omega
  rw [hpow, hinv (2 ^ (n - 1) - 1) (by omega) 0 0]
  rw [decomp_inner _ _ 0 0 (by simp)]
  decide

-- ============================================================================
-- Section 3: Exact counting of ON cells at stage 2^n - 1
-- ============================================================================

private noncomputable def box (t : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(t : ℤ)) (t : ℤ) ×ˢ Finset.Icc (-(t : ℤ)) (t : ℤ)

private lemma onCount_eq_box (t : ℕ) :
    onCount 14 t = ∑ p ∈ box t, if c t p.1 p.2 then 1 else 0 := by
  rw [onCount, box, Finset.sum_product]
  refine Finset.sum_bij (fun i _ => (i : ℤ) - (t : ℤ)) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Icc]; omega
  · intro i1 _ i2 _ h; omega
  · intro x hx
    rw [Finset.mem_Icc] at hx
    refine ⟨(x + (t : ℤ)).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · have : ((x + (t : ℤ)).toNat : ℤ) = x + (t : ℤ) := Int.toNat_of_nonneg (by omega)
      omega
  · intro i _
    refine Finset.sum_bij (fun j _ => (j : ℤ) - (t : ℤ)) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_range] at hj
      rw [Finset.mem_Icc]; omega
    · intro j1 _ j2 _ h; omega
    · intro y hy
      rw [Finset.mem_Icc] at hy
      refine ⟨(y + (t : ℤ)).toNat, ?_, ?_⟩
      · rw [Finset.mem_range]; omega
      · have : ((y + (t : ℤ)).toNat : ℤ) = y + (t : ℤ) := Int.toNat_of_nonneg (by omega)
        omega
    · intro j _; rfl

private noncomputable def eastCount (t : ℕ) : ℕ :=
  ∑ p ∈ box t, if |p.2| < p.1 ∧ c t p.1 p.2 then 1 else 0

private lemma box_mem_iff (t : ℕ) (p : ℤ × ℤ) :
    p ∈ box t ↔ -(t : ℤ) ≤ p.1 ∧ p.1 ≤ (t : ℤ) ∧ -(t : ℤ) ≤ p.2 ∧ p.2 ≤ (t : ℤ) := by
  simp [box, Finset.mem_product, Finset.mem_Icc, and_assoc]

private lemma onCount_eq_four_eastCount (t : ℕ) (h0 : c t 0 0 = false) :
    onCount 14 t = 4 * eastCount t := by
  rw [onCount_eq_box]
  have hsplit : (∑ p ∈ box t, if c t p.1 p.2 then 1 else 0) =
      (∑ p ∈ box t, if |p.2| < p.1 ∧ c t p.1 p.2 then 1 else 0) +
      (∑ p ∈ box t, if |p.2| < -p.1 ∧ c t p.1 p.2 then 1 else 0) +
      (∑ p ∈ box t, if |p.1| < p.2 ∧ c t p.1 p.2 then 1 else 0) +
      (∑ p ∈ box t, if |p.1| < -p.2 ∧ c t p.1 p.2 then 1 else 0) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hc : c t p.1 p.2 = true
    · have hne : |p.1| ≠ |p.2| := by
        intro heq
        by_cases hx0 : p.1 = 0
        · have hy0 : p.2 = 0 := by
            have : |p.2| = 0 := by rw [← heq, hx0, abs_zero]
            exact abs_eq_zero.mp this
          rw [hx0, hy0, h0] at hc; cases hc
        · rw [cell_diag t p.1 p.2 heq hx0] at hc; cases hc
      have h1 : |p.2| < p.1 ∨ |p.2| < -p.1 ∨ |p.1| < p.2 ∨ |p.1| < -p.2 := by
        simp only [abs_eq_max_neg] at hne ⊢; omega
      rcases h1 with h | h | h | h
      · have a2 : ¬ |p.2| < -p.1 := by simp only [abs_eq_max_neg] at h ⊢; omega
        have a3 : ¬ |p.1| < p.2 := by simp only [abs_eq_max_neg] at h ⊢; omega
        have a4 : ¬ |p.1| < -p.2 := by simp only [abs_eq_max_neg] at h ⊢; omega
        simp [hc, h, a2, a3, a4]
      · have a1 : ¬ |p.2| < p.1 := by simp only [abs_eq_max_neg] at h ⊢; omega
        have a3 : ¬ |p.1| < p.2 := by simp only [abs_eq_max_neg] at h ⊢; omega
        have a4 : ¬ |p.1| < -p.2 := by simp only [abs_eq_max_neg] at h ⊢; omega
        simp [hc, a1, h, a3, a4]
      · have a1 : ¬ |p.2| < p.1 := by simp only [abs_eq_max_neg] at h ⊢; omega
        have a2 : ¬ |p.2| < -p.1 := by simp only [abs_eq_max_neg] at h ⊢; omega
        have a4 : ¬ |p.1| < -p.2 := by simp only [abs_eq_max_neg] at h ⊢; omega
        simp [hc, a1, a2, h, a4]
      · have a1 : ¬ |p.2| < p.1 := by simp only [abs_eq_max_neg] at h ⊢; omega
        have a2 : ¬ |p.2| < -p.1 := by simp only [abs_eq_max_neg] at h ⊢; omega
        have a3 : ¬ |p.1| < p.2 := by simp only [abs_eq_max_neg] at h ⊢; omega
        simp [hc, a1, a2, a3, h]
    · simp [hc]
  have hW : (∑ p ∈ box t, if |p.2| < -p.1 ∧ c t p.1 p.2 then 1 else 0) = eastCount t := by
    refine Finset.sum_bij (fun p _ => (-p.1, p.2)) ?_ ?_ ?_ ?_
    · intro p hp; rw [box_mem_iff] at hp ⊢; omega
    · intro p1 _ p2 _ h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact Prod.ext (by omega) h2
    · intro q hq; refine ⟨(-q.1, q.2), ?_, ?_⟩
      · rw [box_mem_iff] at hq ⊢; omega
      · exact Prod.ext (by ring) rfl
    · intro p _; simp [cell_neg_x]
  have hN : (∑ p ∈ box t, if |p.1| < p.2 ∧ c t p.1 p.2 then 1 else 0) = eastCount t := by
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp; rw [box_mem_iff] at hp ⊢; omega
    · intro p1 _ p2 _ h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact Prod.ext h2 h1
    · intro q hq; refine ⟨(q.2, q.1), ?_, ?_⟩
      · rw [box_mem_iff] at hq ⊢; omega
      · exact Prod.ext rfl rfl
    · intro p _; simp [cell_swap]
  have hS : (∑ p ∈ box t, if |p.1| < -p.2 ∧ c t p.1 p.2 then 1 else 0) = eastCount t := by
    refine Finset.sum_bij (fun p _ => (-p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp; rw [box_mem_iff] at hp ⊢; omega
    · intro p1 _ p2 _ h
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact Prod.ext h2 (by omega)
    · intro q hq; refine ⟨(q.2, -q.1), ?_, ?_⟩
      · rw [box_mem_iff] at hq ⊢; omega
      · exact Prod.ext (by ring) rfl
    · intro p _; simp [cell_neg_y, cell_swap]
  rw [hsplit, hW, hN, hS]
  unfold eastCount
  omega

private lemma inner_east_count (m : ℕ) (B : ℕ) (hB : 2 * m ≤ B) :
    (∑ p ∈ box B, if |p.2| < p.1 ∧ p.1 + |p.2| < (2 * m : ℤ) ∧ (p.1 + |p.2|) % 2 = 1 then 1 else 0) =
      m * m := by
  induction m with
  | zero =>
    apply Finset.sum_eq_zero
    intro p _
    split_ifs with h
    · simp only [abs_eq_max_neg] at h; omega
    · rfl
  | succ m ih =>
    have hsplit : (∑ p ∈ box B,
          if |p.2| < p.1 ∧ p.1 + |p.2| < (2 * (m + 1 : ℕ) : ℤ) ∧ (p.1 + |p.2|) % 2 = 1 then 1 else 0) =
        (∑ p ∈ box B,
          if |p.2| < p.1 ∧ p.1 + |p.2| < (2 * m : ℤ) ∧ (p.1 + |p.2|) % 2 = 1 then 1 else 0) +
        (∑ p ∈ box B,
          if |p.2| < p.1 ∧ p.1 + |p.2| = (2 * m + 1 : ℤ) then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> omega
    rw [hsplit, ih (by omega)]
    have hshell : (∑ p ∈ box B, if |p.2| < p.1 ∧ p.1 + |p.2| = (2 * m + 1 : ℤ) then 1 else 0) =
        2 * m + 1 := by
      rw [← Finset.sum_filter]
      have hcard : (∑ _ ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), (1 : ℕ)) = 2 * m + 1 := by
        simp [Int.card_Icc]; omega
      rw [← hcard]
      refine Finset.sum_bij (fun p _ => p.2) ?_ ?_ ?_ ?_
      · intro p hp
        rw [Finset.mem_filter] at hp
        rw [Finset.mem_Icc]
        simp only [abs_eq_max_neg] at hp; omega
      · intro p1 hp1 p2 hp2 h
        rw [Finset.mem_filter] at hp1 hp2
        apply Prod.ext
        · have : p1.1 + |p1.2| = p2.1 + |p2.2| := by omega
          rw [h] at this; omega
        · exact h
      · intro y hy
        rw [Finset.mem_Icc] at hy
        refine ⟨((2 * m + 1 : ℤ) - |y|, y), ?_, rfl⟩
        rw [Finset.mem_filter, box_mem_iff]
        simp only [abs_eq_max_neg] at hy ⊢; omega
      · intro _ _; rfl
    rw [hshell]
    ring

private lemma eastCount_rec (n : ℕ) (hn : 3 ≤ n) :
    eastCount (2 ^ n - 1) = 3 * eastCount (2 ^ (n - 1) - 1) + (2 ^ (n - 2)) * (2 ^ (n - 2)) := by
  set k := n - 1
  set M := 2 ^ k
  have hk : 2 ≤ k := by omega
  have hM4 : 4 ≤ M := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    simpa using this
  have hM2m : M = 2 * 2 ^ (n - 2) := by
    have hkeq : k = (n - 2) + 1 := by omega
    show 2 ^ k = 2 * 2 ^ (n - 2)
    rw [hkeq, pow_succ']
  have h2M : 2 ^ n - 1 = 2 * M - 1 := by
    have : 2 ^ n = 2 * M := by rw [show n = k + 1 by omega, pow_succ']
    omega
  have hdec : ∀ x y : ℤ, c (2 * M - 1) x y = decomp M (M - 1) x y := by
    have hinv := (pow2_invariant k (by omega)).2.2 (M - 1) (by omega)
    intro x y
    rw [show 2 * M - 1 = M + (M - 1) by omega]
    exact hinv x y
  rw [h2M]
  change (∑ p ∈ box (2 * M - 1), if |p.2| < p.1 ∧ c (2 * M - 1) p.1 p.2 then 1 else 0) =
      3 * eastCount (M - 1) + 2 ^ (n - 2) * 2 ^ (n - 2)
  have hsplit : (∑ p ∈ box (2 * M - 1), if |p.2| < p.1 ∧ c (2 * M - 1) p.1 p.2 then 1 else 0) =
      (∑ p ∈ box (2 * M - 1),
        if |p.2| < p.1 ∧ p.1 + |p.2| < (M : ℤ) ∧ c (2 * M - 1) p.1 p.2 then 1 else 0) +
      (∑ p ∈ box (2 * M - 1),
        if |p.2| < p.1 ∧ (M : ℤ) ≤ p.1 + |p.2| ∧ c (2 * M - 1) p.1 p.2 then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : p.1 + |p.2| < (M : ℤ)
    · have hnot : ¬ (M : ℤ) ≤ p.1 + |p.2| := by omega
      simp [h, hnot]
    · have hge : (M : ℤ) ≤ p.1 + |p.2| := by omega
      simp [h, hge]
  rw [hsplit]
  have hInner : (∑ p ∈ box (2 * M - 1),
        if |p.2| < p.1 ∧ p.1 + |p.2| < (M : ℤ) ∧ c (2 * M - 1) p.1 p.2 then 1 else 0) =
      2 ^ (n - 2) * 2 ^ (n - 2) := by
    have hcongr : (∑ p ∈ box (2 * M - 1),
          if |p.2| < p.1 ∧ p.1 + |p.2| < (M : ℤ) ∧ c (2 * M - 1) p.1 p.2 then 1 else 0) =
        ∑ p ∈ box (2 * M - 1),
          if |p.2| < p.1 ∧ p.1 + |p.2| < (2 * 2 ^ (n - 2) : ℤ) ∧ (p.1 + |p.2|) % 2 = 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      have hMeq : (M : ℤ) = (2 * 2 ^ (n - 2) : ℤ) := by exact_mod_cast hM2m
      by_cases h1 : |p.2| < p.1
      · have hp1 : 0 ≤ p.1 := by simp only [abs_eq_max_neg] at h1; omega
        by_cases h2 : p.1 + |p.2| < (M : ℤ)
        · have hc : c (2 * M - 1) p.1 p.2 = decide ((p.1 + |p.2|) % 2 = 1) := by
            rw [hdec, decomp_inner M (M - 1) p.1 p.2 (by rw [abs_of_nonneg hp1]; exact h2), abs_of_nonneg hp1]
          rw [hc, ← hMeq]
          simp [h1, h2]
        · rw [← hMeq]; simp [h1, h2]
      · simp [h1]
    rw [hcongr]
    exact inner_east_count (2 ^ (n - 2)) (2 * M - 1) (by omega)
  have hOuter : (∑ p ∈ box (2 * M - 1),
        if |p.2| < p.1 ∧ (M : ℤ) ≤ p.1 + |p.2| ∧ c (2 * M - 1) p.1 p.2 then 1 else 0) =
      3 * eastCount (M - 1) := by
    have hbij : (∑ p ∈ box (2 * M - 1),
          if |p.2| < p.1 ∧ (M : ℤ) ≤ p.1 + |p.2| ∧ c (2 * M - 1) p.1 p.2 then 1 else 0) =
        ∑ q ∈ box (M - 1), if ¬ (|q.2| < -q.1) ∧ c (M - 1) q.1 q.2 then 1 else 0 := by
      rw [← Finset.sum_filter, ← Finset.sum_filter]
      refine Finset.sum_bij (fun p _ => (p.1 - (M : ℤ), p.2)) ?_ ?_ ?_ ?_
      · intro p hp
        rw [Finset.mem_filter] at hp ⊢
        obtain ⟨_, h1, h2, h3⟩ := hp
        have hp1 : 0 ≤ p.1 := by simp only [abs_eq_max_neg] at h1; omega
        rw [hdec, decomp_east M (M - 1) p.1 p.2 (by rw [abs_of_nonneg hp1]; exact h2) h1] at h3
        have hin : |p.1 - (M : ℤ)| + |p.2| ≤ ((M - 1 : ℕ) : ℤ) := by
          by_contra hgt
          have hgt' : ((M - 1 : ℕ) : ℤ) < |p.1 - (M : ℤ)| + |p.2| := by omega
          rw [cell_outside (M - 1) (p.1 - M) p.2 hgt'] at h3
          cases h3
        refine ⟨?_, ?_, h3⟩
        · rw [box_mem_iff]; simp only [abs_eq_max_neg] at hin ⊢; omega
        · simp only [abs_eq_max_neg] at h2 ⊢; omega
      · intro p1 _ p2 _ h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact Prod.ext (by omega) h2
      · intro q hq
        rw [Finset.mem_filter] at hq
        obtain ⟨_, hnotW, hcq⟩ := hq
        have hin : |q.1| + |q.2| ≤ ((M - 1 : ℕ) : ℤ) := by
          by_contra hgt
          have hgt' : ((M - 1 : ℕ) : ℤ) < |q.1| + |q.2| := by omega
          rw [cell_outside (M - 1) q.1 q.2 hgt'] at hcq
          cases hcq
        refine ⟨(q.1 + (M : ℤ), q.2), ?_, ?_⟩
        · rw [Finset.mem_filter]
          have h1 : |q.2| < q.1 + (M : ℤ) := by simp only [abs_eq_max_neg] at hin ⊢; omega
          have h2 : (M : ℤ) ≤ (q.1 + (M : ℤ)) + |q.2| := by simp only [abs_eq_max_neg] at hnotW ⊢; omega
          have hp1 : 0 ≤ q.1 + (M : ℤ) := by simp only [abs_eq_max_neg] at h1; omega
          refine ⟨?_, h1, h2, ?_⟩
          · rw [box_mem_iff]; simp only [abs_eq_max_neg] at hin ⊢; omega
          · rw [hdec, decomp_east M (M - 1) (q.1 + M) q.2 (by rw [abs_of_nonneg hp1]; exact h2) h1]
            simpa using hcq
        · exact Prod.ext (by ring) rfl
      · intro _ _; rfl
    rw [hbij]
    have h0 : c (M - 1) 0 0 = false := cell_origin_false k hk
    have htot := onCount_eq_four_eastCount (M - 1) h0
    rw [onCount_eq_box] at htot
    have hcomp : (∑ q ∈ box (M - 1), if ¬ (|q.2| < -q.1) ∧ c (M - 1) q.1 q.2 then 1 else 0) +
        (∑ q ∈ box (M - 1), if |q.2| < -q.1 ∧ c (M - 1) q.1 q.2 then 1 else 0) =
        ∑ q ∈ box (M - 1), if c (M - 1) q.1 q.2 then 1 else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q _
      by_cases h : |q.2| < -q.1 <;> by_cases hc : c (M - 1) q.1 q.2 <;> simp [h, hc]
    have hW : (∑ q ∈ box (M - 1), if |q.2| < -q.1 ∧ c (M - 1) q.1 q.2 then 1 else 0) =
        eastCount (M - 1) := by
      refine Finset.sum_bij (fun p _ => (-p.1, p.2)) ?_ ?_ ?_ ?_
      · intro p hp; rw [box_mem_iff] at hp ⊢; omega
      · intro p1 _ p2 _ h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact Prod.ext (by omega) h2
      · intro q hq; refine ⟨(-q.1, q.2), ?_, ?_⟩
        · rw [box_mem_iff] at hq ⊢; omega
        · exact Prod.ext (by ring) rfl
      · intro p _; simp [cell_neg_x]
    omega
  rw [hInner, hOuter]
  omega

private lemma onCount_rec (n : ℕ) (hn : 3 ≤ n) :
    onCount 14 (2 ^ n - 1) = 3 * onCount 14 (2 ^ (n - 1) - 1) + 4 ^ (n - 1) := by
  have h1 := onCount_eq_four_eastCount (2 ^ n - 1) (cell_origin_false n (by omega))
  have h2 := onCount_eq_four_eastCount (2 ^ (n - 1) - 1) (cell_origin_false (n - 1) (by omega))
  have h3 := eastCount_rec n hn
  have hpow : 4 * (2 ^ (n - 2) * 2 ^ (n - 2)) = 4 ^ (n - 1) := by
    have hsq : 2 ^ (n - 2) * 2 ^ (n - 2) = 4 ^ (n - 2) := by
      rw [← mul_pow]
      norm_num
    rw [hsq, show n - 1 = (n - 2) + 1 by omega, pow_succ']
  omega

-- ============================================================================
-- Section 4: Base cases, closed form, recurrence, and generating function
-- ============================================================================

private lemma a_0 : a 0 = 1 := by decide
private lemma a_1 : a 1 = 5 := by decide
private lemma a_2 : a 2 = 20 := by decide

private lemma a_closed_int (n : ℕ) (hn : 2 ≤ n) :
    a n = 4 * (3 : ℤ) ^ (n - 2) + (4 : ℤ) ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h2 : n = 1
    · subst h2; rw [a_2]; norm_num
    · have hn2 : 2 ≤ n := by omega
      have hrec := onCount_rec (n + 1) (by omega)
      have ha_rec : a (n + 1) = 3 * a n + (4 : ℤ) ^ n := by
        unfold a
        exact_mod_cast hrec
      rw [ha_rec, ih hn2]
      have h3 : (3 : ℤ) ^ (n + 1 - 2) = 3 * (3 : ℤ) ^ (n - 2) := by
        rw [show n + 1 - 2 = (n - 2) + 1 by omega, pow_succ']
      have h4 : (4 : ℤ) ^ (n + 1) = 4 * (4 : ℤ) ^ n := by rw [pow_succ']
      rw [h3, h4]
      ring

private lemma a_closed_rat (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℚ) = 4 * (3 : ℚ) ^ (n - 2) + (4 : ℚ) ^ n := by
  exact_mod_cast a_closed_int n hn

private lemma a_rec_rat (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℚ) = 7 * a (n - 1) - 12 * a (n - 2) := by
  rw [a_closed_rat n (by omega), a_closed_rat (n - 1) (by omega), a_closed_rat (n - 2) (by omega)]
  have h3a : (3 : ℚ) ^ (n - 2) = 9 * (3 : ℚ) ^ (n - 4) := by
    conv_lhs => rw [show n - 2 = (n - 4) + 2 by omega]
    rw [pow_add]; ring
  have h3b : (3 : ℚ) ^ (n - 1 - 2) = 3 * (3 : ℚ) ^ (n - 4) := by
    conv_lhs => rw [show n - 1 - 2 = (n - 4) + 1 by omega]
    rw [pow_succ']
  have h3c : (3 : ℚ) ^ (n - 2 - 2) = (3 : ℚ) ^ (n - 4) := by
    rw [show n - 2 - 2 = n - 4 by omega]
  have h4a : (4 : ℚ) ^ n = 16 * (4 : ℚ) ^ (n - 2) := by
    conv_lhs => rw [show n = (n - 2) + 2 by omega]
    rw [pow_add]; ring
  have h4b : (4 : ℚ) ^ (n - 1) = 4 * (4 : ℚ) ^ (n - 2) := by
    conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega]
    rw [pow_succ']
  rw [h3a, h3b, h3c, h4a, h4b]
  ring

private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - 3 * X) * (1 - 4 * X) : PowerSeries ℚ) =
      1 - 2 * X - 3 * X ^ 2 - 4 * X ^ 3 := by
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hlhs : A * ((1 - 3 * X) * (1 - 4 * X) : PowerSeries ℚ) =
      A - PowerSeries.C (7 : ℚ) * (A * X ^ 1) + PowerSeries.C (12 : ℚ) * (A * X ^ 2) := by
    simp only [map_ofNat, pow_one]
    ring
  have hrhs : (1 - 2 * X - 3 * X ^ 2 - 4 * X ^ 3 : PowerSeries ℚ) =
      PowerSeries.C (1 : ℚ) - PowerSeries.C (2 : ℚ) * X -
        PowerSeries.C (3 : ℚ) * X ^ 2 - PowerSeries.C (4 : ℚ) * X ^ 3 := by
    simp only [map_one, map_ofNat]
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_C, PowerSeries.coeff_X, PowerSeries.coeff_mk, A]
  by_cases hn : 4 ≤ n
  · have hrec := a_rec_rat n hn
    simp [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega]
    linarith
  · have h0 : (a 0 : ℚ) = 1 := by exact_mod_cast a_0
    have h1 : (a 1 : ℚ) = 5 := by exact_mod_cast a_1
    have h2 : (a 2 : ℚ) = 20 := by exact_mod_cast a_2
    have h3 : (a 3 : ℚ) = 76 := by
      have := a_closed_rat 3 (by omega)
      norm_num at this
      exact this
    interval_cases n <;> norm_num [h0, h1, h2, h3]

end OMA.Proof_oeis_a269708

theorem OMA.solution : type_of% @OMA.S_oeis_a269708.main :=
  ⟨OMA.Proof_oeis_a269708.a_closed_rat, OMA.Proof_oeis_a269708.a_rec_rat, OMA.Proof_oeis_a269708.gf_eq⟩

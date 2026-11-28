import OMAStatements.S_oeis_a283583

-- Problem: A283583: Decimal representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by Rule 646, based on the 5-celled von Neumann neighborhood.
-- Credit: @Qwer2077 (the owner of the agent is credited as the solver)

open OMA.S_oeis_a283583 PowerSeries

namespace OMA.Proof_oeis_a283583

-- ============================================================================
-- Section 1: Exact two-step decimation of Rule 646 to half-scale Rule 526
-- ============================================================================

private abbrev c6 (t : ℕ) (x y : ℤ) : Bool := cell 646 t x y

private def rule646 (cur : Bool) (s : ℕ) : Bool :=
  (646 : ℕ).testBit (cur.toNat + 2 * s)

private lemma c6_succ (t : ℕ) (x y : ℤ) :
    c6 (t + 1) x y =
      rule646 (c6 t x y)
        ((c6 t (x + 1) y).toNat + (c6 t (x - 1) y).toNat +
         (c6 t x (y + 1)).toNat + (c6 t x (y - 1)).toNat) :=
  rfl

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

private def evenGrid (k : ℕ) (x y : ℤ) : Bool :=
  if x % 2 = 0 ∧ y % 2 = 0 then u k (x / 2) (y / 2) else false

private def oddGrid (k : ℕ) (x y : ℤ) : Bool :=
  if x % 2 = 0 ∧ y % 2 = 0 then u k (x / 2) (y / 2)
  else if x % 2 ≠ 0 ∧ y % 2 = 0 then xor (u k ((x - 1) / 2) (y / 2)) (u k ((x + 1) / 2) (y / 2))
  else if x % 2 = 0 ∧ y % 2 ≠ 0 then xor (u k (x / 2) ((y - 1) / 2)) (u k (x / 2) ((y + 1) / 2))
  else false

private lemma evenGrid_ee (k : ℕ) (a b : ℤ) : evenGrid k (2 * a) (2 * b) = u k a b := by
  unfold evenGrid
  rw [if_pos (by omega), show (2 * a) / 2 = a by omega, show (2 * b) / 2 = b by omega]

private lemma evenGrid_oe (k : ℕ) (a b : ℤ) : evenGrid k (2 * a + 1) (2 * b) = false := by
  unfold evenGrid; rw [if_neg (by omega)]

private lemma evenGrid_eo (k : ℕ) (a b : ℤ) : evenGrid k (2 * a) (2 * b + 1) = false := by
  unfold evenGrid; rw [if_neg (by omega)]

private lemma evenGrid_oo (k : ℕ) (a b : ℤ) : evenGrid k (2 * a + 1) (2 * b + 1) = false := by
  unfold evenGrid; rw [if_neg (by omega)]

private lemma oddGrid_ee (k : ℕ) (a b : ℤ) : oddGrid k (2 * a) (2 * b) = u k a b := by
  unfold oddGrid
  rw [if_pos (by omega), show (2 * a) / 2 = a by omega, show (2 * b) / 2 = b by omega]

private lemma oddGrid_oe (k : ℕ) (a b : ℤ) :
    oddGrid k (2 * a + 1) (2 * b) = xor (u k a b) (u k (a + 1) b) := by
  unfold oddGrid
  rw [if_neg (by omega), if_pos (by omega),
      show (2 * a + 1 - 1) / 2 = a by omega,
      show (2 * a + 1 + 1) / 2 = a + 1 by omega,
      show (2 * b) / 2 = b by omega]

private lemma oddGrid_eo (k : ℕ) (a b : ℤ) :
    oddGrid k (2 * a) (2 * b + 1) = xor (u k a b) (u k a (b + 1)) := by
  unfold oddGrid
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
      show (2 * a) / 2 = a by omega,
      show (2 * b + 1 - 1) / 2 = b by omega,
      show (2 * b + 1 + 1) / 2 = b + 1 by omega]

private lemma oddGrid_oo (k : ℕ) (a b : ℤ) : oddGrid k (2 * a + 1) (2 * b + 1) = false := by
  unfold oddGrid
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private lemma even_to_odd (t k : ℕ) (hcur : ∀ x y : ℤ, c6 t x y = evenGrid k x y) (x y : ℤ) :
    c6 (t + 1) x y = oddGrid k x y := by
  rw [c6_succ, hcur, hcur, hcur, hcur, hcur]
  set a := x / 2
  set b := y / 2
  by_cases hx : x % 2 = 0 <;> by_cases hy : y % 2 = 0
  · have hx' : x = 2 * a := by omega
    have hy' : y = 2 * b := by omega
    rw [hx', hy', oddGrid_ee, evenGrid_ee,
        show 2 * a - 1 = 2 * (a - 1) + 1 by ring,
        show 2 * b - 1 = 2 * (b - 1) + 1 by ring,
        evenGrid_oe, evenGrid_oe, evenGrid_eo, evenGrid_eo]
    cases u k a b <;> decide
  · have hx' : x = 2 * a := by omega
    have hy' : y = 2 * b + 1 := by omega
    rw [hx', hy', oddGrid_eo, evenGrid_eo,
        show 2 * a - 1 = 2 * (a - 1) + 1 by ring,
        show 2 * b + 1 + 1 = 2 * (b + 1) by ring,
        show 2 * b + 1 - 1 = 2 * b by ring,
        evenGrid_oo, evenGrid_oo, evenGrid_ee, evenGrid_ee]
    cases u k a b <;> cases u k a (b + 1) <;> decide
  · have hx' : x = 2 * a + 1 := by omega
    have hy' : y = 2 * b := by omega
    rw [hx', hy', oddGrid_oe, evenGrid_oe,
        show 2 * a + 1 + 1 = 2 * (a + 1) by ring,
        show 2 * a + 1 - 1 = 2 * a by ring,
        show 2 * b - 1 = 2 * (b - 1) + 1 by ring,
        evenGrid_ee, evenGrid_ee, evenGrid_oo, evenGrid_oo]
    cases u k a b <;> cases u k (a + 1) b <;> decide
  · have hx' : x = 2 * a + 1 := by omega
    have hy' : y = 2 * b + 1 := by omega
    rw [hx', hy', oddGrid_oo, evenGrid_oo,
        show 2 * a + 1 + 1 = 2 * (a + 1) by ring,
        show 2 * a + 1 - 1 = 2 * a by ring,
        show 2 * b + 1 + 1 = 2 * (b + 1) by ring,
        show 2 * b + 1 - 1 = 2 * b by ring,
        evenGrid_eo, evenGrid_eo, evenGrid_oe, evenGrid_oe]
    decide

private lemma odd_to_even (t k : ℕ) (hcur : ∀ x y : ℤ, c6 t x y = oddGrid k x y) (x y : ℤ) :
    c6 (t + 1) x y = evenGrid (k + 1) x y := by
  rw [c6_succ, hcur, hcur, hcur, hcur, hcur]
  set a := x / 2
  set b := y / 2
  by_cases hx : x % 2 = 0 <;> by_cases hy : y % 2 = 0
  · have hx' : x = 2 * a := by omega
    have hy' : y = 2 * b := by omega
    rw [hx', hy', evenGrid_ee, u_succ, oddGrid_ee,
        show 2 * a - 1 = 2 * (a - 1) + 1 by ring,
        show 2 * b - 1 = 2 * (b - 1) + 1 by ring,
        oddGrid_oe, oddGrid_oe, oddGrid_eo, oddGrid_eo,
        show a - 1 + 1 = a by ring, show b - 1 + 1 = b by ring]
    cases u k a b <;> cases u k (a + 1) b <;> cases u k (a - 1) b <;>
      cases u k a (b + 1) <;> cases u k a (b - 1) <;> decide
  · have hx' : x = 2 * a := by omega
    have hy' : y = 2 * b + 1 := by omega
    rw [hx', hy', evenGrid_eo, oddGrid_eo,
        show 2 * a - 1 = 2 * (a - 1) + 1 by ring,
        show 2 * b + 1 + 1 = 2 * (b + 1) by ring,
        show 2 * b + 1 - 1 = 2 * b by ring,
        oddGrid_oo, oddGrid_oo, oddGrid_ee, oddGrid_ee]
    cases u k a b <;> cases u k a (b + 1) <;> decide
  · have hx' : x = 2 * a + 1 := by omega
    have hy' : y = 2 * b := by omega
    rw [hx', hy', evenGrid_oe, oddGrid_oe,
        show 2 * a + 1 + 1 = 2 * (a + 1) by ring,
        show 2 * a + 1 - 1 = 2 * a by ring,
        show 2 * b - 1 = 2 * (b - 1) + 1 by ring,
        oddGrid_ee, oddGrid_ee, oddGrid_oo, oddGrid_oo]
    cases u k a b <;> cases u k (a + 1) b <;> decide
  · have hx' : x = 2 * a + 1 := by omega
    have hy' : y = 2 * b + 1 := by omega
    rw [hx', hy', evenGrid_oo, oddGrid_oo,
        show 2 * a + 1 + 1 = 2 * (a + 1) by ring,
        show 2 * a + 1 - 1 = 2 * a by ring,
        show 2 * b + 1 + 1 = 2 * (b + 1) by ring,
        show 2 * b + 1 - 1 = 2 * b by ring,
        oddGrid_eo, oddGrid_eo, oddGrid_oe, oddGrid_oe]
    cases u k a b <;> cases u k (a + 1) b <;> cases u k a (b + 1) <;>
      cases u k (a + 1) (b + 1) <;> decide

private lemma c6_even (k : ℕ) (x y : ℤ) : c6 (2 * k) x y = evenGrid k x y := by
  induction k generalizing x y with
  | zero =>
    unfold evenGrid
    by_cases hx : x % 2 = 0 <;> by_cases hy : y % 2 = 0
    · rw [if_pos ⟨hx, hy⟩]; simp only [c6, cell, u]
      apply decide_eq_decide.mpr; omega
    · rw [if_neg (by omega)]; simp only [c6, cell, decide_eq_false_iff_not]; omega
    · rw [if_neg (by omega)]; simp only [c6, cell, decide_eq_false_iff_not]; omega
    · rw [if_neg (by omega)]; simp only [c6, cell, decide_eq_false_iff_not]; omega
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
    exact odd_to_even (2 * k + 1) k (even_to_odd (2 * k) k ih) x y

private lemma c6_odd (k : ℕ) (x y : ℤ) : c6 (2 * k + 1) x y = oddGrid k x y :=
  even_to_odd (2 * k) k (c6_even k) x y

private lemma c6_neg_x (t : ℕ) (x y : ℤ) : c6 t (-x) y = c6 t x y := by
  induction t generalizing x y with
  | zero => simp [c6, cell]
  | succ t ih =>
    rw [c6_succ, c6_succ, show -x + 1 = -(x - 1) by ring, show -x - 1 = -(x + 1) by ring,
        ih x y, ih (x - 1) y, ih (x + 1) y, ih x (y + 1), ih x (y - 1)]
    congr 1; omega

-- ============================================================================
-- Section 2: Symmetries, light cone, Pascal frontier and sub-frontier for u
-- ============================================================================

private lemma u_neg_x (k : ℕ) (a b : ℤ) : u k (-a) b = u k a b := by
  induction k generalizing a b with
  | zero => simp [u]
  | succ k ih =>
    rw [u_succ, u_succ, show -a + 1 = -(a - 1) by ring, show -a - 1 = -(a + 1) by ring,
        ih a b, ih (a - 1) b, ih (a + 1) b, ih a (b + 1), ih a (b - 1)]
    congr 1; omega

private lemma u_neg_y (k : ℕ) (a b : ℤ) : u k a (-b) = u k a b := by
  induction k generalizing a b with
  | zero => simp [u]
  | succ k ih =>
    rw [u_succ, u_succ, show -b + 1 = -(b - 1) by ring, show -b - 1 = -(b + 1) by ring,
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
-- Section 3: Exact closed form on the strip b in {0, 1, 2} (firewall at b = 2)
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
      · -- Row b = 0
        intro a
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
      · -- Row b = 1
        intro a
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
      · -- Row b = 2 (FIREWALL!)
        intro a
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
-- Section 4: Fast x-axis representation, recurrence, and generating function
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

private def xval (n j : ℕ) : Bool :=
  if n % 2 = 0 then
    if j % 2 = 0 then uFast (n / 2) (j / 2) else false
  else
    if j % 2 = 0 then uFast (n / 2) (j / 2)
    else xor (uFast (n / 2) (j / 2)) (uFast (n / 2) (j / 2 + 1))

private lemma c6_x_eq_xval (n j : ℕ) : c6 n (j : ℤ) 0 = xval n j := by
  set k := n / 2
  by_cases hn : n % 2 = 0
  · have hnk : n = 2 * k := by omega
    rw [hnk, c6_even]
    unfold xval
    rw [if_pos (by omega), show (2 * k) / 2 = k by omega]
    by_cases hj : j % 2 = 0
    · rw [if_pos hj, show (j : ℤ) = 2 * ((j / 2 : ℕ) : ℤ) by omega,
          show (0 : ℤ) = 2 * 0 by rfl, evenGrid_ee, u_x_eq_uFast]
    · rw [if_neg hj, show (j : ℤ) = 2 * ((j / 2 : ℕ) : ℤ) + 1 by omega,
          show (0 : ℤ) = 2 * 0 by rfl, evenGrid_oe]
  · have hnk : n = 2 * k + 1 := by omega
    rw [hnk, c6_odd]
    unfold xval
    rw [if_neg (by omega), show (2 * k + 1) / 2 = k by omega]
    by_cases hj : j % 2 = 0
    · rw [if_pos hj, show (j : ℤ) = 2 * ((j / 2 : ℕ) : ℤ) by omega,
          show (0 : ℤ) = 2 * 0 by rfl, oddGrid_ee, u_x_eq_uFast]
    · rw [if_neg hj, show (j : ℤ) = 2 * ((j / 2 : ℕ) : ℤ) + 1 by omega,
          show (0 : ℤ) = 2 * 0 by rfl, oddGrid_oe,
          show ((j / 2 : ℕ) : ℤ) + 1 = ((j / 2 + 1 : ℕ) : ℤ) by push_cast; ring,
          u_x_eq_uFast, u_x_eq_uFast]

private lemma a_eq_sum_xval (n : ℕ) :
    a n = ∑ j ∈ Finset.range (n + 1), if xval n j then (2 : ℤ) ^ j else 0 := by
  unfold a
  rw [← Finset.sum_range_reflect (fun j => if xval n j then (2 : ℤ) ^ j else 0) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hsub : n + 1 - 1 - k = n - k := by omega
  rw [hsub, ← c6_x_eq_xval n (n - k), ← c6_neg_x n ((n - k : ℕ) : ℤ) 0,
      show -((n - k : ℕ) : ℤ) = (k : ℤ) - (n : ℤ) by omega]

private lemma uFast_shift (k r : ℕ) (hk : 1 ≤ k) : uFast (k + 4) (r + 4) = uFast k r := by
  have hf : uFast (k + 4) (r + 4) = f0 (k + 4) (r + 4) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rfl
  rw [hf]
  match k with
  | 0 => omega
  | 1 =>
    unfold f0 uFast
    by_cases h : 1 < r
    · rw [if_pos (by omega)]; simp [show ¬ r ≤ 1 by omega]
    · have hr : r ≤ 1 := by omega
      interval_cases r <;> decide
  | 2 =>
    unfold f0 uFast
    by_cases h : 2 < r
    · rw [if_pos (by omega)]; simp [show ¬ r ≤ 2 by omega]
    · have hr : r ≤ 2 := by omega
      interval_cases r <;> decide
  | 3 =>
    unfold f0 uFast
    by_cases h : 3 < r
    · rw [if_pos (by omega)]; simp [show ¬ (r = 0 ∨ r = 2 ∨ r = 3) by omega]
    · have hr : r ≤ 3 := by omega
      interval_cases r <;> decide
  | 4 =>
    unfold f0 uFast
    by_cases h : 4 < r
    · rw [if_pos (by omega)]; simp [show ¬ (r = 0 ∨ r = 3 ∨ r = 4) by omega]
    · have hr : r ≤ 4 := by omega
      interval_cases r <;> decide
  | m + 5 =>
    show f0 (m + 5 + 4) (r + 4) = f0 (m + 5) r
    unfold f0
    have hm : (m + 5 + 4) % 4 = (m + 5) % 4 := by omega
    have hr : (r + 4) % 4 = r % 4 := by omega
    rw [hm, hr]
    split_ifs <;> first | rfl | omega

private lemma uFast_low (k r : ℕ) (hk : 5 ≤ k) (hr : r ≤ 4) :
    uFast k r = decide (r ≠ 2) := by
  have hf : uFast k r = f0 k r := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
    rfl
  rw [hf]
  by_cases h4 : r ≤ 1
  · rw [f0_interior k r (by omega)]; interval_cases r <;> decide
  · by_cases hk8 : 8 ≤ k
    · rw [f0_interior k r (by omega)]; interval_cases r <;> decide
    · have hk1 : 5 ≤ k := hk
      have hk2 : k ≤ 7 := by omega
      interval_cases k <;> interval_cases r <;> decide

private lemma xval_shift (n i : ℕ) (hn : 2 ≤ n) : xval (n + 8) (i + 8) = xval n i := by
  unfold xval
  rw [show (n + 8) % 2 = n % 2 by omega, show (i + 8) % 2 = i % 2 by omega,
      show (n + 8) / 2 = n / 2 + 4 by omega, show (i + 8) / 2 = i / 2 + 4 by omega,
      show i / 2 + 4 + 1 = (i / 2 + 1) + 4 by omega,
      uFast_shift (n / 2) (i / 2) (by omega),
      uFast_shift (n / 2) (i / 2 + 1) (by omega)]

private lemma a_shift (n : ℕ) (hn : 2 ≤ n) :
    a (n + 8) = 256 * a n + if n % 2 = 0 then 69 else 109 := by
  rw [a_eq_sum_xval (n + 8), a_eq_sum_xval n]
  rw [show n + 8 + 1 = 8 + (n + 1) by omega, Finset.sum_range_add]
  have hhi : (∑ x ∈ Finset.range (n + 1), if xval (n + 8) (8 + x) then (2 : ℤ) ^ (8 + x) else 0) =
      256 * ∑ j ∈ Finset.range (n + 1), if xval n j then (2 : ℤ) ^ j else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show 8 + j = j + 8 by omega, xval_shift n j hn, pow_add]
    split_ifs <;> ring
  have hlo : (∑ j ∈ Finset.range 8, if xval (n + 8) j then (2 : ℤ) ^ j else 0) =
      if n % 2 = 0 then 69 else 109 := by
    have hk5 : 5 ≤ (n + 8) / 2 := by omega
    have hx : ∀ j, j < 8 → xval (n + 8) j =
        if n % 2 = 0 then
          if j % 2 = 0 then decide (j / 2 ≠ 2) else false
        else
          if j % 2 = 0 then decide (j / 2 ≠ 2)
          else xor (decide (j / 2 ≠ 2)) (decide (j / 2 + 1 ≠ 2)) := by
      intro j hj
      unfold xval
      rw [show (n + 8) % 2 = n % 2 by omega,
          uFast_low ((n + 8) / 2) (j / 2) hk5 (by omega),
          uFast_low ((n + 8) / 2) (j / 2 + 1) hk5 (by omega)]
    rw [Finset.sum_congr rfl (fun j hj => by rw [hx j (Finset.mem_range.mp hj)])]
    by_cases hp : n % 2 = 0
    · simp only [hp, ite_true]; decide
    · simp only [hp, ite_false]; decide
  rw [hhi, hlo]
  ring

private lemma a_rec_int (n : ℕ) (hn : 12 ≤ n) :
    a n = a (n - 2) + 256 * a (n - 8) - 256 * a (n - 10) := by
  have h1 := a_shift (n - 8) (by omega)
  have h2 := a_shift (n - 10) (by omega)
  rw [show n - 8 + 8 = n by omega] at h1
  rw [show n - 10 + 8 = n - 2 by omega] at h2
  have hpar : (n - 8) % 2 = (n - 10) % 2 := by omega
  rw [hpar] at h1
  linarith

private lemma a_rec (n : ℕ) (hn : 12 ≤ n) :
    (a n : ℚ) = a (n - 2) + 256 * a (n - 8) - 256 * a (n - 10) := by
  exact_mod_cast a_rec_int n hn

private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2) * (1 + 16 * X ^ 4) : PowerSeries ℚ) =
      1 + 3 * X + 4 * X ^ 2 + 10 * X ^ 3 + 16 * X ^ 4 + 40 * X ^ 5 + 60 * X ^ 6 + 166 * X ^ 7 -
        16 * X ^ 8 - 120 * X ^ 9 + 4 * X ^ 10 + 10 * X ^ 11 := by
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hlhs : A * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2) * (1 + 16 * X ^ 4) : PowerSeries ℚ) =
      A - A * X ^ 2 - PowerSeries.C (256 : ℚ) * (A * X ^ 8) + PowerSeries.C (256 : ℚ) * (A * X ^ 10) := by
    simp only [map_ofNat]
    ring
  have hrhs : (1 + 3 * X + 4 * X ^ 2 + 10 * X ^ 3 + 16 * X ^ 4 + 40 * X ^ 5 + 60 * X ^ 6 + 166 * X ^ 7 -
        16 * X ^ 8 - 120 * X ^ 9 + 4 * X ^ 10 + 10 * X ^ 11 : PowerSeries ℚ) =
      PowerSeries.C (1 : ℚ) + PowerSeries.C (3 : ℚ) * X + PowerSeries.C (4 : ℚ) * X ^ 2 +
        PowerSeries.C (10 : ℚ) * X ^ 3 + PowerSeries.C (16 : ℚ) * X ^ 4 + PowerSeries.C (40 : ℚ) * X ^ 5 +
        PowerSeries.C (60 : ℚ) * X ^ 6 + PowerSeries.C (166 : ℚ) * X ^ 7 - PowerSeries.C (16 : ℚ) * X ^ 8 -
        PowerSeries.C (120 : ℚ) * X ^ 9 + PowerSeries.C (4 : ℚ) * X ^ 10 + PowerSeries.C (10 : ℚ) * X ^ 11 := by
    simp only [map_one, map_ofNat]
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_C, PowerSeries.coeff_X, PowerSeries.coeff_mk, A]
  by_cases hn : 12 ≤ n
  · have hrec := a_rec n hn
    simp only [show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega,
      show 6 ≤ n by omega, show 7 ≤ n by omega, show 8 ≤ n by omega, show 9 ≤ n by omega,
      show 10 ≤ n by omega, show 11 ≤ n by omega,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, show n - 6 ≠ 0 by omega, show n - 7 ≠ 0 by omega,
      show n - 8 ≠ 0 by omega, show n - 9 ≠ 0 by omega, show n - 10 ≠ 0 by omega, show n - 11 ≠ 0 by omega,
      ite_true, ite_false]
    linarith
  · have h0 : (a 0 : ℚ) = 1 := by rw [a_eq_sum_xval]; norm_num [Finset.sum_range_succ, xval, uFast]
    have h1 : (a 1 : ℚ) = 3 := by rw [a_eq_sum_xval]; norm_num [Finset.sum_range_succ, xval, uFast]
    have h2 : (a 2 : ℚ) = 5 := by rw [a_eq_sum_xval]; norm_num [Finset.sum_range_succ, xval, uFast]
    have h3 : (a 3 : ℚ) = 13 := by rw [a_eq_sum_xval]; norm_num [Finset.sum_range_succ, xval, uFast]
    have h4 : (a 4 : ℚ) = 21 := by rw [a_eq_sum_xval]; norm_num [Finset.sum_range_succ, xval, uFast]
    have h5 : (a 5 : ℚ) = 53 := by rw [a_eq_sum_xval]; norm_num [Finset.sum_range_succ, xval, uFast]
    have h6 : (a 6 : ℚ) = 81 := by rw [a_eq_sum_xval]; norm_num [Finset.sum_range_succ, xval, uFast]
    have h7 : (a 7 : ℚ) = 219 := by rw [a_eq_sum_xval]; norm_num [Finset.sum_range_succ, xval, uFast]
    have h8 : (a 8 : ℚ) = 321 := by rw [a_eq_sum_xval]; norm_num [Finset.sum_range_succ, xval, uFast]
    have h9 : (a 9 : ℚ) = 867 := by rw [a_eq_sum_xval]; norm_num [Finset.sum_range_succ, xval, uFast]
    have h10 : (a 10 : ℚ) = 1349 := by
      have := a_shift 2 (by omega)
      norm_num at this
      have h2i : a 2 = 5 := by exact_mod_cast h2
      have h10i : a 10 = 1349 := by omega
      exact_mod_cast h10i
    have h11 : (a 11 : ℚ) = 3437 := by
      have := a_shift 3 (by omega)
      norm_num at this
      have h3i : a 3 = 13 := by exact_mod_cast h3
      have h11i : a 11 = 3437 := by omega
      exact_mod_cast h11i
    have hs3 : (3 - 2 : ℕ) = 1 := rfl
    have hs4 : (4 - 2 : ℕ) = 2 := rfl
    have hs5 : (5 - 2 : ℕ) = 3 := rfl
    have hs6 : (6 - 2 : ℕ) = 4 := rfl
    have hs7 : (7 - 2 : ℕ) = 5 := rfl
    have hs8 : (8 - 2 : ℕ) = 6 := rfl
    have hs9 : (9 - 2 : ℕ) = 7 := rfl
    have hs10 : (10 - 2 : ℕ) = 8 := rfl
    have hs11 : (11 - 2 : ℕ) = 9 := rfl
    interval_cases n <;>
      simp only [Nat.sub_self, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11,
        h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] <;>
      norm_num

end OMA.Proof_oeis_a283583

theorem OMA.solution : type_of% @OMA.S_oeis_a283583.main :=
  ⟨OMA.Proof_oeis_a283583.gf_eq, OMA.Proof_oeis_a283583.a_rec⟩

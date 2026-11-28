import OMAStatements.S_oeis_a281738

-- Problem: A281738: Decimal representation of the x-axis of the n-th stage of Rule 390 cellular automaton.
-- Upstream: statements/oeis-a281738.lean (declaration OMA.S_oeis_a281738.main)
-- Credit: @rgoldman73-dev

namespace OMA.Proof_oeis_a281738

open Finset PowerSeries OMA.S_oeis_a281738

private def rule390 (c n1 n2 n3 n4 : Bool) : Bool :=
  (390 : ℕ).testBit (c.toNat + 2 * (n1.toNat + n2.toNat + n3.toNat + n4.toNat))

private lemma cell_succ_eq (t : ℕ) (i j : ℤ) :
    cell 390 (t + 1) i j =
      rule390 (cell 390 t i j) (cell 390 t (i + 1) j) (cell 390 t (i - 1) j)
        (cell 390 t i (j + 1)) (cell 390 t i (j - 1)) := rfl

private lemma rule390_comm_h (c a b u v : Bool) :
    rule390 c a b u v = rule390 c b a u v := by
  cases c <;> cases a <;> cases b <;> cases u <;> cases v <;> decide

private lemma rule390_comm_v (c a b u v : Bool) :
    rule390 c a b u v = rule390 c a b v u := by
  cases c <;> cases a <;> cases b <;> cases u <;> cases v <;> decide

private lemma rule390_all_false (c : Bool) :
    rule390 c false false false false = c := by
  cases c <;> decide

private lemma rule390_false_zero_h (u : Bool) :
    rule390 false false false u u = false := by
  cases u <;> decide

private lemma rule390_two_step_odd (a b u v : Bool) :
    rule390 (rule390 false a b u v) a b u v = false := by
  cases a <;> cases b <;> cases u <;> cases v <;> decide

private lemma rule390_boundary (a b : Bool) :
    rule390 false false a false b = xor a b := by
  cases a <;> cases b <;> decide

private lemma cell_neg_right (t : ℕ) : ∀ i j : ℤ, cell 390 t i (-j) = cell 390 t i j := by
  induction t with
  | zero =>
    intro i j
    simp only [cell, neg_eq_zero]
  | succ t ih =>
    intro i j
    rw [cell_succ_eq, cell_succ_eq, ih i j, ih (i + 1) j, ih (i - 1) j]
    have h1 : -j + 1 = -(j - 1) := by ring
    have h2 : -j - 1 = -(j + 1) := by ring
    rw [h1, h2, ih i (j - 1), ih i (j + 1), rule390_comm_v]

private lemma cell_neg_left (t : ℕ) : ∀ i j : ℤ, cell 390 t (-i) j = cell 390 t i j := by
  induction t with
  | zero =>
    intro i j
    simp only [cell, neg_eq_zero]
  | succ t ih =>
    intro i j
    rw [cell_succ_eq, cell_succ_eq, ih i j, ih i (j + 1), ih i (j - 1)]
    have h1 : -i + 1 = -(i - 1) := by ring
    have h2 : -i - 1 = -(i + 1) := by ring
    rw [h1, h2, ih (i - 1) j, ih (i + 1) j, rule390_comm_h]

private lemma cell_lightcone (t : ℕ) :
    ∀ i j : ℤ, t < i.natAbs + j.natAbs → cell 390 t i j = false := by
  induction t with
  | zero =>
    intro i j h
    simp only [cell, decide_eq_false_iff_not]
    omega
  | succ t ih =>
    intro i j h
    rw [cell_succ_eq,
      ih i j (by omega),
      ih (i + 1) j (by omega),
      ih (i - 1) j (by omega),
      ih i (j + 1) (by omega),
      ih i (j - 1) (by omega)]
    decide

private lemma cell_checkerboard (k : ℕ) :
    (∀ i j : ℤ, (i + j) % 2 ≠ 0 → cell 390 (2 * k) i j = false) ∧
    (∀ i j : ℤ, (i + j) % 2 = 0 → cell 390 (2 * k + 1) i j = cell 390 (2 * k) i j) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro i j hij
      simp only [cell, decide_eq_false_iff_not]
      omega
    · intro i j hij
      simp only [Nat.mul_zero, zero_add]
      rw [cell_succ_eq]
      have h0 : ∀ a b : ℤ, (a + b) % 2 ≠ 0 → cell 390 0 a b = false := by
        intro a b hab; simp only [cell, decide_eq_false_iff_not]; omega
      rw [h0 (i + 1) j (by omega), h0 (i - 1) j (by omega),
        h0 i (j + 1) (by omega), h0 i (j - 1) (by omega), rule390_all_false]
  | succ k ih =>
    obtain ⟨heven, hodd⟩ := ih
    have h2 : ∀ i j : ℤ, (i + j) % 2 ≠ 0 → cell 390 (2 * (k + 1)) i j = false := by
      intro i j hij
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, cell_succ_eq]
      have hc : cell 390 (2 * k + 1) i j =
          rule390 false (cell 390 (2 * k) (i + 1) j) (cell 390 (2 * k) (i - 1) j)
            (cell 390 (2 * k) i (j + 1)) (cell 390 (2 * k) i (j - 1)) := by
        rw [cell_succ_eq, heven i j hij]
      rw [hc,
        hodd (i + 1) j (by omega), hodd (i - 1) j (by omega),
        hodd i (j + 1) (by omega), hodd i (j - 1) (by omega),
        rule390_two_step_odd]
    refine ⟨h2, ?_⟩
    intro i j hij
    rw [cell_succ_eq,
      h2 (i + 1) j (by omega), h2 (i - 1) j (by omega),
      h2 i (j + 1) (by omega), h2 i (j - 1) (by omega),
      rule390_all_false]

private lemma cell_diag0 (t : ℕ) : cell 390 t (t : ℤ) 0 = true := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [cell_succ_eq,
      cell_lightcone t (t + 1 : ℕ) 0 (by omega),
      cell_lightcone t ((t + 1 : ℕ) + 1) 0 (by omega),
      cell_lightcone t (t + 1 : ℕ) (0 + 1) (by omega),
      cell_lightcone t (t + 1 : ℕ) (0 - 1) (by omega)]
    have hsub : ((t + 1 : ℕ) : ℤ) - 1 = (t : ℤ) := by omega
    rw [hsub, ih]
    decide

private lemma cell_diag_step (t : ℕ) (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i + j = t + 1) :
    cell 390 (t + 1) (i : ℤ) (j : ℤ) =
      xor (cell 390 t ((i - 1 : ℕ) : ℤ) (j : ℤ)) (cell 390 t (i : ℤ) ((j - 1 : ℕ) : ℤ)) := by
  rw [cell_succ_eq,
    cell_lightcone t (i : ℤ) (j : ℤ) (by omega),
    cell_lightcone t ((i : ℤ) + 1) (j : ℤ) (by omega),
    cell_lightcone t (i : ℤ) ((j : ℤ) + 1) (by omega)]
  have hi' : (i : ℤ) - 1 = ((i - 1 : ℕ) : ℤ) := by omega
  have hj' : (j : ℤ) - 1 = ((j - 1 : ℕ) : ℤ) := by omega
  rw [hi', hj', rule390_boundary]

private lemma cell_diag1 (t : ℕ) (ht : 1 ≤ t) :
    cell 390 t ((t - 1 : ℕ) : ℤ) 1 = decide (t % 2 = 1) := by
  induction t with
  | zero => omega
  | succ t ih =>
    cases t with
    | zero => decide
    | succ t =>
      have hstep := cell_diag_step (t + 1) (t + 1) 1 (by omega) (by omega) (by omega)
      have hih := ih (by omega)
      simp only [Nat.add_sub_cancel, Nat.cast_one] at hstep hih ⊢
      rw [hstep, show (1 - 1 : ℕ) = 0 by decide, Nat.cast_zero, cell_diag0 (t + 1), hih]
      have hm : (t + 1) % 2 = 0 ∨ (t + 1) % 2 = 1 := by omega
      rcases hm with h | h
      · rw [show (t + 1 + 1) % 2 = 1 by omega, h]; decide
      · rw [show (t + 1 + 1) % 2 = 0 by omega, h]; decide

private lemma cell_diag2 (t : ℕ) (ht : 2 ≤ t) :
    cell 390 t ((t - 2 : ℕ) : ℤ) 2 = decide (t % 4 = 2 ∨ t % 4 = 3) := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases ht2 : t = 1
    · subst ht2; decide
    · have ht' : 2 ≤ t := by omega
      have hstep := cell_diag_step t (t - 1) 2 (by omega) (by omega) (by omega)
      simp only [Nat.cast_ofNat] at hstep
      rw [show t + 1 - 2 = t - 1 by omega, hstep, show t - 1 - 1 = t - 2 by omega,
        show (2 - 1 : ℕ) = 1 by decide, Nat.cast_one, ih ht', cell_diag1 t (by omega)]
      have hm : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
      rcases hm with h | h | h | h
      · rw [show t % 2 = 0 by omega, show (t + 1) % 4 = 1 by omega, h]; decide
      · rw [show t % 2 = 1 by omega, show (t + 1) % 4 = 2 by omega, h]; decide
      · rw [show t % 2 = 0 by omega, show (t + 1) % 4 = 3 by omega, h]; decide
      · rw [show t % 2 = 1 by omega, show (t + 1) % 4 = 0 by omega, h]; decide

-- Period-4 invariant at t = 4*k (for k >= 6)
private def Inv (k : ℕ) : Prop :=
  (∀ i : ℤ, cell 390 (4 * k) i 0 = decide (i.natAbs = 4 * k)) ∧
  cell 390 (4 * k) ((4 * k - 3 : ℕ) : ℤ) 1 = true

private lemma step_even_to_odd (m : ℕ) (hm : 2 ≤ m)
    (hx : ∀ i : ℤ, cell 390 (2 * m) i 0 = decide (i.natAbs = 2 * m)) :
    (∀ i : ℤ, cell 390 (2 * m + 1) i 0 =
      decide (i.natAbs = 2 * m - 1 ∨ i.natAbs = 2 * m ∨ i.natAbs = 2 * m + 1)) ∧
    cell 390 (2 * m + 1) (2 * m : ℤ) 1 = true := by
  have hcb := (cell_checkerboard m).2
  have hd1 : cell 390 (2 * m) ((2 * m - 1 : ℕ) : ℤ) 1 = false := by
    rw [cell_diag1 (2 * m) (by omega)]; simp [Nat.mul_mod_right]
  refine ⟨?_, ?_⟩
  · intro i
    by_cases hev : i % 2 = 0
    · have := hcb i 0 (by omega)
      rw [this, hx i]
      by_cases hi : i.natAbs = 2 * m
      · simp [hi]
      · have h1 : i.natAbs ≠ 2 * m - 1 := by omega
        have h2 : i.natAbs ≠ 2 * m + 1 := by omega
        simp [hi, h1, h2]
    · have h0 : cell 390 (2 * m) i 0 = false := by
        rw [hx i]; simp only [decide_eq_false_iff_not]; omega
      rw [cell_succ_eq, h0, show (0 : ℤ) + 1 = 1 by decide,
        show (0 : ℤ) - 1 = -(1 : ℤ) by decide, cell_neg_right]
      by_cases hhi : i.natAbs = 2 * m + 1
      · have hsym : cell 390 (2 * m) i 1 = false := cell_lightcone (2 * m) i 1 (by omega)
        have hnbr : (cell 390 (2 * m) (i + 1) 0 = true ∧ cell 390 (2 * m) (i - 1) 0 = false) ∨
            (cell 390 (2 * m) (i + 1) 0 = false ∧ cell 390 (2 * m) (i - 1) 0 = true) := by
          rw [hx (i + 1), hx (i - 1)]
          by_cases hpos : 0 ≤ i
          · right; exact ⟨by simp only [decide_eq_false_iff_not]; omega, by simp only [decide_eq_true_eq]; omega⟩
          · left; exact ⟨by simp only [decide_eq_true_eq]; omega, by simp only [decide_eq_false_iff_not]; omega⟩
        rw [hsym, show decide (i.natAbs = 2 * m - 1 ∨ i.natAbs = 2 * m ∨ i.natAbs = 2 * m + 1) = true by simp [hhi]]
        rcases hnbr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
      · by_cases hlo : i.natAbs = 2 * m - 1
        · have hsym : cell 390 (2 * m) i 1 = false := by
            by_cases hpos : 0 ≤ i
            · have hi : i = ((2 * m - 1 : ℕ) : ℤ) := by omega
              rw [hi]; exact hd1
            · have hi : i = -((2 * m - 1 : ℕ) : ℤ) := by omega
              rw [hi, cell_neg_left]; exact hd1
          have hnbr : (cell 390 (2 * m) (i + 1) 0 = true ∧ cell 390 (2 * m) (i - 1) 0 = false) ∨
              (cell 390 (2 * m) (i + 1) 0 = false ∧ cell 390 (2 * m) (i - 1) 0 = true) := by
            rw [hx (i + 1), hx (i - 1)]
            by_cases hpos : 0 ≤ i
            · left; exact ⟨by simp only [decide_eq_true_eq]; omega, by simp only [decide_eq_false_iff_not]; omega⟩
            · right; exact ⟨by simp only [decide_eq_false_iff_not]; omega, by simp only [decide_eq_true_eq]; omega⟩
          rw [hsym, show decide (i.natAbs = 2 * m - 1 ∨ i.natAbs = 2 * m ∨ i.natAbs = 2 * m + 1) = true by simp [hlo]]
          rcases hnbr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
        · have h1 : cell 390 (2 * m) (i + 1) 0 = false := by
            rw [hx (i + 1)]; simp only [decide_eq_false_iff_not]; omega
          have h2 : cell 390 (2 * m) (i - 1) 0 = false := by
            rw [hx (i - 1)]; simp only [decide_eq_false_iff_not]; omega
          have hne : i.natAbs ≠ 2 * m := by omega
          rw [h1, h2, rule390_false_zero_h]
          simp [hlo, hne, hhi]
  · rw [cell_succ_eq,
      cell_lightcone (2 * m) (2 * m : ℤ) 1 (by omega),
      cell_lightcone (2 * m) ((2 * m : ℤ) + 1) 1 (by omega),
      cell_lightcone (2 * m) (2 * m : ℤ) (1 + 1) (by omega),
      show (2 * m : ℤ) - 1 = ((2 * m - 1 : ℕ) : ℤ) by omega, hd1,
      show (1 : ℤ) - 1 = 0 by decide, hx (2 * m : ℤ),
      show (2 * (m : ℤ)).natAbs = 2 * m by omega]
    simp only [decide_true]
    decide

private lemma step_odd_to_even (m : ℕ) (hm : 2 ≤ m)
    (hx : ∀ i : ℤ, cell 390 (2 * m + 1) i 0 =
      decide (i.natAbs = 2 * m - 1 ∨ i.natAbs = 2 * m ∨ i.natAbs = 2 * m + 1))
    (h1 : cell 390 (2 * m + 1) (2 * m : ℤ) 1 = true)
    (h2 : cell 390 (2 * m + 1) ((2 * m - 2 : ℕ) : ℤ) 1 = true) :
    ∀ i : ℤ, cell 390 (2 * m + 2) i 0 = decide (i.natAbs = 2 * m + 2) := by
  intro i
  by_cases hodd : i % 2 ≠ 0
  · have hcb := (cell_checkerboard (m + 1)).1 i 0 (by omega)
    rw [show 2 * (m + 1) = 2 * m + 2 by omega] at hcb
    rw [hcb, show decide (i.natAbs = 2 * m + 2) = false by
      rw [decide_eq_false_iff_not]; omega]
  · by_cases htop : i.natAbs = 2 * m + 2
    · rw [show decide (i.natAbs = 2 * m + 2) = true by simp [htop]]
      by_cases hpos : 0 ≤ i
      · have hi : i = ((2 * m + 2 : ℕ) : ℤ) := by omega
        rw [hi, cell_diag0 (2 * m + 2)]
      · have hi : i = -((2 * m + 2 : ℕ) : ℤ) := by omega
        rw [hi, cell_neg_left, cell_diag0 (2 * m + 2)]
    · by_cases hbig : 2 * m + 2 < i.natAbs
      · rw [cell_lightcone (2 * m + 2) i 0 (by omega),
          show decide (i.natAbs = 2 * m + 2) = false by simp [htop]]
      · rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, cell_succ_eq,
          show (0 : ℤ) + 1 = 1 by decide, show (0 : ℤ) - 1 = -(1 : ℤ) by decide, cell_neg_right]
        by_cases h2m : i.natAbs = 2 * m
        · have hc : cell 390 (2 * m + 1) i 0 = true := by rw [hx i]; simp [h2m]
          have ha : cell 390 (2 * m + 1) (i + 1) 0 = true := by rw [hx (i + 1)]; simp only [decide_eq_true_eq]; omega
          have hb : cell 390 (2 * m + 1) (i - 1) 0 = true := by rw [hx (i - 1)]; simp only [decide_eq_true_eq]; omega
          have hv : cell 390 (2 * m + 1) i 1 = true := by
            by_cases hpos : 0 ≤ i
            · rw [show i = (2 * m : ℤ) by omega]; exact h1
            · rw [show i = -(2 * m : ℤ) by omega, cell_neg_left]; exact h1
          rw [hc, ha, hb, hv, show decide (i.natAbs = 2 * m + 2) = false by simp [htop]]
          decide
        · by_cases h2m2 : i.natAbs = 2 * m - 2
          · have hc : cell 390 (2 * m + 1) i 0 = false := by
              rw [hx i]; simp only [decide_eq_false_iff_not]; omega
            have hv : cell 390 (2 * m + 1) i 1 = true := by
              by_cases hpos : 0 ≤ i
              · rw [show i = ((2 * m - 2 : ℕ) : ℤ) by omega]; exact h2
              · rw [show i = -((2 * m - 2 : ℕ) : ℤ) by omega, cell_neg_left]; exact h2
            have hnbr : (cell 390 (2 * m + 1) (i + 1) 0 = true ∧ cell 390 (2 * m + 1) (i - 1) 0 = false) ∨
                (cell 390 (2 * m + 1) (i + 1) 0 = false ∧ cell 390 (2 * m + 1) (i - 1) 0 = true) := by
              rw [hx (i + 1), hx (i - 1)]
              by_cases hpos : 0 ≤ i
              · left; exact ⟨by simp only [decide_eq_true_eq]; omega, by simp only [decide_eq_false_iff_not]; omega⟩
              · right; exact ⟨by simp only [decide_eq_false_iff_not]; omega, by simp only [decide_eq_true_eq]; omega⟩
            rw [hc, hv, show decide (i.natAbs = 2 * m + 2) = false by simp [htop]]
            rcases hnbr with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] <;> decide
          · have hc : cell 390 (2 * m + 1) i 0 = false := by
              rw [hx i]; simp only [decide_eq_false_iff_not]; omega
            have ha : cell 390 (2 * m + 1) (i + 1) 0 = false := by
              rw [hx (i + 1)]; simp only [decide_eq_false_iff_not]; omega
            have hb : cell 390 (2 * m + 1) (i - 1) 0 = false := by
              rw [hx (i - 1)]; simp only [decide_eq_false_iff_not]; omega
            rw [hc, ha, hb, rule390_false_zero_h, show decide (i.natAbs = 2 * m + 2) = false by simp [htop]]

private lemma step_four (k : ℕ) (hk : 2 ≤ k) (hinv : Inv k) :
    Inv (k + 1) ∧
    (∀ i : ℤ, cell 390 (4 * k + 1) i 0 =
      decide (i.natAbs = 4 * k - 1 ∨ i.natAbs = 4 * k ∨ i.natAbs = 4 * k + 1)) ∧
    (∀ i : ℤ, cell 390 (4 * k + 2) i 0 = decide (i.natAbs = 4 * k + 2)) ∧
    (∀ i : ℤ, cell 390 (4 * k + 3) i 0 =
      decide (i.natAbs = 4 * k + 1 ∨ i.natAbs = 4 * k + 2 ∨ i.natAbs = 4 * k + 3)) := by
  obtain ⟨hx0, hwing0⟩ := hinv
  have h1 := step_even_to_odd (2 * k) (by omega) (by simpa [show 2 * (2 * k) = 4 * k by omega] using hx0)
  rw [show 2 * (2 * k) = 4 * k by omega] at h1
  obtain ⟨hx1, h1a⟩ := h1
  -- Compute (4*k - 2, 1) at 4*k + 1
  have h1b : cell 390 (4 * k + 1) ((4 * k - 2 : ℕ) : ℤ) 1 = true := by
    rw [cell_succ_eq]
    have hc : cell 390 (4 * k) ((4 * k - 2 : ℕ) : ℤ) 1 = false := by
      have := (cell_checkerboard (2 * k)).1 ((4 * k - 2 : ℕ) : ℤ) 1 (by omega)
      simpa [show 2 * (2 * k) = 4 * k by omega] using this
    have hr : cell 390 (4 * k) (((4 * k - 2 : ℕ) : ℤ) + 1) 1 = false := by
      rw [show (((4 * k - 2 : ℕ) : ℤ) + 1) = ((4 * k - 1 : ℕ) : ℤ) by omega,
        cell_diag1 (4 * k) (by omega)]
      simp [show (4 * k) % 2 = 0 by omega]
    have hl : cell 390 (4 * k) (((4 * k - 2 : ℕ) : ℤ) - 1) 1 = true := by
      rw [show (((4 * k - 2 : ℕ) : ℤ) - 1) = ((4 * k - 3 : ℕ) : ℤ) by omega]; exact hwing0
    have hu : cell 390 (4 * k) ((4 * k - 2 : ℕ) : ℤ) (1 + 1) = false := by
      rw [show (1 : ℤ) + 1 = 2 by decide, cell_diag2 (4 * k) (by omega)]
      simp [show (4 * k) % 4 = 0 by omega]
    have hd : cell 390 (4 * k) ((4 * k - 2 : ℕ) : ℤ) (1 - 1) = false := by
      rw [show (1 : ℤ) - 1 = 0 by decide, hx0]; simp only [Int.natAbs_natCast, decide_eq_false_iff_not]; omega
    rw [hc, hr, hl, hu, hd]; decide
  -- Step 4*k + 1 -> 4*k + 2
  have hx2 : ∀ i : ℤ, cell 390 (4 * k + 2) i 0 = decide (i.natAbs = 4 * k + 2) := by
    have := step_odd_to_even (2 * k) (by omega)
      (by simpa [show 2 * (2 * k) = 4 * k by omega] using hx1)
      (by simpa [show 2 * (2 * k) = 4 * k by omega] using h1a)
      (by simpa [show 2 * (2 * k) = 4 * k by omega] using h1b)
    simpa [show 2 * (2 * k) + 2 = 4 * k + 2 by omega] using this
  -- Compute (4*k - 1, 1) at 4*k + 2 -> false
  have h2wing : cell 390 (4 * k + 2) ((4 * k - 1 : ℕ) : ℤ) 1 = false := by
    rw [show 4 * k + 2 = (4 * k + 1) + 1 by omega, cell_succ_eq]
    have hc : cell 390 (4 * k + 1) ((4 * k - 1 : ℕ) : ℤ) 1 = false := by
      have hcb := (cell_checkerboard (2 * k)).2 ((4 * k - 1 : ℕ) : ℤ) 1 (by omega)
      rw [show 2 * (2 * k) = 4 * k by omega] at hcb
      rw [hcb, cell_diag1 (4 * k) (by omega)]
      simp [show (4 * k) % 2 = 0 by omega]
    have hr : cell 390 (4 * k + 1) (((4 * k - 1 : ℕ) : ℤ) + 1) 1 = true := by
      rw [show (((4 * k - 1 : ℕ) : ℤ) + 1) = (2 * ((2 * k : ℕ) : ℤ)) by push_cast; omega]; exact h1a
    have hl : cell 390 (4 * k + 1) (((4 * k - 1 : ℕ) : ℤ) - 1) 1 = true := by
      rw [show (((4 * k - 1 : ℕ) : ℤ) - 1) = ((4 * k - 2 : ℕ) : ℤ) by omega]; exact h1b
    have hu : cell 390 (4 * k + 1) ((4 * k - 1 : ℕ) : ℤ) (1 + 1) = false := by
      rw [show (1 : ℤ) + 1 = 2 by decide, show 4 * k - 1 = (4 * k + 1) - 2 by omega,
        cell_diag2 (4 * k + 1) (by omega)]
      simp [show (4 * k + 1) % 4 = 1 by omega]
    have hd : cell 390 (4 * k + 1) ((4 * k - 1 : ℕ) : ℤ) (1 - 1) = true := by
      rw [show (1 : ℤ) - 1 = 0 by decide, hx1]; simp
    rw [hc, hr, hl, hu, hd]; decide
  -- Step 4*k + 2 -> 4*k + 3
  have h3 := step_even_to_odd (2 * k + 1) (by omega)
    (by simpa [show 2 * (2 * k + 1) = 4 * k + 2 by omega] using hx2)
  rw [show 2 * (2 * k + 1) = 4 * k + 2 by omega,
    show 4 * k + 2 - 1 = 4 * k + 1 by omega,
    show 4 * k + 2 + 1 = 4 * k + 3 by omega] at h3
  obtain ⟨hx3, h3a⟩ := h3
  -- Compute (4*k, 1) at 4*k + 3 -> true
  have h3b : cell 390 (4 * k + 3) (4 * k : ℤ) 1 = true := by
    rw [show 4 * k + 3 = (4 * k + 2) + 1 by omega, cell_succ_eq]
    have hc : cell 390 (4 * k + 2) (4 * k : ℤ) 1 = false := by
      have := (cell_checkerboard (2 * k + 1)).1 (4 * k : ℤ) 1 (by omega)
      simpa [show 2 * (2 * k + 1) = 4 * k + 2 by omega] using this
    have hr : cell 390 (4 * k + 2) ((4 * k : ℤ) + 1) 1 = false := by
      rw [show (4 * k : ℤ) + 1 = ((4 * k + 2 - 1 : ℕ) : ℤ) by omega,
        cell_diag1 (4 * k + 2) (by omega)]
      simp [show (4 * k + 2) % 2 = 0 by omega]
    have hl : cell 390 (4 * k + 2) ((4 * k : ℤ) - 1) 1 = false := by
      rw [show (4 * k : ℤ) - 1 = ((4 * k - 1 : ℕ) : ℤ) by omega]; exact h2wing
    have hu : cell 390 (4 * k + 2) (4 * k : ℤ) (1 + 1) = true := by
      rw [show (1 : ℤ) + 1 = 2 by decide, show (4 * k : ℤ) = ((4 * k + 2 - 2 : ℕ) : ℤ) by omega,
        cell_diag2 (4 * k + 2) (by omega)]
      simp [show (4 * k + 2) % 4 = 2 by omega]
    have hd : cell 390 (4 * k + 2) (4 * k : ℤ) (1 - 1) = false := by
      rw [show (1 : ℤ) - 1 = 0 by decide, hx2]; simp only [decide_eq_false_iff_not]; omega
    rw [hc, hr, hl, hu, hd]; decide
  -- Step 4*k + 3 -> 4*k + 4
  have hx4 : ∀ i : ℤ, cell 390 (4 * (k + 1)) i 0 = decide (i.natAbs = 4 * (k + 1)) := by
    have := step_odd_to_even (2 * k + 1) (by omega)
      (by simpa [show 2 * (2 * k + 1) = 4 * k + 2 by omega,
        show 4 * k + 2 - 1 = 4 * k + 1 by omega, show 4 * k + 2 + 1 = 4 * k + 3 by omega] using hx3)
      (by simpa [show 2 * (2 * k + 1) = 4 * k + 2 by omega] using h3a)
      (by simpa [show 2 * (2 * k + 1) = 4 * k + 2 by omega, show 4 * k + 2 - 2 = 4 * k by omega] using h3b)
    simpa [show 2 * (2 * k + 1) + 2 = 4 * (k + 1) by omega] using this
  -- Compute (4*k + 1, 1) at 4*(k + 1) -> true!
  have hwing4 : cell 390 (4 * (k + 1)) ((4 * (k + 1) - 3 : ℕ) : ℤ) 1 = true := by
    rw [show 4 * (k + 1) - 3 = 4 * k + 1 by omega,
      show 4 * (k + 1) = (4 * k + 3) + 1 by omega, cell_succ_eq]
    have hc : cell 390 (4 * k + 3) ((4 * k + 1 : ℕ) : ℤ) 1 = false := by
      have hcb := (cell_checkerboard (2 * k + 1)).2 ((4 * k + 1 : ℕ) : ℤ) 1 (by omega)
      rw [show 2 * (2 * k + 1) = 4 * k + 2 by omega] at hcb
      rw [hcb, show 4 * k + 1 = 4 * k + 2 - 1 by omega, cell_diag1 (4 * k + 2) (by omega)]
      simp [show (4 * k + 2) % 2 = 0 by omega]
    have hr : cell 390 (4 * k + 3) (((4 * k + 1 : ℕ) : ℤ) + 1) 1 = true := by
      rw [show (((4 * k + 1 : ℕ) : ℤ) + 1) = (2 * ((2 * k + 1 : ℕ) : ℤ)) by push_cast; omega]
      exact h3a
    have hl : cell 390 (4 * k + 3) (((4 * k + 1 : ℕ) : ℤ) - 1) 1 = true := by
      rw [show (((4 * k + 1 : ℕ) : ℤ) - 1) = (4 * k : ℤ) by omega]; exact h3b
    have hu : cell 390 (4 * k + 3) ((4 * k + 1 : ℕ) : ℤ) (1 + 1) = true := by
      rw [show (1 : ℤ) + 1 = 2 by decide, show 4 * k + 1 = (4 * k + 3) - 2 by omega,
        cell_diag2 (4 * k + 3) (by omega)]
      simp [show (4 * k + 3) % 4 = 3 by omega]
    have hd : cell 390 (4 * k + 3) ((4 * k + 1 : ℕ) : ℤ) (1 - 1) = true := by
      rw [show (1 : ℤ) - 1 = 0 by decide, hx3]; simp only [Int.natAbs_natCast]; simp
    rw [hc, hr, hl, hu, hd]; decide
  exact ⟨⟨hx4, hwing4⟩, hx1, hx2, hx3⟩

-- Compact computable bitmask-row grid for t <= 25
private def getBit (rows : List ℕ) (i j : ℕ) : Bool :=
  (rows.getD j 0).testBit i

private def nextBit (rows : List ℕ) (i j : ℕ) : Bool :=
  rule390 (getBit rows i j)
    (getBit rows (i + 1) j)
    (getBit rows (if i = 0 then 1 else i - 1) j)
    (getBit rows i (j + 1))
    (getBit rows i (if j = 0 then 1 else j - 1))

private def buildBits (rows : List ℕ) (j : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => (if nextBit rows m j then 1 <<< m else 0) ||| buildBits rows j m

private lemma testBit_buildBits (rows : List ℕ) (j m i : ℕ) :
    (buildBits rows j m).testBit i = (decide (i < m) && nextBit rows i j) := by
  induction m with
  | zero => simp [buildBits]
  | succ m ih =>
    simp only [buildBits, Nat.testBit_or, ih]
    by_cases him : i = m
    · subst him
      by_cases hnb : nextBit rows i j = true
      · simp [hnb, Nat.testBit_shiftLeft]
      · simp [hnb]
    · have hbit : (if nextBit rows m j = true then 1 <<< m else 0).testBit i = false := by
        split_ifs with h
        · rw [Nat.testBit_shiftLeft]
          by_cases hmi : m ≤ i
          · obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (show i - m ≠ 0 by omega)
            rw [hd, Nat.testBit_succ]
            simp [hmi]
          · simp [hmi]
        · simp
      rw [hbit, Bool.false_or]
      have hiff : (i < m) ↔ (i < m + 1) := by omega
      simp [hiff]

private def stepGrid (r : ℕ) (rows : List ℕ) : List ℕ :=
  (List.range (r + 1)).map fun j => buildBits rows j (r + 1 - j)

private lemma getBit_stepGrid (r : ℕ) (rows : List ℕ) (i j : ℕ) :
    getBit (stepGrid r rows) i j = (decide (i + j ≤ r) && nextBit rows i j) := by
  unfold getBit stepGrid
  by_cases hj : j < r + 1
  · have hget : ((List.range (r + 1)).map (fun j => buildBits rows j (r + 1 - j))).getD j 0 =
        buildBits rows j (r + 1 - j) := by
      simp [List.getD_eq_getElem?_getD, hj]
    rw [hget, testBit_buildBits]
    have hiff : (i < r + 1 - j) ↔ (i + j ≤ r) := by omega
    simp [hiff]
  · have hget : ((List.range (r + 1)).map (fun j => buildBits rows j (r + 1 - j))).getD j 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [hget, Nat.zero_testBit]
    have hnot : ¬ (i + j ≤ r) := by omega
    simp [hnot]

private def grid : ℕ → List ℕ
  | 0 => [1]
  | t + 1 => stepGrid (t + 1) (grid t)

private lemma cell_eq_grid_nat (t : ℕ) :
    ∀ a b : ℕ, cell 390 t (a : ℤ) (b : ℤ) = getBit (grid t) a b := by
  induction t with
  | zero =>
    intro a b
    unfold grid getBit
    cases b with
    | zero =>
      cases a with
      | zero => decide
      | succ a =>
        simp only [cell, List.getD, List.getElem?_cons_zero, Option.getD_some]
        rw [Nat.testBit_succ]
        simp only [Nat.reduceDiv, Nat.zero_testBit, decide_eq_false_iff_not]
        omega
    | succ b =>
      simp only [cell, List.getD, List.getElem?_cons_succ, List.getElem?_nil, Option.getD_none,
        Nat.zero_testBit, decide_eq_false_iff_not]
      omega
  | succ t ih =>
    intro a b
    rw [grid, getBit_stepGrid]
    by_cases hcone : a + b ≤ t + 1
    · simp only [hcone, decide_true, Bool.true_and]
      rw [cell_succ_eq]
      unfold nextBit
      have h1 : cell 390 t ((a : ℤ) + 1) (b : ℤ) = getBit (grid t) (a + 1) b := by
        simpa [Nat.cast_add] using ih (a + 1) b
      have h2 : cell 390 t ((a : ℤ) - 1) (b : ℤ) = getBit (grid t) (if a = 0 then 1 else a - 1) b := by
        cases a with
        | zero =>
          simp only [Nat.cast_zero, zero_sub, ↓reduceIte]
          rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by decide, cell_neg_left]
          exact ih 1 b
        | succ a =>
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
          rw [show ((a + 1 : ℕ) : ℤ) - 1 = (a : ℤ) by omega]
          exact ih a b
      have h3 : cell 390 t (a : ℤ) ((b : ℤ) + 1) = getBit (grid t) a (b + 1) := by
        simpa [Nat.cast_add] using ih a (b + 1)
      have h4 : cell 390 t (a : ℤ) ((b : ℤ) - 1) = getBit (grid t) a (if b = 0 then 1 else b - 1) := by
        cases b with
        | zero =>
          simp only [Nat.cast_zero, zero_sub, ↓reduceIte]
          rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by decide, cell_neg_right]
          exact ih a 1
        | succ b =>
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
          rw [show ((b + 1 : ℕ) : ℤ) - 1 = (b : ℤ) by omega]
          exact ih a b
      rw [ih a b, h1, h2, h3, h4]
    · simp only [hcone, decide_false, Bool.false_and]
      exact cell_lightcone (t + 1) (a : ℤ) (b : ℤ) (by omega)

private lemma cell_eq_grid (t : ℕ) (i j : ℤ) :
    cell 390 t i j = getBit (grid t) i.natAbs j.natAbs := by
  have hi : cell 390 t i j = cell 390 t (i.natAbs : ℤ) j := by
    by_cases h : 0 ≤ i
    · rw [Int.natAbs_of_nonneg h]
    · rw [← cell_neg_left, show -i = (i.natAbs : ℤ) by omega]
  have hj : cell 390 t (i.natAbs : ℤ) j = cell 390 t (i.natAbs : ℤ) (j.natAbs : ℤ) := by
    by_cases h : 0 ≤ j
    · rw [Int.natAbs_of_nonneg h]
    · rw [← cell_neg_right, show -j = (j.natAbs : ℤ) by omega]
  rw [hi, hj, cell_eq_grid_nat]

private def gridRow0Val (n : ℕ) : ℤ :=
  ∑ k ∈ range (n + 1), if getBit (grid n) k 0 then (2 : ℤ) ^ (n - k) else 0

private lemma a_eq_gridRow0Val (n : ℕ) : a n = gridRow0Val n := by
  unfold a gridRow0Val
  apply Finset.sum_congr rfl
  intro k _
  have h := cell_eq_grid_nat n k 0
  simp only [Nat.cast_zero] at h
  rw [h]

private def expectedA : ℕ → ℤ
  | 0 => 1 | 1 => 3 | 2 => 1 | 3 => 7 | 4 => 17 | 5 => 39 | 6 => 65 | 7 => 199
  | 8 => 65 | 9 => 455 | 10 => 1025 | 11 => 2055 | 12 => 4097 | 13 => 8199
  | 14 => 16385 | 15 => 32775 | 16 => 65537 | 17 => 131079 | 18 => 262145
  | 19 => 524295 | 20 => 1048577 | 21 => 2097159 | 22 => 4194305 | 23 => 12582919
  | 24 => 1 | 25 => 7 | _ => 0

set_option maxHeartbeats 800000 in
private lemma grid_base_24 :
    (grid 24).getD 0 0 = 2 ^ 24 ∧ getBit (grid 24) 21 1 = true := by
  decide +kernel

set_option maxHeartbeats 800000 in
private lemma grid_small_vals :
    ∀ n : Fin 26, gridRow0Val n.val = expectedA n.val := by
  decide +kernel

private lemma inv_base_6 : Inv 6 := by
  obtain ⟨hrow0, hwing⟩ := grid_base_24
  refine ⟨?_, ?_⟩
  · intro i
    rw [show 4 * 6 = 24 by decide, cell_eq_grid 24 i 0]
    unfold getBit
    simp only [Int.natAbs_zero, hrow0, Nat.testBit_two_pow]
    simp [eq_comm]
  · rw [show 4 * 6 = 24 by decide, show 24 - 3 = 21 by decide]
    have h := cell_eq_grid_nat 24 21 1
    simp only [Nat.cast_one] at h
    rw [h]
    exact hwing

private lemma inv_all (k : ℕ) (hk : 6 ≤ k) : Inv k := by
  induction k, hk using Nat.le_induction with
  | base => exact inv_base_6
  | succ k hk ih => exact (step_four k (by omega) ih).1

private lemma a_of_even_ge_24 (m : ℕ) (hm : 12 ≤ m) : a (2 * m) = 1 := by
  have hx : ∀ i : ℤ, cell 390 (2 * m) i 0 = decide (i.natAbs = 2 * m) := by
    by_cases hpar : m % 2 = 0
    · obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
      simpa [show 2 * (2 * k) = 4 * k by omega] using (inv_all k (by omega)).1
    · obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
      have hst := step_four k (by omega) (inv_all k (by omega))
      simpa [show 2 * (2 * k + 1) = 4 * k + 2 by omega] using hst.2.2.1
  unfold a
  rw [Finset.sum_eq_single (2 * m)]
  · rw [hx ((2 * m : ℕ) : ℤ)]
    simp only [Int.natAbs_natCast, decide_true, ↓reduceIte, Nat.sub_self, pow_zero]
  · intro k hk hne
    rw [hx (k : ℤ)]; simp only [Int.natAbs_natCast, decide_eq_false hne, Bool.false_eq_true, ↓reduceIte]
  · intro hnot; exact absurd (mem_range.mpr (by omega)) hnot

private lemma a_of_odd_ge_25 (m : ℕ) (hm : 12 ≤ m) : a (2 * m + 1) = 7 := by
  have hx : ∀ i : ℤ, cell 390 (2 * m + 1) i 0 =
      decide (i.natAbs = 2 * m - 1 ∨ i.natAbs = 2 * m ∨ i.natAbs = 2 * m + 1) := by
    by_cases hpar : m % 2 = 0
    · obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
      have hst := step_four k (by omega) (inv_all k (by omega))
      simpa [show 2 * (2 * k) = 4 * k by omega] using hst.2.1
    · obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
      have hst := step_four k (by omega) (inv_all k (by omega))
      simpa [show 2 * (2 * k + 1) = 4 * k + 2 by omega,
        show 4 * k + 2 - 1 = 4 * k + 1 by omega,
        show 4 * k + 2 + 1 = 4 * k + 3 by omega] using hst.2.2.2
  unfold a
  have hsub : ({2 * m - 1, 2 * m, 2 * m + 1} : Finset ℕ) ⊆ range (2 * m + 1 + 1) := by
    intro k hk; simp only [mem_insert, mem_singleton] at hk; rw [mem_range]; omega
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_insert (by simp only [mem_insert, mem_singleton]; omega),
      Finset.sum_insert (by simp only [mem_singleton]; omega),
      Finset.sum_singleton, hx, hx, hx]
    simp only [Int.natAbs_natCast]
    rw [if_pos (by simp), if_pos (by simp), if_pos (by simp),
      show 2 * m + 1 - (2 * m - 1) = 2 by omega,
      show 2 * m + 1 - 2 * m = 1 by omega,
      show 2 * m + 1 - (2 * m + 1) = 0 by omega]
    norm_num
  · intro k hk hnot
    simp only [mem_insert, mem_singleton, not_or] at hnot
    rw [hx (k : ℤ)]
    have hne : ¬ (k = 2 * m - 1 ∨ k = 2 * m ∨ k = 2 * m + 1) := by omega
    simp [hne]

private lemma a_ge_24 (n : ℕ) (hn : 24 ≤ n) : a n = if n % 2 = 0 then 1 else 7 := by
  by_cases he : n % 2 = 0
  · rw [if_pos he, show n = 2 * (n / 2) by omega]
    exact a_of_even_ge_24 (n / 2) (by omega)
  · rw [if_neg he, show n = 2 * (n / 2) + 1 by omega]
    exact a_of_odd_ge_25 (n / 2) (by omega)

private lemma a_period_two (n : ℕ) (hn : 26 ≤ n) : (a n : ℚ) = (a (n - 2) : ℚ) := by
  rw [a_ge_24 n (by omega), a_ge_24 (n - 2) (by omega), show (n - 2) % 2 = n % 2 by omega]

private lemma a_small (n : ℕ) (hn : n < 26) : a n = expectedA n := by
  rw [a_eq_gridRow0Val]
  exact grid_small_vals ⟨n, hn⟩

private lemma coeff_mul_X_sq_sub_one (F : PowerSeries ℚ) (k : ℕ) :
    coeff k (F * (X ^ 2 - 1 : PowerSeries ℚ)) =
      (if 2 ≤ k then coeff (k - 2) F else 0) - coeff k F := by
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow']

private def rhsCoeff : ℕ → ℤ
  | 0 => -1 | 1 => -3 | 2 => 0 | 3 => -4 | 4 => -16 | 5 => -32 | 6 => -48
  | 7 => -160 | 8 => 0 | 9 => -256 | 10 => -960 | 11 => -1600 | 12 => -3072
  | 13 => -6144 | 14 => -12288 | 15 => -24576 | 16 => -49152 | 17 => -98304
  | 18 => -196608 | 19 => -393216 | 20 => -786432 | 21 => -1572864
  | 22 => -3145728 | 23 => -10485760 | 24 => 4194304 | 25 => 12582912
  | _ => 0

private lemma expectedA_diff_eq_rhsCoeff :
    ∀ k : Fin 26, (if 2 ≤ k.val then expectedA (k.val - 2) else 0) - expectedA k.val =
      rhsCoeff k.val := by
  decide

private lemma rhs_eq_sum :
    (12582912 * X ^ 25 + 4194304 * X ^ 24 - 10485760 * X ^ 23 - 3145728 * X ^ 22 -
      1572864 * X ^ 21 - 786432 * X ^ 20 - 393216 * X ^ 19 - 196608 * X ^ 18 -
      98304 * X ^ 17 - 49152 * X ^ 16 - 24576 * X ^ 15 - 12288 * X ^ 14 -
      6144 * X ^ 13 - 3072 * X ^ 12 - 1600 * X ^ 11 - 960 * X ^ 10 -
      256 * X ^ 9 - 160 * X ^ 7 - 48 * X ^ 6 - 32 * X ^ 5 - 16 * X ^ 4 -
      4 * X ^ 3 - 3 * X - 1 : PowerSeries ℚ) =
      ∑ i ∈ range 26, C (rhsCoeff i : ℚ) * (X : PowerSeries ℚ) ^ i := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, rhsCoeff,
    Int.cast_neg, Int.cast_ofNat, Int.cast_zero, Int.cast_one, map_neg, map_ofNat,
    map_zero, map_one]
  ring

private lemma gf_identity :
    PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 2 - 1 : PowerSeries ℚ) =
      12582912 * X ^ 25 + 4194304 * X ^ 24 - 10485760 * X ^ 23 - 3145728 * X ^ 22 -
      1572864 * X ^ 21 - 786432 * X ^ 20 - 393216 * X ^ 19 - 196608 * X ^ 18 -
      98304 * X ^ 17 - 49152 * X ^ 16 - 24576 * X ^ 15 - 12288 * X ^ 14 -
      6144 * X ^ 13 - 3072 * X ^ 12 - 1600 * X ^ 11 - 960 * X ^ 10 -
      256 * X ^ 9 - 160 * X ^ 7 - 48 * X ^ 6 - 32 * X ^ 5 - 16 * X ^ 4 -
      4 * X ^ 3 - 3 * X - 1 := by
  rw [rhs_eq_sum]
  ext k
  rw [coeff_mul_X_sq_sub_one, map_sum]
  have hsum : ∑ i ∈ range 26, coeff k (C (rhsCoeff i : ℚ) * (X : PowerSeries ℚ) ^ i) =
      if k < 26 then (rhsCoeff k : ℚ) else 0 := by
    have hpt : ∀ i ∈ range 26,
        coeff k (C (rhsCoeff i : ℚ) * (X : PowerSeries ℚ) ^ i) =
        if k = i then (rhsCoeff i : ℚ) else 0 := by
      intro i _
      rw [coeff_C_mul, coeff_X_pow]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hpt]
    by_cases hk : k < 26
    · rw [if_pos hk, Finset.sum_eq_single k]
      · simp
      · intro i _ hne; simp [Ne.symm hne]
      · intro hnot; exact absurd (mem_range.mpr hk) hnot
    · rw [if_neg hk]
      apply Finset.sum_eq_zero
      intro i hi
      rw [mem_range] at hi
      rw [if_neg (by omega)]
  rw [hsum]
  simp only [coeff_mk]
  by_cases hk : k < 26
  · rw [if_pos hk, a_small k hk]
    have hdiff := expectedA_diff_eq_rhsCoeff ⟨k, hk⟩
    by_cases hk2 : 2 ≤ k
    · rw [if_pos hk2, a_small (k - 2) (by omega)]
      simp only [hk2, ↓reduceIte] at hdiff
      exact_mod_cast hdiff
    · rw [if_neg hk2]
      simp only [hk2, ↓reduceIte] at hdiff
      exact_mod_cast hdiff
  · rw [if_neg hk, if_pos (by omega : 2 ≤ k), a_period_two k (by omega), sub_self]

end OMA.Proof_oeis_a281738

theorem OMA.solution : type_of% @OMA.S_oeis_a281738.main :=
  ⟨OMA.Proof_oeis_a281738.a_period_two, OMA.Proof_oeis_a281738.gf_identity⟩

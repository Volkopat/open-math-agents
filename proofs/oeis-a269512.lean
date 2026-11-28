import OMAStatements.S_oeis_a269512

-- Problem: A269512: First differences of number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by Rule 342, based on the 5-celled von Neumann neighborhood.
-- Credit: @Qwer2077 (the owner of the agent is credited as the solver)

open OMA.S_oeis_a269512 PowerSeries

namespace OMA.Proof_oeis_a269512

-- ============================================================================
-- Section 1: Exact radial closed form for Rule 342 for all t >= 0
-- ============================================================================

private def f342 (t : ℕ) (x y : ℤ) : Bool :=
  let d := |x| + |y|
  if (t : ℤ) < d then false
  else if t % 2 = 0 then decide (((t : ℤ) - d) % 4 = 0)
  else decide (((t : ℤ) - d) % 4 ≠ 3)

private def rule342 (cur : Bool) (s : ℕ) : Bool :=
  (342 : ℕ).testBit (cur.toNat + 2 * s)

private lemma rule342_eval (cur : Bool) (s : ℕ) (hs : s ≤ 4) :
    (cur = true → rule342 true s = decide (s = 0)) ∧
    (cur = false → rule342 false s = decide (1 ≤ s)) := by
  cases cur <;> interval_cases s <;> decide

private lemma nbr_dist_bounds (x y : ℤ) :
    let d := |x| + |y|
    (|x + 1| + |y| = d + 1 ∨ |x + 1| + |y| = d - 1) ∧
    (|x - 1| + |y| = d + 1 ∨ |x - 1| + |y| = d - 1) ∧
    (|x| + |y + 1| = d + 1 ∨ |x| + |y + 1| = d - 1) ∧
    (|x| + |y - 1| = d + 1 ∨ |x| + |y - 1| = d - 1) := by
  dsimp only
  simp only [abs_eq_max_neg]
  refine ⟨by omega, by omega, by omega, by omega⟩

private lemma nbr_cnt_exact (x y : ℤ) (hd : 1 ≤ |x| + |y|) :
    let d := |x| + |y|
    let nPlus := (if |x + 1| + |y| = d + 1 then 1 else 0) +
                 (if |x - 1| + |y| = d + 1 then 1 else 0) +
                 (if |x| + |y + 1| = d + 1 then 1 else 0) +
                 (if |x| + |y - 1| = d + 1 then 1 else 0)
    let nMinus := (if |x + 1| + |y| = d - 1 then 1 else 0) +
                  (if |x - 1| + |y| = d - 1 then 1 else 0) +
                  (if |x| + |y + 1| = d - 1 then 1 else 0) +
                  (if |x| + |y - 1| = d - 1 then 1 else 0)
    (nPlus = 2 ∧ nMinus = 2) ∨ (nPlus = 3 ∧ nMinus = 1) := by
  dsimp only
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> rcases lt_trichotomy y 0 with hy | rfl | hy
  · left
    rw [abs_of_neg hx, abs_of_neg hy, abs_of_neg (by omega : x - 1 < 0),
        abs_of_nonpos (by omega : x + 1 ≤ 0), abs_of_neg (by omega : y - 1 < 0),
        abs_of_nonpos (by omega : y + 1 ≤ 0)]
    split_ifs <;> omega
  · right
    rw [abs_of_neg hx, abs_zero, abs_of_neg (by omega : x - 1 < 0),
        abs_of_nonpos (by omega : x + 1 ≤ 0)]
    norm_num; split_ifs <;> omega
  · left
    rw [abs_of_neg hx, abs_of_pos hy, abs_of_neg (by omega : x - 1 < 0),
        abs_of_nonpos (by omega : x + 1 ≤ 0), abs_of_nonneg (by omega : 0 ≤ y - 1),
        abs_of_pos (by omega : 0 < y + 1)]
    split_ifs <;> omega
  · right
    rw [abs_zero, abs_of_neg hy, abs_of_neg (by omega : y - 1 < 0),
        abs_of_nonpos (by omega : y + 1 ≤ 0)]
    norm_num; split_ifs <;> omega
  · simp at hd
  · right
    rw [abs_zero, abs_of_pos hy, abs_of_nonneg (by omega : 0 ≤ y - 1),
        abs_of_pos (by omega : 0 < y + 1)]
    norm_num; split_ifs <;> omega
  · left
    rw [abs_of_pos hx, abs_of_neg hy, abs_of_nonneg (by omega : 0 ≤ x - 1),
        abs_of_pos (by omega : 0 < x + 1), abs_of_neg (by omega : y - 1 < 0),
        abs_of_nonpos (by omega : y + 1 ≤ 0)]
    split_ifs <;> omega
  · right
    rw [abs_of_pos hx, abs_zero, abs_of_nonneg (by omega : 0 ≤ x - 1),
        abs_of_pos (by omega : 0 < x + 1)]
    norm_num; split_ifs <;> omega
  · left
    rw [abs_of_pos hx, abs_of_pos hy, abs_of_nonneg (by omega : 0 ≤ x - 1),
        abs_of_pos (by omega : 0 < x + 1), abs_of_nonneg (by omega : 0 ≤ y - 1),
        abs_of_pos (by omega : 0 < y + 1)]
    split_ifs <;> omega

private lemma f342_val_by_dist (t : ℕ) (x y : ℤ) (d : ℤ) (hd : |x| + |y| = d) :
    f342 t x y =
      if (t : ℤ) < d then false
      else if t % 2 = 0 then decide (((t : ℤ) - d) % 4 = 0)
      else decide (((t : ℤ) - d) % 4 ≠ 3) := by
  unfold f342; dsimp only; rw [hd]

private lemma cell_342_eq_f342 (t : ℕ) (x y : ℤ) : cell 342 t x y = f342 t x y := by
  induction t generalizing x y with
  | zero =>
    unfold f342; dsimp only
    by_cases h : (0 : ℤ) < |x| + |y|
    · rw [if_pos (by exact_mod_cast h)]
      simp only [cell, decide_eq_false_iff_not]
      rintro ⟨rfl, rfl⟩; simp at h
    · have hx : x = 0 := by simp only [abs_eq_max_neg] at h; omega
      have hy : y = 0 := by simp only [abs_eq_max_neg] at h; omega
      subst hx hy; decide
  | succ t ih =>
    change rule342 (cell 342 t x y)
      ((cell 342 t (x + 1) y).toNat + (cell 342 t (x - 1) y).toNat +
       (cell 342 t x (y + 1)).toNat + (cell 342 t x (y - 1)).toNat) = f342 (t + 1) x y
    rw [ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y + 1), ih x (y - 1)]
    set d := |x| + |y| with hd_def
    have hd0 : 0 ≤ d := by positivity
    by_cases h0 : d = 0
    · have hx0 : x = 0 := by rw [hd_def] at h0; simp only [abs_eq_max_neg] at h0; omega
      have hy0 : y = 0 := by rw [hd_def] at h0; simp only [abs_eq_max_neg] at h0; omega
      subst hx0 hy0
      simp only [zero_add, zero_sub]
      by_cases ht0 : t = 0
      · subst ht0; decide
      · have hnbr : ∀ a b : ℤ, |a| + |b| = 1 →
            f342 t a b = if t % 2 = 0 then decide (((t : ℤ) - 1) % 4 = 0)
                         else decide (((t : ℤ) - 1) % 4 ≠ 3) := by
          intro a b hab
          rw [f342_val_by_dist t a b 1 hab, if_neg (by omega)]
        have hC : f342 t 0 0 =
            if t % 2 = 0 then decide (((t : ℤ) - 0) % 4 = 0)
            else decide (((t : ℤ) - 0) % 4 ≠ 3) := by
          rw [f342_val_by_dist t 0 0 0 (by simp), if_neg (by omega)]
        have hT : f342 (t + 1) 0 0 =
            if (t + 1) % 2 = 0 then decide ((((t + 1 : ℕ) : ℤ) - 0) % 4 = 0)
            else decide ((((t + 1 : ℕ) : ℤ) - 0) % 4 ≠ 3) := by
          rw [f342_val_by_dist (t + 1) 0 0 0 (by simp), if_neg (by push_cast; omega)]
        rw [hnbr 1 0 (by simp), hnbr (-1) 0 (by simp), hnbr 0 1 (by simp), hnbr 0 (-1) (by simp),
            hC, hT]
        set rt := t % 4
        have hrt : rt < 4 := Nat.mod_lt t (by omega)
        have hm2 : t % 2 = rt % 2 := by omega
        have hm2' : (t + 1) % 2 = (rt + 1) % 2 := by omega
        have hm0 : ((t : ℤ) - 0) % 4 = (rt : ℤ) := by omega
        have hm1 : ((t : ℤ) - 1) % 4 = ((rt + 3) % 4 : ℕ) := by omega
        have hm1' : (((t + 1 : ℕ) : ℤ) - 0) % 4 = ((rt + 1) % 4 : ℕ) := by push_cast; omega
        rw [hm2, hm2', hm0, hm1, hm1']
        interval_cases rt <;> decide
    · have hd1 : 1 ≤ d := by omega
      obtain ⟨hb1, hb2, hb3, hb4⟩ := nbr_dist_bounds x y
      have hcnt := nbr_cnt_exact x y hd1
      set vPlus : Bool :=
        if (t : ℤ) < d + 1 then false
        else if t % 2 = 0 then decide (((t : ℤ) - (d + 1)) % 4 = 0)
        else decide (((t : ℤ) - (d + 1)) % 4 ≠ 3)
      set vMinus : Bool :=
        if (t : ℤ) < d - 1 then false
        else if t % 2 = 0 then decide (((t : ℤ) - (d - 1)) % 4 = 0)
        else decide (((t : ℤ) - (d - 1)) % 4 ≠ 3)
      have hval : ∀ a b : ℤ, (|a| + |b| = d + 1 ∨ |a| + |b| = d - 1) →
          (f342 t a b).toNat =
            (if |a| + |b| = d + 1 then 1 else 0) * vPlus.toNat +
            (if |a| + |b| = d - 1 then 1 else 0) * vMinus.toNat := by
        intro a b hab
        rcases hab with h | h
        · have hne : |a| + |b| ≠ d - 1 := by omega
          rw [if_pos h, if_neg hne, one_mul, zero_mul, add_zero]
          exact congrArg Bool.toNat (f342_val_by_dist t a b (d + 1) h)
        · have hne : |a| + |b| ≠ d + 1 := by omega
          rw [if_neg hne, if_pos h, zero_mul, one_mul, zero_add]
          exact congrArg Bool.toNat (f342_val_by_dist t a b (d - 1) h)
      have hs_eq : (f342 t (x + 1) y).toNat + (f342 t (x - 1) y).toNat +
          (f342 t x (y + 1)).toNat + (f342 t x (y - 1)).toNat =
          ((if |x + 1| + |y| = d + 1 then 1 else 0) + (if |x - 1| + |y| = d + 1 then 1 else 0) +
           (if |x| + |y + 1| = d + 1 then 1 else 0) + (if |x| + |y - 1| = d + 1 then 1 else 0)) * vPlus.toNat +
          ((if |x + 1| + |y| = d - 1 then 1 else 0) + (if |x - 1| + |y| = d - 1 then 1 else 0) +
           (if |x| + |y + 1| = d - 1 then 1 else 0) + (if |x| + |y - 1| = d - 1 then 1 else 0)) * vMinus.toNat := by
        rw [hval _ _ hb1, hval _ _ hb2, hval _ _ hb3, hval _ _ hb4]
        ring
      rw [hs_eq]
      set nP := (if |x + 1| + |y| = d + 1 then 1 else 0) + (if |x - 1| + |y| = d + 1 then 1 else 0) +
                (if |x| + |y + 1| = d + 1 then 1 else 0) + (if |x| + |y - 1| = d + 1 then 1 else 0)
      set nM := (if |x + 1| + |y| = d - 1 then 1 else 0) + (if |x - 1| + |y| = d - 1 then 1 else 0) +
                (if |x| + |y + 1| = d - 1 then 1 else 0) + (if |x| + |y - 1| = d - 1 then 1 else 0)
      have hcases : (nP = 2 ∧ nM = 2) ∨ (nP = 3 ∧ nM = 1) := hcnt
      by_cases hgt1 : (t : ℤ) + 1 < d
      · have hC : f342 t x y = false := by rw [f342_val_by_dist t x y d rfl, if_pos (by omega)]
        have hP : vPlus = false := by simp only [vPlus]; rw [if_pos (by omega)]
        have hM : vMinus = false := by simp only [vMinus]; rw [if_pos (by omega)]
        have hT : f342 (t + 1) x y = false := by
          rw [f342_val_by_dist (t + 1) x y d rfl, if_pos (by push_cast; omega)]
        rw [hC, hP, hM, hT]
        rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
      · by_cases heq1 : d = (t : ℤ) + 1
        · have hC : f342 t x y = false := by rw [f342_val_by_dist t x y d rfl, if_pos (by omega)]
          have hP : vPlus = false := by simp only [vPlus]; rw [if_pos (by omega)]
          have hM : vMinus = true := by
            simp only [vMinus]; rw [if_neg (by omega)]
            split_ifs <;> (rw [decide_eq_true_eq]; omega)
          have hT : f342 (t + 1) x y = true := by
            rw [f342_val_by_dist (t + 1) x y d rfl, if_neg (by push_cast; omega)]
            split_ifs <;> (rw [decide_eq_true_eq]; push_cast; omega)
          rw [hC, hP, hM, hT]
          rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
        · by_cases heq0 : d = (t : ℤ)
          · have hC : f342 t x y = true := by
              rw [f342_val_by_dist t x y d rfl, if_neg (by omega)]
              split_ifs <;> (rw [decide_eq_true_eq]; omega)
            have hP : vPlus = false := by simp only [vPlus]; rw [if_pos (by omega)]
            by_cases hte : t % 2 = 0
            · have hM : vMinus = false := by
                simp only [vMinus]; rw [if_neg (by omega), if_pos hte, decide_eq_false_iff_not]; omega
              have hT : f342 (t + 1) x y = true := by
                rw [f342_val_by_dist (t + 1) x y d rfl, if_neg (by push_cast; omega),
                    if_neg (by omega), decide_eq_true_eq]; push_cast; omega
              rw [hC, hP, hM, hT]
              rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
            · have hM : vMinus = true := by
                simp only [vMinus]; rw [if_neg (by omega), if_neg hte, decide_eq_true_eq]; omega
              have hT : f342 (t + 1) x y = false := by
                rw [f342_val_by_dist (t + 1) x y d rfl, if_neg (by push_cast; omega),
                    if_pos (by omega), decide_eq_false_iff_not]; push_cast; omega
              rw [hC, hP, hM, hT]
              rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
          · -- d < t: all of d, d+1, d-1 are <= t
            have hlt : d < (t : ℤ) := by omega
            have hC : f342 t x y = if t % 2 = 0 then decide (((t : ℤ) - d) % 4 = 0)
                                   else decide (((t : ℤ) - d) % 4 ≠ 3) := by
              rw [f342_val_by_dist t x y d rfl, if_neg (by omega)]
            have hP : vPlus = if t % 2 = 0 then decide (((t : ℤ) - (d + 1)) % 4 = 0)
                              else decide (((t : ℤ) - (d + 1)) % 4 ≠ 3) := by
              simp only [vPlus]; rw [if_neg (by omega)]
            have hM : vMinus = if t % 2 = 0 then decide (((t : ℤ) - (d - 1)) % 4 = 0)
                               else decide (((t : ℤ) - (d - 1)) % 4 ≠ 3) := by
              simp only [vMinus]; rw [if_neg (by omega)]
            have hT : f342 (t + 1) x y =
                if (t + 1) % 2 = 0 then decide ((((t + 1 : ℕ) : ℤ) - d) % 4 = 0)
                else decide ((((t + 1 : ℕ) : ℤ) - d) % 4 ≠ 3) := by
              rw [f342_val_by_dist (t + 1) x y d rfl, if_neg (by push_cast; omega)]
            rw [hC, hP, hM, hT]
            set r := (((t : ℤ) - d) % 4).toNat
            have hr : r < 4 := by omega
            have hrz : ((t : ℤ) - d) % 4 = (r : ℤ) := by omega
            have hrP : ((t : ℤ) - (d + 1)) % 4 = (((r + 3) % 4 : ℕ) : ℤ) := by omega
            have hrM : ((t : ℤ) - (d - 1)) % 4 = (((r + 1) % 4 : ℕ) : ℤ) := by omega
            have hrT : (((t + 1 : ℕ) : ℤ) - d) % 4 = (((r + 1) % 4 : ℕ) : ℤ) := by push_cast; omega
            rw [hrz, hrP, hrM, hrT]
            by_cases hte : t % 2 = 0
            · have hto : (t + 1) % 2 ≠ 0 := by omega
              simp only [hte, hto, ite_true, ite_false]
              rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (rw [h1, h2]; interval_cases r <;> decide)
            · have hto : (t + 1) % 2 = 0 := by omega
              simp only [hte, hto, ite_true, ite_false]
              rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (rw [h1, h2]; interval_cases r <;> decide)

-- ============================================================================
-- Section 2: Shell counting and exact closed form for onCount 342 t
-- ============================================================================

private noncomputable def box (B : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(B : ℤ)) (B : ℤ) ×ˢ Finset.Icc (-(B : ℤ)) (B : ℤ)

private lemma box_mem_iff (B : ℕ) (p : ℤ × ℤ) :
    p ∈ box B ↔ -(B : ℤ) ≤ p.1 ∧ p.1 ≤ (B : ℤ) ∧ -(B : ℤ) ≤ p.2 ∧ p.2 ≤ (B : ℤ) := by
  simp [box, Finset.mem_product, Finset.mem_Icc, and_assoc]

private lemma onCount_eq_box_card (t : ℕ) :
    onCount 342 t = ((box t).filter (fun p => f342 t p.1 p.2 = true)).card := by
  unfold onCount
  rw [Finset.card_filter, ← Finset.sum_product']
  refine Finset.sum_bij (fun p _ => ((p.1 : ℤ) - (t : ℤ), (p.2 : ℤ) - (t : ℤ))) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    rw [box_mem_iff]; omega
  · intro p1 _ p2 _ h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact Prod.ext (by omega) (by omega)
  · intro q hq
    rw [box_mem_iff] at hq
    refine ⟨((q.1 + (t : ℤ)).toNat, (q.2 + (t : ℤ)).toNat), ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]; omega
    · exact Prod.ext (by omega) (by omega)
  · intro p _
    simp only [cell_342_eq_f342]

private lemma shell_card (B d : ℕ) (hd : 1 ≤ d) (hdB : d ≤ B) :
    ((box B).filter (fun p => |p.1| + |p.2| = (d : ℤ))).card = 4 * d := by
  rw [Finset.card_filter]
  have hsplit : (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) then 1 else 0) =
      (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) ∧ 0 < p.1 ∧ 0 ≤ p.2 then 1 else 0) +
      (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) ∧ p.1 ≤ 0 ∧ 0 < p.2 then 1 else 0) +
      (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) ∧ p.1 < 0 ∧ p.2 ≤ 0 then 1 else 0) +
      (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) ∧ 0 ≤ p.1 ∧ p.2 < 0 then 1 else 0) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : |p.1| + |p.2| = (d : ℤ)
    · have hne : p.1 ≠ 0 ∨ p.2 ≠ 0 := by simp only [abs_eq_max_neg] at h; omega
      split_ifs <;> omega
    · simp [h]
  have hq1 : (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) ∧ 0 < p.1 ∧ 0 ≤ p.2 then 1 else 0) = d := by
    rw [← Finset.sum_filter]
    have hc : (∑ _ ∈ Finset.range d, (1 : ℕ)) = d := by simp
    rw [← hc]
    refine Finset.sum_bij (fun p _ => p.2.toNat) ?_ ?_ ?_ ?_
    · intro p hp; rw [Finset.mem_filter] at hp; rw [Finset.mem_range]
      simp only [abs_eq_max_neg] at hp; omega
    · intro p1 hp1 p2 hp2 h; rw [Finset.mem_filter] at hp1 hp2
      have hy : p1.2 = p2.2 := by omega
      apply Prod.ext
      · simp only [abs_eq_max_neg] at hp1 hp2; omega
      · exact hy
    · intro k hk; rw [Finset.mem_range] at hk
      refine ⟨((d : ℤ) - k, k), ?_, by omega⟩
      rw [Finset.mem_filter, box_mem_iff]; simp only [abs_eq_max_neg]; omega
    · intro _ _; rfl
  have hq2 : (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) ∧ p.1 ≤ 0 ∧ 0 < p.2 then 1 else 0) = d := by
    rw [← Finset.sum_filter]
    have hc : (∑ _ ∈ Finset.range d, (1 : ℕ)) = d := by simp
    rw [← hc]
    refine Finset.sum_bij (fun p _ => (-p.1).toNat) ?_ ?_ ?_ ?_
    · intro p hp; rw [Finset.mem_filter] at hp; rw [Finset.mem_range]
      simp only [abs_eq_max_neg] at hp; omega
    · intro p1 hp1 p2 hp2 h; rw [Finset.mem_filter] at hp1 hp2
      have hx : p1.1 = p2.1 := by omega
      apply Prod.ext
      · exact hx
      · simp only [abs_eq_max_neg] at hp1 hp2; omega
    · intro k hk; rw [Finset.mem_range] at hk
      refine ⟨(-(k : ℤ), (d : ℤ) - k), ?_, by omega⟩
      rw [Finset.mem_filter, box_mem_iff]; simp only [abs_eq_max_neg]; omega
    · intro _ _; rfl
  have hq3 : (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) ∧ p.1 < 0 ∧ p.2 ≤ 0 then 1 else 0) = d := by
    rw [← Finset.sum_filter]
    have hc : (∑ _ ∈ Finset.range d, (1 : ℕ)) = d := by simp
    rw [← hc]
    refine Finset.sum_bij (fun p _ => (-p.2).toNat) ?_ ?_ ?_ ?_
    · intro p hp; rw [Finset.mem_filter] at hp; rw [Finset.mem_range]
      simp only [abs_eq_max_neg] at hp; omega
    · intro p1 hp1 p2 hp2 h; rw [Finset.mem_filter] at hp1 hp2
      have hy : p1.2 = p2.2 := by omega
      apply Prod.ext
      · simp only [abs_eq_max_neg] at hp1 hp2; omega
      · exact hy
    · intro k hk; rw [Finset.mem_range] at hk
      refine ⟨(-((d : ℤ) - k), -(k : ℤ)), ?_, by omega⟩
      rw [Finset.mem_filter, box_mem_iff]; simp only [abs_eq_max_neg]; omega
    · intro _ _; rfl
  have hq4 : (∑ p ∈ box B, if |p.1| + |p.2| = (d : ℤ) ∧ 0 ≤ p.1 ∧ p.2 < 0 then 1 else 0) = d := by
    rw [← Finset.sum_filter]
    have hc : (∑ _ ∈ Finset.range d, (1 : ℕ)) = d := by simp
    rw [← hc]
    refine Finset.sum_bij (fun p _ => p.1.toNat) ?_ ?_ ?_ ?_
    · intro p hp; rw [Finset.mem_filter] at hp; rw [Finset.mem_range]
      simp only [abs_eq_max_neg] at hp; omega
    · intro p1 hp1 p2 hp2 h; rw [Finset.mem_filter] at hp1 hp2
      have hx : p1.1 = p2.1 := by omega
      apply Prod.ext
      · exact hx
      · simp only [abs_eq_max_neg] at hp1 hp2; omega
    · intro k hk; rw [Finset.mem_range] at hk
      refine ⟨(k, -((d : ℤ) - k)), ?_, by omega⟩
      rw [Finset.mem_filter, box_mem_iff]; simp only [abs_eq_max_neg]; omega
    · intro _ _; rfl
  rw [hsplit, hq1, hq2, hq3, hq4]
  omega

private lemma origin_card (B : ℕ) :
    ((box B).filter (fun p => |p.1| + |p.2| = (0 : ℤ))).card = 1 := by
  have hEq : (box B).filter (fun p => |p.1| + |p.2| = (0 : ℤ)) = {(0, 0)} := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq, box_mem_iff]
    constructor
    · rintro ⟨_, h0⟩; simp only [abs_eq_max_neg] at h0; omega
    · rintro ⟨rfl, rfl⟩; refine ⟨by omega, by simp⟩
  rw [hEq, Finset.card_singleton]

private lemma card_le (B t : ℕ) (ht : t ≤ B) :
    ((box B).filter (fun p => |p.1| + |p.2| ≤ (t : ℤ))).card = 2 * t * t + 2 * t + 1 := by
  induction t with
  | zero =>
    have hEq : (box B).filter (fun p => |p.1| + |p.2| ≤ ((0 : ℕ) : ℤ)) =
        (box B).filter (fun p => |p.1| + |p.2| = (0 : ℤ)) := by
      ext p; have h1 := abs_nonneg p.1; have h2 := abs_nonneg p.2
      simp only [Finset.mem_filter, Nat.cast_zero]; constructor
      · rintro ⟨hp, hle⟩; exact ⟨hp, by omega⟩
      · rintro ⟨hp, heq⟩; exact ⟨hp, by omega⟩
    rw [hEq, origin_card B]
  | succ t ih =>
    have hsplit : (box B).filter (fun p => |p.1| + |p.2| ≤ ((t + 1 : ℕ) : ℤ)) =
        (box B).filter (fun p => |p.1| + |p.2| ≤ (t : ℤ)) ∪
        (box B).filter (fun p => |p.1| + |p.2| = ((t + 1 : ℕ) : ℤ)) := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter]; constructor
      · rintro ⟨hp, hle⟩
        by_cases h : |p.1| + |p.2| ≤ (t : ℤ)
        · left; exact ⟨hp, h⟩
        · right; exact ⟨hp, by push_cast at hle; omega⟩
      · rintro (⟨hp, hle⟩ | ⟨hp, heq⟩)
        · exact ⟨hp, by push_cast; omega⟩
        · exact ⟨hp, by omega⟩
    have hdisj : Disjoint
        ((box B).filter (fun p => |p.1| + |p.2| ≤ (t : ℤ)))
        ((box B).filter (fun p => |p.1| + |p.2| = ((t + 1 : ℕ) : ℤ))) := by
      rw [Finset.disjoint_filter]; intro p _ h1 h2; push_cast at h2; omega
    rw [hsplit, Finset.card_union_of_disjoint hdisj, ih (by omega),
        shell_card B (t + 1) (by omega) ht]
    ring

private lemma card_mod4_0 (B q : ℕ) (hq : 4 * q ≤ B) :
    ((box B).filter (fun p => |p.1| + |p.2| ≤ (4 * q : ℤ) ∧ (|p.1| + |p.2|) % 4 = 0)).card =
      8 * q * q + 8 * q + 1 := by
  induction q with
  | zero =>
    have hEq : (box B).filter (fun p => |p.1| + |p.2| ≤ (4 * (0 : ℕ) : ℤ) ∧ (|p.1| + |p.2|) % 4 = 0) =
        (box B).filter (fun p => |p.1| + |p.2| = (0 : ℤ)) := by
      ext p; have h1 := abs_nonneg p.1; have h2 := abs_nonneg p.2
      simp only [Finset.mem_filter, Nat.cast_zero, mul_zero]; constructor
      · rintro ⟨hp, hle, _⟩; exact ⟨hp, by omega⟩
      · rintro ⟨hp, heq⟩; exact ⟨hp, by omega, by omega⟩
    rw [hEq, origin_card B]
  | succ q ih =>
    have hsplit : (box B).filter (fun p => |p.1| + |p.2| ≤ (4 * ((q + 1 : ℕ) : ℤ)) ∧ (|p.1| + |p.2|) % 4 = 0) =
        (box B).filter (fun p => |p.1| + |p.2| ≤ (4 * (q : ℤ)) ∧ (|p.1| + |p.2|) % 4 = 0) ∪
        (box B).filter (fun p => |p.1| + |p.2| = ((4 * (q + 1) : ℕ) : ℤ)) := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter]; constructor
      · rintro ⟨hp, hle, hpar⟩
        by_cases h : |p.1| + |p.2| ≤ 4 * (q : ℤ)
        · left; exact ⟨hp, h, hpar⟩
        · right; exact ⟨hp, by push_cast at hle ⊢; omega⟩
      · rintro (⟨hp, hle, hpar⟩ | ⟨hp, heq⟩)
        · exact ⟨hp, by push_cast; omega, hpar⟩
        · exact ⟨hp, by push_cast at heq ⊢; omega, by push_cast at heq; omega⟩
    have hdisj : Disjoint
        ((box B).filter (fun p => |p.1| + |p.2| ≤ (4 * (q : ℤ)) ∧ (|p.1| + |p.2|) % 4 = 0))
        ((box B).filter (fun p => |p.1| + |p.2| = ((4 * (q + 1) : ℕ) : ℤ))) := by
      rw [Finset.disjoint_filter]; intro p _ h1 h2; push_cast at h2; omega
    rw [hsplit, Finset.card_union_of_disjoint hdisj, ih (by omega),
        shell_card B (4 * (q + 1)) (by omega) hq]
    ring

private lemma card_mod4_2 (B q : ℕ) (hq : 4 * q + 2 ≤ B) :
    ((box B).filter (fun p => |p.1| + |p.2| ≤ (4 * q + 2 : ℤ) ∧ (|p.1| + |p.2|) % 4 = 2)).card =
      8 * (q + 1) * (q + 1) := by
  induction q with
  | zero =>
    have hEq : (box B).filter (fun p => |p.1| + |p.2| ≤ (4 * (0 : ℕ) + 2 : ℤ) ∧ (|p.1| + |p.2|) % 4 = 2) =
        (box B).filter (fun p => |p.1| + |p.2| = ((2 : ℕ) : ℤ)) := by
      ext p; have h1 := abs_nonneg p.1; have h2 := abs_nonneg p.2
      simp only [Finset.mem_filter, Nat.cast_zero, mul_zero, zero_add, Nat.cast_ofNat]; constructor
      · rintro ⟨hp, hle, hpar⟩; exact ⟨hp, by omega⟩
      · rintro ⟨hp, heq⟩; exact ⟨hp, by omega, by omega⟩
    rw [hEq, shell_card B 2 (by omega) (by omega)]
  | succ q ih =>
    have hsplit : (box B).filter (fun p => |p.1| + |p.2| ≤ (4 * ((q + 1 : ℕ) : ℤ) + 2) ∧ (|p.1| + |p.2|) % 4 = 2) =
        (box B).filter (fun p => |p.1| + |p.2| ≤ (4 * (q : ℤ) + 2) ∧ (|p.1| + |p.2|) % 4 = 2) ∪
        (box B).filter (fun p => |p.1| + |p.2| = ((4 * (q + 1) + 2 : ℕ) : ℤ)) := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter]; constructor
      · rintro ⟨hp, hle, hpar⟩
        by_cases h : |p.1| + |p.2| ≤ 4 * (q : ℤ) + 2
        · left; exact ⟨hp, h, hpar⟩
        · right; exact ⟨hp, by push_cast at hle ⊢; omega⟩
      · rintro (⟨hp, hle, hpar⟩ | ⟨hp, heq⟩)
        · exact ⟨hp, by push_cast; omega, hpar⟩
        · exact ⟨hp, by push_cast at heq ⊢; omega, by push_cast at heq; omega⟩
    have hdisj : Disjoint
        ((box B).filter (fun p => |p.1| + |p.2| ≤ (4 * (q : ℤ) + 2) ∧ (|p.1| + |p.2|) % 4 = 2))
        ((box B).filter (fun p => |p.1| + |p.2| = ((4 * (q + 1) + 2 : ℕ) : ℤ))) := by
      rw [Finset.disjoint_filter]; intro p _ h1 h2; push_cast at h2; omega
    rw [hsplit, Finset.card_union_of_disjoint hdisj, ih (by omega),
        shell_card B (4 * (q + 1) + 2) (by omega) hq]
    ring

private def c342 (t : ℕ) : ℤ :=
  let q : ℤ := (t / 4 : ℕ)
  if t % 4 = 0 then 8 * q * q + 8 * q + 1
  else if t % 4 = 1 then 24 * q * q + 24 * q + 5
  else if t % 4 = 2 then 8 * (q + 1) * (q + 1)
  else 24 * (q + 1) * (q + 1)

private lemma onCount_342_eq (t : ℕ) : (onCount 342 t : ℤ) = c342 t := by
  rw [onCount_eq_box_card]
  set q := t / 4
  set r := t % 4
  have hq_def : t / 4 = q := rfl
  have hr : r < 4 := Nat.mod_lt t (by omega)
  have ht : t = 4 * q + r := by omega
  interval_cases r
  · have hEq : (box t).filter (fun p => f342 t p.1 p.2 = true) =
        (box t).filter (fun p => |p.1| + |p.2| ≤ (4 * q : ℤ) ∧ (|p.1| + |p.2|) % 4 = 0) := by
      ext p; simp only [Finset.mem_filter]; unfold f342; dsimp only
      rw [show t % 2 = 0 by omega, if_pos rfl]
      constructor
      · rintro ⟨hp, hf⟩
        by_cases h : (t : ℤ) < |p.1| + |p.2|
        · rw [if_pos h] at hf; cases hf
        · rw [if_neg h, decide_eq_true_eq] at hf
          exact ⟨hp, by omega, by omega⟩
      · rintro ⟨hp, hle, hpar⟩
        refine ⟨hp, ?_⟩
        rw [if_neg (by omega), decide_eq_true_eq]; omega
    rw [hEq, card_mod4_0 t q (by omega)]
    unfold c342; dsimp only; rw [if_pos (by omega), hq_def]; push_cast; ring
  · by_cases hq0 : q = 0
    · have ht1 : t = 1 := by omega
      subst ht1
      have hEq : (box 1).filter (fun p => f342 1 p.1 p.2 = true) =
          (box 1).filter (fun p => |p.1| + |p.2| ≤ ((1 : ℕ) : ℤ)) := by
        ext p; have h1 := abs_nonneg p.1; have h2 := abs_nonneg p.2
        simp only [Finset.mem_filter]; unfold f342; dsimp only
        constructor
        · rintro ⟨hp, hf⟩
          by_cases h : ((1 : ℕ) : ℤ) < |p.1| + |p.2|
          · rw [if_pos h] at hf; cases hf
          · exact ⟨hp, by omega⟩
        · rintro ⟨hp, hle⟩
          refine ⟨hp, ?_⟩
          rw [if_neg (by omega), if_neg (by omega), decide_eq_true_eq]; push_cast at hle ⊢; omega
      rw [hEq, card_le 1 1 le_rfl]
      unfold c342; decide
    · have hsplit : (box t).filter (fun p => |p.1| + |p.2| ≤ (t : ℤ)) =
          (box t).filter (fun p => f342 t p.1 p.2 = true) ∪
          (box t).filter (fun p => |p.1| + |p.2| ≤ (4 * ((q - 1 : ℕ) : ℤ) + 2) ∧ (|p.1| + |p.2|) % 4 = 2) := by
        ext p; simp only [Finset.mem_union, Finset.mem_filter]; unfold f342; dsimp only
        rw [if_neg (show ¬ t % 2 = 0 by omega)]
        constructor
        · rintro ⟨hp, hle⟩
          by_cases hp2 : (|p.1| + |p.2|) % 4 = 2
          · right; exact ⟨hp, by omega, hp2⟩
          · left; refine ⟨hp, ?_⟩; rw [if_neg (by omega), decide_eq_true_eq]; omega
        · rintro (⟨hp, hf⟩ | ⟨hp, hle, _⟩)
          · by_cases h : (t : ℤ) < |p.1| + |p.2|
            · rw [if_pos h] at hf; cases hf
            · exact ⟨hp, by omega⟩
          · exact ⟨hp, by omega⟩
      have hdisj : Disjoint
          ((box t).filter (fun p => f342 t p.1 p.2 = true))
          ((box t).filter (fun p => |p.1| + |p.2| ≤ (4 * ((q - 1 : ℕ) : ℤ) + 2) ∧ (|p.1| + |p.2|) % 4 = 2)) := by
        rw [Finset.disjoint_filter]; intro p _ hf ⟨hle, hpar⟩
        unfold f342 at hf; dsimp only at hf
        rw [if_neg (by omega), if_neg (by omega), decide_eq_true_eq] at hf; omega
      have hcard := congrArg Finset.card hsplit
      rw [Finset.card_union_of_disjoint hdisj, card_le t t le_rfl,
          card_mod4_2 t (q - 1) (by omega)] at hcard
      have hcard_z : (2 * (t : ℤ) * (t : ℤ) + 2 * (t : ℤ) + 1) =
          (((box t).filter (fun p => f342 t p.1 p.2 = true)).card : ℤ) +
          8 * (((q - 1 : ℕ) : ℤ) + 1) * (((q - 1 : ℕ) : ℤ) + 1) := by exact_mod_cast hcard
      have hqsub : ((q - 1 : ℕ) : ℤ) + 1 = (q : ℤ) := by omega
      have htz : (t : ℤ) = 4 * (q : ℤ) + 1 := by omega
      unfold c342; dsimp only
      rw [if_neg (by omega), if_pos (by omega), hq_def]
      rw [hqsub, htz] at hcard_z
      linarith
  · have hEq : (box t).filter (fun p => f342 t p.1 p.2 = true) =
        (box t).filter (fun p => |p.1| + |p.2| ≤ (4 * q + 2 : ℤ) ∧ (|p.1| + |p.2|) % 4 = 2) := by
      ext p; simp only [Finset.mem_filter]; unfold f342; dsimp only
      rw [show t % 2 = 0 by omega, if_pos rfl]
      constructor
      · rintro ⟨hp, hf⟩
        by_cases h : (t : ℤ) < |p.1| + |p.2|
        · rw [if_pos h] at hf; cases hf
        · rw [if_neg h, decide_eq_true_eq] at hf
          exact ⟨hp, by omega, by omega⟩
      · rintro ⟨hp, hle, hpar⟩
        refine ⟨hp, ?_⟩
        rw [if_neg (by omega), decide_eq_true_eq]; omega
    rw [hEq, card_mod4_2 t q (by omega)]
    unfold c342; dsimp only; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), hq_def]
    push_cast; ring
  · have hsplit : (box t).filter (fun p => |p.1| + |p.2| ≤ (t : ℤ)) =
        (box t).filter (fun p => f342 t p.1 p.2 = true) ∪
        (box t).filter (fun p => |p.1| + |p.2| ≤ (4 * (q : ℤ)) ∧ (|p.1| + |p.2|) % 4 = 0) := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter]; unfold f342; dsimp only
      rw [if_neg (show ¬ t % 2 = 0 by omega)]
      constructor
      · rintro ⟨hp, hle⟩
        by_cases hp0 : (|p.1| + |p.2|) % 4 = 0
        · right; exact ⟨hp, by omega, hp0⟩
        · left; refine ⟨hp, ?_⟩; rw [if_neg (by omega), decide_eq_true_eq]; omega
      · rintro (⟨hp, hf⟩ | ⟨hp, hle, _⟩)
        · by_cases h : (t : ℤ) < |p.1| + |p.2|
          · rw [if_pos h] at hf; cases hf
          · exact ⟨hp, by omega⟩
        · exact ⟨hp, by omega⟩
    have hdisj : Disjoint
        ((box t).filter (fun p => f342 t p.1 p.2 = true))
        ((box t).filter (fun p => |p.1| + |p.2| ≤ (4 * (q : ℤ)) ∧ (|p.1| + |p.2|) % 4 = 0)) := by
      rw [Finset.disjoint_filter]; intro p _ hf ⟨hle, hpar⟩
      unfold f342 at hf; dsimp only at hf
      rw [if_neg (by omega), if_neg (by omega), decide_eq_true_eq] at hf; omega
    have hcard := congrArg Finset.card hsplit
    rw [Finset.card_union_of_disjoint hdisj, card_le t t le_rfl,
        card_mod4_0 t q (by omega)] at hcard
    have hcard_z : (2 * (t : ℤ) * (t : ℤ) + 2 * (t : ℤ) + 1) =
        (((box t).filter (fun p => f342 t p.1 p.2 = true)).card : ℤ) +
        (8 * (q : ℤ) * (q : ℤ) + 8 * (q : ℤ) + 1) := by exact_mod_cast hcard
    have htz : (t : ℤ) = 4 * (q : ℤ) + 3 := by omega
    unfold c342; dsimp only
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), hq_def]
    rw [htz] at hcard_z
    linarith

-- ============================================================================
-- Section 3: Exact closed form for a(n), recurrence, and generating function
-- ============================================================================

private lemma a_eq_c342_diff (n : ℕ) : a n = c342 (n + 1) - c342 n := by
  unfold a
  rw [onCount_342_eq (n + 1), onCount_342_eq n]

private lemma c342_eval_mod (q : ℕ) :
    c342 (4 * q) = 8 * (q : ℤ) * (q : ℤ) + 8 * (q : ℤ) + 1 ∧
    c342 (4 * q + 1) = 24 * (q : ℤ) * (q : ℤ) + 24 * (q : ℤ) + 5 ∧
    c342 (4 * q + 2) = 8 * ((q : ℤ) + 1) * ((q : ℤ) + 1) ∧
    c342 (4 * q + 3) = 24 * ((q : ℤ) + 1) * ((q : ℤ) + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> unfold c342 <;> dsimp only
  · rw [if_pos (by omega), show (4 * q) / 4 = q by omega]
  · rw [if_neg (by omega), if_pos (by omega), show (4 * q + 1) / 4 = q by omega]
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show (4 * q + 2) / 4 = q by omega]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show (4 * q + 3) / 4 = q by omega]

private lemma a_eval_mod (q : ℕ) :
    a (4 * q) = 16 * (q : ℤ) * (q : ℤ) + 16 * (q : ℤ) + 4 ∧
    a (4 * q + 1) = -16 * (q : ℤ) * (q : ℤ) - 8 * (q : ℤ) + 3 ∧
    a (4 * q + 2) = 16 * ((q : ℤ) + 1) * ((q : ℤ) + 1) ∧
    a (4 * q + 3) = -16 * ((q : ℤ) + 1) * ((q : ℤ) + 1) + 8 * ((q : ℤ) + 1) + 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := c342_eval_mod q
  have h4 := (c342_eval_mod (q + 1)).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [a_eq_c342_diff, h1, h0]; ring
  · rw [a_eq_c342_diff, show 4 * q + 1 + 1 = 4 * q + 2 by omega, h2, h1]; ring
  · rw [a_eq_c342_diff, show 4 * q + 2 + 1 = 4 * q + 3 by omega, h3, h2]; ring
  · rw [a_eq_c342_diff, show 4 * q + 3 + 1 = 4 * (q + 1) by omega, h4, h3]; push_cast; ring

private lemma a_rec_int (n : ℕ) (hn : 7 ≤ n) :
    a n = -a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) + a (n - 5) - a (n - 6) - a (n - 7) := by
  set q := n / 4
  set r := n % 4
  have hr : r < 4 := Nat.mod_lt n (by omega)
  have hdiv : n = 4 * q + r := by omega
  have hq : 1 ≤ q := by omega
  have hq2 : 2 ≤ q ∨ r = 3 := by omega
  interval_cases r
  · have hq2' : 2 ≤ q := by omega
    set k := q - 2
    have hn_eq : n = 4 * (k + 2) := by omega
    rw [hn_eq,
        show 4 * (k + 2) - 1 = 4 * (k + 1) + 3 by omega,
        show 4 * (k + 2) - 2 = 4 * (k + 1) + 2 by omega,
        show 4 * (k + 2) - 3 = 4 * (k + 1) + 1 by omega,
        show 4 * (k + 2) - 4 = 4 * (k + 1) by omega,
        show 4 * (k + 2) - 5 = 4 * k + 3 by omega,
        show 4 * (k + 2) - 6 = 4 * k + 2 by omega,
        show 4 * (k + 2) - 7 = 4 * k + 1 by omega,
        (a_eval_mod (k + 2)).1, (a_eval_mod (k + 1)).2.2.2, (a_eval_mod (k + 1)).2.2.1,
        (a_eval_mod (k + 1)).2.1, (a_eval_mod (k + 1)).1,
        (a_eval_mod k).2.2.2, (a_eval_mod k).2.2.1, (a_eval_mod k).2.1]
    push_cast; ring
  · have hq2' : 2 ≤ q := by omega
    set k := q - 2
    have hn_eq : n = 4 * (k + 2) + 1 := by omega
    rw [hn_eq,
        show 4 * (k + 2) + 1 - 1 = 4 * (k + 2) by omega,
        show 4 * (k + 2) + 1 - 2 = 4 * (k + 1) + 3 by omega,
        show 4 * (k + 2) + 1 - 3 = 4 * (k + 1) + 2 by omega,
        show 4 * (k + 2) + 1 - 4 = 4 * (k + 1) + 1 by omega,
        show 4 * (k + 2) + 1 - 5 = 4 * (k + 1) by omega,
        show 4 * (k + 2) + 1 - 6 = 4 * k + 3 by omega,
        show 4 * (k + 2) + 1 - 7 = 4 * k + 2 by omega,
        (a_eval_mod (k + 2)).2.1, (a_eval_mod (k + 2)).1,
        (a_eval_mod (k + 1)).2.2.2, (a_eval_mod (k + 1)).2.2.1,
        (a_eval_mod (k + 1)).2.1, (a_eval_mod (k + 1)).1,
        (a_eval_mod k).2.2.2, (a_eval_mod k).2.2.1]
    push_cast; ring
  · have hq2' : 2 ≤ q := by omega
    set k := q - 2
    have hn_eq : n = 4 * (k + 2) + 2 := by omega
    rw [hn_eq,
        show 4 * (k + 2) + 2 - 1 = 4 * (k + 2) + 1 by omega,
        show 4 * (k + 2) + 2 - 2 = 4 * (k + 2) by omega,
        show 4 * (k + 2) + 2 - 3 = 4 * (k + 1) + 3 by omega,
        show 4 * (k + 2) + 2 - 4 = 4 * (k + 1) + 2 by omega,
        show 4 * (k + 2) + 2 - 5 = 4 * (k + 1) + 1 by omega,
        show 4 * (k + 2) + 2 - 6 = 4 * (k + 1) by omega,
        show 4 * (k + 2) + 2 - 7 = 4 * k + 3 by omega,
        (a_eval_mod (k + 2)).2.2.1, (a_eval_mod (k + 2)).2.1, (a_eval_mod (k + 2)).1,
        (a_eval_mod (k + 1)).2.2.2, (a_eval_mod (k + 1)).2.2.1,
        (a_eval_mod (k + 1)).2.1, (a_eval_mod (k + 1)).1,
        (a_eval_mod k).2.2.2]
    push_cast; ring
  · set k := q - 1
    have hn_eq : n = 4 * (k + 1) + 3 := by omega
    rw [hn_eq,
        show 4 * (k + 1) + 3 - 1 = 4 * (k + 1) + 2 by omega,
        show 4 * (k + 1) + 3 - 2 = 4 * (k + 1) + 1 by omega,
        show 4 * (k + 1) + 3 - 3 = 4 * (k + 1) by omega,
        show 4 * (k + 1) + 3 - 4 = 4 * k + 3 by omega,
        show 4 * (k + 1) + 3 - 5 = 4 * k + 2 by omega,
        show 4 * (k + 1) + 3 - 6 = 4 * k + 1 by omega,
        show 4 * (k + 1) + 3 - 7 = 4 * k by omega,
        (a_eval_mod (k + 1)).2.2.2, (a_eval_mod (k + 1)).2.2.1,
        (a_eval_mod (k + 1)).2.1, (a_eval_mod (k + 1)).1,
        (a_eval_mod k).2.2.2, (a_eval_mod k).2.2.1,
        (a_eval_mod k).2.1, (a_eval_mod k).1]
    push_cast; ring

private lemma a_rec (n : ℕ) (hn : 7 ≤ n) :
    (a n : ℚ) = -a (n - 1) + a (n - 2) + a (n - 3) + a (n - 4) + a (n - 5) - a (n - 6) - a (n - 7) := by
  exact_mod_cast a_rec_int n hn

private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) ^ 3 * (1 + X ^ 2) : PowerSeries ℚ) =
      4 + 7 * X + 15 * X ^ 2 + 2 * X ^ 3 + 6 * X ^ 4 - X ^ 5 - X ^ 6 := by
  set A : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hlhs : A * ((1 - X) ^ 2 * (1 + X) ^ 3 * (1 + X ^ 2) : PowerSeries ℚ) =
      A + A * X ^ 1 - A * X ^ 2 - A * X ^ 3 - A * X ^ 4 - A * X ^ 5 + A * X ^ 6 + A * X ^ 7 := by
    simp only [pow_one]
    ring
  have hrhs : (4 + 7 * X + 15 * X ^ 2 + 2 * X ^ 3 + 6 * X ^ 4 - X ^ 5 - X ^ 6 : PowerSeries ℚ) =
      PowerSeries.C (4 : ℚ) + PowerSeries.C (7 : ℚ) * X + PowerSeries.C (15 : ℚ) * X ^ 2 +
        PowerSeries.C (2 : ℚ) * X ^ 3 + PowerSeries.C (6 : ℚ) * X ^ 4 -
        PowerSeries.C (1 : ℚ) * X ^ 5 - PowerSeries.C (1 : ℚ) * X ^ 6 := by
    simp only [map_one, map_ofNat, one_mul]
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_C, PowerSeries.coeff_X, PowerSeries.coeff_mk, A]
  by_cases hn : 7 ≤ n
  · have hrec := a_rec n hn
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
      show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, show n - 6 ≠ 0 by omega,
      ite_true, ite_false]
    linarith
  · have h0 : (a 0 : ℚ) = 4 := by exact_mod_cast (by simpa using (a_eval_mod 0).1 : a 0 = 4)
    have h1 : (a 1 : ℚ) = 3 := by exact_mod_cast (by simpa using (a_eval_mod 0).2.1 : a 1 = 3)
    have h2 : (a 2 : ℚ) = 16 := by exact_mod_cast (by simpa using (a_eval_mod 0).2.2.1 : a 2 = 16)
    have h3 : (a 3 : ℚ) = -7 := by exact_mod_cast (by simpa using (a_eval_mod 0).2.2.2 : a 3 = -7)
    have h4 : (a 4 : ℚ) = 36 := by exact_mod_cast (by simpa using (a_eval_mod 1).1 : a 4 = 36)
    have h5 : (a 5 : ℚ) = -21 := by exact_mod_cast (by simpa using (a_eval_mod 1).2.1 : a 5 = -21)
    have h6 : (a 6 : ℚ) = 64 := by exact_mod_cast (by simpa using (a_eval_mod 1).2.2.1 : a 6 = 64)
    have hs21 : (2 - 1 : ℕ) = 1 := rfl
    have hs31 : (3 - 1 : ℕ) = 2 := rfl
    have hs41 : (4 - 1 : ℕ) = 3 := rfl
    have hs51 : (5 - 1 : ℕ) = 4 := rfl
    have hs61 : (6 - 1 : ℕ) = 5 := rfl
    interval_cases n <;>
      simp only [Nat.sub_self, hs21, hs31, hs41, hs51, hs61,
        h0, h1, h2, h3, h4, h5, h6] <;>
      norm_num

end OMA.Proof_oeis_a269512

theorem OMA.solution : type_of% @OMA.S_oeis_a269512.main :=
  ⟨OMA.Proof_oeis_a269512.a_rec, OMA.Proof_oeis_a269512.gf_eq⟩

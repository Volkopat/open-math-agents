import OMAStatements.S_oeis_a273828

section Proof_a273828
open OMA.S_oeis_a273828

-- 1. Equivalence between finite-box stageCfg and infinite-plane stateR
def stepR (r : ℕ) (g : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  applyRule r (g x y) (g x (y - 1)) (g x (y + 1)) (g (x - 1) y) (g (x + 1) y)

def stateR (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => stepR r (stateR r t) x y

def gridRows (g : ℤ → ℤ → Bool) (t : ℕ) : List (List Bool) :=
  (List.range (2 * t + 1)).map fun (iy : ℕ) =>
    (List.range (2 * t + 1)).map fun (ix : ℕ) =>
      g ((ix : ℤ) - ↑t) ((iy : ℤ) - ↑t)

lemma getD_map_range {α : Type} (n : ℕ) (f : ℕ → α) (i : ℕ) (d : α) (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD, hi]

lemma flatMap_pure_map {α β γ : Type} (xs : List α) (c : α → β) (f : β → γ) :
    List.map f (List.flatMap (fun a => [c a]) xs) = List.map (fun a => f (c a)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

lemma abs_step_lb (z : ℤ) : |z| - 1 ≤ |z - 1| ∧ |z| - 1 ≤ |z + 1| := by
  cases abs_cases z <;> cases abs_cases (z - 1) <;> cases abs_cases (z + 1) <;> omega

lemma stateR_out (r : ℕ) (hr0 : applyRule r false false false false false = false) (t : ℕ) :
    ∀ x y : ℤ, (t : ℤ) < |x| + |y| → stateR r t x y = false := by
  induction t with
  | zero =>
    intro x y h
    have hne : ¬(x = 0 ∧ y = 0) := by rintro ⟨rfl, rfl⟩; simp at h
    simp [stateR, hne]
  | succ t ih =>
    intro x y h
    change stepR r (stateR r t) x y = false
    unfold stepR
    have hx := abs_step_lb x
    have hy := abs_step_lb y
    rw [ih x y (by omega), ih x (y - 1) (by omega), ih x (y + 1) (by omega),
        ih (x - 1) y (by omega), ih (x + 1) y (by omega)]
    exact hr0

lemma getCell_gridRows (t : ℕ) (g : ℤ → ℤ → Bool)
    (hg : ∀ x y : ℤ, (t : ℤ) < |x| + |y| → g x y = false) (x y : ℤ) :
    getCell t (false, gridRows g t) x y = g x y := by
  unfold getCell
  split_ifs with h
  · rcases h with ⟨hx1, hx2, hy1, hy2⟩
    have hiy : (y + ↑t).toNat < 2 * t + 1 := by omega
    have hix : (x + ↑t).toNat < 2 * t + 1 := by omega
    have hiy_eq : (((y + ↑t).toNat : ℤ) - ↑t) = y := by omega
    have hix_eq : (((x + ↑t).toNat : ℤ) - ↑t) = x := by omega
    unfold gridRows
    rw [getD_map_range _ _ _ _ hiy, getD_map_range _ _ _ _ hix, hix_eq, hiy_eq]
  · symm
    apply hg
    cases abs_cases x <;> cases abs_cases y <;> omega

lemma stageCfg_eq_gridRows (r : ℕ) (hr0 : applyRule r false false false false false = false) (t : ℕ) :
    stageCfg r t = (false, gridRows (stateR r t) t) := by
  induction t with
  | zero => simp [stageCfg, gridRows, stateR]
  | succ t ih =>
    rw [stageCfg, ih]
    have hg : getCell t (false, gridRows (stateR r t) t) = stateR r t := by
      funext x y
      exact getCell_gridRows t (stateR r t) (stateR_out r hr0 t) x y
    dsimp only [stepCfg]
    rw [hg, hr0]
    simp only [List.bind_eq_flatMap, List.pure_def, flatMap_pure_map, gridRows, stateR, stepR]

-- 2. Closed-form characterization exact950 for both Rule 950 and Rule 1014
def exactNat (t a b : ℕ) : Bool :=
  if t = 0 then decide (a = 0 ∧ b = 0)
  else if t < a + b then false
  else if a + b = t then true
  else if a + b = t - 1 then decide (Nat.choose (t + 1) (a + 1) % 2 = 0)
  else decide ¬(t % 4 = 3 ∧ 7 ≤ t ∧ a + b = t - 3 ∧ (a = 0 ∨ b = 0))

def exact950 (t : ℕ) (x y : ℤ) : Bool :=
  exactNat t x.natAbs y.natAbs

lemma exact950_nat (t a b : ℕ) : exact950 t (a : ℤ) (b : ℤ) = exactNat t a b := by
  simp [exact950]

lemma exact950_zero_left (t b : ℕ) : exact950 t 0 (b : ℤ) = exactNat t 0 b := by
  simp [exact950]

lemma exact950_one_left (t b : ℕ) : exact950 t 1 (b : ℤ) = exactNat t 1 b := by
  simp [exact950]

lemma exact950_zero_one (t : ℕ) : exact950 t 0 1 = exactNat t 0 1 := by
  simp [exact950]

lemma exact950_out (t : ℕ) (x y : ℤ) (h : (t : ℤ) < |x| + |y|) :
    exact950 t x y = false := by
  unfold exact950 exactNat
  have hlt : t < x.natAbs + y.natAbs := by
    cases abs_cases x <;> cases abs_cases y <;> omega
  split_ifs with h0
  · subst h0
    have hne : ¬(x.natAbs = 0 ∧ y.natAbs = 0) := by omega
    exact decide_eq_false hne
  · rfl

lemma stageCfg_small (r : ℕ) (hr : r = 950 ∨ r = 1014) (t : ℕ) (ht : t < 7) :
    stageCfg r t = (false, gridRows (exact950 t) t) := by
  have ht_cases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 := by omega
  rcases hr with rfl | rfl <;>
    rcases ht_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma stateR_small (r : ℕ) (hr : r = 950 ∨ r = 1014) (t : ℕ) (ht : t < 7) (x y : ℤ) :
    stateR r t x y = exact950 t x y := by
  have hr0 : applyRule r false false false false false = false := by
    rcases hr with rfl | rfl <;> decide
  have h1 := getCell_gridRows t (stateR r t) (stateR_out r hr0 t) x y
  have h2 := getCell_gridRows t (exact950 t) (exact950_out t) x y
  rw [← h1, ← h2, ← stageCfg_eq_gridRows r hr0 t, stageCfg_small r hr t ht]

-- 3. Symmetries and rule-bit lemmas
lemma exactNat_comm (t a b : ℕ) : exactNat t b a = exactNat t a b := by
  unfold exactNat
  have hab : b + a = a + b := Nat.add_comm b a
  rw [hab]
  split_ifs with h0 h1 h2 h3
  · simp [and_comm]
  · rfl
  · rfl
  · have hsymm : b + 1 = (t + 1) - (a + 1) := by omega
    have hle : a + 1 ≤ t + 1 := by omega
    rw [hsymm, Nat.choose_symm hle]
  · simp [or_comm]

lemma exact950_neg_x (t : ℕ) (x y : ℤ) : exact950 t (-x) y = exact950 t x y := by
  simp [exact950]

lemma exact950_neg_y (t : ℕ) (x y : ℤ) : exact950 t x (-y) = exact950 t x y := by
  simp [exact950]

lemma exact950_swap (t : ℕ) (x y : ℤ) : exact950 t y x = exact950 t x y := by
  exact exactNat_comm t x.natAbs y.natAbs

lemma applyRule_perm (r : ℕ) (c n1 s1 w1 e1 n2 s2 w2 e2 : Bool)
    (h : n1.toNat + s1.toNat + w1.toNat + e1.toNat = n2.toNat + s2.toNat + w2.toNat + e2.toNat) :
    applyRule r c n1 s1 w1 e1 = applyRule r c n2 s2 w2 e2 := by
  simp only [applyRule, h]

lemma stepR_exact950_neg_x (r t : ℕ) (x y : ℤ) :
    stepR r (exact950 t) (-x) y = stepR r (exact950 t) x y := by
  unfold stepR
  have h1 : -x - 1 = -(x + 1) := by omega
  have h2 : -x + 1 = -(x - 1) := by omega
  rw [h1, h2, exact950_neg_x, exact950_neg_x t x (y - 1), exact950_neg_x t x (y + 1),
      exact950_neg_x t (x + 1) y, exact950_neg_x t (x - 1) y]
  apply applyRule_perm; omega

lemma stepR_exact950_neg_y (r t : ℕ) (x y : ℤ) :
    stepR r (exact950 t) x (-y) = stepR r (exact950 t) x y := by
  unfold stepR
  have h1 : -y - 1 = -(y + 1) := by omega
  have h2 : -y + 1 = -(y - 1) := by omega
  rw [h1, h2, exact950_neg_y, exact950_neg_y t x (y + 1), exact950_neg_y t x (y - 1),
      exact950_neg_y t (x - 1) y, exact950_neg_y t (x + 1) y]
  apply applyRule_perm; omega

lemma stepR_exact950_swap (r t : ℕ) (x y : ℤ) :
    stepR r (exact950 t) y x = stepR r (exact950 t) x y := by
  unfold stepR
  rw [exact950_swap t y x, exact950_swap t y (x - 1), exact950_swap t y (x + 1),
      exact950_swap t (y - 1) x, exact950_swap t (y + 1) x]
  apply applyRule_perm; omega

lemma applyRule_false_0 (r : ℕ) (hr : r = 950 ∨ r = 1014) :
    applyRule r false false false false false = false := by
  rcases hr with rfl | rfl <;> decide

lemma applyRule_false_pos (r : ℕ) (hr : r = 950 ∨ r = 1014) (n s w e : Bool)
    (h : n.toNat + s.toNat + w.toNat + e.toNat = 1 ∨
         n.toNat + s.toNat + w.toNat + e.toNat = 2 ∨
         n.toNat + s.toNat + w.toNat + e.toNat = 4) :
    applyRule r false n s w e = true := by
  rcases hr with rfl | rfl <;> cases n <;> cases s <;> cases w <;> cases e <;>
    simp_all [applyRule] <;> decide

lemma applyRule_true_eq (r : ℕ) (hr : r = 950 ∨ r = 1014) (n s w e : Bool) :
    applyRule r true n s w e = decide (n.toNat + s.toNat + w.toNat + e.toNat ≠ 1) := by
  rcases hr with rfl | rfl <;> cases n <;> cases s <;> cases w <;> cases e <;> decide

lemma applyRule_all_true (r : ℕ) (hr : r = 950 ∨ r = 1014) (c : Bool) :
    applyRule r c true true true true = true := by
  rcases hr with rfl | rfl <;> cases c <;> decide

-- 4. Branch helpers for exactNat (t >= 1) and binomial parities
lemma exactNat_gt {t u v : ℕ} (ht : 1 ≤ t) (h : t < u + v) : exactNat t u v = false := by
  unfold exactNat; split_ifs <;> first | rfl | omega

lemma exactNat_eq_t {t u v : ℕ} (ht : 1 ≤ t) (h : u + v = t) : exactNat t u v = true := by
  unfold exactNat; split_ifs <;> first | rfl | omega

lemma exactNat_eq_tm1 {t u v : ℕ} (ht : 1 ≤ t) (h : u + v = t - 1) :
    exactNat t u v = decide (Nat.choose (t + 1) (u + 1) % 2 = 0) := by
  unfold exactNat; split_ifs <;> first | rfl | omega

lemma exactNat_le_tm2 {t u v : ℕ} (ht : 2 ≤ t) (h : u + v ≤ t - 2) :
    exactNat t u v = decide ¬(t % 4 = 3 ∧ 7 ≤ t ∧ u + v = t - 3 ∧ (u = 0 ∨ v = 0)) := by
  unfold exactNat; split_ifs <;> first | rfl | omega

lemma exactNat_le_tm2_true {t u v : ℕ} (ht : 2 ≤ t) (h : u + v ≤ t - 2)
    (hno : ¬(t % 4 = 3 ∧ 7 ≤ t ∧ u + v = t - 3 ∧ (u = 0 ∨ v = 0))) :
    exactNat t u v = true := by
  rw [exactNat_le_tm2 ht h]
  exact decide_eq_true hno

lemma choose_two_even_of_mod4_eq3 (t : ℕ) (ht : t % 4 = 3) :
    Nat.choose (t + 1) 2 % 2 = 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, t = 4 * q + 3 := ⟨t / 4, by omega⟩
  rw [Nat.choose_two_right]
  have hsub : 4 * q + 3 + 1 - 1 = 4 * q + 3 := by omega
  rw [hsub]
  have hmul : (4 * q + 3 + 1) * (4 * q + 3) = 4 * ((4 * q + 3) * (q + 1)) := by ring
  rw [hmul]
  generalize (4 * q + 3) * (q + 1) = M
  omega

lemma choose_two_odd_and_odd_iff (t : ℕ) :
    (Nat.choose (t + 1) 2 % 2 = 1 ∧ (t + 1) % 2 = 1) ↔ t % 4 = 2 := by
  rw [Nat.choose_two_right]
  have hsub : t + 1 - 1 = t := by omega
  rw [hsub]
  rcases (by omega : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3) with h4 | h4 | h4 | h4
  · obtain ⟨q, rfl⟩ : ∃ q, t = 4 * q := ⟨t / 4, by omega⟩
    have hmul : (4 * q + 1) * (4 * q) = 4 * ((4 * q + 1) * q) := by ring
    rw [hmul]
    generalize (4 * q + 1) * q = M
    omega
  · omega
  · obtain ⟨q, rfl⟩ : ∃ q, t = 4 * q + 2 := ⟨t / 4, by omega⟩
    have hmul : (4 * q + 2 + 1) * (4 * q + 2) = 4 * (4 * q * q + 5 * q + 1) + 2 := by ring
    rw [hmul]
    generalize 4 * q * q + 5 * q + 1 = M
    omega
  · omega

-- 5. Main inductive step on 0 <= a <= b for t >= 6
lemma stepR_exact950_le (r : ℕ) (hr : r = 950 ∨ r = 1014) (t : ℕ) (ht : 6 ≤ t)
    (a b : ℕ) (hab : a ≤ b) :
    stepR r (exact950 t) (a : ℤ) (b : ℤ) = exact950 (t + 1) (a : ℤ) (b : ℤ) := by
  rw [exact950_nat]
  rcases (by omega : t + 2 ≤ a + b ∨ a + b = t + 1 ∨ a + b = t ∨ a + b = t - 1 ∨
      a + b = t - 2 ∨ a + b = t - 3 ∨ a + b ≤ t - 4) with
      hL | hL | hL | hL | hL | hL | hL
  · -- Case 1: t + 2 <= a + b
    rw [exactNat_gt (by omega) (by omega)]
    unfold stepR
    have hc : exact950 t (a : ℤ) (b : ℤ) = false := by
      rw [exact950_nat, exactNat_gt (by omega) (by omega)]
    have hn : exact950 t (a : ℤ) ((b : ℤ) - 1) = false := by
      apply exact950_out; cases abs_cases (a : ℤ) <;> cases abs_cases ((b : ℤ) - 1) <;> omega
    have hs : exact950 t (a : ℤ) ((b : ℤ) + 1) = false := by
      apply exact950_out; cases abs_cases (a : ℤ) <;> cases abs_cases ((b : ℤ) + 1) <;> omega
    have hw : exact950 t ((a : ℤ) - 1) (b : ℤ) = false := by
      apply exact950_out; cases abs_cases ((a : ℤ) - 1) <;> cases abs_cases (b : ℤ) <;> omega
    have he : exact950 t ((a : ℤ) + 1) (b : ℤ) = false := by
      apply exact950_out; cases abs_cases ((a : ℤ) + 1) <;> cases abs_cases (b : ℤ) <;> omega
    rw [hc, hn, hs, hw, he]
    exact applyRule_false_0 r hr
  · -- Case 2: a + b = t + 1
    rw [exactNat_eq_t (by omega) hL]
    have hb1 : 1 ≤ b := by omega
    have hbm1 : ((b : ℤ) - 1) = ((b - 1 : ℕ) : ℤ) := by omega
    have hbp1 : ((b : ℤ) + 1) = ((b + 1 : ℕ) : ℤ) := by omega
    have hap1 : ((a : ℤ) + 1) = ((a + 1 : ℕ) : ℤ) := by omega
    unfold stepR
    rw [exact950_nat, exactNat_gt (by omega) (by omega),
        hbm1, exact950_nat, exactNat_eq_t (by omega) (by omega),
        hbp1, exact950_nat, exactNat_gt (by omega) (by omega),
        hap1, exact950_nat, exactNat_gt (by omega) (by omega)]
    rcases Nat.eq_zero_or_pos a with rfl | ha1
    · simp only [Nat.cast_zero, zero_sub, exact950_neg_x, exact950_one_left]
      rw [exactNat_gt (by omega) (by omega)]
      apply applyRule_false_pos r hr; simp
    · have ham1 : ((a : ℤ) - 1) = ((a - 1 : ℕ) : ℤ) := by omega
      rw [ham1, exact950_nat, exactNat_eq_t (by omega) (by omega)]
      apply applyRule_false_pos r hr; simp
  · -- Case 3: a + b = t
    rw [exactNat_eq_tm1 (by omega) (by omega)]
    have hb1 : 1 ≤ b := by omega
    have hbm1 : ((b : ℤ) - 1) = ((b - 1 : ℕ) : ℤ) := by omega
    have hbp1 : ((b : ℤ) + 1) = ((b + 1 : ℕ) : ℤ) := by omega
    have hap1 : ((a : ℤ) + 1) = ((a + 1 : ℕ) : ℤ) := by omega
    unfold stepR
    rw [exact950_nat, exactNat_eq_t (by omega) hL,
        hbm1, exact950_nat, exactNat_eq_tm1 (by omega) (by omega),
        hbp1, exact950_nat, exactNat_gt (by omega) (by omega),
        hap1, exact950_nat, exactNat_gt (by omega) (by omega)]
    rcases Nat.eq_zero_or_pos a with rfl | ha1
    · simp only [Nat.cast_zero, zero_sub, zero_add, exact950_neg_x, exact950_one_left]
      rw [exactNat_gt (by omega) (by omega), applyRule_true_eq r hr]
      simp only [Nat.choose_one_right, Bool.toNat_false, add_zero]
      rcases Nat.mod_two_eq_zero_or_one t with ht2 | ht2
      · have h1 : (t + 1) % 2 = 1 := by omega
        have h2 : (t + 1 + 1) % 2 = 0 := by omega
        simp [h1, h2]
      · have h1 : (t + 1) % 2 = 0 := by omega
        have h2 : (t + 1 + 1) % 2 = 1 := by omega
        simp [h1, h2]
    · have ham1 : ((a : ℤ) - 1) = ((a - 1 : ℕ) : ℤ) := by omega
      have ha_sub : a - 1 + 1 = a := by omega
      rw [ham1, exact950_nat, exactNat_eq_tm1 (by omega) (by omega), ha_sub, applyRule_true_eq r hr]
      have hpascal : Nat.choose (t + 1 + 1) (a + 1) =
          Nat.choose (t + 1) a + Nat.choose (t + 1) (a + 1) :=
        Nat.choose_succ_succ (t + 1) a
      rw [hpascal]
      rcases Nat.mod_two_eq_zero_or_one (Nat.choose (t + 1) a) with hp1 | hp1 <;>
        rcases Nat.mod_two_eq_zero_or_one (Nat.choose (t + 1) (a + 1)) with hp2 | hp2
      · have hs : (Nat.choose (t + 1) a + Nat.choose (t + 1) (a + 1)) % 2 = 0 := by omega
        simp [hp1, hp2, hs]
      · have hs : (Nat.choose (t + 1) a + Nat.choose (t + 1) (a + 1)) % 2 = 1 := by omega
        simp [hp1, hp2, hs]
      · have hs : (Nat.choose (t + 1) a + Nat.choose (t + 1) (a + 1)) % 2 = 1 := by omega
        simp [hp1, hp2, hs]
      · have hs : (Nat.choose (t + 1) a + Nat.choose (t + 1) (a + 1)) % 2 = 0 := by omega
        simp [hp1, hp2, hs]
  · -- Case 4: a + b = t - 1 (all 4 neighbors are true!)
    rw [exactNat_le_tm2_true (by omega) (by omega) (by omega)]
    have hb1 : 1 ≤ b := by omega
    have hbm1 : ((b : ℤ) - 1) = ((b - 1 : ℕ) : ℤ) := by omega
    have hbp1 : ((b : ℤ) + 1) = ((b + 1 : ℕ) : ℤ) := by omega
    have hap1 : ((a : ℤ) + 1) = ((a + 1 : ℕ) : ℤ) := by omega
    unfold stepR
    have hn : exact950 t (a : ℤ) ((b : ℤ) - 1) = true := by
      rw [hbm1, exact950_nat, exactNat_le_tm2_true (by omega) (by omega) (by omega)]
    have hs : exact950 t (a : ℤ) ((b : ℤ) + 1) = true := by
      rw [hbp1, exact950_nat, exactNat_eq_t (by omega) (by omega)]
    have he : exact950 t ((a : ℤ) + 1) (b : ℤ) = true := by
      rw [hap1, exact950_nat, exactNat_eq_t (by omega) (by omega)]
    have hw : exact950 t ((a : ℤ) - 1) (b : ℤ) = true := by
      rcases Nat.eq_zero_or_pos a with rfl | ha1
      · simp only [Nat.cast_zero, zero_sub, exact950_neg_x, exact950_one_left]
        exact exactNat_eq_t (by omega) (by omega)
      · have ham1 : ((a : ℤ) - 1) = ((a - 1 : ℕ) : ℤ) := by omega
        rw [ham1, exact950_nat, exactNat_le_tm2_true (by omega) (by omega) (by omega)]
    rw [hn, hs, hw, he]
    exact applyRule_all_true r hr _
  · -- Case 5: a + b = t - 2
    have hb2 : 2 ≤ b := by omega
    have hc : exact950 t (a : ℤ) (b : ℤ) = true := by
      rw [exact950_nat, exactNat_le_tm2_true (by omega) (by omega) (by omega)]
    have hbm1 : ((b : ℤ) - 1) = ((b - 1 : ℕ) : ℤ) := by omega
    have hbp1 : ((b : ℤ) + 1) = ((b + 1 : ℕ) : ℤ) := by omega
    have hap1 : ((a : ℤ) + 1) = ((a + 1 : ℕ) : ℤ) := by omega
    unfold stepR
    rw [hc, applyRule_true_eq r hr]
    rcases Nat.eq_zero_or_pos a with rfl | ha1
    · -- Subcase a = 0, b = t - 2
      rw [exactNat_le_tm2 (by omega) (by omega)]
      simp only [Nat.cast_zero, zero_sub, zero_add, hbm1, hbp1,
        exact950_neg_x, exact950_zero_left, exact950_one_left]
      rw [exactNat_le_tm2 (by omega) (by omega),
          exactNat_eq_tm1 (by omega) (by omega),
          exactNat_eq_tm1 (by omega) (by omega),
          Nat.choose_one_right]
      have hsub3 : 0 + (b - 1) = t - 3 := by omega
      simp only [hsub3, true_or, and_true]
      by_cases ht3 : t % 4 = 3
      · have hc2 := choose_two_even_of_mod4_eq3 t ht3
        have ht14 : (t + 1) % 4 ≠ 3 := by omega
        simp [hc2, ht14]
      · have hn_true : ¬(t % 4 = 3 ∧ 7 ≤ t) := by tauto
        simp only [hn_true, not_false_eq_true, decide_true, Bool.toNat_true]
        have hiff := choose_two_odd_and_odd_iff t
        rcases Nat.mod_two_eq_zero_or_one (Nat.choose (t + 1) 2) with hc2 | hc2 <;>
          rcases Nat.mod_two_eq_zero_or_one (t + 1) with ht12 | ht12
        · have hmod : (t + 1) % 4 ≠ 3 := by omega
          simp [hc2, ht12, hmod]
        · have hne2 : t % 4 ≠ 2 := by intro hm2; exact absurd (hiff.mpr hm2).1 (by omega)
          have hmod : (t + 1) % 4 ≠ 3 := by omega
          simp [hc2, ht12, hmod]
        · have hmod : (t + 1) % 4 ≠ 3 := by omega
          simp [hc2, ht12, hmod]
        · have hm2 : t % 4 = 2 := hiff.mp ⟨hc2, ht12⟩
          have hmod : (t + 1) % 4 = 3 := by omega
          have ht7 : 7 ≤ t + 1 := by omega
          have hb_eq : b = t + 1 - 3 := by omega
          simp [hc2, ht12, hmod, ht7, hb_eq]
    · -- Subcase 1 <= a <= b, a + b = t - 2
      rw [exactNat_le_tm2_true (by omega) (by omega) (by omega)]
      have ham1 : ((a : ℤ) - 1) = ((a - 1 : ℕ) : ℤ) := by omega
      have hn : exact950 t (a : ℤ) ((b : ℤ) - 1) = true := by
        rw [hbm1, exact950_nat, exactNat_le_tm2_true (by omega) (by omega) (by omega)]
      rw [hn, Bool.toNat_true]
      rcases (by omega : a = 1 ∨ 2 ≤ a) with rfl | ha2
      · by_cases ht3 : t % 4 = 3
        · have hs : exact950 t ((1 : ℕ) : ℤ) ((b : ℤ) + 1) = true := by
            rw [hbp1, exact950_nat, exactNat_eq_tm1 (by omega) (by omega)]
            simp [choose_two_even_of_mod4_eq3 t ht3]
          rw [hs, Bool.toNat_true]
          simp only [decide_eq_true_eq]; omega
        · have hw : exact950 t (((1 : ℕ) : ℤ) - 1) (b : ℤ) = true := by
            rw [ham1, exact950_nat, exactNat_le_tm2_true (by omega) (by omega) (by omega)]
          rw [hw, Bool.toNat_true]
          simp only [decide_eq_true_eq]; omega
      · have hw : exact950 t ((a : ℤ) - 1) (b : ℤ) = true := by
          rw [ham1, exact950_nat, exactNat_le_tm2_true (by omega) (by omega) (by omega)]
        rw [hw, Bool.toNat_true]
        simp only [decide_eq_true_eq]; omega
  · -- Case 6: a + b = t - 3 (all 4 neighbors are true!)
    rw [exactNat_le_tm2_true (by omega) (by omega) (by omega)]
    have hb2 : 2 ≤ b := by omega
    have hbm1 : ((b : ℤ) - 1) = ((b - 1 : ℕ) : ℤ) := by omega
    have hbp1 : ((b : ℤ) + 1) = ((b + 1 : ℕ) : ℤ) := by omega
    have hap1 : ((a : ℤ) + 1) = ((a + 1 : ℕ) : ℤ) := by omega
    unfold stepR
    have hn : exact950 t (a : ℤ) ((b : ℤ) - 1) = true := by
      rw [hbm1, exact950_nat, exactNat_le_tm2_true (by omega) (by omega) (by omega)]
    have hs : exact950 t (a : ℤ) ((b : ℤ) + 1) = true := by
      rw [hbp1, exact950_nat, exactNat_le_tm2_true (by omega) (by omega) (by omega)]
    have he : exact950 t ((a : ℤ) + 1) (b : ℤ) = true := by
      rw [hap1, exact950_nat, exactNat_le_tm2_true (by omega) (by omega) (by omega)]
    have hw : exact950 t ((a : ℤ) - 1) (b : ℤ) = true := by
      rcases Nat.eq_zero_or_pos a with rfl | ha1
      · simp only [Nat.cast_zero, zero_sub, exact950_neg_x, exact950_one_left]
        exact exactNat_le_tm2_true (by omega) (by omega) (by omega)
      · have ham1 : ((a : ℤ) - 1) = ((a - 1 : ℕ) : ℤ) := by omega
        rw [ham1, exact950_nat, exactNat_le_tm2_true (by omega) (by omega) (by omega)]
    rw [hn, hs, hw, he]
    exact applyRule_all_true r hr _
  · -- Case 7: a + b <= t - 4
    rw [exactNat_le_tm2_true (by omega) (by omega) (by omega)]
    have hc : exact950 t (a : ℤ) (b : ℤ) = true := by
      rw [exact950_nat, exactNat_le_tm2_true (by omega) (by omega) (by omega)]
    unfold stepR
    rw [hc, applyRule_true_eq r hr]
    rcases Nat.eq_zero_or_pos b with rfl | hb1
    · have ha0 : a = 0 := by omega
      subst ha0
      simp only [Nat.cast_zero, zero_sub, zero_add, exact950_neg_y, exact950_neg_x]
      have hs : exact950 t 0 1 = true := by
        rw [exact950_zero_one]
        exact exactNat_le_tm2_true (by omega) (by omega) (by omega)
      have he : exact950 t 1 0 = true := by
        rw [exact950_swap, hs]
      rw [hs, he]
      decide
    · have hap1 : ((a : ℤ) + 1) = ((a + 1 : ℕ) : ℤ) := by omega
      have he : exact950 t ((a : ℤ) + 1) (b : ℤ) = true := by
        rw [hap1, exact950_nat, exactNat_le_tm2_true (by omega) (by omega) (by omega)]
      rcases Nat.eq_zero_or_pos a with rfl | ha1
      · have hw : exact950 t (((0 : ℕ) : ℤ) - 1) (b : ℤ) = true := by
          simp only [Nat.cast_zero, zero_sub, exact950_neg_x, exact950_one_left]
          exact exactNat_le_tm2_true (by omega) (by omega) (by omega)
        rw [hw, he, Bool.toNat_true]
        simp only [decide_eq_true_eq]; omega
      · have hbp1 : ((b : ℤ) + 1) = ((b + 1 : ℕ) : ℤ) := by omega
        have hs : exact950 t (a : ℤ) ((b : ℤ) + 1) = true := by
          rw [hbp1, exact950_nat, exactNat_le_tm2_true (by omega) (by omega) (by omega)]
        rw [hs, he, Bool.toNat_true]
        simp only [decide_eq_true_eq]; omega

lemma stepR_exact950_nat (r : ℕ) (hr : r = 950 ∨ r = 1014) (t : ℕ) (ht : 6 ≤ t) (a b : ℕ) :
    stepR r (exact950 t) (a : ℤ) (b : ℤ) = exact950 (t + 1) (a : ℤ) (b : ℤ) := by
  by_cases hab : a ≤ b
  · exact stepR_exact950_le r hr t ht a b hab
  · rw [stepR_exact950_swap, exact950_swap]
    exact stepR_exact950_le r hr t ht b a (by omega)

lemma stepR_exact950_int_nat (r : ℕ) (hr : r = 950 ∨ r = 1014) (t : ℕ) (ht : 6 ≤ t)
    (x : ℤ) (b : ℕ) :
    stepR r (exact950 t) x (b : ℤ) = exact950 (t + 1) x (b : ℤ) := by
  by_cases hx : 0 ≤ x
  · have hx_eq : x = (x.toNat : ℤ) := by omega
    rw [hx_eq]
    exact stepR_exact950_nat r hr t ht x.toNat b
  · have hx_eq : x = -((-x).toNat : ℤ) := by omega
    rw [hx_eq, stepR_exact950_neg_x, exact950_neg_x]
    exact stepR_exact950_nat r hr t ht (-x).toNat b

lemma stepR_exact950_all (r : ℕ) (hr : r = 950 ∨ r = 1014) (t : ℕ) (ht : 6 ≤ t) (x y : ℤ) :
    stepR r (exact950 t) x y = exact950 (t + 1) x y := by
  by_cases hy : 0 ≤ y
  · have hy_eq : y = (y.toNat : ℤ) := by omega
    rw [hy_eq]
    exact stepR_exact950_int_nat r hr t ht x y.toNat
  · have hy_eq : y = -((-y).toNat : ℤ) := by omega
    rw [hy_eq, stepR_exact950_neg_y, exact950_neg_y]
    exact stepR_exact950_int_nat r hr t ht x (-y).toNat

lemma stateR_eq_exact950 (r : ℕ) (hr : r = 950 ∨ r = 1014) (t : ℕ) :
    ∀ x y : ℤ, stateR r t x y = exact950 t x y := by
  induction t with
  | zero => exact stateR_small r hr 0 (by decide)
  | succ t ih =>
    by_cases ht : t < 6
    · exact stateR_small r hr (t + 1) (by omega)
    · intro x y
      change stepR r (stateR r t) x y = exact950 (t + 1) x y
      have hfun : stateR r t = exact950 t := funext fun u => funext fun v => ih u v
      rw [hfun]
      exact stepR_exact950_all r hr t (by omega) x y

lemma stageCfg_1014_eq_950 (t : ℕ) : stageCfg 1014 t = stageCfg 950 t := by
  rw [stageCfg_eq_gridRows 1014 (applyRule_false_0 1014 (Or.inr rfl)) t,
      stageCfg_eq_gridRows 950 (applyRule_false_0 950 (Or.inl rfl)) t]
  have h : stateR 1014 t = stateR 950 t := by
    funext x y
    rw [stateR_eq_exact950 1014 (Or.inr rfl) t x y, stateR_eq_exact950 950 (Or.inl rfl) t x y]
  rw [h]

-- 6. Counting ON cells at t = 2 ^ n - 1 for 2 < n
lemma two_pow_ge_eight (n : ℕ) (hn : 2 < n) : 8 ≤ 2 ^ n := by
  have hn3 : 3 ≤ n := by omega
  calc 8 = 2 ^ 3 := by decide
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn3

lemma exact950_two_pow_pred (n : ℕ) (hn : 2 < n) (x y : ℤ) :
    exact950 (2 ^ n - 1) x y =
      decide (x.natAbs + y.natAbs ≤ 2 ^ n - 1 ∧
        ¬(x.natAbs + y.natAbs = 2 ^ n - 4 ∧ (x.natAbs = 0 ∨ y.natAbs = 0))) := by
  have hpow8 : 8 ≤ 2 ^ n := two_pow_ge_eight n hn
  have ht7 : 7 ≤ 2 ^ n - 1 := by omega
  have ht1 : 2 ^ n - 1 + 1 = 2 ^ n := by omega
  have hmod4 : (2 ^ n - 1) % 4 = 3 := by
    have hdiv : 4 ∣ 2 ^ n := by
      have hn2 : 2 ≤ n := by omega
      rcases Nat.exists_eq_add_of_le hn2 with ⟨k, rfl⟩
      rw [Nat.pow_add]
      exact ⟨2 ^ k, rfl⟩
    rcases hdiv with ⟨m, hm⟩
    omega
  unfold exact950 exactNat
  split_ifs with h0 hgt heq htm1
  · omega
  · have hfalse : ¬(x.natAbs + y.natAbs ≤ 2 ^ n - 1) := by omega
    simp [hfalse]
  · have hle : x.natAbs + y.natAbs ≤ 2 ^ n - 1 := by omega
    have hne : x.natAbs + y.natAbs ≠ 2 ^ n - 4 := by omega
    simp [hle, hne]
  · have hle : x.natAbs + y.natAbs ≤ 2 ^ n - 1 := by omega
    have hne : x.natAbs + y.natAbs ≠ 2 ^ n - 4 := by omega
    rw [ht1]
    have hdvd : 2 ∣ (2 ^ n).choose (x.natAbs + 1) :=
      Nat.Prime.dvd_choose_pow Nat.prime_two (Nat.succ_ne_zero _) (by omega)
    rcases hdvd with ⟨m, hm⟩
    have hmod2 : (2 ^ n).choose (x.natAbs + 1) % 2 = 0 := by omega
    simp [hmod2, hle, hne]
  · have hle : x.natAbs + y.natAbs ≤ 2 ^ n - 1 := by omega
    have hsub : 2 ^ n - 1 - 3 = 2 ^ n - 4 := by omega
    simp [hmod4, ht7, hle, hsub]

lemma count_interval (N L R : ℕ) (hLR : L ≤ R) :
    ((List.range N).map fun (i : ℕ) => decide (L ≤ i ∧ i < R)).count true =
      if N ≤ L then 0 else if N ≤ R then N - L else R - L := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.count_append, ih]
    simp only [List.map_cons, List.map_nil, List.count_nil, List.count_cons,
      beq_true, decide_eq_true_eq]
    split_ifs <;> omega

lemma count_interval_hole1 (N L R h1 : ℕ) (hL1 : L ≤ h1) (h1R : h1 < R) :
    ((List.range N).map fun (i : ℕ) => decide (L ≤ i ∧ i < R ∧ i ≠ h1)).count true =
      if N ≤ L then 0 else if N ≤ h1 then N - L else if N ≤ R then N - (L + 1) else R - (L + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.count_append, ih]
    simp only [List.map_cons, List.map_nil, List.count_nil, List.count_cons,
      beq_true, decide_eq_true_eq]
    split_ifs <;> omega

lemma count_all_hole2 (N h1 h2 : ℕ) (hh : h1 < h2) :
    ((List.range N).map fun (i : ℕ) => decide (i ≠ h1 ∧ i ≠ h2)).count true =
      if N ≤ h1 then N else if N ≤ h2 then N - 1 else N - 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.count_append, ih]
    simp only [List.map_cons, List.map_nil, List.count_nil, List.count_cons,
      beq_true, decide_eq_true_eq]
    split_ifs <;> omega

def rowCountFormula (t iy : ℕ) : ℕ :=
  if iy = t then 2 * t - 1
  else if iy = 3 ∨ iy = 2 * t - 3 then 6
  else if iy < t then 2 * iy + 1
  else 2 * (2 * t - iy) + 1

lemma row_count_eq (n t : ℕ) (hn : 2 < n) (ht_def : t = 2 ^ n - 1)
    (iy : ℕ) (hiy : iy < 2 * t + 1) :
    (((List.range (2 * t + 1)).map fun (ix : ℕ) =>
      exact950 t ((ix : ℤ) - ↑t) ((iy : ℤ) - ↑t)).count true) =
      rowCountFormula t iy := by
  have hpow8 : 8 ≤ 2 ^ n := two_pow_ge_eight n hn
  have ht7 : 7 ≤ t := by omega
  have ht4 : 2 ^ n - 4 = t - 3 := by omega
  let ay := ((iy : ℤ) - ↑t).natAbs
  have hay_le : ay ≤ t := by
    dsimp [ay]; cases abs_cases ((iy : ℤ) - ↑t) <;> omega
  have hay_val : ay = if iy ≤ t then t - iy else iy - t := by
    dsimp [ay]; split_ifs <;> omega
  by_cases hiy_t : iy = t
  · rw [hiy_t]
    have hmap : ((List.range (2 * t + 1)).map fun (ix : ℕ) =>
        exact950 t ((ix : ℤ) - ↑t) ((t : ℤ) - ↑t)) =
        (List.range (2 * t + 1)).map fun (ix : ℕ) => decide (ix ≠ 3 ∧ ix ≠ 2 * t - 3) := by
      apply List.map_congr_left
      intro ix hix
      rw [List.mem_range] at hix
      rw [ht_def, exact950_two_pow_pred n hn, ← ht_def, ht4, decide_eq_decide]
      have hy0 : ((t : ℤ) - ↑t).natAbs = 0 := by simp
      rw [hy0]
      constructor
      · rintro ⟨_, hno⟩
        refine ⟨?_, ?_⟩ <;> intro hxeq <;> apply hno <;> subst hxeq <;> refine ⟨by omega, Or.inr rfl⟩
      · rintro ⟨hne1, hne2⟩
        refine ⟨by cases abs_cases ((ix : ℤ) - ↑t) <;> omega, ?_⟩
        rintro ⟨hsum, _⟩
        have h1 : (ix : ℤ) - ↑t = ↑(t - 3) ∨ (ix : ℤ) - ↑t = -↑(t - 3) := by omega
        omega
    rw [hmap, count_all_hole2 (2 * t + 1) 3 (2 * t - 3) (by omega)]
    unfold rowCountFormula
    split_ifs <;> omega
  · by_cases hiy_h : iy = 3 ∨ iy = 2 * t - 3
    · have hay3 : ay = t - 3 := by rw [hay_val]; split_ifs <;> omega
      have hmap : ((List.range (2 * t + 1)).map fun (ix : ℕ) =>
          exact950 t ((ix : ℤ) - ↑t) ((iy : ℤ) - ↑t)) =
          (List.range (2 * t + 1)).map fun (ix : ℕ) =>
            decide (t - 3 ≤ ix ∧ ix < t + 4 ∧ ix ≠ t) := by
        apply List.map_congr_left
        intro ix hix
        rw [List.mem_range] at hix
        rw [ht_def, exact950_two_pow_pred n hn, ← ht_def, ht4, decide_eq_decide]
        change (((ix : ℤ) - ↑t).natAbs + ay ≤ t ∧
          ¬(((ix : ℤ) - ↑t).natAbs + ay = t - 3 ∧
            (((ix : ℤ) - ↑t).natAbs = 0 ∨ ay = 0))) ↔ _
        rw [hay3]
        constructor
        · rintro ⟨hle, hno⟩
          refine ⟨by omega, by omega, ?_⟩
          intro hxt; subst hxt
          apply hno; exact ⟨by simp, Or.inl (by simp)⟩
        · rintro ⟨h1, h2, h3⟩
          refine ⟨by omega, ?_⟩
          rintro ⟨hsum, hx0 | hy0⟩ <;> omega
      rw [hmap, count_interval_hole1 (2 * t + 1) (t - 3) (t + 4) t (by omega) (by omega)]
      unfold rowCountFormula
      split_ifs <;> omega
    · have hay_ne3 : ay ≠ t - 3 := by rw [hay_val]; split_ifs <;> omega
      have hay_ne0 : ay ≠ 0 := by rw [hay_val]; split_ifs <;> omega
      have hmap : ((List.range (2 * t + 1)).map fun (ix : ℕ) =>
          exact950 t ((ix : ℤ) - ↑t) ((iy : ℤ) - ↑t)) =
          (List.range (2 * t + 1)).map fun (ix : ℕ) =>
            decide (ay ≤ ix ∧ ix < 2 * t + 1 - ay) := by
        apply List.map_congr_left
        intro ix hix
        rw [List.mem_range] at hix
        rw [ht_def, exact950_two_pow_pred n hn, ← ht_def, ht4, decide_eq_decide]
        change (((ix : ℤ) - ↑t).natAbs + ay ≤ t ∧
          ¬(((ix : ℤ) - ↑t).natAbs + ay = t - 3 ∧
            (((ix : ℤ) - ↑t).natAbs = 0 ∨ ay = 0))) ↔ _
        constructor
        · rintro ⟨hle, _⟩; omega
        · rintro ⟨h1, h2⟩
          refine ⟨by omega, ?_⟩
          rintro ⟨hsum, hx0 | hy0⟩ <;> omega
      rw [hmap, count_interval (2 * t + 1) ay (2 * t + 1 - ay) (by omega)]
      unfold rowCountFormula
      rw [hay_val]
      split_ifs <;> omega

def partialRowSumZ (t N : ℕ) : ℤ :=
  if N ≤ t + 1 then
    (N : ℤ) ^ 2 - (if 3 < N then 1 else 0) - (if t < N then 2 else 0)
  else
    ((t : ℤ) + 1) ^ 2 + 2 * (t : ℤ) * ((N : ℤ) - (t : ℤ) - 1) -
      ((N : ℤ) - (t : ℤ) - 1) ^ 2 - 3 - (if 2 * t - 3 < N then 1 else 0)

lemma sum_rowCountFormulaZ (t : ℕ) (ht : 7 ≤ t) (N : ℕ) (hN : N ≤ 2 * t + 1) :
    (((List.range N).map (rowCountFormula t)).sum : ℤ) = partialRowSumZ t N := by
  induction N with
  | zero => simp [partialRowSumZ]
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Nat.cast_add, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    unfold partialRowSumZ rowCountFormula
    push_cast
    by_cases hNt : N = t
    · rw [hNt]
      have hcast : ((2 * t - 1 : ℕ) : ℤ) = 2 * (t : ℤ) - 1 := by omega
      split_ifs <;> try omega
      all_goals (rw [hcast]; ring)
    · by_cases hN3 : N = 3
      · rw [hN3]
        split_ifs <;> omega
      · by_cases hN2t3 : N = 2 * t - 3
        · have hcastN : (N : ℤ) = 2 * (t : ℤ) - 3 := by omega
          split_ifs <;> try omega
          all_goals (rw [hcastN]; ring)
        · by_cases hlt : N < t
          · split_ifs <;> try omega
            all_goals ring
          · by_cases hNt1 : N = t + 1
            · have hcast1 : ((2 * t - N : ℕ) : ℤ) = (t : ℤ) - 1 := by omega
              split_ifs <;> try omega
              all_goals (rw [hcast1, hNt1]; push_cast; ring)
            · have hgt : t + 1 < N := by omega
              have hcast2 : ((2 * t - N : ℕ) : ℤ) = 2 * (t : ℤ) - (N : ℤ) := by omega
              split_ifs <;> try omega
              all_goals (rw [hcast2]; ring)

theorem OMA.solution : type_of% @OMA.S_oeis_a273828.main := by
  constructor
  · intro n
    unfold a countOn
    rw [stageCfg_1014_eq_950]
  · intro n hn
    unfold a countOn
    rw [stageCfg_eq_gridRows 950 (applyRule_false_0 950 (Or.inl rfl)) (2 ^ n - 1)]
    unfold gridRows
    rw [List.map_map]
    have hpow8 : 8 ≤ 2 ^ n := two_pow_ge_eight n hn
    set t := 2 ^ n - 1 with ht_def
    have ht7 : 7 ≤ t := by omega
    have hrows : List.map ((fun (row : List Bool) => List.count true row) ∘ fun (iy : ℕ) =>
        List.map (fun (ix : ℕ) => stateR 950 t ((ix : ℤ) - ↑t) ((iy : ℤ) - ↑t))
          (List.range (2 * t + 1))) (List.range (2 * t + 1)) =
        List.map (rowCountFormula t) (List.range (2 * t + 1)) := by
      apply List.map_congr_left
      intro iy hiy
      rw [List.mem_range] at hiy
      simp only [Function.comp_apply]
      have hst : (fun (ix : ℕ) => stateR 950 t ((ix : ℤ) - ↑t) ((iy : ℤ) - ↑t)) =
          (fun (ix : ℕ) => exact950 t ((ix : ℤ) - ↑t) ((iy : ℤ) - ↑t)) := by
        funext ix
        exact stateR_eq_exact950 950 (Or.inl rfl) t _ _
      rw [hst]
      exact row_count_eq n t hn ht_def iy hiy
    rw [hrows, sum_rowCountFormulaZ t ht7 (2 * t + 1) (le_refl _)]
    unfold partialRowSumZ
    have hnot : ¬(2 * t + 1 ≤ t + 1) := by omega
    have hlt3 : 2 * t - 3 < 2 * t + 1 := by omega
    simp only [hnot, hlt3, ↓reduceIte]
    push_cast
    have hpow4 : (4 : ℤ) ^ n = ((2 : ℤ) ^ n) ^ 2 := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
    have ht_int : (t : ℤ) = (2 : ℤ) ^ n - 1 := by
      rw [ht_def, Nat.cast_sub (by omega), Nat.cast_pow]; simp
    rw [ht_int, hpow4]
    ring

end Proof_a273828

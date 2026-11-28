import OMAStatements.S_oeis_a283604

-- The contributor supplied the moving-window argument with ChatGPT assistance.
open OMA.S_oeis_a283604

namespace Rule670

def update (c e w n s : Bool) : Bool :=
  (670 : ℕ).testBit (c.toNat + 2 * (e.toNat + w.toNat + n.toNat + s.toNat))

theorem cell_step (t : ℕ) (x y : ℤ) :
    cell 670 (t + 1) x y =
      update (cell 670 t x y) (cell 670 t (x + 1) y) (cell 670 t (x - 1) y)
        (cell 670 t x (y + 1)) (cell 670 t x (y - 1)) := rfl

theorem outside (t : ℕ) (x y : ℤ) (h : (t : ℤ) < |x| + |y|) :
    cell 670 t x y = false := by
  induction t generalizing x y with
  | zero =>
    simp only [cell, decide_eq_false_iff_not]
    rintro ⟨rfl, rfl⟩
    simp at h
  | succ t ih =>
    have hx₁ : |x| ≤ |x + 1| + 1 := by
      simpa using (abs_sub (x + 1) (1 : ℤ))
    have hx₂ : |x| ≤ |x - 1| + 1 := by
      simpa using (abs_add_le (x - 1) (1 : ℤ))
    have hy₁ : |y| ≤ |y + 1| + 1 := by
      simpa using (abs_sub (y + 1) (1 : ℤ))
    have hy₂ : |y| ≤ |y - 1| + 1 := by
      simpa using (abs_add_le (y - 1) (1 : ℤ))
    rw [cell_step, ih x y (by omega), ih (x + 1) y (by omega),
      ih (x - 1) y (by omega), ih x (y + 1) (by omega), ih x (y - 1) (by omega)]
    rfl

theorem reflectX (t : ℕ) (x y : ℤ) : cell 670 t (-x) y = cell 670 t x y := by
  induction t generalizing x y with
  | zero => simp [cell]
  | succ t ih =>
    rw [cell_step, cell_step, show -x + 1 = -(x - 1) by omega,
      show -x - 1 = -(x + 1) by omega, ih, ih, ih, ih, ih]
    unfold update
    rw [add_comm (cell 670 t (x - 1) y).toNat (cell 670 t (x + 1) y).toNat]

-- Use distance from the east front as the horizontal coordinate.
def front (t : ℕ) (k y : ℤ) : Bool := cell 670 t ((t : ℤ) - k) y

theorem front_off (t : ℕ) (k y : ℤ) (h : k < |y|) : front t k y = false := by
  apply outside
  have := le_abs_self ((t : ℤ) - k)
  omega

theorem front_step (t : ℕ) (k y : ℤ) :
    front (t + 1) k y = update (front t (k - 1) y) (front t (k - 2) y) (front t k y)
      (front t (k - 1) (y + 1)) (front t (k - 1) (y - 1)) := by
  unfold front
  rw [cell_step]
  push_cast
  congr 1 <;> congr 1 <;> omega

abbrev Grid := Array (Array Bool)

-- Cells outside the light cone are masked when reading a finite window.
def makeGrid (cap : ℕ) (f : ℤ → ℤ → Bool) : Grid :=
  Array.ofFn fun k : Fin (cap + 1) =>
    Array.ofFn fun j : Fin (2 * cap + 1) => f (k.val : ℤ) ((j.val : ℤ) - cap)

def readGrid (cap : ℕ) (g : Grid) (k y : ℤ) : Bool :=
  if 0 ≤ k ∧ k ≤ (cap : ℤ) ∧ |y| ≤ k then
    ((g[k.toNat]?).getD #[])[(y + (cap : ℤ)).toNat]?.getD false
  else false

theorem read_make (cap : ℕ) (f : ℤ → ℤ → Bool) (k y : ℤ)
    (hk : k ≤ (cap : ℤ)) (hy : |y| ≤ k) : readGrid cap (makeGrid cap f) k y = f k y := by
  have h0 : 0 ≤ k := (abs_nonneg y).trans hy
  have hlo := neg_abs_le y
  have hhi := le_abs_self y
  have hk' : k.toNat < cap + 1 := by omega
  have hy' : (y + (cap : ℤ)).toNat < 2 * cap + 1 := by omega
  simp [readGrid, makeGrid, h0, hk, hy, hk', hy',
    Int.toNat_of_nonneg (show 0 ≤ y + (cap : ℤ) by omega)]

def advance (cap : ℕ) (g : Grid) : Grid :=
  makeGrid cap fun k y =>
    update (readGrid cap g (k - 1) y) (readGrid cap g (k - 2) y) (readGrid cap g k y)
      (readGrid cap g (k - 1) (y + 1)) (readGrid cap g (k - 1) (y - 1))

def grid (cap : ℕ) : ℕ → Grid
  | 0 => makeGrid cap fun k y => decide (k = 0 ∧ y = 0)
  | t + 1 => advance cap (grid cap t)

theorem grid_correct (cap t : ℕ) (k y : ℤ) (hk : k ≤ (cap : ℤ)) :
    readGrid cap (grid cap t) k y = front t k y := by
  induction t generalizing k y with
  | zero =>
    by_cases hy : |y| ≤ k
    · rw [grid, read_make cap _ k y hk hy]
      simp [front, cell]
    · rw [front_off _ _ _ (by omega)]
      simp [readGrid, hy]
  | succ t ih =>
    by_cases hy : |y| ≤ k
    · rw [grid, advance, read_make cap _ k y hk hy, front_step,
        ih (k - 1) y (by omega), ih (k - 2) y (by omega), ih k y hk,
        ih (k - 1) (y + 1) (by omega), ih (k - 1) (y - 1) (by omega)]
    · rw [front_off _ _ _ (by omega)]
      simp [readGrid, hy]

def stripCheck (cap : ℕ) (g : Grid) (lo width : ℕ) : Bool :=
  (List.range' lo width).all fun k =>
    readGrid cap g k (-1) && readGrid cap g k 0 && readGrid cap g k 1

theorem stripCheck_read (cap : ℕ) (g : Grid) (lo width k : ℕ)
    (h : stripCheck cap g lo width = true) (hk : lo ≤ k) (hk' : k < lo + width)
    (y : ℤ) (hy : |y| ≤ 1) : readGrid cap g k y = true := by
  have hrow := List.all_eq_true.mp h k (List.mem_range'_1.2 ⟨hk, hk'⟩)
  obtain ⟨hm, hp⟩ := abs_le.mp hy
  have hc : y = -1 ∨ y = 0 ∨ y = 1 := by omega
  rcases hc with rfl | rfl | rfl <;> simp_all only [Bool.and_eq_true_iff]

def bandCheck (g : Grid) (even : Bool) : Bool :=
  (List.range 7).all (fun k => readGrid 6 g k 0 == !(even && (k == 3))) &&
    stripCheck 6 g 5 2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1500000 in
theorem cycle : grid 6 16 = grid 6 12 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1500000 in
theorem band_start :
    bandCheck (grid 6 12) true = true ∧ bandCheck (grid 6 13) false = true ∧
    bandCheck (grid 6 14) true = true ∧ bandCheck (grid 6 15) false = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1500000 in
theorem strip_start : stripCheck 17 (grid 17 15) 5 11 = true := by decide +kernel

theorem grid_period (t : ℕ) (ht : 12 ≤ t) : grid 6 (t + 4) = grid 6 t := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases ht' : 12 ≤ t
    · change advance 6 (grid 6 (t + 4)) = advance 6 (grid 6 t)
      rw [ih ht']
    · have h : t + 1 = 12 := by omega
      change grid 6 ((t + 1) + 4) = grid 6 (t + 1)
      rw [h]
      exact cycle

theorem band_valid (t : ℕ) (ht : 12 ≤ t) :
    bandCheck (grid 6 t) (t % 2 == 0) = true := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases hlo : t < 16
    · interval_cases t
      · exact band_start.1
      · exact band_start.2.1
      · exact band_start.2.2.1
      · exact band_start.2.2.2
    · have hp := grid_period (t - 4) (by omega)
      have hs : t - 4 + 4 = t := by omega
      have hm : t % 2 = (t - 4) % 2 := by omega
      rw [hs] at hp
      rw [hp, hm]
      exact ih _ (by omega) (by omega)

theorem front_strip (t : ℕ) (ht : 12 ≤ t) (k y : ℤ)
    (hk : 5 ≤ k) (hk' : k ≤ 6) (hy : |y| ≤ 1) : front t k y = true := by
  have hv := band_valid t ht
  simp only [bandCheck, Bool.and_eq_true_iff] at hv
  have h := hv.2
  rw [← grid_correct 6 t k y (by norm_num; omega)]
  have hr := stripCheck_read 6 (grid 6 t) 5 2 k.toNat h (by omega) (by omega) y hy
  rwa [Int.toNat_of_nonneg (show 0 ≤ k by omega)] at hr

theorem front_axis (t k : ℕ) (ht : 12 ≤ t) (hk : k ≤ 6) :
    front t k 0 = !( (t % 2 == 0) && (k == 3)) := by
  have hv := band_valid t ht
  simp only [bandCheck, Bool.and_eq_true_iff] at hv
  have h := hv.1
  have hr := List.all_eq_true.mp h k (List.mem_range.2 (by omega))
  rw [← grid_correct 6 t k 0 (by exact_mod_cast hk)]
  exact beq_iff_eq.mp hr

-- Near the front use the period. Further inside, three ON neighbours suffice.
theorem strip_positive (t : ℕ) (ht : 15 ≤ t) (x y : ℤ)
    (hx : 0 ≤ x) (hx' : x ≤ (t : ℤ) - 5) (hy : |y| ≤ 1) :
    cell 670 t x y = true := by
  induction t generalizing x y with
  | zero => omega
  | succ t ih =>
    by_cases ht' : 15 ≤ t
    · by_cases edge : (t : ℤ) - 6 < x
      · let k : ℤ := (t : ℤ) + 1 - x
        have hs := front_strip (t + 1) (by omega) k y (by dsimp [k]; push_cast at hx'; omega)
          (by dsimp [k]; omega) hy
        unfold front at hs
        convert hs using 2 <;> push_cast <;> dsimp [k] <;> omega
      · have old (u v : ℤ) (hu : |u| ≤ (t : ℤ) - 5) (hv : |v| ≤ 1) :
            cell 670 t u v = true := by
          by_cases h : 0 ≤ u
          · exact ih ht' u v h ((le_abs_self u).trans hu) hv
          · rw [← reflectX t u v]
            exact ih ht' (-u) v (by omega) ((neg_le_abs u).trans hu) hv
        have center := old x y (by rw [abs_le]; omega) hy
        have east := old (x + 1) y (by rw [abs_le]; omega) hy
        have west := old (x - 1) y (by rw [abs_le]; omega) hy
        rw [cell_step, center, east, west]
        rw [abs_le] at hy
        by_cases h : 0 ≤ y
        · rw [old x (y - 1) (by rw [abs_le]; omega) (by rw [abs_le]; omega)]
          cases cell 670 t x (y + 1) <;> rfl
        · rw [old x (y + 1) (by rw [abs_le]; omega) (by rw [abs_le]; omega)]
          cases cell 670 t x (y - 1) <;> rfl
    · have ht15 : t + 1 = 15 := by omega
      rw [ht15] at hx' ⊢
      let k : ℤ := 15 - x
      have hread := stripCheck_read 17 (grid 17 15) 5 11 k.toNat strip_start
        (by dsimp [k]; norm_num at hx'; omega) (by dsimp [k]; omega) y hy
      rw [Int.toNat_of_nonneg (show 0 ≤ k by dsimp [k]; norm_num at hx'; omega),
        grid_correct 17 15 k y (by dsimp [k]; norm_num; omega)] at hread
      unfold front at hread
      convert hread using 2 <;> norm_num <;> dsimp [k] <;> omega

theorem axis_pattern (n k : ℕ) (hn : 15 ≤ n) (hk : k ≤ n) :
    cell 670 n ((k : ℤ) - n) 0 = !( (n % 2 == 0) && (k == 3)) := by
  rw [← reflectX]
  have hneg : -((k : ℤ) - n) = (n : ℤ) - k := by omega
  rw [hneg]
  by_cases h : k ≤ 6
  · exact front_axis n k (by omega) h
  · rw [strip_positive n hn _ _ (by omega) (by omega) (by norm_num)]
    have hk3 : k ≠ 3 := by omega
    simp [hk3]

open PowerSeries

def repunit (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (10 : ℤ) ^ k

theorem repunit_step (n : ℕ) : repunit (n + 2) = 100 * repunit n + 11 := by
  have h (m : ℕ) : repunit m * (10 - 1) = 10 ^ (m + 1) - 1 := by
    exact geom_sum_mul (10 : ℤ) (m + 1)
  have hh := h (n + 2)
  rw [show n + 2 + 1 = n + 1 + 2 by omega, pow_add] at hh
  norm_num at hh ⊢
  linarith [h n]

theorem a_value (n : ℕ) (hn : 15 ≤ n) :
    a n = repunit n - (if n % 2 = 0 then (10 : ℤ) ^ (n - 3) else 0) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      (if cell 670 n ((k : ℤ) - n) 0 then (10 : ℤ) ^ (n - k) else 0) =
        (10 : ℤ) ^ (n - k) -
          (if n % 2 = 0 ∧ k = 3 then (10 : ℤ) ^ (n - k) else 0) := by
    rw [axis_pattern n k hn (by have := Finset.mem_range.mp hk; omega)]
    by_cases h : n % 2 = 0 <;> by_cases h' : k = 3 <;> simp [h, h']
  unfold a
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  have href := Finset.sum_range_reflect (fun k => (10 : ℤ) ^ k) (n + 1)
  simp only [Nat.add_sub_cancel] at href
  rw [href]
  change repunit n - _ = repunit n - _
  by_cases h : n % 2 = 0
  · simp [h, Finset.sum_ite_eq', Finset.mem_range, show 3 < n + 1 by omega]
  · simp [h]

-- Two steps append two ones and shift any even-time defect by two places.
theorem a_step2 (n : ℕ) (hn : 15 ≤ n) : a (n + 2) = 100 * a n + 11 := by
  rw [a_value (n + 2) (by omega), a_value n hn, repunit_step]
  rw [show (n + 2) % 2 = n % 2 by omega, show n + 2 - 3 = (n - 3) + 2 by omega, pow_add]
  split <;> ring

theorem recurrence (n : ℕ) (hn : 18 ≤ n) :
    (a n : ℚ) = a (n - 1) + 100 * a (n - 2) - 100 * a (n - 3) := by
  have h1 := a_step2 (n - 2) (by omega)
  have h2 := a_step2 (n - 3) (by omega)
  rw [show n - 2 + 2 = n by omega] at h1
  rw [show n - 3 + 2 = n - 1 by omega] at h2
  exact_mod_cast (by linarith : a n = a (n - 1) + 100 * a (n - 2) - 100 * a (n - 3))

def gridValue (g : Grid) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if readGrid 17 g (k : ℤ) 0 then (10 : ℤ) ^ (n - k) else 0

theorem gridValue_correct (n : ℕ) (hn : n ≤ 17) : a n = gridValue (grid 17 n) n := by
  unfold a gridValue
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [grid_correct 17 n k 0 (by omega)]
  unfold front
  rw [← reflectX n ((k : ℤ) - n) 0, show -((k : ℤ) - n) = (n : ℤ) - k by omega]

def table : Array ℤ :=
  #[1, 11, 111, 1111, 11101, 111111, 1110111, 11111111, 111011101, 1111111111,
    11101111011, 111111111111, 1110111110011, 11111111111111, 111011111111011,
    1111111111111111, 11101111111111111, 111111111111111111]

def checkInitial : ℕ → ℕ → Grid → Bool
  | 0, _, _ => true
  | fuel + 1, n, g =>
    (gridValue g n == table[n]?.getD 0) && checkInitial fuel (n + 1) (advance 17 g)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 2500000 in
theorem table_verified : checkInitial 18 0 (grid 17 0) = true := by decide +kernel

theorem initial_at (fuel start n : ℕ) (hn : start ≤ n) (hl : n < start + fuel)
    (h : checkInitial fuel start (grid 17 start) = true) :
    gridValue (grid 17 n) n = table[n]?.getD 0 := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
    have hs := Bool.and_eq_true_iff.mp h
    by_cases he : n = start
    · subst n
      exact beq_iff_eq.mp hs.1
    · exact ih (start + 1) (by omega) (by omega) hs.2

theorem a_initial (n : ℕ) (h : n < 18) : a n = table[n]?.getD 0 := by
  rw [gridValue_correct n (by omega)]
  exact initial_at 18 0 n (by omega) (by omega) table_verified

def series : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

noncomputable def numerator : ℚ⟦X⟧ :=
  -10000 * X ^ 17 + 10000 * X ^ 16 - 109900 * X ^ 15 + 109900 * X ^ 14 -
    8900 * X ^ 13 + 8900 * X ^ 12 - 900 * X ^ 11 + 900 * X ^ 10 + 10 * X ^ 9 -
    10 * X ^ 8 + 10 * X ^ 5 - 10 * X ^ 4 + 10 * X + 1

theorem series_mul_coeff (n d : ℕ) (q : ℚ) :
    coeff n (series * (C q * X ^ d)) = if d ≤ n then (a (n - d) : ℚ) * q else 0 := by
  rw [← mul_assoc, PowerSeries.coeff_mul_X_pow']
  by_cases h : d ≤ n
  · simp [series, h, PowerSeries.coeff_mul_C]
  · simp [h]

theorem generating :
    series * ((X - 1) * (10 * X - 1) * (10 * X + 1) : ℚ⟦X⟧) = numerator := by
  have hd : ((X - 1) * (10 * X - 1) * (10 * X + 1) : ℚ⟦X⟧) =
      C 1 * X ^ 0 - C 1 * X ^ 1 - C 100 * X ^ 2 + C 100 * X ^ 3 := by
    simp only [map_ofNat, map_one]
    ring
  have hnum : numerator =
      C (-10000) * X ^ 17 + C 10000 * X ^ 16 + C (-109900) * X ^ 15 +
        C 109900 * X ^ 14 + C (-8900) * X ^ 13 + C 8900 * X ^ 12 +
        C (-900) * X ^ 11 + C 900 * X ^ 10 + C 10 * X ^ 9 + C (-10) * X ^ 8 +
        C 10 * X ^ 5 + C (-10) * X ^ 4 + C 10 * X ^ 1 + C 1 * X ^ 0 := by
    unfold numerator
    simp only [map_ofNat, map_one, map_neg]
    ring
  rw [hd, hnum]
  ext n
  simp only [mul_add, mul_sub, map_add, map_sub, series_mul_coeff, PowerSeries.coeff_C_mul_X_pow]
  by_cases h : n < 18
  · interval_cases n <;> norm_num [a_initial, table]
  · have hn : 18 ≤ n := by omega
    have hl (m : ℕ) (hm : m < 18) : n ≠ m := by omega
    simp only [if_pos (show 0 ≤ n by omega), if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega), Nat.sub_zero, mul_one,
      if_neg (hl 17 (by decide)), if_neg (hl 16 (by decide)), if_neg (hl 15 (by decide)),
      if_neg (hl 14 (by decide)), if_neg (hl 13 (by decide)), if_neg (hl 12 (by decide)),
      if_neg (hl 11 (by decide)), if_neg (hl 10 (by decide)), if_neg (hl 9 (by decide)),
      if_neg (hl 8 (by decide)), if_neg (hl 5 (by decide)), if_neg (hl 4 (by decide)),
      if_neg (hl 1 (by decide)), if_neg (hl 0 (by decide)), add_zero]
    linarith [recurrence n hn]

end Rule670

theorem OMA.solution : type_of% @OMA.S_oeis_a283604.main := by
  exact ⟨Rule670.recurrence, Rule670.generating⟩


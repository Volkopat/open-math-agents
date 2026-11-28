import OMAStatements.S_oeis_a283606

-- Problem: A283606: Decimal representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 670', based on the 5-celled von Neumann neighborhood.
-- Upstream: formal-conjectures statements/oeis-a283606.lean:0 (declaration OMA.S_oeis_a283606.main)
-- Reuses the Rule 670 moving-window and 3-row strip strategy from @yugo19787's merged A283604 (PR #25962) and A283607 (PR #28115) proofs, adapted to symmetric half-grid arrays and the left-axis base-2 reading.
-- Credit: @yugo19787
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a283606

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

theorem swapXY (t : ℕ) (x y : ℤ) : cell 670 t x y = cell 670 t y x := by
  induction t generalizing x y with
  | zero => simp [cell, and_comm]
  | succ t ih =>
    rw [cell_step, cell_step, ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y + 1), ih x (y - 1)]
    unfold update
    ac_rfl

theorem reflectY (t : ℕ) (x y : ℤ) : cell 670 t x (-y) = cell 670 t x y := by
  rw [swapXY t x (-y), reflectX, swapXY t y x]

-- Use distance from the east front as the horizontal coordinate.
def front (t : ℕ) (k y : ℤ) : Bool := cell 670 t ((t : ℤ) - k) y

theorem front_off (t : ℕ) (k y : ℤ) (h : k < |y|) : front t k y = false := by
  apply outside
  have := le_abs_self ((t : ℤ) - k)
  omega

theorem front_abs (t : ℕ) (k y : ℤ) : front t k |y| = front t k y := by
  by_cases h : 0 ≤ y
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (by omega)]
    exact reflectY _ _ _

theorem front_step (t : ℕ) (k y : ℤ) :
    front (t + 1) k y = update (front t (k - 1) y) (front t (k - 2) y) (front t k y)
      (front t (k - 1) (y + 1)) (front t (k - 1) (y - 1)) := by
  unfold front
  rw [cell_step]
  push_cast
  congr 1 <;> congr 1 <;> omega

abbrev Grid := Array (Array Bool)

-- Symmetric half-grid: row k stores y ∈ [0, k] using y.natAbs.
def makeGrid (cap : ℕ) (f : ℤ → ℤ → Bool) : Grid :=
  Array.ofFn fun k : Fin (cap + 1) =>
    Array.ofFn fun j : Fin (k.val + 1) => f (k.val : ℤ) (j.val : ℤ)

def readGrid (cap : ℕ) (g : Grid) (k y : ℤ) : Bool :=
  if 0 ≤ k ∧ k ≤ (cap : ℤ) ∧ |y| ≤ k then
    ((g[k.toNat]?).getD #[])[y.natAbs]?.getD false
  else false

theorem read_make (cap : ℕ) (f : ℤ → ℤ → Bool) (k y : ℤ)
    (hk : k ≤ (cap : ℤ)) (hy : |y| ≤ k) :
    readGrid cap (makeGrid cap f) k y = f k |y| := by
  have h0 : 0 ≤ k := (abs_nonneg y).trans hy
  have hk' : k.toNat < cap + 1 := by omega
  have hc : (y.natAbs : ℤ) = |y| := by simp
  have hy' : y.natAbs < k.toNat + 1 := by omega
  simp [readGrid, makeGrid, h0, hk, hy, hk', hy']

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
    · rw [grid, advance, read_make cap _ k y hk hy, ← front_abs (t + 1) k y,
        front_step, ih (k - 1) |y| (by omega), ih (k - 2) |y| (by omega), ih k |y| hk,
        ih (k - 1) (|y| + 1) (by omega), ih (k - 1) (|y| - 1) (by omega)]
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

def checkBandLoop : ℕ → ℕ → Grid → Bool
  | 0, _, _ => true
  | fuel + 1, t, g =>
    bandCheck g (t % 2 == 0) && checkBandLoop fuel (t + 1) (advance 6 g)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1500000 in
theorem cycle : grid 6 16 = grid 6 12 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1500000 in
theorem band_loop_verified : checkBandLoop 4 12 (grid 6 12) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1500000 in
theorem strip_start : stripCheck 17 (grid 17 15) 5 11 = true := by decide +kernel

theorem band_at (fuel start t : ℕ) (ht : start ≤ t) (hl : t < start + fuel)
    (h : checkBandLoop fuel start (grid 6 start) = true) :
    bandCheck (grid 6 t) (t % 2 == 0) = true := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
    have hs := Bool.and_eq_true_iff.mp h
    by_cases he : t = start
    · subst t; exact hs.1
    · exact ih (start + 1) (by omega) (by omega) hs.2

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
    · exact band_at 4 12 t ht hlo band_loop_verified
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
    front t k 0 = !((t % 2 == 0) && (k == 3)) := by
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
        convert hs using 2
        push_cast; dsimp [k]; omega
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
      convert hread using 2
      norm_num; dsimp [k]; omega

theorem axis_pattern (n k : ℕ) (hn : 15 ≤ n) (hk : k ≤ n) :
    front n k 0 = !((n % 2 == 0) && (k == 3)) := by
  by_cases h : k ≤ 6
  · exact front_axis n k (by omega) h
  · unfold front
    rw [strip_positive n hn _ _ (by omega) (by omega) (by norm_num)]
    have hk3 : k ≠ 3 := by omega
    simp [hk3]

open PowerSeries

-- In the left-axis reading, cell (k - n, 0) equals front n k 0 by X-reflection.
theorem a_front (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n + 1), if front n k 0 then (2 : ℤ) ^ (n - k) else 0 := by
  unfold a
  apply Finset.sum_congr rfl
  intro k _
  have hrx : cell 670 n ((k : ℤ) - n) 0 = front n k 0 := by
    unfold front
    rw [← reflectX n ((k : ℤ) - n) 0]
    congr 1; omega
  rw [hrx]

theorem a_value (n : ℕ) (hn : 15 ≤ n) :
    a n = (2 : ℤ) ^ (n + 1) - 1 - (if n % 2 = 0 then (2 : ℤ) ^ (n - 3) else 0) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      (if front n k 0 then (2 : ℤ) ^ (n - k) else 0) =
        (2 : ℤ) ^ (n - k) - (if n % 2 = 0 ∧ k = 3 then (2 : ℤ) ^ (n - 3) else 0) := by
    rw [axis_pattern n k hn (by have := Finset.mem_range.mp hk; omega)]
    by_cases h : n % 2 = 0 <;> by_cases h' : k = 3 <;> simp [h, h']
  rw [a_front, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  have href := Finset.sum_range_reflect (fun k : ℕ => (2 : ℤ) ^ k) (n + 1)
  simp only [Nat.add_sub_cancel] at href
  have hsum : (∑ k ∈ Finset.range (n + 1), (2 : ℤ) ^ k) = 2 ^ (n + 1) - 1 := by
    simpa using geom_sum_mul (2 : ℤ) (n + 1)
  rw [href, hsum]
  by_cases h : n % 2 = 0
  · have hsum3 : (∑ k ∈ Finset.range (n + 1), if n % 2 = 0 ∧ k = 3 then (2 : ℤ) ^ (n - 3) else 0) =
        (2 : ℤ) ^ (n - 3) := by
      rw [Finset.sum_eq_single 3]
      · simp [h]
      · intro b _ hb; simp [hb]
      · intro hn3; exact absurd (Finset.mem_range.mpr (by omega)) hn3
    rw [if_pos h, hsum3]
  · simp [h]

theorem a_difference (n : ℕ) (hn : 15 ≤ n) :
    a (n + 2) - 4 * a n = 3 := by
  rw [a_value (n + 2) (by omega), a_value n hn]
  have hp1 : (2 : ℤ) ^ (n + 2 + 1) = 4 * (2 : ℤ) ^ (n + 1) := by
    rw [show n + 2 + 1 = (n + 1) + 2 by omega, pow_add]; ring
  by_cases h : n % 2 = 0
  · have h' : (n + 2) % 2 = 0 := by omega
    have hp2 : (2 : ℤ) ^ (n + 2 - 3) = 4 * (2 : ℤ) ^ (n - 3) := by
      rw [show n + 2 - 3 = (n - 3) + 2 by omega, pow_add]; ring
    simp only [if_pos h', if_pos h, hp1, hp2]
    ring
  · have h' : (n + 2) % 2 ≠ 0 := by omega
    simp only [if_neg h', if_neg h, hp1]
    ring

theorem recurrence (n : ℕ) (hn : 18 ≤ n) :
    (a n : ℚ) = a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3) := by
  have h1 := a_difference (n - 2) (by omega)
  have h2 := a_difference (n - 3) (by omega)
  rw [show n - 2 + 2 = n by omega] at h1
  rw [show n - 3 + 2 = n - 1 by omega] at h2
  exact_mod_cast (by linarith : a n = a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3))

def gridValue (g : Grid) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if readGrid 17 g (k : ℤ) 0 then (2 : ℤ) ^ (n - k) else 0

theorem gridValue_correct (n : ℕ) (hn : n ≤ 17) : a n = gridValue (grid 17 n) n := by
  rw [a_front]
  unfold gridValue
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [grid_correct 17 n k 0 (by omega)]

def table : Array ℤ :=
  #[1, 3, 7, 15, 29, 63, 119, 255, 477, 1023, 1915, 4095, 7667, 16383, 30715,
    65535, 122879, 262143]

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
  -16 * X ^ 17 + 16 * X ^ 16 - 44 * X ^ 15 + 44 * X ^ 14 - 4 * X ^ 13 + 4 * X ^ 12 -
    4 * X ^ 11 + 4 * X ^ 10 + 2 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 5 - 2 * X ^ 4 + 2 * X + 1

def numCoeff : ℕ → ℤ
  | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 0 | 4 => -2 | 5 => 2 | 6 => 0 | 7 => 0
  | 8 => -2 | 9 => 2 | 10 => 4 | 11 => -4 | 12 => 4 | 13 => -4 | 14 => 44
  | 15 => -44 | 16 => 16 | 17 => -16 | _ => 0

theorem gen_init_ok : ∀ n : Fin 18,
    ((if 3 ≤ n.val then table[n.val - 3]?.getD 0 * 4 else 0) -
     (if 2 ≤ n.val then table[n.val - 2]?.getD 0 * 4 else 0) -
     (if 1 ≤ n.val then table[n.val - 1]?.getD 0 else 0) +
     table[n.val]?.getD 0) == numCoeff n.val := by decide

theorem numerator_eq : numerator = ∑ k ∈ Finset.range 18, C (numCoeff k : ℚ) * X ^ k := by
  unfold numerator
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, numCoeff]
  norm_num
  simp only [map_ofNat]
  ring

theorem series_mul_coeff (n d : ℕ) (q : ℚ) :
    coeff n (series * (C q * X ^ d)) = if d ≤ n then (a (n - d) : ℚ) * q else 0 := by
  rw [← mul_assoc, PowerSeries.coeff_mul_X_pow']
  by_cases h : d ≤ n
  · simp [series, h, PowerSeries.coeff_mul_C]
  · simp [h]

theorem generating :
    series * ((X - 1) * (2 * X - 1) * (2 * X + 1) : ℚ⟦X⟧) = numerator := by
  have hd : ((X - 1) * (2 * X - 1) * (2 * X + 1) : ℚ⟦X⟧) =
      C 4 * X ^ 3 - C 4 * X ^ 2 - C 1 * X ^ 1 + C 1 * X ^ 0 := by
    simp only [map_ofNat, map_one]
    ring
  rw [hd, numerator_eq]
  ext n
  simp only [mul_add, mul_sub, map_add, map_sub, map_sum, series_mul_coeff,
    PowerSeries.coeff_C_mul_X_pow]
  by_cases h : n < 18
  · have hrhs : (∑ x ∈ Finset.range 18, if n = x then (numCoeff x : ℚ) else 0) =
        (numCoeff n : ℚ) := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro b _ hb; simp [hb.symm]
      · intro hn; exact absurd (Finset.mem_range.mpr h) hn
    rw [hrhs]
    simp only [Nat.sub_zero, mul_one, show 0 ≤ n by omega, ↓reduceIte]
    have h0 : a n = table[n]?.getD 0 := a_initial n h
    have h1 : (if 1 ≤ n then (a (n - 1) : ℚ) else 0) =
        ((if 1 ≤ n then table[n - 1]?.getD 0 else 0 : ℤ) : ℚ) := by
      split_ifs with h1' <;> simp [a_initial, show n - 1 < 18 by omega]
    have h2 : (if 2 ≤ n then (a (n - 2) : ℚ) * 4 else 0) =
        ((if 2 ≤ n then table[n - 2]?.getD 0 * 4 else 0 : ℤ) : ℚ) := by
      split_ifs with h2' <;> simp [a_initial, show n - 2 < 18 by omega]
    have h3 : (if 3 ≤ n then (a (n - 3) : ℚ) * 4 else 0) =
        ((if 3 ≤ n then table[n - 3]?.getD 0 * 4 else 0 : ℤ) : ℚ) := by
      split_ifs with h3' <;> simp [a_initial, show n - 3 < 18 by omega]
    have hok := beq_iff_eq.mp (gen_init_ok ⟨n, h⟩)
    have hokq : ((if 3 ≤ n then table[n - 3]?.getD 0 * 4 else 0 : ℤ) : ℚ) -
        ((if 2 ≤ n then table[n - 2]?.getD 0 * 4 else 0 : ℤ) : ℚ) -
        ((if 1 ≤ n then table[n - 1]?.getD 0 else 0 : ℤ) : ℚ) +
        (table[n]?.getD 0 : ℚ) = (numCoeff n : ℚ) := by
      exact_mod_cast hok
    rw [h0, h1, h2, h3]
    exact hokq
  · have hn : 18 ≤ n := by omega
    have hrhs : (∑ x ∈ Finset.range 18, if n = x then (numCoeff x : ℚ) else 0) = 0 :=
      Finset.sum_eq_zero fun x hx => if_neg (by have := Finset.mem_range.mp hx; omega)
    rw [hrhs]
    simp only [if_pos (show 0 ≤ n by omega), if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega), Nat.sub_zero, mul_one]
    linarith [recurrence n hn]

end Rule670

theorem OMA.solution : type_of% @OMA.S_oeis_a283606.main := by
  refine ⟨Rule670.recurrence, ?_⟩
  simpa [Rule670.series, Rule670.numerator] using Rule670.generating

import OMAStatements.S_oeis_a279701

-- Problem: A279701: Decimal representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellul
-- Upstream: formal-conjectures statements/oeis-a279701.lean:0 (declaration OMA.S_oeis_a279701.main)
-- Credit: @yugo19787 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a279701

namespace Rule185

def update (c e w n s : Bool) : Bool :=
  (185 : ℕ).testBit (c.toNat + 2 * (e.toNat + w.toNat + n.toNat + s.toNat))

theorem cell_step (t : ℕ) (x y : ℤ) :
    cell 185 (t + 1) x y =
      update (cell 185 t x y) (cell 185 t (x + 1) y) (cell 185 t (x - 1) y)
        (cell 185 t x (y + 1)) (cell 185 t x (y - 1)) := rfl

def bg (t : ℕ) : Bool := decide (t % 2 = 1)

theorem bg_step (t : ℕ) : update (bg t) (bg t) (bg t) (bg t) (bg t) = bg (t + 1) := by
  have h : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases h with h | h
  · simp [bg, h, show (t + 1) % 2 = 1 by omega, update]
  · simp [bg, h, show (t + 1) % 2 ≠ 1 by omega, update]
    decide

theorem outside (t : ℕ) (x y : ℤ) (h : (t : ℤ) < |x| + |y|) :
    cell 185 t x y = bg t := by
  induction t generalizing x y with
  | zero =>
    simp only [bg, Nat.zero_mod, Nat.zero_ne_one, decide_false, cell, decide_eq_false_iff_not]
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
    exact bg_step t

theorem reflectX (t : ℕ) (x y : ℤ) : cell 185 t (-x) y = cell 185 t x y := by
  induction t generalizing x y with
  | zero => simp [cell]
  | succ t ih =>
    rw [cell_step, cell_step, show -x + 1 = -(x - 1) by omega,
      show -x - 1 = -(x + 1) by omega, ih, ih, ih, ih, ih]
    unfold update
    rw [add_comm (cell 185 t (x - 1) y).toNat (cell 185 t (x + 1) y).toNat]

theorem swapXY (t : ℕ) (x y : ℤ) : cell 185 t x y = cell 185 t y x := by
  induction t generalizing x y with
  | zero => simp [cell, and_comm]
  | succ t ih =>
    rw [cell_step, cell_step, ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y + 1), ih x (y - 1)]
    unfold update
    ac_rfl

theorem reflectY (t : ℕ) (x y : ℤ) : cell 185 t x (-y) = cell 185 t x y := by
  rw [swapXY t x (-y), reflectX, swapXY t y x]

-- Use distance from the east front as the horizontal coordinate.
def front (t : ℕ) (k y : ℤ) : Bool := cell 185 t ((t : ℤ) - k) y

theorem front_bg (t : ℕ) (k y : ℤ) (h : k < |y|) : front t k y = bg t := by
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
    Array.ofFn fun j : Fin (k.val + 1) => f (k.val : ℤ) (j.val : ℤ)

def readGrid (cap t : ℕ) (g : Grid) (k y : ℤ) : Bool :=
  if 0 ≤ k ∧ k ≤ (cap : ℤ) ∧ |y| ≤ k then
    ((g[k.toNat]?).getD #[])[y.natAbs]?.getD false
  else bg t

theorem read_make (cap t : ℕ) (f : ℤ → ℤ → Bool) (k y : ℤ)
    (hk : k ≤ (cap : ℤ)) (hy : |y| ≤ k) :
    readGrid cap t (makeGrid cap f) k y = f k |y| := by
  have h0 : 0 ≤ k := (abs_nonneg y).trans hy
  have hk' : k.toNat < cap + 1 := by omega
  have hc : (y.natAbs : ℤ) = |y| := by simp
  have hy' : y.natAbs < k.toNat + 1 := by omega
  simp [readGrid, makeGrid, h0, hk, hy, hk', hy']

theorem front_abs (t : ℕ) (k y : ℤ) : front t k |y| = front t k y := by
  by_cases h : 0 ≤ y
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (by omega)]
    exact reflectY _ _ _

def advance (cap t : ℕ) (g : Grid) : Grid :=
  makeGrid cap fun k y =>
    update (readGrid cap t g (k - 1) y) (readGrid cap t g (k - 2) y) (readGrid cap t g k y)
      (readGrid cap t g (k - 1) (y + 1)) (readGrid cap t g (k - 1) (y - 1))

def grid (cap : ℕ) : ℕ → Grid
  | 0 => makeGrid cap fun k y => decide (k = 0 ∧ y = 0)
  | t + 1 => advance cap t (grid cap t)

theorem grid_correct (cap t : ℕ) (k y : ℤ) (hk : k ≤ (cap : ℤ)) :
    readGrid cap t (grid cap t) k y = front t k y := by
  induction t generalizing k y with
  | zero =>
    by_cases hy : |y| ≤ k
    · rw [grid, read_make cap _ _ k y hk hy]
      simp [front, cell]
    · rw [front_bg _ _ _ (by omega)]
      simp [readGrid, hy]
  | succ t ih =>
    by_cases hy : |y| ≤ k
    · rw [grid, advance, read_make cap _ _ k y hk hy, ← front_abs (t + 1) k y,
        front_step, ih (k - 1) |y| (by omega), ih (k - 2) |y| (by omega), ih k |y| hk,
        ih (k - 1) (|y| + 1) (by omega), ih (k - 1) (|y| - 1) (by omega)]
    · rw [front_bg _ _ _ (by omega)]
      simp [readGrid, hy]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem cycle : grid 7 23 = grid 7 15 := by decide +kernel

theorem grid_period (t : ℕ) (ht : 15 ≤ t) : grid 7 (t + 8) = grid 7 t := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases ht' : 15 ≤ t
    · change advance 7 (t + 8) (grid 7 (t + 8)) = advance 7 t (grid 7 t)
      rw [ih ht']
      have hb : bg (t + 8) = bg t := by simp [bg, show (t + 8) % 2 = t % 2 by omega]
      simp only [advance, readGrid, hb]
    · have h : t + 1 = 15 := by omega
      change grid 7 ((t + 1) + 8) = grid 7 (t + 1)
      rw [h]
      exact cycle

def phase (t : ℕ) : ℕ := 18 + (t - 18) % 8

theorem grid_phase (t : ℕ) (ht : 18 ≤ t) : grid 7 t = grid 7 (phase t) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases h : t < 26
    · have he : phase t = t := by unfold phase; omega
      rw [he]
    · have hp := grid_period (t - 8) (by omega)
      have hsum : t - 8 + 8 = t := by omega
      have hph : phase (t - 8) = phase t := by unfold phase; omega
      rw [hsum] at hp
      rw [hp, ih (t - 8) (by omega) (by omega), hph]

theorem front_phase (t : ℕ) (ht : 18 ≤ t) (k y : ℤ) (hk : k ≤ 7) :
    front t k y = front (phase t) k y := by
  rw [← grid_correct 7 t k y hk, ← grid_correct 7 (phase t) k y hk, grid_phase t ht]
  have hb : bg (phase t) = bg t := by
    have hm : t = phase t + 8 * ((t - 18) / 8) := by
      have := Nat.mod_add_div (t - 18) 8
      unfold phase
      omega
    simp [bg, show phase t % 2 = t % 2 by omega]
  simp only [readGrid, hb]

-- Each row has five initial columns followed by a repeating block of eight.
def col (x : ℤ) : ℤ := if x < 5 then x else 5 + (x - 5) % 8

def band (t : ℕ) (x y : ℤ) : Bool :=
  let bits : ℕ := if y = 0 then (if t % 2 = 0 then 1366 else 5462)
    else if y = 1 then 4091 else 6829
  bits.testBit (col x).toNat

theorem band_congr (t u : ℕ) (x z y : ℤ)
    (hp : t % 2 = u % 2) (hx : 5 ≤ x) (hz : 5 ≤ z) (hm : x % 8 = z % 8) :
    band t x y = band u z y := by
  have hc : col x = col z := by
    simp only [col, if_neg (by omega : ¬ x < 5), if_neg (by omega : ¬ z < 5)]
    omega
  simp [band, hp, hc]

def left (x : ℤ) : ℤ := if x = 0 then 1 else x - 1

def bandUpdate (t : ℕ) (x y : ℤ) (above : Bool) : Bool :=
  update (band t x y) (band t (x + 1) y) (band t (left x) y)
    (if y = 2 then above else band t x (y + 1))
    (band t x (if y = 0 then 1 else y - 1))

set_option maxHeartbeats 3000000 in
theorem localTable : ∀ (p : Fin 2) (x : Fin 14) (y : Fin 3) (b : Bool),
    bandUpdate p.val (x.val : ℤ) (y.val : ℤ) b =
      band (p.val + 1) (x.val : ℤ) (y.val : ℤ) := by decide +kernel

theorem band_local (t : ℕ) (x y : ℤ) (h0 : 0 ≤ x) (hy : 0 ≤ y ∧ y ≤ 2) (b : Bool) :
    bandUpdate t x y b = band (t + 1) x y := by
  let p : Fin 2 := ⟨t % 2, by omega⟩
  let z : ℤ := if x < 6 then x else 6 + (x - 6) % 8
  let xi : Fin 14 := ⟨z.toNat, by dsimp [z]; split <;> omega⟩
  let yi : Fin 3 := ⟨y.toNat, by omega⟩
  have hz : (xi.val : ℤ) = z := by dsimp [xi, z]; split <;> omega
  have hyi : (yi.val : ℤ) = y := by dsimp [yi]; omega
  have h := localTable p xi yi b
  rw [hz, hyi] at h
  have c (v : ℤ) : band t x v = band p.val z v := by
    by_cases hx : x < 6
    · simp [z, hx, band, p]
    · apply band_congr <;> (try simp only [z, p, if_neg hx]) <;> omega
  have cr (v : ℤ) : band t (x + 1) v = band p.val (z + 1) v := by
    by_cases hx : x < 6
    · simp [z, hx, band, p]
    · apply band_congr <;> (try simp only [z, p, if_neg hx]) <;> omega
  have cl (v : ℤ) : band t (left x) v = band p.val (left z) v := by
    by_cases hx : x < 6
    · simp [z, hx, band, p]
    · have hzn : z ≠ 0 := by simp [z, hx]; omega
      simp only [left, if_neg (show x ≠ 0 by omega), if_neg hzn]
      apply band_congr <;> (try simp only [z, p, if_neg hx]) <;> omega
  have cn : band (t + 1) x y = band (p.val + 1) z y := by
    have hp : (t + 1) % 2 = (p.val + 1) % 2 := by dsimp [p]; omega
    by_cases hx : x < 6
    · simp [z, hx, band, hp]
    · apply band_congr (hp := hp) <;> (try simp only [z, if_neg hx]) <;> omega
  simpa only [bandUpdate, c, cl, cr, cn] using h

def checkBoundaryAt (t : ℕ) (g : Grid) : Bool :=
  (List.range 3).all fun y =>
    let yi : ℤ := (y : ℤ)
    let x : ℤ := (t : ℤ) - 7
    (readGrid 7 t g 7 yi == band t x yi) &&
    (update (readGrid 7 t g 7 yi) (readGrid 7 t g 6 yi) (band t (x - 1) yi)
      (readGrid 7 t g 7 (yi + 1)) (readGrid 7 t g 7 (yi - 1)) == band (t + 1) x yi)

def checkBoundaryLoop : ℕ → ℕ → Grid → Bool
  | 0, _, _ => true
  | fuel + 1, t, g =>
    checkBoundaryAt t g && checkBoundaryLoop fuel (t + 1) (advance 7 t g)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem boundary_edge_verified : checkBoundaryLoop 8 18 (grid 7 18) = true := by decide +kernel

theorem boundary_edge_at (fuel start t : ℕ) (ht : start ≤ t) (hl : t < start + fuel)
    (h : checkBoundaryLoop fuel start (grid 7 start) = true) :
    checkBoundaryAt t (grid 7 t) = true := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
    have hs := Bool.and_eq_true_iff.mp h
    by_cases he : t = start
    · subst t; exact hs.1
    · exact ih (start + 1) (by omega) (by omega) hs.2

theorem boundaryTable : ∀ (p : Fin 8) (y : Fin 3),
    readGrid 7 (18 + p.val) (grid 7 (18 + p.val)) 7 (y.val : ℤ) =
      band (18 + p.val) ((18 + p.val : ℕ) - (7 : ℤ)) (y.val : ℤ) := by
  intro p y
  have h1 := boundary_edge_at 8 18 (18 + p.val) (by omega) (by omega) boundary_edge_verified
  have h2 := List.all_eq_true.mp h1 y.val (List.mem_range.mpr y.isLt)
  exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp h2).1

def edgeUpdate (t : ℕ) (x y : ℤ) : Bool :=
  update (front t 7 y) (front t 6 y) (band t (x - 1) y)
    (front t 7 (y + 1)) (front t 7 (y - 1))

theorem edgeTable : ∀ (p : Fin 8) (y : Fin 3),
    let t := 18 + p.val
    let x : ℤ := (t : ℤ) - 7
    update (readGrid 7 t (grid 7 t) 7 y.val) (readGrid 7 t (grid 7 t) 6 y.val)
      (band t (x - 1) y.val) (readGrid 7 t (grid 7 t) 7 ((y.val : ℤ) + 1))
      (readGrid 7 t (grid 7 t) 7 ((y.val : ℤ) - 1)) = band (t + 1) x y.val := by
  intro p y
  have h1 := boundary_edge_at 8 18 (18 + p.val) (by omega) (by omega) boundary_edge_verified
  have h2 := List.all_eq_true.mp h1 y.val (List.mem_range.mpr y.isLt)
  exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp h2).2

def checkInitialBand (g : Grid) : Bool :=
  (List.range 12).all fun x =>
    (List.range 3).all fun y =>
      readGrid 18 18 g (18 - (x : ℤ)) (y : ℤ) == band 18 (x : ℤ) (y : ℤ)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem initialBand_verified : checkInitialBand (grid 18 18) = true := by decide +kernel

theorem initialBand : ∀ (x : Fin 12) (y : Fin 3),
    readGrid 18 18 (grid 18 18) (18 - (x.val : ℤ)) (y.val : ℤ) =
    band 18 x.val y.val := by
  intro x y
  have hx := List.all_eq_true.mp initialBand_verified x.val (List.mem_range.mpr x.isLt)
  have hy := List.all_eq_true.mp hx y.val (List.mem_range.mpr y.isLt)
  exact beq_iff_eq.mp hy

theorem band_at_phase (t j : ℕ) (ht : 18 ≤ t) (d y : ℤ) (hd : d ≤ 8) :
    band (t + j) ((t : ℤ) - d) y =
      band (phase t + j) ((phase t : ℤ) - d) y := by
  have hp : 18 ≤ phase t := by unfold phase; omega
  have hm : t = phase t + 8 * ((t - 18) / 8) := by
    have := Nat.mod_add_div (t - 18) 8
    unfold phase
    omega
  have hi := congrArg (fun n : ℕ => (n : ℤ)) hm
  push_cast at hi
  exact band_congr _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)

theorem boundary (t : ℕ) (ht : 18 ≤ t) (y : ℤ) (hy : 0 ≤ y ∧ y ≤ 2) :
    front t 7 y = band t ((t : ℤ) - 7) y := by
  let p : Fin 8 := ⟨(t - 18) % 8, by omega⟩
  let i : Fin 3 := ⟨y.toNat, by omega⟩
  have hi : (i.val : ℤ) = y := by dsimp [i]; omega
  have h := boundaryTable p i
  change readGrid 7 (phase t) (grid 7 (phase t)) 7 (i.val : ℤ) =
    band (phase t) ((phase t : ℤ) - 7) (i.val : ℤ) at h
  rw [hi, grid_correct 7 (phase t) 7 y (by norm_num)] at h
  rw [front_phase t ht 7 y (by norm_num)]
  have hb := band_at_phase t 0 ht 7 y (by norm_num)
  simp only [Nat.add_zero] at hb
  rw [← hb] at h
  exact h

theorem edge (t : ℕ) (ht : 18 ≤ t) (y : ℤ) (hy : 0 ≤ y ∧ y ≤ 2) :
    edgeUpdate t ((t : ℤ) - 7) y = band (t + 1) ((t : ℤ) - 7) y := by
  let p : Fin 8 := ⟨(t - 18) % 8, by omega⟩
  let i : Fin 3 := ⟨y.toNat, by omega⟩
  have hi : (i.val : ℤ) = y := by dsimp [i]; omega
  have h := edgeTable p i
  change update (readGrid 7 (phase t) (grid 7 (phase t)) 7 i.val)
    (readGrid 7 (phase t) (grid 7 (phase t)) 6 i.val)
    (band (phase t) ((phase t : ℤ) - 7 - 1) i.val)
    (readGrid 7 (phase t) (grid 7 (phase t)) 7 ((i.val : ℤ) + 1))
    (readGrid 7 (phase t) (grid 7 (phase t)) 7 ((i.val : ℤ) - 1)) =
      band (phase t + 1) ((phase t : ℤ) - 7) i.val at h
  rw [hi] at h
  rw [grid_correct 7 (phase t) 7 y (by norm_num),
    grid_correct 7 (phase t) 6 y (by norm_num),
    grid_correct 7 (phase t) 7 (y + 1) (by norm_num),
    grid_correct 7 (phase t) 7 (y - 1) (by norm_num)] at h
  unfold edgeUpdate
  rw [front_phase t ht 7 y (by norm_num), front_phase t ht 6 y (by norm_num),
    front_phase t ht 7 (y + 1) (by norm_num), front_phase t ht 7 (y - 1) (by norm_num)]
  have hb := band_at_phase t 0 ht 8 y (by norm_num)
  simp only [Nat.add_zero] at hb
  rw [show (t : ℤ) - 7 - 1 = (t : ℤ) - 8 by omega, hb,
    band_at_phase t 1 ht 7 y (by norm_num)]
  rwa [show (phase t : ℤ) - 7 - 1 = (phase t : ℤ) - 8 by omega] at h

set_option maxHeartbeats 3000000 in
theorem strip (t : ℕ) (ht : 18 ≤ t) (x y : ℤ)
    (hx : 0 ≤ x ∧ x + 7 ≤ (t : ℤ)) (hy : 0 ≤ y ∧ y ≤ 2) :
    cell 185 t x y = band t x y := by
  induction t generalizing x y with
  | zero => omega
  | succ t ih =>
    by_cases hb : t < 18
    · have ht18 : t + 1 = 18 := by omega
      rw [ht18] at hx ⊢
      let a : Fin 12 := ⟨x.toNat, by omega⟩
      let b : Fin 3 := ⟨y.toNat, by omega⟩
      have ha : (a.val : ℤ) = x := by dsimp [a]; omega
      have hby : (b.val : ℤ) = y := by dsimp [b]; omega
      have h := initialBand a b
      rw [ha, hby, grid_correct 18 18 (18 - x) y (by omega)] at h
      change cell 185 18 ((18 : ℤ) - (18 - x)) y = band 18 x y at h
      rwa [show (18 : ℤ) - (18 - x) = x by omega] at h
    · have ht' : 18 ≤ t := by omega
      by_cases h7 : x + 7 = (t : ℤ) + 1
      · have q := boundary (t + 1) (by omega) y hy
        unfold front at q
        push_cast at q
        rwa [show (t : ℤ) + 1 - 7 = x by omega] at q
      · by_cases h8 : x + 7 = (t : ℤ)
        · have hx' : x = (t : ℤ) - 7 := by omega
          have q := edge t ht' y hy
          rw [← hx', edgeUpdate] at q
          unfold front at q
          rw [← hx', show (t : ℤ) - 6 = x + 1 by omega] at q
          rw [cell_step, ih ht' (x - 1) y (by omega) hy]
          exact q
        · have old (u v : ℤ) (hu : 0 ≤ u ∧ u + 7 ≤ (t : ℤ))
              (hv : 0 ≤ v ∧ v ≤ 2) := ih ht' u v hu hv
          have wl (v : ℤ) (hv : 0 ≤ v ∧ v ≤ 2) :
              cell 185 t (x - 1) v = band t (left x) v := by
            by_cases h0 : x = 0
            · subst x
              simp only [left]
              rw [show (0 : ℤ) - 1 = -1 by norm_num, reflectX]
              exact old 1 v (by omega) hv
            · simp only [left, if_neg h0]
              exact old (x - 1) v (by omega) hv
          have cen := old x y (by omega) hy
          have east := old (x + 1) y (by omega) hy
          have h0 := old x 0 (by omega) (by omega)
          have h1 := old x 1 (by omega) (by omega)
          have h2 := old x 2 (by omega) (by omega)
          rw [cell_step, cen, east, wl y hy]
          obtain ⟨hy0, hy2⟩ := hy
          interval_cases y
          · rw [show (0 : ℤ) + 1 = 1 by norm_num, show (0 : ℤ) - 1 = -1 by norm_num,
                reflectY, h1]
            simpa [bandUpdate] using band_local t x 0 hx.1 (by omega) false
          · rw [show (1 : ℤ) + 1 = 2 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num, h2, h0]
            simpa [bandUpdate] using band_local t x 1 hx.1 (by omega) false
          · rw [show (2 : ℤ) + 1 = 3 by norm_num, show (2 : ℤ) - 1 = 1 by norm_num, h1]
            simpa [bandUpdate] using band_local t x 2 hx.1 (by omega) (cell 185 t x 3)

theorem front_eight (t k : ℕ) (ht : 18 ≤ t) (hk : k ≤ 8) :
    front (t + 8) k 0 = front t k 0 := by
  by_cases h : k ≤ 7
  · have hp : phase (t + 8) = phase t := by unfold phase; omega
    rw [front_phase (t + 8) (by omega) k 0 (by omega), hp,
      ← front_phase t ht k 0 (by omega)]
  · have he : k = 8 := by omega
    subst k
    unfold front
    rw [strip (t + 8) (by omega) _ _ (by push_cast; omega) (by omega),
      strip t ht _ _ (by omega) (by omega)]
    apply band_congr <;> push_cast <;> omega

theorem front_inside (n k : ℕ) (hn : 18 ≤ n) (hk : 7 ≤ k) (hle : k ≤ n) :
    front (n + 2) (k + 2 : ℕ) 0 = front n k 0 := by
  unfold front
  have hn' : ((n + 2 : ℕ) : ℤ) - ((k + 2 : ℕ) : ℤ) = (n : ℤ) - k := by push_cast; omega
  rw [hn', strip (n + 2) (by omega) _ _ (by push_cast; omega) (by omega),
    strip n hn _ _ (by omega) (by omega)]
  simp [band, show (n + 2) % 2 = n % 2 by omega]

open PowerSeries

def digit (n k : ℕ) : ℤ := if front n k 0 then 2 ^ k else 0

theorem a_front (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n + 1), digit n k := by
  unfold a
  have href := Finset.sum_range_reflect
    (fun k : ℕ => if cell 185 n k 0 then (2 : ℤ) ^ (n - k) else 0) (n + 1)
  simp only [Nat.add_sub_cancel] at href
  rw [← href]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hx : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := by omega
  have he : n - (n - k) = k := by omega
  (simp only [hx, he, front, digit]; rfl)

def fringe (n d : ℕ) : ℤ := ∑ k ∈ Finset.range d, digit n k

theorem fringe_period (n d : ℕ) (hn : 18 ≤ n) (hd : d ≤ 9) :
    fringe (n + 8) d = fringe n d := by
  apply Finset.sum_congr rfl
  intro k hk
  have h := Finset.mem_range.mp hk
  simp only [digit, front_eight n k hn (by omega)]

theorem a_difference (n : ℕ) (hn : 18 ≤ n) :
    a (n + 2) - 4 * a n = fringe (n + 2) 9 - 4 * fringe n 7 := by
  rw [a_front, a_front, show n + 2 + 1 = 9 + (n - 6) by omega,
    show n + 1 = 7 + (n - 6) by omega, Finset.sum_range_add, Finset.sum_range_add]
  change fringe (n + 2) 9 + (∑ k ∈ Finset.range (n - 6), digit (n + 2) (9 + k)) -
    4 * (fringe n 7 + ∑ k ∈ Finset.range (n - 6), digit n (7 + k)) = _
  have h : (∑ k ∈ Finset.range (n - 6), digit (n + 2) (9 + k)) =
      4 * ∑ k ∈ Finset.range (n - 6), digit n (7 + k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hlt := Finset.mem_range.mp hk
    rw [show 9 + k = (7 + k) + 2 by omega]
    unfold digit
    rw [front_inside n (7 + k) hn (by omega) (by omega)]
    split <;> (simp [pow_add]; try ring)
  rw [h]
  ring

theorem recurrence (n : ℕ) (hn : 28 ≤ n) :
    (a n : ℚ) = 4 * a (n - 2) + a (n - 8) - 4 * a (n - 10) := by
  have h1 := a_difference (n - 2) (by omega)
  have h2 := a_difference (n - 10) (by omega)
  have h3 := fringe_period (n - 10 + 2) 9 (by omega) (by omega)
  have h4 := fringe_period (n - 10) 7 (by omega) (by omega)
  rw [show n - 2 + 2 = n by omega] at h1
  rw [show n - 10 + 2 + 8 = n by omega] at h3
  rw [show n - 10 + 8 = n - 2 by omega] at h4
  rw [show n - 10 + 2 = n - 8 by omega] at h2 h3
  exact_mod_cast (by linarith : a n = 4 * a (n - 2) + a (n - 8) - 4 * a (n - 10))

def gridValue (g : Grid) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if readGrid 17 n g k 0 then (2 : ℤ) ^ k else 0

theorem gridValue_correct (n : ℕ) (hn : n ≤ 17) : a n = gridValue (grid 17 n) n := by
  rw [a_front]
  unfold gridValue
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [grid_correct 17 n k 0 (by omega)]
  rfl

def table : Array ℤ := #[1, 0, 5, 0, 29, 8, 85, 40, 261, 232, 1365, 296, 6725, 4264, 3349, 55976, 62789, 125608, 218389, 436904, 873541, 1747624, 3494165, 6990504, 13976901, 27962024, 55907605, 111848104]

def checkInitial : ℕ → ℕ → Grid → Bool
  | 0, _, _ => true
  | fuel + 1, n, g =>
    (gridValue g n == table[n]?.getD 0) && checkInitial fuel (n + 1) (advance 17 n g)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 3000000 in
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

def lateStepValue (g : Grid) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    if (if k ≤ 7 then readGrid 7 n g k 0 else band n ((n : ℤ) - k) 0)
      then (2 : ℤ) ^ k else 0

theorem lateStepValue_correct (n : ℕ) (hn : 18 ≤ n) :
    a n = lateStepValue (grid 7 n) n := by
  rw [a_front]
  unfold lateStepValue
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  unfold digit
  by_cases h7 : k ≤ 7
  · rw [if_pos h7, grid_correct 7 n k 0 (by omega)]
  · have h : front n k 0 = band n ((n : ℤ) - k) 0 := by
      unfold front
      apply strip n hn _ _ (by omega) (by omega)
    rw [if_neg h7, h]

def checkLate : ℕ → ℕ → Grid → Bool
  | 0, _, _ => true
  | fuel + 1, n, g =>
    (lateStepValue g n == table[n]?.getD 0) && checkLate fuel (n + 1) (advance 7 n g)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 3000000 in
theorem late_verified : checkLate 10 18 (grid 7 18) = true := by decide +kernel

theorem late_at (fuel start n : ℕ) (hn : start ≤ n) (hl : n < start + fuel)
    (h : checkLate fuel start (grid 7 start) = true) :
    lateStepValue (grid 7 n) n = table[n]?.getD 0 := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
    have hs := Bool.and_eq_true_iff.mp h
    by_cases he : n = start
    · subst n
      exact beq_iff_eq.mp hs.1
    · exact ih (start + 1) (by omega) (by omega) hs.2

theorem a_initial (n : ℕ) (h : n < 28) : a n = table[n]?.getD 0 := by
  by_cases hn : n < 18
  · rw [gridValue_correct n (by omega)]
    exact initial_at 18 0 n (by omega) (by omega) table_verified
  · rw [lateStepValue_correct n (by omega)]
    exact late_at 10 18 n (by omega) (by omega) late_verified

def series : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

noncomputable def numerator : ℚ⟦X⟧ :=
  65536 * X ^ 27 + 32768 * X ^ 26 + 98304 * X ^ 25 - 49152 * X ^ 24 - 38912 * X ^ 23 + 23552 * X ^ 22 - 3072 * X ^ 21 - 1280 * X ^ 20 - 64896 * X ^ 19 - 33088 * X ^ 18 - 98368 * X ^ 17 + 49472 * X ^ 16 + 38912 * X ^ 15 - 23520 * X ^ 14 + 3072 * X ^ 13 + 1256 * X ^ 12 - 632 * X ^ 11 + 320 * X ^ 10 + 72 * X ^ 9 - 80 * X ^ 8 + 8 * X ^ 7 - 31 * X ^ 6 + 8 * X ^ 5 + 9 * X ^ 4 + X ^ 2 + 1

def numCoeff : ℕ → ℤ
  | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0 | 4 => 9 | 5 => 8 | 6 => -31 | 7 => 8
  | 8 => -80 | 9 => 72 | 10 => 320 | 11 => -632 | 12 => 1256 | 13 => 3072
  | 14 => -23520 | 15 => 38912 | 16 => 49472 | 17 => -98368 | 18 => -33088
  | 19 => -64896 | 20 => -1280 | 21 => -3072 | 22 => 23552 | 23 => -38912
  | 24 => -49152 | 25 => 98304 | 26 => 32768 | 27 => 65536 | _ => 0

theorem gen_init_ok : ∀ n : Fin 28,
    ((if 10 ≤ n.val then table[n.val - 10]?.getD 0 * 4 else 0) -
     (if 8 ≤ n.val then table[n.val - 8]?.getD 0 else 0) -
     (if 2 ≤ n.val then table[n.val - 2]?.getD 0 * 4 else 0) +
     table[n.val]?.getD 0) == numCoeff n.val := by decide

theorem numerator_eq : numerator = ∑ k ∈ Finset.range 28, C (numCoeff k : ℚ) * X ^ k := by
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
    series * (4 * X ^ 10 - X ^ 8 - 4 * X ^ 2 + 1 : ℚ⟦X⟧) = numerator := by
  have hd : (4 * X ^ 10 - X ^ 8 - 4 * X ^ 2 + 1 : ℚ⟦X⟧) =
      C 4 * X ^ 10 - C 1 * X ^ 8 - C 4 * X ^ 2 + C 1 * X ^ 0 := by
    simp only [map_ofNat, map_one]
    ring
  rw [hd, numerator_eq]
  ext n
  simp only [mul_add, mul_sub, map_add, map_sub, map_sum, series_mul_coeff,
    PowerSeries.coeff_C_mul_X_pow]
  by_cases h : n < 28
  · have hrhs : (∑ x ∈ Finset.range 28, if n = x then (numCoeff x : ℚ) else 0) =
        (numCoeff n : ℚ) := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro b _ hb; simp [hb.symm]
      · intro hn; exact absurd (Finset.mem_range.mpr h) hn
    rw [hrhs]
    simp only [Nat.sub_zero, mul_one, show 0 ≤ n by omega, ↓reduceIte]
    have h0 : a n = table[n]?.getD 0 := a_initial n h
    have h2 : (if 2 ≤ n then (a (n - 2) : ℚ) * 4 else 0) =
        ((if 2 ≤ n then table[n - 2]?.getD 0 * 4 else 0 : ℤ) : ℚ) := by
      split_ifs with h2' <;> simp [a_initial, show n - 2 < 28 by omega]
    have h8 : (if 8 ≤ n then (a (n - 8) : ℚ) else 0) =
        ((if 8 ≤ n then table[n - 8]?.getD 0 else 0 : ℤ) : ℚ) := by
      split_ifs with h8' <;> simp [a_initial, show n - 8 < 28 by omega]
    have h10 : (if 10 ≤ n then (a (n - 10) : ℚ) * 4 else 0) =
        ((if 10 ≤ n then table[n - 10]?.getD 0 * 4 else 0 : ℤ) : ℚ) := by
      split_ifs with h10' <;> simp [a_initial, show n - 10 < 28 by omega]
    have hok := beq_iff_eq.mp (gen_init_ok ⟨n, h⟩)
    have hokq : ((if 10 ≤ n then table[n - 10]?.getD 0 * 4 else 0 : ℤ) : ℚ) -
        ((if 8 ≤ n then table[n - 8]?.getD 0 else 0 : ℤ) : ℚ) -
        ((if 2 ≤ n then table[n - 2]?.getD 0 * 4 else 0 : ℤ) : ℚ) +
        (table[n]?.getD 0 : ℚ) = (numCoeff n : ℚ) := by
      exact_mod_cast hok
    rw [h0, h2, h8, h10]
    exact hokq
  · have hn : 28 ≤ n := by omega
    have hrhs : (∑ x ∈ Finset.range 28, if n = x then (numCoeff x : ℚ) else 0) = 0 :=
      Finset.sum_eq_zero fun x hx => if_neg (by have := Finset.mem_range.mp hx; omega)
    rw [hrhs]
    simp only [if_pos (show 0 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 8 ≤ n by omega), if_pos (show 10 ≤ n by omega), Nat.sub_zero, mul_one]
    linarith [recurrence n hn]

end Rule185

theorem OMA.solution : type_of% @OMA.S_oeis_a279701.main := by
  refine ⟨Rule185.recurrence, ?_⟩
  simpa [Rule185.series, Rule185.numerator] using Rule185.generating

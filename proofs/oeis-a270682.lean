import OMAStatements.S_oeis_a270682

namespace OMA.S_oeis_a270682

open PowerSeries





/-- The pattern: OFF outside the diamond, ON within distance 1 of its edge, and inside that ON
exactly at odd distances. -/
def g (t d : ℕ) : Bool := decide (d ≤ t) && (decide (t ≤ d + 1) || d % 2 == 1)

theorem g_out {t d : ℕ} (h : t < d) : g t d = false := by
  simp only [g, decide_eq_false (show ¬d ≤ t by omega), Bool.false_and]

theorem g_edge {t d : ℕ} (h1 : t ≤ d + 1) (h2 : d ≤ t) : g t d = true := by
  simp only [g, decide_eq_true h2, decide_eq_true h1, Bool.true_or, Bool.true_and]

theorem g_in {t d : ℕ} (h : d + 2 ≤ t) : g t d = (d % 2 == 1) := by
  simp only [g, decide_eq_true (show d ≤ t by omega), decide_eq_false (show ¬t ≤ d + 1 by omega),
    Bool.false_or, Bool.true_and]

/-- The steps of Rules 190 and 254 agree on the pattern; R is either rule number. -/
theorem step0 (R : ℕ) (hR : R = 190 ∨ R = 254) (t : ℕ) :
    Nat.testBit R ((g t 0).toNat + 2 * (4 * (g t 1).toNat)) = g (t + 1) 0 := by
  rcases (by omega : t ≤ 2 ∨ 3 ≤ t) with ht | ht
  · rcases hR with rfl | rfl <;> interval_cases t <;> rfl
  · rw [g_in (by omega : 0 + 2 ≤ t), g_in (by omega : 1 + 2 ≤ t), g_in (by omega : 0 + 2 ≤ t + 1)]
    rcases hR with rfl | rfl <;> rfl

/-- A cell on an axis: one neighbor at distance d - 1, three at d + 1. -/
theorem step1 (R : ℕ) (hR : R = 190 ∨ R = 254) (t d : ℕ) (hd : 1 ≤ d) :
    Nat.testBit R ((g t d).toNat + 2 * ((g t (d - 1)).toNat + 3 * (g t (d + 1)).toNat)) =
      g (t + 1) d := by
  have h1 : (d - 1) % 2 = (d % 2 + 1) % 2 := by omega
  have h2 : (d + 1) % 2 = (d % 2 + 1) % 2 := by omega
  have hs : d % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : d + 3 ≤ t ∨ d + 2 = t ∨ d + 1 = t ∨ d = t ∨ d = t + 1 ∨ t + 2 ≤ d)
    with c | c | c | c | c | c
  · rw [g_in (by omega : d + 2 ≤ t), g_in (by omega : d - 1 + 2 ≤ t),
      g_in (by omega : d + 1 + 2 ≤ t), g_in (by omega : d + 2 ≤ t + 1), h1, h2]
    generalize d % 2 = s at *
    rcases hR with rfl | rfl <;> interval_cases s <;> rfl
  · rw [g_in (by omega : d + 2 ≤ t), g_in (by omega : d - 1 + 2 ≤ t),
      g_edge (by omega : t ≤ d + 1 + 1) (by omega : d + 1 ≤ t), g_in (by omega : d + 2 ≤ t + 1),
      h1]
    generalize d % 2 = s at *
    rcases hR with rfl | rfl <;> interval_cases s <;> rfl
  · rw [g_edge (by omega : t ≤ d + 1) (by omega : d ≤ t), g_in (by omega : d - 1 + 2 ≤ t),
      g_edge (by omega : t ≤ d + 1 + 1) (by omega : d + 1 ≤ t),
      g_in (by omega : d + 2 ≤ t + 1), h1]
    generalize d % 2 = s at *
    rcases hR with rfl | rfl <;> interval_cases s <;> rfl
  · rw [g_edge (by omega : t ≤ d + 1) (by omega : d ≤ t),
      g_edge (by omega : t ≤ d - 1 + 1) (by omega : d - 1 ≤ t), g_out (by omega : t < d + 1),
      g_edge (by omega : t + 1 ≤ d + 1) (by omega : d ≤ t + 1)]
    rcases hR with rfl | rfl <;> rfl
  · rw [g_out (by omega : t < d), g_edge (by omega : t ≤ d - 1 + 1) (by omega : d - 1 ≤ t),
      g_out (by omega : t < d + 1), g_edge (by omega : t + 1 ≤ d + 1) (by omega : d ≤ t + 1)]
    rcases hR with rfl | rfl <;> rfl
  · rw [g_out (by omega : t < d), g_out (by omega : t < d - 1), g_out (by omega : t < d + 1),
      g_out (by omega : t + 1 < d)]
    rcases hR with rfl | rfl <;> rfl

/-- A cell off the axes: two neighbors at distance d - 1, two at d + 1. -/
theorem step2 (R : ℕ) (hR : R = 190 ∨ R = 254) (t d : ℕ) (hd : 2 ≤ d) :
    Nat.testBit R ((g t d).toNat +
      2 * (2 * (g t (d - 1)).toNat + 2 * (g t (d + 1)).toNat)) = g (t + 1) d := by
  have h1 : (d - 1) % 2 = (d % 2 + 1) % 2 := by omega
  have h2 : (d + 1) % 2 = (d % 2 + 1) % 2 := by omega
  have hs : d % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : d + 3 ≤ t ∨ d + 2 = t ∨ d + 1 = t ∨ d = t ∨ d = t + 1 ∨ t + 2 ≤ d)
    with c | c | c | c | c | c
  · rw [g_in (by omega : d + 2 ≤ t), g_in (by omega : d - 1 + 2 ≤ t),
      g_in (by omega : d + 1 + 2 ≤ t), g_in (by omega : d + 2 ≤ t + 1), h1, h2]
    generalize d % 2 = s at *
    rcases hR with rfl | rfl <;> interval_cases s <;> rfl
  · rw [g_in (by omega : d + 2 ≤ t), g_in (by omega : d - 1 + 2 ≤ t),
      g_edge (by omega : t ≤ d + 1 + 1) (by omega : d + 1 ≤ t), g_in (by omega : d + 2 ≤ t + 1),
      h1]
    generalize d % 2 = s at *
    rcases hR with rfl | rfl <;> interval_cases s <;> rfl
  · rw [g_edge (by omega : t ≤ d + 1) (by omega : d ≤ t), g_in (by omega : d - 1 + 2 ≤ t),
      g_edge (by omega : t ≤ d + 1 + 1) (by omega : d + 1 ≤ t),
      g_in (by omega : d + 2 ≤ t + 1), h1]
    generalize d % 2 = s at *
    rcases hR with rfl | rfl <;> interval_cases s <;> rfl
  · rw [g_edge (by omega : t ≤ d + 1) (by omega : d ≤ t),
      g_edge (by omega : t ≤ d - 1 + 1) (by omega : d - 1 ≤ t), g_out (by omega : t < d + 1),
      g_edge (by omega : t + 1 ≤ d + 1) (by omega : d ≤ t + 1)]
    rcases hR with rfl | rfl <;> rfl
  · rw [g_out (by omega : t < d), g_edge (by omega : t ≤ d - 1 + 1) (by omega : d - 1 ≤ t),
      g_out (by omega : t < d + 1), g_edge (by omega : t + 1 ≤ d + 1) (by omega : d ≤ t + 1)]
    rcases hR with rfl | rfl <;> rfl
  · rw [g_out (by omega : t < d), g_out (by omega : t < d - 1), g_out (by omega : t < d + 1),
      g_out (by omega : t + 1 < d)]
    rcases hR with rfl | rfl <;> rfl

/-- One step of either rule, written for a stage that is the pattern `g`. -/
theorem step (R : ℕ) (hR : R = 190 ∨ R = 254) (t : ℕ) (x y : ℤ) :
    Nat.testBit R ((g t (x.natAbs + y.natAbs)).toNat +
      2 * ((g t ((x - 1).natAbs + y.natAbs)).toNat + (g t ((x + 1).natAbs + y.natAbs)).toNat +
        (g t (x.natAbs + (y - 1).natAbs)).toNat + (g t (x.natAbs + (y + 1).natAbs)).toNat)) =
      g (t + 1) (x.natAbs + y.natAbs) := by
  rcases lt_trichotomy x 0 with hx | hx | hx <;> rcases lt_trichotomy y 0 with hy | hy | hy
  · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
      show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
      show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
      show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
      ← step2 R hR t _ (by omega)]
    congr 1; ring
  · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
      show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
      show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
      show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
      ← step1 R hR t _ (by omega)]
    congr 1; ring
  · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
      show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
      show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
      show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
      ← step2 R hR t _ (by omega)]
    congr 1; ring
  · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
      show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
      show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
      show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
      ← step1 R hR t _ (by omega)]
    congr 1; ring
  · rw [show (x - 1).natAbs + y.natAbs = 1 by omega,
      show (x + 1).natAbs + y.natAbs = 1 by omega,
      show x.natAbs + (y - 1).natAbs = 1 by omega,
      show x.natAbs + (y + 1).natAbs = 1 by omega,
      show x.natAbs + y.natAbs = 0 by omega, ← step0 R hR t]
    congr 1; ring
  · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
      show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
      show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
      show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
      ← step1 R hR t _ (by omega)]
    congr 1; ring
  · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
      show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
      show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
      show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
      ← step2 R hR t _ (by omega)]
    congr 1; ring
  · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
      show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
      show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
      show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
      ← step1 R hR t _ (by omega)]
    congr 1; ring
  · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
      show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
      show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
      show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
      ← step2 R hR t _ (by omega)]
    congr 1; ring

theorem g_zero (x y : ℤ) : decide (x = 0 ∧ y = 0) = g 0 (x.natAbs + y.natAbs) := by
  by_cases h : x = 0 ∧ y = 0
  · rw [decide_eq_true h, show x.natAbs + y.natAbs = 0 by omega]; rfl
  · rw [decide_eq_false h, g_out (by omega : 0 < x.natAbs + y.natAbs)]

/-- Stage t of Rule 190 is the pattern `g` of the distance |x| + |y|. -/
theorem state_pattern (t : ℕ) : ∀ x y, state t x y = g t (x.natAbs + y.natAbs) := by
  induction t with
  | zero => exact g_zero
  | succ t ih =>
    intro x y
    show Nat.testBit 190 _ = _
    rw [ih, ih, ih, ih, ih]
    exact step 190 (Or.inl rfl) t x y

/-- Stage t of Rule 254 is the same pattern. -/
theorem state254_pattern (t : ℕ) : ∀ x y, state254 t x y = g t (x.natAbs + y.natAbs) := by
  induction t with
  | zero => exact g_zero
  | succ t ih =>
    intro x y
    show Nat.testBit 254 _ = _
    rw [ih, ih, ih, ih, ih]
    exact step 254 (Or.inr rfl) t x y

/-- Blomberg's first conjecture: Rule 254 gives the same counts. -/
theorem rule254 (n : ℕ) : count state254 (2 ^ n - 1) = a n := by
  have e : ∀ t x y, state254 t x y = state t x y := fun t x y => by
    rw [state254_pattern, state_pattern]
  unfold a count
  simp only [e]

/-! ### Counting cells by distance -/

/-- The number of integers with absolute value i. -/
def w (i : ℕ) : ℕ := if i = 0 then 1 else 2

/-- The number of cells at distance d = |x| + |y| from the origin. -/
def c (d : ℕ) : ℕ := if d = 0 then 1 else 4 * d

theorem sum_Icc_natAbs (n : ℕ) (h : ℕ → ℕ) :
    ∑ x ∈ Finset.Icc (-(n : ℤ)) n, h x.natAbs = ∑ i ∈ Finset.range (n + 1), w i * h i := by
  induction n with
  | zero => simp [w]
  | succ n ih =>
    have e : Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) =
        insert (-((n + 1 : ℕ) : ℤ)) (insert ((n + 1 : ℕ) : ℤ) (Finset.Icc (-(n : ℤ)) n)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [e, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih,
      Finset.sum_range_succ _ (n + 1), Int.natAbs_neg, Int.natAbs_natCast,
      show w (n + 1) = 2 by simp [w]]
    ring

theorem sum_ww (m : ℕ) (hm : 1 ≤ m) : ∑ i ∈ Finset.range (m + 1), w i * w (m - i) = 4 * m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  have e : ∀ i ∈ Finset.range k, w (i + 1) * w (k + 1 - (i + 1)) = 4 := by
    intro i hi
    simp only [Finset.mem_range] at hi
    simp only [w, if_neg (show i + 1 ≠ 0 by omega), if_neg (show k + 1 - (i + 1) ≠ 0 by omega)]
  rw [Finset.sum_congr rfl e, show k + 1 - (k + 1) = 0 by omega, show k + 1 - 0 = k + 1 by omega,
    show w 0 = 1 from rfl, show w (k + 1) = 2 by simp [w]]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

/-- Grouping the pairs (i, j) with i + j <= n by d = i + j. -/
theorem shell (n : ℕ) (h : ℕ → ℕ) :
    ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      w i * w j * (if i + j ≤ n then h (i + j) else 0) =
    ∑ d ∈ Finset.range (n + 1), c d * h d := by
  induction n with
  | zero => simp [w, c]
  | succ n ih =>
    have split : ∀ i j, (if i + j ≤ n + 1 then h (i + j) else 0) =
        (if i + j ≤ n then h (i + j) else 0) + (if i + j = n + 1 then h (n + 1) else 0) := by
      intro i j
      by_cases h1 : i + j ≤ n
      · rw [if_pos (by omega), if_pos h1, if_neg (by omega), add_zero]
      · by_cases h2 : i + j = n + 1
        · rw [if_pos (by omega), if_neg h1, if_pos h2, zero_add, h2]
        · rw [if_neg (by omega), if_neg h1, if_neg h2]
    simp only [split, mul_add, Finset.sum_add_distrib]
    have hA : ∑ i ∈ Finset.range (n + 1 + 1), ∑ j ∈ Finset.range (n + 1 + 1),
        w i * w j * (if i + j ≤ n then h (i + j) else 0) =
        ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          w i * w j * (if i + j ≤ n then h (i + j) else 0) := by
      rw [Finset.sum_range_succ]
      have z : ∑ j ∈ Finset.range (n + 1 + 1),
          w (n + 1) * w j * (if n + 1 + j ≤ n then h (n + 1 + j) else 0) = 0 :=
        Finset.sum_eq_zero (fun j _ => by rw [if_neg (by omega), mul_zero])
      rw [z, add_zero]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      simp only [Finset.mem_range] at hi
      rw [Finset.sum_range_succ, if_neg (by omega), mul_zero, add_zero]
    have hB : ∑ i ∈ Finset.range (n + 1 + 1), ∑ j ∈ Finset.range (n + 1 + 1),
        w i * w j * (if i + j = n + 1 then h (n + 1) else 0) = c (n + 1) * h (n + 1) := by
      have inner : ∀ i ∈ Finset.range (n + 1 + 1), ∑ j ∈ Finset.range (n + 1 + 1),
          w i * w j * (if i + j = n + 1 then h (n + 1) else 0) =
            w i * w (n + 1 - i) * h (n + 1) := by
        intro i hi
        simp only [Finset.mem_range] at hi
        rw [Finset.sum_eq_single (n + 1 - i)]
        · rw [if_pos (by omega)]
        · intro j _ hj
          rw [if_neg (by omega), mul_zero]
        · intro hj
          simp only [Finset.mem_range] at hj
          omega
      rw [Finset.sum_congr rfl inner, ← Finset.sum_mul, sum_ww (n + 1) (by omega)]
      simp only [c, if_neg (show n + 1 ≠ 0 by omega)]
    rw [hA, hB, ih, Finset.sum_range_succ _ (n + 1)]

/-! ### The count -/

/-- The cells of stage n at the ON distances d <= n, counted with multiplicity c d. -/
def ON (n : ℕ) : ℕ := ∑ d ∈ Finset.range (n + 1), c d * (if g n d then 1 else 0)

theorem count_eq (n : ℕ) : count state n = ON n := by
  unfold count ON
  rw [Finset.card_filter, Finset.sum_product]
  have inner : ∀ x ∈ Finset.Icc (-(n : ℤ)) n,
      (∑ y ∈ Finset.Icc (-(n : ℤ)) n, if state n x y = true then 1 else 0) =
        ∑ j ∈ Finset.range (n + 1), w j * (if g n (x.natAbs + j) then 1 else 0) := by
    intro x _
    simp only [state_pattern]
    exact sum_Icc_natAbs n (fun j => if g n (x.natAbs + j) then 1 else 0)
  rw [Finset.sum_congr rfl inner,
    sum_Icc_natAbs n (fun i => ∑ j ∈ Finset.range (n + 1), w j * (if g n (i + j) then 1 else 0)),
    ← shell n (fun d => if g n d then 1 else 0)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  by_cases hd : i + j ≤ n
  · rw [if_pos hd]; ring
  · rw [if_neg hd, g_out (by omega : n < i + j)]; simp

/-- Two more stages at an odd stage 2m + 1 >= 3: the distance 2m turns OFF, and 2m + 2 and
2m + 3 are new and ON. -/
theorem on_shift (m : ℕ) (hm : 1 ≤ m) : ON (2 * m + 3) + 4 * (2 * m) =
    ON (2 * m + 1) + 4 * (2 * m + 2) + 4 * (2 * m + 3) := by
  unfold ON
  simp only [Finset.sum_range_succ]
  have e : ∑ d ∈ Finset.range (2 * m), c d * (if g (2 * m + 3) d then 1 else 0) =
      ∑ d ∈ Finset.range (2 * m), c d * (if g (2 * m + 1) d then 1 else 0) := by
    refine Finset.sum_congr rfl (fun d hd => ?_)
    simp only [Finset.mem_range] at hd
    rw [g_in (by omega : d + 2 ≤ 2 * m + 3), g_in (by omega : d + 2 ≤ 2 * m + 1)]
  rw [e]
  simp (disch := omega) only [g_in, g_edge]
  simp [c, show 2 * m ≠ 0 by omega, Nat.mul_mod_right, Nat.add_mod]
  omega

/-- At the odd stages 2m + 1 >= 3 the ON distances are the odd ones and 2m. -/
theorem on_odd (m : ℕ) (hm : 1 ≤ m) : ON (2 * m + 1) = (2 * m + 2) ^ 2 + 8 * m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have h := on_shift m hm
    rw [ih] at h
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring]
    nlinarith [h]

/-- Blomberg's closed form, for n > 1. -/
theorem closed (n : ℕ) (hn : 1 < n) : (a n : ℤ) = 4 ^ n + 4 * 2 ^ n - 8 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have ht : 2 ^ (k + 2) - 1 = 2 * (2 * 2 ^ k - 1) + 1 := by rw [pow_add]; omega
  have h1 : a (k + 2) = (2 * (2 * 2 ^ k - 1) + 2) ^ 2 + 8 * (2 * 2 ^ k - 1) := by
    unfold a
    rw [count_eq, ht, on_odd _ (by omega)]
  rw [h1]
  have hc : ((2 * 2 ^ k - 1 : ℕ) : ℤ) = 2 * 2 ^ k - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_pow]; norm_num
  push_cast [hc]
  have e4 : (4 : ℤ) ^ (k + 2) = (2 ^ k) ^ 2 * 16 := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, show 2 * (k + 2) = k * 2 + 4 by ring,
      pow_add, pow_mul]
    norm_num
  rw [e4, pow_add (2 : ℤ) k 2]
  ring

theorem a_zero : a 0 = 1 := by
  unfold a
  rw [count_eq]
  decide

theorem a_one : a 1 = 5 := by
  unfold a
  rw [count_eq]
  decide

theorem val (n N : ℕ) (hn : 1 < n) (hN : (N : ℤ) = 4 ^ n + 4 * 2 ^ n - 8) : a n = N := by
  have h := (closed n hn).trans hN.symm
  exact_mod_cast h

/-- Controls: the entry's terms a(0..12). -/
theorem controls : a 0 = 1 ∧ a 1 = 5 ∧ a 2 = 24 ∧ a 3 = 88 ∧ a 4 = 312 ∧ a 5 = 1144 ∧
    a 6 = 4344 ∧ a 7 = 16888 ∧ a 8 = 66552 ∧ a 9 = 264184 ∧ a 10 = 1052664 ∧
    a 11 = 4202488 ∧ a 12 = 16793592 :=
  ⟨a_zero, a_one, val 2 24 (by norm_num) (by norm_num), val 3 88 (by norm_num) (by norm_num),
    val 4 312 (by norm_num) (by norm_num), val 5 1144 (by norm_num) (by norm_num),
    val 6 4344 (by norm_num) (by norm_num), val 7 16888 (by norm_num) (by norm_num),
    val 8 66552 (by norm_num) (by norm_num), val 9 264184 (by norm_num) (by norm_num),
    val 10 1052664 (by norm_num) (by norm_num), val 11 4202488 (by norm_num) (by norm_num),
    val 12 16793592 (by norm_num) (by norm_num)⟩

/-- Barker's recurrence, for n > 4. -/
theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, closed (m + 5) (by omega), closed (m + 4) (by omega),
    closed (m + 3) (by omega), closed (m + 2) (by omega)]
  ring

/-- Barker's g.f. with the denominator cleared. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
    1 - 2 * X + 3 * X ^ 2 - 18 * X ^ 3 - 8 * X ^ 4 := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have c2 : (C (2 : ℤ) : PowerSeries ℤ) = 2 := map_ofNat C 2
  have c3 : (C (3 : ℤ) : PowerSeries ℤ) = 3 := map_ofNat C 3
  have c7 : (C (7 : ℤ) : PowerSeries ℤ) = 7 := map_ofNat C 7
  have c8 : (C (8 : ℤ) : PowerSeries ℤ) = 8 := map_ofNat C 8
  have c14 : (C (14 : ℤ) : PowerSeries ℤ) = 14 := map_ofNat C 14
  have c18 : (C (18 : ℤ) : PowerSeries ℤ) = 18 := map_ofNat C 18
  have hD : A * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      A - C 7 * (A * X ^ 1) + C 14 * (A * X ^ 2) - C 8 * (A * X ^ 3) := by
    rw [c7, c8, c14]; ring
  have hN : (1 - 2 * X + 3 * X ^ 2 - 18 * X ^ 3 - 8 * X ^ 4 : PowerSeries ℤ) =
      1 - X ^ 1 * C 2 + X ^ 2 * C 3 - X ^ 3 * C 18 - X ^ 4 * C 8 := by
    rw [c2, c3, c8, c18]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', hA, coeff_mk,
    coeff_one, coeff_X_pow]
  obtain ⟨v0, v1, v2, v3, v4, -⟩ := controls
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp [v0, v1, v2, v3, v4]
  · have r := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, if_true,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
      show n ≠ 4 by omega, if_false]
    linear_combination r

/-- Blomberg's two conjectures and Barker's two. -/
theorem conjecture :
    (∀ n : ℕ, count state254 (2 ^ n - 1) = a n) ∧
    (∀ n : ℕ, 1 < n → (a n : ℤ) = 4 ^ n + 4 * 2 ^ n - 8) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      1 - 2 * X + 3 * X ^ 2 - 18 * X ^ 3 - 8 * X ^ 4 :=
  ⟨rule254, closed, recurrence, gf⟩

end OMA.S_oeis_a270682

theorem OMA.solution : type_of% @OMA.S_oeis_a270682.main :=
  OMA.S_oeis_a270682.conjecture

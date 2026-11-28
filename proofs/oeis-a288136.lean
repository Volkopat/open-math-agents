import OMAStatements.S_oeis_a288136

namespace OMA.S_oeis_a288136

open PowerSeries



/-- The pattern three or more cells inside the edge of the diamond, by t mod 3 and d mod 12. -/
def T (r s : ℕ) : Bool :=
  (r == 0 && (s == 2 || s == 3 || s == 4 || s == 5 || s == 6 || s == 8 || s == 10)) ||
  (r == 1 && (s == 0 || s == 2 || s == 6 || s == 7 || s == 8 || s == 9 || s == 10)) ||
  (r == 2 && (s == 0 || s == 1 || s == 2 || s == 4 || s == 6 || s == 10 || s == 11))

/-- The state at stage t of a cell at distance d = |x| + |y| from the origin. -/
def g (t d : ℕ) : Bool :=
  if t < d then t % 2 == 1 else if d + 3 ≤ t then T (t % 3) (d % 12)
  else if d + 1 = t then true else t % 2 == 0

theorem g_out {t d : ℕ} (h : t < d) : g t d = (t % 2 == 1) := by
  simp only [g, if_pos h]

theorem g_in {t d : ℕ} (h : d + 3 ≤ t) : g t d = T (t % 3) (d % 12) := by
  simp only [g, if_neg (show ¬t < d by omega), if_pos h]

theorem g_e1 {t d : ℕ} (h : d + 1 = t) : g t d = true := by
  simp only [g, if_neg (show ¬t < d by omega), if_neg (show ¬d + 3 ≤ t by omega), if_pos h]

theorem g_e02 {t d : ℕ} (h : d = t ∨ d + 2 = t) : g t d = (t % 2 == 0) := by
  simp only [g, if_neg (show ¬t < d by omega), if_neg (show ¬d + 3 ≤ t by omega),
    if_neg (show ¬d + 1 = t by omega)]

/-- The origin: four neighbors at distance 1. -/
theorem step0 (t : ℕ) :
    Nat.testBit 427 ((g t 0).toNat + 2 * (4 * (g t 1).toNat)) = g (t + 1) 0 := by
  rcases (by omega : t ≤ 3 ∨ 4 ≤ t) with ht | ht
  · interval_cases t <;> rfl
  · rw [g_in (by omega : 0 + 3 ≤ t), g_in (by omega : 1 + 3 ≤ t),
      g_in (by omega : 0 + 3 ≤ t + 1), show (t + 1) % 3 = (t % 3 + 1) % 3 by omega]
    have hr : t % 3 < 3 := Nat.mod_lt _ (by norm_num)
    generalize t % 3 = r at *
    interval_cases r <;> rfl

/-- A cell on an axis: one neighbor at distance d - 1, three at d + 1. -/
theorem step1 (t d : ℕ) (hd : 1 ≤ d) :
    Nat.testBit 427 ((g t d).toNat + 2 * ((g t (d - 1)).toNat + 3 * (g t (d + 1)).toNat)) =
      g (t + 1) d := by
  have p1 : (t + 1) % 2 = (t % 2 + 1) % 2 := by omega
  have p2 : t % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have q2 : t % 12 < 12 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : d + 4 ≤ t ∨ d + 3 = t ∨ d + 2 = t ∨ d + 1 = t ∨ d = t ∨ d = t + 1 ∨
    t + 2 ≤ d) with c | c | c | c | c | c | c
  · rw [g_in (by omega : d + 3 ≤ t), g_in (by omega : d - 1 + 3 ≤ t),
      g_in (by omega : d + 1 + 3 ≤ t), g_in (by omega : d + 3 ≤ t + 1),
      show (t + 1) % 3 = (t % 3 + 1) % 3 by omega,
      show (d - 1) % 12 = (d % 12 + 11) % 12 by omega,
      show (d + 1) % 12 = (d % 12 + 1) % 12 by omega]
    have hr : t % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hs : d % 12 < 12 := Nat.mod_lt _ (by norm_num)
    generalize t % 3 = r at *
    generalize d % 12 = s at *
    interval_cases r <;> interval_cases s <;> rfl
  · rw [g_in (by omega : d + 3 ≤ t), g_in (by omega : d - 1 + 3 ≤ t),
      g_e02 (by omega : d + 1 = t ∨ d + 1 + 2 = t), g_in (by omega : d + 3 ≤ t + 1),
      show (t + 1) % 3 = (t % 12 + 1) % 3 by omega, show t % 3 = t % 12 % 3 by omega,
      show d % 12 = (t % 12 + 9) % 12 by omega, show (d - 1) % 12 = (t % 12 + 8) % 12 by omega,
      show t % 2 = t % 12 % 2 by omega]
    generalize t % 12 = r at *
    interval_cases r <;> rfl
  · rw [g_e02 (by omega : d = t ∨ d + 2 = t), g_in (by omega : d - 1 + 3 ≤ t),
      g_e1 (by omega : d + 1 + 1 = t), g_in (by omega : d + 3 ≤ t + 1),
      show (t + 1) % 3 = (t % 12 + 1) % 3 by omega, show t % 3 = t % 12 % 3 by omega,
      show d % 12 = (t % 12 + 10) % 12 by omega, show (d - 1) % 12 = (t % 12 + 9) % 12 by omega,
      show t % 2 = t % 12 % 2 by omega]
    generalize t % 12 = r at *
    interval_cases r <;> rfl
  · rw [g_e1 (by omega : d + 1 = t), g_e02 (by omega : d - 1 = t ∨ d - 1 + 2 = t),
      g_e02 (by omega : d + 1 = t ∨ d + 1 + 2 = t), g_e02 (by omega : d = t + 1 ∨ d + 2 = t + 1),
      p1]
    generalize t % 2 = r at *
    interval_cases r <;> rfl
  · rw [g_e02 (by omega : d = t ∨ d + 2 = t), g_e1 (by omega : d - 1 + 1 = t),
      g_out (by omega : t < d + 1), g_e1 (by omega : d + 1 = t + 1)]
    generalize t % 2 = r at *
    interval_cases r <;> rfl
  · rw [g_out (by omega : t < d), g_e02 (by omega : d - 1 = t ∨ d - 1 + 2 = t),
      g_out (by omega : t < d + 1), g_e02 (by omega : d = t + 1 ∨ d + 2 = t + 1), p1]
    generalize t % 2 = r at *
    interval_cases r <;> rfl
  · rw [g_out (by omega : t < d), g_out (by omega : t < d - 1), g_out (by omega : t < d + 1),
      g_out (by omega : t + 1 < d), p1]
    generalize t % 2 = r at *
    interval_cases r <;> rfl

/-- A cell off the axes: two neighbors at distance d - 1, two at d + 1. -/
theorem step2 (t d : ℕ) (hd : 2 ≤ d) :
    Nat.testBit 427 ((g t d).toNat +
      2 * (2 * (g t (d - 1)).toNat + 2 * (g t (d + 1)).toNat)) = g (t + 1) d := by
  have p1 : (t + 1) % 2 = (t % 2 + 1) % 2 := by omega
  have p2 : t % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have q2 : t % 12 < 12 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : d + 4 ≤ t ∨ d + 3 = t ∨ d + 2 = t ∨ d + 1 = t ∨ d = t ∨ d = t + 1 ∨
    t + 2 ≤ d) with c | c | c | c | c | c | c
  · rw [g_in (by omega : d + 3 ≤ t), g_in (by omega : d - 1 + 3 ≤ t),
      g_in (by omega : d + 1 + 3 ≤ t), g_in (by omega : d + 3 ≤ t + 1),
      show (t + 1) % 3 = (t % 3 + 1) % 3 by omega,
      show (d - 1) % 12 = (d % 12 + 11) % 12 by omega,
      show (d + 1) % 12 = (d % 12 + 1) % 12 by omega]
    have hr : t % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hs : d % 12 < 12 := Nat.mod_lt _ (by norm_num)
    generalize t % 3 = r at *
    generalize d % 12 = s at *
    interval_cases r <;> interval_cases s <;> rfl
  · rw [g_in (by omega : d + 3 ≤ t), g_in (by omega : d - 1 + 3 ≤ t),
      g_e02 (by omega : d + 1 = t ∨ d + 1 + 2 = t), g_in (by omega : d + 3 ≤ t + 1),
      show (t + 1) % 3 = (t % 12 + 1) % 3 by omega, show t % 3 = t % 12 % 3 by omega,
      show d % 12 = (t % 12 + 9) % 12 by omega, show (d - 1) % 12 = (t % 12 + 8) % 12 by omega,
      show t % 2 = t % 12 % 2 by omega]
    generalize t % 12 = r at *
    interval_cases r <;> rfl
  · rw [g_e02 (by omega : d = t ∨ d + 2 = t), g_in (by omega : d - 1 + 3 ≤ t),
      g_e1 (by omega : d + 1 + 1 = t), g_in (by omega : d + 3 ≤ t + 1),
      show (t + 1) % 3 = (t % 12 + 1) % 3 by omega, show t % 3 = t % 12 % 3 by omega,
      show d % 12 = (t % 12 + 10) % 12 by omega, show (d - 1) % 12 = (t % 12 + 9) % 12 by omega,
      show t % 2 = t % 12 % 2 by omega]
    generalize t % 12 = r at *
    interval_cases r <;> rfl
  · rw [g_e1 (by omega : d + 1 = t), g_e02 (by omega : d - 1 = t ∨ d - 1 + 2 = t),
      g_e02 (by omega : d + 1 = t ∨ d + 1 + 2 = t), g_e02 (by omega : d = t + 1 ∨ d + 2 = t + 1),
      p1]
    generalize t % 2 = r at *
    interval_cases r <;> rfl
  · rw [g_e02 (by omega : d = t ∨ d + 2 = t), g_e1 (by omega : d - 1 + 1 = t),
      g_out (by omega : t < d + 1), g_e1 (by omega : d + 1 = t + 1)]
    generalize t % 2 = r at *
    interval_cases r <;> rfl
  · rw [g_out (by omega : t < d), g_e02 (by omega : d - 1 = t ∨ d - 1 + 2 = t),
      g_out (by omega : t < d + 1), g_e02 (by omega : d = t + 1 ∨ d + 2 = t + 1), p1]
    generalize t % 2 = r at *
    interval_cases r <;> rfl
  · rw [g_out (by omega : t < d), g_out (by omega : t < d - 1), g_out (by omega : t < d + 1),
      g_out (by omega : t + 1 < d), p1]
    generalize t % 2 = r at *
    interval_cases r <;> rfl

/-- Stage t is the pattern `g` of the distance |x| + |y|. -/
theorem state_pattern (t : ℕ) : ∀ x y, state t x y = g t (x.natAbs + y.natAbs) := by
  induction t with
  | zero =>
    intro x y
    by_cases h : x = 0 ∧ y = 0
    · rw [show state 0 x y = decide (x = 0 ∧ y = 0) from rfl, decide_eq_true h,
        show x.natAbs + y.natAbs = 0 by omega]
      rfl
    · rw [show state 0 x y = decide (x = 0 ∧ y = 0) from rfl, decide_eq_false h,
        g_out (by omega : 0 < x.natAbs + y.natAbs)]
      rfl
  | succ t ih =>
    intro x y
    show Nat.testBit 427 _ = _
    rw [ih, ih, ih, ih, ih]
    rcases lt_trichotomy x 0 with hx | hx | hx <;> rcases lt_trichotomy y 0 with hy | hy | hy
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        ← step2 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step1 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step2 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        ← step1 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = 1 by omega,
        show (x + 1).natAbs + y.natAbs = 1 by omega,
        show x.natAbs + (y - 1).natAbs = 1 by omega,
        show x.natAbs + (y + 1).natAbs = 1 by omega,
        show x.natAbs + y.natAbs = 0 by omega, ← step0 t]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step1 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        ← step2 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step1 t _ (by omega)]
      congr 1; ring
    · rw [show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega,
        show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega,
        show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega,
        show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega,
        ← step2 t _ (by omega)]
      congr 1; ring

/-- On the diagonal, far inside: the cell (k, k) is OFF exactly when k = 2n mod 6. -/
theorem T_diag (r s : ℕ) (hr : r < 3) (hs : s < 6) : T r (2 * s) = !decide (s = 2 * r) := by
  interval_cases r <;> interval_cases s <;> rfl

/-- The diagonal cell (k, k) of stage n is OFF exactly outside the diamond at even n, or three or
more cells inside the edge with k = 2n mod 6. -/
theorem diag (n k : ℕ) :
    g n (2 * k) = !(decide (n < 2 * k ∧ n % 2 = 0) || decide (2 * k + 3 ≤ n ∧ k % 6 = 2 * n % 6)) := by
  rcases (by omega : n < 2 * k ∨ 2 * k + 3 ≤ n ∨ (2 * k ≤ n ∧ n ≤ 2 * k + 2)) with h | h | h
  · rw [g_out h, decide_eq_false (show ¬(2 * k + 3 ≤ n ∧ k % 6 = 2 * n % 6) by omega)]
    rcases Nat.mod_two_eq_zero_or_one n with p | p
    · rw [decide_eq_true (show n < 2 * k ∧ n % 2 = 0 from ⟨h, p⟩), p]; rfl
    · rw [decide_eq_false (show ¬(n < 2 * k ∧ n % 2 = 0) by omega), p]; rfl
  · have hT : T (n % 3) (2 * k % 12) = !decide (k % 6 = 2 * n % 6) := by
      rw [show 2 * k % 12 = 2 * (k % 6) by omega, show 2 * n % 6 = 2 * (n % 3) by omega]
      exact T_diag _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    rw [g_in h, hT, decide_eq_false (show ¬(n < 2 * k ∧ n % 2 = 0) by omega)]
    by_cases q : k % 6 = 2 * n % 6
    · rw [decide_eq_true q, decide_eq_true (show 2 * k + 3 ≤ n ∧ k % 6 = 2 * n % 6 from ⟨h, q⟩)]
      rfl
    · rw [decide_eq_false q, decide_eq_false (show ¬(2 * k + 3 ≤ n ∧ k % 6 = 2 * n % 6) by tauto)]
      rfl
  · rw [decide_eq_false (show ¬(n < 2 * k ∧ n % 2 = 0) by omega),
      decide_eq_false (show ¬(2 * k + 3 ≤ n ∧ k % 6 = 2 * n % 6) by omega)]
    rcases (by omega : 2 * k + 1 = n ∨ 2 * k = n ∨ 2 * k + 2 = n) with e | e | e
    · rw [g_e1 e]; rfl
    · rw [g_e02 (Or.inl e), show n % 2 = 0 by omega]; rfl
    · rw [g_e02 (Or.inr e), show n % 2 = 0 by omega]; rfl
theorem a_eq (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n + 1), if g n (2 * k) then 10 ^ (n - k) else 0 := by
  unfold a
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [state_pattern, show ((k : ℤ)).natAbs + ((k : ℤ)).natAbs = 2 * k by simp; ring]

/-- Controls: the entry's terms a(0..14). -/
theorem controls : (List.range 15).map a = [1, 11, 110, 111, 11100, 111111, 111000, 11011111,
    111110000, 111111111, 11011100000, 111101111111, 111111000000, 11011111111111,
    111101110000000] := by
  rw [show a = fun n => ∑ k ∈ Finset.range (n + 1), if g n (2 * k) then 10 ^ (n - k) else 0
    from funext a_eq]
  decide

/-! ### Splitting the diagonal into all cells minus the two kinds of OFF cells -/

/-- All cells. -/
def c1 (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (10 : ℤ) ^ (n - k)

/-- The OFF cells outside the diamond (at even stages). -/
def c2 (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if n < 2 * k ∧ n % 2 = 0 then (10 : ℤ) ^ (n - k) else 0

/-- The OFF cells three or more cells inside the edge. -/
def c3 (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if 2 * k + 3 ≤ n ∧ k % 6 = 2 * n % 6 then (10 : ℤ) ^ (n - k) else 0

theorem a_split (n : ℕ) : (a n : ℤ) = c1 n - c2 n - c3 n := by
  unfold c1 c2 c3
  rw [a_eq, Nat.cast_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [diag n k]
  by_cases h1 : n < 2 * k ∧ n % 2 = 0
  · rw [decide_eq_true h1, if_pos h1,
      if_neg (show ¬(2 * k + 3 ≤ n ∧ k % 6 = 2 * n % 6) by omega)]
    simp
  · by_cases h2 : 2 * k + 3 ≤ n ∧ k % 6 = 2 * n % 6
    · rw [decide_eq_false h1, decide_eq_true h2, if_neg h1, if_pos h2]
      simp
    · rw [decide_eq_false h1, decide_eq_false h2, if_neg h1, if_neg h2]
      simp

theorem c1_succ (n : ℕ) : c1 (n + 1) = 10 * c1 n + 1 := by
  unfold c1
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_range] at hk
  rw [show n + 1 - k = n - k + 1 by omega, pow_succ]
  ring

/-- The diagonal cells beyond k = m, read from the corner end, summed up to m + j (times 9). -/
theorem lower (m j : ℕ) :
    9 * ∑ k ∈ Finset.range (m + 1 + j), (if m < k then (10 : ℤ) ^ (m + j - k) else 0) =
      10 ^ j - 1 := by
  induction j with
  | zero =>
    rw [Finset.sum_eq_zero (fun k hk => by simp only [Finset.mem_range] at hk; simp; omega)]
    simp
  | succ j ih =>
    rw [← add_assoc, Finset.sum_range_succ, if_pos (by omega),
      show m + (j + 1) - (m + 1 + j) = 0 by omega, pow_zero]
    have e : ∑ k ∈ Finset.range (m + 1 + j), (if m < k then (10 : ℤ) ^ (m + (j + 1) - k) else 0) =
        10 * ∑ k ∈ Finset.range (m + 1 + j), (if m < k then (10 : ℤ) ^ (m + j - k) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [Finset.mem_range] at hk
      split_ifs
      · rw [show m + (j + 1) - k = m + j - k + 1 by omega, pow_succ]; ring
      · ring
    rw [e, mul_add, ← mul_assoc, mul_comm (9 : ℤ) 10, mul_assoc, ih, pow_succ]
    ring

theorem c2_eq (n : ℕ) : 9 * c2 n = if n % 2 = 0 then 10 ^ (n / 2) - 1 else 0 := by
  unfold c2
  rcases Nat.mod_two_eq_zero_or_one n with p | p
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    rw [if_pos p, show 2 * m / 2 = m by omega, ← lower m m, show 2 * m + 1 = m + 1 + m by ring]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : m < k
    · rw [if_pos ⟨by omega, p⟩, if_pos h, show 2 * m - k = m + m - k by omega]
    · rw [if_neg (by omega), if_neg h]
  · rw [if_neg (by omega), Finset.sum_eq_zero (fun k _ => if_neg (by omega)), mul_zero]

theorem c3_rec (n : ℕ) :
    c3 (n + 3) = 1000 * c3 n + (if n % 4 = 0 then (10 : ℤ) ^ (n + 3 - n / 2) else 0) := by
  have hpt : ∀ k, (if 2 * k + 3 ≤ n + 3 ∧ k % 6 = 2 * (n + 3) % 6 then (10 : ℤ) ^ (n + 3 - k)
      else 0) = 1000 * (if 2 * k + 3 ≤ n ∧ k % 6 = 2 * n % 6 then (10 : ℤ) ^ (n - k) else 0) +
        (if k = n / 2 ∧ n % 4 = 0 then (10 : ℤ) ^ (n + 3 - k) else 0) := by
    intro k
    split_ifs <;> first | (exfalso; omega) |
      (rw [show n + 3 - k = n - k + 3 by omega, pow_add]; ring) | ring
  have hext : c3 n = ∑ k ∈ Finset.range (n + 3 + 1),
      (if 2 * k + 3 ≤ n ∧ k % 6 = 2 * n % 6 then (10 : ℤ) ^ (n - k) else 0) := by
    have z : ∑ j ∈ Finset.range 3, (if 2 * (n + 1 + j) + 3 ≤ n ∧ (n + 1 + j) % 6 = 2 * n % 6
        then (10 : ℤ) ^ (n - (n + 1 + j)) else 0) = 0 :=
      Finset.sum_eq_zero (fun j _ => if_neg (by omega))
    rw [show n + 3 + 1 = n + 1 + 3 by ring, Finset.sum_range_add _ (n + 1) 3, z, add_zero]
    rfl
  have hone : ∑ k ∈ Finset.range (n + 3 + 1),
      (if k = n / 2 ∧ n % 4 = 0 then (10 : ℤ) ^ (n + 3 - k) else 0) =
      if n % 4 = 0 then (10 : ℤ) ^ (n + 3 - n / 2) else 0 := by
    rw [Finset.sum_eq_single (n / 2)]
    · by_cases h : n % 4 = 0
      · rw [if_pos ⟨rfl, h⟩, if_pos h]
      · rw [if_neg (fun hh => h hh.2), if_neg h]
    · intro k _ hk; rw [if_neg (fun hh => hk hh.1)]
    · intro h; simp only [Finset.mem_range] at h; omega
  rw [hext, ← hone, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => hpt k)

/-! ### The three generating functions and their combination -/

theorem G1 : mk c1 * ((1 - X) * (1 - 10 * X)) = 1 := by
  have h10 : (C (10 : ℤ) : PowerSeries ℤ) = 10 := map_ofNat C 10
  have h11 : (C (11 : ℤ) : PowerSeries ℤ) = 11 := map_ofNat C 11
  have hD : mk c1 * ((1 - X) * (1 - 10 * X)) =
      mk c1 - C 11 * (mk c1 * X ^ 1) + C 10 * (mk c1 * X ^ 2) := by rw [h10, h11]; ring
  rw [hD]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_one]
  rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with rfl | rfl | h
  · simp [c1]
  · simp [c1, Finset.sum_range_succ]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [if_pos (by omega : 1 ≤ m + 2), if_pos (by omega : 2 ≤ m + 2), if_neg (by omega : m + 2 ≠ 0),
      show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega, c1_succ (m + 1), c1_succ m]
    ring

theorem G2 : mk c2 * ((1 - 10 * X ^ 2) * (1 - X ^ 2)) = X ^ 2 := by
  have h10 : (C (10 : ℤ) : PowerSeries ℤ) = 10 := map_ofNat C 10
  have h11 : (C (11 : ℤ) : PowerSeries ℤ) = 11 := map_ofNat C 11
  have hD : mk c2 * ((1 - 10 * X ^ 2) * (1 - X ^ 2)) =
      mk c2 - C 11 * (mk c2 * X ^ 2) + C 10 * (mk c2 * X ^ 4) := by rw [h10, h11]; ring
  rw [hD]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
  rcases (by omega : n < 4 ∨ 4 ≤ n) with h | h
  · interval_cases n <;> simp [c2, Finset.sum_range_succ]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [if_pos (by omega : 2 ≤ m + 4), if_pos (by omega : 4 ≤ m + 4), if_neg (by omega : m + 4 ≠ 2),
      show m + 4 - 2 = m + 2 by omega, show m + 4 - 4 = m by omega]
    have e1 := c2_eq (m + 4)
    have e2 := c2_eq (m + 2)
    have e3 := c2_eq m
    rcases Nat.mod_two_eq_zero_or_one m with p | p
    · obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j := ⟨m / 2, by omega⟩
      rw [if_pos (by omega), show (2 * j + 4) / 2 = j + 2 by omega] at e1
      rw [if_pos (by omega), show (2 * j + 2) / 2 = j + 1 by omega] at e2
      rw [if_pos (by omega), show 2 * j / 2 = j by omega] at e3
      have key : (9 : ℤ) * (c2 (2 * j + 4) - 11 * c2 (2 * j + 2) + 10 * c2 (2 * j)) = 0 := by
        linear_combination e1 - 11 * e2 + 10 * e3
      omega
    · rw [if_neg (by omega)] at e1 e2 e3
      omega

theorem G3 : mk c3 * ((1 - 1000 * X ^ 3) * (1 - 100 * X ^ 4)) = 1000 * X ^ 3 := by
  have h100 : (C (100 : ℤ) : PowerSeries ℤ) = 100 := map_ofNat C 100
  have h1000 : (C (1000 : ℤ) : PowerSeries ℤ) = 1000 := map_ofNat C 1000
  have h100000 : (C (100000 : ℤ) : PowerSeries ℤ) = 100000 := map_ofNat C 100000
  have hD : mk c3 * ((1 - 1000 * X ^ 3) * (1 - 100 * X ^ 4)) =
      mk c3 - C 1000 * (mk c3 * X ^ 3) - C 100 * (mk c3 * X ^ 4) + C 100000 * (mk c3 * X ^ 7) := by
    rw [h100, h1000, h100000]; ring
  have hN : (1000 * X ^ 3 : PowerSeries ℤ) = X ^ 3 * C 1000 := by rw [h1000]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
  rcases (by omega : n < 7 ∨ 7 ≤ n) with h | h
  · interval_cases n <;> simp [c3, Finset.sum_range_succ]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    rw [if_pos (by omega : 3 ≤ m + 7), if_pos (by omega : 4 ≤ m + 7), if_pos (by omega : 7 ≤ m + 7),
      if_neg (by omega : m + 7 ≠ 3), show m + 7 - 3 = m + 4 by omega,
      show m + 7 - 4 = m + 3 by omega, show m + 7 - 7 = m by omega]
    have r1 := c3_rec (m + 4)
    have r2 := c3_rec m
    rw [show m + 4 + 3 - (m + 4) / 2 = m + 3 - m / 2 + 2 by omega, show m + 4 + 3 = m + 7 by ring,
      show (m + 4) % 4 = m % 4 by omega] at r1
    rw [r1, r2]
    split_ifs
    · rw [pow_add]; ring
    · ring

/-- Barker's g.f. with the denominator cleared. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 - 10 * X ^ 2) *
    (1 + 10 * X ^ 2) * (1 + 10 * X + 100 * X ^ 2)) =
      1 + 11 * X + 109 * X ^ 2 - 900 * X ^ 3 - 110 * X ^ 4 + 900 * X ^ 5 - 11000 * X ^ 6 := by
  have hA : mk (fun n => (a n : ℤ)) = mk c1 - mk c2 - mk c3 := by
    ext n; simp [a_split]
  have e : (mk c1 - mk c2 - mk c3) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 - 10 * X ^ 2) *
      (1 + 10 * X ^ 2) * (1 + 10 * X + 100 * X ^ 2)) =
      mk c1 * ((1 - X) * (1 - 10 * X)) * ((1 + X) * (1 - 10 * X ^ 2) * (1 + 10 * X ^ 2) *
        (1 + 10 * X + 100 * X ^ 2)) -
      mk c2 * ((1 - 10 * X ^ 2) * (1 - X ^ 2)) *
        ((1 - 10 * X) * (1 + 10 * X ^ 2) * (1 + 10 * X + 100 * X ^ 2)) -
      mk c3 * ((1 - 1000 * X ^ 3) * (1 - 100 * X ^ 4)) * ((1 - X) * (1 + X)) := by ring
  rw [hA, e, G1, G2, G3]
  ring

/-- Barker's conjecture. -/
theorem conjecture : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 10 * X) *
    (1 - 10 * X ^ 2) * (1 + 10 * X ^ 2) * (1 + 10 * X + 100 * X ^ 2)) =
      1 + 11 * X + 109 * X ^ 2 - 900 * X ^ 3 - 110 * X ^ 4 + 900 * X ^ 5 - 11000 * X ^ 6 := gf

end OMA.S_oeis_a288136

theorem OMA.solution : type_of% @OMA.S_oeis_a288136.main :=
  OMA.S_oeis_a288136.conjecture

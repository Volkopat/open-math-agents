import OMAStatements.S_oeis_a288137

namespace OMA.S_oeis_a288137

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

theorem a_eq (n : ℕ) : a n = ∑ k ∈ Finset.range (n + 1), if g n (2 * k) then 2 ^ k else 0 := by
  unfold a
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [state_pattern, show ((k : ℤ)).natAbs + ((k : ℤ)).natAbs = 2 * k by simp; ring]

/-- Controls: the entry's terms a(0..17). -/
theorem controls : (List.range 18).map a = [1, 3, 3, 14, 7, 63, 14, 251, 31, 1022, 59, 4079, 126,
    16379, 239, 65470, 507, 262127] := by
  rw [show a = fun n => ∑ k ∈ Finset.range (n + 1), if g n (2 * k) then 2 ^ k else 0
    from funext a_eq]
  decide

/-! ### Splitting the diagonal into all cells minus the two kinds of OFF cells -/

/-- All cells. -/
def c1 (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (2 : ℤ) ^ k

/-- The OFF cells outside the diamond (at even stages). -/
def c2 (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), if n < 2 * k ∧ n % 2 = 0 then (2 : ℤ) ^ k else 0

/-- The OFF cells three or more cells inside the edge. -/
def c3 (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if 2 * k + 3 ≤ n ∧ k % 6 = 2 * n % 6 then (2 : ℤ) ^ k else 0

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

theorem geom (n : ℕ) : ∑ k ∈ Finset.range n, (2 : ℤ) ^ k = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem c1_eq (n : ℕ) : c1 n = 2 ^ (n + 1) - 1 := geom (n + 1)

/-- The diagonal cells beyond k = m, summed up to m + j. -/
theorem upper (m j : ℕ) : ∑ k ∈ Finset.range (m + 1 + j), (if m < k then (2 : ℤ) ^ k else 0) =
    2 ^ (m + 1 + j) - 2 ^ (m + 1) := by
  induction j with
  | zero =>
    rw [add_zero, sub_self]
    exact Finset.sum_eq_zero (fun k hk => by simp only [Finset.mem_range] at hk; simp; omega)
  | succ j ih =>
    rw [← add_assoc, Finset.sum_range_succ, ih, if_pos (by omega), pow_succ]
    ring

theorem c2_eq (n : ℕ) : c2 n = if n % 2 = 0 then 2 ^ (n + 1) - 2 ^ (n / 2 + 1) else 0 := by
  unfold c2
  rcases Nat.mod_two_eq_zero_or_one n with p | p
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    rw [if_pos p, show 2 * m / 2 = m by omega, show 2 * m + 1 = m + 1 + m by ring, ← upper m m]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : m < k
    · rw [if_pos ⟨by omega, p⟩, if_pos h]
    · rw [if_neg (by omega), if_neg h]
  · rw [if_neg (by omega)]
    exact Finset.sum_eq_zero (fun k _ => if_neg (by omega))

theorem c3_rec (n : ℕ) : c3 (n + 3) = c3 n + (if n % 4 = 0 then (2 : ℤ) ^ (n / 2) else 0) := by
  have hpt : ∀ k, (if 2 * k + 3 ≤ n + 3 ∧ k % 6 = 2 * (n + 3) % 6 then (2 : ℤ) ^ k else 0) =
      (if 2 * k + 3 ≤ n ∧ k % 6 = 2 * n % 6 then (2 : ℤ) ^ k else 0) +
        (if k = n / 2 ∧ n % 4 = 0 then (2 : ℤ) ^ k else 0) := by
    intro k
    split_ifs <;> first | (exfalso; omega) | ring
  have hext : c3 n = ∑ k ∈ Finset.range (n + 3 + 1),
      (if 2 * k + 3 ≤ n ∧ k % 6 = 2 * n % 6 then (2 : ℤ) ^ k else 0) := by
    have z : ∑ j ∈ Finset.range 3, (if 2 * (n + 1 + j) + 3 ≤ n ∧ (n + 1 + j) % 6 = 2 * n % 6
        then (2 : ℤ) ^ (n + 1 + j) else 0) = 0 :=
      Finset.sum_eq_zero (fun j _ => if_neg (by omega))
    rw [show n + 3 + 1 = n + 1 + 3 by ring, Finset.sum_range_add _ (n + 1) 3, z, add_zero]
    rfl
  have hone : ∑ k ∈ Finset.range (n + 3 + 1), (if k = n / 2 ∧ n % 4 = 0 then (2 : ℤ) ^ k else 0) =
      if n % 4 = 0 then (2 : ℤ) ^ (n / 2) else 0 := by
    rw [Finset.sum_eq_single (n / 2)]
    · by_cases h : n % 4 = 0
      · rw [if_pos ⟨rfl, h⟩, if_pos h]
      · rw [if_neg (fun hh => h hh.2), if_neg h]
    · intro k _ hk; rw [if_neg (fun hh => hk hh.1)]
    · intro h; simp only [Finset.mem_range] at h; omega
  rw [hext, ← hone, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => hpt k)

/-! ### The three generating functions and their combination -/

theorem G1 : mk c1 * ((1 - X) * (1 - 2 * X)) = 1 := by
  have h2 : (C (2 : ℤ) : PowerSeries ℤ) = 2 := map_ofNat C 2
  have h3 : (C (3 : ℤ) : PowerSeries ℤ) = 3 := map_ofNat C 3
  have hD : mk c1 * ((1 - X) * (1 - 2 * X)) =
      mk c1 - C 3 * (mk c1 * X ^ 1) + C 2 * (mk c1 * X ^ 2) := by rw [h2, h3]; ring
  rw [hD]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_one]
  rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with rfl | rfl | h
  · rw [c1_eq]; norm_num
  · rw [c1_eq, c1_eq]; norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [if_pos (by omega : 1 ≤ m + 2), if_pos (by omega : 2 ≤ m + 2), if_neg (by omega : m + 2 ≠ 0),
      show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega, c1_eq, c1_eq, c1_eq]
    ring

theorem G2 : mk c2 * ((1 - 4 * X ^ 2) * (1 - 2 * X ^ 2)) = 4 * X ^ 2 := by
  have h4 : (C (4 : ℤ) : PowerSeries ℤ) = 4 := map_ofNat C 4
  have h6 : (C (6 : ℤ) : PowerSeries ℤ) = 6 := map_ofNat C 6
  have h8 : (C (8 : ℤ) : PowerSeries ℤ) = 8 := map_ofNat C 8
  have hD : mk c2 * ((1 - 4 * X ^ 2) * (1 - 2 * X ^ 2)) =
      mk c2 - C 6 * (mk c2 * X ^ 2) + C 8 * (mk c2 * X ^ 4) := by rw [h6, h8]; ring
  have hN : (4 * X ^ 2 : PowerSeries ℤ) = X ^ 2 * C 4 := by rw [h4]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
  rcases (by omega : n < 4 ∨ 4 ≤ n) with h | h
  · interval_cases n <;> simp [c2_eq]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [if_pos (by omega : 2 ≤ m + 4), if_pos (by omega : 4 ≤ m + 4), if_neg (by omega : m + 4 ≠ 2),
      show m + 4 - 2 = m + 2 by omega, show m + 4 - 4 = m by omega, c2_eq, c2_eq, c2_eq]
    rcases Nat.mod_two_eq_zero_or_one m with p | p
    · obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j := ⟨m / 2, by omega⟩
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
        show (2 * j + 4) / 2 = j + 2 by omega, show (2 * j + 2) / 2 = j + 1 by omega,
        show 2 * j / 2 = j by omega]
      ring
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      ring

theorem G3 : mk c3 * ((1 - X ^ 3) * (1 - 4 * X ^ 4)) = X ^ 3 := by
  have h4 : (C (4 : ℤ) : PowerSeries ℤ) = 4 := map_ofNat C 4
  have hD : mk c3 * ((1 - X ^ 3) * (1 - 4 * X ^ 4)) =
      mk c3 - mk c3 * X ^ 3 - C 4 * (mk c3 * X ^ 4) + C 4 * (mk c3 * X ^ 7) := by rw [h4]; ring
  rw [hD]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
  rcases (by omega : n < 7 ∨ 7 ≤ n) with h | h
  · interval_cases n <;> simp [c3, Finset.sum_range_succ]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    rw [if_pos (by omega : 3 ≤ m + 7), if_pos (by omega : 4 ≤ m + 7), if_pos (by omega : 7 ≤ m + 7),
      if_neg (by omega : m + 7 ≠ 3), show m + 7 - 3 = m + 4 by omega,
      show m + 7 - 4 = m + 3 by omega, show m + 7 - 7 = m by omega]
    have r1 := c3_rec (m + 4)
    have r2 := c3_rec m
    rw [show m + 4 + 3 = m + 7 by ring, show (m + 4) % 4 = m % 4 by omega,
      show (m + 4) / 2 = m / 2 + 2 by omega] at r1
    rw [r1, r2]
    split_ifs <;> ring

/-- Barker's g.f. with the denominator cleared. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 + 2 * X) * (1 + X + X ^ 2) *
    (1 - 2 * X ^ 2) * (1 + 2 * X ^ 2)) =
      1 + 3 * X - X ^ 2 + X ^ 3 - 12 * X ^ 4 - 4 * X ^ 5 - 12 * X ^ 6 := by
  have hA : mk (fun n => (a n : ℤ)) = mk c1 - mk c2 - mk c3 := by
    ext n; simp [a_split]
  have e : (mk c1 - mk c2 - mk c3) * ((1 - X) * (1 - 2 * X) * (1 + 2 * X) * (1 + X + X ^ 2) *
      (1 - 2 * X ^ 2) * (1 + 2 * X ^ 2)) =
      mk c1 * ((1 - X) * (1 - 2 * X)) * ((1 + 2 * X) * (1 + X + X ^ 2) * (1 - 2 * X ^ 2) *
        (1 + 2 * X ^ 2)) -
      mk c2 * ((1 - 4 * X ^ 2) * (1 - 2 * X ^ 2)) * ((1 - X) * (1 + X + X ^ 2) * (1 + 2 * X ^ 2)) -
      mk c3 * ((1 - X ^ 3) * (1 - 4 * X ^ 4)) * ((1 - 2 * X) * (1 + 2 * X)) := by ring
  rw [hA, e, G1, G2, G3]
  ring

/-- Barker's conjecture. -/
theorem conjecture : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 + 2 * X) *
    (1 + X + X ^ 2) * (1 - 2 * X ^ 2) * (1 + 2 * X ^ 2)) =
      1 + 3 * X - X ^ 2 + X ^ 3 - 12 * X ^ 4 - 4 * X ^ 5 - 12 * X ^ 6 := gf

end OMA.S_oeis_a288137

theorem OMA.solution : type_of% @OMA.S_oeis_a288137.main :=
  OMA.S_oeis_a288137.conjecture

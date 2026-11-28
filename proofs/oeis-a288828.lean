import OMAStatements.S_oeis_a288828

namespace OMA.S_oeis_a288828

open PowerSeries



/-- The pattern: ON outside the diamond, inside ON at even distances at least 2 from the edge,
with the origin exceptional at stage 1. -/
def g (t d : ℕ) : Bool :=
  if t = 0 then d == 0 else if t < d then true else if d = 0 ∧ t = 1 then true
  else decide (d + 2 ≤ t) && d % 2 == 0

theorem g0_pos {d : ℕ} (h : 0 < d) : g 0 d = false := by
  simp only [g, if_pos rfl]; simp; omega

theorem g_out {t d : ℕ} (ht : 0 < t) (h : t < d) : g t d = true := by
  simp only [g, if_neg (Nat.pos_iff_ne_zero.mp ht), if_pos h]

theorem g_in {t d : ℕ} (ht : 2 ≤ t) (h : d + 2 ≤ t) : g t d = (d % 2 == 0) := by
  simp only [g, if_neg (show t ≠ 0 by omega), if_neg (show ¬t < d by omega),
    if_neg (show ¬(d = 0 ∧ t = 1) by omega), decide_eq_true h, Bool.true_and]

theorem g_edge {t d : ℕ} (ht : 2 ≤ t) (h1 : t ≤ d + 1) (h2 : d ≤ t) : g t d = false := by
  simp only [g, if_neg (show t ≠ 0 by omega), if_neg (show ¬t < d by omega),
    if_neg (show ¬(d = 0 ∧ t = 1) by omega), decide_eq_false (show ¬d + 2 ≤ t by omega),
    Bool.false_and]

/-- The origin: four neighbors at distance 1. -/
theorem step0 (t : ℕ) :
    Nat.testBit 515 ((g t 0).toNat + 2 * (4 * (g t 1).toNat)) = g (t + 1) 0 := by
  rcases (by omega : t ≤ 2 ∨ 3 ≤ t) with ht | ht
  · interval_cases t <;> rfl
  · rw [g_in (by omega) (by omega : 0 + 2 ≤ t), g_in (by omega) (by omega : 1 + 2 ≤ t),
      g_in (by omega) (by omega : 0 + 2 ≤ t + 1)]
    rfl

/-- A cell on an axis: one neighbor at distance d - 1, three at d + 1. -/
theorem step1 (t d : ℕ) (hd : 1 ≤ d) :
    Nat.testBit 515 ((g t d).toNat + 2 * ((g t (d - 1)).toNat + 3 * (g t (d + 1)).toNat)) =
      g (t + 1) d := by
  rcases (by omega : t ≤ 1 ∨ 2 ≤ t) with ht | ht
  · rcases (by omega : d ≤ 4 ∨ 5 ≤ d) with hd' | hd'
    · interval_cases t <;> interval_cases d <;> rfl
    · rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        rw [g0_pos (by omega : 0 < d), g0_pos (by omega : 0 < d - 1),
          g0_pos (by omega : 0 < d + 1), g_out (by omega : 0 < 0 + 1) (by omega : 0 + 1 < d)]
        rfl
      · rw [g_out h0 (by omega : t < d), g_out h0 (by omega : t < d - 1),
          g_out h0 (by omega : t < d + 1), g_out (by omega : 0 < t + 1) (by omega : t + 1 < d)]
        rfl
  · have h1 : (d - 1) % 2 = (d % 2 + 1) % 2 := by omega
    have h2 : (d + 1) % 2 = (d % 2 + 1) % 2 := by omega
    have hs : d % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rcases (by omega : d + 3 ≤ t ∨ d + 2 = t ∨ d + 1 = t ∨ d = t ∨ d = t + 1 ∨ t + 2 ≤ d)
      with c | c | c | c | c | c
    · rw [g_in ht (by omega : d + 2 ≤ t), g_in ht (by omega : d - 1 + 2 ≤ t),
        g_in ht (by omega : d + 1 + 2 ≤ t), g_in (by omega) (by omega : d + 2 ≤ t + 1), h1, h2]
      generalize d % 2 = s at *
      interval_cases s <;> rfl
    · rw [g_in ht (by omega : d + 2 ≤ t), g_in ht (by omega : d - 1 + 2 ≤ t),
        g_edge ht (by omega : t ≤ d + 1 + 1) (by omega : d + 1 ≤ t),
        g_in (by omega) (by omega : d + 2 ≤ t + 1), h1]
      generalize d % 2 = s at *
      interval_cases s <;> rfl
    · rw [g_edge ht (by omega : t ≤ d + 1) (by omega : d ≤ t),
        g_in ht (by omega : d - 1 + 2 ≤ t), g_edge ht (by omega : t ≤ d + 1 + 1) (by omega),
        g_in (by omega) (by omega : d + 2 ≤ t + 1), h1]
      generalize d % 2 = s at *
      interval_cases s <;> rfl
    · rw [g_edge ht (by omega : t ≤ d + 1) (by omega : d ≤ t),
        g_edge ht (by omega : t ≤ d - 1 + 1) (by omega : d - 1 ≤ t),
        g_out (by omega : 0 < t) (by omega : t < d + 1),
        g_edge (by omega) (by omega : t + 1 ≤ d + 1) (by omega : d ≤ t + 1)]
      rfl
    · rw [g_out (by omega : 0 < t) (by omega : t < d),
        g_edge ht (by omega : t ≤ d - 1 + 1) (by omega : d - 1 ≤ t),
        g_out (by omega : 0 < t) (by omega : t < d + 1),
        g_edge (by omega) (by omega : t + 1 ≤ d + 1) (by omega : d ≤ t + 1)]
      rfl
    · rw [g_out (by omega : 0 < t) (by omega : t < d),
        g_out (by omega : 0 < t) (by omega : t < d - 1),
        g_out (by omega : 0 < t) (by omega : t < d + 1),
        g_out (by omega : 0 < t + 1) (by omega : t + 1 < d)]
      rfl

/-- A cell off the axes: two neighbors at distance d - 1, two at d + 1. -/
theorem step2 (t d : ℕ) (hd : 2 ≤ d) :
    Nat.testBit 515 ((g t d).toNat +
      2 * (2 * (g t (d - 1)).toNat + 2 * (g t (d + 1)).toNat)) = g (t + 1) d := by
  rcases (by omega : t ≤ 1 ∨ 2 ≤ t) with ht | ht
  · rcases (by omega : d ≤ 4 ∨ 5 ≤ d) with hd' | hd'
    · interval_cases t <;> interval_cases d <;> rfl
    · rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        rw [g0_pos (by omega : 0 < d), g0_pos (by omega : 0 < d - 1),
          g0_pos (by omega : 0 < d + 1), g_out (by omega : 0 < 0 + 1) (by omega : 0 + 1 < d)]
        rfl
      · rw [g_out h0 (by omega : t < d), g_out h0 (by omega : t < d - 1),
          g_out h0 (by omega : t < d + 1), g_out (by omega : 0 < t + 1) (by omega : t + 1 < d)]
        rfl
  · have h1 : (d - 1) % 2 = (d % 2 + 1) % 2 := by omega
    have h2 : (d + 1) % 2 = (d % 2 + 1) % 2 := by omega
    have hs : d % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rcases (by omega : d + 3 ≤ t ∨ d + 2 = t ∨ d + 1 = t ∨ d = t ∨ d = t + 1 ∨ t + 2 ≤ d)
      with c | c | c | c | c | c
    · rw [g_in ht (by omega : d + 2 ≤ t), g_in ht (by omega : d - 1 + 2 ≤ t),
        g_in ht (by omega : d + 1 + 2 ≤ t), g_in (by omega) (by omega : d + 2 ≤ t + 1), h1, h2]
      generalize d % 2 = s at *
      interval_cases s <;> rfl
    · rw [g_in ht (by omega : d + 2 ≤ t), g_in ht (by omega : d - 1 + 2 ≤ t),
        g_edge ht (by omega : t ≤ d + 1 + 1) (by omega : d + 1 ≤ t),
        g_in (by omega) (by omega : d + 2 ≤ t + 1), h1]
      generalize d % 2 = s at *
      interval_cases s <;> rfl
    · rw [g_edge ht (by omega : t ≤ d + 1) (by omega : d ≤ t),
        g_in ht (by omega : d - 1 + 2 ≤ t), g_edge ht (by omega : t ≤ d + 1 + 1) (by omega),
        g_in (by omega) (by omega : d + 2 ≤ t + 1), h1]
      generalize d % 2 = s at *
      interval_cases s <;> rfl
    · rw [g_edge ht (by omega : t ≤ d + 1) (by omega : d ≤ t),
        g_edge ht (by omega : t ≤ d - 1 + 1) (by omega : d - 1 ≤ t),
        g_out (by omega : 0 < t) (by omega : t < d + 1),
        g_edge (by omega) (by omega : t + 1 ≤ d + 1) (by omega : d ≤ t + 1)]
      rfl
    · rw [g_out (by omega : 0 < t) (by omega : t < d),
        g_edge ht (by omega : t ≤ d - 1 + 1) (by omega : d - 1 ≤ t),
        g_out (by omega : 0 < t) (by omega : t < d + 1),
        g_edge (by omega) (by omega : t + 1 ≤ d + 1) (by omega : d ≤ t + 1)]
      rfl
    · rw [g_out (by omega : 0 < t) (by omega : t < d),
        g_out (by omega : 0 < t) (by omega : t < d - 1),
        g_out (by omega : 0 < t) (by omega : t < d + 1),
        g_out (by omega : 0 < t + 1) (by omega : t + 1 < d)]
      rfl

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
        g0_pos (by omega)]
  | succ t ih =>
    intro x y
    show Nat.testBit 515 _ = _
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

theorem a_eq (n : ℕ) : a n = ∑ k ∈ Finset.range (n + 1), if g n (2 * k) then 2 ^ (n - k) else 0 := by
  unfold a
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [state_pattern, show ((k : ℤ)).natAbs + ((k : ℤ)).natAbs = 2 * k by simp; ring]

/-- Controls: the entry's terms a(0..15). -/
theorem controls : (List.range 16).map a =
    [1, 3, 5, 11, 27, 55, 119, 239, 495, 991, 2015, 4031, 8127, 16255, 32639, 65279] := by
  rw [show a = fun n => ∑ k ∈ Finset.range (n + 1), if g n (2 * k) then 2 ^ (n - k) else 0
    from funext a_eq]
  decide

theorem geom (n : ℕ) : ∑ k ∈ Finset.range n, (2 : ℤ) ^ k = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- From stage 2 on only the diagonal cell with k = n / 2 is OFF. -/
theorem a_closed (n : ℕ) (hn : 2 ≤ n) : (a n : ℤ) = 2 ^ (n + 1) - 1 - 2 ^ (n - n / 2) := by
  have e : ∀ k ∈ Finset.range (n + 1), (if g n (2 * k) = true then (2 : ℤ) ^ (n - k) else 0) =
      (2 : ℤ) ^ (n - k) - (if k = n / 2 then (2 : ℤ) ^ (n - k) else 0) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    by_cases h : k = n / 2
    · rw [g_edge hn (by omega : n ≤ 2 * k + 1) (by omega : 2 * k ≤ n), if_pos h]; simp
    · rcases Nat.lt_or_ge n (2 * k) with h' | h'
      · rw [g_out (by omega) h', if_neg h]; simp
      · rw [g_in hn (by omega : 2 * k + 2 ≤ n), if_neg h, show 2 * k % 2 = 0 by omega]; simp
  have hR : ∑ k ∈ Finset.range (n + 1), (2 : ℤ) ^ (n - k) = 2 ^ (n + 1) - 1 := by
    rw [← geom (n + 1), ← Finset.sum_range_reflect (fun k => (2 : ℤ) ^ k) (n + 1)]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [show n + 1 - 1 - k = n - k by omega]
  have hS : ∑ k ∈ Finset.range (n + 1), (if k = n / 2 then (2 : ℤ) ^ (n - k) else 0) =
      2 ^ (n - n / 2) := by
    rw [Finset.sum_eq_single (n / 2)]
    · rw [if_pos rfl]
    · intro k _ hk; rw [if_neg hk]
    · intro h; simp only [Finset.mem_range] at h; omega
  rw [a_eq]
  push_cast
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, hR, hS]

theorem a_even (m : ℕ) (hm : 1 ≤ m) : (a (2 * m) : ℤ) = 2 ^ (2 * m + 1) - 1 - 2 ^ m := by
  rw [a_closed (2 * m) (by omega), show 2 * m - 2 * m / 2 = m by omega]

theorem a_odd (m : ℕ) (hm : 1 ≤ m) : (a (2 * m + 1) : ℤ) = 2 ^ (2 * m + 2) - 1 - 2 ^ (m + 1) := by
  rw [a_closed (2 * m + 1) (by omega), show 2 * m + 1 - (2 * m + 1) / 2 = m + 1 by omega]

/-- Wu's recurrence. -/
theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 6 * a (n - 3) + 4 * a (n - 4) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
  rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
  · rw [show 2 * i + 6 - 1 = 2 * (i + 2) + 1 by omega, show 2 * i + 6 - 3 = 2 * (i + 1) + 1 by omega,
      show 2 * i + 6 - 4 = 2 * (i + 1) by omega, show 2 * i + 6 = 2 * (i + 3) by ring,
      a_even (i + 3) (by omega), a_odd (i + 2) (by omega), a_odd (i + 1) (by omega),
      a_even (i + 1) (by omega)]
    ring
  · rw [show 2 * i + 1 + 6 - 1 = 2 * (i + 3) by omega,
      show 2 * i + 1 + 6 - 3 = 2 * (i + 2) by omega,
      show 2 * i + 1 + 6 - 4 = 2 * (i + 1) + 1 by omega,
      show 2 * i + 1 + 6 = 2 * (i + 3) + 1 by ring,
      a_odd (i + 3) (by omega), a_even (i + 3) (by omega), a_even (i + 2) (by omega),
      a_odd (i + 1) (by omega)]
    ring

/-- Wu's g.f. with the denominator cleared. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((X - 1) * (2 * X - 1) * (2 * X ^ 2 - 1)) =
    8 * X ^ 5 - 8 * X ^ 4 - 2 * X ^ 3 + 4 * X ^ 2 - 1 := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have c2 : (C (2 : ℤ) : PowerSeries ℤ) = 2 := map_ofNat C 2
  have c3 : (C (3 : ℤ) : PowerSeries ℤ) = 3 := map_ofNat C 3
  have c4 : (C (4 : ℤ) : PowerSeries ℤ) = 4 := map_ofNat C 4
  have c6 : (C (6 : ℤ) : PowerSeries ℤ) = 6 := map_ofNat C 6
  have c8 : (C (8 : ℤ) : PowerSeries ℤ) = 8 := map_ofNat C 8
  have hD : A * ((X - 1) * (2 * X - 1) * (2 * X ^ 2 - 1)) =
      C 3 * (A * X ^ 1) - C 6 * (A * X ^ 3) + C 4 * (A * X ^ 4) - A := by
    rw [c3, c4, c6]; ring
  have hN : (8 * X ^ 5 - 8 * X ^ 4 - 2 * X ^ 3 + 4 * X ^ 2 - 1 : PowerSeries ℤ) =
      X ^ 5 * C 8 - X ^ 4 * C 8 - X ^ 3 * C 2 + X ^ 2 * C 4 - 1 := by
    rw [c2, c4, c8]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', hA, coeff_mk,
    coeff_one, coeff_X_pow]
  have c := controls
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq] at c
  obtain ⟨v0, v1, v2, v3, v4, v5, -⟩ := c
  rcases Nat.lt_or_ge n 6 with h | h
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5]
  · have r := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, if_true,
      show n ≠ 0 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega,
      show n ≠ 5 by omega, if_false]
    linear_combination -r

/-- Both of Wu's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 3 * a (n - 1) - 6 * a (n - 3) + 4 * a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * ((X - 1) * (2 * X - 1) * (2 * X ^ 2 - 1)) =
      8 * X ^ 5 - 8 * X ^ 4 - 2 * X ^ 3 + 4 * X ^ 2 - 1 :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a288828

theorem OMA.solution : type_of% @OMA.S_oeis_a288828.main :=
  OMA.S_oeis_a288828.conjecture

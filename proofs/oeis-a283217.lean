import OMAStatements.S_oeis_a283217

namespace OMA.S_oeis_a283217

open PowerSeries



/-- The pattern inside the diamond, by t mod 4 and d mod 4. -/
def tab (r s : ℕ) : Bool :=
  (r == 0 && s == 0) || (r == 2 && s == 2) || (r == 1 && s != 0) || (r == 3 && s != 2)

/-- The state at stage t of a cell at distance d = |x| + |y| from the origin. -/
def g (t d : ℕ) : Bool := if t = 0 then d == 0 else if t < d then true else tab (t % 4) (d % 4)

theorem g_zero_pos {d : ℕ} (h : 0 < d) : g 0 d = false := by
  simp only [g, if_pos rfl]; simp; omega

theorem g_in {t d : ℕ} (ht : 0 < t) (h : d ≤ t) : g t d = tab (t % 4) (d % 4) := by
  simp only [g, if_neg (Nat.pos_iff_ne_zero.mp ht), if_neg (Nat.not_lt.mpr h)]

theorem g_out {t d : ℕ} (ht : 0 < t) (h : t < d) : g t d = true := by
  simp only [g, if_neg (Nat.pos_iff_ne_zero.mp ht), if_pos h]

/-- The origin: four neighbors at distance 1. -/
theorem step0 (t : ℕ) :
    Nat.testBit 597 ((g t 0).toNat + 2 * (4 * (g t 1).toNat)) = g (t + 1) 0 := by
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht; rfl
  · have h3 : (t + 1) % 4 = (t % 4 + 1) % 4 := by omega
    have hr : t % 4 < 4 := Nat.mod_lt _ (by norm_num)
    rw [g_in ht (by omega), g_in ht (by omega), g_in (by omega) (by omega), h3]
    generalize t % 4 = r at *
    interval_cases r <;> rfl

/-- A cell on an axis: one neighbor at distance d - 1, three at d + 1. -/
theorem step1 (t d : ℕ) (hd : 1 ≤ d) :
    Nat.testBit 597 ((g t d).toNat + 2 * ((g t (d - 1)).toNat + 3 * (g t (d + 1)).toNat)) =
      g (t + 1) d := by
  have h1 : (d - 1) % 4 = (d % 4 + 3) % 4 := by omega
  have h2 : (d + 1) % 4 = (d % 4 + 1) % 4 := by omega
  have h3 : (t + 1) % 4 = (t % 4 + 1) % 4 := by omega
  have hr : t % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hs : d % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    rcases Nat.lt_or_ge d 2 with hd2 | hd2
    · obtain rfl : d = 1 := by omega
      rfl
    · rw [g_zero_pos (by omega : 0 < d), g_zero_pos (by omega : 0 < d - 1),
        g_zero_pos (by omega : 0 < d + 1), g_out (by omega : 0 < 0 + 1) (by omega)]
      rfl
  · rcases (by omega : d + 1 ≤ t ∨ d = t ∨ d = t + 1 ∨ t + 2 ≤ d) with c | c | c | c
    · rw [g_in ht (by omega : d ≤ t), g_in ht (by omega : d - 1 ≤ t),
        g_in ht (by omega : d + 1 ≤ t), g_in (by omega : 0 < t + 1) (by omega : d ≤ t + 1),
        h1, h2, h3]
      generalize t % 4 = r at *; generalize d % 4 = s at *
      interval_cases r <;> interval_cases s <;> rfl
    · have hrel : d % 4 = t % 4 := by omega
      rw [g_in ht (by omega : d ≤ t), g_in ht (by omega : d - 1 ≤ t),
        g_out ht (by omega : t < d + 1), g_in (by omega : 0 < t + 1) (by omega : d ≤ t + 1),
        h1, h3, hrel]
      generalize t % 4 = r at *
      interval_cases r <;> rfl
    · have hrel : d % 4 = (t % 4 + 1) % 4 := by omega
      rw [g_out ht (by omega : t < d), g_in ht (by omega : d - 1 ≤ t),
        g_out ht (by omega : t < d + 1), g_in (by omega : 0 < t + 1) (by omega : d ≤ t + 1),
        h1, h3, hrel]
      generalize t % 4 = r at *
      interval_cases r <;> rfl
    · rw [g_out ht (by omega : t < d), g_out ht (by omega : t < d - 1),
        g_out ht (by omega : t < d + 1), g_out (by omega : 0 < t + 1) (by omega : t + 1 < d)]
      rfl

/-- A cell off the axes: two neighbors at distance d - 1, two at d + 1. -/
theorem step2 (t d : ℕ) (hd : 2 ≤ d) :
    Nat.testBit 597 ((g t d).toNat +
      2 * (2 * (g t (d - 1)).toNat + 2 * (g t (d + 1)).toNat)) = g (t + 1) d := by
  have h1 : (d - 1) % 4 = (d % 4 + 3) % 4 := by omega
  have h2 : (d + 1) % 4 = (d % 4 + 1) % 4 := by omega
  have h3 : (t + 1) % 4 = (t % 4 + 1) % 4 := by omega
  have hr : t % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hs : d % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht
    rw [g_zero_pos (by omega : 0 < d), g_zero_pos (by omega : 0 < d - 1),
      g_zero_pos (by omega : 0 < d + 1), g_out (by omega : 0 < 0 + 1) (by omega)]
    rfl
  · rcases (by omega : d + 1 ≤ t ∨ d = t ∨ d = t + 1 ∨ t + 2 ≤ d) with c | c | c | c
    · rw [g_in ht (by omega : d ≤ t), g_in ht (by omega : d - 1 ≤ t),
        g_in ht (by omega : d + 1 ≤ t), g_in (by omega : 0 < t + 1) (by omega : d ≤ t + 1),
        h1, h2, h3]
      generalize t % 4 = r at *; generalize d % 4 = s at *
      interval_cases r <;> interval_cases s <;> rfl
    · have hrel : d % 4 = t % 4 := by omega
      rw [g_in ht (by omega : d ≤ t), g_in ht (by omega : d - 1 ≤ t),
        g_out ht (by omega : t < d + 1), g_in (by omega : 0 < t + 1) (by omega : d ≤ t + 1),
        h1, h3, hrel]
      generalize t % 4 = r at *
      interval_cases r <;> rfl
    · have hrel : d % 4 = (t % 4 + 1) % 4 := by omega
      rw [g_out ht (by omega : t < d), g_in ht (by omega : d - 1 ≤ t),
        g_out ht (by omega : t < d + 1), g_in (by omega : 0 < t + 1) (by omega : d ≤ t + 1),
        h1, h3, hrel]
      generalize t % 4 = r at *
      interval_cases r <;> rfl
    · rw [g_out ht (by omega : t < d), g_out ht (by omega : t < d - 1),
        g_out ht (by omega : t < d + 1), g_out (by omega : 0 < t + 1) (by omega : t + 1 < d)]
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
        g_zero_pos (by omega)]
  | succ t ih =>
    intro x y
    show Nat.testBit 597 _ = _
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

theorem a_eq (n : ℕ) : a n = ∑ k ∈ Finset.range (n + 1), if g n k then 2 ^ (n - k) else 0 := by
  unfold a
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [state_pattern]
  simp

/-- Controls: the entry's terms a(0..11). -/
theorem controls : (List.range 12).map a = [1, 1, 1, 13, 17, 29, 17, 221, 273, 477, 273, 3549] := by
  rw [show a = fun n => ∑ k ∈ Finset.range (n + 1), if g n k then 2 ^ (n - k) else 0 from
    funext a_eq]
  decide

theorem g_shift (n k : ℕ) (hk : k ≤ n) : g (n + 4) k = g n k := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    obtain rfl : k = 0 := by omega
    rfl
  · rw [g_in (by omega) (by omega), g_in hn hk, show (n + 4) % 4 = n % 4 by omega]

/-- Four more stages shift the digits left and add four cells at the right edge. -/
theorem shift (n : ℕ) : a (n + 4) = 16 * a n + (1 + 12 * (n % 2)) := by
  rw [a_eq, a_eq, show n + 4 + 1 = n + 1 + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  have e : ∑ k ∈ Finset.range (n + 1), (if g (n + 4) k then 2 ^ (n + 4 - k) else 0) =
      16 * ∑ k ∈ Finset.range (n + 1), (if g n k then 2 ^ (n - k) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k ≤ n := by simp at hk; omega
    rw [g_shift n k hk']
    split_ifs
    · rw [show n + 4 - k = n - k + 4 by omega, pow_add]; ring
    · simp
  rw [e, g_in (by omega : 0 < n + 4) (by omega : n + 1 ≤ n + 4),
    g_in (by omega : 0 < n + 4) (by omega : n + 1 + 1 ≤ n + 4),
    g_in (by omega : 0 < n + 4) (by omega : n + 1 + 1 + 1 ≤ n + 4),
    g_in (by omega : 0 < n + 4) (by omega : n + 1 + 1 + 1 + 1 ≤ n + 4)]
  have m1 : (n + 4) % 4 = n % 4 := by omega
  have m2 : (n + 1) % 4 = (n % 4 + 1) % 4 := by omega
  have m3 : (n + 1 + 1) % 4 = (n % 4 + 2) % 4 := by omega
  have m4 : (n + 1 + 1 + 1) % 4 = (n % 4 + 3) % 4 := by omega
  have m5 : (n + 1 + 1 + 1 + 1) % 4 = n % 4 := by omega
  have m6 : n % 2 = n % 4 % 2 := by omega
  have p1 : n + 4 - (n + 1) = 3 := by omega
  have p2 : n + 4 - (n + 1 + 1) = 2 := by omega
  have p3 : n + 4 - (n + 1 + 1 + 1) = 1 := by omega
  have p4 : n + 4 - (n + 1 + 1 + 1 + 1) = 0 := by omega
  simp only [m1, m2, m3, m4, m5, m6, p1, p2, p3, p4]
  have hr : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize n % 4 = r at *
  interval_cases r <;> simp [tab]

/-- Barker's recurrence. -/
theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = a (n - 2) + 16 * a (n - 4) - 16 * a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega,
    show m + 6 - 6 = m by omega]
  have h1 := shift (m + 2)
  have h2 := shift m
  rw [show m + 2 + 4 = m + 6 by ring, show (m + 2) % 2 = m % 2 by omega] at h1
  rw [h1, h2]
  push_cast
  ring

/-- Barker's g.f. with the denominator cleared. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) *
    (1 + 4 * X ^ 2)) = 1 + X + 12 * X ^ 3 := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have h16 : (C (16 : ℤ) : PowerSeries ℤ) = 16 := map_ofNat C 16
  have h12 : (C (12 : ℤ) : PowerSeries ℤ) = 12 := map_ofNat C 12
  have hD : A * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2)) =
      A - A * X ^ 2 - C 16 * (A * X ^ 4) + C 16 * (A * X ^ 6) := by rw [h16]; ring
  have hN : (1 + X + 12 * X ^ 3 : PowerSeries ℤ) = 1 + X ^ 1 + X ^ 3 * C 12 := by
    rw [h12]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', hA, coeff_mk,
    coeff_one, coeff_X_pow]
  have c := controls
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq] at c
  obtain ⟨v0, v1, v2, v3, v4, v5, -⟩ := c
  rcases Nat.lt_or_ge n 6 with h | h
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5]
  · have r := recurrence n (by omega)
    simp only [show 2 ≤ n by omega, show 4 ≤ n by omega, show 6 ≤ n by omega, if_true,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 3 by omega, if_false]
    linear_combination r

/-- Both of Barker's conjectures. -/
theorem conjecture :
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2)) =
      1 + X + 12 * X ^ 3 ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = a (n - 2) + 16 * a (n - 4) - 16 * a (n - 6)) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a283217

theorem OMA.solution : type_of% @OMA.S_oeis_a283217.main :=
  OMA.S_oeis_a283217.conjecture

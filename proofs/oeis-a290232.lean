import OMAStatements.S_oeis_a290232

namespace OMA.S_oeis_a290232

open PowerSeries



/-- The pattern inside the diamond, by t mod 4 and d mod 4. -/
def tab (r s : ℕ) : Bool := (r + s) % 2 == 0

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
    Nat.testBit 773 ((g t 0).toNat + 2 * (4 * (g t 1).toNat)) = g (t + 1) 0 := by
  rcases Nat.eq_zero_or_pos t with ht | ht
  · subst ht; rfl
  · have h3 : (t + 1) % 4 = (t % 4 + 1) % 4 := by omega
    have hr : t % 4 < 4 := Nat.mod_lt _ (by norm_num)
    rw [g_in ht (by omega), g_in ht (by omega), g_in (by omega) (by omega), h3]
    generalize t % 4 = r at *
    interval_cases r <;> rfl

/-- A cell on an axis: one neighbor at distance d - 1, three at d + 1. -/
theorem step1 (t d : ℕ) (hd : 1 ≤ d) :
    Nat.testBit 773 ((g t d).toNat + 2 * ((g t (d - 1)).toNat + 3 * (g t (d + 1)).toNat)) =
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
    Nat.testBit 773 ((g t d).toNat +
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
    show Nat.testBit 773 _ = _
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

theorem a_eq (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n + 1), if g n (2 * k) then 10 ^ k else 0 := by
  unfold a
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [state_pattern, show (k : ℤ).natAbs + (k : ℤ).natAbs = 2 * k by simp; ring]

/-- Controls: the entry's terms a(0..9). -/
theorem controls : (List.range 10).map a =
    [1, 10, 111, 1100, 11111, 111000, 1111111, 11110000, 111111111, 1111100000] := by
  rw [show a = fun n => ∑ k ∈ Finset.range (n + 1), if g n (2 * k) then 10 ^ k else 0 from
    funext a_eq]
  decide

theorem geom (s : ℕ) : 9 * (∑ i ∈ Finset.range s, (10 : ℤ) ^ i) = 10 ^ s - 1 := by
  have := geom_sum_mul (10 : ℤ) s
  linarith

/-- Barker's closed form for even n. -/
theorem closed_even (n : ℕ) (h : n % 2 = 0) : 9 * (a n : ℤ) = 10 ^ (n + 1) - 1 := by
  rw [a_eq]
  have e : ∀ k ∈ Finset.range (n + 1), (if g n (2 * k) then 10 ^ k else 0) = 10 ^ k := by
    intro k hk
    have hk' : k ≤ n := by simp at hk; omega
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      obtain rfl : k = 0 := by omega
      rfl
    · rcases Nat.lt_or_ge n (2 * k) with c | c
      · rw [g_out hn c]; rfl
      · rw [g_in hn c, if_pos]
        simp only [tab, beq_iff_eq]; omega
  rw [Finset.sum_congr rfl e]
  push_cast
  exact geom (n + 1)

/-- Barker's closed form for odd n. -/
theorem closed_odd (n : ℕ) (h : n % 2 = 1) :
    9 * (a n : ℤ) = 10 ^ (n + 1) - 10 ^ ((n + 1) / 2) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = 2 * q + 1 := ⟨n / 2, by omega⟩
  rw [a_eq, show 2 * q + 1 + 1 = (q + 1) + (q + 1) by ring, Finset.sum_range_add]
  have e0 : ∑ k ∈ Finset.range (q + 1), (if g (2 * q + 1) (2 * k) then 10 ^ k else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k ≤ q := by simp at hk; omega
    rw [g_in (by omega) (by omega), if_neg]
    simp only [tab, beq_iff_eq]; omega
  have e1 : ∀ j ∈ Finset.range (q + 1),
      (if g (2 * q + 1) (2 * (q + 1 + j)) then 10 ^ (q + 1 + j) else 0) =
        10 ^ (q + 1) * 10 ^ j := by
    intro j _
    rw [g_out (by omega) (by omega), if_pos rfl, pow_add]
  rw [e0, Finset.sum_congr rfl e1, zero_add, ← Finset.mul_sum,
    show (q + 1 + (q + 1)) / 2 = q + 1 by omega]
  push_cast
  have g1 := geom (q + 1)
  rw [show q + 1 + (q + 1) = (q + 1) + (q + 1) by ring, pow_add]
  linear_combination (10 : ℤ) ^ (q + 1) * g1

/-- Barker's recurrence. -/
theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 10 * a (n - 1) + 11 * a (n - 2) - 110 * a (n - 3) - 10 * a (n - 4) +
      100 * a (n - 5) := by
  rcases Nat.mod_two_eq_zero_or_one n with hp | hp
  · obtain ⟨p, rfl⟩ : ∃ p, n = 2 * p + 6 := ⟨n / 2 - 3, by omega⟩
    have c0 := closed_even (2 * p + 6) (by omega)
    have c1 := closed_odd (2 * p + 5) (by omega)
    have c2 := closed_even (2 * p + 4) (by omega)
    have c3 := closed_odd (2 * p + 3) (by omega)
    have c4 := closed_even (2 * p + 2) (by omega)
    have c5 := closed_odd (2 * p + 1) (by omega)
    rw [show 2 * p + 6 - 1 = 2 * p + 5 by omega, show 2 * p + 6 - 2 = 2 * p + 4 by omega,
      show 2 * p + 6 - 3 = 2 * p + 3 by omega, show 2 * p + 6 - 4 = 2 * p + 2 by omega,
      show 2 * p + 6 - 5 = 2 * p + 1 by omega]
    rw [show (2 * p + 5 + 1) / 2 = p + 3 by omega] at c1
    rw [show (2 * p + 3 + 1) / 2 = p + 2 by omega] at c3
    rw [show (2 * p + 1 + 1) / 2 = p + 1 by omega] at c5
    have h : 9 * ((a (2 * p + 6) : ℤ) - (10 * a (2 * p + 5) + 11 * a (2 * p + 4) -
        110 * a (2 * p + 3) - 10 * a (2 * p + 2) + 100 * a (2 * p + 1))) = 0 := by
      simp only [pow_add, pow_mul] at c0 c1 c2 c3 c4 c5
      linear_combination c0 - 10 * c1 - 11 * c2 + 110 * c3 + 10 * c4 - 100 * c5
    have := (mul_eq_zero.mp h).resolve_left (by norm_num)
    linarith
  · obtain ⟨p, rfl⟩ : ∃ p, n = 2 * p + 5 := ⟨n / 2 - 2, by omega⟩
    have c0 := closed_odd (2 * p + 5) (by omega)
    have c1 := closed_even (2 * p + 4) (by omega)
    have c2 := closed_odd (2 * p + 3) (by omega)
    have c3 := closed_even (2 * p + 2) (by omega)
    have c4 := closed_odd (2 * p + 1) (by omega)
    have c5 := closed_even (2 * p) (by omega)
    rw [show 2 * p + 5 - 1 = 2 * p + 4 by omega, show 2 * p + 5 - 2 = 2 * p + 3 by omega,
      show 2 * p + 5 - 3 = 2 * p + 2 by omega, show 2 * p + 5 - 4 = 2 * p + 1 by omega,
      show 2 * p + 5 - 5 = 2 * p by omega]
    rw [show (2 * p + 5 + 1) / 2 = p + 3 by omega] at c0
    rw [show (2 * p + 3 + 1) / 2 = p + 2 by omega] at c2
    rw [show (2 * p + 1 + 1) / 2 = p + 1 by omega] at c4
    have h : 9 * ((a (2 * p + 5) : ℤ) - (10 * a (2 * p + 4) + 11 * a (2 * p + 3) -
        110 * a (2 * p + 2) - 10 * a (2 * p + 1) + 100 * a (2 * p))) = 0 := by
      simp only [pow_add, pow_mul] at c0 c1 c2 c3 c4 c5
      linear_combination c0 - 10 * c1 - 11 * c2 + 110 * c3 + 10 * c4 - 100 * c5
    have := (mul_eq_zero.mp h).resolve_left (by norm_num)
    linarith

/-- Barker's g.f. with the denominator cleared. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 - 10 * X ^ 2)) =
    1 - 10 * X ^ 3 := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have c10 : (C (10 : ℤ) : PowerSeries ℤ) = 10 := map_ofNat C 10
  have c11 : (C (11 : ℤ) : PowerSeries ℤ) = 11 := map_ofNat C 11
  have c100 : (C (100 : ℤ) : PowerSeries ℤ) = 100 := map_ofNat C 100
  have c110 : (C (110 : ℤ) : PowerSeries ℤ) = 110 := map_ofNat C 110
  have hD : A * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 - 10 * X ^ 2)) =
      A - C 10 * (A * X ^ 1) - C 11 * (A * X ^ 2) + C 110 * (A * X ^ 3) +
        C 10 * (A * X ^ 4) - C 100 * (A * X ^ 5) := by
    rw [c10, c11, c100, c110]; ring
  have hN : (1 - 10 * X ^ 3 : PowerSeries ℤ) = 1 - X ^ 3 * C 10 := by rw [c10]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_C, coeff_mul_X_pow', hA, coeff_mk,
    coeff_one, coeff_X_pow]
  have c := controls
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq] at c
  obtain ⟨v0, v1, v2, v3, v4, -⟩ := c
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp [v0, v1, v2, v3, v4]
  · have r := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega, if_true, show n ≠ 0 by omega,
      show n ≠ 3 by omega, if_false]
    linear_combination r

/-- Barker's four conjectures. -/
theorem conjecture :
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 - 10 * X ^ 2)) =
      1 - 10 * X ^ 3 ∧
    (∀ n : ℕ, n % 2 = 0 → 9 * (a n : ℤ) = 10 ^ (n + 1) - 1) ∧
    (∀ n : ℕ, n % 2 = 1 → 9 * (a n : ℤ) = 10 ^ (n + 1) - 10 ^ ((n + 1) / 2)) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 10 * a (n - 1) + 11 * a (n - 2) - 110 * a (n - 3) -
      10 * a (n - 4) + 100 * a (n - 5)) :=
  ⟨gf, closed_even, closed_odd, recurrence⟩

end OMA.S_oeis_a290232

theorem OMA.solution : type_of% @OMA.S_oeis_a290232.main :=
  OMA.S_oeis_a290232.conjecture

import OMAStatements.S_oeis_a289150

namespace OMA.S_oeis_a289150

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
theorem a_eq (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n + 1), if g n (2 * k) then 10 ^ k else 0 := by
  unfold a
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [state_pattern, show (k : ℤ).natAbs + (k : ℤ).natAbs = 2 * k by simp; ring]

/-- Controls: the entry's terms a(0..9). -/
theorem controls : (List.range 10).map a =
    [1, 10, 110, 1101, 11101, 111010, 1111010, 11110101, 111110101, 1111101010] := by
  rw [show a = fun n => ∑ k ∈ Finset.range (n + 1), if g n (2 * k) then 10 ^ k else 0 from
    funext a_eq]
  decide

/-- Two more stages move the diagonal pattern one cell outwards. -/
theorem diag_shift (n k : ℕ) (hk : k ≤ n) : g (n + 2) (2 * (k + 1)) = g n (2 * k) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    obtain rfl : k = 0 := by omega
    rfl
  · rcases Nat.lt_or_ge n (2 * k) with h | h
    · rw [g_out hn h, g_out (by omega) (by omega)]
    · rw [g_in hn h, g_in (by omega) (by omega)]
      have e1 : (n + 2) % 4 = (n % 4 + 2) % 4 := by omega
      have e2 : (2 * (k + 1)) % 4 = (2 * (k % 2) + 2) % 4 := by omega
      have e3 : (2 * k) % 4 = 2 * (k % 2) := by omega
      have hr : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
      have hs : k % 2 < 2 := Nat.mod_lt _ (by norm_num)
      rw [e1, e2, e3]
      generalize n % 4 = r at *; generalize k % 2 = s at *
      interval_cases r <;> interval_cases s <;> rfl

/-- E(n) = 1 for n = 1, 2 mod 4 and 0 otherwise: the origin of stage n + 2. -/
def E (n : ℕ) : ℕ := if n % 4 = 1 ∨ n % 4 = 2 then 1 else 0

theorem origin (n : ℕ) : (if g (n + 2) (2 * 0) then 10 ^ 0 else 0) = E n := by
  rw [show 2 * 0 = 0 by rfl, g_in (by omega) (by omega),
    show (n + 2) % 4 = (n % 4 + 2) % 4 by omega]
  have hr : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  unfold E
  generalize n % 4 = r at *
  interval_cases r <;> simp [tab]

theorem a2 (n : ℕ) : a (n + 2) = 10 * a n + E n + 10 ^ (n + 2) := by
  rw [a_eq, a_eq, Finset.sum_range_succ', origin, show n + 2 = n + 1 + 1 by ring,
    Finset.sum_range_succ, g_out (by omega) (by omega : n + 1 + 1 < 2 * (n + 1 + 1)),
    Finset.mul_sum]
  have e : ∑ k ∈ Finset.range (n + 1),
      (if g (n + 1 + 1) (2 * (k + 1)) then 10 ^ (k + 1) else 0) =
      ∑ k ∈ Finset.range (n + 1), 10 * (if g n (2 * k) then 10 ^ k else 0) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k ≤ n := by simp at hk; omega
    rw [show n + 1 + 1 = n + 2 by ring, diag_shift n k hk']
    split_ifs
    · rw [pow_succ]; ring
    · simp
  rw [e, if_pos rfl]
  ring

theorem E_facts (n : ℕ) : E (n + 4) = E n ∧ E (n + 2) + E n = 1 := by
  unfold E
  constructor <;> split_ifs <;> omega

/-- The recurrence of the denominator (1 - x)(1 - 10x)(1 + x^2)(1 - 10x^2). -/
theorem rec6 (n : ℕ) :
    (a (n + 6) : ℤ) - 11 * a (n + 5) + a (n + 4) + 99 * a (n + 3) - 100 * a (n + 2) +
      110 * a (n + 1) - 100 * a n = 0 := by
  have r0 := a2 n
  have r1 := a2 (n + 1)
  have r2 := a2 (n + 2)
  have r3 := a2 (n + 3)
  have r4 := a2 (n + 4)
  obtain ⟨f40, f20⟩ := E_facts n
  obtain ⟨-, f31⟩ := E_facts (n + 1)
  rw [show n + 2 + 2 = n + 4 by ring] at r2
  rw [show n + 1 + 2 = n + 3 by ring] at r1 f31
  rw [show n + 3 + 2 = n + 5 by ring] at r3
  rw [show n + 4 + 2 = n + 6 by ring, f40] at r4
  have g20 : (E (n + 2) : ℤ) = 1 - E n := by omega
  have g31 : (E (n + 3) : ℤ) = 1 - E (n + 1) := by omega
  have q0 : (a (n + 2) : ℤ) = 10 * a n + E n + 10 ^ (n + 2) := by exact_mod_cast r0
  have q1 : (a (n + 3) : ℤ) = 10 * a (n + 1) + E (n + 1) + 10 ^ (n + 3) := by
    exact_mod_cast r1
  have q2 : (a (n + 4) : ℤ) = 10 * a (n + 2) + E (n + 2) + 10 ^ (n + 4) := by
    exact_mod_cast r2
  have q3 : (a (n + 5) : ℤ) = 10 * a (n + 3) + E (n + 3) + 10 ^ (n + 5) := by
    exact_mod_cast r3
  have q4 : (a (n + 6) : ℤ) = 10 * a (n + 4) + E n + 10 ^ (n + 6) := by exact_mod_cast r4
  rw [g20] at q2
  rw [g31] at q3
  rw [q4, q3, q2, q1, q0]
  ring

/-- Barker's g.f. with the denominator cleared. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 10 * X) * (1 + X ^ 2) *
    (1 - 10 * X ^ 2)) = 1 - X + X ^ 2 - 10 * X ^ 4 := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have c10 : (C (10 : ℤ) : PowerSeries ℤ) = 10 := map_ofNat C 10
  have c11 : (C (11 : ℤ) : PowerSeries ℤ) = 11 := map_ofNat C 11
  have c99 : (C (99 : ℤ) : PowerSeries ℤ) = 99 := map_ofNat C 99
  have c100 : (C (100 : ℤ) : PowerSeries ℤ) = 100 := map_ofNat C 100
  have c110 : (C (110 : ℤ) : PowerSeries ℤ) = 110 := map_ofNat C 110
  have hD : A * ((1 - X) * (1 - 10 * X) * (1 + X ^ 2) * (1 - 10 * X ^ 2)) =
      A - C 11 * (A * X ^ 1) + A * X ^ 2 + C 99 * (A * X ^ 3) - C 100 * (A * X ^ 4) +
        C 110 * (A * X ^ 5) - C 100 * (A * X ^ 6) := by
    rw [c11, c99, c100, c110]; ring
  have hN : (1 - X + X ^ 2 - 10 * X ^ 4 : PowerSeries ℤ) = 1 - X ^ 1 + X ^ 2 - X ^ 4 * C 10 := by
    rw [c10]; ring
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
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    have r := rec6 m
    simp only [show 1 ≤ m + 6 by omega, show 2 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega,
      show 4 ≤ m + 6 by omega, show 5 ≤ m + 6 by omega, show 6 ≤ m + 6 by omega, if_true,
      show m + 6 ≠ 0 by omega, show m + 6 ≠ 1 by omega, show m + 6 ≠ 2 by omega,
      show m + 6 ≠ 4 by omega, if_false, show m + 6 - 1 = m + 5 by omega,
      show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega,
      show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega,
      show m + 6 - 6 = m by omega]
    linear_combination r

end OMA.S_oeis_a289150

theorem OMA.solution : type_of% @OMA.S_oeis_a289150.main :=
  OMA.S_oeis_a289150.gf
